//! Execute a frontend-proved structural order projection on fingerprint values.
//! Concrete states and transitions are never rewritten.
use crate::error::{EResult, EvalError};
use std::collections::{BTreeMap, BTreeSet};
use tlx_sema::optimize::{OrderedPlan, OrderedShape};
use tlx_value::Value;

pub(super) fn project(plan: &OrderedPlan, values: &[Value]) -> EResult<Value> {
    let mut roots: Vec<BTreeSet<i64>> = plan
        .anchors
        .iter()
        .map(|ns| {
            ns.iter().map(|n| i64::try_from(*n).map_err(|_| EvalError::new("optimization anchor exceeds integer representation"))).collect()
        })
        .collect::<EResult<_>>()?;
    let mut values = values.iter().map(Value::normalize).collect::<tlx_value::Result<Vec<_>>>()?;
    for (i, (s, v)) in plan.variables.iter().zip(&values).enumerate() {
        if plan.history.as_ref().is_some_and(|h| h.variable == i) {
            continue;
        }
        walk(v, &[s], &mut |f, n| {
            roots[f].insert(n);
            Ok(n)
        })?;
    }
    if let Some(h) = &plan.history {
        let pairs = pairs(&values[h.variable])?;
        let retained = pairs.into_iter().filter(|(k, _)| matches!(k, Value::Int(n) if roots[h.family].contains(n))).collect();
        values[h.variable] = Value::fcn_rcd_from_pairs(retained)?;
        walk(&values[h.variable], &[&plan.variables[h.variable]], &mut |f, n| {
            roots[f].insert(n);
            Ok(n)
        })?;
    }
    let ranks: Vec<BTreeMap<i64, i64>> = roots
        .iter()
        .map(|s| {
            s.iter()
                .filter(|n| **n > 0)
                .enumerate()
                .map(|(i, n)| {
                    Ok((*n, i64::try_from(i + 1).map_err(|_| EvalError::new("optimization rank exceeds integer representation"))?))
                })
                .collect()
        })
        .collect::<EResult<_>>()?;
    let mut rename = |f: usize, n: i64| {
        if n <= 0 {
            Ok(n)
        } else {
            ranks[f].get(&n).copied().ok_or_else(|| EvalError::new("missing optimization rank"))
        }
    };
    let projected = plan.variables.iter().zip(&values).map(|(s, v)| walk(v, &[s], &mut rename)).collect::<EResult<Vec<_>>>()?;
    // Fixed literal anchors are part of the key, so their positions cannot
    // silently change when other live values disappear.
    let anchors = plan
        .anchors
        .iter()
        .enumerate()
        .map(|(f, ns)| {
            ns.iter()
                .map(|n| Ok(Value::Int(rename(f, i64::try_from(*n).map_err(|_| EvalError::new("invalid optimization anchor"))?)?)))
                .collect::<EResult<Vec<_>>>()
                .map(|vs| Value::Tuple(vs.into()))
        })
        .collect::<EResult<Vec<_>>>()?;
    Ok(Value::Tuple(vec![Value::Tuple(projected.into()), Value::Tuple(anchors.into())].into()))
}

fn pairs(v: &Value) -> EResult<Vec<(Value, Value)>> {
    Ok(match v {
        Value::Fcn(ps, _) => ps.to_vec(),
        Value::Tuple(vs) => vs
            .iter()
            .enumerate()
            .map(|(i, v)| {
                Ok((Value::Int(i64::try_from(i + 1).map_err(|_| EvalError::new("tuple index exceeds integer representation"))?), v.clone()))
            })
            .collect::<EResult<_>>()?,
        Value::Record(fs) => fs.iter().map(|(k, v)| (Value::Str(*k), v.clone())).collect(),
        _ => return Err(EvalError::new("expected a function in ordered optimization")),
    })
}

fn walk(v: &Value, shapes: &[&OrderedShape], rename: &mut impl FnMut(usize, i64) -> EResult<i64>) -> EResult<Value> {
    if shapes.iter().all(|s| s.family.is_none() && s.fields.is_empty() && s.key.is_none() && s.value.is_none() && s.element.is_none()) {
        return Ok(v.clone());
    }
    Ok(match v {
        Value::Int(n) => {
            let families: BTreeSet<_> = shapes.iter().filter_map(|s| s.family).collect();
            if families.len() > 1 {
                return Err(EvalError::new("conflicting optimization families"));
            }
            Value::Int(if let Some(f) = families.first() { rename(*f, *n)? } else { *n })
        }
        Value::Set(es) => {
            let children: Vec<_> = shapes.iter().filter_map(|s| s.element.as_deref()).collect();
            Value::set_from(es.iter().map(|v| walk(v, &children, rename)).collect::<EResult<_>>()?)?
        }
        Value::Interval(lo, hi) => {
            let children: Vec<_> = shapes.iter().filter_map(|s| s.element.as_deref()).collect();
            if children.iter().all(|s| s.family.is_none()) {
                return Ok(v.clone());
            }
            Value::set_from((*lo..=*hi).map(|n| walk(&Value::Int(n), &children, rename)).collect::<EResult<_>>()?)?
        }
        Value::Fcn(_, _) | Value::Record(_) | Value::Tuple(_) => {
            let keys: Vec<_> = shapes.iter().filter_map(|s| s.key.as_deref()).collect();
            let mut out = Vec::new();
            for (key, value) in pairs(v)? {
                let mut children: Vec<_> = shapes.iter().filter_map(|s| s.value.as_deref()).collect();
                if let Value::Str(name) = &key {
                    children.extend(shapes.iter().filter_map(|s| s.fields.get(name.as_str())));
                }
                out.push((walk(&key, &keys, rename)?, walk(&value, &children, rename)?));
            }
            Value::fcn_rcd_from_pairs(out)?
        }
        Value::LazySet(_) | Value::LazyFcn(_) => return Err(EvalError::new("unnormalized ordered optimization value")),
        _ => v.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tlx_sema::optimize::OrderedHistory;

    fn family(f: usize) -> OrderedShape {
        OrderedShape { family: Some(f), ..Default::default() }
    }

    #[test]
    fn rank_discards_numeric_gaps_but_keeps_ties_and_anchors() {
        let plan = OrderedPlan { variables: vec![family(0), family(0)], anchors: vec![vec![1]], history: None };
        let key = |a, b| project(&plan, &[Value::Int(a), Value::Int(b)]).unwrap();
        assert_eq!(key(100, 50), key(10, 5));
        assert_ne!(key(100, 100), key(100, 50));
        assert_ne!(key(100, 1), key(100, 2));
        assert_ne!(key(100, 0), key(100, -1));
    }

    #[test]
    fn history_roots_precede_rank_collection_from_payloads() {
        let map = OrderedShape { key: Some(Box::new(family(0))), value: Some(Box::new(family(1))), ..Default::default() };
        let plan = OrderedPlan {
            variables: vec![family(0), family(0), family(1), map],
            anchors: vec![vec![], vec![]],
            history: Some(OrderedHistory { variable: 3, family: 0 }),
        };
        let state = |now, old, uuid, entries: &[(i64, i64)]| {
            vec![
                Value::Int(now),
                Value::Int(old),
                Value::Int(uuid),
                Value::fcn_rcd_from_pairs(entries.iter().map(|(k, v)| (Value::Int(*k), Value::Int(*v))).collect()).unwrap(),
            ]
        };
        let a = state(100, 20, 50, &[(10, 1), (20, 30), (100, 40)]);
        let b = state(10, 2, 5, &[(2, 3), (7, 1000), (10, 4)]);
        assert_eq!(project(&plan, &a).unwrap(), project(&plan, &b).unwrap());
        let c = state(10, 2, 5, &[(2, 4), (10, 3)]);
        assert_ne!(project(&plan, &a).unwrap(), project(&plan, &c).unwrap());
    }
}
