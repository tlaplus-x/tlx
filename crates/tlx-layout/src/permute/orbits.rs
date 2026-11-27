//! Close inferred atom universes under the active model-value permutations.

use std::collections::{HashMap, HashSet};

use tlx_value::{Sym, Value};

use crate::shape::{join_all, map_shape, set_shape};
use crate::Shape;

/// Disjoint orbits of moved model values.
pub struct AtomOrbits(Vec<Shape>);

impl AtomOrbits {
    pub fn from_factors(factors: &[&[Sym]]) -> Self {
        Self(factors.iter().map(|keys| Shape::Atom(keys.iter().copied().map(Value::ModelValue).collect())).collect())
    }

    /// The explicit group contains every non-identity permutation, so the
    /// images of one representative enumerate its entire orbit.
    pub fn from_group(maps: &[HashMap<Sym, Value>]) -> Self {
        let mut seen = HashSet::new();
        let mut orbits = Vec::new();
        for &key in maps.iter().flat_map(HashMap::keys) {
            if seen.insert(key) {
                let mut values = vec![Value::ModelValue(key)];
                for map in maps {
                    if let Some(Value::ModelValue(image)) = map.get(&key) {
                        if seen.insert(*image) {
                            values.push(Value::ModelValue(*image));
                        }
                    }
                }
                values.sort_unstable();
                orbits.push(Shape::Atom(values.into()));
            }
        }
        Self(orbits)
    }

    /// Preserve fixed function domains and container bounds. Rebuild maps
    /// through their checked constructor as expanded keys may exceed its limits.
    pub fn close(&self, shape: &Shape) -> Shape {
        if self.0.is_empty() {
            return shape.clone();
        }
        match shape {
            Shape::Atom(atoms) => {
                let mut result = shape.clone();
                for orbit in &self.0 {
                    if atoms.iter().any(|a| orbit.contains(a)) {
                        result = result.join(orbit);
                    }
                }
                result
            }
            Shape::Record(fields) => Shape::Record(fields.iter().map(|(name, field)| (*name, self.close(field))).collect()),
            Shape::Tuple(parts) => Shape::Tuple(parts.iter().map(|p| self.close(p)).collect()),
            Shape::Union(arms) => join_all(arms.iter().map(|a| self.close(a))),
            Shape::Set { elem, max_card } => set_shape(self.close(elem), *max_card),
            Shape::Seq { elem, max_len } => Shape::Seq { elem: Box::new(self.close(elem)), max_len: *max_len },
            Shape::Fcn { dom, range, witness, key_variants } => {
                Shape::Fcn { dom: dom.clone(), range: Box::new(self.close(range)), witness: *witness, key_variants: key_variants.clone() }
            }
            Shape::Map { key, range, witness } => map_shape(self.close(key), self.close(range), *witness),
            Shape::Never | Shape::Bool | Shape::Int { .. } | Shape::Dyn | Shape::Ref(_) => shape.clone(),
        }
    }
}
