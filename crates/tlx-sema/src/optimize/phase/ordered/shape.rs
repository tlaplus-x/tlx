//! Structural provenance. Joins retain every possible numeric origin; they
//! never infer a property merely because it appears in an invariant.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Shape {
    pub family: Option<usize>,
    pub numbers: BTreeSet<i128>,
    pub integer: bool,
    pub opaque: bool,
    pub fields: BTreeMap<Arc<str>, Shape>,
    pub key: Option<Box<Shape>>,
    pub value: Option<Box<Shape>>,
    pub element: Option<Box<Shape>>,
}

impl Shape {
    pub fn number(n: i128) -> Self {
        Self { numbers: BTreeSet::from([n]), ..Self::default() }
    }
    pub fn family(family: usize) -> Self {
        Self { family: Some(family), ..Self::default() }
    }
    pub fn plain() -> Self {
        Self { opaque: true, ..Self::default() }
    }
    pub fn integer() -> Self {
        Self { integer: true, ..Self::default() }
    }
    pub fn set(element: Self) -> Self {
        Self { element: Some(Box::new(element)), ..Self::default() }
    }
    pub fn function(key: Self, value: Self) -> Self {
        Self { key: Some(Box::new(key)), value: Some(Box::new(value)), ..Self::default() }
    }
    pub fn colored(&self) -> bool {
        self.family.is_some()
            || self.fields.values().any(Self::colored)
            || [&self.key, &self.value, &self.element].into_iter().flatten().any(|s| s.colored())
    }
    pub fn has_family(&self, family: usize) -> bool {
        self.family == Some(family)
            || self.fields.values().any(|s| s.has_family(family))
            || [&self.key, &self.value, &self.element].into_iter().flatten().any(|s| s.has_family(family))
    }
    pub fn join(&mut self, other: &Self) -> Option<()> {
        if self.family.is_some() && other.family.is_some() && self.family != other.family {
            return None;
        }
        self.family = self.family.or(other.family);
        self.numbers.extend(&other.numbers);
        if self.numbers.len() > 64 {
            self.numbers.clear();
            self.integer = true;
        }
        self.integer |= other.integer;
        self.opaque |= other.opaque;
        if self.family.is_some() && (self.integer || self.opaque) {
            return None;
        }
        for (name, shape) in &other.fields {
            self.fields.entry(name.clone()).or_default().join(shape)?;
        }
        for (a, b) in [(&mut self.key, &other.key), (&mut self.value, &other.value), (&mut self.element, &other.element)] {
            if let Some(b) = b {
                a.get_or_insert_with(Default::default).join(b)?;
            }
        }
        // Records and general functions are the same TLA+ values. Account
        // for generic range information at every named field as well.
        if let Some(value) = &self.value {
            for field in self.fields.values_mut() {
                field.join(value)?;
            }
        }
        if !self.fields.is_empty() && self.key.as_ref().is_some_and(|s| s.colored()) {
            return None;
        }
        if self.opaque && self.colored() {
            return None;
        }
        Some(())
    }
    pub fn joined(mut self, other: &Self) -> Option<Self> {
        self.join(other)?;
        Some(self)
    }
    pub fn range(&self) -> Option<Self> {
        self.container()?;
        let mut out = self.value.as_deref().cloned().unwrap_or_default();
        for value in self.fields.values() {
            out.join(value)?;
        }
        Some(out)
    }
    pub fn field(&self, name: &str) -> Option<Self> {
        self.container()?;
        let mut out = self.fields.get(name).cloned().unwrap_or_default();
        if let Some(value) = &self.value {
            out.join(value)?;
        }
        Some(out)
    }
    // Unknown pure operators can return containers, so opaque output is
    // not an empty container. Never erase that uncertainty through a read.
    pub fn container(&self) -> Option<()> {
        (!self.opaque && !self.integer && self.family.is_none() && self.numbers.is_empty()).then_some(())
    }
    pub fn elements(&self) -> Option<Self> {
        self.container()?;
        Some(self.element.as_deref().cloned().unwrap_or_default())
    }
    pub fn anchors(&self, initial: &[i128], out: &mut [BTreeSet<i128>]) -> Option<()> {
        if let Some(family) = self.family {
            if self.numbers.iter().any(|n| *n > initial[family]) {
                return None;
            }
            out[family].extend(self.numbers.iter().filter(|n| **n > 0));
        }
        for child in self.fields.values() {
            child.anchors(initial, out)?;
        }
        for child in [&self.key, &self.value, &self.element].into_iter().flatten() {
            child.anchors(initial, out)?;
        }
        Some(())
    }
}
