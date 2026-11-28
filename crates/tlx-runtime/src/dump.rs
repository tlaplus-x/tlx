//! TLC's `-dump`: write every distinct reachable state to a file, as text
//! (`State n:` blocks) or as a GraphViz graph (`-dump dot[,actionlabels]
//! [,colorize]`). A `DumpObserver` watches one search
//! (`explore_observed`) and records the states (and transitions) as the
//! search finds them.

use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;
use std::sync::Arc;
use tlx_base::hash::IdMap;

use parking_lot::Mutex;

use crate::explore::SearchObserver;
use crate::model::Model;

#[derive(Clone, Copy, Debug, Default)]
pub struct DumpOptions {
    /// GraphViz output instead of text.
    pub dot: bool,
    /// Label transitions with their action.
    pub action_labels: bool,
    /// Color transitions by action.
    pub colorize: bool,
    /// `-view`: render the states through the `.cfg` `VIEW` (the caller
    /// provides the rendering; see `DumpObserver::create_with`).
    pub use_view: bool,
    /// `-difftrace`: label a non-initial GraphViz node with the fields that
    /// differ from its parent, keeping the full state in `tooltip`.
    pub difftrace: bool,
    /// What reduced the search (`symmetry`), noted at the top of the file:
    /// the dump is of the reduced graph.
    pub reduced: Option<&'static str>,
}

/// How a state of a `-dump` is rendered: the full text TLC prints for it
/// (through `-view` when the caller's renderer applies it). A `-difftrace`
/// label is derived from the texts of a state and its parent.
type StateRenderer<'a, S> = Box<dyn Fn(&S) -> String + Send + Sync + 'a>;

struct Out {
    w: BufWriter<File>,
    /// BFS level of each state written (also the set of written states).
    level: IdMap<u32>,
    /// States per level, in discovery order (dot ranks).
    ranks: Vec<Vec<u64>>,
    /// The full texts of the states of the last two levels, for
    /// `-difftrace` (a state's parent is at the level before it).
    texts: LevelTexts,
    err: Option<std::io::Error>,
}

impl Out {
    fn write(&mut self, s: &str) {
        if self.err.is_none() {
            if let Err(e) = self.w.write_all(s.as_bytes()) {
                self.err = Some(e);
            }
        }
    }
}

/// The full texts of the recorded states, by dump level (the last two
/// levels kept).
#[derive(Default)]
struct LevelTexts {
    level: Option<u32>,
    previous: IdMap<Arc<str>>,
    current: IdMap<Arc<str>>,
}

impl LevelTexts {
    fn insert(&mut self, level: u32, fp: u64, text: String) {
        match self.level {
            None => self.level = Some(level),
            Some(l) if level > l => {
                self.previous = std::mem::take(&mut self.current);
                self.level = Some(level);
            }
            // (A state recorded below the retained level cannot be the
            // parent of a later state.)
            Some(l) if level < l => return,
            _ => {}
        }
        self.current.insert(fp, Arc::from(text));
    }

    fn get(&self, level: u32, fp: u64) -> Option<&Arc<str>> {
        let current = self.level?;
        if level == current {
            self.current.get(&fp)
        } else if level + 1 == current {
            self.previous.get(&fp)
        } else {
            None
        }
    }
}

/// The `-difftrace` label of a state from its full text and its parent's:
/// the lines that differ when both show the same fields, else the whole
/// text (a representation that changed shape, e.g. a VIEW that failed to
/// evaluate on one of them).
fn diff_label(full: &str, prev: &str) -> String {
    let lines: Vec<&str> = full.lines().collect();
    let old: Vec<&str> = prev.lines().collect();
    if lines.len() != old.len() {
        return full.to_owned();
    }
    lines.iter().zip(&old).filter(|(line, old)| line != old).map(|(line, _)| *line).collect::<Vec<_>>().join("\n")
}

pub struct DumpObserver<'a, M: Model> {
    model: &'a M,
    opts: DumpOptions,
    /// The full state rendering, when the caller supplies it (`-view`).
    render: Option<StateRenderer<'a, M::State>>,
    out: Mutex<Out>,
}

/// A string as a GraphViz label.
fn dot_label(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n")
}

impl<'a, M: Model> DumpObserver<'a, M> {
    /// The dump of a search of `model` to `path`.
    pub fn create(model: &'a M, path: &Path, opts: DumpOptions) -> std::io::Result<DumpObserver<'a, M>> {
        Self::create_with(model, path, opts, None)
    }

    /// Like `create`, rendering each state's full text with `render`: the
    /// `-view` presentation (the runtime does not know the model's VIEW or
    /// variables; `tlx-eval`'s `InterpModel` does). `-difftrace` labels are
    /// derived from these texts, so they also work when the search resolves
    /// representatives at the end of a level (several workers) and does not
    /// hand the observer the parent state itself.
    pub fn create_with(
        model: &'a M,
        path: &Path,
        opts: DumpOptions,
        render: Option<StateRenderer<'a, M::State>>,
    ) -> std::io::Result<DumpObserver<'a, M>> {
        let mut out = Out {
            w: BufWriter::new(File::create(path)?),
            level: IdMap::default(),
            ranks: Vec::new(),
            texts: LevelTexts::default(),
            err: None,
        };
        if let Some(what) = opts.reduced {
            let note = format!("reduced by {what}; use -tlc for the full graph");
            out.write(&if opts.dot { format!("/* {note} */\n") } else { format!("\\* {note}\n") });
        }
        if opts.dot {
            out.write("strict digraph DiskGraph {\nnode [shape=box,style=rounded]\n");
            if opts.colorize {
                out.write("edge [colorscheme=\"paired12\"]\n");
            }
            out.write("nodesep=0.35;\nsubgraph cluster_graph {\ncolor=\"white\";\n");
        }
        Ok(DumpObserver { model, opts, render, out: Mutex::new(out) })
    }

    /// Complete the file (dot: the ranks of the levels).
    pub fn finish(self) -> std::io::Result<()> {
        let mut out = self.out.into_inner();
        if self.opts.dot {
            for rank in std::mem::take(&mut out.ranks) {
                let ids: String = rank.iter().rev().map(|fp| format!("{};", *fp as i64)).collect();
                out.write(&format!("{{rank = same; {ids}}}\n"));
            }
            out.write("}\n");
            if self.opts.colorize {
                // A legend of the action colors (by name, as TLC).
                out.write("subgraph cluster_legend {graph[style=bold];label = \"Next State Actions\" style=\"solid\"\n");
                out.write("node [ labeljust=\"l\",colorscheme=\"paired12\",style=filled,shape=record ]\n");
                let mut names: Vec<(&String, usize)> = Vec::new();
                for (i, n) in self.model.action_names().iter().enumerate() {
                    if !names.iter().any(|(m, _)| *m == n) {
                        names.push((n, i));
                    }
                }
                names.sort();
                for (n, i) in names {
                    out.write(&format!("{n} [label=\"{}\",fillcolor={}]\n", dot_label(n), i + 2));
                }
                out.write("}");
            }
            out.write("}");
        }
        if let Some(e) = out.err.take() {
            return Err(e);
        }
        out.w.flush()
    }

    /// Record state `s` (fingerprint `fp`, at depth `depth`) the search
    /// reports as new (or outside the model), generated from the state of
    /// fingerprint `parent`: at the level after its parent's (the parent's
    /// as recorded: a state is recorded once, at the level it was first
    /// found at); without a parent (an initial state, or a representative
    /// chosen at the end of a level), at the level of its depth.
    fn record(&self, s: &M::State, fp: u64, depth: u32, parent: Option<u64>) {
        let init = depth == 1;
        let mut out = self.out.lock();
        let level = match parent {
            Some(p) => out.level.get(&p).map_or(0, |l| *l + 1),
            None => depth - 1,
        };
        if out.level.contains_key(&fp) {
            return;
        }
        out.level.insert(fp, level);
        if out.ranks.len() <= level as usize {
            out.ranks.resize(level as usize + 1, Vec::new());
        }
        out.ranks[level as usize].push(fp);
        let full = match &self.render {
            Some(render) => render(s),
            None => self.model.render(s),
        };
        let diff = self.opts.dot && self.opts.difftrace;
        let label = if diff {
            // (The parent's recorded level, which the retained texts are
            // keyed by; a parent outside the last two levels is not diffed.)
            let prev = parent.and_then(|p| out.level.get(&p).and_then(|parent_level| out.texts.get(*parent_level, p)).cloned());
            match prev {
                Some(prev) => diff_label(&full, &prev),
                None => full.clone(),
            }
        } else {
            full.clone()
        };
        if diff {
            out.texts.insert(level, fp, full.clone());
        }
        if self.opts.dot {
            let label = dot_label(&label);
            let line = if init {
                format!("{} [label=\"{label}\",style = filled]\n", fp as i64)
            } else {
                format!("{} [label=\"{label}\",tooltip=\"{}\"];\n", fp as i64, dot_label(&full))
            };
            out.write(&line);
        } else {
            let n = out.level.len();
            out.write(&format!("State {n}:\n{full}\n\n"));
        }
    }
}

impl<M: Model> SearchObserver<M::State> for DumpObserver<'_, M> {
    fn needs_parent_fingerprint(&self) -> bool {
        // (`-difftrace` labels need the parent of a representative that the
        // ordered search resolves at the end of a level.)
        self.opts.dot && self.opts.difftrace
    }

    fn on_new_state(&self, s: &M::State, fp: u64, depth: u32, parent: Option<u64>) {
        self.record(s, fp, depth, parent);
    }

    fn on_edge(&self, from: u64, to: u64, a: u32) {
        if !self.opts.dot {
            return;
        }
        let names = self.model.action_names();
        let (label, color) = match (self.opts.action_labels, self.opts.colorize) {
            (true, true) => (names[a as usize].clone(), (a + 2).to_string()),
            (true, false) => (names[a as usize].clone(), "black".to_string()),
            (false, true) => (String::new(), (a + 2).to_string()),
            (false, false) => (String::new(), "black".to_string()),
        };
        let line = format!("{} -> {} [label=\"{}\",color=\"{color}\",fontcolor=\"{color}\"];\n", from as i64, to as i64, dot_label(&label));
        self.out.lock().write(&line);
    }
}
