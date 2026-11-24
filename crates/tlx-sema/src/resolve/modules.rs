//! Finding, parsing and registering modules; collecting ASSUMEs.

use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use tlx_front::ast::{self, FileId};

use super::{err, Env, ModIdx, ModInfo, ModuleOrigin, Program, SemaError, SourceFile, Sym, ROOT_CTX};
use crate::builtins::{COMMUNITY_MODULES, STD_MODULES};
use crate::hir::{DefId, RootSymbol};

impl Program {
    /// Parse a source file and register all of its modules (and their nested
    /// modules). Returns the first top-level module.
    pub(super) fn add_module_source(&mut self, path: PathBuf, src: Arc<str>, origin: ModuleOrigin) -> Result<ModIdx, Vec<SemaError>> {
        let file = FileId(self.files.len() as u32);
        self.files.push(SourceFile::with_origin(path.clone(), src.clone(), origin));
        let ms =
            tlx_front::parse::parse_modules(&src, file).map_err(|ds| ds.into_iter().map(|d| err(d.span, d.message)).collect::<Vec<_>>())?;
        // SANY: the first module of a file must be named after the file.
        if let (Some(m), Some(stem)) = (ms.first(), path.file_stem().and_then(|s| s.to_str())) {
            if origin == ModuleOrigin::User && *m.name.name != *stem {
                let msg = format!("File name '{stem}' does not match the name '{}' of the top level module it contains.", m.name.name);
                return Err(vec![err(m.name.span, msg)]);
            }
        }
        let std = origin == ModuleOrigin::Stdlib;
        let mut first = None;
        for m in ms {
            let idx = self.register_module(m, std, None);
            first.get_or_insert(idx);
        }
        Ok(first.expect("parse_modules returns at least one module"))
    }

    fn register_module(&mut self, m: ast::Module, std: bool, parent: Option<ModIdx>) -> ModIdx {
        let idx = self.mods.len();
        let name: Arc<str> = m.name.name.clone();
        let ast = Arc::new(m);
        // Native overrides apply by module name, wherever the module was found (as in TLC).
        let std = std || STD_MODULES.iter().any(|(n, _)| **n == *name);
        self.mods.push(ModInfo { name: name.clone(), ast: ast.clone(), std, parent });
        if parent.is_none() {
            self.mod_by_name.entry(name).or_insert(idx);
        }
        for u in &ast.units {
            if let ast::Unit::Module(nested) = u {
                self.register_module(nested.clone(), std, Some(idx));
            }
        }
        idx
    }

    /// The nested module named `name` of `m` (or of its ancestors).
    pub(super) fn find_nested_module(&self, m: ModIdx, name: &str) -> Option<ModIdx> {
        let mut cur = Some(m);
        while let Some(c) = cur {
            if let Some(n) = (0..self.mods.len()).find(|&i| self.mods[i].parent == Some(c) && &*self.mods[i].name == name) {
                return Some(n);
            }
            cur = self.mods[c].parent;
        }
        None
    }

    /// The module instantiated by `INSTANCE name` appearing in module `m`:
    /// a nested module of `m` (or of its ancestors), or a top-level module.
    pub(super) fn find_instance_module(&mut self, m: ModIdx, name: &ast::Ident) -> Option<ModIdx> {
        self.find_nested_module(m, &name.name).or_else(|| self.find_module(name))
    }

    /// The module named `name`, loading it if necessary.
    ///
    /// Lookup order (TLC's `SimpleFilenameToStream`: the user directory and
    /// the `-DTLA-Library` paths, then the standard modules in its jar, then
    /// the classpath, where the CommunityModules jar is): the root module's
    /// directory, the `-I` search paths, the bundled standard modules, the
    /// bundled CommunityModules, then the late paths (`TLX_CLASSPATH`,
    /// mirroring TLC's classpath after its own modules).
    pub(super) fn find_module(&mut self, name: &ast::Ident) -> Option<ModIdx> {
        if let Some(&m) = self.mod_by_name.get(&name.name) {
            return Some(m);
        }
        let file_name = format!("{}.tla", name.name);
        let dirs = self.search_paths.clone();
        if let Some(m) = self.load_from_dirs(&dirs, &file_name) {
            return m;
        }
        if let Some(&(_, src)) = STD_MODULES.iter().find(|(n, _)| **n == *name.name) {
            return self.load_module_file(PathBuf::from(format!("<stdlib>/{file_name}")), Arc::from(src), ModuleOrigin::Stdlib);
        }
        if let Some(&(_, src)) = COMMUNITY_MODULES.iter().find(|(n, _)| **n == *name.name) {
            return self.load_module_file(PathBuf::from(format!("<community>/{file_name}")), Arc::from(src), ModuleOrigin::Community);
        }
        let late = self.late_paths.clone();
        if let Some(m) = self.load_from_dirs(&late, &file_name) {
            return m;
        }
        self.errors.push(err(name.span, format!("cannot find module {}", name.name)));
        None
    }

    /// Load `file_name` from the first directory containing it. `None` if no
    /// directory has it; `Some(None)` if it was found but failed to parse.
    fn load_from_dirs(&mut self, dirs: &[PathBuf], file_name: &str) -> Option<Option<ModIdx>> {
        for dir in dirs {
            let p = Path::new(dir).join(file_name);
            if let Ok(src) = std::fs::read_to_string(&p) {
                return Some(self.load_module_file(p, src.into(), ModuleOrigin::User));
            }
        }
        None
    }

    fn load_module_file(&mut self, path: PathBuf, src: Arc<str>, origin: ModuleOrigin) -> Option<ModIdx> {
        match self.add_module_source(path, src, origin) {
            Ok(m) => Some(m),
            Err(es) => {
                self.errors.extend(es);
                None
            }
        }
    }

    /// TLC's (SANY's) module orders, loading every module the root depends
    /// on through EXTENDS and INSTANCE: the files in parse order
    /// (breadth-first from the root, as SANY reads them) and in semantic
    /// order (dependencies first, as SANY analyses them). TLC interns
    /// identifier tokens in the former order and string literals in the
    /// latter (docs/tlc-semantics.md §1.3).
    pub fn sany_file_orders(&mut self) -> (Vec<FileId>, Vec<FileId>) {
        let root = self.root_mod;
        let mut parse = vec![root];
        let mut i = 0;
        while i < parse.len() {
            for d in self.module_deps(parse[i], parse[i] == root) {
                if !parse.contains(&d) {
                    parse.push(d);
                }
            }
            i += 1;
        }
        let mut semantic = Vec::new();
        self.postorder(root, true, &mut Vec::new(), &mut semantic);
        let files = |p: &Program, ms: &[ModIdx]| {
            let mut fs: Vec<FileId> = Vec::new();
            for &m in ms {
                let f = p.mods[m].ast.span.file;
                if !fs.contains(&f) {
                    fs.push(f);
                }
            }
            fs
        };
        (files(self, &parse), files(self, &semantic))
    }

    /// The constants and definitions TLC evaluates at startup, in its order
    /// (`SpecProcessor.processConstantDefns`), before the assumptions and the
    /// initial states. It walks the modules in semantic order (SANY's
    /// `ExternalModuleTable`, dependencies first), skipping a module that is
    /// instantiated and declares constants or variables
    /// (`ModuleNode.processConstantDefns`). In each module it evaluates the
    /// definitions substituted for 0-ary constants (`C <- Def`), then the
    /// module's 0-ary definitions in declaration order (`getOpDefs`; those of
    /// extended modules were evaluated with their module), then its nested
    /// modules. TLC only keeps the constant-level ones and ignores evaluation
    /// errors; the caller filters by level. Evaluating a definition interns
    /// the strings it creates, so this order is part of the string order
    /// (tlc-semantics.md §1.3).
    pub fn tlc_constant_defn_order(&mut self) -> Vec<RootSymbol> {
        let mut mods = Vec::new();
        self.postorder(self.root_mod, true, &mut Vec::new(), &mut mods);
        // `isInstantiated`: the target of an INSTANCE anywhere in the spec.
        let mut instantiated = Vec::new();
        for m in 0..self.mods.len() {
            for u in &self.mods[m].ast.units {
                if let ast::Unit::Instance(i) = u {
                    if let Some(t) = self.find_nested_module(m, &i.module.name).or_else(|| self.mod_by_name.get(&i.module.name).copied()) {
                        instantiated.push(t);
                    }
                }
            }
        }
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        for m in mods {
            self.constant_defns_of(m, &instantiated, &mut seen, &mut out);
        }
        out
    }

    fn constant_defns_of(&mut self, m: ModIdx, instantiated: &[ModIdx], seen: &mut HashSet<DefId>, out: &mut Vec<RootSymbol>) {
        if instantiated.contains(&m) && self.has_decls(m, &mut Vec::new()) {
            return;
        }
        let Some(&sc) = self.scope_of.get(&(ROOT_CTX, m)) else { return };
        let ast = self.mods[m].ast.clone();
        for u in &ast.units {
            if let ast::Unit::Constants(decls) = u {
                for d in decls.iter().filter(|d| d.arity == 0) {
                    if let Some(Sym::Const(c)) = self.scopes[sc].names.get(&d.name.name) {
                        out.push(RootSymbol::Const(*c));
                    }
                }
            }
        }
        self.unit_defns(sc, m, true, &mut Vec::new(), seen, out);
        let nested: Vec<ModIdx> = (0..self.mods.len()).filter(|&i| self.mods[i].parent == Some(m)).collect();
        for n in nested {
            self.constant_defns_of(n, instantiated, seen, out);
        }
    }

    /// The 0-ary definitions of module `m` as they appear in scope `sc` (the
    /// module's own scope, or one that imports them through INSTANCE), in
    /// declaration order: a 0-ary named INSTANCE contributes the instance's
    /// definitions `I!D` where it appears, as in SANY's module context, so
    /// do an anonymous INSTANCE and (for an instance) the EXTENDS of the
    /// instantiated module.
    fn unit_defns(
        &mut self,
        sc: usize,
        m: ModIdx,
        own: bool,
        mods: &mut Vec<ModIdx>,
        seen: &mut HashSet<DefId>,
        out: &mut Vec<RootSymbol>,
    ) {
        if mods.contains(&m) {
            return;
        }
        mods.push(m);
        let ast = self.mods[m].ast.clone();
        if !own {
            for e in &ast.extends {
                if let Some(&em) = self.mod_by_name.get(&e.name) {
                    self.unit_defns(sc, em, false, mods, seen, out);
                }
            }
        }
        for u in &ast.units {
            let name = match u {
                ast::Unit::OpDef(d) if d.params.is_empty() && (own || !d.local) => &d.name.name,
                ast::Unit::FnDef(d) if own || !d.local => &d.name.name,
                ast::Unit::Instance(i) if i.params.is_empty() && (own || !i.local) => {
                    let Some(im) = self.find_nested_module(m, &i.module.name).or_else(|| self.mod_by_name.get(&i.module.name).copied())
                    else {
                        continue;
                    };
                    match &i.name {
                        Some(n) => {
                            let Some(&Sym::Instance(id)) = self.scopes[sc].names.get(&n.name) else { continue };
                            let Some(t) = self.named_instance(id) else { continue };
                            let isc = self.scope(t.0, t.1);
                            self.unit_defns(isc, im, false, &mut Vec::new(), seen, out);
                        }
                        None => self.unit_defns(sc, im, false, mods, seen, out),
                    }
                    continue;
                }
                _ => continue,
            };
            if let Some(&Sym::Def(d)) = self.scopes[sc].names.get(name) {
                if seen.insert(d) {
                    out.push(RootSymbol::Def(d));
                }
            }
        }
    }

    fn postorder(&mut self, m: ModIdx, is_root: bool, seen: &mut Vec<ModIdx>, out: &mut Vec<ModIdx>) {
        if seen.contains(&m) {
            return;
        }
        seen.push(m);
        for d in self.module_deps(m, is_root) {
            self.postorder(d, false, seen, out);
        }
        out.push(m);
    }

    /// The modules `m` (with its nested modules) depends on, as SANY lists
    /// them: EXTENDS, then INSTANCEs in textual order. TLC adds its trace
    /// module (which extends TLCExt) to the root's dependencies.
    fn module_deps(&mut self, m: ModIdx, is_root: bool) -> Vec<ModIdx> {
        let ast = self.mods[m].ast.clone();
        let mut names: Vec<ast::Ident> = Vec::new();
        fn walk(md: &ast::Module, names: &mut Vec<ast::Ident>, instances: &mut Vec<ast::Ident>, nested: &mut Vec<Arc<str>>) {
            names.extend(md.extends.iter().cloned());
            for u in &md.units {
                match u {
                    ast::Unit::Instance(i) => instances.push(i.module.clone()),
                    ast::Unit::Module(inner) => {
                        nested.push(inner.name.name.clone());
                        walk(inner, names, instances, nested);
                    }
                    _ => {}
                }
            }
        }
        let mut instances = Vec::new();
        let mut nested = Vec::new();
        walk(&ast, &mut names, &mut instances, &mut nested);
        if is_root {
            names.push(ast::Ident { name: "TLCExt".into(), span: ast.name.span });
        }
        names.extend(instances);
        let mut out = Vec::new();
        for n in names {
            // Nested modules are part of this one.
            if nested.contains(&n.name) {
                continue;
            }
            if let Some(d) = self.find_module(&n) {
                if d != m && !out.contains(&d) {
                    out.push(d);
                }
            }
        }
        out
    }

    /// Whether the module (or its EXTENDS closure) declares constants/variables.
    pub(super) fn has_decls(&mut self, m: ModIdx, seen: &mut Vec<ModIdx>) -> bool {
        if seen.contains(&m) {
            return false;
        }
        seen.push(m);
        let ast = self.mods[m].ast.clone();
        if ast.units.iter().any(|u| matches!(u, ast::Unit::Constants(_) | ast::Unit::Variables(_))) {
            return true;
        }
        for e in &ast.extends {
            if let Some(em) = self.find_module(e) {
                if self.has_decls(em, seen) {
                    return true;
                }
            }
        }
        false
    }

    /// Resolve the ASSUMEs of `m` and its EXTENDS closure (in the root context).
    pub(super) fn collect_assumes(&mut self, m: ModIdx, seen: &mut Vec<ModIdx>) {
        if seen.contains(&m) {
            return;
        }
        seen.push(m);
        let ast = self.mods[m].ast.clone();
        for e in &ast.extends {
            if let Some(em) = self.mod_by_name.get(&e.name).copied() {
                self.collect_assumes(em, seen);
            }
        }
        for u in &ast.units {
            if let ast::Unit::Assume { body, .. } = u {
                if let Ok(e) = self.expr(&mut Env::new(ROOT_CTX, m), body) {
                    self.assumes.push(e);
                }
            }
        }
        self.drain_worklist();
    }
}
