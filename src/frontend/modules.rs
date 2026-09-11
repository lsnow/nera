//! Closed module graph and lexical declaration scopes. No source concatenation,
//! independent units, filesystem discovery, or trusted imported summaries.
use super::{AstEnumVariantPayload, AstFile, AstType, FrontendFailure};
use crate::{ByteSpan, VirSourceId};
use std::collections::{BTreeMap, BTreeSet};

pub(super) struct ModuleScope {
    pub path: String,
    aliases: BTreeMap<String, String>,
}

pub(super) struct ModuleGraph {
    pub scopes: Vec<ModuleScope>,
    pub entry_module: usize,
    pub entry_name: String,
}

impl ModuleGraph {
    pub fn single(ast: &AstFile) -> Result<Self, FrontendFailure> {
        let path = ast.module.clone().unwrap_or_else(|| "crate".into());
        let entry = ast
            .functions
            .first()
            .ok_or_else(|| FrontendFailure::elaboration(ast.span, "entry function is missing"))?
            .name
            .clone();
        Self::build(&[(path.clone(), ast)], &format!("{path}::{entry}"))
    }

    pub fn build(files: &[(String, &AstFile)], entry: &str) -> Result<Self, FrontendFailure> {
        let mut symbols = BTreeMap::new();
        let paths: BTreeMap<_, _> = files
            .iter()
            .enumerate()
            .map(|(i, (path, _))| (path.as_str(), i))
            .collect();
        for (i, (path, ast)) in files.iter().enumerate() {
            if ast.module.as_ref().is_some_and(|declared| declared != path) {
                return Err(at(
                    i,
                    ast.span,
                    "module declaration does not match the explicit source mapping",
                ));
            }
            for (name, span) in ast
                .structs
                .iter()
                .map(|d| (&d.name, d.span))
                .chain(ast.enums.iter().map(|d| (&d.name, d.span)))
                .chain(ast.functions.iter().map(|d| (&d.name, d.span)))
            {
                let key = format!("{path}::{name}");
                if symbols
                    .insert(key, (i, ast.public.contains(name)))
                    .is_some()
                {
                    return Err(at(i, span, "duplicate declaration/export within module"));
                }
            }
        }
        let mut scopes = Vec::new();
        let mut edges = vec![BTreeSet::new(); files.len()];
        for (i, (path, ast)) in files.iter().enumerate() {
            let mut aliases: BTreeMap<String, String> = symbols
                .iter()
                .filter(|(_, (owner, _))| *owner == i)
                .map(|(key, _)| (key.rsplit("::").next().unwrap().to_owned(), key.clone()))
                .collect();
            for (import, span) in &ast.imports {
                let Some((owner_path, name)) = import.rsplit_once("::") else {
                    return Err(at(i, *span, "use requires a module-qualified declaration"));
                };
                let Some(&owner) = paths.get(owner_path) else {
                    return Err(at(
                        i,
                        *span,
                        "missing module dependency in explicit source set",
                    ));
                };
                let Some((_, public)) = symbols.get(import) else {
                    return Err(at(
                        i,
                        *span,
                        "imported declaration is missing (re-exports are not supported)",
                    ));
                };
                if !public && owner != i {
                    return Err(at(i, *span, "cannot import a private declaration"));
                }
                if aliases.insert(name.to_owned(), import.clone()).is_some() {
                    return Err(at(
                        i,
                        *span,
                        "ambiguous or duplicate import conflicts with a local name",
                    ));
                }
                edges[i].insert(owner);
            }
            scopes.push(ModuleScope {
                path: path.clone(),
                aliases,
            });
        }
        // Iterative dependency removal: module cycles are a capability boundary,
        // not a substitute for the independent call-SCC or layout checks.
        let mut pending: BTreeSet<_> = (0..files.len()).collect();
        while !pending.is_empty() {
            let ready: Vec<_> = pending
                .iter()
                .copied()
                .filter(|i| edges[*i].iter().all(|d| !pending.contains(d)))
                .collect();
            if ready.is_empty() {
                let i = *pending.first().unwrap();
                let mut failure = FrontendFailure::unsupported(
                    files[i].1.span,
                    "module dependency cycles are not supported; function recursion is independent",
                );
                failure.source = Some(VirSourceId::new(i as u32));
                return Err(failure);
            }
            for i in ready {
                pending.remove(&i);
            }
        }
        // Public representations and signatures may not expose private nominal
        // types, including those under aggregates/references. Opaque types wait
        // for stage 8; fields of a public struct are public in this first slice.
        for (i, (_, ast)) in files.iter().enumerate() {
            for f in &ast.functions {
                let check = |ty: &AstType, span| {
                    check_public_type(ty, span, i, &scopes, &symbols, &f.generics)
                };
                if ast.public.contains(&f.name) {
                    check(&f.return_type, f.span)?;
                    for p in &f.parameters {
                        check(&p.ty, p.span)?;
                    }
                }
            }
            for s in &ast.structs {
                let check = |ty: &AstType, span| {
                    check_public_type(ty, span, i, &scopes, &symbols, &s.generics)
                };
                if ast.public.contains(&s.name) {
                    for f in &s.fields {
                        check(&f.ty, f.span)?;
                    }
                }
            }
            for e in &ast.enums {
                let check = |ty: &AstType, span| {
                    check_public_type(ty, span, i, &scopes, &symbols, &e.generics)
                };
                if ast.public.contains(&e.name) {
                    for v in &e.variants {
                        match &v.payload {
                            AstEnumVariantPayload::Unit => {}
                            AstEnumVariantPayload::Tuple(fields) => {
                                for f in fields {
                                    check(&f.ty, f.span)?;
                                }
                            }
                            AstEnumVariantPayload::Named(fields) => {
                                for f in fields {
                                    check(&f.ty, f.span)?;
                                }
                            }
                        }
                    }
                }
            }
        }
        let Some((module, name)) = entry.rsplit_once("::") else {
            return Err(at(0, files[0].1.span, "entry must name module::function"));
        };
        let Some(&entry_module) = paths.get(module) else {
            return Err(at(0, files[0].1.span, "entry module is missing"));
        };
        if !files[entry_module]
            .1
            .functions
            .iter()
            .any(|f| f.name == name)
        {
            return Err(at(
                entry_module,
                files[entry_module].1.span,
                "entry function is missing",
            ));
        }
        Ok(Self {
            scopes,
            entry_module,
            entry_name: name.to_owned(),
        })
    }
    pub fn key(&self, module: usize, name: &str) -> String {
        if let Some(key) = name.strip_prefix('@') {
            return key.to_owned();
        }
        self.scopes[module]
            .aliases
            .get(name)
            .cloned()
            .unwrap_or_else(|| self.declared_key(module, name))
    }
    pub fn declared_key(&self, module: usize, name: &str) -> String {
        format!("{}::{name}", self.scopes[module].path)
    }
}

fn check_public_type(
    ty: &AstType,
    span: ByteSpan,
    i: usize,
    scopes: &[ModuleScope],
    symbols: &BTreeMap<String, (usize, bool)>,
    parameters: &[super::AstGenericParameter],
) -> Result<(), FrontendFailure> {
    match ty {
        AstType::Named(name) => {
            if parameters
                .iter()
                .any(|p| matches!(p, super::AstGenericParameter::Type(n) if n == name))
            {
                return Ok(());
            }
            let key = scopes[i]
                .aliases
                .get(name)
                .ok_or_else(|| at(i, span, "public interface contains an unresolved type"))?;
            if !symbols[key].1 {
                return Err(at(
                    i,
                    span,
                    "private type escapes through a public interface",
                ));
            }
        }
        AstType::Applied { name, arguments } => {
            check_public_type(
                &AstType::Named(name.clone()),
                span,
                i,
                scopes,
                symbols,
                parameters,
            )?;
            for arg in arguments {
                if let super::AstGenericArgument::Type(ty) = arg {
                    if matches!(ty, AstType::Named(name) if parameters.iter().any(|p| matches!(p, super::AstGenericParameter::Const(n) if n == name)))
                    {
                        continue;
                    }
                    check_public_type(ty, span, i, scopes, symbols, parameters)?;
                }
            }
        }
        AstType::ConstArray {
            element: pointee, ..
        }
        | AstType::Reference { pointee, .. }
        | AstType::Slice { element: pointee }
        | AstType::Array {
            element: pointee, ..
        } => check_public_type(pointee, span, i, scopes, symbols, parameters)?,
        AstType::Tuple(types) => {
            for ty in types {
                check_public_type(ty, span, i, scopes, symbols, parameters)?;
            }
        }
        _ => {}
    }
    Ok(())
}

pub(super) fn at(i: usize, span: ByteSpan, message: &'static str) -> FrontendFailure {
    let mut failure = FrontendFailure::elaboration(span, message);
    failure.source = Some(VirSourceId::new(i as u32));
    failure
}
