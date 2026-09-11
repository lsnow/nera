//! Deterministic text projection of an immutable preview. No I/O, verification,
//! replay, SummaryAudit construction, or resource-state mutation.
mod condition;
mod source;
use super::*;
use crate::{
    BorrowProjection, BorrowResultRelation, BorrowSliceBound, ByteSpan, ObligationStatus,
    VerifierFinding, VirFunctionId, VirLocation, VirOriginKind, VirSourceSpan,
};
use condition::condition;
use source::{SourceLines, visible};
use std::fmt::Write;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TextReportMode {
    #[default]
    Summary,
    Explain,
}

/// Render the existing result without changing its verdict. Text is experimental,
/// not a stable machine format. Columns count Unicode scalars (not terminal cells).
pub fn render_text(preview: &VerificationPreview, mode: TextReportMode) -> String {
    let mut renderer = Renderer {
        preview,
        explain: mode == TextReportMode::Explain,
        source: preview.source().map(SourceLines::new),
        out: String::new(),
    };
    renderer.render();
    renderer.out
}

struct Renderer<'a> {
    preview: &'a VerificationPreview,
    explain: bool,
    source: Option<SourceLines<'a>>,
    out: String,
}

impl Renderer<'_> {
    fn render(&mut self) {
        writeln!(
            self.out,
            "verification preview (experimental): {:?}",
            self.preview.outcome()
        )
        .unwrap();
        writeln!(
            self.out,
            "Profile-relative analysis only; no checked executable or compiler soundness theorem."
        )
        .unwrap();
        writeln!(self.out, "Refuted means a condition is false under abstract facts, not an executable counterexample; Unknown means not proved.").unwrap();
        if let Some(report) = self
            .preview
            .instantiations()
            .filter(|r| !r.templates.is_empty())
        {
            writeln!(self.out, "generics: {} templates; {} concrete instances; verdict covers concrete bodies only, never all template substitutions", report.templates.len(), report.instances.len()).unwrap();
            for template in report.uninstantiated() {
                writeln!(
                    self.out,
                    "uninstantiated template (not verified): {}",
                    visible(&template.definition)
                )
                .unwrap();
            }
        }
        if let Some(source) = self.preview.source() {
            writeln!(
                self.out,
                "input: {} ({} original bytes)",
                visible(&source.path().to_string_lossy()),
                source.len()
            )
            .unwrap();
            let input = self.preview.source_input().expect("source input binding");
            if input.is_module_program() {
                writeln!(self.out, "source snapshot: {} files; closed module program (all module bodies required); entry: {:?}",
                    input.sources().entries().len(), input.entry()).unwrap();
            } else {
                writeln!(self.out, "source snapshot: {} files; analyzed source: {:?} (snapshot ID {}); other files not analyzed",
                    input.sources().entries().len(), input.logical_name(), input.source_id().get()).unwrap();
            }
            writeln!(
                self.out,
                "requested profiles: target={:?}, runtime={:?}, verifier={:?}",
                input.requested().target,
                input.requested().runtime,
                input.requested().verifier
            )
            .unwrap();
            writeln!(
                self.out,
                "effective capability profile: {}; target={}, runtime={:?}, verifier={}",
                input.effective().profile().profile(),
                input.effective().target(),
                input.effective().runtime().id,
                input.effective().verifier()
            )
            .unwrap();
        } else {
            writeln!(
                self.out,
                "input: raw VIR (source text unavailable; frontend not run)"
            )
            .unwrap();
        }
        writeln!(self.out, "versions: {:?}", self.preview.versions()).unwrap();
        if self.preview.versions().runtime.is_none() {
            writeln!(self.out, "validated unit/runtime identity: unavailable").unwrap();
        }
        writeln!(
            self.out,
            "numeric engine: local kernel; external solver: none"
        )
        .unwrap();
        writeln!(self.out, "budgets/config: {:?}", self.preview.config()).unwrap();
        writeln!(
            self.out,
            "implementation TCB: {:?}",
            self.preview.implementation_trust_boundary()
        )
        .unwrap();
        writeln!(
            self.out,
            "native execution boundary (not invoked): {:?}",
            NATIVE_EXECUTION_BOUNDARY
        )
        .unwrap();
        writeln!(self.out, "Location columns count Unicode scalars; source operand names unavailable (not reconstructed from SSA IDs); use the source excerpt.").unwrap();
        match self.preview.counts() {
            Some(c) => {
                writeln!(
                    self.out,
                    "obligations: total={} (CFG={}, postcondition={}, Spec={}); functions={}",
                    c.total(),
                    c.cfg.total(),
                    c.postconditions.total(),
                    c.proofs.total(),
                    c.functions
                )
                .unwrap();
                for (layer, n) in [
                    ("CFG", c.cfg),
                    ("postcondition", c.postconditions),
                    ("Spec", c.proofs),
                ] {
                    writeln!(
                        self.out,
                        "  {layer}: Proven={} Refuted={} Unknown={}",
                        n.proven, n.refuted, n.unknown
                    )
                    .unwrap();
                }
                writeln!(
                    self.out,
                    "historical (not additional obligations): {:?}",
                    c.historical
                )
                .unwrap();
                writeln!(self.out, "summaries: Closed={} Candidate={} Unknown={} (summary state alone does not determine success)", c.summaries_closed, c.summaries_candidate, c.summaries_unknown).unwrap();
                writeln!(
                    self.out,
                    "inferred borrow interfaces: functions={}; complete result worlds={}",
                    c.borrow_interfaces, c.borrow_worlds
                )
                .unwrap();
            }
            None => writeln!(
                self.out,
                "obligations/statistics: unavailable (analysis incomplete)"
            )
            .unwrap(),
        }
        self.borrow_interfaces();
        match self.preview.trust_report() {
            None => writeln!(
                self.out,
                "explicit trust: unavailable (not an empty assumption set)"
            )
            .unwrap(),
            Some(trust) => {
                writeln!(
                    self.out,
                    "explicit trust entries: {}",
                    trust.entries().len()
                )
                .unwrap();
                for entry in trust.entries() {
                    writeln!(
                        self.out,
                        "[trust] registered assumption: {:?}",
                        entry.policy()
                    )
                    .unwrap();
                    self.finding(entry.finding());
                    if self.explain {
                        writeln!(self.out, "  evidence: {entry:?}").unwrap();
                    }
                }
            }
        }
        for issue in self.preview.frontend_issues() {
            let diagnostic = issue.diagnostic();
            writeln!(
                self.out,
                "[frontend/{:?}] {:?}: {}",
                issue.kind(),
                diagnostic.severity(),
                visible(diagnostic.message())
            )
            .unwrap();
            if let Some(source) = issue
                .source_id()
                .and_then(|id| self.preview.source_input()?.sources().source(id))
            {
                if let Some(span) = diagnostic.primary_span() {
                    SourceLines::new(source).render(&mut self.out, span);
                }
            } else {
                self.input_span(diagnostic.primary_span());
            }
        }
        if let Some(failure) = self.preview.failure() {
            match failure {
                PreviewFailure::Validation(e) => {
                    writeln!(self.out, "[validation] {:?}", e.kind()).unwrap();
                    self.input_span(e.source_span());
                }
                PreviewFailure::Resolution(e) => {
                    writeln!(self.out, "[resolution] {}", visible(&e.to_string())).unwrap();
                    if let Some(mut position) = self.preview.validated_unit().and_then(|unit| {
                        unit.as_unit()
                            .source_map
                            .source_span(VirLocation::FunctionEntry {
                                function: e.function(),
                            })
                    }) {
                        position.span = e.source_span();
                        self.position(position);
                    } else {
                        self.input_span(Some(e.source_span()));
                    }
                }
                PreviewFailure::Verification(e) => {
                    writeln!(self.out, "[analysis] {}", visible(&e.to_string())).unwrap();
                    if let VerificationError::Cfg { function, .. }
                    | VerificationError::Summary { function, .. } = e
                    {
                        self.location(VirLocation::FunctionEntry {
                            function: *function,
                        });
                    }
                }
                PreviewFailure::MissingValidatedUnit => writeln!(
                    self.out,
                    "[analysis] accepted producer did not supply a validated unit"
                )
                .unwrap(),
            }
        }
        if let Some(obligations) = self.preview.obligations() {
            for obligation in obligations {
                if self.explain || !obligation.status().is_proven() {
                    let (layer, reason) = match obligation.evidence {
                        ObligationEvidence::Cfg(c) => ("CFG", condition(c.obligation().kind())),
                        ObligationEvidence::Postcondition(_) => (
                            "postcondition",
                            "return satisfies the declared or type-induced postcondition".into(),
                        ),
                        ObligationEvidence::Proof(_) => {
                            ("Spec", "specification proposition holds".into())
                        }
                    };
                    self.obligation(layer, obligation.status(), &reason, obligation.finding());
                    if self.explain {
                        writeln!(self.out, "  evidence: {:?}", obligation.evidence).unwrap();
                    }
                }
            }
        }
        if self.explain {
            if let Some(history) = self.preview.historical() {
                for record in history {
                    self.obligation(
                        "historical/not-additional",
                        record.obligation().status(),
                        &condition(record.obligation().kind()),
                        record.finding(),
                    );
                    writeln!(self.out, "  evidence: {record:?}").unwrap();
                }
            }
            if let Some(diagnostics) = self.preview.diagnostics() {
                for diagnostic in diagnostics {
                    writeln!(
                        self.out,
                        "[diagnostic/explanation-not-additional] {:?}: {}",
                        diagnostic.kind(),
                        visible(diagnostic.message())
                    )
                    .unwrap();
                    self.finding(diagnostic.finding());
                    if !diagnostic.relation_queries().is_empty() {
                        writeln!(self.out, "  query-local evidence (auxiliary attempts, not necessarily the sole cause):").unwrap();
                        for query in diagnostic.relation_queries() {
                            writeln!(self.out, "    {query:?}").unwrap();
                        }
                    }
                    for note in diagnostic.provenance_notes() {
                        writeln!(self.out, "  provenance: {note:?}").unwrap();
                    }
                }
            }
        }
        self.summaries();
    }

    fn obligation(
        &mut self,
        layer: &str,
        status: ObligationStatus,
        reason: &str,
        finding: VerifierFinding,
    ) {
        let explanation = match status {
            ObligationStatus::Proven => "established",
            ObligationStatus::Refuted => "required condition is false under abstract facts",
            ObligationStatus::Unknown => "insufficient facts to establish condition",
        };
        writeln!(self.out, "[{layer}/{status:?}] {reason}: {explanation}").unwrap();
        self.finding(finding);
    }

    fn borrow_interfaces(&mut self) {
        if !self.explain || self.preview.verification().is_none() {
            return;
        }
        let Some(runtime) = self.preview.validated_unit().map(|unit| unit.runtime()) else {
            return;
        };
        let mut entries = Vec::new();
        for function in runtime.functions {
            let Some(abi) = runtime.abis.function(function.id) else {
                continue;
            };
            if let Some(relation) = abi.signature.borrow_result() {
                entries.push((
                    function.id,
                    function.name.clone(),
                    "always".to_owned(),
                    relation,
                ));
            }
            for alternative in abi.signature.borrow_result_alternatives() {
                let guard = alternative
                    .guard
                    .iter()
                    .map(|atom| match atom {
                        crate::BorrowGuardAtom::Boolean {
                            parameter,
                            expected,
                        } => format!("parameter #{parameter} == {expected}"),
                    })
                    .collect::<Vec<_>>()
                    .join(" and ");
                entries.push((
                    function.id,
                    function.name.clone(),
                    guard,
                    alternative.relation,
                ));
            }
        }
        if entries.is_empty() {
            return;
        }
        let (tag, introduction) = if self.preview.source().is_some() {
            (
                "generated",
                "borrow interfaces below are derived from source function bodies and structurally validated; they are not user contracts or trusted assumptions",
            )
        } else {
            (
                "validated-unit",
                "borrow interfaces below come from the validated VIR unit; this report does not classify them as source inference or user contracts",
            )
        };
        writeln!(self.out, "{introduction}").unwrap();
        for (function, name, guard, relation) in entries {
            writeln!(
                self.out,
                "[borrow-interface/{tag}] `{}` when {}: result #{} borrows {:?} from parameter #{}; {}",
                visible(&name),
                guard,
                relation.result,
                relation.access,
                relation.parameter,
                borrow_projection(relation),
            )
            .unwrap();
            self.location(VirLocation::FunctionEntry { function });
        }
    }

    fn function_name(&self, id: VirFunctionId) -> String {
        self.preview
            .validated_unit()
            .and_then(|u| u.runtime().functions.iter().find(|f| f.id == id))
            .map(|f| visible(&f.name))
            .unwrap_or_else(|| "<function name unavailable>".into())
    }

    fn finding(&mut self, finding: VerifierFinding) {
        writeln!(
            self.out,
            "  in function `{}`",
            self.function_name(finding.site().function())
        )
        .unwrap();
        self.position(finding.source_position());
        if let Some(unit) = self.preview.validated_unit() {
            let map = &unit.as_unit().source_map;
            let mut origin = map.origin(finding.origin());
            while let Some(crate::VirOrigin {
                kind: VirOriginKind::Generated { parent, reason },
                ..
            }) = origin
            {
                writeln!(
                    self.out,
                    "  generated {reason:?}: attributed to the enclosing source construct"
                )
                .unwrap();
                origin = map.origin(*parent);
            }
        }
        if let Some(occurrence) = finding.occurrence() {
            writeln!(self.out, "  related return occurrence:").unwrap();
            self.location(occurrence);
        }
        if self.explain {
            writeln!(
                self.out,
                "  site: {:?}; origin: {:?}",
                finding.site(),
                finding.origin()
            )
            .unwrap();
        }
    }

    fn input_span(&mut self, span: Option<ByteSpan>) {
        match (span, &self.source) {
            (Some(span), Some(source)) => source.render(&mut self.out, span),
            (Some(span), None) => writeln!(
                self.out,
                "  source text unavailable; input byte span {}..{}",
                span.start(),
                span.end()
            )
            .unwrap(),
            (None, _) => writeln!(self.out, "  source position unavailable").unwrap(),
        }
    }

    fn position(&mut self, position: VirSourceSpan) {
        let entry = self
            .preview
            .validated_unit()
            .and_then(|u| u.as_unit().source_map.source(position.source));
        // Explicit unit -> snapshot binding supplied by the source producer.
        // Matching path text/byte length alone cannot establish source identity.
        if let Some(source) = self.preview.locate_vir_span(position).and_then(|located| {
            self.preview
                .source_input()?
                .sources()
                .source(located.source)
        }) {
            SourceLines::new(source).render(&mut self.out, position.span);
            return;
        }
        let name = entry
            .map(|s| visible(&s.name))
            .unwrap_or_else(|| "<source unavailable>".into());
        writeln!(
            self.out,
            "  --> {name}: bytes {}..{} (source text unavailable; line/column unavailable)",
            position.span.start(),
            position.span.end()
        )
        .unwrap();
    }

    fn location(&mut self, location: VirLocation) {
        if let Some(position) = self
            .preview
            .validated_unit()
            .and_then(|u| u.as_unit().source_map.source_span(location))
        {
            self.position(position);
        } else {
            writeln!(self.out, "  related source position unavailable").unwrap();
        }
    }

    fn summaries(&mut self) {
        use crate::verifier::summary::{CallSummaryOutcome, SummaryState};
        let Some(summaries) = self.preview.summaries() else {
            return;
        };
        for (id, summary) in summaries {
            if self.explain || !matches!(summary.state, SummaryState::Closed) {
                writeln!(
                    self.out,
                    "[summary/precision-not-obligation] `{}`: {:?}; audit_complete={}",
                    self.function_name(id),
                    summary.state,
                    summary.audit_complete
                )
                .unwrap();
                if let Some(recursion) = &summary.recursion {
                    writeln!(self.out, "  SCC closure: {:?}", recursion.outcome).unwrap();
                    if self.explain {
                        writeln!(
                            self.out,
                            "  iterations={}; body_analyses={}; final_recheck={}; widenings={}",
                            recursion.iterations,
                            recursion.body_analyses,
                            recursion.final_recheck,
                            recursion.widenings
                        )
                        .unwrap();
                    }
                }
            }
            if self.explain {
                writeln!(self.out, "  summary effects: {:?}", summary.effects).unwrap();
                // Borrow the existing exported worlds; do not build an audit or
                // run a closure/replay to provide a more impressive explanation.
                writeln!(
                    self.out,
                    "  summary return alternatives: {:?}",
                    summary.normal_returns
                )
                .unwrap();
            }
            for call in &summary.call_uses {
                if !self.explain
                    && matches!(
                        call.outcome,
                        CallSummaryOutcome::Applied | CallSummaryOutcome::Inductive
                    )
                {
                    continue;
                }
                writeln!(
                    self.out,
                    "[call/precision-not-obligation] `{}` -> `{}`: {:?}; mapping loss: {:?}",
                    self.function_name(id),
                    visible(&call.symbol),
                    call.outcome,
                    call.observation.mapping_loss
                )
                .unwrap();
                if let Some(finding) = call.observation.finding {
                    self.finding(finding);
                } else {
                    writeln!(self.out, "  caller source position unavailable").unwrap();
                }
                let callee = self
                    .preview
                    .validated_unit()
                    .and_then(|u| u.runtime().functions.iter().find(|f| f.name == call.symbol));
                if let Some(callee) = callee {
                    writeln!(
                        self.out,
                        "  related callee definition (not by itself the failure cause):"
                    )
                    .unwrap();
                    self.location(VirLocation::FunctionEntry {
                        function: callee.id,
                    });
                }
                if self.explain {
                    writeln!(
                        self.out,
                        "  case={}; instance_site={}; guard={:?}",
                        call.observation.case_ordinal,
                        call.observation.instance_site,
                        call.observation.guard
                    )
                    .unwrap();
                    writeln!(
                        self.out,
                        "  arguments={:?}; dependency={:?}",
                        call.observation.arguments, call.observation.dependency
                    )
                    .unwrap();
                    for world in &call.observation.worlds {
                        writeln!(self.out, "  mapping world: {world:?}").unwrap();
                    }
                }
            }
            if self.explain {
                let cfg = self.preview.verification().unwrap().functions()[&id].cfg();
                for (block, losses) in cfg.guarded_precision_losses() {
                    if !losses.is_empty() {
                        writeln!(
                            self.out,
                            "[precision-not-obligation] `{}` {block:?}: {losses:?}",
                            self.function_name(id)
                        )
                        .unwrap();
                    }
                }
            }
        }
    }
}

fn borrow_projection(relation: BorrowResultRelation) -> String {
    match relation.projection {
        BorrowProjection::Whole => "projection=whole input view".to_owned(),
        BorrowProjection::Fixed {
            offset_bytes,
            size_bytes,
            alignment,
        } => format!(
            "projection=fixed bytes {offset_bytes}..{} (alignment {alignment})",
            offset_bytes.saturating_add(size_bytes)
        ),
        BorrowProjection::Slice {
            start,
            end,
            stride_bytes,
            alignment,
        } => format!(
            "projection=slice {}..{} (stride {stride_bytes}, alignment {alignment})",
            borrow_bound(start),
            borrow_bound(end)
        ),
    }
}

fn borrow_bound(bound: BorrowSliceBound) -> String {
    match bound {
        BorrowSliceBound::Constant(value) => value.to_string(),
        BorrowSliceBound::Parameter(parameter) => format!("parameter #{parameter}"),
        BorrowSliceBound::SourceLength => "source length".to_owned(),
    }
}
