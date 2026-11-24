import Lean
import GravitonCert.Core.Boundary

/-!
# GravitonCert.Core.Inspect

Kernel-level axiom auditor.
Given a compiled Lean `Environment`, inspects every registered theorem using
`Lean.CollectAxioms.collect`, rejects `sorryAx` and unapproved custom axioms,
and renders both `epistemic-manifest.json` and a human-readable Markdown ledger.
-/

namespace GravitonCert

open Lean

/-- Standard trusted axioms of Lean 4's logic (no `sorryAx`, no `ofReduceBool`/`trustCompiler`). -/
def standardLeanAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

private local instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv f := modify f

/-- Collect all kernel axioms transitively depended on by `declName` in `env`. -/
def collectAxiomsInEnv (env : Environment) (declName : Name) : List Name :=
  ((Lean.collectAxioms declName : StateM Environment (Array Name)).run' env).toList

/-- Audit a single registered claim directly against Lean's compiled environment. -/
def auditClaim (env : Environment) (claim : RegisteredClaim) : AuditedClaim :=
  match env.find? claim.leanDecl with
  | none =>
      { claim := claim
        existsInKernel := false
        axioms := []
        usesSorry := false
        usesCustomAxiom := false
        kernelPassed := false }
  | some _ =>
      let axList := collectAxiomsInEnv env claim.leanDecl
      let usesSorry := axList.any (· == ``sorryAx)
      let usesCustom := axList.any (fun a => a != ``sorryAx && !standardLeanAxioms.contains a)
      let passed := !usesSorry && !usesCustom
      { claim := claim
        existsInKernel := true
        axioms := axList.map Name.toString
        usesSorry := usesSorry
        usesCustomAxiom := usesCustom
        kernelPassed := passed }

/-- Audit every claim in a `StudyCertificate`. -/
def auditStudy (env : Environment) (study : StudyCertificate) : AuditedStudy :=
  let audited := study.claims.map (auditClaim env)
  { study := study
    auditedClaims := audited
    allPassed := audited.all (·.kernelPassed) }

/-- Render an audited manifest as JSON for web embedding (e.g. gravitonresearch.org). -/
def renderManifestJson (studies : List AuditedStudy) : Json :=
  let totalClaims := studies.foldl (fun acc s => acc + s.auditedClaims.length) 0
  let passedClaims := studies.foldl (fun acc s => acc + (s.auditedClaims.filter (·.kernelPassed)).length) 0
  let totalOpenGates := studies.foldl (fun acc s => acc + s.study.openGates.length) 0
  Json.mkObj [
    ("schema", toJson "graviton-cert/v0.1"),
    ("organization", toJson "Graviton Research Foundation"),
    ("website", toJson "https://gravitonresearch.org"),
    ("all_studies_passed", toJson (studies.all (·.allPassed))),
    ("summary", Json.mkObj [
      ("studies_audited", toJson studies.length),
      ("claims_verified", toJson passedClaims),
      ("claims_total", toJson totalClaims),
      ("open_empirical_gates", toJson totalOpenGates)
    ]),
    ("studies", toJson studies)
  ]

/-- Render a clean Markdown verification ledger for GitHub / documentation. -/
def renderVerificationMarkdown (studies : List AuditedStudy) : String :=
  let header :=
    "# GravitonCert — Machine-Checked Epistemic Ledger\n\n" ++
    "Generated directly from Lean 4's compiled kernel via `Lean.collectAxioms`.\n" ++
    "Every claim marked **PASS** was type-checked with **zero `sorryAx`** and **zero custom axioms**.\n\n"
  let body := studies.foldl (fun acc s =>
    let statusBadge := if s.allPassed then "PASS" else "FAIL"
    let sHead :=
      s!"## {s.study.title} (`{s.study.studyId}`)\n\n" ++
      s!"- **Domain:** {s.study.domain}\n" ++
      s!"- **Reference:** {s.study.url}\n" ++
      s!"- **Kernel Audit:** **{statusBadge}**\n" ++
      s!"- **Scope:** {s.study.scopeStatement}\n\n"
    let claimsTable :=
      "### Kernel-Checked Claims\n\n" ++
      "| Claim | Kind | Lean Declaration | Kernel Axioms | Status |\n" ++
      "| :--- | :--- | :--- | :--- | :--- |\n" ++
      s.auditedClaims.foldl (fun cAcc ac =>
        let axStr := if ac.axioms.isEmpty then "*(pure constructive — none)*" else String.intercalate ", " (ac.axioms.map (s!"`{·}`"))
        let stStr := if ac.kernelPassed then "PASS" else "FAIL"
        cAcc ++ s!"| {ac.claim.title} | `{ac.claim.claimKind}` | `{ac.claim.leanDecl}` | {axStr} | **{stStr}** |\n"
      ) "" ++ "\n"
    let boundaries :=
      "### Explicit Epistemic Boundaries (What These Proofs Do *Not* Establish)\n\n" ++
      s.auditedClaims.foldl (fun bAcc ac =>
        ac.claim.doesNotEstablish.foldl (fun iAcc d => iAcc ++ s!"- **{ac.claim.id}:** {d}\n") bAcc
      ) "" ++ "\n"
    let gates :=
      if s.study.openGates.isEmpty then ""
      else
        "### Open Empirical Gates (Cannot Be Closed by Mathematics Alone)\n\n" ++
        "| Gate | Quantity | Units | Required Control | Status |\n" ++
        "| :--- | :--- | :--- | :--- | :--- |\n" ++
        s.study.openGates.foldl (fun gAcc g =>
          gAcc ++ s!"| `{g.id}` | {g.quantity} | `{g.units}` | {g.requiredControl} | `{g.status}` |\n"
        ) "" ++ "\n"
    acc ++ sHead ++ claimsTable ++ boundaries ++ gates
  ) ""
  header ++ body

end GravitonCert
