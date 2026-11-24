import Lean
import GravitonCert

open Lean GravitonCert

/--
`graviton-cert` CLI:
1. Initializes the Lean search path and loads the compiled `GravitonCert` `.olean`
   environment directly into Lean's kernel inspector.
2. Audits every registered claim using `Lean.CollectAxioms.collect` to confirm:
   - The declaration exists in the compiled environment,
   - Zero `sorryAx` dependencies,
   - Zero unapproved custom axioms (only standard Lean axioms or pure constructive proofs).
3. Writes `epistemic-manifest.json` (ready for `gravitonresearch.org`) and
   `VERIFICATION.md` (human-readable audit ledger).
4. Exits non-zero if ANY check fails (CI-ready).
-/
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `GravitonCert }] {}
  let audited := allStudies.map (auditStudy env)
  let json := renderManifestJson audited
  let md := renderVerificationMarkdown audited
  IO.FS.writeFile "epistemic-manifest.json" (json.pretty ++ "\n")
  IO.FS.writeFile "VERIFICATION.md" md
  let mut allOk := true
  IO.println "GravitonCert — Lean 4 Kernel Epistemic Audit"
  IO.println "============================================"
  for s in audited do
    let badge := if s.allPassed then "PASS" else "FAIL"
    IO.println s!"[{badge}] {s.study.studyId} ({s.auditedClaims.length} claims, {s.study.openGates.length} open empirical gates)"
    for ac in s.auditedClaims do
      let axStr := if ac.axioms.isEmpty then "pure constructive" else String.intercalate ", " ac.axioms
      let mark := if ac.kernelPassed then "OK" else "FAIL"
      IO.println s!"  - [{mark}] {ac.claim.id}: {ac.claim.leanDecl}  (axioms: {axStr})"
      if !ac.kernelPassed then
        allOk := false
  IO.println ""
  IO.println "Wrote epistemic-manifest.json and VERIFICATION.md"
  if allOk then
    IO.println "ALL KERNEL CHECKS PASSED (0 sorryAx, 0 custom axioms)."
    return 0
  else
    IO.eprintln "ERROR: One or more registered claims failed kernel verification."
    return 1
