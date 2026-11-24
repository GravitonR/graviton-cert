import Lean.Data.Json

/-!
# GravitonCert.Core.Boundary

Core data structures for **Boundary-Explicit Science**:
every formalized scientific claim carries:
1. A reference to an actual Lean 4 declaration checked by the kernel,
2. The exact mathematical/physical assumptions it requires,
3. Explicit boundaries stating what the theorem *does not* establish, and
4. Typed empirical gates separating mathematics from unmeasured reality.
-/

namespace GravitonCert

open Lean

/-- A declared assumption scoping a study or theorem. -/
structure Assumption where
  id : String
  kind : String
  statement : String
  deriving Repr, Inhabited

/-- An open experimental or observational requirement that mathematics alone cannot close. -/
structure EmpiricalGate where
  id : String
  quantity : String
  units : String
  requiredControl : String
  status : String
  deriving Repr, Inhabited

/-- A single claim anchored to an actual Lean 4 declaration in the compiled kernel. -/
structure RegisteredClaim where
  id : String
  title : String
  leanDecl : Name
  claimKind : String
  summary : String
  assumptionIds : List String
  doesNotEstablish : List String
  deriving Repr, Inhabited

/-- A complete verification ledger for one research study or note. -/
structure StudyCertificate where
  studyId : String
  title : String
  url : String
  domain : String
  scopeStatement : String
  assumptions : List Assumption
  claims : List RegisteredClaim
  openGates : List EmpiricalGate
  sourceArtifacts : List (String × String)
  deriving Repr, Inhabited

/-- Result of auditing one `RegisteredClaim` against Lean's compiled environment. -/
structure AuditedClaim where
  claim : RegisteredClaim
  existsInKernel : Bool
  axioms : List String
  usesSorry : Bool
  usesCustomAxiom : Bool
  kernelPassed : Bool
  deriving Repr, Inhabited

/-- Result of auditing an entire `StudyCertificate`. -/
structure AuditedStudy where
  study : StudyCertificate
  auditedClaims : List AuditedClaim
  allPassed : Bool
  deriving Repr, Inhabited

instance : ToJson Assumption where
  toJson a := Json.mkObj [
    ("id", toJson a.id),
    ("kind", toJson a.kind),
    ("statement", toJson a.statement)
  ]

instance : ToJson EmpiricalGate where
  toJson g := Json.mkObj [
    ("id", toJson g.id),
    ("quantity", toJson g.quantity),
    ("units", toJson g.units),
    ("required_control", toJson g.requiredControl),
    ("status", toJson g.status)
  ]

instance : ToJson AuditedClaim where
  toJson ac := Json.mkObj [
    ("id", toJson ac.claim.id),
    ("title", toJson ac.claim.title),
    ("lean_declaration", toJson ac.claim.leanDecl.toString),
    ("claim_kind", toJson ac.claim.claimKind),
    ("summary", toJson ac.claim.summary),
    ("assumptions", toJson ac.claim.assumptionIds),
    ("does_not_establish", toJson ac.claim.doesNotEstablish),
    ("exists_in_kernel", toJson ac.existsInKernel),
    ("kernel_axioms", toJson ac.axioms),
    ("uses_sorry", toJson ac.usesSorry),
    ("uses_custom_axiom", toJson ac.usesCustomAxiom),
    ("kernel_passed", toJson ac.kernelPassed)
  ]

instance : ToJson AuditedStudy where
  toJson s := Json.mkObj [
    ("study_id", toJson s.study.studyId),
    ("title", toJson s.study.title),
    ("url", toJson s.study.url),
    ("domain", toJson s.study.domain),
    ("scope_statement", toJson s.study.scopeStatement),
    ("all_kernel_checks_passed", toJson s.allPassed),
    ("assumptions", toJson s.study.assumptions),
    ("claims", toJson s.auditedClaims),
    ("open_empirical_gates", toJson s.study.openGates),
    ("source_artifacts", Json.mkObj (s.study.sourceArtifacts.map fun (k, v) => (k, toJson v)))
  ]

end GravitonCert
