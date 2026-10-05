import ELVAELeanVerification
import Official
import PostHoc

/-!
# Axiom report for all libraries

`#axiom_report` enumerates every constant declared in a module of `ELVAELeanVerification`,
`Official`, `PostHoc.Relations`, `PostHoc.LeanL2` or `PostHoc.E1` (including private and auxiliary
constants), computes the axioms it depends on with
`Lean.collectAxioms`, prints per-library counts and the union, and fails unless the union is
contained in the standard set {propext, Classical.choice, Quot.sound}. In particular it fails on
`sorryAx` or on any user-declared axiom.

Run: `lake env lean scripts/AxiomReport.lean`
-/

namespace ELVAEAxiomReport

open Lean Elab Command

syntax (name := axiomReport) "#axiom_report" : command

@[command_elab axiomReport] def elabAxiomReport : CommandElab := fun _ => do
  let env ← getEnv
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let libs : List Name :=
    [`ELVAELeanVerification, `Official, `PostHoc.Relations, `PostHoc.LeanL2, `PostHoc.E1]
  let mut perLib : Std.HashMap Name (Nat × NameSet) := {}
  let mut union : NameSet := {}
  let mut offenders : Array (Name × Array Name) := #[]
  let mut total := 0
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    let some lib := libs.find? (·.isPrefixOf mod) | continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    total := total + 1
    let (c, s) := perLib.getD lib (0, {})
    perLib := perLib.insert lib (c + 1, axs.foldl (·.insert ·) s)
    union := axs.foldl (·.insert ·) union
    let bad := axs.filter (fun a => !standard.contains a)
    unless bad.isEmpty do offenders := offenders.push (n, bad)
  for lib in libs do
    let (c, s) := perLib.getD lib (0, {})
    logInfo m!"AXIOM_REPORT library={lib} constants={c} axioms={s.toList.toArray.qsort Name.lt}"
  logInfo m!"AXIOM_REPORT total_constants={total} union={union.toList.toArray.qsort Name.lt}"
  if offenders.isEmpty then
    logInfo m!"AXIOM_REPORT PASS union ⊆ [propext, Classical.choice, Quot.sound]"
  else
    throwError m!"AXIOM_REPORT FAIL nonstandard axioms: {offenders}"

end ELVAEAxiomReport

#axiom_report
