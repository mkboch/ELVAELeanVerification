import Lean

/-!
# Dependency audit for relation certificates

`#relation_audit rel [t₁, t₂, …]` inspects the proof term of the relation theorem `rel`. It collects every
constant the proof uses, following transitively every theorem and definition (including auxiliary `_proof_`
declarations) defined in the current module or in any `PostHoc.Relations.*` / `PostHoc.LeanL2.*` module, so
a target theorem cannot be hidden behind an intermediate post-hoc declaration. It then reports which
`Official.*` (B2) theorems are reached.

The command fails if any of the listed *target* theorems (the B2 declarations whose statement strength is
being compared) occurs among them. Every use of other Official theorems ("permitted foundational lemmas") is
printed, so that a reader can judge it.
-/

namespace PostHocAudit

open Lean Elab Command

/-- Official theorems used (transitively through current-module theorems) by the proof of `root`. -/
def officialTheoremsUsed (env : Environment) (root : Name) : Array Name := Id.run do
  let mut stack : Array Name := #[root]
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  let mut fuel := 100000
  while !stack.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let val? : Option Expr := match ci with
      | .thmInfo v => some v.value
      | .defnInfo v => some v.value
      | _ => none
    let some v := val? | continue
    for c in v.getUsedConstants do
      match env.getModuleIdxFor? c with
      | some idx =>
        let mod := env.header.moduleNames[idx.toNat]!
        if (`Official).isPrefixOf mod then
          if let some (.thmInfo _) := env.find? c then
            out := out.insert c
        else if (`PostHoc.Relations).isPrefixOf mod || (`PostHoc.LeanL2).isPrefixOf mod then
          stack := stack.push c
      | none =>
        -- defined in the current module
        stack := stack.push c
  return out.toArray.qsort Name.lt

syntax (name := relationAudit) "#relation_audit " ident " [" ident,* "]" : command

@[command_elab relationAudit] def elabRelationAudit : CommandElab := fun stx => do
  let env ← getEnv
  let rel ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let targets ← (stx[3].getSepArgs).mapM fun t => liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let used := officialTheoremsUsed env rel
  let bad := used.filter (targets.contains ·)
  let usedStr := if used.isEmpty then "none" else ", ".intercalate (used.toList.map toString)
  if bad.isEmpty then
    logInfo m!"RELATION_AUDIT {rel} PASS targets_excluded=yes official_theorems_used=[{usedStr}]"
  else
    throwError m!"RELATION_AUDIT {rel} FAIL target theorem(s) used: {bad}"

end PostHocAudit
