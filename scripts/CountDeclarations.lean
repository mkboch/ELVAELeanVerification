import ELVAELeanVerification
open Lean

/-!
Counts the user-facing declarations of this package, read from the Lean environment.
Run: lake env lean scripts/CountDeclarations.lean
Auto-generated auxiliary constants (names with internal components) are excluded.
-/

#eval show CoreM Unit from do
  let env ← getEnv
  let mut thms := 0
  let mut defs := 0
  let mut others := 0
  let mut mods : Std.HashSet Name := {}
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`ELVAELeanVerification).isPrefixOf m do continue
    if m == `ELVAELeanVerification.Basic then continue
    if n.isInternalDetail then continue
    mods := mods.insert m
    match ci with
    | .thmInfo _ =>
        thms := thms + 1
        if (← IO.getEnv "ELVAE_LIST").isSome then IO.println s!"thm {n}"
    | .defnInfo _ => defs := defs + 1
    | _ => others := others + 1
  IO.println s!"modules with declarations: {mods.size}"
  IO.println s!"theorems/lemmas: {thms}"
  IO.println s!"definitions: {defs}"
  IO.println s!"other (structures, constructors, recursors, ...): {others}"
