# ELVAE Lean Verification

Lean 4 source code accompanying work on formal verification of mathematical results for the ELVAE
project.

## Repository contents

- `Official/`, `Official.lean`: the assisted B2 corpus, modules `Official.M01`–`Official.M23`
  (namespace `NIGBottleneck`). The code of M01 and M02 is identical to the accepted B1 modules; in this
  public copy only their comments differ.
- `ELVAELeanVerification/`, `ELVAELeanVerification.lean`: the earlier reference Lean development
  (namespace `ELVAE`), which predates the study's generated L1. `VerifiedCore.lean` imports all of its
  modules.
- `PostHoc/`, `PostHoc.lean`: post-hoc Lean relation and audit code:
  - `PostHoc/Relations/`: L1–B2 relation certificates. `L1_<item>` schemas formalize the L1
    statements, `B2_<item>` restate the B2 declarations, and `rel_<item>` prove their relation;
    `Audit.lean` defines `#relation_audit`, which checks that a relation proof does not use the
    item's target B2 theorems.
  - `PostHoc/LeanL2/`: Lean–L2 code-level checks. `Vocab.lean` proves L2's definitions equal to B2's
    (`l2def_*`); `Items1`–`Items3` relate each item's L2 statements to the B2 declarations they
    translate (`rel2_*`).
  - `PostHoc/E1/`: the de-identified E1 Lean corpus `PostHoc.E1.M01`–`M23` (namespace `NS1`), a
    mechanical renaming of the B2 corpus that typechecks on its own.
- `scripts/`: reusable build and audit utilities: `audit.sh` (clean rebuild and verification audit),
  `AxiomReport.lean` (axioms of every constant of all libraries), `CountDeclarations.lean`
  (declaration count for the `ELVAE` library). `AxiomAudit.lean` lists `#print axioms` checks for
  main results of the `ELVAE` library.
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`: Lean/Lake environment configuration.
- `.github/workflows/lean_action_ci.yml`: continuous-integration build.

## Requirements

- [elan](https://github.com/leanprover/elan) (installs the toolchain pinned in `lean-toolchain`,
  `leanprover/lean4:v4.35.0-rc3`).
- Mathlib `v4.35.0-rc3`, pinned in `lake-manifest.json` and fetched by Lake.
- `bash` for `scripts/audit.sh` (Git Bash on Windows, or Linux/macOS).

## Build

```sh
lake exe cache get   # fetch prebuilt Mathlib
lake build           # build all libraries; runs the #relation_audit checks
bash scripts/audit.sh
```

`scripts/audit.sh` rebuilds the project and prints `AUDIT PASSED` only if the build has no warnings
or errors, the sources contain no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` or
`implemented_by`, and every constant depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Repository scope

This repository is intentionally code-only. Non-code records (manuscripts, model prompts and
transcripts, experimental results, reviewer materials, benchmark data, ledgers, planning files,
private maps and keys, and account/session records) are maintained separately and are not included
here.

## License

MIT License (see `LICENSE`). Third-party dependencies, including Lean 4 and Mathlib, remain subject
to their own licenses.
