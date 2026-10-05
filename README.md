# ELVAE Lean Verification

Lean 4 source code accompanying work on formal verification of mathematical results for the ELVAE
project.

## Repository contents

- `ELVAELeanVerification/`, `ELVAELeanVerification.lean`: Lean formalization library (namespace
  `ELVAE`); `ELVAELeanVerification/VerifiedCore.lean` imports all of its modules.
- `Official/`, `Official.lean`: Lean formalization modules `Official.M01`–`Official.M23`
  (namespace `NIGBottleneck`).
- `AxiomAudit.lean`: `#print axioms` checks for main results of the `ELVAE` library.
- `scripts/AxiomReport.lean`: axiom report over every constant of both libraries.
- `scripts/CountDeclarations.lean`: declaration count for the `ELVAE` library.
- `scripts/audit.sh`: clean rebuild and verification audit.
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
lake build           # build both libraries
bash scripts/audit.sh
```

`scripts/audit.sh` rebuilds the project and prints `AUDIT PASSED` only if the build has no warnings
or errors, the sources contain no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` or
`implemented_by`, and every constant depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Repository scope

This repository is intentionally code-only. Research manuscripts, model prompts and responses,
experimental results, reviewer materials, benchmark data, internal planning documents, and private
research records are maintained separately and are not included here.

## License

MIT License (see `LICENSE`). Third-party dependencies, including Lean 4 and Mathlib, remain subject
to their own licenses.
