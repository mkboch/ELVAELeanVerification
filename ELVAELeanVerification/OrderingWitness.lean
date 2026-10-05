import Mathlib
import ELVAELeanVerification.ManuscriptRemaining

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Weight invariance does not give ordering invariance across outer optima

The conditional weight invariance of `WeightInvariance` does not imply that
ordering is invariant across outer optima obtained with different
regularization weights. This is a non-implication, formalized by an explicit
witness (`ordering_across_outer_optima_can_change`).
-/

namespace ELVAE

/-! ## Ordering across outer optima can change with `λ` -/

section OrderingWitness

open Classical in
/-- Reconstruction term of input 2: minimized only at the prior base state. -/
noncomputable def witnessL2 (θ0 : QuotientState) (θ : QuotientState) : ℝ :=
  if θ = θ0 then 0 else 1

open Classical in
/-- Reconstruction term of input 1: `−R_can + h` with `h(θ₀) = 0`, `h(θ_B) = −R_can(θ_B)/2`,
`h = 1` elsewhere. -/
noncomputable def witnessL1 (R : QuotientState → ℝ) (θ0 θB : QuotientState)
    (θ : QuotientState) : ℝ :=
  -R θ + (if θ = θ0 then 0 else if θ = θB then -(R θB / 2) else 1)

/-- The witness prior `(γ₀, ν₀, α₀, β₀) = (0, 2, 1/2, 1)` and its base state. -/
lemma witness_prior_base :
    priorQuotient 0 2 (1 / 2) 1 = ⟨0, 1 / 2, 3 / 2⟩ := by
  simp only [priorQuotient, priorC0]
  norm_num

lemma witness_nuCan_base :
    QuotientState.nuCan 0 2 (1 / 2) 1 ⟨0, 1 / 2, 3 / 2⟩ = 2 := by
  have h := nuCanFromParams_at_prior 0 2 (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
  have hc : priorC0 2 1 = 3 / 2 := by simp only [priorC0]; norm_num
  rw [hc] at h
  exact h

lemma witness_nuCan_B :
    QuotientState.nuCan 0 2 (1 / 2) 1 ⟨1, 2, 32 / 7⟩ = 3 := by
  have hB : BFromParams 1 2 (32 / 7) 0 2 1 = 15 / 8 := by unfold BFromParams; norm_num
  simp only [QuotientState.nuCan, nuCanFromParams]
  rw [hB, nuCan, sqrt_eq_of_sq (y := 17 / 8) (by norm_num) (by norm_num)]
  norm_num

/--
Conditional weight invariance of `ν_can` does not make the
ordering by inverse canonical allocation invariant across outer optima obtained with
different KL weights. For the prior `(0, 2, 1/2, 1)` there are two reconstruction terms
`L₁, L₂` (two inputs) whose unique outer optima `θ*_i(λ)` satisfy:
`1/ν_can(θ*_1(1)) < 1/ν_can(θ*_2(1))`, but `1/ν_can(θ*_1(2)) = 1/ν_can(θ*_2(2))`.
-/
theorem ordering_across_outer_optima_can_change :
    let R := Rcan 0 2 (1 / 2) 1
    let s := QuotientState.nuCan 0 2 (1 / 2) 1
    let θ0 : QuotientState := ⟨0, 1 / 2, 3 / 2⟩
    let θB : QuotientState := ⟨1, 2, 32 / 7⟩
    let L1 := witnessL1 R θ0 θB
    let L2 := witnessL2 θ0
    let J := fun (L : QuotientState → ℝ) (lam : ℝ) (θ : QuotientState) =>
      partialJ3 L (fiberKL 0 2 (1 / 2) 1) s lam θ
    -- unique outer optima
    (∀ θ ∈ admissibleQuotients, θ ≠ θB → J L1 1 θB < J L1 1 θ)
      ∧ (∀ θ ∈ admissibleQuotients, θ ≠ θ0 → J L1 2 θ0 < J L1 2 θ)
      ∧ (∀ lam : ℝ, 0 ≤ lam → ∀ θ ∈ admissibleQuotients, θ ≠ θ0 → J L2 lam θ0 < J L2 lam θ)
      -- ordering by inverse canonical allocation at the optima
      ∧ 1 / s θB < 1 / s θ0 := by
  intro R s θ0 θB L1 L2 J
  have hθ0 : θ0 ∈ admissibleQuotients := ⟨by norm_num, by norm_num⟩
  have hθB : θB ∈ admissibleQuotients := ⟨by norm_num, by norm_num⟩
  have hR0 : R θ0 = 0 := by
    have := Rcan_prior_eq_zero (gamma0 := 0) (nu0 := 2) (alpha0 := 1 / 2) (beta0 := 1)
      (by norm_num) (by norm_num) (by norm_num)
    rw [witness_prior_base] at this
    exact this
  have hRB : 0 < R θB :=
    Rcan_pos_of_gamma_ne (by norm_num) (by norm_num) (by norm_num) hθB (by norm_num)
      (by norm_num)
  have hRnn : ∀ θ, 0 ≤ R θ := fun θ => Rcan_nonneg θ
  have hne : θB ≠ θ0 := by
    intro h
    have := congrArg QuotientState.gamma h
    norm_num [θB, θ0] at this
  have hJ : ∀ L lam θ, J L lam θ = L θ + lam * R θ := fun _ _ _ => rfl
  refine ⟨fun θ _ hθ => ?_, fun θ _ hθ => ?_, fun lam hlam θ _ hθ => ?_, ?_⟩
  · -- λ = 1: `J = h`
    rw [hJ, hJ]
    by_cases h0 : θ = θ0
    · rw [h0]
      simp only [L1, witnessL1]
      simp [hne, hR0]
      linarith
    · simp only [L1, witnessL1]
      simp [hne, h0, hθ]
      linarith
  · -- λ = 2: `J = h + R`
    rw [hJ, hJ]
    by_cases hb : θ = θB
    · rw [hb]
      simp only [L1, witnessL1]
      simp [hne, hR0]
      linarith
    · simp only [L1, witnessL1]
      simp [hθ, hb, hR0]
      linarith [hRnn θ]
  · rw [hJ, hJ]
    simp only [L2, witnessL2]
    simp [hθ, hR0]
    nlinarith [hRnn θ]
  · simp only [s, θB, θ0, witness_nuCan_B, witness_nuCan_base]
    norm_num

end OrderingWitness

end ELVAE
