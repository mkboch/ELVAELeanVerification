import Mathlib
import ELVAELeanVerification.ParameterBridge

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Exact partial minimization

The four-coordinate objective is

  J₄(θ, ν) = L_rec(θ) + λ · R(θ, ν),

where `θ = (γ, α, c)` is the quotient state, `ν` the fiber coordinate,
`L_rec` does not depend on `ν`, and `R(θ, ν)` is the KL regularizer
restricted to the fiber `β = c ν / (1 + ν)`.
The three-coordinate objective is

  J₃(θ) = L_rec(θ) + λ · R_can(θ),   R_can(θ) = min_{ν > 0} R(θ, ν).

This module proves exact partial minimization in two layers.

1. An abstract partial-minimization theorem: for any quotient-state type,
   any admissible set `S`, any fiber domain `F`, any `ν`-independent term
   `L`, any regularizer `R`, and any selector `s` that is the unique
   minimizer of `R θ` on `F`:
   * `J₄(θ, s θ) = J₃(θ)`;
   * `J₃(θ) ≤ J₄(θ, ν)` for `λ ≥ 0`;
   * `J₃(θ) < J₄(θ, ν)` for `λ > 0` and `ν ≠ s θ`;
   * `R_can θ = sInf (R θ '' F)`;
   * `sInf J₄(S × F) = sInf J₃(S)` in `ℝ`, with no boundedness or
     nonemptiness side conditions (the two value sets have the same lower
     bounds, so their real infima coincide in every case);
   * minimizers correspond exactly: `(θ, ν)` minimizes `J₄` iff `θ`
     minimizes `J₃` and `ν = s θ` (for `λ > 0`).

2. Instantiation with the ELVAE fiber: `R(θ, ν) = fiberObjective α₀ B(θ) ν + C(θ)`
   with an *arbitrary* `ν`-independent term `C(θ)`, selector
   `ν_can(θ) = nuCanFromParams`, and an *arbitrary* reconstruction term.
   The link from this form to the explicit closed-form NIG KL is proved
   in `RestrictedKLDivergence.lean`.
-/

namespace ELVAE

section Abstract

variable {Θ : Type*}

/-- Four-coordinate objective `J₄(θ, ν) = L(θ) + λ R(θ, ν)`. -/
def partialJ4 (L : Θ → ℝ) (R : Θ → ℝ → ℝ) (lam : ℝ)
    (θ : Θ) (ν : ℝ) : ℝ :=
  L θ + lam * R θ ν

/-- Three-coordinate objective `J₃(θ) = L(θ) + λ R(θ, s θ)`. -/
def partialJ3 (L : Θ → ℝ) (R : Θ → ℝ → ℝ) (s : Θ → ℝ) (lam : ℝ)
    (θ : Θ) : ℝ :=
  L θ + lam * R θ (s θ)

/-- Value set of `J₄` over admissible states and fiber coordinates. -/
def J4Values (S : Set Θ) (F : Set ℝ)
    (L : Θ → ℝ) (R : Θ → ℝ → ℝ) (lam : ℝ) : Set ℝ :=
  {y | ∃ θ ∈ S, ∃ ν ∈ F, partialJ4 L R lam θ ν = y}

/-- Value set of `J₃` over admissible states. -/
def J3Values (S : Set Θ)
    (L : Θ → ℝ) (R : Θ → ℝ → ℝ) (s : Θ → ℝ) (lam : ℝ) : Set ℝ :=
  partialJ3 L R s lam '' S

/-- The selector representative realizes `J₃` exactly. -/
theorem partialJ4_at_selector
    (L : Θ → ℝ) (R : Θ → ℝ → ℝ) (s : Θ → ℝ) (lam : ℝ) (θ : Θ) :
    partialJ4 L R lam θ (s θ) = partialJ3 L R s lam θ :=
  rfl

/-- `J₃` is a lower bound for `J₄` along each fiber (only `λ ≥ 0` is needed). -/
theorem partialJ3_le_partialJ4
    {F : Set ℝ} (L : Θ → ℝ) (R : Θ → ℝ → ℝ) (s : Θ → ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) {θ : Θ}
    (hmin : ∀ ν ∈ F, R θ (s θ) ≤ R θ ν)
    {ν : ℝ} (hν : ν ∈ F) :
    partialJ3 L R s lam θ ≤ partialJ4 L R lam θ ν := by
  unfold partialJ3 partialJ4
  have := mul_le_mul_of_nonneg_left (hmin ν hν) hlam
  linarith

/-- Every non-selector fiber representative is strictly penalized (`λ > 0`). -/
theorem partialJ3_lt_partialJ4
    {F : Set ℝ} (L : Θ → ℝ) (R : Θ → ℝ → ℝ) (s : Θ → ℝ)
    {lam : ℝ} (hlam : 0 < lam) {θ : Θ}
    (hstrict : ∀ ν ∈ F, ν ≠ s θ → R θ (s θ) < R θ ν)
    {ν : ℝ} (hν : ν ∈ F) (hne : ν ≠ s θ) :
    partialJ3 L R s lam θ < partialJ4 L R lam θ ν := by
  unfold partialJ3 partialJ4
  have := mul_lt_mul_of_pos_left (hstrict ν hν hne) hlam
  linarith

/-- The selector value is the least value of `R θ` on the fiber. -/
theorem selector_isLeast
    {F : Set ℝ} (R : Θ → ℝ → ℝ) (s : Θ → ℝ) {θ : Θ}
    (hsF : s θ ∈ F)
    (hmin : ∀ ν ∈ F, R θ (s θ) ≤ R θ ν) :
    IsLeast (R θ '' F) (R θ (s θ)) := by
  refine ⟨⟨s θ, hsF, rfl⟩, ?_⟩
  rintro y ⟨ν, hν, rfl⟩
  exact hmin ν hν

/-- `R_can(θ) = R(θ, s θ)` is the fiber infimum `inf_{ν ∈ F} R(θ, ν)`. -/
theorem selector_eq_sInf
    {F : Set ℝ} (R : Θ → ℝ → ℝ) (s : Θ → ℝ) {θ : Θ}
    (hsF : s θ ∈ F)
    (hmin : ∀ ν ∈ F, R θ (s θ) ≤ R θ ν) :
    sInf (R θ '' F) = R θ (s θ) :=
  (selector_isLeast R s hsF hmin).csInf_eq

/--
Two subsets of `ℝ` with the same lower bounds and the same nonemptiness
have the same real infimum. No boundedness hypothesis is needed.
-/
theorem real_sInf_eq_of_lowerBounds_eq
    {A B : Set ℝ}
    (hlb : lowerBounds A = lowerBounds B)
    (hne : A.Nonempty ↔ B.Nonempty) :
    sInf A = sInf B := by
  rcases B.eq_empty_or_nonempty with hB | hB
  · have hA : A = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro a ha
      have : B.Nonempty := hne.mp ⟨a, ha⟩
      rw [hB] at this
      exact Set.not_nonempty_empty this
    rw [hA, hB]
  · by_cases hbdd : BddBelow B
    · have hglb : IsGLB B (sInf B) := isGLB_csInf hB hbdd
      have hglbA : IsGLB A (sInf B) := by
        unfold IsGLB IsGreatest at hglb ⊢
        rw [hlb]
        exact hglb
      exact hglbA.csInf_eq (hne.mpr hB)
    · have hbddA : ¬ BddBelow A := by
        intro h
        apply hbdd
        obtain ⟨m, hm⟩ := h
        exact ⟨m, hlb ▸ hm⟩
      rw [Real.sInf_of_not_bddBelow hbdd, Real.sInf_of_not_bddBelow hbddA]

/--
The value sets of `J₄` and `J₃` have the same lower bounds, assuming the
selector lies in the fiber domain and minimizes `R θ` there
(`λ ≥ 0` suffices).
-/
theorem J4Values_lowerBounds_eq
    {S : Set Θ} {F : Set ℝ}
    (L : Θ → ℝ) (R : Θ → ℝ → ℝ) (s : Θ → ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hsF : ∀ θ ∈ S, s θ ∈ F)
    (hmin : ∀ θ ∈ S, ∀ ν ∈ F, R θ (s θ) ≤ R θ ν) :
    lowerBounds (J4Values S F L R lam)
      = lowerBounds (J3Values S L R s lam) := by
  ext m
  constructor
  · rintro hm y ⟨θ, hθ, rfl⟩
    exact hm ⟨θ, hθ, s θ, hsF θ hθ, rfl⟩
  · rintro hm y ⟨θ, hθ, ν, hν, rfl⟩
    exact le_trans (hm ⟨θ, hθ, rfl⟩)
      (partialJ3_le_partialJ4 L R s hlam (hmin θ hθ) hν)

theorem J4Values_nonempty_iff
    {S : Set Θ} {F : Set ℝ}
    (L : Θ → ℝ) (R : Θ → ℝ → ℝ) (s : Θ → ℝ) (lam : ℝ)
    (hsF : ∀ θ ∈ S, s θ ∈ F) :
    (J4Values S F L R lam).Nonempty
      ↔ (J3Values S L R s lam).Nonempty := by
  constructor
  · rintro ⟨_, θ, hθ, _, _, rfl⟩
    exact ⟨_, θ, hθ, rfl⟩
  · rintro ⟨_, θ, hθ, rfl⟩
    exact ⟨_, θ, hθ, s θ, hsF θ hθ, rfl⟩

/--
**Abstract partial minimization (infimum equality).**

  inf_{θ ∈ S, ν ∈ F} J₄(θ, ν) = inf_{θ ∈ S} J₃(θ)

as real infima (`sInf` on `ℝ`), unconditionally in `S`: if either side is
unbounded below or empty, so is the other, and both conventions agree.
-/
theorem partial_minimization_sInf_eq
    {S : Set Θ} {F : Set ℝ}
    (L : Θ → ℝ) (R : Θ → ℝ → ℝ) (s : Θ → ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hsF : ∀ θ ∈ S, s θ ∈ F)
    (hmin : ∀ θ ∈ S, ∀ ν ∈ F, R θ (s θ) ≤ R θ ν) :
    sInf (J4Values S F L R lam) = sInf (J3Values S L R s lam) :=
  real_sInf_eq_of_lowerBounds_eq
    (J4Values_lowerBounds_eq L R s hlam hsF hmin)
    (J4Values_nonempty_iff L R s lam hsF)

/-- The infimum of `J₄` is attained iff the infimum of `J₃` is, with the same value. -/
theorem partial_minimization_isLeast_iff
    {S : Set Θ} {F : Set ℝ}
    (L : Θ → ℝ) (R : Θ → ℝ → ℝ) (s : Θ → ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hsF : ∀ θ ∈ S, s θ ∈ F)
    (hmin : ∀ θ ∈ S, ∀ ν ∈ F, R θ (s θ) ≤ R θ ν)
    (m : ℝ) :
    IsLeast (J4Values S F L R lam) m
      ↔ IsLeast (J3Values S L R s lam) m := by
  have hlb := J4Values_lowerBounds_eq L R s hlam hsF hmin
  constructor
  · rintro ⟨⟨θ, hθ, ν, hν, hval⟩, hlow⟩
    refine ⟨⟨θ, hθ, ?_⟩, hlb ▸ hlow⟩
    apply le_antisymm
    · rw [← hval]
      exact partialJ3_le_partialJ4 L R s hlam (hmin θ hθ) hν
    · exact hlow ⟨θ, hθ, s θ, hsF θ hθ, rfl⟩
  · rintro ⟨⟨θ, hθ, hval⟩, hlow⟩
    exact ⟨⟨θ, hθ, s θ, hsF θ hθ, hval⟩, hlb.symm ▸ hlow⟩

/--
**Minimizer correspondence.** For `λ > 0`, `(θ, ν)` minimizes `J₄` over
`S × F` iff `θ` minimizes `J₃` over `S` and `ν = s θ` is the canonical
representative.
-/
theorem partial_minimization_minimizer_iff
    {S : Set Θ} {F : Set ℝ}
    (L : Θ → ℝ) (R : Θ → ℝ → ℝ) (s : Θ → ℝ)
    {lam : ℝ} (hlam : 0 < lam)
    (hsF : ∀ θ ∈ S, s θ ∈ F)
    (hmin : ∀ θ ∈ S, ∀ ν ∈ F, R θ (s θ) ≤ R θ ν)
    (hstrict : ∀ θ ∈ S, ∀ ν ∈ F, ν ≠ s θ → R θ (s θ) < R θ ν)
    {θ : Θ} (hθ : θ ∈ S) {ν : ℝ} (hν : ν ∈ F) :
    (∀ θ' ∈ S, ∀ ν' ∈ F, partialJ4 L R lam θ ν ≤ partialJ4 L R lam θ' ν')
      ↔
    (ν = s θ ∧ ∀ θ' ∈ S, partialJ3 L R s lam θ ≤ partialJ3 L R s lam θ') := by
  constructor
  · intro h
    have hνeq : ν = s θ := by
      by_contra hne
      have hlt := partialJ3_lt_partialJ4 L R s hlam (hstrict θ hθ) hν hne
      have hle := h θ hθ (s θ) (hsF θ hθ)
      rw [partialJ4_at_selector] at hle
      linarith
    refine ⟨hνeq, fun θ' hθ' => ?_⟩
    have := h θ' hθ' (s θ') (hsF θ' hθ')
    rw [hνeq, partialJ4_at_selector, partialJ4_at_selector] at this
    exact this
  · rintro ⟨rfl, h⟩ θ' hθ' ν' hν'
    rw [partialJ4_at_selector]
    exact le_trans (h θ' hθ')
      (partialJ3_le_partialJ4 L R s hlam.le (hmin θ' hθ') hν')

end Abstract

/-! ## Instantiation with the ELVAE fiber objective -/

/-- Quotient coordinates `θ = (γ, α, c)`. -/
structure QuotientState where
  gamma : ℝ
  alpha : ℝ
  c : ℝ

/-- Admissible quotient domain `ℝ × (0, ∞) × (0, ∞)`. -/
def QuotientState.Admissible (θ : QuotientState) : Prop :=
  0 < θ.alpha ∧ 0 < θ.c

/-- The set of admissible quotient states. -/
def admissibleQuotients : Set QuotientState :=
  {θ | θ.Admissible}

/-- The scalar `B(θ)` at a quotient state. -/
noncomputable def QuotientState.B
    (gamma0 nu0 beta0 : ℝ) (θ : QuotientState) : ℝ :=
  BFromParams θ.gamma θ.alpha θ.c gamma0 nu0 beta0

/-- The canonical selector at a quotient state. -/
noncomputable def QuotientState.nuCan
    (gamma0 nu0 alpha0 beta0 : ℝ) (θ : QuotientState) : ℝ :=
  nuCanFromParams θ.gamma θ.alpha θ.c gamma0 nu0 alpha0 beta0

/--
Restricted regularizer of the form

  R(θ, ν) = (α₀ + 1/2) log ν − α₀ log(1 + ν) + B(θ)/ν + C(θ),

with an arbitrary `ν`-independent term `C`.
-/
noncomputable def restrictedRegularizer
    (gamma0 nu0 alpha0 beta0 : ℝ) (C : QuotientState → ℝ)
    (θ : QuotientState) (ν : ℝ) : ℝ :=
  fiberObjective alpha0 (θ.B gamma0 nu0 beta0) ν + C θ

theorem restrictedRegularizer_strict_min
    (gamma0 nu0 alpha0 beta0 : ℝ) (C : QuotientState → ℝ)
    (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients)
    {ν : ℝ} (hν : ν ∈ Set.Ioi (0 : ℝ))
    (hne : ν ≠ θ.nuCan gamma0 nu0 alpha0 beta0) :
    restrictedRegularizer gamma0 nu0 alpha0 beta0 C θ
        (θ.nuCan gamma0 nu0 alpha0 beta0)
      < restrictedRegularizer gamma0 nu0 alpha0 beta0 C θ ν := by
  have hB : 0 < θ.B gamma0 nu0 beta0 :=
    BFromParams_positive _ _ _ _ _ _ hθ.1 hθ.2 hnu0 hbeta0
  unfold restrictedRegularizer
  have := fiberObjective_strict_global_min alpha0 _ ν hB hν hne
  simp only [QuotientState.nuCan, nuCanFromParams] at this ⊢
  exact add_lt_add_left this _

theorem restrictedRegularizer_min
    (gamma0 nu0 alpha0 beta0 : ℝ) (C : QuotientState → ℝ)
    (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) :
    ∀ θ ∈ admissibleQuotients, ∀ ν ∈ Set.Ioi (0 : ℝ),
      restrictedRegularizer gamma0 nu0 alpha0 beta0 C θ
          (θ.nuCan gamma0 nu0 alpha0 beta0)
        ≤ restrictedRegularizer gamma0 nu0 alpha0 beta0 C θ ν := by
  intro θ hθ ν hν
  by_cases hne : ν = θ.nuCan gamma0 nu0 alpha0 beta0
  · rw [hne]
  · exact (restrictedRegularizer_strict_min gamma0 nu0 alpha0 beta0 C
      hnu0 hbeta0 hθ hν hne).le

theorem QuotientState.nuCan_mem
    (gamma0 nu0 alpha0 beta0 : ℝ)
    (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) :
    ∀ θ ∈ admissibleQuotients,
      θ.nuCan gamma0 nu0 alpha0 beta0 ∈ Set.Ioi (0 : ℝ) := by
  intro θ hθ
  exact nuCanFromParams_positive _ _ _ _ _ _ _ hθ.1 hθ.2 hnu0 hbeta0

/--
**ELVAE instantiation, fixed quotient state.**

For every admissible quotient state `θ`, every reconstruction term `L`
(independent of `ν`), every `ν`-independent constant `C`, and `λ > 0`:

1. the canonical representative realizes `J₃(θ)`;
2. `J₃(θ) ≤ J₄(θ, ν)` for every `ν > 0`;
3. `J₃(θ) < J₄(θ, ν)` for every non-canonical `ν > 0`.
-/
theorem theorem2_fixed_state
    (gamma0 nu0 alpha0 beta0 lam : ℝ)
    (L C : QuotientState → ℝ)
    (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) (hlam : 0 < lam)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) :
    let R := restrictedRegularizer gamma0 nu0 alpha0 beta0 C
    let s := QuotientState.nuCan gamma0 nu0 alpha0 beta0
    partialJ4 L R lam θ (s θ) = partialJ3 L R s lam θ
    ∧ (∀ ν, 0 < ν → partialJ3 L R s lam θ ≤ partialJ4 L R lam θ ν)
    ∧ (∀ ν, 0 < ν → ν ≠ s θ → partialJ3 L R s lam θ < partialJ4 L R lam θ ν) := by
  intro R s
  refine ⟨rfl, fun ν hν => ?_, fun ν hν hne => ?_⟩
  · exact partialJ3_le_partialJ4 L R s hlam.le
      (restrictedRegularizer_min gamma0 nu0 alpha0 beta0 C hnu0 hbeta0 θ hθ) hν
  · exact partialJ3_lt_partialJ4 L R s hlam
      (fun ν' hν' hne' => restrictedRegularizer_strict_min gamma0 nu0 alpha0 beta0 C
        hnu0 hbeta0 hθ hν' hne') hν hne

/--
**ELVAE instantiation, infimum equality.**

  inf_{(γ,α,c) admissible, ν > 0} J₄ = inf_{(γ,α,c) admissible} J₃,

and `R_can(θ)` is the fiber infimum of `R(θ, ·)` over `ν > 0`.
-/
theorem theorem2_sInf_eq
    (gamma0 nu0 alpha0 beta0 lam : ℝ)
    (L C : QuotientState → ℝ)
    (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) (hlam : 0 ≤ lam) :
    sInf (J4Values admissibleQuotients (Set.Ioi 0) L
        (restrictedRegularizer gamma0 nu0 alpha0 beta0 C) lam)
      =
    sInf (J3Values admissibleQuotients L
        (restrictedRegularizer gamma0 nu0 alpha0 beta0 C)
        (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam) :=
  partial_minimization_sInf_eq L _ _ hlam
    (QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0)
    (restrictedRegularizer_min gamma0 nu0 alpha0 beta0 C hnu0 hbeta0)

/-- `R_can(θ) = inf_{ν > 0} R(θ, ν)`, attained at `ν_can(θ)`. -/
theorem Rcan_eq_fiber_sInf
    (gamma0 nu0 alpha0 beta0 : ℝ) (C : QuotientState → ℝ)
    (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) :
    sInf (restrictedRegularizer gamma0 nu0 alpha0 beta0 C θ '' Set.Ioi 0)
      = restrictedRegularizer gamma0 nu0 alpha0 beta0 C θ
          (θ.nuCan gamma0 nu0 alpha0 beta0) :=
  selector_eq_sInf _ _
    (QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0 θ hθ)
    (restrictedRegularizer_min gamma0 nu0 alpha0 beta0 C hnu0 hbeta0 θ hθ)

/--
**ELVAE instantiation, minimizers.** For `λ > 0`, a pair
`(θ, ν)` minimizes `J₄` iff `θ` minimizes `J₃` and `ν = ν_can(θ)`.
-/
theorem theorem2_minimizer_iff
    (gamma0 nu0 alpha0 beta0 lam : ℝ)
    (L C : QuotientState → ℝ)
    (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) (hlam : 0 < lam)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) {ν : ℝ} (hν : 0 < ν) :
    (∀ θ' ∈ admissibleQuotients, ∀ ν' ∈ Set.Ioi (0 : ℝ),
        partialJ4 L (restrictedRegularizer gamma0 nu0 alpha0 beta0 C) lam θ ν
          ≤ partialJ4 L (restrictedRegularizer gamma0 nu0 alpha0 beta0 C) lam θ' ν')
      ↔
    (ν = θ.nuCan gamma0 nu0 alpha0 beta0
      ∧ ∀ θ' ∈ admissibleQuotients,
        partialJ3 L (restrictedRegularizer gamma0 nu0 alpha0 beta0 C)
            (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam θ
          ≤ partialJ3 L (restrictedRegularizer gamma0 nu0 alpha0 beta0 C)
            (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam θ') :=
  partial_minimization_minimizer_iff L _ _ hlam
    (QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0)
    (restrictedRegularizer_min gamma0 nu0 alpha0 beta0 C hnu0 hbeta0)
    (fun _ hθ' _ hν' hne => restrictedRegularizer_strict_min gamma0 nu0 alpha0 beta0 C
      hnu0 hbeta0 hθ' hν' hne)
    hθ hν

end ELVAE
