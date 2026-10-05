import Mathlib
import Official.M07
import Official.M08
import Official.M12

/-!
# Changing `λ` can reverse orderings at optima

Independence of fiber selection from `λ > 0` does not imply that selected
allocation orderings are invariant across optimizers obtained with different weights; this can
occur with a common complete prior and finite, nonnegative reconstruction losses. For every
complete prior, with `x₀ = (γ₀, A, s₀)`, `x₁ = (γ₀, A, 4s₀)`, `x₂ = (γ₀, A, 2s₀)` and the two
losses of the counterexample (inputs `y₁`, `y₂` encoded as `true`, `false`), the optimum for `y₁`
is `x₁` at `λ₋ = 1/(2R₁)` and `x₀` at `λ₊ = 2/R₁`, while the optimum for `y₂` is `x₂` at both
weights, so the order of the selected allocations reverses; `Official.M08` transfers this to the
original objectives.
-/

noncomputable section

namespace NIGBottleneck

variable (p₀ : Parameters)

/-- `x₁ = (γ₀, A, 4s₀)`. -/
def lamX₁ : QuotientState :=
  ⟨p₀.gamma, p₀.alpha, 4 * (priorQuotient p₀).s, p₀.alpha_pos,
    by have := (priorQuotient p₀).s_pos; positivity⟩

/-- `x₂ = (γ₀, A, 2s₀)`. -/
def lamX₂ : QuotientState :=
  ⟨p₀.gamma, p₀.alpha, 2 * (priorQuotient p₀).s, p₀.alpha_pos,
    by have := (priorQuotient p₀).s_pos; positivity⟩

lemma lamX_ne : lamX₁ p₀ ≠ priorQuotient p₀ ∧ lamX₂ p₀ ≠ priorQuotient p₀
    ∧ lamX₁ p₀ ≠ lamX₂ p₀ := by
  have hs := (priorQuotient p₀).s_pos
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrArg QuotientState.s h
    simp only [lamX₁] at this
    linarith
  · have := congrArg QuotientState.s h
    simp only [lamX₂] at this
    linarith
  · have := congrArg QuotientState.s h
    simp only [lamX₁, lamX₂] at this
    linarith

/-- The scores satisfy `Q₁ < Q₂ < Q₀`, so `ν₁ < ν₂ < ν₀`. -/
theorem lam_scores :
    scoreQ p₀ (lamX₁ p₀) < scoreQ p₀ (lamX₂ p₀)
      ∧ scoreQ p₀ (lamX₂ p₀) < scoreQ p₀ (priorQuotient p₀)
      ∧ selNu p₀ (lamX₁ p₀) < selNu p₀ (lamX₂ p₀)
      ∧ selNu p₀ (lamX₂ p₀) < selNu p₀ (priorQuotient p₀) := by
  have hs := (priorQuotient p₀).s_pos
  have hb := bParam_pos p₀
  have hA := p₀.alpha_pos
  have hQ1 : scoreQ p₀ (lamX₁ p₀) < scoreQ p₀ (lamX₂ p₀) := by
    simp only [scoreQ, lamX₁, lamX₂, sub_self]
    apply div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  have hQ2 : scoreQ p₀ (lamX₂ p₀) < scoreQ p₀ (priorQuotient p₀) := by
    have e : (priorQuotient p₀).gamma = p₀.gamma := rfl
    have e' : (priorQuotient p₀).alpha = p₀.alpha := rfl
    simp only [scoreQ, lamX₂, e, e', sub_self]
    apply div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  exact ⟨hQ1, hQ2, (selNu_lt_iff_score p₀ _ _).mpr hQ1, (selNu_lt_iff_score p₀ _ _).mpr hQ2⟩

lemma regularizerR_pos_of_ne (x : QuotientState) (hx : x ≠ priorQuotient p₀) :
    0 < regularizerR p₀ x := by
  rcases (regularizerR_nonneg p₀ x).lt_or_eq with h | h
  · exact h
  · exact absurd ((minimizedKL_eq_zero_iff p₀ x).mp h.symm) hx

/-- `λ₋ = 1/(2R₁)`. -/
def lamMinus : PositiveReal :=
  ⟨1 / (2 * regularizerR p₀ (lamX₁ p₀)), by
    have := regularizerR_pos_of_ne p₀ _ (lamX_ne p₀).1; positivity⟩

/-- `λ₊ = 2/R₁`. -/
def lamPlus : PositiveReal :=
  ⟨2 / regularizerR p₀ (lamX₁ p₀), by
    have := regularizerR_pos_of_ne p₀ _ (lamX_ne p₀).1; positivity⟩

open Classical in
/-- The reconstruction loss of the counterexample; `true` is the input `y₁` and
`false` the input `y₂`. -/
def lamLoss : ReconstructionLoss Bool := fun μ y =>
  if y then
    (if μ = quotientLaw (lamX₁ p₀) then 0 else if μ = quotientLaw (priorQuotient p₀) then 1 else 2)
  else
    (if μ = quotientLaw (lamX₂ p₀) then 0
      else (((1 + (lamPlus p₀).val * regularizerR p₀ (lamX₂ p₀) : ℝ)) : EReal))

/-- The losses are finite and nonnegative. -/
theorem lamLoss_finite_nonneg (μ : MeasureTheory.Measure ℝ) (y : Bool) :
    0 ≤ lamLoss p₀ μ y ∧ lamLoss p₀ μ y ≠ ⊤ := by
  classical
  have hR2 := regularizerR_nonneg p₀ (lamX₂ p₀)
  have hw := (lamPlus p₀).property
  unfold lamLoss
  cases y <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs
  · exact ⟨le_rfl, EReal.zero_ne_top⟩
  · exact ⟨EReal.coe_nonneg.mpr (by positivity), EReal.coe_ne_top _⟩
  · exact ⟨le_rfl, EReal.zero_ne_top⟩
  · exact ⟨zero_le_one, ne_of_lt (EReal.coe_lt_top 1)⟩
  · exact ⟨by norm_num, ne_of_lt (EReal.coe_lt_top 2)⟩

open Classical in
lemma quotientLoss_lam (x : QuotientState) (y : Bool) :
    quotientLoss (lamLoss p₀) x y = if y then
      (if x = lamX₁ p₀ then 0 else if x = priorQuotient p₀ then 1 else 2)
    else (if x = lamX₂ p₀ then 0
      else (((1 + (lamPlus p₀).val * regularizerR p₀ (lamX₂ p₀) : ℝ)) : EReal)) := by
  classical
  simp only [quotientLoss, lamLoss, quotientLaw_injective.eq_iff]

lemma ereal_lt_add_nonneg {a b : ℝ} (hab : a < b) {c : ℝ} (hc : 0 ≤ c) :
    ((a : ℝ) : EReal) < ((b : ℝ) : EReal) + ((c : ℝ) : EReal) := by
  rw [← EReal.coe_add, EReal.coe_lt_coe_iff]
  linarith

/-- Unique optimum `x_*` of `J₃(·; y)` at weight `w`. -/
def UniqueOptimum (w : PositiveReal) (y : Bool) (x : QuotientState) : Prop :=
  ∀ x', x' ≠ x → reducedObjective (lamLoss p₀) p₀ w x y < reducedObjective (lamLoss p₀) p₀ w x' y

theorem optimum_y₁_minus : UniqueOptimum p₀ (lamMinus p₀) true (lamX₁ p₀) := by
  classical
  obtain ⟨hne1, -, -⟩ := lamX_ne p₀
  have hR1 := regularizerR_pos_of_ne p₀ _ hne1
  have hRnn := regularizerR_nonneg p₀
  intro x hx
  have hval : (lamMinus p₀).val * regularizerR p₀ (lamX₁ p₀) = 1 / 2 := by
    change 1 / (2 * regularizerR p₀ (lamX₁ p₀)) * regularizerR p₀ (lamX₁ p₀) = 1 / 2
    field_simp
  have hv : reducedObjective (lamLoss p₀) p₀ (lamMinus p₀) (lamX₁ p₀) true
      = ((1 / 2 : ℝ) : EReal) := by
    rw [reducedObjective, quotientLoss_lam]
    simp only [↓reduceIte]
    rw [hval, zero_add]
  rw [hv, reducedObjective, quotientLoss_lam]
  simp only [hx, ↓reduceIte]
  have hw : 0 ≤ (lamMinus p₀).val * regularizerR p₀ x :=
    mul_nonneg (lamMinus p₀).property.le (hRnn x)
  split_ifs
  · rw [← EReal.coe_one]
    exact ereal_lt_add_nonneg (by norm_num) hw
  · rw [show (2 : EReal) = ((2 : ℝ) : EReal) by norm_cast]
    exact ereal_lt_add_nonneg (by norm_num) hw

theorem optimum_y₁_plus : UniqueOptimum p₀ (lamPlus p₀) true (priorQuotient p₀) := by
  classical
  obtain ⟨hne1, -, -⟩ := lamX_ne p₀
  have hR1 := regularizerR_pos_of_ne p₀ _ hne1
  have hRnn := regularizerR_nonneg p₀
  have hR0 : regularizerR p₀ (priorQuotient p₀) = 0 := minimizedKL_priorQuotient p₀
  intro x hx
  have hv : reducedObjective (lamLoss p₀) p₀ (lamPlus p₀) (priorQuotient p₀) true
      = ((1 : ℝ) : EReal) := by
    rw [reducedObjective, quotientLoss_lam]
    simp only [Ne.symm hne1, ↓reduceIte, hR0, mul_zero, EReal.coe_zero, add_zero, EReal.coe_one]
  rw [hv, reducedObjective, quotientLoss_lam]
  have hw : 0 ≤ (lamPlus p₀).val * regularizerR p₀ x :=
    mul_nonneg (lamPlus p₀).property.le (hRnn x)
  simp only [hx, ↓reduceIte]
  by_cases h1 : x = lamX₁ p₀
  · subst h1
    simp only [↓reduceIte]
    have : (lamPlus p₀).val * regularizerR p₀ (lamX₁ p₀) = 2 := by
      change 2 / regularizerR p₀ (lamX₁ p₀) * regularizerR p₀ (lamX₁ p₀) = 2
      field_simp
    rw [this, zero_add, EReal.coe_lt_coe_iff]
    norm_num
  · simp only [h1, ↓reduceIte]
    rw [show (2 : EReal) = ((2 : ℝ) : EReal) by norm_cast]
    exact ereal_lt_add_nonneg (by norm_num) hw

theorem optimum_y₂ (w : PositiveReal) (hw : w.val ≤ (lamPlus p₀).val) :
    UniqueOptimum p₀ w false (lamX₂ p₀) := by
  classical
  have hRnn := regularizerR_nonneg p₀
  intro x hx
  rw [reducedObjective, reducedObjective, quotientLoss_lam, quotientLoss_lam]
  simp only [Bool.false_eq_true, ↓reduceIte, hx]
  rw [zero_add, ← EReal.coe_add, EReal.coe_lt_coe_iff]
  have h1 : w.val * regularizerR p₀ (lamX₂ p₀) ≤ (lamPlus p₀).val * regularizerR p₀ (lamX₂ p₀) :=
    mul_le_mul_of_nonneg_right hw (hRnn _)
  have h2 : 0 ≤ w.val * regularizerR p₀ x := mul_nonneg w.property.le (hRnn x)
  linarith

theorem lamMinus_le_lamPlus : (lamMinus p₀).val ≤ (lamPlus p₀).val := by
  have := regularizerR_pos_of_ne p₀ _ (lamX_ne p₀).1
  simp only [lamMinus, lamPlus]
  rw [div_le_div_iff₀ (by positivity) this]
  nlinarith

/-- A unique minimizer of `J₃` has a finite infimum, and its selected representative is the unique
minimizer of `J₄`. -/
theorem unique_original_minimizer (w : PositiveReal) (y : Bool) (x : QuotientState)
    (hx : UniqueOptimum p₀ w y x) (p : Parameters) :
    originalObjective (lamLoss p₀) p p₀ w y = ⨅ q, originalObjective (lamLoss p₀) q p₀ w y
      ↔ p = fiberParameters x (selTPos p₀ x) := by
  have hmin : ⨅ x', reducedObjective (lamLoss p₀) p₀ w x' y
      = reducedObjective (lamLoss p₀) p₀ w x y := by
    refine le_antisymm (iInf_le _ _) (le_iInf fun x' => ?_)
    by_cases h : x' = x
    · rw [h]
    · exact (hx x' h).le
  have hℓ : ∀ x', quotientLoss (lamLoss p₀) x' y ≠ ⊥ := fun x' =>
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (lamLoss_finite_nonneg p₀ _ y).1)
  have hval : reducedObjective (lamLoss p₀) p₀ w x y ≠ ⊥
      ∧ reducedObjective (lamLoss p₀) p₀ w x y ≠ ⊤ := by
    rw [reducedObjective]
    exact ⟨EReal.add_ne_bot_iff.mpr ⟨hℓ x, EReal.coe_ne_bot _⟩,
      EReal.add_ne_top_iff_ne_top₂ (hℓ x) (EReal.coe_ne_bot _) |>.mpr
        ⟨(lamLoss_finite_nonneg p₀ _ y).2, EReal.coe_ne_top _⟩⟩
  rw [originalObjective_minimizer_iff (lamLoss p₀) p₀ w y hℓ (by rw [hmin]; exact hval) p, hmin]
  constructor
  · rintro ⟨h3, hp⟩
    have hq : quotientCoordinates p = x := by
      by_contra hne
      exact (hx _ hne).ne' h3
    rw [hp, hq]
  · rintro rfl
    rw [quotientCoordinates_fiberParameters]
    exact ⟨rfl, rfl⟩

/-- Changing `λ` can reverse the ordering of the selected allocations at
optima, with a common complete prior and finite nonnegative reconstruction losses. At `λ₋` the
unique optima for `y₁`, `y₂` are `x₁`, `x₂`, with `ν_sel(x₁) < ν_sel(x₂)`; at `λ₊` they are `x₀`,
`x₂`, with `ν_sel(x₀) > ν_sel(x₂)`. `Official.M08` transfers this to the original four-parameter
objectives, whose unique minimizers are the selected representatives, with `ν = ν_sel`. -/
theorem lambda_reverses_order :
    (∀ μ y, 0 ≤ lamLoss p₀ μ y ∧ lamLoss p₀ μ y ≠ ⊤)
      ∧ UniqueOptimum p₀ (lamMinus p₀) true (lamX₁ p₀)
      ∧ UniqueOptimum p₀ (lamMinus p₀) false (lamX₂ p₀)
      ∧ UniqueOptimum p₀ (lamPlus p₀) true (priorQuotient p₀)
      ∧ UniqueOptimum p₀ (lamPlus p₀) false (lamX₂ p₀)
      ∧ selNu p₀ (lamX₁ p₀) < selNu p₀ (lamX₂ p₀)
      ∧ selNu p₀ (lamX₂ p₀) < selNu p₀ (priorQuotient p₀)
      ∧ (∀ p, originalObjective (lamLoss p₀) p p₀ (lamMinus p₀) true
            = ⨅ q, originalObjective (lamLoss p₀) q p₀ (lamMinus p₀) true
          ↔ p = fiberParameters (lamX₁ p₀) (selTPos p₀ (lamX₁ p₀)))
      ∧ (∀ p, originalObjective (lamLoss p₀) p p₀ (lamPlus p₀) true
            = ⨅ q, originalObjective (lamLoss p₀) q p₀ (lamPlus p₀) true
          ↔ p = fiberParameters (priorQuotient p₀) (selTPos p₀ (priorQuotient p₀)))
      ∧ (∀ w : PositiveReal, w.val ≤ (lamPlus p₀).val → ∀ p,
          originalObjective (lamLoss p₀) p p₀ w false
            = ⨅ q, originalObjective (lamLoss p₀) q p₀ w false
          ↔ p = fiberParameters (lamX₂ p₀) (selTPos p₀ (lamX₂ p₀)))
      ∧ ∀ x t, (fiberParameters x t).nu = 1 / (t : ℝ) := by
  obtain ⟨-, -, h3, h4⟩ := lam_scores p₀
  refine ⟨lamLoss_finite_nonneg p₀, optimum_y₁_minus p₀,
    optimum_y₂ p₀ _ (lamMinus_le_lamPlus p₀), optimum_y₁_plus p₀, optimum_y₂ p₀ _ le_rfl, h3, h4,
    unique_original_minimizer p₀ _ _ _ (optimum_y₁_minus p₀),
    unique_original_minimizer p₀ _ _ _ (optimum_y₁_plus p₀),
    fun w hw => unique_original_minimizer p₀ _ _ _ (optimum_y₂ p₀ w hw), fun x t => rfl⟩

end NIGBottleneck
