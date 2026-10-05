import Mathlib
import Official.M07

/-!
# Quotient objective and exact partial minimization

The quotient reconstruction loss `ℓ(x;y) = rec(f_{γ,α,s}; y)`, the regularizer
`R(x) = F(x, t_*(x))`, and exact partial minimization of the original objective `J₄`, with
values in `ℝ ∪ {±∞}`.
-/

noncomputable section

namespace NIGBottleneck

open MeasureTheory

section Definitions

variable {Y : Type*}

/-- The quotient reconstruction loss `ℓ(x;y) = rec(f_{γ,α,s}; y)`. -/
def quotientLoss (L : ReconstructionLoss Y) (x : QuotientState) (y : Y) : EReal :=
  L (quotientLaw x) y

/-- The quotient regularizer `R(x) = F(x, t_*(x))`. -/
def regularizerR (p₀ : Parameters) (x : QuotientState) : ℝ :=
  fiberKL p₀ x (selTPos p₀ x)

/-- The reduced objective `J₃(x;y) = ℓ(x;y) + λ R(x)`. -/
def reducedObjective (L : ReconstructionLoss Y) (p₀ : Parameters) (w : PositiveReal)
    (x : QuotientState) (y : Y) : EReal :=
  quotientLoss L x y + ((w.val * regularizerR p₀ x : ℝ) : EReal)

end Definitions

section Reduction

variable {Y : Type*} (L : ReconstructionLoss Y) (p₀ : Parameters) (w : PositiveReal) (y : Y)

theorem regularizerR_eq_minimizedKL (x : QuotientState) : regularizerR p₀ x = minimizedKL p₀ x :=
  rfl

theorem regularizerR_nonneg (x : QuotientState) : 0 ≤ regularizerR p₀ x :=
  minimizedKL_nonneg p₀ x

/-- The original objective, with its reconstruction term written through the quotient state. -/
theorem originalObjective_eq (p : Parameters) :
    originalObjective L p p₀ w y
      = quotientLoss L (quotientCoordinates p) y
        + ((w.val * hierarchicalKL p p₀ : ℝ) : EReal) := by
  rw [originalObjective, quotientLoss, predictiveLaw_eq_quotientLaw]

theorem hierarchicalKL_eq_fiberKL (p : Parameters) :
    hierarchicalKL p p₀ = fiberKL p₀ (quotientCoordinates p) (fiberCoordinate p) := by
  rw [fiberKL, fiberParameters_quotientCoordinates]

theorem regularizerR_le_hierarchicalKL (p : Parameters) :
    regularizerR p₀ (quotientCoordinates p) ≤ hierarchicalKL p p₀ := by
  rw [hierarchicalKL_eq_fiberKL]
  by_cases h : (fiberCoordinate p : ℝ) = selT p₀ (quotientCoordinates p)
  · have : fiberCoordinate p = selTPos p₀ (quotientCoordinates p) := Subtype.ext h
    rw [regularizerR, this]
  · exact (fiberKL_selected_lt p₀ _ _ h).le

/-- The original objective at the selected representative is the reduced objective. -/
theorem originalObjective_selected (x : QuotientState) :
    originalObjective L (fiberParameters x (selTPos p₀ x)) p₀ w y
      = reducedObjective L p₀ w x y := by
  rw [originalObjective_eq, quotientCoordinates_fiberParameters, reducedObjective, regularizerR,
    fiberKL]

theorem reducedObjective_le_originalObjective (p : Parameters) :
    reducedObjective L p₀ w (quotientCoordinates p) y ≤ originalObjective L p p₀ w y := by
  rw [originalObjective_eq, reducedObjective]
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr
    (mul_le_mul_of_nonneg_left (regularizerR_le_hierarchicalKL p₀ p) w.property.le))

/-- `inf_{γ,ν,α,β} J₄ = inf_{x ∈ Q} J₃(x;y)`. -/
theorem iInf_originalObjective_eq :
    ⨅ p, originalObjective L p p₀ w y = ⨅ x, reducedObjective L p₀ w x y := by
  apply le_antisymm
  · refine le_iInf fun x => ?_
    rw [← originalObjective_selected]
    exact iInf_le _ _
  · refine le_iInf fun p => ?_
    exact (iInf_le _ (quotientCoordinates p)).trans
      (reducedObjective_le_originalObjective L p₀ w y p)

/-- At every point of the fiber,
`J₄(γ, 1/t, α, s/(1+t); y) = J₃(x;y) + λ [F(x,t) − R(x)]`. -/
theorem originalObjective_fiber (x : QuotientState) (t : PositiveReal) :
    originalObjective L (fiberParameters x t) p₀ w y
      = reducedObjective L p₀ w x y
        + ((w.val * (fiberKL p₀ x t - regularizerR p₀ x) : ℝ) : EReal) := by
  rw [originalObjective_eq, quotientCoordinates_fiberParameters, reducedObjective, add_assoc,
    ← EReal.coe_add, fiberKL]
  congr 2
  ring

/-- The second term is given explicitly by the gap formula of `Official.M06`. -/
theorem fiberKL_sub_regularizerR (x : QuotientState) (t : PositiveReal) :
    fiberKL p₀ x t - regularizerR p₀ x = fiberGap p₀ x t :=
  fiberKL_sub_selected p₀ x t

/-- The fiber minimizer is independent of `λ > 0`: for every weight, `t_*` is
the unique minimizer of `t ↦ λ F(x,t)`. -/
theorem fiber_minimizer_independent_of_weight (x : QuotientState) (t : PositiveReal) :
    (∀ t' : PositiveReal, w.val * fiberKL p₀ x t ≤ w.val * fiberKL p₀ x t') ↔ t = selTPos p₀ x := by
  have hw := w.property
  constructor
  · intro h
    by_contra hne
    have hne' : (t : ℝ) ≠ selT p₀ x := fun h' => hne (Subtype.ext h')
    have h1 := fiberKL_selected_lt p₀ x t hne'
    have h2 := h (selTPos p₀ x)
    nlinarith
  · rintro rfl t'
    by_cases h : (t' : ℝ) = selT p₀ x
    · have : t' = selTPos p₀ x := Subtype.ext h
      rw [this]
    · exact mul_le_mul_of_nonneg_left (fiberKL_selected_lt p₀ x t' h).le hw.le

lemma coe_add_cancel {a : EReal} (ha : a ≠ ⊥) (ha' : a ≠ ⊤) {b c : ℝ}
    (h : a + (b : EReal) = a + (c : EReal)) : b = c := by
  lift a to ℝ using ⟨ha', ha⟩
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff] at h
  linarith

/-- If the common infimum is finite, the minimizers of `J₄` are exactly the
selected representatives of the minimizers of `J₃`. -/
theorem originalObjective_minimizer_iff
    (hℓ : ∀ x, quotientLoss L x y ≠ ⊥)
    (hfin : (⨅ x, reducedObjective L p₀ w x y) ≠ ⊥ ∧ (⨅ x, reducedObjective L p₀ w x y) ≠ ⊤)
    (p : Parameters) :
    originalObjective L p p₀ w y = ⨅ q, originalObjective L q p₀ w y ↔
      reducedObjective L p₀ w (quotientCoordinates p) y = ⨅ x, reducedObjective L p₀ w x y ∧
        p = fiberParameters (quotientCoordinates p) (selTPos p₀ (quotientCoordinates p)) := by
  rw [iInf_originalObjective_eq]
  set m := ⨅ x, reducedObjective L p₀ w x y with hm
  constructor
  · intro h
    have hle := reducedObjective_le_originalObjective L p₀ w y p
    have hge : m ≤ reducedObjective L p₀ w (quotientCoordinates p) y := iInf_le _ _
    have hJ3 : reducedObjective L p₀ w (quotientCoordinates p) y = m := le_antisymm (h ▸ hle) hge
    refine ⟨hJ3, ?_⟩
    have heq : originalObjective L p p₀ w y
        = reducedObjective L p₀ w (quotientCoordinates p) y := by
      rw [h, hJ3]
    rw [originalObjective_eq, reducedObjective] at heq
    have htop : quotientLoss L (quotientCoordinates p) y ≠ ⊤ := by
      intro htop
      apply hfin.2
      rw [← hJ3, reducedObjective, htop, EReal.top_add_coe]
    have hKR := coe_add_cancel (hℓ _) htop heq
    have hK : hierarchicalKL p p₀ = regularizerR p₀ (quotientCoordinates p) :=
      mul_left_cancel₀ w.property.ne' hKR
    rw [hierarchicalKL_eq_fiberKL] at hK
    have ht : fiberCoordinate p = selTPos p₀ (quotientCoordinates p) := by
      by_contra hne
      have hne' : (fiberCoordinate p : ℝ) ≠ selT p₀ (quotientCoordinates p) :=
        fun h' => hne (Subtype.ext h')
      have := fiberKL_selected_lt p₀ _ _ hne'
      rw [regularizerR] at hK
      linarith
    conv_lhs => rw [← fiberParameters_quotientCoordinates p]
    rw [ht]
  · rintro ⟨hJ3, hp⟩
    rw [hp, originalObjective_selected]
    exact hJ3

/-- The selected representative of a minimizer of `J₃` minimizes `J₄`. -/
theorem selected_minimizes_originalObjective (x : QuotientState)
    (hx : reducedObjective L p₀ w x y = ⨅ x', reducedObjective L p₀ w x' y) :
    originalObjective L (fiberParameters x (selTPos p₀ x)) p₀ w y
      = ⨅ q, originalObjective L q p₀ w y := by
  rw [originalObjective_selected, iInf_originalObjective_eq, hx]

/-- If the common infimum is `−∞`, neither objective attains it. -/
theorem not_attained_of_iInf_eq_bot (hℓ : ∀ x, quotientLoss L x y ≠ ⊥)
    (hbot : (⨅ x, reducedObjective L p₀ w x y) = ⊥) :
    (∀ p, originalObjective L p p₀ w y ≠ ⨅ q, originalObjective L q p₀ w y) ∧
      (∀ x, reducedObjective L p₀ w x y ≠ ⨅ x', reducedObjective L p₀ w x' y) := by
  have h4 : ∀ p, originalObjective L p p₀ w y ≠ ⊥ := fun p => by
    rw [originalObjective_eq]
    exact EReal.add_ne_bot_iff.mpr ⟨hℓ _, EReal.coe_ne_bot _⟩
  have h3 : ∀ x, reducedObjective L p₀ w x y ≠ ⊥ := fun x => by
    rw [reducedObjective]
    exact EReal.add_ne_bot_iff.mpr ⟨hℓ _, EReal.coe_ne_bot _⟩
  refine ⟨fun p => ?_, fun x => ?_⟩
  · rw [iInf_originalObjective_eq, hbot]; exact h4 p
  · rw [hbot]; exact h3 x

end Reduction

section NoMinimizer

variable (p₀ : Parameters)

/-- A quotient state on the prior's `(γ₀, A)`-line with scale `s₀/r`. -/
def lineState (r : ℝ) (hr : 0 < r) : QuotientState :=
  ⟨p₀.gamma, p₀.alpha, (priorQuotient p₀).s / r, p₀.alpha_pos,
    div_pos (priorQuotient p₀).s_pos hr⟩

/-- On the line, the divergence at `t = 1/n` is `A (r − 1 − log r)`. -/
lemma fiberKL_lineState (r : ℝ) (hr : 0 < r) :
    fiberKL p₀ (lineState p₀ r hr) ⟨1 / p₀.nu, one_div_pos.mpr p₀.nu_pos⟩
      = p₀.alpha * (r - 1 - Real.log r) := by
  have hn := p₀.nu_pos
  have hb := p₀.beta_pos
  have hs0 := (priorQuotient p₀).s_pos
  rw [fiberKL_eq, fiberKLFormula, priorB]
  simp only [lineState, priorQuotient, quotientCoordinates, quotientScale, sub_self]
  have h1 : 1 + 1 / p₀.nu ≠ 0 := by positivity
  rw [div_self (Real.Gamma_pos_of_pos p₀.alpha_pos).ne', Real.log_one,
    show p₀.nu * (1 / p₀.nu) = 1 by field_simp, Real.log_one,
    Real.log_div (by positivity) hb.ne', Real.log_div (by positivity) hr.ne',
    Real.log_mul hb.ne' h1]
  field_simp
  ring

lemma lineState_ne (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) : lineState p₀ r hr ≠ priorQuotient p₀ := by
  intro h
  have hs := congrArg QuotientState.s h
  simp only [lineState] at hs
  have hs0 := (priorQuotient p₀).s_pos
  rw [div_eq_iff hr.ne'] at hs
  exact hr1 (by nlinarith)

/-- Points `x ≠ x₀` with arbitrarily small reduced regularizer `R(x)`. -/
theorem exists_regularizerR_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ x : QuotientState, x ≠ priorQuotient p₀ ∧ regularizerR p₀ x < ε := by
  have hA := p₀.alpha_pos
  set h : ℝ := min 1 (ε / (2 * p₀.alpha)) / 2 with hh
  have hpos : 0 < h := by positivity
  have hle1 : h ≤ 1 / 2 := by
    have := min_le_left 1 (ε / (2 * p₀.alpha)); linarith
  have hleε : h ≤ ε / (2 * p₀.alpha) := by
    have := min_le_right 1 (ε / (2 * p₀.alpha)); linarith
  have hr : 0 < 1 + h := by linarith
  refine ⟨lineState p₀ (1 + h) hr, lineState_ne p₀ _ hr (by linarith), ?_⟩
  have hR : regularizerR p₀ (lineState p₀ (1 + h) hr)
      ≤ fiberKL p₀ (lineState p₀ (1 + h) hr) ⟨1 / p₀.nu, one_div_pos.mpr p₀.nu_pos⟩ := by
    rw [regularizerR]
    by_cases hc : (1 / p₀.nu : ℝ) = selT p₀ (lineState p₀ (1 + h) hr)
    · have : (⟨1 / p₀.nu, one_div_pos.mpr p₀.nu_pos⟩ : PositiveReal)
          = selTPos p₀ (lineState p₀ (1 + h) hr) := Subtype.ext hc
      rw [this]
    · exact (fiberKL_selected_lt p₀ _ _ hc).le
  rw [fiberKL_lineState] at hR
  have hlog : 1 - 1 / (1 + h) ≤ Real.log (1 + h) := by
    have := Real.one_sub_inv_le_log_of_pos hr
    simpa [one_div] using this
  have hbound : 1 + h - 1 - Real.log (1 + h) ≤ h ^ 2 := by
    have : 1 - 1 / (1 + h) = h / (1 + h) := by field_simp; ring
    rw [this] at hlog
    have hdiv : h - h / (1 + h) = h ^ 2 / (1 + h) := by field_simp; ring
    have : h ^ 2 / (1 + h) ≤ h ^ 2 := div_le_self (sq_nonneg h) (by linarith)
    linarith
  have hsq : h ^ 2 ≤ h := by nlinarith
  calc regularizerR p₀ (lineState p₀ (1 + h) hr) ≤ p₀.alpha * (1 + h - 1 - Real.log (1 + h)) := hR
    _ ≤ p₀.alpha * h := by nlinarith
    _ ≤ p₀.alpha * (ε / (2 * p₀.alpha)) := by nlinarith
    _ < ε := by field_simp; linarith

open Classical in
/-- The loss of the counterexample: `1` at the law of `x₀`, `0` at every other law. -/
def pointLoss : ReconstructionLoss Unit :=
  fun μ _ => if μ = quotientLaw (priorQuotient p₀) then 1 else 0

/-- No global minimizer is guaranteed for an arbitrary reconstruction loss, even
if that loss is finite and nonnegative everywhere. -/
theorem exists_loss_without_minimizer (w : PositiveReal) :
    ∃ L : ReconstructionLoss Unit, (∀ μ, 0 ≤ L μ () ∧ L μ () ≠ ⊤) ∧
      ¬ ∃ p : Parameters, ∀ q : Parameters,
        originalObjective L p p₀ w () ≤ originalObjective L q p₀ w () := by
  classical
  have hw := w.property
  refine ⟨pointLoss p₀, fun μ => ?_, ?_⟩
  · unfold pointLoss
    split_ifs
    · exact ⟨zero_le_one, ne_of_lt (EReal.coe_lt_top 1)⟩
    · exact ⟨le_rfl, EReal.zero_ne_top⟩
  · rintro ⟨p, hp⟩
    have hloss : ∀ x, quotientLoss (pointLoss p₀) x () = if x = priorQuotient p₀ then 1 else 0 := by
      intro x
      simp only [quotientLoss, pointLoss, quotientLaw_injective.eq_iff]
    -- the value at a line point `x ≠ x₀` is `λ R(x)`
    have hval : ∀ x, x ≠ priorQuotient p₀ →
        originalObjective (pointLoss p₀) (fiberParameters x (selTPos p₀ x)) p₀ w ()
          = ((w.val * regularizerR p₀ x : ℝ) : EReal) := by
      intro x hx
      rw [originalObjective_selected, reducedObjective, hloss]
      simp [hx]
    set x := quotientCoordinates p with hxdef
    have hlow := reducedObjective_le_originalObjective (pointLoss p₀) p₀ w () p
    by_cases hx0 : x = priorQuotient p₀
    · obtain ⟨z, hz, hRz⟩ := exists_regularizerR_lt p₀ (1 / w.val) (by positivity)
      have h1 := hp (fiberParameters z (selTPos p₀ z))
      rw [hval z hz] at h1
      have h2 : (1 : EReal) ≤ originalObjective (pointLoss p₀) p p₀ w () := by
        refine le_trans ?_ hlow
        rw [reducedObjective, hloss, ← hxdef]
        simp only [hx0, ↓reduceIte]
        exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr
          (mul_nonneg hw.le (regularizerR_nonneg p₀ _)))
      have h3 : w.val * regularizerR p₀ z < 1 := by
        rw [lt_div_iff₀ hw] at hRz
        linarith
      have := lt_of_le_of_lt (h2.trans h1) (EReal.coe_lt_coe_iff.mpr h3)
      exact lt_irrefl _ this
    · have hRpos : 0 < regularizerR p₀ x := by
        rcases (regularizerR_nonneg p₀ x).lt_or_eq with h | h
        · exact h
        · exact absurd ((minimizedKL_eq_zero_iff p₀ x).mp h.symm) hx0
      obtain ⟨z, hz, hRz⟩ := exists_regularizerR_lt p₀ (regularizerR p₀ x) hRpos
      have h1 := hp (fiberParameters z (selTPos p₀ z))
      rw [hval z hz] at h1
      have h2 : ((w.val * regularizerR p₀ x : ℝ) : EReal)
          ≤ originalObjective (pointLoss p₀) p p₀ w () := by
        refine le_trans ?_ hlow
        rw [reducedObjective, hloss, ← hxdef]
        simp [hx0]
      have h3 : w.val * regularizerR p₀ z < w.val * regularizerR p₀ x :=
        mul_lt_mul_of_pos_left hRz hw
      have := lt_of_le_of_lt (h2.trans h1) (EReal.coe_lt_coe_iff.mpr h3)
      exact lt_irrefl _ this

end NoMinimizer

end NIGBottleneck
