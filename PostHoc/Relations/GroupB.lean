import Official.M06
import Official.M07
import Official.M08
import Official.M09
import Official.M10
import Official.M11
import PostHoc.Relations.GroupA

/-!
# L1 ↔ B2 formal relation certificates, group B

Items: theorem-2, corollary-1, eq-3, theorem-3, proposition-3, proposition-4, proposition-5. Method
as in
`GroupA`.
-/

-- cosmetic only: long statement lines are kept verbatim-readable
set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory NIGBottleneck

namespace PostHocFidelity

/-- L1's T_A(d) (L1 eq. (T)), literally. -/
def l1TA (A d : ℝ) : ℝ := (2 * A + 1 - d + Real.sqrt ((d - 2 * A - 1) ^ 2 + 4 * d)) / (2 * d)

/-- L1's Φ_A(d) (L1 eq. (Phi)), literally. -/
def l1PhiA (A d : ℝ) : ℝ := (d - 2 * A - 1 + Real.sqrt ((d - 2 * A - 1) ^ 2 + 4 * d)) / 2

/-- L1's d = n + 2αB/s with B = β₀ + (n/2)δ², literally. -/
def l1d (p₀ : Parameters) (x : QuotientState) : ℝ :=
  p₀.nu + 2 * x.alpha * (p₀.beta + p₀.nu / 2 * (x.gamma - p₀.gamma) ^ 2) / x.s

/-- L1's F(x,t) := K(γ, 1/t, α, s/(1+t)), with K the KL divergence (Mathlib `klDiv`). -/
def l1Fkl (p₀ : Parameters) (x : QuotientState) (t : PositiveReal) : ℝ :=
  (klDiv (nigLaw (fiberParameters x t)) (nigLaw p₀)).toReal

/-- L1's gap formula A(η−1−log η) + ½(ζ−1−log ζ), η=(1+t)/(1+t*), ζ=t/t*, literally. -/
def l1Gap (A t ts : ℝ) : ℝ :=
  A * ((1 + t) / (1 + ts) - 1 - Real.log ((1 + t) / (1 + ts))) + 1 / 2 * (t / ts - 1 - Real.log (t / ts))

/-- Foundational (not an item target): KL integral = Mathlib KL (M07 `hierarchicalKL_eq_toReal_klDiv`). -/
def FoundKL : Prop := ∀ p p₀ : Parameters, hierarchicalKL p p₀ = (klDiv (nigLaw p) (nigLaw p₀)).toReal

theorem FoundKL_holds : FoundKL := hierarchicalKL_eq_toReal_klDiv

lemma l1d_pos (p₀ : Parameters) (x : QuotientState) : 0 < l1d p₀ x := by
  have := p₀.nu_pos; have := p₀.beta_pos; have := x.alpha_pos; have := x.s_pos
  unfold l1d; positivity

/-- Elementary positivity of the literal T_A(d) for d > 0 (no B2 theorem used). -/
lemma l1TA_pos {A d : ℝ} (hd : 0 < d) : 0 < l1TA A d := by
  have hs : |d - 2 * A - 1| < Real.sqrt ((d - 2 * A - 1) ^ 2 + 4 * d) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have := le_abs_self (d - 2 * A - 1)
  unfold l1TA
  apply div_pos _ (by linarith)
  linarith

/-- L1's t_* as an element of (0,∞). -/
def l1tStar (p₀ : Parameters) (x : QuotientState) : PositiveReal :=
  ⟨l1TA p₀.alpha (l1d p₀ x), l1TA_pos (l1d_pos p₀ x)⟩

/-! ## theorem-2

L1_form: as written, with F = `l1Fkl` and with T_A, Φ_A, d and the gap written literally. Analyticity is
stated for the literal 7-variable maps (γ,α,s,γ₀,n,A,β₀) ↦ t_*, ν_sel, β_sel on the admissible open set. -/

def l1dCoord (v : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  v.2.2.2.2.1 + 2 * v.2.1 * (v.2.2.2.2.2.2 + v.2.2.2.2.1 / 2 * (v.1 - v.2.2.2.1) ^ 2) / v.2.2.1
def l1tCoord (v : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ := l1TA v.2.2.2.2.2.1 (l1dCoord v)
def l1nuCoord (v : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ := l1PhiA v.2.2.2.2.2.1 (l1dCoord v)
def l1betaCoord (v : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ := v.2.2.1 / (1 + l1tCoord v)
def l1AdmissibleSP : Set (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) :=
  {v | 0 < v.2.1 ∧ 0 < v.2.2.1 ∧ 0 < v.2.2.2.2.1 ∧ 0 < v.2.2.2.2.2.1 ∧ 0 < v.2.2.2.2.2.2}

def L1_theorem2 : Prop :=
  (∀ (p₀ : Parameters) (x : QuotientState),
    0 < l1d p₀ x
    ∧ (∀ t : PositiveReal, l1Fkl p₀ x (l1tStar p₀ x) ≤ l1Fkl p₀ x t)
    ∧ (∀ t : PositiveReal, (∀ t' : PositiveReal, l1Fkl p₀ x t ≤ l1Fkl p₀ x t') →
        (t : ℝ) = l1TA p₀.alpha (l1d p₀ x))
    ∧ (∀ t : ℝ, 0 < t → (l1d p₀ x = 2 * p₀.alpha / (1 + t) + 1 / t ↔ t = l1TA p₀.alpha (l1d p₀ x)))
    ∧ l1PhiA p₀.alpha (l1d p₀ x) = 1 / l1TA p₀.alpha (l1d p₀ x)
    ∧ (∀ t : PositiveReal, l1Fkl p₀ x t - l1Fkl p₀ x (l1tStar p₀ x)
        = l1Gap p₀.alpha t (l1TA p₀.alpha (l1d p₀ x)))
    ∧ (∀ t : ℝ, 0 < t → t ≠ l1TA p₀.alpha (l1d p₀ x) → 0 < l1Gap p₀.alpha t (l1TA p₀.alpha (l1d p₀ x))))
  ∧ AnalyticOnNhd ℝ l1tCoord l1AdmissibleSP
  ∧ AnalyticOnNhd ℝ l1nuCoord l1AdmissibleSP
  ∧ AnalyticOnNhd ℝ l1betaCoord l1AdmissibleSP

def B2_theorem2 : Prop :=
  (∀ (p₀ : Parameters) (x : QuotientState) (t : ℝ), 0 < t →
      (selD p₀ x = 2 * p₀.alpha / (1 + t) + 1 / t ↔ t = selT p₀ x))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), ∃! t, ∀ (t' : PositiveReal), fiberKL p₀ x t ≤ fiberKL p₀ x t')
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : PositiveReal),
      fiberKL p₀ x t - fiberKL p₀ x (selTPos p₀ x) = fiberGap p₀ x t)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : ℝ), 0 < t → t ≠ selT p₀ x → 0 < fiberGap p₀ x t)
  ∧ AnalyticOnNhd ℝ selTCoord statePriorDomain
  ∧ AnalyticOnNhd ℝ selNuCoord statePriorDomain
  ∧ AnalyticOnNhd ℝ selBetaCoord statePriorDomain
  ∧ (∀ {A d : ℝ}, 0 < d → TA A d * PhiA A d = 1)

theorem rel_theorem2 : FoundKL → B2_theorem2 → L1_theorem2 := by
  rintro hK ⟨hsol, -, hsub, hgap, han1, han2, han3, hmul⟩
  have hF : ∀ p₀ x (t : PositiveReal), l1Fkl p₀ x t = fiberKL p₀ x t := fun p₀ x t => (hK _ _).symm
  have hst : ∀ p₀ x, l1tStar p₀ x = selTPos p₀ x := fun _ _ => rfl
  refine ⟨fun p₀ x => ⟨l1d_pos p₀ x, ?_, ?_, ?_, ?_, ?_, ?_⟩, han1, han2, han3⟩
  · intro t
    have h1 := hsub p₀ x t
    have h2 : 0 ≤ fiberGap p₀ x t := by
      by_cases ht : (t : ℝ) = selT p₀ x
      · have hs : 0 < selT p₀ x := by rw [← ht]; exact t.2
        simp only [fiberGap, ht, div_self (show (1 : ℝ) + selT p₀ x ≠ 0 by linarith), div_self hs.ne',
          Real.log_one, sub_self, mul_zero, zero_add]
        all_goals exact le_rfl
      · exact (hgap p₀ x t t.2 ht).le
    rw [hF, hF, hst]
    linarith
  · intro t ht
    by_contra hne
    have h1 := hsub p₀ x t
    have h2 := hgap p₀ x t t.2 hne
    have h3 := ht (selTPos p₀ x)
    rw [hF, hF] at h3
    linarith
  · intro t ht
    exact hsol p₀ x t ht
  · have hd := l1d_pos p₀ x
    have hm : TA p₀.alpha (l1d p₀ x) * PhiA p₀.alpha (l1d p₀ x) = 1 := hmul hd
    have hT : 0 < l1TA p₀.alpha (l1d p₀ x) := l1TA_pos hd
    rw [eq_div_iff hT.ne']
    calc l1PhiA p₀.alpha (l1d p₀ x) * l1TA p₀.alpha (l1d p₀ x)
        = TA p₀.alpha (l1d p₀ x) * PhiA p₀.alpha (l1d p₀ x) := by rw [mul_comm]; rfl
      _ = 1 := hm
  · intro t
    rw [hF, hF, hst]
    exact hsub p₀ x t
  · intro t ht hne
    exact hgap p₀ x t ht hne

#relation_audit rel_theorem2 [NIGBottleneck.selT_unique_solution, NIGBottleneck.fiberKL_unique_minimizer,
  NIGBottleneck.fiberKL_sub_selected, NIGBottleneck.fiberGap_pos, NIGBottleneck.selTCoord_analyticOnNhd,
  NIGBottleneck.selNuCoord_analyticOnNhd, NIGBottleneck.selBetaCoord_analyticOnNhd, NIGBottleneck.TA_mul_PhiA]

theorem B2_theorem2_holds : B2_theorem2 :=
  ⟨selT_unique_solution, fiberKL_unique_minimizer, fiberKL_sub_selected, fiberGap_pos,
    selTCoord_analyticOnNhd, selNuCoord_analyticOnNhd, selBetaCoord_analyticOnNhd, TA_mul_PhiA⟩

theorem L1_theorem2_holds : L1_theorem2 := rel_theorem2 FoundKL_holds B2_theorem2_holds

/-! ## corollary-1

L1:  The minimized divergence is F(x, t_*(x)), with F = `l1Fkl`. -/

def l1x0 (p₀ : Parameters) : QuotientState :=
  ⟨p₀.gamma, p₀.alpha, p₀.beta * (1 + 1 / p₀.nu), p₀.alpha_pos, by
    have := p₀.beta_pos; have := p₀.nu_pos; positivity⟩

def L1_cor1 : Prop :=
  ∀ p₀ : Parameters,
    l1TA p₀.alpha (l1d p₀ (l1x0 p₀)) = 1 / p₀.nu
    ∧ (l1x0 p₀).gamma = p₀.gamma ∧ l1PhiA p₀.alpha (l1d p₀ (l1x0 p₀)) = p₀.nu
    ∧ (l1x0 p₀).alpha = p₀.alpha ∧ (l1x0 p₀).s / (1 + l1TA p₀.alpha (l1d p₀ (l1x0 p₀))) = p₀.beta
    ∧ ∀ x : QuotientState, (l1Fkl p₀ x (l1tStar p₀ x) = 0 ↔ x = l1x0 p₀)

def B2_cor1 : Prop :=
  (∀ p₀ : Parameters, fiberParameters (priorQuotient p₀) (selTPos p₀ (priorQuotient p₀)) = p₀)
  ∧ (∀ p₀ : Parameters, (priorQuotient p₀).gamma = p₀.gamma ∧ selNu p₀ (priorQuotient p₀) = p₀.nu
      ∧ (priorQuotient p₀).alpha = p₀.alpha ∧ selBeta p₀ (priorQuotient p₀) = p₀.beta)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), minimizedKL p₀ x = 0 ↔ x = priorQuotient p₀)

theorem rel_cor1 : FoundKL → B2_cor1 → L1_cor1 := by
  rintro hK ⟨hsel, hcoords, hzero⟩ p₀
  have hx0 : l1x0 p₀ = priorQuotient p₀ := rfl
  obtain ⟨h1, h2, h3, h4⟩ := hcoords p₀
  refine ⟨?_, h1, h2, h3, h4, fun x => ?_⟩
  · have hnu := congrArg Parameters.nu (hsel p₀)
    simp only [fiberParameters] at hnu
    have hpos : 0 < selT p₀ (priorQuotient p₀) := (selTPos p₀ (priorQuotient p₀)).2
    change selT p₀ (priorQuotient p₀) = 1 / p₀.nu
    rw [← hnu, one_div_one_div]
    rfl
  · rw [hx0, ← hzero p₀ x]
    unfold l1Fkl minimizedKL fiberKL
    rw [← hK]
    rfl

#relation_audit rel_cor1 [NIGBottleneck.selected_priorQuotient, NIGBottleneck.selected_priorQuotient_coords,
  NIGBottleneck.minimizedKL_priorQuotient, NIGBottleneck.minimizedKL_eq_zero_iff,
  NIGBottleneck.hierarchicalKL_eq_zero_iff]

theorem B2_cor1_holds : B2_cor1 :=
  ⟨selected_priorQuotient, selected_priorQuotient_coords, minimizedKL_eq_zero_iff⟩

theorem L1_cor1_holds : L1_cor1 := rel_cor1 FoundKL_holds B2_cor1_holds

/-! ## eq-3

L1:  f_{γ,α,s} is the law with L1's
displayed predictive density; F = `l1Fkl`; t_* = T_A(d). The B2 side consists of definitions
(`quotientLoss`, `regularizerR`); the relation is definitional, modulo the foundational KL identification. -/

def l1PredLaw (x : QuotientState) : Measure ℝ :=
  volume.withDensity (fun z => ENNReal.ofReal
    (Real.Gamma (x.alpha + 1 / 2) / (Real.Gamma x.alpha * Real.sqrt (2 * Real.pi * x.s))
      * (1 + (z - x.gamma) ^ 2 / (2 * x.s)) ^ (-x.alpha - 1 / 2)))

def L1_eq3 : Prop :=
  (∀ {Y : Type} (rec : ReconstructionLoss Y) (x : QuotientState) (y : Y), quotientLoss rec x y = rec (l1PredLaw x) y)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), regularizerR p₀ x = l1Fkl p₀ x (l1tStar p₀ x))

theorem rel_eq3 : FoundKL → L1_eq3 := by
  intro hK
  refine ⟨fun rec x y => rfl, fun p₀ x => ?_⟩
  unfold regularizerR fiberKL l1Fkl
  exact hK _ _

#relation_audit rel_eq3 [NIGBottleneck.hierarchicalKL_eq_closedForm]

theorem L1_eq3_holds : L1_eq3 := rel_eq3 FoundKL_holds

/-! ## theorem-3

L1_form uses the eq-2/eq-3 objects (`originalObjective`, `reducedObjective`), already certified against L1's
literal definitions. "ℓ : Q → ℝ∪{+∞}" is `∀ x, ℓ x ≠ ⊥`. "No global minimizer is guaranteed" is read as: for every
prior and weight there is a finite nonnegative loss with no minimizer. -/

def L1_theorem3 : Prop :=
  ∀ {Y : Type} (L : ReconstructionLoss Y) (p₀ : Parameters) (w : PositiveReal) (y : Y),
    (⨅ p, originalObjective L p p₀ w y = ⨅ x, reducedObjective L p₀ w x y)
    ∧ ((∀ x, quotientLoss L x y ≠ ⊥) → (⨅ x, reducedObjective L p₀ w x y) ≠ ⊥ →
        (⨅ x, reducedObjective L p₀ w x y) ≠ ⊤ →
        ∀ p, (originalObjective L p p₀ w y = ⨅ q, originalObjective L q p₀ w y ↔
          (reducedObjective L p₀ w (quotientCoordinates p) y = ⨅ x, reducedObjective L p₀ w x y
            ∧ p = fiberParameters (quotientCoordinates p) (l1tStar p₀ (quotientCoordinates p)))))
    ∧ ((∀ x, quotientLoss L x y ≠ ⊥) → (⨅ x, reducedObjective L p₀ w x y) = ⊥ →
        (∀ p, originalObjective L p p₀ w y ≠ ⨅ q, originalObjective L q p₀ w y)
        ∧ (∀ x, reducedObjective L p₀ w x y ≠ ⨅ x', reducedObjective L p₀ w x' y))
    ∧ (∀ (x : QuotientState) (t : PositiveReal), quotientLoss L x y ≠ ⊥ → quotientLoss L x y ≠ ⊤ →
        originalObjective L (fiberParameters x t) p₀ w y
          = reducedObjective L p₀ w x y + ((w.val * (l1Fkl p₀ x t - regularizerR p₀ x) : ℝ) : EReal)
        ∧ l1Fkl p₀ x t - regularizerR p₀ x = l1Gap p₀.alpha t (l1TA p₀.alpha (l1d p₀ x)))
    ∧ (∀ (x : QuotientState) (t : PositiveReal),
        (∀ t' : PositiveReal, w.val * l1Fkl p₀ x t ≤ w.val * l1Fkl p₀ x t') ↔ t = l1tStar p₀ x)
    ∧ (∃ L' : ReconstructionLoss Unit, (∀ μ, 0 ≤ L' μ () ∧ L' μ () ≠ ⊤) ∧
        ¬ ∃ p : Parameters, ∀ q : Parameters, originalObjective L' p p₀ w () ≤ originalObjective L' q p₀ w ())

def B2_theorem3 : Prop :=
  (∀ {Y : Type} (L : ReconstructionLoss Y) (p₀ : Parameters) (w : PositiveReal) (y : Y),
    ⨅ p, originalObjective L p p₀ w y = ⨅ x, reducedObjective L p₀ w x y)
  ∧ (∀ {Y : Type} (L : ReconstructionLoss Y) (p₀ : Parameters) (w : PositiveReal) (y : Y)
      (x : QuotientState) (t : PositiveReal),
      originalObjective L (fiberParameters x t) p₀ w y =
        reducedObjective L p₀ w x y + ((w.val * (fiberKL p₀ x t - regularizerR p₀ x) : ℝ) : EReal))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : PositiveReal), fiberKL p₀ x t - regularizerR p₀ x = fiberGap p₀ x t)
  ∧ (∀ (p₀ : Parameters) (w : PositiveReal) (x : QuotientState) (t : PositiveReal),
      (∀ (t' : PositiveReal), w.val * fiberKL p₀ x t ≤ w.val * fiberKL p₀ x t') ↔ t = selTPos p₀ x)
  ∧ (∀ {Y : Type} (L : ReconstructionLoss Y) (p₀ : Parameters) (w : PositiveReal) (y : Y),
      (∀ (x : QuotientState), quotientLoss L x y ≠ ⊥) →
      (⨅ x, reducedObjective L p₀ w x y ≠ ⊥ ∧ ⨅ x, reducedObjective L p₀ w x y ≠ ⊤) →
      ∀ (p : Parameters), originalObjective L p p₀ w y = ⨅ q, originalObjective L q p₀ w y ↔
        reducedObjective L p₀ w (quotientCoordinates p) y = ⨅ x, reducedObjective L p₀ w x y ∧
          p = fiberParameters (quotientCoordinates p) (selTPos p₀ (quotientCoordinates p)))
  ∧ (∀ {Y : Type} (L : ReconstructionLoss Y) (p₀ : Parameters) (w : PositiveReal) (y : Y),
      (∀ (x : QuotientState), quotientLoss L x y ≠ ⊥) → ⨅ x, reducedObjective L p₀ w x y = ⊥ →
      (∀ (p : Parameters), originalObjective L p p₀ w y ≠ ⨅ q, originalObjective L q p₀ w y) ∧
        ∀ (x : QuotientState), reducedObjective L p₀ w x y ≠ ⨅ x', reducedObjective L p₀ w x' y)
  ∧ (∀ (p₀ : Parameters) (w : PositiveReal), ∃ L : ReconstructionLoss Unit,
      (∀ (μ : Measure ℝ), 0 ≤ L μ () ∧ L μ () ≠ ⊤) ∧
      ¬∃ p, ∀ (q : Parameters), originalObjective L p p₀ w () ≤ originalObjective L q p₀ w ())

theorem rel_theorem3 : FoundKL → B2_theorem3 → L1_theorem3 := by
  rintro hK ⟨h1, h2, h3, h4, h5, h6, h7⟩ Y L p₀ w y
  have hF : ∀ x (t : PositiveReal), l1Fkl p₀ x t = fiberKL p₀ x t := fun x t => (hK _ _).symm
  refine ⟨h1 L p₀ w y, fun hl hb ht p => h5 L p₀ w y hl ⟨hb, ht⟩ p, fun hl hb => h6 L p₀ w y hl hb,
    fun x t _ _ => ⟨by rw [hF]; exact h2 L p₀ w y x t, by rw [hF]; exact h3 p₀ x t⟩,
    fun x t => by simp only [hF]; exact h4 p₀ w x t, h7 p₀ w⟩

#relation_audit rel_theorem3 [NIGBottleneck.iInf_originalObjective_eq, NIGBottleneck.originalObjective_fiber,
  NIGBottleneck.fiberKL_sub_regularizerR, NIGBottleneck.fiber_minimizer_independent_of_weight,
  NIGBottleneck.originalObjective_minimizer_iff, NIGBottleneck.selected_minimizes_originalObjective,
  NIGBottleneck.not_attained_of_iInf_eq_bot, NIGBottleneck.exists_loss_without_minimizer]

theorem B2_theorem3_holds : B2_theorem3 :=
  ⟨fun L p₀ w y => iInf_originalObjective_eq L p₀ w y, fun L p₀ w y x t => originalObjective_fiber L p₀ w y x t,
    fiberKL_sub_regularizerR, fiber_minimizer_independent_of_weight,
    fun L p₀ w y => originalObjective_minimizer_iff L p₀ w y, fun L p₀ w y => not_attained_of_iInf_eq_bot L p₀ w y,
    exists_loss_without_minimizer⟩

theorem L1_theorem3_holds : L1_theorem3 := rel_theorem3 FoundKL_holds B2_theorem3_holds

/-! ## proposition-3

L1_form: R is written in coordinates (γ,α,s) with L1's literal closed form F(x,t_*(x)), including
log(Γ(A)/Γ(α)). Partial derivatives are directional derivatives along the coordinate axes. The last sentence is
read as: some finite nonnegative loss has distinct unique optimal states for two weights. The equality of the
literal R with B2's `RCoord` on the admissible domain is proved in `l1R_eq_RCoord`, using Mathlib's
`Real.log_div` and `Real.Gamma_pos_of_pos` only. -/

/-- L1's R in coordinates (γ,α,s), literally: F(x,t_*(x)) with L1's fiber formula (log of a quotient). -/
def l1R (p₀ : Parameters) (q : ℝ × ℝ × ℝ) : ℝ :=
  l1F p₀ q.1 q.2.1 q.2.2
    (l1TA p₀.alpha (p₀.nu + 2 * q.2.1 * (p₀.beta + p₀.nu / 2 * (q.1 - p₀.gamma) ^ 2) / q.2.2))

lemma l1R_eq_RCoord (p₀ : Parameters) {q : ℝ × ℝ × ℝ} (hq : q ∈ qDomain) : l1R p₀ q = RCoord p₀ q := by
  obtain ⟨ha, -⟩ := hq
  unfold l1R l1F RCoord FCoord
  rw [Real.log_div (Real.Gamma_pos_of_pos p₀.alpha_pos).ne' (Real.Gamma_pos_of_pos ha).ne']
  rfl

lemma l1R_eventuallyEq (p₀ : Parameters) {q : ℝ × ℝ × ℝ} (hq : q ∈ qDomain) : l1R p₀ =ᶠ[nhds q] RCoord p₀ := by
  have hopen : IsOpen qDomain := by
    have h1 : IsOpen {x : ℝ × ℝ × ℝ | 0 < x.2.1} := isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
    have h2 : IsOpen {x : ℝ × ℝ × ℝ | 0 < x.2.2} := isOpen_lt continuous_const (continuous_snd.comp continuous_snd)
    exact h1.inter h2
  filter_upwards [hopen.mem_nhds hq] with z hz using l1R_eq_RCoord p₀ hz

def L1_prop3 : Prop :=
  ∀ p₀ : Parameters,
    AnalyticOnNhd ℝ (l1R p₀) qDomain
    ∧ (∀ {x : ℝ × ℝ × ℝ}, x ∈ qDomain →
        HasDerivAt (fun u : ℝ => l1R p₀ (x + u • ((1 : ℝ), (0 : ℝ), (0 : ℝ))))
          (p₀.nu * x.2.1 * (x.1 - p₀.gamma) * (1 + tStarCoord p₀ x) / x.2.2) (0 : ℝ)
        ∧ HasDerivAt (fun u : ℝ => l1R p₀ (x + u • ((0 : ℝ), (1 : ℝ), (0 : ℝ))))
          ((x.2.1 - p₀.alpha) * deriv l1Psi x.2.1 - 1
            + (p₀.beta + p₀.nu / 2 * (x.1 - p₀.gamma) ^ 2) * (1 + tStarCoord p₀ x) / x.2.2) (0 : ℝ)
        ∧ HasDerivAt (fun u : ℝ => l1R p₀ (x + u • ((0 : ℝ), (0 : ℝ), (1 : ℝ))))
          (p₀.alpha / x.2.2 - x.2.1 * (p₀.beta + p₀.nu / 2 * (x.1 - p₀.gamma) ^ 2)
            * (1 + tStarCoord p₀ x) / x.2.2 ^ 2) (0 : ℝ)
        ∧ HasFDerivAt (l1R p₀)
          ((fderiv ℝ (fun q : (ℝ × ℝ × ℝ) × ℝ => FCoord p₀ q.1 q.2) (x, tStarCoord p₀ x)).comp
            (ContinuousLinearMap.inl ℝ (ℝ × ℝ × ℝ) ℝ)) x)
    ∧ (∀ {ℓ : ℝ × ℝ × ℝ → ℝ} {ℓ' : (ℝ × ℝ × ℝ) →L[ℝ] ℝ} (w : PositiveReal) {x : ℝ × ℝ × ℝ},
        x ∈ qDomain → HasFDerivAt ℓ ℓ' x → IsLocalMin (fun z => ℓ z + w.val * l1R p₀ z) x →
        ℓ' + w.val • fderiv ℝ (l1R p₀) x = 0)
    ∧ (∃ (L : ReconstructionLoss Unit) (w₁ w₂ : PositiveReal) (x₁ x₂ : QuotientState), x₁ ≠ x₂
        ∧ (∀ μ, 0 ≤ L μ () ∧ L μ () ≠ ⊤)
        ∧ (∀ x, x ≠ x₁ → reducedObjective L p₀ w₁ x₁ () < reducedObjective L p₀ w₁ x ())
        ∧ (∀ x, x ≠ x₂ → reducedObjective L p₀ w₂ x₂ () < reducedObjective L p₀ w₂ x ()))

def B2_prop3 : Prop :=
  ∀ p₀ : Parameters,
    AnalyticOnNhd ℝ (RCoord p₀) qDomain
    ∧ (∀ {x : QCoord}, x ∈ qDomain →
        HasFDerivAt (RCoord p₀)
          ((fderiv ℝ (fun q : QCoord × ℝ => FCoord p₀ q.1 q.2) (x, tStarCoord p₀ x)).comp
            (ContinuousLinearMap.inl ℝ QCoord ℝ)) x)
    ∧ (∀ {x : QCoord}, x ∈ qDomain → HasDerivAt (fun u : ℝ => RCoord p₀ (x + u • ((1 : ℝ), (0 : ℝ), (0 : ℝ))))
          (p₀.nu * x.2.1 * (x.1 - p₀.gamma) * (1 + tStarCoord p₀ x) / x.2.2) (0 : ℝ))
    ∧ (∀ {x : QCoord}, x ∈ qDomain → HasDerivAt (fun u : ℝ => RCoord p₀ (x + u • ((0 : ℝ), (1 : ℝ), (0 : ℝ))))
          ((x.2.1 - p₀.alpha) * trigamma x.2.1 - 1 + BCoord p₀ x * (1 + tStarCoord p₀ x) / x.2.2) (0 : ℝ))
    ∧ (∀ {x : QCoord}, x ∈ qDomain → HasDerivAt (fun u : ℝ => RCoord p₀ (x + u • ((0 : ℝ), (0 : ℝ), (1 : ℝ))))
          (p₀.alpha / x.2.2 - x.2.1 * BCoord p₀ x * (1 + tStarCoord p₀ x) / x.2.2 ^ 2) (0 : ℝ))
    ∧ (∀ {ℓ : QCoord → ℝ} {ℓ' : QCoord →L[ℝ] ℝ} (w : PositiveReal) {x : QCoord}, x ∈ qDomain →
        HasFDerivAt ℓ ℓ' x → IsLocalMin (fun y => ℓ y + w.val * RCoord p₀ y) x →
        ℓ' + w.val • fderiv ℝ (RCoord p₀) x = 0)
    ∧ (∃ (L : ReconstructionLoss Unit) (w₁ w₂ : PositiveReal) (x₁ x₂ : QuotientState), x₁ ≠ x₂
        ∧ (∀ μ, 0 ≤ L μ () ∧ L μ () ≠ ⊤)
        ∧ (∀ x, x ≠ x₁ → reducedObjective L p₀ w₁ x₁ () < reducedObjective L p₀ w₁ x ())
        ∧ (∀ x, x ≠ x₂ → reducedObjective L p₀ w₂ x₂ () < reducedObjective L p₀ w₂ x ())
        ∧ ∀ (w : PositiveReal) (x : QuotientState) (t : PositiveReal),
          (∀ (t' : PositiveReal), w.val * fiberKL p₀ x t ≤ w.val * fiberKL p₀ x t') ↔ t = selTPos p₀ x)

/-- Directional-derivative transfer through local equality (elementary). -/
lemma hasDerivAt_dir_congr (p₀ : Parameters) {x : ℝ × ℝ × ℝ} (hx : x ∈ qDomain) (e : ℝ × ℝ × ℝ) {c : ℝ}
    (h : HasDerivAt (fun u : ℝ => RCoord p₀ (x + u • e)) c 0) :
    HasDerivAt (fun u : ℝ => l1R p₀ (x + u • e)) c 0 := by
  apply h.congr_of_eventuallyEq
  have hcont : Continuous (fun u : ℝ => x + u • e) := continuous_const.add (continuous_id.smul continuous_const)
  have : Filter.Tendsto (fun u : ℝ => x + u • e) (nhds 0) (nhds x) := by
    simpa using hcont.tendsto 0
  exact this.eventually (l1R_eventuallyEq p₀ hx)

theorem rel_prop3 : B2_prop3 → L1_prop3 := by
  intro hB p₀
  obtain ⟨han, hfd, hg, ha, hs, hst, ⟨L, w₁, w₂, x₁, x₂, hne, hL, h1, h2, -⟩⟩ := hB p₀
  refine ⟨?_, fun {x} hx => ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨L, w₁, w₂, x₁, x₂, hne, hL, h1, h2⟩⟩
  · intro q hq
    exact (han q hq).congr (l1R_eventuallyEq p₀ hq).symm
  · exact hasDerivAt_dir_congr p₀ hx _ (hg hx)
  · exact hasDerivAt_dir_congr p₀ hx _ (ha hx)
  · exact hasDerivAt_dir_congr p₀ hx _ (hs hx)
  · exact (hfd hx).congr_of_eventuallyEq (l1R_eventuallyEq p₀ hx)
  · intro ℓ ℓ' w x hx hℓ hmin
    have heq := l1R_eventuallyEq p₀ hx
    have hmin' : IsLocalMin (fun y => ℓ y + w.val * RCoord p₀ y) x := by
      apply hmin.congr
      filter_upwards [heq] with z hz
      rw [hz]
    have := hst w hx hℓ hmin'
    rw [heq.fderiv_eq]
    exact this

#relation_audit rel_prop3 [NIGBottleneck.RCoord_analyticOnNhd, NIGBottleneck.RCoord_eq,
  NIGBottleneck.hasFDerivAt_RCoord, NIGBottleneck.hasDerivAt_RCoord_gamma, NIGBottleneck.hasDerivAt_RCoord_alpha,
  NIGBottleneck.hasDerivAt_RCoord_s, NIGBottleneck.stationarity, NIGBottleneck.optimal_state_depends_on_weight]

theorem B2_prop3_holds : B2_prop3 := fun p₀ =>
  ⟨RCoord_analyticOnNhd p₀, fun hx => hasFDerivAt_RCoord p₀ hx, fun hx => hasDerivAt_RCoord_gamma p₀ hx,
    fun hx => hasDerivAt_RCoord_alpha p₀ hx, fun hx => hasDerivAt_RCoord_s p₀ hx,
    fun {_ _} w {_} hx hℓ hmin => stationarity p₀ w hx hℓ hmin, optimal_state_depends_on_weight p₀⟩

theorem L1_prop3_holds : L1_prop3 := rel_prop3 B2_prop3_holds

/-! ## proposition-4

L1_form: the ELBO, the evidence and the posterior KL are written literally as integrals of log density ratios
(they coincide definitionally with B2's `elbo`, `evidence`, `posteriorKL`). p(y∣z), for the fixed y, is a
measurable function `lik` of z. "E_q|log p(y∣z)| < ∞" is read as: `lik > 0` q-a.e. and `log lik` integrable
under the z-marginal. Interpretation caveat: in L1's standard convention log 0 = −∞ and integrability already
forces `lik > 0` a.e.; Lean's `Real.log 0 = 0` requires the positivity to be stated. K is Mathlib `klDiv`. -/

def l1Joint (p₀ : Parameters) (lik : ℝ → ℝ) (h : HierarchySpace) : ℝ := hierarchyDensity p₀ h * lik h.2
def l1Evidence (p₀ : Parameters) (lik : ℝ → ℝ) : ℝ := ∫ h, l1Joint p₀ lik h
def l1ELBO (p₀ : Parameters) (lik : ℝ → ℝ) (p : Parameters) : ℝ :=
  ∫ h, Real.log (l1Joint p₀ lik h / hierarchyDensity p h) ∂(hierarchyLaw p)
def l1PostKL (p₀ : Parameters) (lik : ℝ → ℝ) (p : Parameters) : ℝ :=
  ∫ h, Real.log (hierarchyDensity p h / (l1Joint p₀ lik h / l1Evidence p₀ lik)) ∂(hierarchyLaw p)

def L1_prop4 : Prop :=
  ∀ (p₀ : Parameters) (lik : ℝ → ℝ), Measurable lik → ∀ p : Parameters,
    (∀ᵐ h ∂hierarchyLaw p, 0 < lik h.2) → Integrable (fun z => Real.log (lik z)) (predictiveLaw p) →
      -l1ELBO p₀ lik p = -(∫ z, Real.log (lik z) ∂(l1PredLaw (quotientCoordinates p)))
          + (klDiv (nigLaw p) (nigLaw p₀)).toReal
      ∧ (0 < l1Evidence p₀ lik → -l1ELBO p₀ lik p = l1PostKL p₀ lik p - Real.log (l1Evidence p₀ lik))
      ∧ (Integrable (fun z => Real.log (lik z)) (l1PredLaw (quotientCoordinates p)) →
          (∀ᵐ z ∂l1PredLaw (quotientCoordinates p), 0 < lik z) →
          l1ELBO p₀ lik p ≤ l1ELBO p₀ lik (fiberParameters (quotientCoordinates p) (l1tStar p₀ (quotientCoordinates p)))
          ∧ (l1ELBO p₀ lik p = l1ELBO p₀ lik (fiberParameters (quotientCoordinates p)
                (l1tStar p₀ (quotientCoordinates p)))
              ↔ p = fiberParameters (quotientCoordinates p) (l1tStar p₀ (quotientCoordinates p))))

def B2_prop4 : Prop :=
  (∀ {p₀ : Parameters} {lik : ℝ → ℝ}, Measurable lik → ∀ (p : Parameters),
    (∀ᵐ h ∂hierarchyLaw p, 0 < lik h.2) → Integrable (fun z => Real.log (lik z)) (predictiveLaw p) →
      -elbo p₀ lik p = likelihoodLoss lik (quotientLaw (quotientCoordinates p)) + hierarchicalKL p p₀)
  ∧ (∀ {p₀ : Parameters} {lik : ℝ → ℝ}, Measurable lik → ∀ (p : Parameters), 0 < evidence p₀ lik →
      (∀ᵐ h ∂hierarchyLaw p, 0 < lik h.2) → Integrable (fun z => Real.log (lik z)) (predictiveLaw p) →
        -elbo p₀ lik p = posteriorKL p₀ lik p - Real.log (evidence p₀ lik))
  ∧ (∀ {p₀ : Parameters} {lik : ℝ → ℝ}, Measurable lik → ∀ (x : QuotientState) (p : Parameters),
      quotientCoordinates p = x → (∀ᵐ z ∂quotientLaw x, 0 < lik z) →
      Integrable (fun z => Real.log (lik z)) (quotientLaw x) →
        elbo p₀ lik p ≤ elbo p₀ lik (fiberParameters x (selTPos p₀ x))
        ∧ (elbo p₀ lik p = elbo p₀ lik (fiberParameters x (selTPos p₀ x)) ↔ p = fiberParameters x (selTPos p₀ x)))

theorem rel_prop4 : FoundKL → B2_prop4 → L1_prop4 := by
  rintro hK ⟨h1, h2, h3⟩ p₀ lik hm p hpos hint
  refine ⟨?_, fun hev => h2 hm p hev hpos hint, fun hint' hpos' => h3 hm _ p rfl hpos' hint'⟩
  have := h1 (p₀ := p₀) hm p hpos hint
  rw [← hK]
  exact this

#relation_audit rel_prop4 [NIGBottleneck.neg_elbo_eq, NIGBottleneck.neg_elbo_eq_originalObjective,
  NIGBottleneck.neg_elbo_eq_posteriorKL, NIGBottleneck.elbo_le_selected]

theorem B2_prop4_holds : B2_prop4 :=
  ⟨fun hm p hpos hint => neg_elbo_eq hm p hpos hint, fun hm p hev hpos hint => neg_elbo_eq_posteriorKL hm p hev hpos hint,
    fun hm x p hx hpos hint => elbo_le_selected hm x p hx hpos hint⟩

theorem L1_prop4_holds : L1_prop4 := rel_prop4 FoundKL_holds B2_prop4_holds

/-! ## proposition-5

L1_form: u_var = E[X] and u_epi = Var(μ) under NIG (as L1 defines them); V_z = Var of the law of z
(Mathlib `variance`). Selected quantities use the literal t_* and Φ_A. -/

def l1uVar (p : Parameters) : ℝ := ∫ q, q.2 ∂nigLaw p
def l1uEpi (p : Parameters) : ℝ := Var[fun q : ℝ × ℝ => q.1; nigLaw p]
def l1Vz (p : Parameters) : ℝ := Var[id; predictiveLaw p]

def L1_prop5 : Prop :=
  (∀ (x : QuotientState), 1 < x.alpha → ∀ t : PositiveReal,
      l1uVar (fiberParameters x t) = x.s / ((x.alpha - 1) * (1 + t))
      ∧ l1uEpi (fiberParameters x t) = x.s * t / ((x.alpha - 1) * (1 + t))
      ∧ l1Vz (fiberParameters x t) = l1uVar (fiberParameters x t) + l1uEpi (fiberParameters x t)
      ∧ l1Vz (fiberParameters x t) = x.s / (x.alpha - 1))
  ∧ (∀ (x : QuotientState), 1 < x.alpha → ∀ p₀ : Parameters,
      l1uEpi (fiberParameters x (l1tStar p₀ x)) / l1uVar (fiberParameters x (l1tStar p₀ x)) = l1TA p₀.alpha (l1d p₀ x)
      ∧ l1TA p₀.alpha (l1d p₀ x) = 1 / l1PhiA p₀.alpha (l1d p₀ x)
      ∧ l1uEpi (fiberParameters x (l1tStar p₀ x)) / l1Vz (fiberParameters x (l1tStar p₀ x))
          = l1TA p₀.alpha (l1d p₀ x) / (1 + l1TA p₀.alpha (l1d p₀ x))
      ∧ l1uVar (fiberParameters x (l1tStar p₀ x)) / l1Vz (fiberParameters x (l1tStar p₀ x))
          = 1 / (1 + l1TA p₀.alpha (l1d p₀ x)))
  ∧ (∀ p q : Parameters, predictiveLaw p = predictiveLaw q → l1Vz p = l1Vz q)
  ∧ (∀ (x : QuotientState), 1 < x.alpha → ∀ a b : ℝ, 0 < a → 0 < b → a + b = x.s / (x.alpha - 1) →
      ∃ t : PositiveReal, l1uVar (fiberParameters x t) = a ∧ l1uEpi (fiberParameters x t) = b)

def B2_prop5 : Prop :=
  (∀ (x : QuotientState), 1 < x.alpha → ∀ (t : PositiveReal),
    uVar (fiberParameters x t) = x.s / ((x.alpha - 1) * (1 + ↑t)))
  ∧ (∀ (x : QuotientState), 1 < x.alpha → ∀ (t : PositiveReal),
    uEpi (fiberParameters x t) = x.s * ↑t / ((x.alpha - 1) * (1 + ↑t)))
  ∧ (∀ (x : QuotientState), 1 < x.alpha → ∀ (t : PositiveReal),
    totalVar (fiberParameters x t) = uVar (fiberParameters x t) + uEpi (fiberParameters x t)
      ∧ totalVar (fiberParameters x t) = x.s / (x.alpha - 1))
  ∧ (∀ (x : QuotientState), 1 < x.alpha → ∀ (p₀ : Parameters),
      uEpi (fiberParameters x (selTPos p₀ x)) / uVar (fiberParameters x (selTPos p₀ x)) = selT p₀ x
      ∧ selT p₀ x = 1 / selNu p₀ x
      ∧ uEpi (fiberParameters x (selTPos p₀ x)) / totalVar (fiberParameters x (selTPos p₀ x))
          = selT p₀ x / (1 + selT p₀ x)
      ∧ uVar (fiberParameters x (selTPos p₀ x)) / totalVar (fiberParameters x (selTPos p₀ x)) = 1 / (1 + selT p₀ x))
  ∧ (∀ (p q : Parameters), predictiveLaw p = predictiveLaw q → totalVar p = totalVar q)
  ∧ (∀ (x : QuotientState), 1 < x.alpha → ∀ (a b : ℝ), 0 < a → 0 < b → a + b = x.s / (x.alpha - 1) →
      ∃ t, uVar (fiberParameters x t) = a ∧ uEpi (fiberParameters x t) = b)

theorem rel_prop5 : B2_prop5 ↔ L1_prop5 := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨fun x hx t => ⟨h1 x hx t, h2 x hx t, (h3 x hx t).1, (h3 x hx t).2⟩, fun x hx p₀ => h4 x hx p₀, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun x hx t => (h1 x hx t).1, fun x hx t => (h1 x hx t).2.1,
      fun x hx t => ⟨(h1 x hx t).2.2.1, (h1 x hx t).2.2.2⟩, fun x hx p₀ => h2 x hx p₀, h3, h4⟩

#relation_audit rel_prop5 [NIGBottleneck.uVar_fiber, NIGBottleneck.uEpi_fiber, NIGBottleneck.totalVar_fiber,
  NIGBottleneck.totalVar_eq_add, NIGBottleneck.selected_ratios, NIGBottleneck.totalVar_determined_by_predictiveLaw,
  NIGBottleneck.every_split_occurs]

theorem B2_prop5_holds : B2_prop5 :=
  ⟨uVar_fiber, uEpi_fiber, totalVar_fiber, selected_ratios, totalVar_determined_by_predictiveLaw, every_split_occurs⟩

theorem L1_prop5_holds : L1_prop5 := rel_prop5.mp B2_prop5_holds

end PostHocFidelity
