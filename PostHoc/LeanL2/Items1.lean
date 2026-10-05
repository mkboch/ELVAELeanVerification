import PostHoc.LeanL2.Vocab
import PostHoc.Relations.GroupB

/-!
# L2 statement fidelity, items lemma-1 … proposition-5 (layer 2)

For each item, `L2_<item>` is the conjunction of the item's L2 theorem statements, with exactly the
hypotheses L2 states; hypotheses that L2 states in scoping sentences are applied to the theorems
they precede. The vocabulary is B2's, certified equal to L2's definitions in `Vocab`. `B2L2_<item>`
is the conjunction of the types of the B2 declarations that the statements translate. `rel2_<item>`
proves the relation structurally and is audited to exclude those declarations. eq-1, eq-2 and eq-3
consist only of L2 definitions (layer 1).
-/

-- cosmetic only: long statement lines are kept verbatim-readable
set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory NIGBottleneck

namespace PostHocL2Audit

/-! ## lemma-1 -/

def L2_lemma1 : Prop :=
  ∀ a b c : PositiveReal,
    (∫ x : ℝ, x⁻¹ ∂inverseGammaLaw a b) = (a : ℝ) / (b : ℝ)
    ∧ (∫ x : ℝ, Real.log x ∂inverseGammaLaw a b) = Real.log (b : ℝ) - digamma (a : ℝ)
    ∧ (1 < (a : ℝ) → (∫ x : ℝ, x ∂inverseGammaLaw a b) = (b : ℝ) / ((a : ℝ) - 1))
    ∧ Measure.map (fun x : ℝ => (c : ℝ) * x) (inverseGammaLaw a b)
        = inverseGammaLaw a ⟨(c : ℝ) * (b : ℝ), mul_pos c.property b.property⟩

def B2L2_lemma1 : Prop :=
  (∀ (a b : PositiveReal), ∫ (x : ℝ), x⁻¹ ∂inverseGammaLaw a b = ↑a / ↑b)
  ∧ (∀ (a b : PositiveReal), ∫ (x : ℝ), Real.log x ∂inverseGammaLaw a b = Real.log ↑b - digamma ↑a)
  ∧ (∀ (a b : PositiveReal), 1 < (a : ℝ) → ∫ (x : ℝ), x ∂inverseGammaLaw a b = ↑b / (↑a - 1))
  ∧ (∀ (a b c : PositiveReal), Measure.map (fun x => (c : ℝ) * x) (inverseGammaLaw a b)
      = inverseGammaLaw a ⟨(c : ℝ) * ↑b, mul_pos c.property b.property⟩)

theorem rel2_lemma1 : B2L2_lemma1 ↔ L2_lemma1 :=
  ⟨fun ⟨h1, h2, h3, h4⟩ a b c => ⟨h1 a b, h2 a b, h3 a b, h4 a b c⟩,
   fun h => ⟨fun a b => (h a b 1).1, fun a b => (h a b 1).2.1, fun a b => (h a b 1).2.2.1,
     fun a b c => (h a b c).2.2.2⟩⟩

#relation_audit rel2_lemma1 [NIGBottleneck.inverseGamma_integral_inv, NIGBottleneck.inverseGamma_integral_log,
  NIGBottleneck.inverseGamma_integral_id, NIGBottleneck.inverseGammaLaw_scale]

theorem B2L2_lemma1_holds : B2L2_lemma1 :=
  ⟨inverseGamma_integral_inv, inverseGamma_integral_log, inverseGamma_integral_id, inverseGammaLaw_scale⟩

/-! ## theorem-1
(1)
(2)
(3)
(4)
(5)
(6)
The chained ⟺ in (4) is read as both equivalences with Pred(p)=Pred(q). -/

def L2_theorem1 : Prop :=
  (∀ (x : QuotientState) (t : PositiveReal) (p : Parameters), quotientCoordinates (fiberParameters x t) = x
      ∧ fiberCoordinate (fiberParameters x t) = t ∧ fiberParameters (quotientCoordinates p) (fiberCoordinate p) = p)
  ∧ (∀ p : Parameters, predictiveLaw p = nigZMarginal p.gamma p.nu p.alpha p.beta
      ∧ predictiveLaw p = studentTMeasure (2 * p.alpha) p.gamma (quotientScale p / p.alpha))
  ∧ (∀ p : Parameters, predictiveLaw p = quotientLaw (quotientCoordinates p)
      ∧ predictiveLaw p = volume.withDensity (fun z => ENNReal.ofReal
          (Real.Gamma (p.alpha + 1 / 2) / (Real.Gamma p.alpha * Real.sqrt (2 * Real.pi * quotientScale p))
            * (1 + (z - p.gamma) ^ 2 / (2 * quotientScale p)) ^ (-p.alpha - 1 / 2))))
  ∧ (Function.Injective quotientLaw ∧ ∀ p q : Parameters,
      (predictiveLaw p = predictiveLaw q ↔ quotientCoordinates p = quotientCoordinates q)
      ∧ (predictiveLaw p = predictiveLaw q ↔
          (p.gamma = q.gamma ∧ p.alpha = q.alpha ∧ quotientScale p = quotientScale q)))
  ∧ (∀ {Y : Type} (L : ReconstructionLoss Y) (y : Y),
      (∀ (x : QuotientState) (p q : Parameters), p ∈ coordinateFiber x → q ∈ coordinateFiber x →
          L (predictiveLaw p) y = L (predictiveLaw q) y)
      ∧ (∀ (x : QuotientState) (t t' : PositiveReal),
          L (predictiveLaw (fiberParameters x t)) y = L (predictiveLaw (fiberParameters x t')) y)
      ∧ (∀ p : Parameters, L (predictiveLaw p) y = L (quotientLaw (quotientCoordinates p)) y))
  ∧ (∃ L : ReconstructionLoss Unit, ¬ Function.Injective (fun x : QuotientState => L (quotientLaw x) ()))

def B2L2_theorem1 : Prop :=
  (∀ (x : QuotientState) (t : PositiveReal), quotientCoordinates (fiberParameters x t) = x)
  ∧ (∀ (x : QuotientState) (t : PositiveReal), fiberCoordinate (fiberParameters x t) = t)
  ∧ (∀ (p : Parameters), fiberParameters (quotientCoordinates p) (fiberCoordinate p) = p)
  ∧ (∀ (p : Parameters), predictiveLaw p = nigZMarginal p.gamma p.nu p.alpha p.beta)
  ∧ (∀ (p : Parameters), predictiveLaw p = studentTMeasure (2 * p.alpha) p.gamma (studentScaleSquared p))
  ∧ (∀ (p : Parameters), predictiveLaw p = quotientLaw (quotientCoordinates p))
  ∧ (∀ (p : Parameters), predictiveLaw p = volume.withDensity fun z => ENNReal.ofReal
        (Real.Gamma (p.alpha + 1 / 2) / (Real.Gamma p.alpha * √(2 * Real.pi * quotientScale p)) *
          (1 + (z - p.gamma) ^ 2 / (2 * quotientScale p)) ^ (-p.alpha - 1 / 2)))
  ∧ Function.Injective quotientLaw
  ∧ (∀ (p q : Parameters), predictiveLaw p = predictiveLaw q ↔ quotientCoordinates p = quotientCoordinates q)
  ∧ (∀ (p q : Parameters), predictiveLaw p = predictiveLaw q ↔
      p.gamma = q.gamma ∧ p.alpha = q.alpha ∧ quotientScale p = quotientScale q)
  ∧ (∀ {Y : Type} (L : ReconstructionLoss Y) (y : Y) {x : QuotientState} {p q : Parameters},
      p ∈ coordinateFiber x → q ∈ coordinateFiber x → L (predictiveLaw p) y = L (predictiveLaw q) y)
  ∧ (∀ {Y : Type} (L : ReconstructionLoss Y) (y : Y) (x : QuotientState) (t t' : PositiveReal),
      L (predictiveLaw (fiberParameters x t)) y = L (predictiveLaw (fiberParameters x t')) y)
  ∧ (∀ {Y : Type} (L : ReconstructionLoss Y) (y : Y) (p : Parameters),
      L (predictiveLaw p) y = L (quotientLaw (quotientCoordinates p)) y)
  ∧ (∃ L : ReconstructionLoss Unit, ¬Function.Injective fun x => L (quotientLaw x) ())

theorem rel2_theorem1 : B2L2_theorem1 ↔ L2_theorem1 := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    exact ⟨fun x t p => ⟨h1 x t, h2 x t, h3 p⟩, fun p => ⟨h4 p, h5 p⟩, fun p => ⟨h6 p, h7 p⟩,
      ⟨h8, fun p q => ⟨h9 p q, h10 p q⟩⟩, fun L y => ⟨fun _ _ _ hp hq => h11 L y hp hq, h12 L y, h13 L y⟩, h14⟩
  · rintro ⟨h1, h2, h3, ⟨h4, h5⟩, h6, h7⟩
    exact ⟨fun x t => (h1 x t somePar).1, fun x t => (h1 x t somePar).2.1, fun p => (h1 someQS 1 p).2.2,
      fun p => (h2 p).1, fun p => (h2 p).2, fun p => (h3 p).1, fun p => (h3 p).2, h4, fun p q => (h5 p q).1,
      fun p q => (h5 p q).2, fun L y _ _ _ hp hq => (h6 L y).1 _ _ _ hp hq, fun L y => (h6 L y).2.1,
      fun L y => (h6 L y).2.2, h7⟩
where
  somePar : Parameters := ⟨0, 1, 1, 1, one_pos, one_pos, one_pos⟩
  someQS : QuotientState := ⟨0, 1, 1, one_pos, one_pos⟩

#relation_audit rel2_theorem1 [NIGBottleneck.quotientCoordinates_fiberParameters,
  NIGBottleneck.fiberCoordinate_fiberParameters, NIGBottleneck.fiberParameters_quotientCoordinates,
  NIGBottleneck.predictiveLaw_eq_nigZMarginal, NIGBottleneck.predictiveLaw_eq_studentT,
  NIGBottleneck.predictiveLaw_eq_quotientLaw, NIGBottleneck.predictiveLaw_density, NIGBottleneck.quotientLaw_injective,
  NIGBottleneck.predictiveLaw_eq_iff, NIGBottleneck.predictiveLaw_eq_iff_triple,
  NIGBottleneck.reconstruction_const_on_fiber, NIGBottleneck.reconstruction_fiberParameters,
  NIGBottleneck.reconstruction_factors_through_quotient, NIGBottleneck.exists_reconstruction_not_identifying]

theorem B2L2_theorem1_holds : B2L2_theorem1 :=
  ⟨quotientCoordinates_fiberParameters, fiberCoordinate_fiberParameters, fiberParameters_quotientCoordinates,
    predictiveLaw_eq_nigZMarginal, predictiveLaw_eq_studentT, predictiveLaw_eq_quotientLaw, predictiveLaw_density,
    quotientLaw_injective, predictiveLaw_eq_iff, predictiveLaw_eq_iff_triple,
    fun L y _ _ _ hp hq => reconstruction_const_on_fiber L y hp hq,
    fun L y x t t' => reconstruction_fiberParameters L y x t t', fun L y p => reconstruction_factors_through_quotient L y p,
    exists_reconstruction_not_identifying⟩

/-! ## proposition-1
(1)
(2)  (3) -/

def L2_prop1 : Prop :=
  ((∀ x, nonredundantLaw x = quotientLaw x) ∧ (∀ p, predictiveLaw p = nonredundantLaw (quotientCoordinates p))
      ∧ Function.Injective nonredundantLaw)
  ∧ (Function.Injective nonredundantLaw ∧ (∀ x, ∃ p, predictiveLaw p = nonredundantLaw x)
      ∧ ∀ p q, predictiveLaw p = predictiveLaw q ↔ quotientCoordinates p = quotientCoordinates q)
  ∧ (∀ x, (nonredundantJointLaw x).map Prod.snd = nonredundantLaw x)

def B2L2_prop1 : Prop :=
  (∀ (x : QuotientState), nonredundantLaw x = quotientLaw x)
  ∧ (∀ (p : Parameters), predictiveLaw p = nonredundantLaw (quotientCoordinates p))
  ∧ Function.Injective nonredundantLaw
  ∧ (Function.Injective nonredundantLaw ∧ (∀ (x : QuotientState), ∃ p, predictiveLaw p = nonredundantLaw x) ∧
      ∀ (p q : Parameters), predictiveLaw p = predictiveLaw q ↔ quotientCoordinates p = quotientCoordinates q)
  ∧ (∀ (x : QuotientState), Measure.map Prod.snd (nonredundantJointLaw x) = nonredundantLaw x)

theorem rel2_prop1 : B2L2_prop1 ↔ L2_prop1 :=
  ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨h1, h2, h3⟩, h4, h5⟩, fun ⟨⟨h1, h2, h3⟩, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩⟩

#relation_audit rel2_prop1 [NIGBottleneck.nonredundantLaw_eq_quotientLaw, NIGBottleneck.predictiveLaw_eq_nonredundantLaw,
  NIGBottleneck.nonredundantLaw_injective, NIGBottleneck.nonredundantLaw_uses_exactly_triple,
  NIGBottleneck.nonredundantJointLaw_map_snd]

theorem B2L2_prop1_holds : B2L2_prop1 :=
  ⟨nonredundantLaw_eq_quotientLaw, predictiveLaw_eq_nonredundantLaw, nonredundantLaw_injective,
    nonredundantLaw_uses_exactly_triple, nonredundantJointLaw_map_snd⟩

/-! ## proposition-2 -/

def L2_prop2 : Prop :=
  (∀ p p₀ : Parameters, Integrable (fun h => Real.log (nigDensity p h / nigDensity p₀ h)) (nigLaw p))
  ∧ (∀ p p₀ : Parameters, hierarchicalKL p p₀ = nigKLClosedForm p p₀)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : PositiveReal), fiberKL p₀ x t = fiberKLFormula p₀ x t)

def B2L2_prop2 : Prop :=
  (∀ (p p₀ : Parameters), Integrable (fun h => Real.log (nigDensity p h / nigDensity p₀ h)) (nigLaw p))
  ∧ (∀ (p p₀ : Parameters), hierarchicalKL p p₀ = nigKLClosedForm p p₀)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : PositiveReal), fiberKL p₀ x t = fiberKLFormula p₀ x ↑t)

theorem rel2_prop2 : B2L2_prop2 ↔ L2_prop2 := Iff.rfl

#relation_audit rel2_prop2 [NIGBottleneck.integrable_nigLogRatio, NIGBottleneck.hierarchicalKL_eq_closedForm,
  NIGBottleneck.fiberKL_eq]

theorem B2L2_prop2_holds : B2L2_prop2 := ⟨integrable_nigLogRatio, hierarchicalKL_eq_closedForm, fiberKL_eq⟩

/-! ## theorem-2 -/

def L2_theorem2 : Prop :=
  (∀ A d : ℝ, 0 < d → TA A d * PhiA A d = 1 ∧ PhiA A d = 1 / TA A d)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : ℝ), 0 < t →
      (selD p₀ x = 2 * p₀.alpha / (1 + t) + 1 / t ↔ t = selT p₀ x))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), (∀ t : ℝ, 0 < t → t ≠ selT p₀ x → 0 < fiberGap p₀ x t)
      ∧ fiberGap p₀ x (selT p₀ x) = 0)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : PositiveReal),
      fiberKL p₀ x t - fiberKL p₀ x (selTPos p₀ x) = fiberGap p₀ x t
      ∧ ((t : ℝ) ≠ selT p₀ x → fiberKL p₀ x (selTPos p₀ x) < fiberKL p₀ x t))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), ∃! t : PositiveReal, ∀ t', fiberKL p₀ x t ≤ fiberKL p₀ x t')
  ∧ (AnalyticOnNhd ℝ selTCoord statePriorDomain ∧ AnalyticOnNhd ℝ selNuCoord statePriorDomain
      ∧ AnalyticOnNhd ℝ selBetaCoord statePriorDomain)

def B2L2_theorem2 : Prop :=
  (∀ {A d : ℝ}, 0 < d → TA A d * PhiA A d = 1)
  ∧ (∀ {A d : ℝ}, 0 < d → PhiA A d = 1 / TA A d)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : ℝ), 0 < t → (selD p₀ x = 2 * p₀.alpha / (1 + t) + 1 / t ↔ t = selT p₀ x))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : ℝ), 0 < t → t ≠ selT p₀ x → 0 < fiberGap p₀ x t)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), fiberGap p₀ x (selT p₀ x) = 0)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : PositiveReal),
      fiberKL p₀ x t - fiberKL p₀ x (selTPos p₀ x) = fiberGap p₀ x ↑t)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : PositiveReal), ↑t ≠ selT p₀ x → fiberKL p₀ x (selTPos p₀ x) < fiberKL p₀ x t)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), ∃! t, ∀ (t' : PositiveReal), fiberKL p₀ x t ≤ fiberKL p₀ x t')
  ∧ AnalyticOnNhd ℝ selTCoord statePriorDomain ∧ AnalyticOnNhd ℝ selNuCoord statePriorDomain
  ∧ AnalyticOnNhd ℝ selBetaCoord statePriorDomain

theorem rel2_theorem2 : B2L2_theorem2 ↔ L2_theorem2 := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨fun A d hd => ⟨h1 hd, h2 hd⟩, h3, fun p₀ x => ⟨h4 p₀ x, h5 p₀ x⟩, fun p₀ x t => ⟨h6 p₀ x t, h7 p₀ x t⟩,
      h8, h9, h10, h11⟩
  · rintro ⟨h1, h3, h45, h67, h8, h9, h10, h11⟩
    exact ⟨fun {A d} hd => (h1 A d hd).1, fun {A d} hd => (h1 A d hd).2, h3, fun p₀ x => (h45 p₀ x).1,
      fun p₀ x => (h45 p₀ x).2, fun p₀ x t => (h67 p₀ x t).1, fun p₀ x t => (h67 p₀ x t).2, h8, h9, h10, h11⟩

#relation_audit rel2_theorem2 [NIGBottleneck.TA_mul_PhiA, NIGBottleneck.PhiA_eq_inv_TA,
  NIGBottleneck.selT_unique_solution, NIGBottleneck.fiberGap_pos, NIGBottleneck.fiberGap_self,
  NIGBottleneck.fiberKL_sub_selected, NIGBottleneck.fiberKL_selected_lt, NIGBottleneck.fiberKL_unique_minimizer,
  NIGBottleneck.selTCoord_analyticOnNhd, NIGBottleneck.selNuCoord_analyticOnNhd, NIGBottleneck.selBetaCoord_analyticOnNhd]

theorem B2L2_theorem2_holds : B2L2_theorem2 :=
  ⟨TA_mul_PhiA, PhiA_eq_inv_TA, selT_unique_solution, fiberGap_pos, fiberGap_self, fiberKL_sub_selected,
    fiberKL_selected_lt, fiberKL_unique_minimizer, selTCoord_analyticOnNhd, selNuCoord_analyticOnNhd,
    selBetaCoord_analyticOnNhd⟩

/-! ## corollary-1 -/

def L2_cor1 : Prop :=
  (∀ p p₀ : Parameters, hierarchicalKL p p₀ = 0 ↔ nigLaw p = nigLaw p₀)
  ∧ (∀ p₀ : Parameters, selT p₀ (priorQuotient p₀) = 1 / p₀.nu
      ∧ fiberParameters (priorQuotient p₀) (selTPos p₀ (priorQuotient p₀)) = p₀)
  ∧ (∀ p₀ : Parameters, (priorQuotient p₀).gamma = p₀.gamma ∧ selNu p₀ (priorQuotient p₀) = p₀.nu
      ∧ (priorQuotient p₀).alpha = p₀.alpha ∧ selBeta p₀ (priorQuotient p₀) = p₀.beta)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), 0 ≤ minimizedKL p₀ x ∧ minimizedKL p₀ (priorQuotient p₀) = 0
      ∧ (minimizedKL p₀ x = 0 ↔ x = priorQuotient p₀))

def B2L2_cor1 : Prop :=
  (∀ (p p₀ : Parameters), hierarchicalKL p p₀ = 0 ↔ nigLaw p = nigLaw p₀)
  ∧ (∀ (p₀ : Parameters), selT p₀ (priorQuotient p₀) = 1 / p₀.nu)
  ∧ (∀ (p₀ : Parameters), fiberParameters (priorQuotient p₀) (selTPos p₀ (priorQuotient p₀)) = p₀)
  ∧ (∀ (p₀ : Parameters), (priorQuotient p₀).gamma = p₀.gamma ∧ selNu p₀ (priorQuotient p₀) = p₀.nu ∧
      (priorQuotient p₀).alpha = p₀.alpha ∧ selBeta p₀ (priorQuotient p₀) = p₀.beta)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), 0 ≤ minimizedKL p₀ x)
  ∧ (∀ (p₀ : Parameters), minimizedKL p₀ (priorQuotient p₀) = 0)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), minimizedKL p₀ x = 0 ↔ x = priorQuotient p₀)

theorem rel2_cor1 : B2L2_cor1 ↔ L2_cor1 :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, fun p₀ => ⟨h2 p₀, h3 p₀⟩, h4, fun p₀ x => ⟨h5 p₀ x, h6 p₀, h7 p₀ x⟩⟩,
   fun ⟨h1, h23, h4, h567⟩ => ⟨h1, fun p₀ => (h23 p₀).1, fun p₀ => (h23 p₀).2, h4, fun p₀ x => (h567 p₀ x).1,
     fun p₀ => (h567 p₀ (priorQuotient p₀)).2.1, fun p₀ x => (h567 p₀ x).2.2⟩⟩

#relation_audit rel2_cor1 [NIGBottleneck.hierarchicalKL_eq_zero_iff, NIGBottleneck.selT_priorQuotient,
  NIGBottleneck.selected_priorQuotient, NIGBottleneck.selected_priorQuotient_coords, NIGBottleneck.minimizedKL_nonneg,
  NIGBottleneck.minimizedKL_priorQuotient, NIGBottleneck.minimizedKL_eq_zero_iff]

theorem B2L2_cor1_holds : B2L2_cor1 :=
  ⟨hierarchicalKL_eq_zero_iff, selT_priorQuotient, selected_priorQuotient, selected_priorQuotient_coords,
    minimizedKL_nonneg, minimizedKL_priorQuotient, minimizedKL_eq_zero_iff⟩

/-! ## theorem-3

  (L, p₀, w, y are the ambient parameters of these statements.) -/

def L2_theorem3 : Prop :=
  ∀ {Y : Type} (L : ReconstructionLoss Y) (p₀ : Parameters) (w : PositiveReal) (y : Y),
    (⨅ p, originalObjective L p p₀ w y = ⨅ x, reducedObjective L p₀ w x y)
    ∧ (∀ (x : QuotientState) (t : PositiveReal), originalObjective L (fiberParameters x t) p₀ w y
          = reducedObjective L p₀ w x y + ((w.val * (fiberKL p₀ x t - regularizerR p₀ x) : ℝ) : EReal)
        ∧ fiberKL p₀ x t - regularizerR p₀ x = fiberGap p₀ x t)
    ∧ (∀ (x : QuotientState) (t : PositiveReal),
        (∀ t' : PositiveReal, w.val * fiberKL p₀ x t ≤ w.val * fiberKL p₀ x t') ↔ t = selTPos p₀ x)
    ∧ ((∀ x, quotientLoss L x y ≠ ⊥) → (⨅ x, reducedObjective L p₀ w x y) ≠ ⊥ → (⨅ x, reducedObjective L p₀ w x y) ≠ ⊤ →
        ∀ p, originalObjective L p p₀ w y = ⨅ q, originalObjective L q p₀ w y ↔
          (reducedObjective L p₀ w (quotientCoordinates p) y = ⨅ x, reducedObjective L p₀ w x y
            ∧ p = fiberParameters (quotientCoordinates p) (selTPos p₀ (quotientCoordinates p))))
    ∧ (∀ x, reducedObjective L p₀ w x y = ⨅ x', reducedObjective L p₀ w x' y →
        originalObjective L (fiberParameters x (selTPos p₀ x)) p₀ w y = ⨅ q, originalObjective L q p₀ w y)
    ∧ ((∀ x, quotientLoss L x y ≠ ⊥) → (⨅ x, reducedObjective L p₀ w x y) = ⊥ →
        (∀ p, originalObjective L p p₀ w y ≠ ⨅ q, originalObjective L q p₀ w y)
        ∧ ∀ x, reducedObjective L p₀ w x y ≠ ⨅ x', reducedObjective L p₀ w x' y)
    ∧ (∃ L' : ReconstructionLoss Unit, (∀ μ, 0 ≤ L' μ () ∧ L' μ () ≠ ⊤)
        ∧ ¬ ∃ p, ∀ q, originalObjective L' p p₀ w () ≤ originalObjective L' q p₀ w ())

theorem rel2_theorem3 : PostHocFidelity.B2_theorem3 → (∀ {Y : Type} (L : ReconstructionLoss Y) (p₀ : Parameters) (w : PositiveReal) (y : Y)
    (x : QuotientState), reducedObjective L p₀ w x y = ⨅ x', reducedObjective L p₀ w x' y →
      originalObjective L (fiberParameters x (selTPos p₀ x)) p₀ w y = ⨅ q, originalObjective L q p₀ w y) → L2_theorem3 := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩ hsel Y L p₀ w y
  exact ⟨h1 L p₀ w y, fun x t => ⟨h2 L p₀ w y x t, h3 p₀ x t⟩, fun x t => h4 p₀ w x t,
    fun hl hb ht => h5 L p₀ w y hl ⟨hb, ht⟩, fun x hx => hsel L p₀ w y x hx, h6 L p₀ w y, h7 p₀ w⟩

theorem rel2_theorem3_conv : L2_theorem3 → PostHocFidelity.B2_theorem3 := by
  intro h
  exact ⟨fun L p₀ w y => (h L p₀ w y).1, fun L p₀ w y x t => ((h L p₀ w y).2.1 x t).1,
    fun p₀ x t => ((h (fun _ _ => (0 : EReal)) p₀ ⟨1, one_pos⟩ ()).2.1 x t).2,
    fun p₀ w x t => (h (fun _ _ => (0 : EReal)) p₀ w ()).2.2.1 x t,
    fun L p₀ w y hl hfin => (h L p₀ w y).2.2.2.1 hl hfin.1 hfin.2, fun L p₀ w y hl hb => (h L p₀ w y).2.2.2.2.2.1 hl hb,
    fun p₀ w => (h (fun _ _ => (0 : EReal)) p₀ w ()).2.2.2.2.2.2⟩

#relation_audit rel2_theorem3 [NIGBottleneck.iInf_originalObjective_eq, NIGBottleneck.originalObjective_fiber,
  NIGBottleneck.fiberKL_sub_regularizerR, NIGBottleneck.fiber_minimizer_independent_of_weight,
  NIGBottleneck.originalObjective_minimizer_iff, NIGBottleneck.selected_minimizes_originalObjective,
  NIGBottleneck.not_attained_of_iInf_eq_bot, NIGBottleneck.exists_loss_without_minimizer]

#relation_audit rel2_theorem3_conv [NIGBottleneck.iInf_originalObjective_eq, NIGBottleneck.originalObjective_fiber,
  NIGBottleneck.fiberKL_sub_regularizerR, NIGBottleneck.fiber_minimizer_independent_of_weight,
  NIGBottleneck.originalObjective_minimizer_iff, NIGBottleneck.selected_minimizes_originalObjective,
  NIGBottleneck.not_attained_of_iInf_eq_bot, NIGBottleneck.exists_loss_without_minimizer]

end PostHocL2Audit
