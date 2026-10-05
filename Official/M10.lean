import Mathlib
import Official.M05
import Official.M08

/-!
# The negative ELBO for the specified latent factorization

The generative model is `p₀(μ,X) N(z; μ, X) p(y | z)` and the variational
family is `q(μ,X | y) N(z; μ, X)` with `q(μ,X | y) = NIG(γ,ν,α,β)`. For a fixed observation `y`
the likelihood is a measurable function `lik z = p(y | z) ≥ 0`, and the evidence is
`p₀(y) = ∫ p₀(μ,X) N(z;μ,X) p(y|z) dμ dX dz`. The hypothesis `0 < p₀(y)` on the real-valued
Bochner integral also encodes `p₀(y) < ∞` (a non-integrable integrand has integral `0`). The
hypothesis `E_q |log p(y|z)| < ∞` is integrability of `log lik` under `q` together with
`lik > 0` `q`-almost everywhere (the logarithm of `0` being `−∞`).
-/

noncomputable section

namespace NIGBottleneck

open MeasureTheory

section Marginals

/-- The `(μ, X)`-marginal of the hierarchy is the NIG law. -/
theorem map_fst_hierarchyLaw (p : Parameters) :
    (hierarchyLaw p).map Prod.fst = nigLaw p := by
  have hH := measurable_hierarchyDensity p
  ext s hs
  rw [Measure.map_apply measurable_fst hs, hierarchyLaw, withDensity_apply _ (measurable_fst hs),
    ← lintegral_indicator (measurable_fst hs), Measure.volume_eq_prod,
    lintegral_prod _ ((hH.ennreal_ofReal.indicator (measurable_fst hs)).aemeasurable), nigLaw,
    withDensity_apply _ hs, ← lintegral_indicator hs]
  refine lintegral_congr fun q => ?_
  have h1 := lintegral_latent_indicator p MeasurableSet.univ q
  simp only [Set.indicator_univ, measure_univ, mul_one] at h1
  by_cases hq : q ∈ s
  · have : ∀ z, (Prod.fst ⁻¹' s).indicator (fun h => ENNReal.ofReal (hierarchyDensity p h)) (q, z)
        = ENNReal.ofReal (hierarchyDensity p (q, z)) := fun z =>
      Set.indicator_of_mem (by exact hq) _
    simp only [this, h1, Set.indicator_of_mem hq]
  · have : ∀ z, (Prod.fst ⁻¹' s).indicator (fun h => ENNReal.ofReal (hierarchyDensity p h)) (q, z)
        = 0 := fun z => Set.indicator_of_notMem (by exact hq) _
    simp only [this, lintegral_zero, Set.indicator_of_notMem hq]

instance isProbabilityMeasure_hierarchyLaw (p : Parameters) :
    IsProbabilityMeasure (hierarchyLaw p) := by
  have := isProbabilityMeasure_nigLaw p
  constructor
  have h := congrArg (fun μ : Measure (ℝ × ℝ) => μ Set.univ) (map_fst_hierarchyLaw p)
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
    measure_univ] at h
  exact h

/-- Integrals of functions of `(μ, X)` against the hierarchy. -/
lemma integral_hierarchyLaw_fst (p : Parameters) {g : ℝ × ℝ → ℝ}
    (hg : AEStronglyMeasurable g (nigLaw p)) :
    ∫ h, g h.1 ∂(hierarchyLaw p) = ∫ q, g q ∂(nigLaw p) := by
  rw [← map_fst_hierarchyLaw] at hg ⊢
  exact (integral_map measurable_fst.aemeasurable hg).symm

lemma integrable_hierarchyLaw_fst (p : Parameters) {g : ℝ × ℝ → ℝ}
    (hg : Integrable g (nigLaw p)) :
    Integrable (fun h : HierarchySpace => g h.1) (hierarchyLaw p) := by
  rw [← map_fst_hierarchyLaw] at hg
  exact hg.comp_measurable measurable_fst

/-- Integrals of functions of `z` against the hierarchy are integrals against the marginal law. -/
lemma integral_hierarchyLaw_snd (p : Parameters) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (predictiveLaw p)) :
    ∫ h, g h.2 ∂(hierarchyLaw p) = ∫ z, g z ∂(predictiveLaw p) :=
  (integral_map (measurable_snd (α := ℝ × ℝ) (β := ℝ)).aemeasurable hg).symm

lemma integrable_hierarchyLaw_snd_iff (p : Parameters) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (predictiveLaw p)) :
    Integrable (fun h : HierarchySpace => g h.2) (hierarchyLaw p)
      ↔ Integrable g (predictiveLaw p) :=
  (integrable_map_measure hg (measurable_snd (α := ℝ × ℝ) (β := ℝ)).aemeasurable).symm

end Marginals

section ELBO

variable (p₀ : Parameters) (lik : ℝ → ℝ)

/-- The joint density `p₀(μ,X) N(z;μ,X) p(y|z)` of the generative model at
the fixed observation `y`. -/
def jointDensity (h : HierarchySpace) : ℝ := hierarchyDensity p₀ h * lik h.2

/-- The evidence `p₀(y)`. -/
def evidence : ℝ := ∫ h, jointDensity p₀ lik h

/-- The unrestricted posterior density `p₀(μ,X,z | y)`. -/
def posteriorDensity (h : HierarchySpace) : ℝ := jointDensity p₀ lik h / evidence p₀ lik

/-- The evidence lower bound of `q = NIG(γ,ν,α,β) ⊗ N(z;μ,X)`,
`ELBO(q) = E_q log [p₀(μ,X) N(z;μ,X) p(y|z) / (q(μ,X|y) N(z;μ,X))]`. -/
def elbo (p : Parameters) : ℝ :=
  ∫ h, Real.log (jointDensity p₀ lik h / hierarchyDensity p h) ∂(hierarchyLaw p)

/-- `KL[q(μ,X,z|y) ‖ p₀(μ,X,z|y)]`, as a log-density-ratio integral. -/
def posteriorKL (p : Parameters) : ℝ :=
  ∫ h, Real.log (hierarchyDensity p h / posteriorDensity p₀ lik h) ∂(hierarchyLaw p)

/-- The reconstruction loss `ℓ(x;y) = −E_{f_x} log p(y|z)`, a functional of
the marginal law of `z` only. -/
def likelihoodLoss (μ : Measure ℝ) : ℝ := -∫ z, Real.log (lik z) ∂μ

/-- The same loss as a reconstruction functional in the sense of `Official.M01`. -/
def likelihoodReconstruction : ReconstructionLoss Unit :=
  fun μ _ => ((likelihoodLoss lik μ : ℝ) : EReal)

variable {p₀ lik}

lemma factors_pos_of_hierarchyDensity_pos {p : Parameters} {h : HierarchySpace}
    (hh : 0 < hierarchyDensity p h) :
    0 < nigDensity p h.1
      ∧ 0 < normalDensity (meanCoordinate h) (varianceCoordinate h) (latentCoordinate h) := by
  have hq0 := nigDensity_nonneg p h.1
  have hN0 := normalDensity_nonneg (meanCoordinate h) (varianceCoordinate h) (latentCoordinate h)
  refine ⟨hq0.lt_of_ne fun h' => ?_, hN0.lt_of_ne fun h' => ?_⟩
  · rw [hierarchyDensity, ← h', zero_mul] at hh; exact lt_irrefl 0 hh
  · rw [hierarchyDensity, ← h', mul_zero] at hh; exact lt_irrefl 0 hh

lemma hierarchyDensity_pos_of_pos (p p₀ : Parameters) (h : HierarchySpace)
    (hh : 0 < hierarchyDensity p h) : 0 < hierarchyDensity p₀ h := by
  obtain ⟨hq, hN⟩ := factors_pos_of_hierarchyDensity_pos hh
  exact mul_pos (nigDensity_pos_of_pos p p₀ h.1 hq) hN

lemma log_elbo_integrand {p : Parameters} {h : HierarchySpace} (hh : 0 < hierarchyDensity p h)
    (hl : 0 < lik h.2) :
    Real.log (jointDensity p₀ lik h / hierarchyDensity p h)
      = Real.log (lik h.2) - Real.log (nigDensity p h.1 / nigDensity p₀ h.1) := by
  obtain ⟨hq, hN⟩ := factors_pos_of_hierarchyDensity_pos hh
  have hq₀ := nigDensity_pos_of_pos p p₀ h.1 hq
  rw [jointDensity, hierarchyDensity, hierarchyDensity,
    show nigDensity p₀ h.1 * normalDensity (meanCoordinate h) (varianceCoordinate h)
        (latentCoordinate h) * lik h.2
        / (nigDensity p h.1 * normalDensity (meanCoordinate h) (varianceCoordinate h)
          (latentCoordinate h)) = lik h.2 * (nigDensity p h.1 / nigDensity p₀ h.1)⁻¹ by
      field_simp,
    Real.log_mul hl.ne' (inv_pos.mpr (div_pos hq hq₀)).ne', Real.log_inv, sub_eq_add_neg]

lemma ae_hierarchyDensity_pos (p : Parameters) :
    ∀ᵐ h ∂(hierarchyLaw p), 0 < hierarchyDensity p h :=
  ae_withDensity_ofReal_pos _ (measurable_hierarchyDensity p)

variable (hlm : Measurable lik)
include hlm

/-- With `λ = 1`, `−ELBO(q) = ℓ(x;y) + K(γ,ν,α,β)`, where `x` is the
quotient state of `q` and `ℓ` depends on `q` only through the marginal law `f_x` of `z`. -/
theorem neg_elbo_eq (p : Parameters) (hpos : ∀ᵐ h ∂(hierarchyLaw p), 0 < lik h.2)
    (hint : Integrable (fun z => Real.log (lik z)) (predictiveLaw p)) :
    -elbo p₀ lik p
      = likelihoodLoss lik (quotientLaw (quotientCoordinates p)) + hierarchicalKL p p₀ := by
  have hlog : AEStronglyMeasurable (fun z => Real.log (lik z)) (predictiveLaw p) :=
    (Real.measurable_log.comp hlm).aestronglyMeasurable
  have hKm : AEStronglyMeasurable (fun q => Real.log (nigDensity p q / nigDensity p₀ q))
      (nigLaw p) :=
    (integrable_nigLogRatio p p₀).aestronglyMeasurable
  have hae : (fun h => Real.log (jointDensity p₀ lik h / hierarchyDensity p h)) =ᵐ[hierarchyLaw p]
      fun h => Real.log (lik h.2) - Real.log (nigDensity p h.1 / nigDensity p₀ h.1) := by
    filter_upwards [ae_hierarchyDensity_pos p, hpos] with h hh hl
    exact log_elbo_integrand (p₀ := p₀) (lik := lik) hh hl
  have i1 : Integrable (fun h : HierarchySpace => Real.log (lik h.2)) (hierarchyLaw p) :=
    (integrable_hierarchyLaw_snd_iff p (g := fun z => Real.log (lik z)) hlog).mpr hint
  have i2 : Integrable (fun h : HierarchySpace => Real.log (nigDensity p h.1 / nigDensity p₀ h.1))
      (hierarchyLaw p) := integrable_hierarchyLaw_fst p
      (g := fun q => Real.log (nigDensity p q / nigDensity p₀ q)) (integrable_nigLogRatio p p₀)
  have e1 := integral_hierarchyLaw_snd p (g := fun z => Real.log (lik z)) hlog
  have e2 := integral_hierarchyLaw_fst p
    (g := fun q => Real.log (nigDensity p q / nigDensity p₀ q)) hKm
  rw [elbo, integral_congr_ae hae, integral_sub i1 i2, e1, e2, likelihoodLoss,
    ← predictiveLaw_eq_quotientLaw, hierarchicalKL]
  ring

/-- The same identity in the objective of `Official.M01` with `λ = 1`. -/
theorem neg_elbo_eq_originalObjective (p : Parameters)
    (hpos : ∀ᵐ h ∂(hierarchyLaw p), 0 < lik h.2)
    (hint : Integrable (fun z => Real.log (lik z)) (predictiveLaw p)) :
    ((-elbo p₀ lik p : ℝ) : EReal)
      = originalObjective (likelihoodReconstruction lik) p p₀ ⟨1, one_pos⟩ () := by
  rw [neg_elbo_eq hlm p hpos hint, originalObjective, likelihoodReconstruction,
    predictiveLaw_eq_quotientLaw, one_mul, EReal.coe_add]

/-- `−ELBO(q) = KL[q(μ,X,z|y) ‖ p₀(μ,X,z|y)] − log p₀(y)`. -/
theorem neg_elbo_eq_posteriorKL (p : Parameters) (hev : 0 < evidence p₀ lik)
    (hpos : ∀ᵐ h ∂(hierarchyLaw p), 0 < lik h.2)
    (hint : Integrable (fun z => Real.log (lik z)) (predictiveLaw p)) :
    -elbo p₀ lik p = posteriorKL p₀ lik p - Real.log (evidence p₀ lik) := by
  have hlog : AEStronglyMeasurable (fun z => Real.log (lik z)) (predictiveLaw p) :=
    (Real.measurable_log.comp hlm).aestronglyMeasurable
  have hae : (fun h => Real.log (hierarchyDensity p h / posteriorDensity p₀ lik h))
      =ᵐ[hierarchyLaw p]
      fun h => -Real.log (jointDensity p₀ lik h / hierarchyDensity p h)
        + Real.log (evidence p₀ lik) := by
    filter_upwards [ae_hierarchyDensity_pos p, hpos] with h hh hl
    have hj : 0 < jointDensity p₀ lik h :=
      mul_pos (hierarchyDensity_pos_of_pos p p₀ h hh) hl
    rw [posteriorDensity, div_div_eq_mul_div, Real.log_div (mul_pos hh hev).ne' hj.ne',
      Real.log_mul hh.ne' hev.ne', Real.log_div hj.ne' hh.ne']
    ring
  have i1 : Integrable (fun h => Real.log (jointDensity p₀ lik h / hierarchyDensity p h))
      (hierarchyLaw p) := by
    have hae' : (fun h => Real.log (jointDensity p₀ lik h / hierarchyDensity p h))
        =ᵐ[hierarchyLaw p]
        fun h => Real.log (lik h.2) - Real.log (nigDensity p h.1 / nigDensity p₀ h.1) := by
      filter_upwards [ae_hierarchyDensity_pos p, hpos] with h hh hl
      exact log_elbo_integrand (p₀ := p₀) (lik := lik) hh hl
    refine Integrable.congr ?_ hae'.symm
    exact ((integrable_hierarchyLaw_snd_iff p (g := fun z => Real.log (lik z)) hlog).mpr hint).sub
      (integrable_hierarchyLaw_fst p
      (g := fun q => Real.log (nigDensity p q / nigDensity p₀ q)) (integrable_nigLogRatio p p₀))
  have i1' : Integrable (fun h => -Real.log (jointDensity p₀ lik h / hierarchyDensity p h))
      (hierarchyLaw p) := i1.neg
  rw [posteriorKL, integral_congr_ae hae, integral_add i1' (integrable_const _), integral_neg,
    integral_const, probReal_univ, one_smul, elbo]
  ring

/-- Exact fiber minimization gives the best ELBO within this variational
family for each fixed predictive marginal: on the fiber of `x`, the ELBO is maximized exactly at
the selected hierarchy `(γ, 1/t_*, α, s/(1+t_*))`. -/
theorem elbo_le_selected (x : QuotientState) (p : Parameters) (hx : quotientCoordinates p = x)
    (hpos : ∀ᵐ z ∂(quotientLaw x), 0 < lik z)
    (hint : Integrable (fun z => Real.log (lik z)) (quotientLaw x)) :
    elbo p₀ lik p ≤ elbo p₀ lik (fiberParameters x (selTPos p₀ x))
      ∧ (elbo p₀ lik p = elbo p₀ lik (fiberParameters x (selTPos p₀ x))
          ↔ p = fiberParameters x (selTPos p₀ x)) := by
  set p' := fiberParameters x (selTPos p₀ x)
  have hint₁ : Integrable (fun z => Real.log (lik z)) (predictiveLaw p) := by
    rwa [predictiveLaw_eq_quotientLaw, hx]
  have hint₂ : Integrable (fun z => Real.log (lik z)) (predictiveLaw p') := by
    rwa [predictiveLaw_fiberParameters]
  have hpos₁ : ∀ᵐ h ∂(hierarchyLaw p), 0 < lik h.2 := by
    refine ae_of_ae_map (f := latentCoordinate) (μ := hierarchyLaw p) (p := fun z => 0 < lik z)
      measurable_snd.aemeasurable ?_
    rw [← predictiveLaw, predictiveLaw_eq_quotientLaw, hx]
    exact hpos
  have hpos₂ : ∀ᵐ h ∂(hierarchyLaw p'), 0 < lik h.2 := by
    refine ae_of_ae_map (f := latentCoordinate) (μ := hierarchyLaw p') (p := fun z => 0 < lik z)
      measurable_snd.aemeasurable ?_
    rw [← predictiveLaw, predictiveLaw_fiberParameters]
    exact hpos
  have e1 := neg_elbo_eq (p₀ := p₀) hlm p hpos₁ hint₁
  have e2 := neg_elbo_eq (p₀ := p₀) hlm p' hpos₂ hint₂
  rw [quotientCoordinates_fiberParameters] at e2
  rw [hx] at e1
  have hK : hierarchicalKL p p₀ = fiberKL p₀ x (fiberCoordinate p) := by
    rw [hierarchicalKL_eq_fiberKL, hx]
  have hK' : hierarchicalKL p' p₀ = fiberKL p₀ x (selTPos p₀ x) := rfl
  have hp : p = fiberParameters x (fiberCoordinate p) := by
    conv_lhs => rw [← fiberParameters_quotientCoordinates p]
    rw [hx]
  constructor
  · by_cases h : (fiberCoordinate p : ℝ) = selT p₀ x
    · have : fiberCoordinate p = selTPos p₀ x := Subtype.ext h
      rw [hp, this]
    · have := fiberKL_selected_lt p₀ x (fiberCoordinate p) h
      linarith
  · constructor
    · intro heq
      by_contra hne
      have h : (fiberCoordinate p : ℝ) ≠ selT p₀ x := by
        intro h'
        have : fiberCoordinate p = selTPos p₀ x := Subtype.ext h'
        exact hne (hp.trans (by rw [this]))
      have := fiberKL_selected_lt p₀ x (fiberCoordinate p) h
      linarith
    · intro h
      rw [h]

end ELBO

end NIGBottleneck
