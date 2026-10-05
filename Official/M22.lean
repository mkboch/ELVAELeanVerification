import Mathlib
import Official.M04
import Official.M05
import Official.M07
import Official.M08
import Official.M21

/-!
# Comparison with predictive and nonredundant regularization

(1) The predictive divergence `KL[f_x ‖ f_{x₀}]` is finite and at most
`R(x)`, with equality exactly at `x = x₀`. The proof writes the hierarchy as the
composition-product of the NIG law with the Gaussian kernel `(μ, X) ↦ N(μ, X)`, uses Mathlib's
data-processing inequality and KL chain rule, disintegrates the joint law with respect to `z`, and
shows that equality forces the density ratio of the two NIG laws to be almost everywhere constant.
(2) Regularizing only the mixing variable gives `K^V_mix(x) = KL[IG(α,s) ‖ IG(A,s₀)]`, which
ignores `γ`. (3) Regularizing the full nonredundant joint laws gives `K^{V,z}_mix(x) = K^V_mix(x)
+ α(γ−γ₀)²/(2s)`. Both depend only on the prior predictive coordinates, and neither is, in
general, the reduced regularizer `R`.
-/

noncomputable section

namespace NIGBottleneck

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal

section GaussianKernel

variable {α : Type*} [MeasurableSpace α]

/-- The Gaussian kernel `a ↦ N(m a, v a)`. -/
def gaussKernel (m v : α → ℝ) (hm : Measurable m) (hv : Measurable v) : Kernel α ℝ where
  toFun a := gaussianReal (m a) (v a).toNNReal
  measurable' := measurable_gaussianReal.comp (hm.prodMk hv.real_toNNReal)

instance (m v : α → ℝ) (hm : Measurable m) (hv : Measurable v) :
    IsMarkovKernel (gaussKernel m v hm hv) :=
  ⟨fun a => by
    change IsProbabilityMeasure (gaussianReal (m a) (v a).toNNReal)
    infer_instance⟩

lemma lintegral_section_normal (c : ℝ) (hc : 0 ≤ c) (m v : ℝ) (hcv : c ≠ 0 → 0 < v)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∫⁻ z, s.indicator (fun z => ENNReal.ofReal (c * normalDensity m v z)) z
      = ENNReal.ofReal c * gaussianReal m v.toNNReal s := by
  rcases eq_or_ne c 0 with h0 | h0
  · subst h0
    simp
  · have hv := hcv h0
    have hv' : v.toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hv
    have hfun : (fun z => ENNReal.ofReal (c * normalDensity m v z))
        = fun z => ENNReal.ofReal c * gaussianPDF m v.toNNReal z := by
      funext z
      rw [gaussianPDF, ← ENNReal.ofReal_mul hc, normalDensity_eq_gaussianPDFReal _ _ _ hv.le]
    rw [hfun, lintegral_indicator hs, lintegral_const_mul _ (measurable_gaussianPDF _ _),
      gaussianReal_apply _ hv']

/-- A density of the form `c(a) · N(z; m a, v a)` is the composition-product of `c · μ` with the
Gaussian kernel. -/
theorem withDensity_normal_eq_compProd (μ : Measure α) [SFinite μ] {c m v : α → ℝ}
    (hc : Measurable c) (hm : Measurable m) (hv : Measurable v) (hc0 : ∀ a, 0 ≤ c a)
    (hcv : ∀ a, c a ≠ 0 → 0 < v a) :
    (μ.prod volume).withDensity
        (fun p : α × ℝ => ENNReal.ofReal (c p.1 * normalDensity (m p.1) (v p.1) p.2))
      = (μ.withDensity fun a => ENNReal.ofReal (c a)) ⊗ₘ gaussKernel m v hm hv := by
  have hF : Measurable
      (fun p : α × ℝ => ENNReal.ofReal (c p.1 * normalDensity (m p.1) (v p.1) p.2)) := by
    unfold normalDensity
    fun_prop
  ext S hS
  rw [withDensity_apply _ hS, ← lintegral_indicator hS,
    lintegral_prod _ (hF.indicator hS).aemeasurable, Measure.compProd_apply hS,
    lintegral_withDensity_eq_lintegral_mul _ hc.ennreal_ofReal
      (Kernel.measurable_kernel_prodMk_left hS)]
  refine lintegral_congr fun a => ?_
  change _ = ENNReal.ofReal (c a) * gaussianReal (m a) (v a).toNNReal (Prod.mk a ⁻¹' S)
  rw [← lintegral_section_normal (c a) (hc0 a) (m a) (v a) (hcv a) (measurable_prodMk_left hS)]
  rfl

end GaussianKernel

section Hierarchy

instance (p : Parameters) : IsProbabilityMeasure (nigLaw p) := isProbabilityMeasure_nigLaw p

instance (p : Parameters) : IsProbabilityMeasure (predictiveLaw p) :=
  isProbabilityMeasure_predictiveLaw p

instance (x : QuotientState) : IsProbabilityMeasure (quotientLaw x) := by
  rw [← predictiveLaw_fiberParameters x ⟨1, one_pos⟩]
  infer_instance

/-- The kernel `(μ, X) ↦ N(μ, X)` of the hierarchy. -/
def hierKernel : Kernel (ℝ × ℝ) ℝ := gaussKernel Prod.fst Prod.snd measurable_fst measurable_snd

instance : IsMarkovKernel hierKernel := by
  unfold hierKernel
  infer_instance

theorem hierarchyLaw_eq_compProd (p : Parameters) : hierarchyLaw p = nigLaw p ⊗ₘ hierKernel := by
  rw [hierarchyLaw, Measure.volume_eq_prod]
  exact withDensity_normal_eq_compProd volume (measurable_nigDensity p) measurable_fst
    measurable_snd (nigDensity_nonneg p) fun q hq => by
      by_contra h
      exact hq (nigDensity_of_nonpos p q h)

/-- The marginal law of `z` is the kernel composition `N(μ, X) ∘ NIG`. -/
theorem predictiveLaw_eq_comp (p : Parameters) : predictiveLaw p = hierKernel ∘ₘ nigLaw p := by
  rw [predictiveLaw, hierarchyLaw_eq_compProd]
  exact Measure.snd_compProd (nigLaw p) hierKernel

/-- `KL[NIG(p) ‖ NIG(p₀)] = K(p ‖ p₀)` as extended reals. -/
theorem klDiv_nigLaw (p p₀ : Parameters) :
    klDiv (nigLaw p) (nigLaw p₀) = ENNReal.ofReal (hierarchicalKL p p₀) := by
  have hP : IsProbabilityMeasure (volume.withDensity fun q => ENNReal.ofReal (nigDensity p q)) :=
    isProbabilityMeasure_nigLaw p
  have hP0 : IsProbabilityMeasure (volume.withDensity fun q => ENNReal.ofReal (nigDensity p₀ q)) :=
    isProbabilityMeasure_nigLaw p₀
  have hkl := klDiv_withDensity_ofReal volume (measurable_nigDensity p) (measurable_nigDensity p₀)
    (nigDensity_nonneg p) (nigDensity_pos_of_pos p p₀) (integrable_nig_mul_logRatio p p₀)
  have hval : ∫ q : ℝ × ℝ, nigDensity p q * Real.log (nigDensity p q / nigDensity p₀ q)
      = hierarchicalKL p p₀ := by
    rw [hierarchicalKL, nigLaw, integral_withDensity_eq_integral_toReal_smul
      (measurable_nigDensity p).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    funext q
    rw [smul_eq_mul, ENNReal.toReal_ofReal (nigDensity_nonneg p q)]
  change klDiv (volume.withDensity fun q => ENNReal.ofReal (nigDensity p q))
    (volume.withDensity fun q => ENNReal.ofReal (nigDensity p₀ q)) = _
  rw [hkl, hval]

/-- KL divergences are invariant under the swap of coordinates. -/
theorem klDiv_map_swap {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (μ ν : Measure (β × γ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map Prod.swap) (ν.map Prod.swap) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν measurable_swap) ?_
  have h := klDiv_map_le (μ.map Prod.swap) (ν.map Prod.swap) measurable_swap
  rwa [Measure.map_map measurable_swap measurable_swap, Measure.map_map measurable_swap
    measurable_swap, Prod.swap_swap_eq, Measure.map_id, Measure.map_id] at h

end Hierarchy

section DataProcessing

variable (p₀ : Parameters)

/-- The predictive divergence `KL[f_x ‖ f_{x₀}]`. -/
def predictiveKL (x : QuotientState) : ℝ≥0∞ :=
  klDiv (quotientLaw x) (quotientLaw (priorQuotient p₀))

/-- Data processing: `KL[f_p ‖ f_{p₀}] ≤ K(p ‖ p₀)`. -/
theorem klDiv_predictiveLaw_le (p : Parameters) :
    klDiv (predictiveLaw p) (predictiveLaw p₀) ≤ ENNReal.ofReal (hierarchicalKL p p₀) := by
  have := isProbabilityMeasure_nigLaw p
  have := isProbabilityMeasure_nigLaw p₀
  rw [predictiveLaw_eq_comp, predictiveLaw_eq_comp, ← klDiv_nigLaw]
  exact klDiv_comp_right_le _ _ _

lemma quotientLaw_sel (x : QuotientState) :
    quotientLaw x = predictiveLaw (fiberParameters x (selTPos p₀ x))
      ∧ quotientLaw (priorQuotient p₀) = predictiveLaw p₀ :=
  ⟨(predictiveLaw_fiberParameters x _).symm, (predictiveLaw_eq_quotientLaw p₀).symm⟩

/-- The predictive divergence is finite and obeys
`KL[f_x ‖ f_{x₀}] ≤ R(x)`. -/
theorem predictiveKL_le_regularizerR (x : QuotientState) :
    predictiveKL p₀ x ≠ ⊤ ∧ (predictiveKL p₀ x).toReal ≤ regularizerR p₀ x := by
  have h := klDiv_predictiveLaw_le p₀ (fiberParameters x (selTPos p₀ x))
  rw [← (quotientLaw_sel p₀ x).1, ← (quotientLaw_sel p₀ x).2] at h
  have hR : regularizerR p₀ x = hierarchicalKL (fiberParameters x (selTPos p₀ x)) p₀ := rfl
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top h, ?_⟩
  rw [hR]
  exact ENNReal.toReal_le_of_le_ofReal (hierarchicalKL_nonneg _ _) h

end DataProcessing

section Equality

/-- The ratio of two NIG densities. -/
def nigRatio (p p₀ : Parameters) (q : ℝ × ℝ) : ℝ := nigDensity p q / nigDensity p₀ q

lemma measurable_nigRatio (p p₀ : Parameters) : Measurable (nigRatio p p₀) :=
  (measurable_nigDensity p).div (measurable_nigDensity p₀)

lemma nigDensity_eq_mul_ratio (p p₀ : Parameters) (q : ℝ × ℝ) :
    nigDensity p q = nigDensity p₀ q * nigRatio p p₀ q := by
  rcases (nigDensity_nonneg p₀ q).lt_or_eq with h | h
  · rw [nigRatio]
    field_simp
  · have : nigDensity p q = 0 := by
      rcases (nigDensity_nonneg p q).lt_or_eq with h' | h'
      · exact absurd (nigDensity_pos_of_pos p p₀ q h') (by rw [← h]; exact lt_irrefl 0)
      · exact h'.symm
    rw [this, ← h, zero_mul]

/-- `NIG(p) = NIG(p₀).withDensity (NIG(p)/NIG(p₀))`. -/
theorem nigLaw_eq_withDensity (p p₀ : Parameters) :
    nigLaw p = (nigLaw p₀).withDensity fun q => ENNReal.ofReal (nigRatio p p₀ q) := by
  rw [nigLaw, nigLaw, ← withDensity_mul _ (measurable_nigDensity p₀).ennreal_ofReal
    (measurable_nigRatio p p₀).ennreal_ofReal]
  congr 1
  funext q
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (nigDensity_nonneg p₀ q), nigDensity_eq_mul_ratio p p₀ q]

lemma map_swap_withDensity {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure (β × γ)) {F : β × γ → ℝ≥0∞} (hF : Measurable F) :
    (μ.withDensity F).map Prod.swap = (μ.map Prod.swap).withDensity (F ∘ Prod.swap) := by
  ext S hS
  rw [Measure.map_apply measurable_swap hS, withDensity_apply _ (measurable_swap hS),
    withDensity_apply _ hS, setLIntegral_map hS (hF.comp measurable_swap) measurable_swap]
  rfl

/-- If `KL[f_p ‖ f_{p₀}] = K(p ‖ p₀)`, then `NIG(p) = NIG(p₀)`. -/
theorem nigLaw_eq_of_klDiv_eq (p p₀ : Parameters)
    (h : klDiv (predictiveLaw p) (predictiveLaw p₀) = ENNReal.ofReal (hierarchicalKL p p₀)) :
    nigLaw p = nigLaw p₀ := by
  have hP := isProbabilityMeasure_nigLaw p
  have hP0 := isProbabilityMeasure_nigLaw p₀
  set P := nigLaw p with hPdef
  set P0 := nigLaw p₀ with hP0def
  set H := P ⊗ₘ hierKernel with hH
  set H0 := P0 ⊗ₘ hierKernel with hH0
  set ρ := H.map Prod.swap with hρ
  set ρ0 := H0.map Prod.swap with hρ0
  have hHP : IsProbabilityMeasure H := by rw [hH]; infer_instance
  have hH0P : IsProbabilityMeasure H0 := by rw [hH0]; infer_instance
  have hρP : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff measurable_swap.aemeasurable).mpr hHP
  have hρ0P : IsProbabilityMeasure ρ0 :=
    (Measure.isProbabilityMeasure_map_iff measurable_swap.aemeasurable).mpr hH0P
  have hfst : ρ.fst = predictiveLaw p := by
    rw [hρ, Measure.fst_map_swap, predictiveLaw_eq_comp]
    exact Measure.snd_compProd P hierKernel
  have hfst0 : ρ0.fst = predictiveLaw p₀ := by
    rw [hρ0, Measure.fst_map_swap, predictiveLaw_eq_comp]
    exact Measure.snd_compProd P0 hierKernel
  have hKL : klDiv ρ ρ0 = ENNReal.ofReal (hierarchicalKL p p₀) := by
    rw [hρ, hρ0, klDiv_map_swap, hH, hH0, klDiv_compProd_left, klDiv_nigLaw]
  -- chain rule along the disintegration with respect to `z`
  have hchain := klDiv_compProd_eq_add ρ.fst ρ0.fst ρ.condKernel ρ0.condKernel
  rw [ρ.disintegrate ρ.condKernel, ρ0.disintegrate ρ0.condKernel, hKL] at hchain
  have hf : klDiv ρ.fst ρ0.fst = ENNReal.ofReal (hierarchicalKL p p₀) := by
    rw [hfst, hfst0, h]
  rw [hf] at hchain
  have hzero : klDiv ρ (ρ.fst ⊗ₘ ρ0.condKernel) = 0 :=
    (ENNReal.add_right_inj ENNReal.ofReal_ne_top).mp (hchain.symm.trans (add_zero _).symm)
  rw [klDiv_eq_zero_iff] at hzero
  -- the Radon–Nikodym derivative `dρ/dρ0` is a function of `z` …
  have h1 := ProbabilityTheory.rnDeriv_measure_compProd_left ρ.fst ρ0.fst ρ0.condKernel
  rw [← hzero, ρ0.disintegrate ρ0.condKernel] at h1
  -- … and a function of `(μ, X)`
  have hHwd : H = H0.withDensity fun w => ENNReal.ofReal (nigRatio p p₀ w.1) := by
    rw [hH, hH0, hPdef, nigLaw_eq_withDensity p p₀,
      Measure.withDensity_compProd (measurable_nigRatio p p₀).ennreal_ofReal]
  have hρwd : ρ = ρ0.withDensity fun w => ENNReal.ofReal (nigRatio p p₀ w.2) := by
    rw [hρ, hρ0, hHwd, map_swap_withDensity H0
      (F := fun w : (ℝ × ℝ) × ℝ => ENNReal.ofReal (nigRatio p p₀ w.1))
      ((measurable_nigRatio p p₀).ennreal_ofReal.comp measurable_fst)]
    rfl
  have h2 : ρ.rnDeriv ρ0 =ᵐ[ρ0] fun w => ENNReal.ofReal (nigRatio p p₀ w.2) := by
    conv_lhs => rw [hρwd]
    exact Measure.rnDeriv_withDensity ρ0
      ((measurable_nigRatio p p₀).ennreal_ofReal.comp measurable_snd)
  set g := ρ.fst.rnDeriv ρ0.fst with hg
  have hae : ∀ᵐ w ∂ρ0, ENNReal.ofReal (nigRatio p p₀ w.2) = g w.1 := by
    filter_upwards [h1, h2] with w hw1 hw2
    rw [← hw2, hw1]
  -- pull back to `H0 = P0 ⊗ N`
  have hae' : ∀ᵐ w ∂H0, ENNReal.ofReal (nigRatio p p₀ w.1) = g w.2 :=
    ae_of_ae_map measurable_swap.aemeasurable hae
  have hmeasSet : MeasurableSet {w : (ℝ × ℝ) × ℝ | ENNReal.ofReal (nigRatio p p₀ w.1) = g w.2} :=
    measurableSet_eq_fun ((measurable_nigRatio p p₀).ennreal_ofReal.comp measurable_fst)
      ((Measure.measurable_rnDeriv _ _).comp measurable_snd)
  rw [hH0, Measure.ae_compProd_iff hmeasSet] at hae'
  -- for `P0`-a.e. `(μ, X)`, the equality holds for Lebesgue-a.e. `z`
  have hpos : ∀ᵐ q ∂P0, 0 < q.2 := by
    filter_upwards [ae_withDensity_ofReal_pos volume (measurable_nigDensity p₀)] with q hq
    by_contra hc
    rw [nigDensity_of_nonpos p₀ q hc] at hq
    exact lt_irrefl 0 hq
  have hgood : ∀ᵐ q ∂P0, ∀ᵐ z ∂(volume : Measure ℝ), ENNReal.ofReal (nigRatio p p₀ q) = g z := by
    filter_upwards [hae', hpos] with q hq hq2
    have hv : q.2.toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hq2
    exact (gaussianReal_absolutelyContinuous' q.1 hv).ae_le hq
  have hne : (ae P0).NeBot := ae_neBot.mpr (IsProbabilityMeasure.ne_zero P0)
  obtain ⟨q₀, hq₀⟩ := hgood.exists
  have hconst : ∀ᵐ q ∂P0, ENNReal.ofReal (nigRatio p p₀ q) = ENNReal.ofReal (nigRatio p p₀ q₀) := by
    filter_upwards [hgood] with q hq
    obtain ⟨z, hz, hz₀⟩ := (hq.and hq₀).exists
    rw [hz, hz₀]
  have hPc : P = ENNReal.ofReal (nigRatio p p₀ q₀) • P0 := by
    rw [hPdef, nigLaw_eq_withDensity p p₀, ← hP0def, withDensity_congr_ae hconst,
      withDensity_const]
  have hc1 : ENNReal.ofReal (nigRatio p p₀ q₀) = 1 := by
    have := congrArg (fun μ : Measure (ℝ × ℝ) => μ univ) hPc
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at this
    exact this.symm
  rw [hPc, hc1, one_smul]

variable (p₀ : Parameters)

/-- Equality `KL[f_x ‖ f_{x₀}] = R(x)` holds exactly at `x = x₀`, where
both sides vanish. -/
theorem predictiveKL_eq_iff (x : QuotientState) :
    (predictiveKL p₀ x).toReal = regularizerR p₀ x ↔ x = priorQuotient p₀ := by
  constructor
  · intro h
    set p := fiberParameters x (selTPos p₀ x)
    have hfin := (predictiveKL_le_regularizerR p₀ x).1
    have hR : regularizerR p₀ x = hierarchicalKL p p₀ := rfl
    have hkl : klDiv (predictiveLaw p) (predictiveLaw p₀)
        = ENNReal.ofReal (hierarchicalKL p p₀) := by
      rw [← (quotientLaw_sel p₀ x).1, ← (quotientLaw_sel p₀ x).2, ← hR, ← h]
      exact (ENNReal.ofReal_toReal hfin).symm
    have hnig := nigLaw_eq_of_klDiv_eq p p₀ hkl
    have hpred := predictiveLaw_eq_of_nigLaw_eq hnig
    rw [← (quotientLaw_sel p₀ x).1, ← (quotientLaw_sel p₀ x).2] at hpred
    exact quotientLaw_injective hpred
  · rintro rfl
    rw [predictiveKL, klDiv_self, ENNReal.toReal_zero]
    exact (minimizedKL_priorQuotient p₀).symm

end Equality

section Mixing

/-- `IG(α, s)` for a quotient state. -/
def mixingLaw (x : QuotientState) : Measure ℝ :=
  inverseGammaLaw ⟨x.alpha, x.alpha_pos⟩ ⟨x.s, x.s_pos⟩

instance (x : QuotientState) : IsProbabilityMeasure (mixingLaw x) :=
  isProbabilityMeasure_inverseGammaLaw _ _

/-- Regularizing only the mixing variable,
`K^V_mix(x) = KL[IG(α, s) ‖ IG(A, s₀)]`. It takes no `γ`-argument. -/
def mixKLV (x x₀ : QuotientState) : ℝ≥0∞ := klDiv (mixingLaw x) (mixingLaw x₀)

/-- Regularizing the full nonredundant joint laws,
`K^{V,z}_mix(x) = KL[IG(V;α,s)N(z;γ,V) ‖ IG(V;A,s₀)N(z;γ₀,V)]`. -/
def mixKLJoint (x x₀ : QuotientState) : ℝ≥0∞ :=
  klDiv (nonredundantJointLaw x) (nonredundantJointLaw x₀)

/-- `K^V_mix` ignores `γ`. -/
theorem mixKLV_ignores_gamma (x x' x₀ : QuotientState) (ha : x.alpha = x'.alpha)
    (hs : x.s = x'.s) :
    mixKLV x x₀ = mixKLV x' x₀ := by
  have : mixingLaw x = mixingLaw x' := by
    simp only [mixingLaw]
    congr 2
  rw [mixKLV, mixKLV, this]

/-- The NIG parameters `(γ, 1, α, s)` realizing the nonredundant joint law in swapped
coordinates. -/
def nonredParams (x : QuotientState) : Parameters :=
  ⟨x.gamma, 1, x.alpha, x.s, one_pos, x.alpha_pos, x.s_pos⟩

theorem nonredundantJointLaw_eq_map (x : QuotientState) :
    nonredundantJointLaw x = (nigLaw (nonredParams x)).map Prod.swap := by
  rw [nigLaw, map_swap_withDensity _ (measurable_nigDensity _).ennreal_ofReal,
    Measure.volume_eq_prod, Measure.prod_swap, ← Measure.volume_eq_prod, nonredundantJointLaw]
  congr 1
  funext q
  simp only [Function.comp, nigDensity, nonredParams, Prod.fst_swap, Prod.snd_swap, div_one]

theorem nonredundantJointLaw_eq_compProd (x : QuotientState) :
    nonredundantJointLaw x = mixingLaw x ⊗ₘ gaussKernel (fun _ => x.gamma) id measurable_const
      measurable_id := by
  rw [nonredundantJointLaw, Measure.volume_eq_prod]
  exact withDensity_normal_eq_compProd volume (measurable_inverseGammaDensity _ _)
    measurable_const measurable_id
    (fun V => inverseGammaDensity_nonneg _ _ _ x.alpha_pos x.s_pos.le) fun V hV => by
      by_contra h
      exact hV (inverseGammaDensity_of_nonpos _ _ _ h)

/-- The explicit inverse-gamma divergence
`A log(s/s₀) + log(Γ(A)/Γ(α)) + (α−A)ψ(α) − α + αs₀/s`. -/
def igKLForm (x x₀ : QuotientState) : ℝ :=
  x₀.alpha * Real.log (x.s / x₀.s) + Real.log (Real.Gamma x₀.alpha / Real.Gamma x.alpha)
    + (x.alpha - x₀.alpha) * digamma x.alpha - x.alpha + x.alpha * x₀.s / x.s

theorem klDiv_nonred (x x₀ : QuotientState) :
    mixKLJoint x x₀ = ENNReal.ofReal (hierarchicalKL (nonredParams x) (nonredParams x₀)) := by
  have := isProbabilityMeasure_nigLaw (nonredParams x)
  have := isProbabilityMeasure_nigLaw (nonredParams x₀)
  rw [mixKLJoint, nonredundantJointLaw_eq_map, nonredundantJointLaw_eq_map, klDiv_map_swap,
    klDiv_nigLaw]

/-- `K^V_mix(x)` is finite and equals the explicit inverse-gamma
divergence. -/
theorem mixKLV_eq (x x₀ : QuotientState) :
    mixKLV x x₀ = ENNReal.ofReal (igKLForm x x₀) ∧ 0 ≤ igKLForm x x₀ := by
  -- the nonredundant joint laws with the common center `γ₀` share the Gaussian kernel
  let x' : QuotientState := ⟨x₀.gamma, x.alpha, x.s, x.alpha_pos, x.s_pos⟩
  have hmix : mixingLaw x' = mixingLaw x := rfl
  have hIG := isProbabilityMeasure_inverseGammaLaw ⟨x.alpha, x.alpha_pos⟩ ⟨x.s, x.s_pos⟩
  have hIG0 := isProbabilityMeasure_inverseGammaLaw ⟨x₀.alpha, x₀.alpha_pos⟩ ⟨x₀.s, x₀.s_pos⟩
  have h1 : mixKLJoint x' x₀ = mixKLV x x₀ := by
    rw [mixKLJoint, nonredundantJointLaw_eq_compProd, nonredundantJointLaw_eq_compProd, hmix]
    exact klDiv_compProd_left _ _ _
  have hform : hierarchicalKL (nonredParams x') (nonredParams x₀) = igKLForm x x₀ := by
    rw [hierarchicalKL_eq_closedForm, nigKLClosedForm, igKLForm]
    simp only [nonredParams, x', sub_self, div_one, Real.log_one]
    ring
  rw [← h1, klDiv_nonred, hform]
  exact ⟨rfl, hform ▸ hierarchicalKL_nonneg _ _⟩

/-- `K^{V,z}_mix(x) = K^V_mix(x) + α(γ−γ₀)²/(2s)`. -/
theorem mixKLJoint_eq (x x₀ : QuotientState) :
    mixKLJoint x x₀
      = mixKLV x x₀ + ENNReal.ofReal (x.alpha * (x.gamma - x₀.gamma) ^ 2 / (2 * x.s)) := by
  obtain ⟨hV, hV0⟩ := mixKLV_eq x x₀
  have hs := x.s_pos
  have hform : hierarchicalKL (nonredParams x) (nonredParams x₀)
      = igKLForm x x₀ + x.alpha * (x.gamma - x₀.gamma) ^ 2 / (2 * x.s) := by
    rw [hierarchicalKL_eq_closedForm, nigKLClosedForm, igKLForm]
    simp only [nonredParams, div_one, Real.log_one]
    field_simp
    ring
  rw [klDiv_nonred, hform, hV, ENNReal.ofReal_add hV0 (by have := x.alpha_pos; positivity)]

/-- Both `K^V_mix` and `K^{V,z}_mix` depend on the complete prior only
through its prior predictive coordinates `x₀ = (γ₀, A, s₀)`. -/
theorem mix_depend_on_prior_predictive (p₀ p₀' : Parameters)
    (h : predictiveLaw p₀ = predictiveLaw p₀') (x : QuotientState) :
    mixKLV x (priorQuotient p₀) = mixKLV x (priorQuotient p₀')
      ∧ mixKLJoint x (priorQuotient p₀) = mixKLJoint x (priorQuotient p₀') := by
  have hq : priorQuotient p₀ = priorQuotient p₀' := (predictiveLaw_eq_iff p₀ p₀').mp h
  rw [hq]
  exact ⟨rfl, rfl⟩

/-- Neither `K^V_mix` nor `K^{V,z}_mix` is, in general, the reduced
complete-prior regularizer `R`: along the complete priors inducing `x₀` (which leave both mixing
regularizers fixed), `R(x)` diverges at any state with `γ ≠ γ₀`. -/
theorem mix_ne_regularizerR (x₀ x : QuotientState) (hγ : x.gamma ≠ x₀.gamma) :
    ∃ (n : ℝ) (hn : 0 < n), priorQuotient (priorFamily x₀ n hn) = x₀
      ∧ regularizerR (priorFamily x₀ n hn) x ≠ (mixKLV x x₀).toReal
      ∧ regularizerR (priorFamily x₀ n hn) x ≠ (mixKLJoint x x₀).toReal := by
  obtain ⟨N, hN⟩ := regularizerR_diverges x₀ x hγ
    (max (mixKLV x x₀).toReal (mixKLJoint x x₀).toReal)
  refine ⟨max N 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    quotientCoordinates_priorFamily x₀ _ _, ?_, ?_⟩
  · have := hN (max N 1) (lt_of_lt_of_le one_pos (le_max_right _ _)) (le_max_left _ _)
    exact (lt_of_le_of_lt (le_max_left _ _) this).ne'
  · have := hN (max N 1) (lt_of_lt_of_le one_pos (le_max_right _ _)) (le_max_left _ _)
    exact (lt_of_le_of_lt (le_max_right _ _) this).ne'

end Mixing

end NIGBottleneck
