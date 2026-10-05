import Official.M01
import Official.M02
import Official.M03
import Official.M04
import Official.M05
import Official.M07
import Official.M22
import PostHoc.Relations.Audit

/-!
# L1 ↔ B2 formal relation certificates, group A

Items: eq-1, eq-2, lemma-1, theorem-1, proposition-1, proposition-2.

Method:
* `L1_<item>` is a proposition schema written from the L1 statement. Where L1 gives an explicit
  formula, the formula is written out here literally rather than taken from a B2 definition.
  Probability objects (laws, KL) use B2 or Mathlib vocabulary; that choice is an interpretive step
  and is stated.
* `B2_<item>` restates the types of the B2 declarations for the item.
* `rel_<item>` proves the logical relation between the two schemas. `#relation_audit` checks
  mechanically that the proof does not use the item's target B2 theorems.
* `B2_<item>_holds` checks that the restated schema is exactly what B2 proves (it is proved *by* the
  targets). `L1_<item>_holds` follows.
-/

-- cosmetic only: long statement lines are kept verbatim-readable
set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory NIGBottleneck

namespace PostHocFidelity

/-! ## eq-1

L1_form: the joint law of ((μ,X),z) has the product density IG(X;α,β)·N(μ;γ,X/ν)·N(z;μ,X), with L1's density
formulas written literally. Its (μ,X)-part composed with the Gaussian kernel z∣μ,X is the joint law (`⊗ₘ`, the
hierarchical reading), and the law of z is the image of the joint law under h ↦ z.
Interpretation: "∼" is read as the Lebesgue-density specification (the Gaussian density is the standard one,
which L1 does not display), and as `compProd` for the conditional step. -/

/-- L1's inverse-gamma density, literally (extended by 0 off x > 0). -/
def l1IGDensity (a b x : ℝ) : ℝ :=
  if 0 < x then b ^ a / Real.Gamma a * x ^ (-a - 1) * Real.exp (-b / x) else 0

/-- The standard Gaussian density N(m, v) (not displayed in L1). -/
def l1NormalDensity (m v z : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-((z - m) ^ 2) / (2 * v))

def L1_eq1 : Prop :=
  ∀ p : Parameters,
    (∀ h : HierarchySpace, hierarchyDensity p h =
        l1IGDensity p.alpha p.beta h.1.2 * l1NormalDensity p.gamma (h.1.2 / p.nu) h.1.1
          * l1NormalDensity h.1.1 h.1.2 h.2)
    ∧ hierarchyLaw p = volume.withDensity (fun h => ENNReal.ofReal
        (l1IGDensity p.alpha p.beta h.1.2 * l1NormalDensity p.gamma (h.1.2 / p.nu) h.1.1
          * l1NormalDensity h.1.1 h.1.2 h.2))
    ∧ hierarchyLaw p = nigLaw p ⊗ₘ hierKernel
    ∧ predictiveLaw p = (hierarchyLaw p).map (fun h => h.2)

/-- B2 side: the M01 definitions (eq-1 targets are definitions) together with the foundational M22 lemma
`hierarchyLaw_eq_compProd`. -/
def B2_eq1 : Prop :=
  ∀ p : Parameters, hierarchyLaw p = nigLaw p ⊗ₘ hierKernel

theorem rel_eq1 : B2_eq1 ↔ L1_eq1 := by
  constructor
  · intro h p
    exact ⟨fun _ => rfl, rfl, h p, rfl⟩
  · intro h p
    exact (h p).2.2.1

#relation_audit rel_eq1 [NIGBottleneck.hierarchyLaw_eq_compProd]

theorem B2_eq1_holds : B2_eq1 := hierarchyLaw_eq_compProd

theorem L1_eq1_holds : L1_eq1 := rel_eq1.mp B2_eq1_holds

/-! ## eq-2

L1_form: the objective is the reconstruction loss of the law of z plus λ times Mathlib's Kullback–Leibler
divergence `klDiv` of the NIG laws, converted to a real number. Interpretation: KL is read as Mathlib `klDiv`
(an extended nonnegative real); B2 defines it as the log-density-ratio integral. Their equality is the
foundational M07 lemma `hierarchicalKL_eq_toReal_klDiv`, which is not an eq-2 target. -/

def L1_eq2 : Prop :=
  ∀ {Y : Type} (rec : Measure ℝ → Y → EReal) (p p₀ : Parameters) (lam : PositiveReal) (y : Y),
    originalObjective rec p p₀ lam y =
      rec (predictiveLaw p) y + ((lam.val * (klDiv (nigLaw p) (nigLaw p₀)).toReal : ℝ) : EReal)

def B2_eq2 : Prop :=
  ∀ p p₀ : Parameters, hierarchicalKL p p₀ = (klDiv (nigLaw p) (nigLaw p₀)).toReal

theorem rel_eq2 : B2_eq2 ↔ L1_eq2 := by
  constructor
  · intro h Y rec p p₀ lam y
    simp only [originalObjective]
    rw [h p p₀]
  · intro h p p₀
    have := @h Unit (fun _ _ => 0) p p₀ ⟨1, one_pos⟩ ()
    simp only [originalObjective, zero_add, one_mul] at this
    exact EReal.coe_injective this

#relation_audit rel_eq2 [NIGBottleneck.hierarchicalKL_eq_toReal_klDiv]

theorem B2_eq2_holds : B2_eq2 := hierarchicalKL_eq_toReal_klDiv

theorem L1_eq2_holds : L1_eq2 := rel_eq2.mp B2_eq2_holds

/-! ## lemma-1

L1:  with ψ(a)=d/da log Γ(a).

L1_form: IG(a,b) is the measure with L1's literal density, and ψ is L1's literal derivative of log Γ. -/

def l1IGLaw (a b : ℝ) : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (l1IGDensity a b x))

def l1Psi (a : ℝ) : ℝ := deriv (fun s : ℝ => Real.log (Real.Gamma s)) a

def L1_lemma1 : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b →
    (∫ x, x⁻¹ ∂l1IGLaw a b) = a / b
    ∧ (∫ x, Real.log x ∂l1IGLaw a b) = Real.log b - l1Psi a
    ∧ (1 < a → ∫ x, x ∂l1IGLaw a b = b / (a - 1))
    ∧ ∀ c : ℝ, 0 < c → (l1IGLaw a b).map (fun x => c * x) = l1IGLaw a (c * b)

def B2_lemma1 : Prop :=
  (∀ a b : PositiveReal, (∫ x : ℝ, x⁻¹ ∂inverseGammaLaw a b) = (a : ℝ) / (b : ℝ))
  ∧ (∀ a b : PositiveReal,
      (∫ x : ℝ, Real.log x ∂inverseGammaLaw a b) = Real.log (b : ℝ) - digamma (a : ℝ))
  ∧ (∀ a b : PositiveReal, 1 < (a : ℝ) → (∫ x : ℝ, x ∂inverseGammaLaw a b) = (b : ℝ) / ((a : ℝ) - 1))
  ∧ (∀ a b c : PositiveReal, Measure.map (fun x : ℝ => (c : ℝ) * x) (inverseGammaLaw a b) =
      inverseGammaLaw a ⟨(c : ℝ) * (b : ℝ), mul_pos c.property b.property⟩)

lemma l1IGLaw_eq (a b : PositiveReal) : l1IGLaw a b = inverseGammaLaw a b := rfl

theorem rel_lemma1 : B2_lemma1 ↔ L1_lemma1 := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ a b ha hb
    refine ⟨h1 ⟨a, ha⟩ ⟨b, hb⟩, h2 ⟨a, ha⟩ ⟨b, hb⟩, fun h => h3 ⟨a, ha⟩ ⟨b, hb⟩ h, fun c hc => ?_⟩
    exact h4 ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  · intro h
    refine ⟨fun a b => (h a.1 b.1 a.2 b.2).1, fun a b => (h a.1 b.1 a.2 b.2).2.1,
      fun a b ha => (h a.1 b.1 a.2 b.2).2.2.1 ha, fun a b c => (h a.1 b.1 a.2 b.2).2.2.2 c.1 c.2⟩

#relation_audit rel_lemma1 [NIGBottleneck.inverseGamma_integral_inv, NIGBottleneck.inverseGamma_integral_log,
  NIGBottleneck.inverseGamma_integral_id, NIGBottleneck.inverseGammaLaw_scale]

theorem B2_lemma1_holds : B2_lemma1 :=
  ⟨inverseGamma_integral_inv, inverseGamma_integral_log, inverseGamma_integral_id, inverseGammaLaw_scale⟩

theorem L1_lemma1_holds : L1_lemma1 := rel_lemma1.mp B2_lemma1_holds

/-! ## theorem-1

L1. Clauses:
(a) with s=β(1+1/ν), the marginal density of z is Γ(α+½)/(Γ(α)√(2πs))·(1+(z−γ)²/(2s))^{−α−½};
(b) equivalently Student with location γ, 2α degrees of freedom and squared scale w=s/α;
(c) two quadruples induce the same marginal law iff their triples (γ,α,s) agree;
(d) the fiber is F_x={(γ,1/t,α,s/(1+t)) : t>0};
(e) t=1/ν is a global coordinate on every fiber;
(f) every reconstruction functional is constant on F_x;
(g) the entire marginal law identifies x;
(h) an individual reconstruction functional may identify less.

Interpretation: "Student distribution" is written with the standard Student density literally (Mathlib has no
Student-t law). Clause (h) "may identify less" is read as: some functional is not injective in x. -/

/-- L1's s = β(1+1/ν), literally. -/
def l1S (p : Parameters) : ℝ := p.beta * (1 + 1 / p.nu)

/-- Standard Student density with `k` degrees of freedom, location `m`, squared scale `w` (literal). -/
def l1StudentDensity (k m w z : ℝ) : ℝ :=
  Real.Gamma ((k + 1) / 2) / (Real.Gamma (k / 2) * Real.sqrt (k * Real.pi * w))
    * (1 + (z - m) ^ 2 / (k * w)) ^ (-((k + 1) / 2))

/-- L1's fiber of a triple (γ,α,s), as a set of parameter quadruples, literally. -/
def l1Fiber (g a s : ℝ) : Set Parameters :=
  {p | ∃ t : ℝ, 0 < t ∧ p.gamma = g ∧ p.nu = 1 / t ∧ p.alpha = a ∧ p.beta = s / (1 + t)}

def L1_theorem1 : Prop :=
  (∀ p : Parameters, predictiveLaw p = volume.withDensity (fun z => ENNReal.ofReal
      (Real.Gamma (p.alpha + 1 / 2) / (Real.Gamma p.alpha * Real.sqrt (2 * Real.pi * l1S p))
        * (1 + (z - p.gamma) ^ 2 / (2 * l1S p)) ^ (-p.alpha - 1 / 2))))
  ∧ (∀ p : Parameters, predictiveLaw p = volume.withDensity (fun z => ENNReal.ofReal
      (l1StudentDensity (2 * p.alpha) p.gamma (l1S p / p.alpha) z)))
  ∧ (∀ p q : Parameters, predictiveLaw p = predictiveLaw q ↔
      (p.gamma = q.gamma ∧ p.alpha = q.alpha ∧ l1S p = l1S q))
  ∧ (∀ p : Parameters, ∀ g a s : ℝ, 0 < a → 0 < s →
      ((p.gamma = g ∧ p.alpha = a ∧ l1S p = s) ↔ p ∈ l1Fiber g a s))
  ∧ (∀ g a s : ℝ, 0 < a → 0 < s → ∀ p ∈ l1Fiber g a s, ∃! t : ℝ, 0 < t ∧ p.nu = 1 / t)
  ∧ (∀ {Y : Type} (L : Measure ℝ → Y → EReal) (y : Y) (p q : Parameters),
      (p.gamma = q.gamma ∧ p.alpha = q.alpha ∧ l1S p = l1S q) → L (predictiveLaw p) y = L (predictiveLaw q) y)
  ∧ (∀ p q : Parameters, predictiveLaw p = predictiveLaw q → (p.gamma = q.gamma ∧ p.alpha = q.alpha ∧ l1S p = l1S q))
  ∧ (∃ L : Measure ℝ → Unit → EReal, ∃ p q : Parameters,
      ¬ (p.gamma = q.gamma ∧ p.alpha = q.alpha ∧ l1S p = l1S q) ∧ L (predictiveLaw p) () = L (predictiveLaw q) ())

def B2_theorem1 : Prop :=
  (∀ p : Parameters, predictiveLaw p = volume.withDensity (fun z => ENNReal.ofReal
      (Real.Gamma (p.alpha + 1 / 2)
          / (Real.Gamma p.alpha * Real.sqrt (2 * Real.pi * quotientScale p))
        * (1 + (z - p.gamma) ^ 2 / (2 * quotientScale p)) ^ (-p.alpha - 1 / 2))))
  ∧ (∀ p : Parameters, predictiveLaw p = studentTMeasure (2 * p.alpha) p.gamma (studentScaleSquared p))
  ∧ (∀ p q : Parameters, predictiveLaw p = predictiveLaw q ↔ quotientCoordinates p = quotientCoordinates q)
  ∧ (∀ {Y : Type} (L : ReconstructionLoss Y) (y : Y) {x : QuotientState} {p q : Parameters},
      p ∈ coordinateFiber x → q ∈ coordinateFiber x → L (predictiveLaw p) y = L (predictiveLaw q) y)
  ∧ (∀ (x : QuotientState) (t : PositiveReal), quotientCoordinates (fiberParameters x t) = x)
  ∧ (∀ p : Parameters, fiberParameters (quotientCoordinates p) (fiberCoordinate p) = p)

lemma qc_eq_iff (p q : Parameters) :
    quotientCoordinates p = quotientCoordinates q ↔
      (p.gamma = q.gamma ∧ p.alpha = q.alpha ∧ l1S p = l1S q) := by
  constructor
  · intro h
    exact ⟨congrArg QuotientState.gamma h, congrArg QuotientState.alpha h, congrArg QuotientState.s h⟩
  · rintro ⟨h1, h2, h3⟩
    unfold quotientCoordinates
    congr 1

lemma l1Fiber_of (p : Parameters) (g a s : ℝ) (ha : 0 < a) (hs : 0 < s)
    (hfib : ∀ (x : QuotientState) (t : PositiveReal), quotientCoordinates (fiberParameters x t) = x)
    (hsec : ∀ p : Parameters, fiberParameters (quotientCoordinates p) (fiberCoordinate p) = p) :
    ((p.gamma = g ∧ p.alpha = a ∧ l1S p = s) ↔ p ∈ l1Fiber g a s) := by
  constructor
  · rintro ⟨hg, ha', hs'⟩
    refine ⟨1 / p.nu, one_div_pos.mpr p.nu_pos, hg, by rw [one_div_one_div], ha', ?_⟩
    have h := congrArg Parameters.beta (hsec p)
    simp only [fiberParameters, fiberCoordinate] at h
    rw [← hs']
    exact h.symm
  · rintro ⟨t, ht, hg, hn, ha', hb⟩
    have hx := hfib ⟨g, a, s, ha, hs⟩ ⟨t, ht⟩
    have hp : p = fiberParameters ⟨g, a, s, ha, hs⟩ ⟨t, ht⟩ := by
      obtain ⟨g', n', a', b', hn0, ha0, hb0⟩ := p
      simp only at hg hn ha' hb
      subst hg hn ha' hb
      rfl
    subst hp
    exact ⟨congrArg QuotientState.gamma hx, congrArg QuotientState.alpha hx, congrArg QuotientState.s hx⟩

theorem rel_theorem1 : B2_theorem1 → L1_theorem1 := by
  rintro ⟨hdens, hst, hiff, hrec, hfib, hsec⟩
  refine ⟨hdens, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [hst p]
    rfl
  · intro p q
    rw [hiff p q, qc_eq_iff]
  · intro p g a s ha hs
    exact l1Fiber_of p g a s ha hs hfib hsec
  · rintro g a s - - p ⟨t, ht, -, hn, -, -⟩
    refine ⟨t, ⟨ht, hn⟩, ?_⟩
    rintro t' ⟨ht', hn'⟩
    have h := hn'.symm.trans hn
    rw [one_div, one_div, inv_inj] at h
    exact h
  · intro Y L y p q hpq
    exact hrec L y (x := quotientCoordinates q) (p := p) (q := q) ((qc_eq_iff p q).mpr hpq) rfl
  · intro p q h
    exact (qc_eq_iff p q).mp ((hiff p q).mp h)
  · refine ⟨fun _ _ => 0, ⟨0, 1, 1, 1, one_pos, one_pos, one_pos⟩, ⟨1, 1, 1, 1, one_pos, one_pos, one_pos⟩,
      ?_, rfl⟩
    rintro ⟨h, -, -⟩
    norm_num at h

#relation_audit rel_theorem1 [NIGBottleneck.predictiveLaw_eq_quotientLaw, NIGBottleneck.predictiveLaw_density,
  NIGBottleneck.predictiveLaw_eq_studentT, NIGBottleneck.predictiveLaw_eq_iff, NIGBottleneck.quotientLaw_injective,
  NIGBottleneck.reconstruction_const_on_fiber, NIGBottleneck.exists_reconstruction_not_identifying,
  NIGBottleneck.quotientCoordinates_fiberParameters, NIGBottleneck.fiberParameters_quotientCoordinates]

theorem B2_theorem1_holds : B2_theorem1 :=
  ⟨predictiveLaw_density, predictiveLaw_eq_studentT, predictiveLaw_eq_iff,
    fun L y _ _ _ hp hq => reconstruction_const_on_fiber L y hp hq,
    quotientCoordinates_fiberParameters, fiberParameters_quotientCoordinates⟩

theorem L1_theorem1_holds : L1_theorem1 := rel_theorem1 B2_theorem1_holds

/-! ## proposition-1

L1_form: for every admissible triple, the mixture IG(α,s) ⋆ N(γ,V) (Mathlib `bind` with `gaussianReal`) equals
the predictive law of every quadruple with that triple. The map from triples to these laws is injective. -/

def l1Mixture (g a s : ℝ) : Measure ℝ :=
  (l1IGLaw a s).bind (fun v => gaussianReal g v.toNNReal)

def L1_prop1 : Prop :=
  (∀ p : Parameters, predictiveLaw p = l1Mixture p.gamma p.alpha (l1S p))
  ∧ (∀ x y : QuotientState, l1Mixture x.gamma x.alpha x.s = l1Mixture y.gamma y.alpha y.s → x = y)

def B2_prop1 : Prop :=
  (∀ p : Parameters, predictiveLaw p = nonredundantLaw (quotientCoordinates p))
  ∧ Function.Injective nonredundantLaw

theorem rel_prop1 : B2_prop1 ↔ L1_prop1 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun p => h1 p, fun x y h => h2 h⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p => h1 p, fun x y h => h2 x y h⟩

#relation_audit rel_prop1 [NIGBottleneck.nonredundantLaw_eq_quotientLaw, NIGBottleneck.predictiveLaw_eq_nonredundantLaw,
  NIGBottleneck.nonredundantLaw_injective, NIGBottleneck.nonredundantLaw_uses_exactly_triple,
  NIGBottleneck.nonredundantJointLaw_map_snd]

theorem B2_prop1_holds : B2_prop1 := ⟨predictiveLaw_eq_nonredundantLaw, nonredundantLaw_injective⟩

theorem L1_prop1_holds : L1_prop1 := rel_prop1.mp B2_prop1_holds

/-! ## proposition-2

L1:  (A=α₀, n=ν₀, δ=γ−γ₀.)

L1_form: KL is Mathlib `klDiv` of the NIG laws, ψ is L1's literal ψ, and both closed forms are written
literally. "Finite" is `klDiv ≠ ⊤`. -/

def l1K (p p₀ : Parameters) : ℝ :=
  p₀.alpha * Real.log (p.beta / p₀.beta) + Real.log (Real.Gamma p₀.alpha / Real.Gamma p.alpha)
    + (p.alpha - p₀.alpha) * l1Psi p.alpha - p.alpha + p.alpha * p₀.beta / p.beta
    + 1 / 2 * (p₀.nu / p.nu - 1 + Real.log (p.nu / p₀.nu) + p₀.nu * p.alpha * (p.gamma - p₀.gamma) ^ 2 / p.beta)

def l1F (p₀ : Parameters) (g a s t : ℝ) : ℝ :=
  p₀.alpha * Real.log (s / p₀.beta) + Real.log (Real.Gamma p₀.alpha / Real.Gamma a)
    + (a - p₀.alpha) * l1Psi a - a - p₀.alpha * Real.log (1 + t)
    + a * (p₀.beta + p₀.nu / 2 * (g - p₀.gamma) ^ 2) / s * (1 + t)
    + 1 / 2 * (p₀.nu * t - 1 - Real.log (p₀.nu * t))

def L1_prop2 : Prop :=
  (∀ p p₀ : Parameters, klDiv (nigLaw p) (nigLaw p₀) ≠ ⊤ ∧ (klDiv (nigLaw p) (nigLaw p₀)).toReal = l1K p p₀)
  ∧ (∀ p₀ : Parameters, ∀ g : ℝ, 0 < p₀.beta + p₀.nu / 2 * (g - p₀.gamma) ^ 2)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : PositiveReal),
      (klDiv (nigLaw (fiberParameters x t)) (nigLaw p₀)).toReal = l1F p₀ x.gamma x.alpha x.s t)

def B2_prop2 : Prop :=
  (∀ p p₀ : Parameters, hierarchicalKL p p₀ = nigKLClosedForm p p₀)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : PositiveReal), fiberKL p₀ x t = fiberKLFormula p₀ x t)

/-- Permitted foundational facts (not proposition-2 targets): the M22/M07 identification of the KL integral with
Mathlib's `klDiv` (`klDiv_nigLaw`, `hierarchicalKL_eq_toReal_klDiv`). -/
def Found_prop2 : Prop :=
  (∀ p p₀ : Parameters, klDiv (nigLaw p) (nigLaw p₀) = ENNReal.ofReal (hierarchicalKL p p₀))
  ∧ (∀ p p₀ : Parameters, hierarchicalKL p p₀ = (klDiv (nigLaw p) (nigLaw p₀)).toReal)

theorem rel_prop2 : Found_prop2 → (B2_prop2 ↔ L1_prop2) := by
  rintro ⟨hF, hT⟩
  have hB : ∀ p₀ : Parameters, ∀ g : ℝ, 0 < p₀.beta + p₀.nu / 2 * (g - p₀.gamma) ^ 2 := by
    intro p₀ g
    have := p₀.beta_pos
    have := p₀.nu_pos
    positivity
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p p₀ => ⟨by rw [hF]; exact ENNReal.ofReal_ne_top, by rw [← hT, h1]; rfl⟩, hB, ?_⟩
    intro p₀ x t
    rw [← hT]
    exact h2 p₀ x t
  · rintro ⟨h1, -, h3⟩
    refine ⟨fun p p₀ => ?_, fun p₀ x t => ?_⟩
    · rw [hT]; exact (h1 p p₀).2
    · unfold fiberKL; rw [hT]; exact h3 p₀ x t

#relation_audit rel_prop2 [NIGBottleneck.integrable_nigLogRatio, NIGBottleneck.hierarchicalKL_eq_closedForm,
  NIGBottleneck.fiberKL_eq]

theorem B2_prop2_holds : B2_prop2 := ⟨fun p p₀ => hierarchicalKL_eq_closedForm p p₀, fiberKL_eq⟩

theorem Found_prop2_holds : Found_prop2 := ⟨klDiv_nigLaw, hierarchicalKL_eq_toReal_klDiv⟩

theorem L1_prop2_holds : L1_prop2 := (rel_prop2 Found_prop2_holds).mp B2_prop2_holds

end PostHocFidelity
