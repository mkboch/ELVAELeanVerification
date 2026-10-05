import Mathlib
import Official.M02

/-!
# Predictive density, identifiable quotient, and fiber coordinates

Scale coordinates, the quotient state and its fiber chart, inverse-gamma rescaling, the
Student-t and inverse-gamma mixture machinery, and the marginal law of `z` with its
identifiability and fiber invariance.
-/

noncomputable section

namespace NIGBottleneck

/-- The scale coordinate `s = β (1 + 1 / ν)`. -/
def quotientScale (p : Parameters) : ℝ :=
  p.beta * (1 + 1 / p.nu)

/-- The squared Student scale coordinate `w = s / α`. -/
def studentScaleSquared (p : Parameters) : ℝ :=
  quotientScale p / p.alpha

/-- The variance inflation factor is positive. -/
theorem varianceInflation_pos (p : Parameters) :
    0 < 1 + 1 / p.nu :=
  add_pos zero_lt_one (one_div_pos.mpr p.nu_pos)

/-- The scale coordinate `s` is positive. -/
theorem quotientScale_pos (p : Parameters) :
    0 < quotientScale p :=
  mul_pos p.beta_pos (varianceInflation_pos p)

/-- The squared Student scale coordinate `w` is positive. -/
theorem studentScaleSquared_pos (p : Parameters) :
    0 < studentScaleSquared p :=
  div_pos (quotientScale_pos p) p.alpha_pos

/-- The coordinate domain `ℝ × (0,∞) × (0,∞)`. -/
@[ext]
structure QuotientState where
  gamma : ℝ
  alpha : ℝ
  s : ℝ
  alpha_pos : 0 < alpha
  s_pos : 0 < s

/-- The triple of scale coordinates associated to a hierarchy. -/
def quotientCoordinates (p : Parameters) : QuotientState where
  gamma := p.gamma
  alpha := p.alpha
  s := quotientScale p
  alpha_pos := p.alpha_pos
  s_pos := quotientScale_pos p

/-- The positive coordinate `t = 1 / ν`. -/
def fiberCoordinate (p : Parameters) : PositiveReal :=
  ⟨1 / p.nu, one_div_pos.mpr p.nu_pos⟩

/-- Parameters on the coordinate fiber, expressed in terms of `t`. -/
def fiberParameters (x : QuotientState) (t : PositiveReal) : Parameters where
  gamma := x.gamma
  nu := 1 / (t : ℝ)
  alpha := x.alpha
  beta := x.s / (1 + (t : ℝ))
  nu_pos := one_div_pos.mpr t.property
  alpha_pos := x.alpha_pos
  beta_pos := div_pos x.s_pos (add_pos zero_lt_one t.property)

/-- The level set of the triple of scale coordinates. -/
def coordinateFiber (x : QuotientState) : Set Parameters :=
  {p | quotientCoordinates p = x}

/-- Equality of parameter records follows from equality of their four coordinates. -/
private theorem parameters_ext_for_chart {p q : Parameters}
    (hgamma : p.gamma = q.gamma) (hnu : p.nu = q.nu)
    (halpha : p.alpha = q.alpha) (hbeta : p.beta = q.beta) :
    p = q := by
  cases p
  cases q
  cases hgamma
  cases hnu
  cases halpha
  cases hbeta
  rfl

/-- Equality of coordinate triples is precisely equality of
`γ`, `α`, and `β (1 + 1 / ν)`. -/
theorem quotientCoordinates_eq_iff (p q : Parameters) :
    quotientCoordinates p = quotientCoordinates q ↔
      p.gamma = q.gamma ∧
      p.alpha = q.alpha ∧
      p.beta * (1 + 1 / p.nu) = q.beta * (1 + 1 / q.nu) := by
  constructor
  · intro h
    exact ⟨congrArg QuotientState.gamma h,
      congrArg QuotientState.alpha h, congrArg QuotientState.s h⟩
  · rintro ⟨hgamma, halpha, hs⟩
    exact QuotientState.ext hgamma halpha hs

/-- Every parameter record in the displayed fiber
parameterization has the prescribed triple. -/
theorem quotientCoordinates_fiberParameters
    (x : QuotientState) (t : PositiveReal) :
    quotientCoordinates (fiberParameters x t) = x := by
  apply QuotientState.ext
  · rfl
  · rfl
  · change
      (x.s / (1 + (t : ℝ))) * (1 + 1 / (1 / (t : ℝ))) = x.s
    have hden : 1 + (t : ℝ) ≠ 0 :=
      ne_of_gt (add_pos zero_lt_one t.property)
    simp only [one_div, inv_inv]
    exact div_mul_cancel₀ x.s hden

/-- The fiber parameterization recovers its positive coordinate. -/
theorem fiberCoordinate_fiberParameters
    (x : QuotientState) (t : PositiveReal) :
    fiberCoordinate (fiberParameters x t) = t := by
  apply Subtype.ext
  change 1 / (1 / (t : ℝ)) = (t : ℝ)
  simp only [one_div, inv_inv]

/-- The triple and the reciprocal of `ν` recover the
original admissible parameter quadruple. -/
theorem fiberParameters_quotientCoordinates (p : Parameters) :
    fiberParameters (quotientCoordinates p) (fiberCoordinate p) = p := by
  apply parameters_ext_for_chart
  · rfl
  · change 1 / (1 / p.nu) = p.nu
    simp only [one_div, inv_inv]
  · rfl
  · change
      (p.beta * (1 + 1 / p.nu)) / (1 + 1 / p.nu) = p.beta
    exact mul_div_cancel_right₀ p.beta (ne_of_gt (varianceInflation_pos p))

/-- All triples in the stated coordinate domain occur. -/
theorem quotientCoordinates_surjective :
    Function.Surjective quotientCoordinates := by
  intro x
  refine ⟨fiberParameters x ⟨1, zero_lt_one⟩, ?_⟩
  exact quotientCoordinates_fiberParameters x ⟨1, zero_lt_one⟩

/-- Membership in a coordinate fiber is equivalent to
the displayed positive-parameter representation. -/
theorem mem_coordinateFiber_iff (x : QuotientState) (p : Parameters) :
    p ∈ coordinateFiber x ↔
      ∃ t : PositiveReal, fiberParameters x t = p := by
  constructor
  · intro hp
    have hx : quotientCoordinates p = x := hp
    refine ⟨fiberCoordinate p, ?_⟩
    rw [← hx]
    exact fiberParameters_quotientCoordinates p
  · rintro ⟨t, rfl⟩
    exact quotientCoordinates_fiberParameters x t

/-- The coordinate fiber is exactly the range of
`(γ, 1/t, α, s/(1+t))` for positive `t`. -/
theorem coordinateFiber_eq_range (x : QuotientState) :
    coordinateFiber x = Set.range (fiberParameters x) := by
  apply Set.ext
  intro p
  exact mem_coordinateFiber_iff x p

/-- Different positive fiber coordinates give different
admissible parameter quadruples. -/
theorem fiberParameters_injective (x : QuotientState) :
    Function.Injective (fiberParameters x) := by
  intro t u h
  have hc := congrArg fiberCoordinate h
  simpa only [fiberCoordinate_fiberParameters] using hc

/-- Each point of a coordinate fiber has a unique positive
fiber coordinate. -/
theorem coordinateFiber_existsUnique (x : QuotientState) (p : Parameters)
    (hp : p ∈ coordinateFiber x) :
    ∃! t : PositiveReal, fiberParameters x t = p := by
  have hx : quotientCoordinates p = x := hp
  refine ⟨fiberCoordinate p, ?_, ?_⟩
  · rw [← hx]
    exact fiberParameters_quotientCoordinates p
  · intro t ht
    have hc := congrArg fiberCoordinate ht
    simpa only [fiberCoordinate_fiberParameters] using hc

/-- The coordinate triple together with `t = 1/ν`
is a complete global coordinate system for the parameter quadruple. -/
theorem parameters_eq_iff_chart (p q : Parameters) :
    p = q ↔
      quotientCoordinates p = quotientCoordinates q ∧
      fiberCoordinate p = fiberCoordinate q := by
  constructor
  · intro h
    subst q
    exact ⟨rfl, rfl⟩
  · rintro ⟨hx, ht⟩
    calc
      p = fiberParameters (quotientCoordinates p) (fiberCoordinate p) :=
        (fiberParameters_quotientCoordinates p).symm
      _ = fiberParameters (quotientCoordinates q) (fiberCoordinate q) := by
        rw [hx, ht]
      _ = q := fiberParameters_quotientCoordinates q

/-- The global chart consisting of a coordinate triple
and one positive fiber coordinate. -/
def parameterCoordinatesEquiv : Parameters ≃ QuotientState × PositiveReal where
  toFun p := (quotientCoordinates p, fiberCoordinate p)
  invFun u := fiberParameters u.1 u.2
  left_inv := fiberParameters_quotientCoordinates
  right_inv u := by
    rcases u with ⟨x, t⟩
    change
      (quotientCoordinates (fiberParameters x t),
        fiberCoordinate (fiberParameters x t)) = (x, t)
    rw [quotientCoordinates_fiberParameters, fiberCoordinate_fiberParameters]

/-- The squared Student scale coordinate is fixed along
each coordinate fiber and equals `s/α`. -/
theorem studentScaleSquared_fiberParameters
    (x : QuotientState) (t : PositiveReal) :
    studentScaleSquared (fiberParameters x t) = x.s / x.alpha := by
  have hs := congrArg QuotientState.s (quotientCoordinates_fiberParameters x t)
  change quotientScale (fiberParameters x t) = x.s at hs
  change quotientScale (fiberParameters x t) / x.alpha = x.s / x.alpha
  rw [hs]

/-- Rescaling the hierarchy's inverse-gamma variance by
`1 + 1/ν` gives inverse-gamma shape `α` and scale `s`. -/
theorem varianceLaw_scale_to_quotient (p : Parameters) :
    MeasureTheory.Measure.map
        (fun v : ℝ => (1 + 1 / p.nu) * v) (varianceLaw p) =
      inverseGammaLaw ⟨p.alpha, p.alpha_pos⟩
        ⟨quotientScale p, quotientScale_pos p⟩ := by
  have h :=
    inverseGammaLaw_scale
      (⟨p.alpha, p.alpha_pos⟩ : PositiveReal)
      (⟨p.beta, p.beta_pos⟩ : PositiveReal)
      (⟨1 + 1 / p.nu, varianceInflation_pos p⟩ : PositiveReal)
  simpa only [varianceLaw, quotientScale, mul_comm] using h

/-- The coefficient appearing in the displayed density expression. -/
private def densityPrefactor (x : QuotientState) : ℝ :=
  Real.Gamma (x.alpha + 1 / 2) /
    (Real.Gamma x.alpha * Real.sqrt (2 * Real.pi * x.s))

/-- Positivity of the coefficient in the displayed density expression. -/
private theorem densityPrefactor_pos (x : QuotientState) :
    0 < densityPrefactor x := by
  have hs := x.s_pos
  unfold densityPrefactor
  apply div_pos
  · exact Real.Gamma_pos_of_pos (by linarith [x.alpha_pos])
  · exact mul_pos (Real.Gamma_pos_of_pos x.alpha_pos)
      (Real.sqrt_pos.mpr (by positivity))

/-- Positivity of the base of the real power in the displayed density. -/
private theorem densityBase_pos (x : QuotientState) (z : ℝ) :
    0 < 1 + (z - x.gamma) ^ 2 / (2 * x.s) := by
  have hs := x.s_pos
  positivity

/-- The expression on the right-hand side of the
predictive-density equation. This notation does not redefine `predictiveLaw`. -/
def displayedPredictiveDensity (x : QuotientState) (z : ℝ) : ℝ :=
  densityPrefactor x *
    (1 + (z - x.gamma) ^ 2 / (2 * x.s)) ^ (-x.alpha - 1 / 2)

/-- The displayed density expression is strictly positive. -/
theorem displayedPredictiveDensity_pos (x : QuotientState) (z : ℝ) :
    0 < displayedPredictiveDensity x z :=
  mul_pos (densityPrefactor_pos x)
    (Real.rpow_pos_of_pos (densityBase_pos x z) _)

/-- The displayed density expression has a strict maximum
at its location parameter. -/
theorem displayedPredictiveDensity_lt_mode (x : QuotientState) (z : ℝ)
    (hz : z ≠ x.gamma) :
    displayedPredictiveDensity x z <
      displayedPredictiveDensity x x.gamma := by
  have hsq : 0 < (z - x.gamma) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hz)
  have hdiv : 0 < (z - x.gamma) ^ 2 / (2 * x.s) :=
    div_pos hsq (mul_pos (by norm_num) x.s_pos)
  have hbase : 1 < 1 + (z - x.gamma) ^ 2 / (2 * x.s) := by
    linarith
  have hexponent : -x.alpha - (1 / 2 : ℝ) < 0 := by
    linarith [x.alpha_pos]
  have hpow :
      (1 + (z - x.gamma) ^ 2 / (2 * x.s)) ^ (-x.alpha - 1 / 2) < 1 := by
    rw [Real.rpow_def_of_pos (densityBase_pos x z)]
    exact Real.exp_lt_one_iff.mpr
      (mul_neg_of_pos_of_neg (Real.log_pos hbase) hexponent)
  calc
    displayedPredictiveDensity x z =
        densityPrefactor x *
          (1 + (z - x.gamma) ^ 2 / (2 * x.s)) ^ (-x.alpha - 1 / 2) := rfl
    _ < densityPrefactor x * 1 :=
      mul_lt_mul_of_pos_left hpow (densityPrefactor_pos x)
    _ = displayedPredictiveDensity x x.gamma := by
      simp [displayedPredictiveDensity]

/-- The maximum of the displayed density expression is unique. -/
theorem displayedPredictiveDensity_eq_mode_iff (x : QuotientState) (z : ℝ) :
    displayedPredictiveDensity x z = displayedPredictiveDensity x x.gamma ↔
      z = x.gamma := by
  constructor
  · intro h
    by_contra hz
    exact (ne_of_lt (displayedPredictiveDensity_lt_mode x z hz)) h
  · intro h
    subst z
    rfl

/-- Expansion of the logarithm of the displayed density expression. -/
private theorem log_displayedPredictiveDensity (x : QuotientState) (z : ℝ) :
    Real.log (displayedPredictiveDensity x z) =
      Real.log (densityPrefactor x) +
        (-x.alpha - 1 / 2) *
          Real.log (1 + (z - x.gamma) ^ 2 / (2 * x.s)) := by
  unfold displayedPredictiveDensity
  rw [Real.log_mul (ne_of_gt (densityPrefactor_pos x))
    (ne_of_gt (Real.rpow_pos_of_pos (densityBase_pos x z) _)),
    Real.log_rpow (densityBase_pos x z)]

/-- The logarithmic derivative of the displayed density expression. -/
private theorem hasDerivAt_log_displayedPredictiveDensity
    (x : QuotientState) (z : ℝ) :
    HasDerivAt (fun u : ℝ => Real.log (displayedPredictiveDensity x u))
      (-((2 * x.alpha + 1) * (z - x.gamma)) /
        (2 * x.s + (z - x.gamma) ^ 2)) z := by
  have hbase :
      HasDerivAt (fun u : ℝ => 1 + (u - x.gamma) ^ 2 / (2 * x.s))
        ((2 * (z - x.gamma)) / (2 * x.s)) z := by
    convert ((((hasDerivAt_id z).sub_const x.gamma).pow 2).div_const
      (2 * x.s)).const_add 1 using 1 <;> (dsimp; try ring)
  have haux :=
    ((hbase.log (ne_of_gt (densityBase_pos x z))).const_mul
      (-x.alpha - 1 / 2)).const_add (Real.log (densityPrefactor x))
  have hfun :
      (fun u : ℝ => Real.log (displayedPredictiveDensity x u)) =
        (fun u : ℝ => Real.log (densityPrefactor x) +
          (-x.alpha - 1 / 2) *
            Real.log (1 + (u - x.gamma) ^ 2 / (2 * x.s))) :=
    funext (log_displayedPredictiveDensity x)
  have hs0 : x.s ≠ 0 := ne_of_gt x.s_pos
  have hd0 : 2 * x.s + (z - x.gamma) ^ 2 ≠ 0 :=
    ne_of_gt (by nlinarith [x.s_pos, sq_nonneg (z - x.gamma)])
  have hb0 : 1 + (z - x.gamma) ^ 2 / (2 * x.s) ≠ 0 :=
    ne_of_gt (densityBase_pos x z)
  rw [hfun]
  convert haux using 1
  field_simp [hs0, hd0, hb0]
  ring

/-- Distinct coordinate triples give distinct displayed
density functions. The proof uses the unique mode and logarithmic derivatives. -/
theorem displayedPredictiveDensity_injective :
    Function.Injective displayedPredictiveDensity := by
  intro x y h
  have hgamma : x.gamma = y.gamma := by
    by_contra hne
    have hxy := displayedPredictiveDensity_lt_mode y x.gamma hne
    have hyx := displayedPredictiveDensity_lt_mode x y.gamma (Ne.symm hne)
    rw [h] at hyx
    exact lt_asymm hxy hyx
  have hderiv (z : ℝ) :
      -((2 * x.alpha + 1) * (z - x.gamma)) /
          (2 * x.s + (z - x.gamma) ^ 2) =
        -((2 * y.alpha + 1) * (z - y.gamma)) /
          (2 * y.s + (z - y.gamma) ^ 2) := by
    have hy := hasDerivAt_log_displayedPredictiveDensity y z
    rw [← h] at hy
    exact (hasDerivAt_log_displayedPredictiveDensity x z).unique hy
  have h1 := hderiv (x.gamma + 1)
  have h2 := hderiv (x.gamma + 2)
  simp only [← hgamma] at h1 h2
  have hshift1 : x.gamma + 1 - x.gamma = (1 : ℝ) := by ring
  have hshift2 : x.gamma + 2 - x.gamma = (2 : ℝ) := by ring
  simp only [hshift1, one_pow, mul_one] at h1
  simp only [hshift2, show (2 : ℝ) ^ 2 = 4 by norm_num] at h2
  have hsx1 : 2 * x.s + 1 ≠ 0 :=
    ne_of_gt (by linarith [x.s_pos])
  have hsy1 : 2 * y.s + 1 ≠ 0 :=
    ne_of_gt (by linarith [y.s_pos])
  have hsx4 : 2 * x.s + 4 ≠ 0 :=
    ne_of_gt (by linarith [x.s_pos])
  have hsy4 : 2 * y.s + 4 ≠ 0 :=
    ne_of_gt (by linarith [y.s_pos])
  have hc1 :
      (2 * x.alpha + 1) * (2 * y.s + 1) =
        (2 * y.alpha + 1) * (2 * x.s + 1) := by
    have hc := (div_eq_div_iff hsx1 hsy1).mp h1
    nlinarith [hc]
  have hc2 :
      (2 * x.alpha + 1) * (2 * y.s + 4) =
        (2 * y.alpha + 1) * (2 * x.s + 4) := by
    have hc := (div_eq_div_iff hsx4 hsy4).mp h2
    nlinarith [hc]
  have halpha : x.alpha = y.alpha := by
    nlinarith [hc1, hc2]
  have hc1' :
      (2 * x.alpha + 1) * (2 * y.s + 1) =
        (2 * x.alpha + 1) * (2 * x.s + 1) := by
    simpa only [← halpha] using hc1
  have ha0 : 2 * x.alpha + 1 ≠ 0 :=
    ne_of_gt (by linarith [x.alpha_pos])
  have he := mul_left_cancel₀ ha0 hc1'
  have hs : x.s = y.s := by
    linarith
  exact QuotientState.ext hgamma halpha hs

/-- Equality of the displayed density functions is equivalent
to equality of their three coordinates. -/
theorem displayedPredictiveDensity_eq_iff (x y : QuotientState) :
    (∀ z : ℝ, displayedPredictiveDensity x z =
      displayedPredictiveDensity y z) ↔ x = y := by
  constructor
  · intro h
    exact displayedPredictiveDensity_injective (funext h)
  · rintro rfl
    intro z
    rfl

/-- For parameter quadruples, the displayed density functions
agree exactly when `γ`, `α`, and `s` agree. -/
theorem displayedPredictiveDensity_parameters_eq_iff (p q : Parameters) :
    (∀ z : ℝ, displayedPredictiveDensity (quotientCoordinates p) z =
      displayedPredictiveDensity (quotientCoordinates q) z) ↔
      p.gamma = q.gamma ∧
      p.alpha = q.alpha ∧
      p.beta * (1 + 1 / p.nu) = q.beta * (1 + 1 / q.nu) :=
  (displayedPredictiveDensity_eq_iff
    (quotientCoordinates p) (quotientCoordinates q)).trans
      (quotientCoordinates_eq_iff p q)


/-! ## Student-t law and inverse-gamma mixtures

Mathlib's
`gaussianReal`, `gammaMeasure`, `Measure.bind` and convolution are used unchanged. -/

section StudentT

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

/-- Student-t density: `n` degrees of freedom, location `m`, squared scale `s2`. -/
def studentTPDFReal (n m s2 y : ℝ) : ℝ :=
  Real.Gamma ((n + 1) / 2) / (Real.Gamma (n / 2) * Real.sqrt (n * π * s2))
    * (1 + (y - m) ^ 2 / (n * s2)) ^ (-((n + 1) / 2))

/-- Pointwise form of the mixture integrand on τ > 0. -/
lemma mixture_integrand_eq (a b k m y t : ℝ) (ha : 0 < a) (hk : 0 < k) (ht : 0 < t) :
    gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y
      = (b ^ a / (Real.Gamma a * Real.sqrt (2 * π * k)))
          * (t ^ ((a + 1 / 2) - 1) * Real.exp (-((b + (y - m) ^ 2 / (2 * k)) * t))) := by
  have hkt : 0 ≤ k / t := by positivity
  simp only [gammaPDFReal, ht.le, ↓reduceIte]
  rw [gaussianPDFReal, Real.coe_toNNReal _ hkt]
  have hsq : Real.sqrt (2 * π * (k / t)) = Real.sqrt (2 * π * k) / Real.sqrt t := by
    rw [← Real.sqrt_div' _ ht.le]; congr 1; ring
  have hpow : t ^ ((a + 1 / 2) - 1) = t ^ (a - 1) * Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]; congr 1; ring
  have hexp : Real.exp (-(b * t)) * Real.exp (-(y - m) ^ 2 / (2 * (k / t)))
      = Real.exp (-((b + (y - m) ^ 2 / (2 * k)) * t)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [hsq, hpow, ← hexp]
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 : 0 < Real.sqrt (2 * π * k) := Real.sqrt_pos.mpr (by positivity)
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  field_simp

/-- The inverse-gamma/Gamma mixture integral of a Gaussian density is the Student-t density. -/
theorem mixture_integral (a b k m y : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    ∫ t in Ioi 0, gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y
      = studentTPDFReal (2 * a) m (k * b / a) y := by
  set u : ℝ := (y - m) ^ 2 / (2 * k * b) with hu
  have hu0 : 0 ≤ u := by positivity
  have hr : b + (y - m) ^ 2 / (2 * k) = b * (1 + u) := by
    rw [hu]; field_simp
  have hrpos : 0 < b + (y - m) ^ 2 / (2 * k) := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => mixture_integrand_eq a b k m y t ha hk ht),
    integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hrpos, hr]
  have h1u : 0 < 1 + u := by linarith
  unfold studentTPDFReal
  have e1 : (2 * a + 1) / 2 = a + 1 / 2 := by ring
  have e2 : 2 * a / 2 = a := by ring
  have e3 : 2 * a * π * (k * b / a) = (2 * π * k) * b := by field_simp
  have e4 : (y - m) ^ 2 / (2 * a * (k * b / a)) = u := by rw [hu]; field_simp
  rw [e1, e2, e3, e4, Real.sqrt_mul (by positivity), one_div, Real.inv_rpow (by positivity),
    Real.mul_rpow hb.le h1u.le, Real.rpow_neg h1u.le]
  have hbp : b ^ (a + 1 / 2) = b ^ a * Real.sqrt b := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb]
  rw [hbp]
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hs2 : 0 < Real.sqrt (2 * π * k) := Real.sqrt_pos.mpr (by positivity)
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hba : 0 < b ^ a := Real.rpow_pos_of_pos hb a
  have hup : 0 < (1 + u) ^ (a + 1 / 2) := Real.rpow_pos_of_pos h1u _
  field_simp
  rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * π * k),
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * π)]

/-- The Student-t density is positive for positive degrees of freedom and squared scale. -/
lemma studentTPDFReal_pos (n m s2 y : ℝ) (hn : 0 < n) (hs : 0 < s2) :
    0 < studentTPDFReal n m s2 y := by
  unfold studentTPDFReal
  have h1 : 0 < Real.Gamma ((n + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : 0 < Real.Gamma (n / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h3 : 0 < Real.sqrt (n * π * s2) := Real.sqrt_pos.mpr (by positivity)
  have h4 : 0 < (1 + (y - m) ^ 2 / (n * s2)) ^ (-((n + 1) / 2)) :=
    Real.rpow_pos_of_pos (by positivity) _
  positivity

/-- Lower-integral form of `mixture_integral`. -/
lemma mixture_lintegral (a b k m y : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    ∫⁻ t, gammaPDF a b t * gaussianPDF m (k / t).toNNReal y
      = ENNReal.ofReal (studentTPDFReal (2 * a) m (k * b / a) y) := by
  have hf : (fun t => gammaPDF a b t * gaussianPDF m (k / t).toNNReal y)
      = fun t => ENNReal.ofReal (gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y) := by
    funext t
    rw [gammaPDF, gaussianPDF, ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hb t)]
  rw [hf, ← lintegral_add_compl _ (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))),
    Set.compl_Ioi]
  have hzero : ∫⁻ t in Iic 0,
      ENNReal.ofReal (gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y) = 0 := by
    rw [← setLIntegral_congr Iio_ae_eq_Iic]
    rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
      (fun t (ht : t < 0) => by simp [gammaPDFReal, not_le.mpr ht])]
    simp
  rw [hzero, add_zero]
  have hint_val := mixture_integral a b k m y ha hb hk
  have hpos := studentTPDFReal_pos (2 * a) m (k * b / a) y (by positivity) (by positivity)
  have hint : Integrable
      (fun t => gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y)
      (volume.restrict (Ioi 0)) :=
    Integrable.of_integral_ne_zero (by rw [hint_val]; exact hpos.ne')
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun t => mul_nonneg (gammaPDFReal_nonneg ha hb t)
      (gaussianPDFReal_nonneg _ _ _)), hint_val]

/-- Student-t law: `n` degrees of freedom, location `m`, squared scale `s2`. -/
def studentTMeasure (n m s2 : ℝ) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (studentTPDFReal n m s2 y))

lemma measurable_gaussian_kernel (m k : ℝ) :
    Measurable (fun t : ℝ => gaussianReal m (k / t).toNNReal) :=
  measurable_gaussianReal.comp
    (measurable_const.prodMk ((measurable_const.div measurable_id).real_toNNReal))

/-- A Gamma precision mixture of Gaussians is Student-t. -/
theorem gamma_mixture_gaussian_eq_studentT (a b k m : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    (gammaMeasure a b).bind (fun t => gaussianReal m (k / t).toNNReal)
      = studentTMeasure (2 * a) m (k * b / a) := by
  ext s hs
  have hmeasG : Measurable (gammaPDF a b) := (measurable_gammaPDFReal a b).ennreal_ofReal
  have hmk : Measurable (fun t : ℝ => gaussianReal m (k / t).toNNReal s) :=
    (Measure.measurable_coe hs).comp (measurable_gaussian_kernel m k)
  rw [Measure.bind_apply hs (measurable_gaussian_kernel m k).aemeasurable, studentTMeasure,
    withDensity_apply _ hs, gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hmeasG hmk]
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    have : (volume : Measure ℝ) {0} = 0 := measure_singleton 0
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with t ht
    simpa using ht
  have hstep : ∀ᵐ t ∂(volume : Measure ℝ),
      (gammaPDF a b * fun t => gaussianReal m (k / t).toNNReal s) t
        = ∫⁻ y in s, gammaPDF a b t * gaussianPDF m (k / t).toNNReal y := by
    filter_upwards [hae] with t ht
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · have h0 : gammaPDF a b t = 0 := gammaPDF_of_neg hneg
      simp [h0]
    · have hv : (k / t).toNNReal ≠ 0 := by
        rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
      simp only [Pi.mul_apply]
      rw [gaussianReal_apply _ hv, lintegral_const_mul _ (measurable_gaussianPDF _ _)]
  rw [lintegral_congr_ae hstep]
  have hmeas2 : Measurable (Function.uncurry
      (fun (t y : ℝ) => gammaPDF a b t * gaussianPDF m (k / t).toNNReal y)) := by
    refine (hmeasG.comp measurable_fst).mul ?_
    exact measurable_uncurry_gaussianPDF.comp (measurable_const.prodMk
      (((measurable_const.div measurable_fst).real_toNNReal).prodMk measurable_snd))
  rw [lintegral_lintegral_swap hmeas2.aemeasurable]
  refine lintegral_congr fun y => ?_
  exact mixture_lintegral a b k m y ha hb hk

/-- Binding a location family `x ↦ ν.map (x + ·)` is additive convolution. -/
lemma bind_map_const_add_eq_conv (μ ν : Measure ℝ) [SFinite ν]
    (hf : AEMeasurable (fun x : ℝ => ν.map (x + ·)) μ) :
    μ.bind (fun x => ν.map (x + ·)) = μ ∗ ν := by
  ext s hs
  rw [Measure.bind_apply hs hf, ← lintegral_indicator_one hs,
    Measure.lintegral_conv (measurable_one.indicator hs)]
  refine lintegral_congr fun x => ?_
  rw [Measure.map_apply (measurable_const_add x) hs,
    ← lintegral_indicator_one (measurable_const_add x hs)]
  rfl

/-- Gaussian hierarchy: `z ~ N(m, v₁)`, `y | z ~ N(z, v₂)` gives `y ~ N(m, v₁ + v₂)`. -/
theorem gaussianReal_bind_gaussianReal (m : ℝ) (v1 v2 : ℝ≥0) :
    (gaussianReal m v1).bind (fun z => gaussianReal z v2) = gaussianReal m (v1 + v2) := by
  have hk : (fun z : ℝ => gaussianReal z v2) = fun z => (gaussianReal 0 v2).map (z + ·) := by
    funext z
    rw [gaussianReal_map_const_add, zero_add]
  have hmeas : Measurable (fun z : ℝ => gaussianReal z v2) :=
    measurable_gaussianReal.comp (measurable_id.prodMk measurable_const)
  rw [hk, bind_map_const_add_eq_conv _ _ (hk ▸ hmeas.aemeasurable),
    gaussianReal_conv_gaussianReal, add_zero]

/-- Inverse-gamma law as the law of `1/τ` for `τ ~ Gamma(shape α, rate β)`. -/
def invGammaMeasure (a b : ℝ) : Measure ℝ :=
  (gammaMeasure a b).map (fun t => t⁻¹)

/-- The three-layer hierarchy written with Mathlib's Markov-kernel composition:
`σ² ~ IG(α, β)`, `μ | σ² ~ N(γ, σ²/ν)`, `z | μ, σ² ~ N(μ, σ²)`. -/
def nigZMarginal (gamma nu alpha beta : ℝ) : Measure ℝ :=
  (invGammaMeasure alpha beta).bind
    (fun s => (gaussianReal gamma (s / nu).toNNReal).bind
      (fun m => gaussianReal m s.toNNReal))

lemma bind_map_eq_bind_comp {μ : Measure ℝ} {f : ℝ → ℝ} {g : ℝ → Measure ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (g ∘ f) := by
  ext s hs
  rw [Measure.bind_apply hs hg.aemeasurable, Measure.bind_apply hs (hg.comp hf).aemeasurable,
    lintegral_map (f := fun a => g a s) ((Measure.measurable_coe hs).comp hg) hf]
  rfl

/-- The Gamma law is concentrated on `(0, ∞)`. -/
lemma gammaMeasure_ae_pos (a b : ℝ) : ∀ᵐ t ∂(gammaMeasure a b), 0 < t := by
  rw [ae_iff]
  have hset : {t : ℝ | ¬ 0 < t} = Iic 0 := by ext t; simp
  rw [hset, gammaMeasure, withDensity_apply _ measurableSet_Iic,
    ← setLIntegral_congr Iio_ae_eq_Iic]
  exact lintegral_gammaPDF_of_nonpos le_rfl

/-- The bind-form hierarchy law of `z` is Student-t with `2α` degrees of freedom, location
`γ` and squared scale `β (1 + 1/ν) / α`. -/
theorem nigZMarginal_eq_studentT (gamma nu alpha beta : ℝ)
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    nigZMarginal gamma nu alpha beta
      = studentTMeasure (2 * alpha) gamma (beta * (1 + 1 / nu) / alpha) := by
  have hinner : (fun s : ℝ => (gaussianReal gamma (s / nu).toNNReal).bind
        (fun m => gaussianReal m s.toNNReal))
      = fun s => gaussianReal gamma ((s / nu).toNNReal + s.toNNReal) := by
    funext s
    exact gaussianReal_bind_gaussianReal gamma _ _
  have hg : Measurable (fun s : ℝ => gaussianReal gamma ((s / nu).toNNReal + s.toNNReal)) :=
    measurable_gaussianReal.comp (measurable_const.prodMk
      (((measurable_id.div_const nu).real_toNNReal).add measurable_id.real_toNNReal))
  rw [nigZMarginal, hinner, invGammaMeasure, bind_map_eq_bind_comp measurable_inv hg]
  have hae : (fun s : ℝ => gaussianReal gamma ((s / nu).toNNReal + s.toNNReal)) ∘ (fun t => t⁻¹)
      =ᵐ[gammaMeasure alpha beta]
        fun t => gaussianReal gamma ((1 + 1 / nu) / t).toNNReal := by
    filter_upwards [gammaMeasure_ae_pos alpha beta] with t ht
    have h1 : 0 ≤ t⁻¹ / nu := by positivity
    have h2 : 0 ≤ t⁻¹ := by positivity
    simp only [Function.comp_apply]
    rw [← Real.toNNReal_add h1 h2]
    congr 2
    field_simp
    ring
  rw [Measure.bind_congr_right hae,
    gamma_mixture_gaussian_eq_studentT _ _ _ _ halpha hbeta (by positivity)]
  congr 1
  ring

/-- The Student-t law with positive parameters is a probability measure. -/
theorem isProbabilityMeasure_studentTMeasure (n m s2 : ℝ) (hn : 0 < n) (hs2 : 0 < s2) :
    IsProbabilityMeasure (studentTMeasure n m s2) := by
  have hn2 : 2 * (n / 2) = n := by ring
  have hmix2 := gamma_mixture_gaussian_eq_studentT (n / 2) (n / 2) s2 m
    (by positivity) (by positivity) hs2
  rw [hn2, show s2 * (n / 2) / (n / 2) = s2 by field_simp] at hmix2
  rw [← hmix2]
  have : IsProbabilityMeasure (gammaMeasure (n / 2) (n / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)
  constructor
  rw [Measure.bind_apply MeasurableSet.univ (measurable_gaussian_kernel m s2).aemeasurable]
  have h1 : ∀ t : ℝ, (gaussianReal m (s2 / t).toNNReal) Set.univ = 1 := fun t => by
    have := instIsProbabilityMeasureGaussianReal m (s2 / t).toNNReal
    exact measure_univ
  simp [h1]

/-- Restricting a gamma-density integral to the positive half-line loses nothing. -/
lemma setLIntegral_gammaPDF_inter_Ioi (a b : ℝ) (A : Set ℝ) :
    ∫⁻ t in A, gammaPDF a b t = ∫⁻ t in A ∩ Ioi 0, gammaPDF a b t := by
  rw [← lintegral_inter_add_sdiff _ A (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
  have hzero : ∫⁻ t in A \ Ioi 0, gammaPDF a b t = 0 := by
    refine le_antisymm ?_ bot_le
    calc ∫⁻ t in A \ Ioi 0, gammaPDF a b t ≤ ∫⁻ t in Iic 0, gammaPDF a b t :=
          lintegral_mono_set fun t ht => by
            simpa using ht.2
      _ = 0 := by
          rw [← setLIntegral_congr Iio_ae_eq_Iic]
          exact lintegral_gammaPDF_of_nonpos le_rfl
  rw [hzero, add_zero]

/-- The model's inverse-gamma density is measurable. -/
lemma measurable_inverseGammaDensity (a b : ℝ) : Measurable (inverseGammaDensity a b) := by
  unfold inverseGammaDensity
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  simp only [Real.rpow_eq_pow]
  fun_prop

/-- **Density bridge.** The model's inverse-gamma law (defined by its density) is the
push-forward of Mathlib's Gamma law under `τ ↦ 1/τ`. -/
theorem inverseGammaLaw_eq_invGammaMeasure (a b : PositiveReal) :
    inverseGammaLaw a b = invGammaMeasure a b := by
  have ha : 0 < (a : ℝ) := a.property
  have hmeasIG : Measurable fun x => ENNReal.ofReal (inverseGammaDensity a b x) :=
    (measurable_inverseGammaDensity _ _).ennreal_ofReal
  ext s hs
  rw [inverseGammaLaw, invGammaMeasure, Measure.map_apply measurable_inv hs, gammaMeasure,
    withDensity_apply _ (measurable_inv hs), withDensity_apply _ hs,
    setLIntegral_gammaPDF_inter_Ioi _ _ _]
  have hRHS : ∫⁻ x in s, ENNReal.ofReal (inverseGammaDensity a b x)
      = ∫⁻ x in s ∩ Ioi 0, ENNReal.ofReal (inverseGammaDensity a b x) := by
    rw [← lintegral_inter_add_sdiff _ s (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    have hzero : ∫⁻ x in s \ Ioi 0, ENNReal.ofReal (inverseGammaDensity a b x) = 0 := by
      rw [setLIntegral_congr_fun (hs.diff measurableSet_Ioi) (g := fun _ => 0)
        (fun x hx => by
          have hx2 : ¬ 0 < x := hx.2
          simp [inverseGammaDensity, hx2])]
      simp
    rw [hzero, add_zero]
  rw [hRHS]
  set S := (fun t : ℝ => t⁻¹) ⁻¹' s ∩ Ioi 0 with hS
  have hSmeas : MeasurableSet S := (measurable_inv hs).inter measurableSet_Ioi
  have himage : (fun t : ℝ => t⁻¹) '' S = s ∩ Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t, ⟨ht, (htpos : 0 < t)⟩, rfl⟩
      exact ⟨ht, inv_pos.mpr htpos⟩
    · rintro ⟨hx, (hxpos : 0 < x)⟩
      exact ⟨x⁻¹, ⟨by simpa using hx, inv_pos.mpr hxpos⟩, inv_inv x⟩
  have hderiv : ∀ t ∈ S, HasDerivWithinAt (fun t : ℝ => t⁻¹) (-(t ^ 2)⁻¹) S t :=
    fun t ht => (hasDerivAt_inv (ne_of_gt ht.2)).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => t⁻¹) S := fun a _ b _ h => inv_injective h
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul hSmeas hderiv hinj]
  refine setLIntegral_congr_fun hSmeas fun t ht => ?_
  have htpos : 0 < t := ht.2
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hgam : gammaPDFReal a b t = (b : ℝ) ^ (a : ℝ) / Real.Gamma a
      * (t ^ ((a : ℝ) - 1) * Real.exp (-((b : ℝ) * t))) := by
    simp only [gammaPDFReal, htpos.le, ↓reduceIte]
    ring
  rw [gammaPDF, hgam, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  simp only [inverseGammaDensity, inv_pos.mpr htpos, ↓reduceIte, abs_neg,
    abs_of_pos (inv_pos.mpr (pow_pos htpos 2)), Real.rpow_eq_pow, div_inv_eq_mul]
  rw [Real.inv_rpow htpos.le, ← Real.rpow_neg htpos.le, neg_sub, sub_neg_eq_add]
  have hpow : t ^ ((a : ℝ) - 1) = (t ^ 2)⁻¹ * t ^ (1 + (a : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg htpos.le, ← Real.rpow_add htpos]
    congr 1
    push_cast
    ring
  rw [hpow]
  ring

end StudentT

/-! ## The marginal law of `z`

The model defines the hierarchy by its joint density on `((μ, σ²), z)` and the marginal
law of `z` as its push-forward (`predictiveLaw`). The bridge `predictiveLaw_eq_nigZMarginal`
identifies it with the kernel form `nigZMarginal`; the Student-t machinery then gives its density.
-/

section PredictiveLaw

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

lemma inverseGammaDensity_nonneg (a b x : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ inverseGammaDensity a b x := by
  unfold inverseGammaDensity
  split_ifs with hx
  · have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
    exact mul_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg hb a) hG.le)
      (Real.rpow_nonneg hx.le _)) (Real.exp_pos _).le
  · exact le_rfl

lemma inverseGammaDensity_of_nonpos (a b x : ℝ) (hx : ¬ 0 < x) :
    inverseGammaDensity a b x = 0 := by
  simp [inverseGammaDensity, hx]

lemma normalDensity_nonneg (m v z : ℝ) : 0 ≤ normalDensity m v z :=
  mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_pos _).le

/-- The model's normal density is Mathlib's `gaussianPDFReal` for nonnegative variance. -/
lemma normalDensity_eq_gaussianPDFReal (m v z : ℝ) (hv : 0 ≤ v) :
    normalDensity m v z = gaussianPDFReal m v.toNNReal z := by
  simp only [normalDensity, gaussianPDFReal, Real.coe_toNNReal _ hv]

lemma nigDensity_nonneg (p : Parameters) (q : ℝ × ℝ) : 0 ≤ nigDensity p q :=
  mul_nonneg (inverseGammaDensity_nonneg _ _ _ p.alpha_pos p.beta_pos.le)
    (normalDensity_nonneg _ _ _)

lemma nigDensity_of_nonpos (p : Parameters) (q : ℝ × ℝ) (hq : ¬ 0 < q.2) : nigDensity p q = 0 := by
  simp [nigDensity, inverseGammaDensity_of_nonpos _ _ _ hq]

lemma measurable_nigDensity (p : Parameters) : Measurable (nigDensity p) := by
  have hIG := measurable_inverseGammaDensity p.alpha p.beta
  unfold nigDensity normalDensity
  fun_prop

lemma measurable_hierarchyDensity (p : Parameters) : Measurable (hierarchyDensity p) := by
  have hN := measurable_nigDensity p
  unfold hierarchyDensity normalDensity meanCoordinate varianceCoordinate latentCoordinate
  fun_prop

/-- Integrating out `z` over a measurable set, for fixed `(μ, σ²)`. -/
lemma lintegral_latent_indicator (p : Parameters) {s : Set ℝ} (hs : MeasurableSet s) (q : ℝ × ℝ) :
    ∫⁻ z, s.indicator (fun z => ENNReal.ofReal (hierarchyDensity p (q, z))) z
      = ENNReal.ofReal (nigDensity p q) * gaussianReal q.1 q.2.toNNReal s := by
  by_cases hq : 0 < q.2
  · have hv : q.2.toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hq
    have hfun : (fun z => ENNReal.ofReal (hierarchyDensity p (q, z)))
        = fun z => ENNReal.ofReal (nigDensity p q) * gaussianPDF q.1 q.2.toNNReal z := by
      funext z
      rw [gaussianPDF, ← ENNReal.ofReal_mul (nigDensity_nonneg p q)]
      congr 1
      simp only [hierarchyDensity, meanCoordinate, varianceCoordinate, latentCoordinate]
      rw [normalDensity_eq_gaussianPDFReal _ _ _ hq.le]
    rw [hfun, lintegral_indicator hs, lintegral_const_mul _ (measurable_gaussianPDF _ _),
      gaussianReal_apply _ hv]
  · have h0 : nigDensity p q = 0 := nigDensity_of_nonpos p q hq
    have hfun : (fun z => ENNReal.ofReal (hierarchyDensity p (q, z))) = fun _ => 0 := by
      funext z
      simp [hierarchyDensity, h0]
    simp [hfun, h0]

/-- Integrating out `μ` for fixed `σ² = x`: the Gaussian hierarchy collapses. -/
lemma lintegral_mean_layer (p : Parameters) {s : Set ℝ} (hs : MeasurableSet s) (x : ℝ) :
    ∫⁻ m, ENNReal.ofReal (nigDensity p (m, x)) * gaussianReal m x.toNNReal s
      = ENNReal.ofReal (inverseGammaDensity p.alpha p.beta x)
          * gaussianReal p.gamma ((x / p.nu).toNNReal + x.toNNReal) s := by
  by_cases hx : 0 < x
  · have hv : (x / p.nu).toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact div_pos hx p.nu_pos
    have hker : Measurable (fun m : ℝ => gaussianReal m x.toNNReal) :=
      measurable_gaussianReal.comp (measurable_id.prodMk measurable_const)
    have hmk : Measurable (fun m : ℝ => gaussianReal m x.toNNReal s) :=
      (Measure.measurable_coe hs).comp hker
    have hfun : (fun m => ENNReal.ofReal (nigDensity p (m, x)) * gaussianReal m x.toNNReal s)
        = fun m => ENNReal.ofReal (inverseGammaDensity p.alpha p.beta x)
            * (gaussianPDF p.gamma (x / p.nu).toNNReal m * gaussianReal m x.toNNReal s) := by
      funext m
      rw [← mul_assoc, gaussianPDF,
        ← ENNReal.ofReal_mul (inverseGammaDensity_nonneg _ _ _ p.alpha_pos p.beta_pos.le)]
      congr 2
      simp only [nigDensity]
      rw [normalDensity_eq_gaussianPDFReal _ _ _ (div_pos hx p.nu_pos).le]
    rw [hfun, lintegral_const_mul _
        (f := fun m => gaussianPDF p.gamma (x / p.nu).toNNReal m * gaussianReal m x.toNNReal s)
        ((measurable_gaussianPDF _ _).mul hmk),
      ← gaussianReal_bind_gaussianReal, Measure.bind_apply hs hker.aemeasurable,
      gaussianReal_of_var_ne_zero _ hv,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hmk]
    rfl
  · have h0 : inverseGammaDensity p.alpha p.beta x = 0 := inverseGammaDensity_of_nonpos _ _ _ hx
    have hfun : (fun m => ENNReal.ofReal (nigDensity p (m, x)) * gaussianReal m x.toNNReal s)
        = fun _ => 0 := by
      funext m
      simp [nigDensity, h0]
    simp [hfun, h0]

/-- **Bridge (kernel form).** The model's marginal law of `z` (push-forward of the
density-defined hierarchy) is the inverse-gamma mixture of `N(γ, σ²/ν + σ²)`. -/
theorem predictiveLaw_eq_bind (p : Parameters) :
    predictiveLaw p = (inverseGammaLaw ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩).bind
      (fun x => gaussianReal p.gamma ((x / p.nu).toNNReal + x.toNNReal)) := by
  have hK : Measurable (fun x : ℝ => gaussianReal p.gamma ((x / p.nu).toNNReal + x.toNNReal)) :=
    measurable_gaussianReal.comp (measurable_const.prodMk
      (((measurable_id.div_const _).real_toNNReal).add measurable_id.real_toNNReal))
  have hH := measurable_hierarchyDensity p
  have hlat : Measurable latentCoordinate := measurable_snd
  ext s hs
  rw [Measure.bind_apply hs hK.aemeasurable, inverseGammaLaw,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_inverseGammaDensity _ _).ennreal_ofReal
      (g := fun x => gaussianReal p.gamma ((x / p.nu).toNNReal + x.toNNReal) s)
      ((Measure.measurable_coe hs).comp hK),
    predictiveLaw, Measure.map_apply hlat hs, hierarchyLaw, withDensity_apply _ (hlat hs),
    ← lintegral_indicator (hlat hs), Measure.volume_eq_prod,
    lintegral_prod _ ((hH.ennreal_ofReal.indicator (hlat hs)).aemeasurable)]
  have hin : ∀ q : ℝ × ℝ,
      ∫⁻ z, (latentCoordinate ⁻¹' s).indicator
          (fun h => ENNReal.ofReal (hierarchyDensity p h)) (q, z)
        = ENNReal.ofReal (nigDensity p q) * gaussianReal q.1 q.2.toNNReal s := fun q =>
    lintegral_latent_indicator p hs q
  simp_rw [hin]
  have hmeas : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal (nigDensity p q) * gaussianReal q.1 q.2.toNNReal s) :=
    (measurable_nigDensity p).ennreal_ofReal.mul ((Measure.measurable_coe hs).comp
      (measurable_gaussianReal.comp (measurable_fst.prodMk measurable_snd.real_toNNReal)))
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ hmeas.aemeasurable]
  refine lintegral_congr fun x => ?_
  exact lintegral_mean_layer p hs x

/-- **Bridge (measure level).** The model's `predictiveLaw` equals the three-layer kernel
form `σ² ~ IG(α, β)`, `μ | σ² ~ N(γ, σ²/ν)`, `z | μ, σ² ~ N(μ, σ²)`. -/
theorem predictiveLaw_eq_nigZMarginal (p : Parameters) :
    predictiveLaw p = nigZMarginal p.gamma p.nu p.alpha p.beta := by
  rw [predictiveLaw_eq_bind, inverseGammaLaw_eq_invGammaMeasure, nigZMarginal]
  congr 1
  funext x
  exact (gaussianReal_bind_gaussianReal _ _ _).symm

/-- The marginal law of `z` is the Student distribution with location `γ`,
`2α` degrees of freedom and squared Student scale `w = s/α`. -/
theorem predictiveLaw_eq_studentT (p : Parameters) :
    predictiveLaw p = studentTMeasure (2 * p.alpha) p.gamma (studentScaleSquared p) := by
  rw [predictiveLaw_eq_nigZMarginal,
    nigZMarginal_eq_studentT _ _ _ _ p.nu_pos p.alpha_pos p.beta_pos]
  rfl

/-- The Student density with `2α` degrees of freedom and squared scale `s/α` is the displayed
density `f_{γ,α,s}`. -/
theorem studentTPDFReal_eq_displayedPredictiveDensity (x : QuotientState) (z : ℝ) :
    studentTPDFReal (2 * x.alpha) x.gamma (x.s / x.alpha) z = displayedPredictiveDensity x z := by
  have ha := x.alpha_pos
  unfold studentTPDFReal displayedPredictiveDensity densityPrefactor
  have e1 : (2 * x.alpha + 1) / 2 = x.alpha + 1 / 2 := by ring
  have e2 : 2 * x.alpha / 2 = x.alpha := by ring
  have e3 : 2 * x.alpha * Real.pi * (x.s / x.alpha) = 2 * Real.pi * x.s := by
    field_simp
  have e4 : 2 * x.alpha * (x.s / x.alpha) = 2 * x.s := by
    field_simp
  rw [e1, e2, e3, e4, neg_add']

/-- The displayed density is
`f_{γ,α,s}(z) = Γ(α+½) / (Γ(α) √(2πs)) · (1 + (z-γ)²/(2s))^{-α-½}`. -/
theorem displayedPredictiveDensity_apply (x : QuotientState) (z : ℝ) :
    displayedPredictiveDensity x z =
      Real.Gamma (x.alpha + 1 / 2) / (Real.Gamma x.alpha * Real.sqrt (2 * Real.pi * x.s))
        * (1 + (z - x.gamma) ^ 2 / (2 * x.s)) ^ (-x.alpha - 1 / 2) := rfl

/-- The law with density `f_{γ,α,s}`, indexed by the quotient state `x = (γ, α, s)`. -/
def quotientLaw (x : QuotientState) : Measure ℝ :=
  volume.withDensity (fun z => ENNReal.ofReal (displayedPredictiveDensity x z))

/-- Marginal density: the marginal law of `z` has Lebesgue density
`f_{γ,α,s}` with `s = β(1 + 1/ν)`. -/
theorem predictiveLaw_eq_quotientLaw (p : Parameters) :
    predictiveLaw p = quotientLaw (quotientCoordinates p) := by
  rw [predictiveLaw_eq_studentT, studentTMeasure, quotientLaw]
  congr 1
  funext z
  congr 1
  exact studentTPDFReal_eq_displayedPredictiveDensity (quotientCoordinates p) z

/-- The marginal density of `z`, written out. -/
theorem predictiveLaw_density (p : Parameters) :
    predictiveLaw p = volume.withDensity (fun z => ENNReal.ofReal
      (Real.Gamma (p.alpha + 1 / 2)
          / (Real.Gamma p.alpha * Real.sqrt (2 * Real.pi * quotientScale p))
        * (1 + (z - p.gamma) ^ 2 / (2 * quotientScale p)) ^ (-p.alpha - 1 / 2))) :=
  predictiveLaw_eq_quotientLaw p

/-- The marginal law of `z` is a probability measure. -/
theorem isProbabilityMeasure_predictiveLaw (p : Parameters) :
    IsProbabilityMeasure (predictiveLaw p) := by
  rw [predictiveLaw_eq_studentT]
  exact isProbabilityMeasure_studentTMeasure _ _ _ (by linarith [p.alpha_pos])
    (studentScaleSquared_pos p)

theorem continuous_displayedPredictiveDensity (x : QuotientState) :
    Continuous (displayedPredictiveDensity x) := by
  unfold displayedPredictiveDensity
  refine continuous_const.mul ?_
  exact (by fun_prop : Continuous fun z : ℝ => 1 + (z - x.gamma) ^ 2 / (2 * x.s)).rpow_const
    (fun z => Or.inl (densityBase_pos x z).ne')

/-- The entire marginal law identifies the quotient state. -/
theorem quotientLaw_injective : Function.Injective quotientLaw := by
  intro x y h
  have hcx : Continuous (fun z => ENNReal.ofReal (displayedPredictiveDensity x z)) :=
    ENNReal.continuous_ofReal.comp (continuous_displayedPredictiveDensity x)
  have hcy : Continuous (fun z => ENNReal.ofReal (displayedPredictiveDensity y z)) :=
    ENNReal.continuous_ofReal.comp (continuous_displayedPredictiveDensity y)
  have hae := (withDensity_eq_iff_of_sigmaFinite hcx.measurable.aemeasurable
    hcy.measurable.aemeasurable).mp h
  have hfun := (Continuous.ae_eq_iff_eq volume hcx hcy).mp hae
  apply displayedPredictiveDensity_injective
  funext z
  exact (ENNReal.ofReal_eq_ofReal_iff (displayedPredictiveDensity_pos x z).le
    (displayedPredictiveDensity_pos y z).le).mp (congrFun hfun z)

/-- Two admissible parameter quadruples induce the same marginal law if and
only if their triples `(γ, α, s)` agree. -/
theorem predictiveLaw_eq_iff (p q : Parameters) :
    predictiveLaw p = predictiveLaw q ↔ quotientCoordinates p = quotientCoordinates q := by
  rw [predictiveLaw_eq_quotientLaw, predictiveLaw_eq_quotientLaw]
  exact quotientLaw_injective.eq_iff

/-- The same statement, with the triples written out. -/
theorem predictiveLaw_eq_iff_triple (p q : Parameters) :
    predictiveLaw p = predictiveLaw q ↔
      p.gamma = q.gamma ∧ p.alpha = q.alpha ∧ quotientScale p = quotientScale q :=
  (predictiveLaw_eq_iff p q).trans (quotientCoordinates_eq_iff p q)

/-- The marginal law is constant on each fiber `F_x`. -/
theorem predictiveLaw_eq_of_mem_fiber {x : QuotientState} {p q : Parameters}
    (hp : p ∈ coordinateFiber x) (hq : q ∈ coordinateFiber x) :
    predictiveLaw p = predictiveLaw q :=
  (predictiveLaw_eq_iff p q).mpr (hp.trans hq.symm)

/-- On the fiber `F_x`, parameterized by `t = 1/ν`, the marginal law is the law
with density `f_x`. -/
theorem predictiveLaw_fiberParameters (x : QuotientState) (t : PositiveReal) :
    predictiveLaw (fiberParameters x t) = quotientLaw x := by
  rw [predictiveLaw_eq_quotientLaw, quotientCoordinates_fiberParameters]

/-- Every reconstruction functional of the model (a functional
`ReconstructionLoss Y` of the marginal law of `z`) is constant on each fiber `F_x`. -/
theorem reconstruction_const_on_fiber {Y : Type*} (L : ReconstructionLoss Y) (y : Y)
    {x : QuotientState} {p q : Parameters} (hp : p ∈ coordinateFiber x)
    (hq : q ∈ coordinateFiber x) :
    L (predictiveLaw p) y = L (predictiveLaw q) y := by
  rw [predictiveLaw_eq_of_mem_fiber hp hq]

/-- In particular, the reconstruction term of the original objective takes the
same value at every point `(γ, 1/t, α, s/(1+t))` of the fiber. -/
theorem reconstruction_fiberParameters {Y : Type*} (L : ReconstructionLoss Y) (y : Y)
    (x : QuotientState) (t t' : PositiveReal) :
    L (predictiveLaw (fiberParameters x t)) y = L (predictiveLaw (fiberParameters x t')) y := by
  rw [predictiveLaw_fiberParameters, predictiveLaw_fiberParameters]

/-- Converse: the entire marginal law identifies `x`; every
reconstruction functional therefore factors through the quotient state. -/
theorem reconstruction_factors_through_quotient {Y : Type*} (L : ReconstructionLoss Y) (y : Y)
    (p : Parameters) : L (predictiveLaw p) y = L (quotientLaw (quotientCoordinates p)) y := by
  rw [predictiveLaw_eq_quotientLaw]

/-- An individual reconstruction functional may identify less than the
entire marginal law: there is a reconstruction functional whose values do not determine the
quotient state, although the marginal law itself does (`quotientLaw_injective`). -/
theorem exists_reconstruction_not_identifying :
    ∃ (L : ReconstructionLoss Unit), ¬ Function.Injective
      (fun x : QuotientState => L (quotientLaw x) ()) := by
  refine ⟨fun _ _ => 0, fun h => ?_⟩
  let x₁ : QuotientState := ⟨0, 1, 1, one_pos, one_pos⟩
  let x₂ : QuotientState := ⟨1, 1, 1, one_pos, one_pos⟩
  have h12 : x₁ = x₂ := h rfl
  have : (0 : ℝ) = 1 := congrArg QuotientState.gamma h12
  exact zero_ne_one this

end PredictiveLaw

end NIGBottleneck
