import Mathlib

/-!
# Hierarchical NIG model and original objective

The hierarchy is constructed from its inverse-gamma and conditional Gaussian
densities. Its predictive law is defined by projection of the full joint law,
not by a closed-form marginal density. The hierarchical divergence is defined
by the integral of the log density ratio.
-/

noncomputable section

open MeasureTheory

namespace NIGBottleneck

/-- Positive real parameters, used for the hierarchy and the objective. -/
abbrev PositiveReal := {r : ℝ // 0 < r}

/-- Admissible parameters of a normal--inverse-gamma hierarchy.
The same parameter space is used for the complete prior. -/
structure Parameters where
  /-- Location of the conditional mean. -/
  gamma : ℝ
  /-- Positive conditional-mean precision multiplier. -/
  nu : ℝ
  /-- Positive inverse-gamma shape. -/
  alpha : ℝ
  /-- Positive inverse-gamma scale. -/
  beta : ℝ
  /-- Admissibility of the precision multiplier. -/
  nu_pos : 0 < nu
  /-- Admissibility of the shape. -/
  alpha_pos : 0 < alpha
  /-- Admissibility of the scale. -/
  beta_pos : 0 < beta

/-- The inverse-gamma density, extended by zero outside
the positive half-line. -/
def inverseGammaDensity (a b x : ℝ) : ℝ :=
  if 0 < x then
    Real.rpow b a / Real.Gamma a *
      Real.rpow x (-a - 1) * Real.exp (-b / x)
  else
    0

/-- The inverse-gamma law with positive shape and scale. -/
def inverseGammaLaw (a b : PositiveReal) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun x => ENNReal.ofReal (inverseGammaDensity a.val b.val x))

/-- The Gaussian density with mean `m` and variance `v`,
used on the domain `v > 0`. -/
def normalDensity (m v z : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * v))⁻¹ *
    Real.exp (-((z - m) ^ 2) / (2 * v))

/-- A Gaussian law with strictly positive variance. -/
def normalLaw (m : ℝ) (v : PositiveReal) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun z => ENNReal.ofReal (normalDensity m v.val z))

/-- The law of the variance variable `X = σ²`. -/
def varianceLaw (p : Parameters) : Measure ℝ :=
  inverseGammaLaw ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩

/-- The conditional law of `μ` given a positive value of `X`. -/
def meanGivenVariance (p : Parameters) (x : PositiveReal) : Measure ℝ :=
  normalLaw p.gamma ⟨x.val / p.nu, div_pos x.property p.nu_pos⟩

/-- The conditional law of `z` given `μ` and positive `X`. -/
def latentGivenMeanVariance (m : ℝ) (x : PositiveReal) : Measure ℝ :=
  normalLaw m x

/-- The joint NIG density in coordinate order `(μ, X)`,
obtained by multiplying the marginal and conditional densities. -/
def nigDensity (p : Parameters) (h : ℝ × ℝ) : ℝ :=
  inverseGammaDensity p.alpha p.beta h.2 *
    normalDensity p.gamma (h.2 / p.nu) h.1

/-- The complete normal--inverse-gamma law of `(μ, X)`. -/
def nigLaw (p : Parameters) : Measure (ℝ × ℝ) :=
  (volume : Measure (ℝ × ℝ)).withDensity
    (fun h => ENNReal.ofReal (nigDensity p h))

/-- The complete prior `p₀`, retaining all four parameters. -/
def completePriorLaw (p₀ : Parameters) : Measure (ℝ × ℝ) :=
  nigLaw p₀

/-- The sample space of the full hierarchy, in coordinate
order `((μ, X), z)`. -/
abbrev HierarchySpace := (ℝ × ℝ) × ℝ

/-- The variance coordinate `X = σ²` of the hierarchy. -/
def varianceCoordinate (h : HierarchySpace) : ℝ :=
  h.1.2

/-- The random-mean coordinate `μ` of the hierarchy. -/
def meanCoordinate (h : HierarchySpace) : ℝ :=
  h.1.1

/-- The latent coordinate `z` of the hierarchy. -/
def latentCoordinate (h : HierarchySpace) : ℝ :=
  h.2

/-- The full hierarchical density, formed from the NIG density
and the specified conditional density of `z`. -/
def hierarchyDensity (p : Parameters) (h : HierarchySpace) : ℝ :=
  nigDensity p h.1 *
    normalDensity (meanCoordinate h) (varianceCoordinate h) (latentCoordinate h)

/-- The joint law of `((μ, X), z)` specified by the hierarchy. -/
def hierarchyLaw (p : Parameters) : Measure HierarchySpace :=
  (volume : Measure HierarchySpace).withDensity
    (fun h => ENNReal.ofReal (hierarchyDensity p h))

/-- The marginal law of `z`, defined by projection of the
hierarchy rather than by a derived predictive-density formula. -/
def predictiveLaw (p : Parameters) : Measure ℝ :=
  Measure.map latentCoordinate (hierarchyLaw p)

/-- The complete hierarchical forward KL divergence, defined
by its log-density-ratio integral. For admissible NIG parameters this integral
is finite, so its value is represented as a real number. -/
def hierarchicalKL (p p₀ : Parameters) : ℝ :=
  ∫ h : ℝ × ℝ,
    Real.log (nigDensity p h / nigDensity p₀ h) ∂(nigLaw p)

/-- A reconstruction functional takes only the predictive
marginal and the observed input as arguments. Extended-real values also allow
the infinite-loss cases allowed by the model. -/
abbrev ReconstructionLoss (Y : Type*) :=
  Measure ℝ → Y → EReal

/-- The original four-parameter objective, with strictly
positive variational weight and a complete NIG prior. -/
def originalObjective {Y : Type*} (reconstruction : ReconstructionLoss Y)
    (p p₀ : Parameters) (weight : PositiveReal) (y : Y) : EReal :=
  reconstruction (predictiveLaw p) y +
    ((weight.val * hierarchicalKL p p₀ : ℝ) : EReal)

end NIGBottleneck
