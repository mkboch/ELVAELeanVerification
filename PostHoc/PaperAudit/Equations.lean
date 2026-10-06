import Official.M07
import Official.M22
import ELVAELeanVerification.RestrictedKLDivergence

/-!
# Paper audit: hierarchy, divergence, predictive law, quotient and fiber (Eqs. (1)–(9))

Post-arXiv paper-wide verification (not part of the historical B1/B2 study). Each theorem restates a
displayed equation of the arXiv v1 manuscript in the paper's notation and proves it from the formal
corpus. Paper notation: `V` is the latent variance, `q = (γ, α, c)` a quotient state with `c = β(1 +
1/ν)`; a quotient state is represented by `NIGBottleneck.QuotientState`, whose third coordinate `s`
is the paper's `c`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory NIGBottleneck

namespace PaperAudit

/-! ## Eqs. (1)–(3): hierarchy, inverse-gamma parameterization, complete prior -/

/-- Paper Eq. (2): `f_IG(v; α, β) = β^α / Γ(α) · v^(−α−1) · exp(−β/v)`. -/
def paperIGDensity (α β v : ℝ) : ℝ :=
  β ^ α / Real.Gamma α * v ^ (-α - 1) * Real.exp (-β / v)

/-- Paper Eq. (2): the inverse-gamma density of the formal model is the paper's density on `v > 0`
(and is zero elsewhere). -/
theorem paper_eq2_ig_density (α β v : ℝ) (hv : 0 < v) :
    inverseGammaDensity α β v = paperIGDensity α β v := by
  unfold inverseGammaDensity paperIGDensity
  simp only [hv, ↓reduceIte]
  rfl

/-- Paper Eqs. (1) and (3): the admissible parameter domain `γ ∈ ℝ`, `ν, α, β > 0` (the same domain
is used for the complete prior `p₀`), and the joint law of `(μ, V)` has density `f_IG(V; α, β) ·
N(μ; γ, V/ν)`, with `z | μ, V ∼ N(μ, V)` as the hierarchy kernel. -/
theorem paper_eq1_eq3_hierarchy (p : Parameters) :
    (0 < p.nu ∧ 0 < p.alpha ∧ 0 < p.beta)
      ∧ (∀ h : ℝ × ℝ, nigDensity p h
          = inverseGammaDensity p.alpha p.beta h.2 * normalDensity p.gamma (h.2 / p.nu) h.1)
      ∧ hierarchyLaw p = nigLaw p ⊗ₘ hierKernel :=
  ⟨⟨p.nu_pos, p.alpha_pos, p.beta_pos⟩, fun _ => rfl, hierarchyLaw_eq_compProd p⟩

/-! ## Eq. (4): the four-coordinate objective -/

/-- Paper Eq. (4): `J₄ = L_rec(L(z); y) + λ KL[NIG(γ,ν,α,β) ‖ p₀]`, `λ > 0`, where the KL term is
Mathlib's Kullback–Leibler divergence of the two NIG laws and the reconstruction term depends on the
hierarchy only through the marginal law of `z`. -/
theorem paper_eq4_objective {Y : Type*} (L : ReconstructionLoss Y) (p p₀ : Parameters)
    (w : PositiveReal) (y : Y) :
    originalObjective L p p₀ w y
      = L (predictiveLaw p) y
        + ((w.val * (klDiv (nigLaw p) (nigLaw p₀)).toReal : ℝ) : EReal) := by
  rw [originalObjective, hierarchicalKL_eq_toReal_klDiv]

/-! ## Eq. (5): the explicit NIG divergence -/

/-- Paper Eq. (5): for admissible parameter tuples, `KL[NIG(p) ‖ NIG(p₀)]` is finite and equals the
explicit closed form `C(p, p₀)` (B2's `nigKLClosedForm`). -/
theorem paper_eq5_kl_closed_form (p p₀ : Parameters) :
    klDiv (nigLaw p) (nigLaw p₀) ≠ ⊤
      ∧ (klDiv (nigLaw p) (nigLaw p₀)).toReal = nigKLClosedForm p p₀ := by
  refine ⟨by rw [klDiv_nigLaw]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [← hierarchicalKL_eq_toReal_klDiv, hierarchicalKL_eq_closedForm]

/-- The two digamma conventions agree on `α > 0`: B2's `deriv (log ∘ Γ)` and the reference
development's `logDeriv Γ`. -/
theorem digamma_eq_realDigamma {a : ℝ} (ha : 0 < a) :
    NIGBottleneck.digamma a = ELVAE.realDigamma a := by
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hd : DifferentiableAt ℝ Real.Gamma a := by
    apply Real.differentiableAt_Gamma
    intro m hm
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [NIGBottleneck.digamma, ELVAE.realDigamma, logDeriv_apply, deriv.log hd hΓ.ne']

/-- Cross-check of Eq. (5) between the two formal developments: the B2 closed form `C(p, p₀)` equals
the closed form of the earlier reference development, which separately proves `klDiv (NIG) (NIG) =
C` for its own measure construction (`ELVAE.klDiv_nigMeasureMuSigma`). -/
theorem paper_eq5_closed_forms_agree (p p₀ : Parameters) :
    nigKLClosedForm p p₀
      = ELVAE.nigKLClosedForm p.gamma p.nu p.alpha p.beta p₀.gamma p₀.nu p₀.alpha p₀.beta := by
  have hb := p.beta_pos
  have hb0 := p₀.beta_pos
  have hn := p.nu_pos
  have hn0 := p₀.nu_pos
  have hΓ := Real.Gamma_pos_of_pos p.alpha_pos
  have hΓ0 := Real.Gamma_pos_of_pos p₀.alpha_pos
  rw [NIGBottleneck.nigKLClosedForm, ELVAE.nigKLClosedForm, digamma_eq_realDigamma p.alpha_pos,
    Real.log_div hb.ne' hb0.ne', Real.log_div hΓ0.ne' hΓ.ne']
  field_simp
  ring

/-! ## Eq. (6): the predictive Student-t law -/

/-- Paper Eq. (6): `z | y ∼ Student-t_{2α}(γ, c/α)` with `c = β(1 + 1/ν)`. The third Student-t
argument is the *squared* scale: `studentTPDFReal n m s2` is the density with `n` degrees of
freedom, location `m` and squared scale `s2` (see `paper_eq6_student_convention`). -/
theorem paper_eq6_predictive_student (p : Parameters) :
    predictiveLaw p = studentTMeasure (2 * p.alpha) p.gamma (p.beta * (1 + 1 / p.nu) / p.alpha) :=
  predictiveLaw_eq_studentT p

/-- The Student-t convention used for Eq. (6): the parameter `s2` enters as a squared scale, i.e.
the density is `Γ((n+1)/2) / (Γ(n/2) √(n π s2)) · (1 + (y−m)²/(n s2))^(−(n+1)/2)`. -/
theorem paper_eq6_student_convention (n m s2 y : ℝ) :
    studentTPDFReal n m s2 y
      = Real.Gamma ((n + 1) / 2) / (Real.Gamma (n / 2) * Real.sqrt (n * Real.pi * s2))
        * (1 + (y - m) ^ 2 / (n * s2)) ^ (-((n + 1) / 2)) :=
  rfl

/-! ## Eqs. (7)–(9): quotient coordinates, quotient map and fiber -/

/-- Paper Eq. (8): the quotient map `π(γ, ν, α, β) = (γ, α, c)`, `c = β(1 + 1/ν)`. -/
def paperPi (p : Parameters) : ℝ × ℝ × ℝ :=
  (p.gamma, p.alpha, p.beta * (1 + 1 / p.nu))

/-- Paper Eq. (7): the predictive law depends on the NIG quadruple exactly through `q = (γ, α, c)`.
-/
theorem paper_eq7_eq8_quotient (p p' : Parameters) :
    predictiveLaw p = predictiveLaw p' ↔ paperPi p = paperPi p' := by
  rw [predictiveLaw_eq_iff_triple]
  simp only [paperPi, quotientScale, Prod.mk.injEq]

/-- Paper Eq. (9): the point `(γ, ν, α, cν/(1+ν))` of the fiber over `q`, for `ν > 0`. -/
def paperFiberParams (q : QuotientState) (ν : ℝ) (hν : 0 < ν) : Parameters where
  gamma := q.gamma
  nu := ν
  alpha := q.alpha
  beta := q.s * ν / (1 + ν)
  nu_pos := hν
  alpha_pos := q.alpha_pos
  beta_pos := by have := q.s_pos; positivity

/-- The paper's ν-parameterized fiber point is B2's `t`-parameterized fiber point with `t = 1/ν`. -/
theorem paperFiberParams_eq (q : QuotientState) (ν : ℝ) (hν : 0 < ν) :
    paperFiberParams q ν hν = fiberParameters q ⟨1 / ν, one_div_pos.mpr hν⟩ := by
  have h1 : (1 + ν) ≠ 0 := by linarith
  have h2 : ν ≠ 0 := hν.ne'
  apply parameters_ext <;> simp only [paperFiberParams, fiberParameters]
  · rw [one_div_one_div]
  · field_simp
    ring

/-- Paper Eq. (9): the fiber over `q` is exactly `{(γ, ν, α, cν/(1+ν)) : ν > 0}`: every fiber point
lies over `q`, and every parameter tuple over `q` is the fiber point with its own `ν`. -/
theorem paper_eq9_fiber (q : QuotientState) :
    (∀ ν (hν : 0 < ν), quotientCoordinates (paperFiberParams q ν hν) = q)
      ∧ ∀ p : Parameters, quotientCoordinates p = q → p = paperFiberParams q p.nu p.nu_pos := by
  refine ⟨fun ν hν => ?_, fun p hp => ?_⟩
  · rw [paperFiberParams_eq]
    exact quotientCoordinates_fiberParameters q _
  · have hfib := fiberParameters_quotientCoordinates p
    rw [hp] at hfib
    rw [paperFiberParams_eq]
    conv_lhs => rw [← hfib]
    rfl

/-- Section 3.2: a quotient state fixes the predictive law but not the allocation between `ν` and
`β`: the predictive law is constant along the fiber, while distinct `ν` give distinct parameter
tuples.
-/
theorem paper_fiber_predictive_invariance (q : QuotientState) (ν ν' : ℝ) (hν : 0 < ν)
    (hν' : 0 < ν') :
    predictiveLaw (paperFiberParams q ν hν) = predictiveLaw (paperFiberParams q ν' hν')
      ∧ (ν ≠ ν' → paperFiberParams q ν hν ≠ paperFiberParams q ν' hν') := by
  refine ⟨?_, fun hne h => hne ?_⟩
  · rw [predictiveLaw_eq_iff, (paper_eq9_fiber q).1, (paper_eq9_fiber q).1]
  · have := congrArg Parameters.nu h
    simpa [paperFiberParams] using this

end PaperAudit
