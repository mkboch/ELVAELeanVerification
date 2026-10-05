import Official.M23
import Official.M22
import Official.M21
import Official.M20
import Official.M19
import Official.M17
import Official.M16
import Official.M15
import Official.M14
import Official.M13
import Official.M12
import Official.M11
import Official.M10
import Official.M09
import Official.M08
import Official.M07
import Official.M06
import Official.M05
import Official.M04
import Official.M03
import PostHoc.Relations.Audit

/-!
# L2 definition fidelity (layer 1 of the L2 ↔ Lean audit)

Each theorem `l2def_*` writes an L2 definition literally and proves that it coincides with the B2
definition it was translated from. Most are definitional (`rfl`). Together they certify that the
objects L2 talks about are B2's objects, so that the statement layer (`Items1`–`Items3`) can be
written in B2 vocabulary.

Conventions stated in L2 (Lean/Mathlib totalized division, `Real.log`, `Real.sqrt`, `Real.rpow`,
Bochner integral, `withDensity`, `gaussianReal`, `gammaMeasure`) are Mathlib's own, so they need no
separate formalization.
-/

-- cosmetic only: long statement lines are kept verbatim-readable
set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory NIGBottleneck

namespace PostHocL2Audit

/-- L2: f^IG_{a,b}(x)=b^a/Γ(a)·x^{−a−1}e^{−b/x} if x>0, 0 otherwise; IG(a,b)=Leb⊙ofR∘f^IG. -/
theorem l2def_IG (a b : PositiveReal) :
    (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal
      (if 0 < x then (b : ℝ) ^ (a : ℝ) / Real.Gamma a * x ^ (-(a : ℝ) - 1) * Real.exp (-(b : ℝ) / x) else 0))
    = inverseGammaLaw a b := rfl

/-- L2: n_{m,v}(z)=(√(2πv))⁻¹exp(−(z−m)²/(2v)); normalLaw(m,v)=Leb⊙ofR∘n_{m,v}. -/
theorem l2def_normal (m : ℝ) (v : PositiveReal) :
    (volume : Measure ℝ).withDensity (fun z => ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹
      * Real.exp (-((z - m) ^ 2) / (2 * v)))) = normalLaw m v := rfl

/-- L2: f^NIG_p(m,x)=f^IG_{α,β}(x)·n_{γ,x/ν}(m); NIG(p)=Leb⊙ofR∘f^NIG. -/
theorem l2def_NIG (p : Parameters) :
    (volume : Measure (ℝ × ℝ)).withDensity (fun h => ENNReal.ofReal
      (inverseGammaDensity p.alpha p.beta h.2 * normalDensity p.gamma (h.2 / p.nu) h.1)) = nigLaw p := rfl

/-- L2: f^H_p(h)=f^NIG_p(m,x)n_{m,x}(z); Hier(p)=Leb⊙ofR∘f^H; Pred(p)=pushforward under h ↦ z. -/
theorem l2def_Hier (p : Parameters) :
    (volume : Measure HierarchySpace).withDensity (fun h => ENNReal.ofReal
      (nigDensity p h.1 * normalDensity h.1.1 h.1.2 h.2)) = hierarchyLaw p
    ∧ (hierarchyLaw p).map (fun h => h.2) = predictiveLaw p := ⟨rfl, rfl⟩

/-- L2: KL(p‖p₀)=∫ log(f^NIG_p/f^NIG_{p₀}) dNIG(p). -/
theorem l2def_KL (p p₀ : Parameters) :
    ∫ h, Real.log (nigDensity p h / nigDensity p₀ h) ∂(nigLaw p) = hierarchicalKL p p₀ := rfl

/-- L2: J(L,p,p₀,w,y)=L(Pred(p),y)+(w·KL(p‖p₀)). -/
theorem l2def_J {Y : Type} (L : ReconstructionLoss Y) (p p₀ : Parameters) (w : PositiveReal) (y : Y) :
    L (predictiveLaw p) y + ((w.val * hierarchicalKL p p₀ : ℝ) : EReal) = originalObjective L p p₀ w y := rfl

/-- L2: ψ(a)=deriv(s ↦ log Γ(s))(a). -/
theorem l2def_psi (a : ℝ) : deriv (fun s : ℝ => Real.log (Real.Gamma s)) a = digamma a := rfl

/-- L2: S(p)=β(1+1/ν), studentScaleSquared(p)=S(p)/α. -/
theorem l2def_S (p : Parameters) :
    p.beta * (1 + 1 / p.nu) = quotientScale p ∧ quotientScale p / p.alpha = studentScaleSquared p := ⟨rfl, rfl⟩

/-- L2: π(p)=(γ,α,S(p)), τ(p)=1/ν, φ_x(t)=(γ_x,1/t,α_x,s_x/(1+t)), Fib(x)={p : π(p)=x}. -/
theorem l2def_quotient (p : Parameters) (x : QuotientState) (t : PositiveReal) :
    ((quotientCoordinates p).gamma = p.gamma ∧ (quotientCoordinates p).alpha = p.alpha
      ∧ (quotientCoordinates p).s = p.beta * (1 + 1 / p.nu))
    ∧ (fiberCoordinate p : ℝ) = 1 / p.nu
    ∧ ((fiberParameters x t).gamma = x.gamma ∧ (fiberParameters x t).nu = 1 / (t : ℝ)
      ∧ (fiberParameters x t).alpha = x.alpha ∧ (fiberParameters x t).beta = x.s / (1 + (t : ℝ)))
    ∧ coordinateFiber x = {q | quotientCoordinates q = x} :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

/-- L2: d_x(z)=Γ(α+½)/(Γ(α)√(2πs))·(1+(z−γ)²/(2s))^{−α−1/2}; q_x=Leb⊙ofR∘d_x. -/
theorem l2def_q (x : QuotientState) :
    (volume : Measure ℝ).withDensity (fun z => ENNReal.ofReal
      (Real.Gamma (x.alpha + 1 / 2) / (Real.Gamma x.alpha * Real.sqrt (2 * Real.pi * x.s))
        * (1 + (z - x.gamma) ^ 2 / (2 * x.s)) ^ (-x.alpha - 1 / 2))) = quotientLaw x := rfl

/-- L2: t_{n,m,s₂}(y)=Γ((n+1)/2)/(Γ(n/2)√(nπs₂))·(1+(y−m)²/(ns₂))^{−(n+1)/2}; St=Leb⊙ofR∘t. -/
theorem l2def_St (n m s2 : ℝ) :
    (volume : Measure ℝ).withDensity (fun y => ENNReal.ofReal
      (Real.Gamma ((n + 1) / 2) / (Real.Gamma (n / 2) * Real.sqrt (n * Real.pi * s2))
        * (1 + (y - m) ^ 2 / (n * s2)) ^ (-((n + 1) / 2)))) = studentTMeasure n m s2 := rfl

/-- L2: invGamma(a,b)=(t ↦ t⁻¹)_*Gamma(a,b); nigZ = invGamma.bind(s ↦ N(γ,(s/ν)⁺).bind(m ↦ N(m,s⁺))). -/
theorem l2def_nigZ (g n a b : ℝ) :
    ((gammaMeasure a b).map (fun t => t⁻¹)).bind (fun s => (gaussianReal g (s / n).toNNReal).bind
      (fun m => gaussianReal m s.toNNReal)) = nigZMarginal g n a b := rfl

/-- L2: NR(x)=IG(α,s).bind(v ↦ N(γ,v⁺)); NRJ(x) has density f^IG_{α,s}(v)n_{γ,v}(z). -/
theorem l2def_NR (x : QuotientState) :
    (inverseGammaLaw ⟨x.alpha, x.alpha_pos⟩ ⟨x.s, x.s_pos⟩).bind (fun v => gaussianReal x.gamma v.toNNReal)
      = nonredundantLaw x
    ∧ (volume : Measure (ℝ × ℝ)).withDensity (fun q => ENNReal.ofReal
        (inverseGammaDensity x.alpha x.s q.1 * normalDensity x.gamma q.1 q.2)) = nonredundantJointLaw x :=
  ⟨rfl, rfl⟩

/-- L2: C(p,p₀), B_{p₀}(x), K_{p₀,x}(t)=KL(φ_x(t)‖p₀), F_{p₀,x}(t). -/
theorem l2def_KLforms (p p₀ : Parameters) (x : QuotientState) (t : PositiveReal) (u : ℝ) :
    p₀.alpha * Real.log (p.beta / p₀.beta) + Real.log (Real.Gamma p₀.alpha / Real.Gamma p.alpha)
      + (p.alpha - p₀.alpha) * digamma p.alpha - p.alpha + p.alpha * p₀.beta / p.beta
      + 1 / 2 * (p₀.nu / p.nu - 1 + Real.log (p.nu / p₀.nu) + p₀.nu * p.alpha * (p.gamma - p₀.gamma) ^ 2 / p.beta)
      = nigKLClosedForm p p₀
    ∧ p₀.beta + p₀.nu / 2 * (x.gamma - p₀.gamma) ^ 2 = priorB p₀ x
    ∧ hierarchicalKL (fiberParameters x t) p₀ = fiberKL p₀ x t
    ∧ p₀.alpha * Real.log (x.s / p₀.beta) + Real.log (Real.Gamma p₀.alpha / Real.Gamma x.alpha)
        + (x.alpha - p₀.alpha) * digamma x.alpha - x.alpha - p₀.alpha * Real.log (1 + u)
        + x.alpha * priorB p₀ x / x.s * (1 + u) + 1 / 2 * (p₀.nu * u - 1 - Real.log (p₀.nu * u))
      = fiberKLFormula p₀ x u := ⟨rfl, rfl, rfl, rfl⟩

/-- L2: Δ, T_A, Φ_A; D_{p₀}(x), t*, ν*, β*; G_{p₀,x}(t). -/
theorem l2def_selection (A d : ℝ) (p₀ : Parameters) (x : QuotientState) (u : ℝ) :
    (2 * A + 1 - d + Real.sqrt ((d - 2 * A - 1) ^ 2 + 4 * d)) / (2 * d) = TA A d
    ∧ (d - 2 * A - 1 + Real.sqrt ((d - 2 * A - 1) ^ 2 + 4 * d)) / 2 = PhiA A d
    ∧ p₀.nu + 2 * x.alpha * priorB p₀ x / x.s = selD p₀ x
    ∧ TA p₀.alpha (selD p₀ x) = selT p₀ x ∧ PhiA p₀.alpha (selD p₀ x) = selNu p₀ x
    ∧ x.s / (1 + selT p₀ x) = selBeta p₀ x ∧ ((selTPos p₀ x : PositiveReal) : ℝ) = selT p₀ x
    ∧ p₀.alpha * ((1 + u) / (1 + selT p₀ x) - 1 - Real.log ((1 + u) / (1 + selT p₀ x)))
        + 1 / 2 * (u / selT p₀ x - 1 - Real.log (u / selT p₀ x)) = fiberGap p₀ x u :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- L2: Ω₇ and the 7-variable maps D, T, N, 𝓑. -/
theorem l2def_coords (v : StatePrior) :
    (v ∈ statePriorDomain ↔ 0 < v.2.1 ∧ 0 < v.2.2.1 ∧ 0 < v.2.2.2.2.1 ∧ 0 < v.2.2.2.2.2.1 ∧ 0 < v.2.2.2.2.2.2)
    ∧ v.2.2.2.2.1 + 2 * v.2.1 * (v.2.2.2.2.2.2 + v.2.2.2.2.1 / 2 * (v.1 - v.2.2.2.1) ^ 2) / v.2.2.1 = selDCoord v
    ∧ TA v.2.2.2.2.2.1 (selDCoord v) = selTCoord v ∧ PhiA v.2.2.2.2.2.1 (selDCoord v) = selNuCoord v
    ∧ v.2.2.1 / (1 + selTCoord v) = selBetaCoord v := ⟨Iff.rfl, rfl, rfl, rfl, rfl⟩

/-- L2: x̄₀=π(p₀); minKL; ℓ_L(x,y)=L(q_x,y); R_{p₀}(x)=K(t*); J♭=ℓ+wR. -/
theorem l2def_reduced {Y : Type} (L : ReconstructionLoss Y) (p₀ : Parameters) (w : PositiveReal) (x : QuotientState)
    (y : Y) :
    priorQuotient p₀ = quotientCoordinates p₀ ∧ minimizedKL p₀ x = fiberKL p₀ x (selTPos p₀ x)
    ∧ quotientLoss L x y = L (quotientLaw x) y ∧ regularizerR p₀ x = fiberKL p₀ x (selTPos p₀ x)
    ∧ reducedObjective L p₀ w x y = L (quotientLaw x) y + ((w.val * regularizerR p₀ x : ℝ) : EReal) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- L2: ψ₁=deriv ψ; Ω₃, B(ξ), F(ξ,t) (with log Γ(α₀) − log Γ(α)), d(ξ), t*(ξ), 𝖱(ξ). -/
theorem l2def_Rcoords (p₀ : Parameters) (ξ : QCoord) (u a : ℝ) :
    deriv digamma a = trigamma a
    ∧ (ξ ∈ qDomain ↔ 0 < ξ.2.1 ∧ 0 < ξ.2.2)
    ∧ p₀.beta + p₀.nu / 2 * (ξ.1 - p₀.gamma) ^ 2 = BCoord p₀ ξ
    ∧ p₀.alpha * Real.log (ξ.2.2 / p₀.beta) + (Real.log (Real.Gamma p₀.alpha) - Real.log (Real.Gamma ξ.2.1))
        + (ξ.2.1 - p₀.alpha) * digamma ξ.2.1 - ξ.2.1 - p₀.alpha * Real.log (1 + u)
        + ξ.2.1 * BCoord p₀ ξ / ξ.2.2 * (1 + u) + 1 / 2 * (p₀.nu * u - 1 - Real.log (p₀.nu * u)) = FCoord p₀ ξ u
    ∧ p₀.nu + 2 * ξ.2.1 * BCoord p₀ ξ / ξ.2.2 = dCoord p₀ ξ
    ∧ TA p₀.alpha (dCoord p₀ ξ) = tStarCoord p₀ ξ ∧ FCoord p₀ ξ (tStarCoord p₀ ξ) = RCoord p₀ ξ :=
  ⟨rfl, Iff.rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- L2: j, 𝓔, π^post, ELBO, postKL, LL, likRec. -/
theorem l2def_elbo (p₀ p : Parameters) (lik : ℝ → ℝ) (h : HierarchySpace) (μ : Measure ℝ) :
    hierarchyDensity p₀ h * lik h.2 = jointDensity p₀ lik h
    ∧ ∫ h, jointDensity p₀ lik h = evidence p₀ lik
    ∧ jointDensity p₀ lik h / evidence p₀ lik = posteriorDensity p₀ lik h
    ∧ ∫ h, Real.log (jointDensity p₀ lik h / hierarchyDensity p h) ∂(hierarchyLaw p) = elbo p₀ lik p
    ∧ ∫ h, Real.log (hierarchyDensity p h / posteriorDensity p₀ lik h) ∂(hierarchyLaw p) = posteriorKL p₀ lik p
    ∧ -∫ z, Real.log (lik z) ∂μ = likelihoodLoss lik μ
    ∧ ((likelihoodLoss lik μ : ℝ) : EReal) = likelihoodReconstruction lik μ () :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- L2: U_al(p)=∫x dNIG(p), U_ep(p)=Var[(m,x) ↦ m; NIG(p)], V(p)=Var[id; Pred(p)]. -/
theorem l2def_unc (p : Parameters) :
    ∫ q, q.2 ∂nigLaw p = uVar p ∧ Var[fun q : ℝ × ℝ => q.1; nigLaw p] = uEpi p
    ∧ Var[id; predictiveLaw p] = totalVar p := ⟨rfl, rfl, rfl⟩

/-- L2: b(p₀)=2β₀/ν₀; prior(g₀,b,A,n)=(g₀,n,A,nb/2); Q_{p₀}(x); t_{A,n}, ν_{A,n}. -/
theorem l2def_score (p₀ : Parameters) (x : QuotientState) (g₀ b A n Q : ℝ) (hb : 0 < b) (hA : 0 < A) (hn : 0 < n) :
    2 * p₀.beta / p₀.nu = bParam p₀
    ∧ ((priorOfCoords g₀ b A n hb hA hn).gamma = g₀ ∧ (priorOfCoords g₀ b A n hb hA hn).nu = n
      ∧ (priorOfCoords g₀ b A n hb hA hn).alpha = A ∧ (priorOfCoords g₀ b A n hb hA hn).beta = n * b / 2)
    ∧ x.alpha * ((x.gamma - p₀.gamma) ^ 2 + bParam p₀) / x.s = scoreQ p₀ x
    ∧ TA A (n * (1 + Q)) = tOfScore A n Q ∧ PhiA A (n * (1 + Q)) = nuOfScore A n Q :=
  ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- L2: p^{x₀}_n; Q^B, t^B; Q^N, Q_low, Q_high, t^N; M(A,n)=T_A(n). -/
theorem l2def_families (x₀ : QuotientState) (n : ℝ) (hn : 0 < n) (A e w b s₀ : ℝ) :
    ((priorFamily x₀ n hn).gamma = x₀.gamma ∧ (priorFamily x₀ n hn).nu = n ∧ (priorFamily x₀ n hn).alpha = x₀.alpha
      ∧ (priorFamily x₀ n hn).beta = x₀.s * n / (n + 1))
    ∧ (e + b) / w = scoreB e w b ∧ TA A (n * (1 + scoreB e w b)) = tB A n e w b
    ∧ (e + 2 * s₀ / (n + 1)) / w = scoreN s₀ e w n ∧ (e + 2 * s₀) / w = scoreLow s₀ e w ∧ e / w = scoreHigh e w
    ∧ TA A (n * (1 + scoreN s₀ e w n)) = tN A s₀ e w n ∧ TA A n = boundM A n :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- L2: sel, agg, M_max = max_i M; ρ(a,t). -/
theorem l2def_agg {ι : Type} [Fintype ι] [Nonempty ι] (p₀ : ι → Parameters) (x : ι → QuotientState) (c a t : ι → ℝ)
    (q : Parameters) (z : QuotientState) :
    selParams q z = fiberParameters z (selTPos q z)
    ∧ (∑ i, c i * uEpi (selParams (p₀ i) (x i))) / (∑ i, c i * uVar (selParams (p₀ i) (x i))) = aggRatio p₀ x c
    ∧ Finset.univ.sup' Finset.univ_nonempty (fun i => boundM (p₀ i).alpha (p₀ i).nu) = maxBound p₀
    ∧ (∑ i, a i * (t i / (1 + t i))) / (∑ i, a i * (1 / (1 + t i))) = ratioOfT a t :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- L2: t^S, ν^S, C_{p₀}; U^S_al, U^S_ep. -/
theorem l2def_scale (A n D a s γ α : ℝ) (p₀ : Parameters) :
    TA A (n + D / s) = tScale A n D s ∧ PhiA A (n + D / s) = nuScale A n D s
    ∧ α * ((γ - p₀.gamma) ^ 2 + bParam p₀) = scaleC p₀ γ α
    ∧ s / (a * (1 + tScale A n D s)) = uVarScale A n D a s
    ∧ s * tScale A n D s / (a * (1 + tScale A n D s)) = uEpiScale A n D a s := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- L2: σ_κ(p)=(κγ,ν,α,κ²β), σ_κ(x)=(κγ,α,κ²s). -/
theorem l2def_sigma (κ : ℝ) (hκ : κ ≠ 0) (p : Parameters) (x : QuotientState) :
    ((scaleParams κ hκ p).gamma = κ * p.gamma ∧ (scaleParams κ hκ p).nu = p.nu ∧ (scaleParams κ hκ p).alpha = p.alpha
      ∧ (scaleParams κ hκ p).beta = κ ^ 2 * p.beta)
    ∧ ((scaleState κ hκ x).gamma = κ * x.gamma ∧ (scaleState κ hκ x).alpha = x.alpha
      ∧ (scaleState κ hκ x).s = κ ^ 2 * x.s) := ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- L2: X^λ₁=(γ₀,α₀,4s̄), X^λ₂=(γ₀,α₀,2s̄), w₋=1/(2R(X₁)), w₊=2/R(X₁). -/
theorem l2def_lambda (p₀ : Parameters) :
    ((lamX₁ p₀).gamma = p₀.gamma ∧ (lamX₁ p₀).alpha = p₀.alpha ∧ (lamX₁ p₀).s = 4 * (priorQuotient p₀).s)
    ∧ ((lamX₂ p₀).gamma = p₀.gamma ∧ (lamX₂ p₀).alpha = p₀.alpha ∧ (lamX₂ p₀).s = 2 * (priorQuotient p₀).s)
    ∧ ((lamMinus p₀ : PositiveReal) : ℝ) = 1 / (2 * regularizerR p₀ (lamX₁ p₀))
    ∧ ((lamPlus p₀ : PositiveReal) : ℝ) = 2 / regularizerR p₀ (lamX₁ p₀) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl⟩

open Classical in
/-- L2: the loss L^λ on Y = {true, false}. -/
theorem l2def_lamLoss (p₀ : Parameters) (μ : Measure ℝ) :
    lamLoss p₀ μ true = (if μ = quotientLaw (lamX₁ p₀) then 0 else if μ = quotientLaw (priorQuotient p₀) then 1 else 2)
    ∧ lamLoss p₀ μ false = (if μ = quotientLaw (lamX₂ p₀) then 0
        else (((1 + (lamPlus p₀).val * regularizerR p₀ (lamX₂ p₀) : ℝ)) : EReal)) := by
  constructor <;> simp only [lamLoss, ↓reduceIte, Bool.false_eq_true]

/-- L2: UO(w,y,x). -/
theorem l2def_UO (p₀ : Parameters) (w : PositiveReal) (y : Bool) (x : QuotientState) :
    UniqueOptimum p₀ w y x ↔ ∀ x', x' ≠ x → reducedObjective (lamLoss p₀) p₀ w x y < reducedObjective (lamLoss p₀) p₀ w x' y :=
  Iff.rfl

/-- L2: pKL, mix, mKV, mKJ, nr, I. -/
theorem l2def_mix (p₀ : Parameters) (x x₀ : QuotientState) :
    klDiv (quotientLaw x) (quotientLaw (priorQuotient p₀)) = predictiveKL p₀ x
    ∧ inverseGammaLaw ⟨x.alpha, x.alpha_pos⟩ ⟨x.s, x.s_pos⟩ = mixingLaw x
    ∧ klDiv (mixingLaw x) (mixingLaw x₀) = mixKLV x x₀
    ∧ klDiv (nonredundantJointLaw x) (nonredundantJointLaw x₀) = mixKLJoint x x₀
    ∧ ((nonredParams x).gamma = x.gamma ∧ (nonredParams x).nu = 1 ∧ (nonredParams x).alpha = x.alpha
      ∧ (nonredParams x).beta = x.s)
    ∧ x₀.alpha * Real.log (x.s / x₀.s) + Real.log (Real.Gamma x₀.alpha / Real.Gamma x.alpha)
        + (x.alpha - x₀.alpha) * digamma x.alpha - x.alpha + x.alpha * x₀.s / x.s = igKLForm x x₀ :=
  ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

end PostHocL2Audit
