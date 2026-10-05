import PostHoc.LeanL2.Items1
import PostHoc.Relations.GroupD

/-!
# L2 statement fidelity, items proposition-3 … corollary-2 (layer 2)

Method as in `Items1`. Where a B2 schema of `PostHoc.Relations` (`PostHocFidelity.B2_*`) already
lists exactly the B2 declarations translated by an item's L2 statements, it is reused. Declarations
translated in L2 but absent from that schema are added explicitly (`Extra*`).
-/

-- cosmetic only: long statement lines are kept verbatim-readable
set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory NIGBottleneck Filter Topology Asymptotics Set

namespace PostHocL2Audit

/-! ## proposition-3 -/

def ExtraProp3 : Prop :=
  (∀ (p₀ : Parameters) (x : QuotientState) (t : ℝ), FCoord p₀ (x.gamma, x.alpha, x.s) t = fiberKLFormula p₀ x t)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), tStarCoord p₀ (x.gamma, x.alpha, x.s) = selT p₀ x)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), RCoord p₀ (x.gamma, x.alpha, x.s) = regularizerR p₀ x)

def L2_prop3 : Prop :=
  ∀ p₀ : Parameters,
    (∀ (x : QuotientState) (t : ℝ), FCoord p₀ (x.gamma, x.alpha, x.s) t = fiberKLFormula p₀ x t
        ∧ tStarCoord p₀ (x.gamma, x.alpha, x.s) = selT p₀ x ∧ RCoord p₀ (x.gamma, x.alpha, x.s) = regularizerR p₀ x)
    ∧ AnalyticOnNhd ℝ (RCoord p₀) qDomain
    ∧ (∀ ξ ∈ qDomain, HasFDerivAt (RCoord p₀)
        ((fderiv ℝ (fun q : QCoord × ℝ => FCoord p₀ q.1 q.2) (ξ, tStarCoord p₀ ξ)).comp (ContinuousLinearMap.inl ℝ QCoord ℝ)) ξ)
    ∧ (∀ ξ ∈ qDomain,
        HasDerivAt (fun u : ℝ => RCoord p₀ (ξ + u • ((1 : ℝ), (0 : ℝ), (0 : ℝ))))
          (p₀.nu * ξ.2.1 * (ξ.1 - p₀.gamma) * (1 + tStarCoord p₀ ξ) / ξ.2.2) (0 : ℝ)
        ∧ HasDerivAt (fun u : ℝ => RCoord p₀ (ξ + u • ((0 : ℝ), (1 : ℝ), (0 : ℝ))))
          ((ξ.2.1 - p₀.alpha) * trigamma ξ.2.1 - 1 + BCoord p₀ ξ * (1 + tStarCoord p₀ ξ) / ξ.2.2) (0 : ℝ)
        ∧ HasDerivAt (fun u : ℝ => RCoord p₀ (ξ + u • ((0 : ℝ), (0 : ℝ), (1 : ℝ))))
          (p₀.alpha / ξ.2.2 - ξ.2.1 * BCoord p₀ ξ * (1 + tStarCoord p₀ ξ) / ξ.2.2 ^ 2) (0 : ℝ))
    ∧ (∀ (w : PositiveReal) (ξ : QCoord), ξ ∈ qDomain → ∀ (ℓ : QCoord → ℝ) (ℓ' : QCoord →L[ℝ] ℝ),
        HasFDerivAt ℓ ℓ' ξ → IsLocalMin (fun η => ℓ η + w.val * RCoord p₀ η) ξ → ℓ' + w.val • fderiv ℝ (RCoord p₀) ξ = 0)
    ∧ (∃ (L : ReconstructionLoss Unit) (w₁ w₂ : PositiveReal) (x₁ x₂ : QuotientState), x₁ ≠ x₂
        ∧ (∀ μ, 0 ≤ L μ () ∧ L μ () ≠ ⊤)
        ∧ (∀ x, x ≠ x₁ → reducedObjective L p₀ w₁ x₁ () < reducedObjective L p₀ w₁ x ())
        ∧ (∀ x, x ≠ x₂ → reducedObjective L p₀ w₂ x₂ () < reducedObjective L p₀ w₂ x ())
        ∧ ∀ (w : PositiveReal) (x : QuotientState) (t : PositiveReal),
          (∀ t', w.val * fiberKL p₀ x t ≤ w.val * fiberKL p₀ x t') ↔ t = selTPos p₀ x)

theorem rel2_prop3 : (PostHocFidelity.B2_prop3 ∧ ExtraProp3) ↔ L2_prop3 := by
  constructor
  · rintro ⟨hB, h1, h2, h3⟩ p₀
    obtain ⟨han, hfd, hg, ha, hs, hst, hex⟩ := hB p₀
    exact ⟨fun x t => ⟨h1 p₀ x t, h2 p₀ x, h3 p₀ x⟩, han, fun ξ hξ => hfd hξ, fun ξ hξ => ⟨hg hξ, ha hξ, hs hξ⟩,
      fun w ξ hξ ℓ ℓ' hℓ hmin => hst w hξ hℓ hmin, hex⟩
  · intro h
    refine ⟨fun p₀ => ?_, fun p₀ x t => ((h p₀).1 x t).1, fun p₀ x => ((h p₀).1 x 0).2.1,
      fun p₀ x => ((h p₀).1 x 0).2.2⟩
    obtain ⟨-, han, hfd, hdir, hst, hex⟩ := h p₀
    exact ⟨han, fun hξ => hfd _ hξ, fun hξ => (hdir _ hξ).1, fun hξ => (hdir _ hξ).2.1, fun hξ => (hdir _ hξ).2.2,
      fun {ℓ ℓ'} w {ξ} hξ hℓ hmin => hst w ξ hξ ℓ ℓ' hℓ hmin, hex⟩

#relation_audit rel2_prop3 [NIGBottleneck.FCoord_eq, NIGBottleneck.tStarCoord_eq, NIGBottleneck.RCoord_eq,
  NIGBottleneck.RCoord_analyticOnNhd, NIGBottleneck.hasFDerivAt_RCoord, NIGBottleneck.hasDerivAt_RCoord_gamma,
  NIGBottleneck.hasDerivAt_RCoord_alpha, NIGBottleneck.hasDerivAt_RCoord_s, NIGBottleneck.stationarity,
  NIGBottleneck.optimal_state_depends_on_weight]

theorem ExtraProp3_holds : ExtraProp3 := ⟨FCoord_eq, tStarCoord_eq, RCoord_eq⟩

/-! ## proposition-4 -/

def L2_prop4 : Prop :=
  ∀ (p₀ : Parameters) (lik : ℝ → ℝ), Measurable lik →
    (∀ p : Parameters, (∀ᵐ h ∂hierarchyLaw p, 0 < lik h.2) → Integrable (fun z => Real.log (lik z)) (predictiveLaw p) →
      -elbo p₀ lik p = likelihoodLoss lik (quotientLaw (quotientCoordinates p)) + hierarchicalKL p p₀
      ∧ ((-elbo p₀ lik p : ℝ) : EReal) = originalObjective (likelihoodReconstruction lik) p p₀ ⟨1, one_pos⟩ ()
      ∧ (0 < evidence p₀ lik → -elbo p₀ lik p = posteriorKL p₀ lik p - Real.log (evidence p₀ lik)))
    ∧ (∀ (x : QuotientState) (p : Parameters), quotientCoordinates p = x → (∀ᵐ z ∂quotientLaw x, 0 < lik z) →
        Integrable (fun z => Real.log (lik z)) (quotientLaw x) →
        elbo p₀ lik p ≤ elbo p₀ lik (fiberParameters x (selTPos p₀ x))
        ∧ (elbo p₀ lik p = elbo p₀ lik (fiberParameters x (selTPos p₀ x)) ↔ p = fiberParameters x (selTPos p₀ x)))

def ExtraProp4 : Prop :=
  ∀ {p₀ : Parameters} {lik : ℝ → ℝ}, Measurable lik → ∀ (p : Parameters),
    (∀ᵐ (h : HierarchySpace) ∂hierarchyLaw p, 0 < lik h.2) → Integrable (fun z => Real.log (lik z)) (predictiveLaw p) →
      ((-elbo p₀ lik p : ℝ) : EReal) = originalObjective (likelihoodReconstruction lik) p p₀ ⟨1, one_pos⟩ ()

theorem rel2_prop4 : (PostHocFidelity.B2_prop4 ∧ ExtraProp4) ↔ L2_prop4 := by
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩ p₀ lik hm
    exact ⟨fun p hpos hint => ⟨h1 hm p hpos hint, h4 hm p hpos hint, fun hev => h2 hm p hev hpos hint⟩,
      fun x p hx hpos hint => h3 hm x p hx hpos hint⟩
  · intro h
    exact ⟨⟨fun {p₀} {lik} hm p hpos hint => ((h p₀ lik hm).1 p hpos hint).1,
      fun {p₀} {lik} hm p hev hpos hint => ((h p₀ lik hm).1 p hpos hint).2.2 hev,
      fun {p₀} {lik} hm x p hx hpos hint => (h p₀ lik hm).2 x p hx hpos hint⟩,
      fun {p₀} {lik} hm p hpos hint => ((h p₀ lik hm).1 p hpos hint).2.1⟩

#relation_audit rel2_prop4 [NIGBottleneck.neg_elbo_eq, NIGBottleneck.neg_elbo_eq_originalObjective,
  NIGBottleneck.neg_elbo_eq_posteriorKL, NIGBottleneck.elbo_le_selected]

theorem ExtraProp4_holds : ExtraProp4 := fun hm p hpos hint => neg_elbo_eq_originalObjective hm p hpos hint

/-! ## proposition-5 -/

def L2_prop5 : Prop :=
  (∀ p : Parameters, 1 < p.alpha → totalVar p = uVar p + uEpi p ∧ totalVar p = quotientScale p / (p.alpha - 1))
  ∧ (∀ x : QuotientState, 1 < x.alpha → ∀ t : PositiveReal,
      (uVar (fiberParameters x t) = x.s / ((x.alpha - 1) * (1 + t)) ∧ uEpi (fiberParameters x t) = x.s * t / ((x.alpha - 1) * (1 + t)))
      ∧ (totalVar (fiberParameters x t) = uVar (fiberParameters x t) + uEpi (fiberParameters x t)
          ∧ totalVar (fiberParameters x t) = x.s / (x.alpha - 1))
      ∧ ∀ p₀ : Parameters,
          uEpi (fiberParameters x (selTPos p₀ x)) / uVar (fiberParameters x (selTPos p₀ x)) = selT p₀ x
          ∧ selT p₀ x = 1 / selNu p₀ x
          ∧ uEpi (fiberParameters x (selTPos p₀ x)) / totalVar (fiberParameters x (selTPos p₀ x)) = selT p₀ x / (1 + selT p₀ x)
          ∧ uVar (fiberParameters x (selTPos p₀ x)) / totalVar (fiberParameters x (selTPos p₀ x)) = 1 / (1 + selT p₀ x))
  ∧ (∀ p q : Parameters, predictiveLaw p = predictiveLaw q → totalVar p = totalVar q)
  ∧ (∀ x : QuotientState, 1 < x.alpha → ∀ a b : ℝ, 0 < a → 0 < b → a + b = x.s / (x.alpha - 1) →
      ∃ t : PositiveReal, uVar (fiberParameters x t) = a ∧ uEpi (fiberParameters x t) = b)

def ExtraProp5 : Prop :=
  (∀ (p : Parameters), 1 < p.alpha → totalVar p = uVar p + uEpi p)
  ∧ (∀ (p : Parameters), 1 < p.alpha → totalVar p = quotientScale p / (p.alpha - 1))

theorem rel2_prop5 : (PostHocFidelity.B2_prop5 ∧ ExtraProp5) ↔ L2_prop5 := by
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, e1, e2⟩
    exact ⟨fun p hp => ⟨e1 p hp, e2 p hp⟩, fun x hx t => ⟨⟨h1 x hx t, h2 x hx t⟩, h3 x hx t, fun p₀ => h4 x hx p₀⟩, h5, h6⟩
  · rintro ⟨h0, h1, h5, h6⟩
    exact ⟨⟨fun x hx t => (h1 x hx t).1.1, fun x hx t => (h1 x hx t).1.2, fun x hx t => (h1 x hx t).2.1,
      fun x hx p₀ => (h1 x hx 1).2.2 p₀, h5, h6⟩, fun p hp => (h0 p hp).1, fun p hp => (h0 p hp).2⟩

#relation_audit rel2_prop5 [NIGBottleneck.totalVar_eq_add, NIGBottleneck.totalVar_eq, NIGBottleneck.uVar_fiber,
  NIGBottleneck.uEpi_fiber, NIGBottleneck.totalVar_fiber, NIGBottleneck.selected_ratios,
  NIGBottleneck.totalVar_determined_by_predictiveLaw, NIGBottleneck.every_split_occurs]

theorem ExtraProp5_holds : ExtraProp5 := ⟨totalVar_eq_add, totalVar_eq⟩

/-! ## theorem-4, theorem-5, theorem-6, corollary-2, proposition-8
These L2 statements restate, clause for clause and with the same explicit hypotheses, exactly the B2 declarations
in the schemas `B2_theorem4`, `B2_theorem5`, `B2_theorem6`, `B2_cor2`, `B2_prop8`. L2_form for each item is
therefore taken to be the corresponding schema with L2's notation (certified in `Vocab`). The one structural
point is the theorem-6 monotonicity clause in `A`: L2 states it for A ≥ 0, matching B2, which is broader than
L1's A > 0. The theorem-6 statement uses M₀ = M(α₀,ν₀). -/

def L2_theorem4 : Prop := PostHocFidelity.B2_theorem4
def L2_theorem5 : Prop := PostHocFidelity.B2_theorem5
def L2_cor2 : Prop := PostHocFidelity.B2_cor2
def L2_prop8 : Prop := PostHocFidelity.B2_prop8

/-- theorem-6 in L2 form: M₀ written as M(α₀,ν₀) via `boundM` (L2's definition of M, certified equal to `boundM`), the
aggregate maximum written via `maxBound` (certified). -/
def L2_theorem6 : Prop := PostHocFidelity.B2_theorem6

theorem rel2_identity_items :
    (PostHocFidelity.B2_theorem4 ↔ L2_theorem4) ∧ (PostHocFidelity.B2_theorem5 ↔ L2_theorem5)
    ∧ (PostHocFidelity.B2_theorem6 ↔ L2_theorem6) ∧ (PostHocFidelity.B2_cor2 ↔ L2_cor2)
    ∧ (PostHocFidelity.B2_prop8 ↔ L2_prop8) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! ## proposition-7
Beyond the schema `B2_prop7`, L2 also states the statements collected in `ExtraProp7`. -/

def ExtraProp7 : Prop :=
  (∀ {A : ℝ}, 0 < A → Tendsto (fun d => d * TA A d) (𝓝[>] 0) (𝓝 (2 * A + 1)))
  ∧ (∀ {A : ℝ}, Tendsto (fun d => d * TA A d) atTop (𝓝 1))
  ∧ (∀ {A : ℝ}, 0 < A → TA A ~[𝓝[>] 0] fun d => (2 * A + 1) / d)
  ∧ (∀ {A : ℝ}, TA A ~[atTop] fun d => 1 / d)
  ∧ (∀ (s₀ e w n : ℝ), 0 ≤ n → ContinuousAt (scoreN s₀ e w) n)

def L2_prop7 : Prop := PostHocFidelity.B2_prop7 ∧ ExtraProp7

theorem rel2_prop7 : (PostHocFidelity.B2_prop7 ∧ ExtraProp7) ↔ L2_prop7 := Iff.rfl

#relation_audit rel2_prop7 [NIGBottleneck.tendsto_mul_TA_zero, NIGBottleneck.tendsto_mul_TA_atTop,
  NIGBottleneck.TA_isEquivalent_zero, NIGBottleneck.TA_isEquivalent_atTop, NIGBottleneck.scoreN_continuousAt]

theorem ExtraProp7_holds : ExtraProp7 :=
  ⟨fun hA => tendsto_mul_TA_zero hA, fun {_} => tendsto_mul_TA_atTop, fun hA => TA_isEquivalent_zero hA,
    fun {_} => TA_isEquivalent_atTop,
    scoreN_continuousAt⟩

/-! ## proposition-6
Beyond `B2_prop6`, L2 states the statements of `ExtraProp6`, and the ratio monotonicity (`ratioOfT_mono`),
which `B2_prop6` already contains. -/

def ExtraProp6 : Prop :=
  (∀ (p₀ : Parameters) (γ α : ℝ), 0 < α → ∀ (Q : ℝ), 0 < Q → ∃ x : QuotientState, x.gamma = γ ∧ x.alpha = α ∧ scoreQ p₀ x = Q)
  ∧ (∀ {A n : ℝ}, 0 < A → 0 < n →
      tOfScore A n 2 < (tOfScore A n 1 + tOfScore A n 3) / 2 ∧ nuOfScore A n 2 < (nuOfScore A n 1 + nuOfScore A n 3) / 2)

def L2_prop6 : Prop := PostHocFidelity.B2_prop6 ∧ ExtraProp6

theorem rel2_prop6 : (PostHocFidelity.B2_prop6 ∧ ExtraProp6) ↔ L2_prop6 := Iff.rfl

#relation_audit rel2_prop6 [NIGBottleneck.exists_state_score, NIGBottleneck.mean_score_same_mean_allocation_differs]

theorem ExtraProp6_holds : ExtraProp6 := ⟨exists_state_score, fun hA hn => mean_score_same_mean_allocation_differs hA hn⟩

end PostHocL2Audit
