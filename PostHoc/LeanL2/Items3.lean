import PostHoc.LeanL2.Items2

/-!
# L2 statement fidelity, items proposition-9 … proposition-13 (layer 2)

Method as in `Items1`/`Items2`. Where a B2 schema (`PostHocFidelity.B2_*`) already lists the B2
declarations translated by an item's L2 statements, it is reused; declarations translated in L2 but
absent from that schema are added explicitly (`Extra*`). For propositions 10 and 11 the L2 form is
additionally related to the L1 form, so the direction of the scope difference is checked from the L2
side.
-/

-- cosmetic only: long statement lines are kept verbatim-readable
set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory NIGBottleneck Filter Topology Set

namespace PostHocL2Audit

/-! ## proposition-9
L2 writes every rescaled state as σ_κ(x); B2's `rescaleState` is defined as `scaleState`
(`Official.M19`), so L2_prop9 below uses `scaleState` throughout. Beyond `B2_prop9`, L2 states the
scaling identity of the fiber divergence (`fiberKLFormula_scale`). -/

def L2_prop9 : Prop :=
  (∀ (κ : ℝ) (hκ : κ ≠ 0) (p : Parameters), quotientCoordinates (scaleParams κ hκ p) = scaleState κ hκ (quotientCoordinates p))
  ∧ (∀ (κ : ℝ) (hκ : κ ≠ 0) (p₀ : Parameters) (x : QuotientState),
      (scaleState κ hκ x).s = κ ^ 2 * x.s ∧ (scaleState κ hκ x).s / (scaleState κ hκ x).alpha = κ ^ 2 * (x.s / x.alpha)
      ∧ bParam (scaleParams κ hκ p₀) = κ ^ 2 * bParam p₀)
  ∧ (∀ (κ : ℝ) (hκ : κ ≠ 0) (p₀ : Parameters) (x : QuotientState),
      scoreQ (scaleParams κ hκ p₀) (scaleState κ hκ x) = scoreQ p₀ x
      ∧ selT (scaleParams κ hκ p₀) (scaleState κ hκ x) = selT p₀ x ∧ selNu (scaleParams κ hκ p₀) (scaleState κ hκ x) = selNu p₀ x)
  ∧ (∀ (κ : ℝ) (hκ : κ ≠ 0) (p₀ : Parameters) (x : QuotientState),
      (∀ t : ℝ, fiberKLFormula (scaleParams κ hκ p₀) (scaleState κ hκ x) t = fiberKLFormula p₀ x t)
      ∧ regularizerR (scaleParams κ hκ p₀) (scaleState κ hκ x) = regularizerR p₀ x)
  ∧ (∀ (κ : ℝ) (hκ : κ ≠ 0) (p : Parameters), 1 < p.alpha →
      uVar (scaleParams κ hκ p) = κ ^ 2 * uVar p ∧ uEpi (scaleParams κ hκ p) = κ ^ 2 * uEpi p
      ∧ totalVar (scaleParams κ hκ p) = κ ^ 2 * totalVar p)
  ∧ (∀ (p₀ : Parameters) (κ : ℝ) (hκ : κ ≠ 0) (x : QuotientState),
      scoreQ p₀ (scaleState κ hκ x) = x.alpha * ((κ * x.gamma - p₀.gamma) ^ 2 + bParam p₀) / (κ ^ 2 * x.s)
      ∧ scoreQ p₀ (scaleState κ hκ x) = ((x.gamma - p₀.gamma / κ) ^ 2 + bParam p₀ / κ ^ 2) / (x.s / x.alpha))
  ∧ (∀ (p₀ : Parameters), p₀.gamma = 0 → ∀ (x : QuotientState) {κ κ' : ℝ} (hκ : 0 < κ) (hκκ : κ < κ'),
      scoreQ p₀ (scaleState κ' (by linarith) x) < scoreQ p₀ (scaleState κ hκ.ne' x)
      ∧ selT p₀ (scaleState κ hκ.ne' x) < selT p₀ (scaleState κ' (by linarith) x))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) {κ κ' : ℝ} (hκ : 0 < κ) (hκκ : κ < κ'),
      scoreQ p₀ (rescaleAboutCenter p₀ κ hκ.ne' x) = ((x.gamma - p₀.gamma) ^ 2 + bParam p₀ / κ ^ 2) / (x.s / x.alpha)
      ∧ scoreQ p₀ (rescaleAboutCenter p₀ κ' (by linarith) x) < scoreQ p₀ (rescaleAboutCenter p₀ κ hκ.ne' x)
      ∧ selT p₀ (rescaleAboutCenter p₀ κ hκ.ne' x) < selT p₀ (rescaleAboutCenter p₀ κ' (by linarith) x))
  ∧ (∀ (p₀ : Parameters), p₀.gamma = 0 → ∀ (x : QuotientState), scoreQ p₀ (scaleState 2 two_ne_zero x) ≠ scoreQ p₀ x)
  ∧ (∀ (p₀ : Parameters), p₀.gamma = 0 → ∃ x₁ x₂ κ κ', ∃ (hκ : κ ≠ 0) (hκ' : κ' ≠ 0),
      scoreQ p₀ (scaleState κ hκ x₁) < scoreQ p₀ (scaleState κ hκ x₂)
      ∧ scoreQ p₀ (scaleState κ' hκ' x₂) < scoreQ p₀ (scaleState κ' hκ' x₁)
      ∧ selT p₀ (scaleState κ hκ x₂) < selT p₀ (scaleState κ hκ x₁)
      ∧ selT p₀ (scaleState κ' hκ' x₁) < selT p₀ (scaleState κ' hκ' x₂))

def ExtraProp9 : Prop :=
  ∀ (κ : ℝ) (hκ : κ ≠ 0) (p₀ : Parameters) (x : QuotientState) (t : ℝ),
    fiberKLFormula (scaleParams κ hκ p₀) (scaleState κ hκ x) t = fiberKLFormula p₀ x t

theorem rel2_prop9 : (PostHocFidelity.B2_prop9 ∧ ExtraProp9) ↔ L2_prop9 := by
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, e⟩
    exact ⟨h1, h2, fun κ hκ p₀ x => ⟨h3 κ hκ p₀ x, (h4 κ hκ p₀ x).1, (h4 κ hκ p₀ x).2⟩,
      fun κ hκ p₀ x => ⟨e κ hκ p₀ x, h5 κ hκ p₀ x⟩, h6, h7, h8, h9, h10, h11⟩
  · rintro ⟨h1, h2, h3, h4, h6, h7, h8, h9, h10, h11⟩
    exact ⟨⟨h1, h2, fun κ hκ p₀ x => (h3 κ hκ p₀ x).1, fun κ hκ p₀ x => (h3 κ hκ p₀ x).2,
      fun κ hκ p₀ x => (h4 κ hκ p₀ x).2, h6, h7, h8, h9, h10, h11⟩, fun κ hκ p₀ x => (h4 κ hκ p₀ x).1⟩

#relation_audit rel2_prop9 [NIGBottleneck.quotientCoordinates_scaleParams, NIGBottleneck.scale_s_w_b,
  NIGBottleneck.scoreQ_scale, NIGBottleneck.selT_selNu_scale, NIGBottleneck.fiberKLFormula_scale,
  NIGBottleneck.regularizerR_scale, NIGBottleneck.uncertainty_scale, NIGBottleneck.scoreQ_rescale,
  NIGBottleneck.rescale_monotone, NIGBottleneck.rescaleAboutCenter_monotone, NIGBottleneck.no_general_invariance,
  NIGBottleneck.rescale_reverses_order]

theorem ExtraProp9_holds : ExtraProp9 := fun κ hκ p₀ x t => fiberKLFormula_scale κ hκ p₀ x t

/-! ## proposition-10
Beyond `B2_prop10` (= the type of `lambda_reverses_order`), L2 states for the same, universally
quantified, prior p₀: the Q- and ν*-orderings (`lam_scores`); UO(w,false,X₂) for every w ≤ w₊ and
w₋ ≤ w₊ (`optimum_y₂`, `lamMinus_le_lamPlus`); and the general characterization
(`unique_original_minimizer`). -/

def ExtraProp10 : Prop :=
  ∀ p₀ : Parameters,
    (scoreQ p₀ (lamX₁ p₀) < scoreQ p₀ (lamX₂ p₀) ∧ scoreQ p₀ (lamX₂ p₀) < scoreQ p₀ (priorQuotient p₀)
      ∧ selNu p₀ (lamX₁ p₀) < selNu p₀ (lamX₂ p₀) ∧ selNu p₀ (lamX₂ p₀) < selNu p₀ (priorQuotient p₀))
    ∧ (∀ w : PositiveReal, w.val ≤ (lamPlus p₀).val → UniqueOptimum p₀ w false (lamX₂ p₀))
    ∧ (lamMinus p₀).val ≤ (lamPlus p₀).val
    ∧ (∀ (w : PositiveReal) (y : Bool) (x : QuotientState), UniqueOptimum p₀ w y x → ∀ p : Parameters,
        originalObjective (lamLoss p₀) p p₀ w y = ⨅ q, originalObjective (lamLoss p₀) q p₀ w y
          ↔ p = fiberParameters x (selTPos p₀ x))

/-- L2_form of proposition-10: everything L2 states, for every complete prior p₀ (as in B2). -/
def L2_prop10 : Prop := ExtraProp10 ∧ PostHocFidelity.B2_prop10

theorem rel2_prop10 : (PostHocFidelity.B2_prop10 ∧ ExtraProp10) ↔ L2_prop10 := And.comm

#relation_audit rel2_prop10 [NIGBottleneck.lam_scores, NIGBottleneck.lamLoss_finite_nonneg,
  NIGBottleneck.optimum_y₁_minus, NIGBottleneck.optimum_y₁_plus, NIGBottleneck.optimum_y₂,
  NIGBottleneck.lamMinus_le_lamPlus, NIGBottleneck.unique_original_minimizer, NIGBottleneck.lambda_reverses_order]

theorem ExtraProp10_holds : ExtraProp10 := fun p₀ =>
  ⟨lam_scores p₀, fun w hw => optimum_y₂ p₀ w hw, lamMinus_le_lamPlus p₀,
    fun w y x hx p => unique_original_minimizer p₀ w y x hx p⟩

/-- L2 ⇒ L1 for proposition-10 (through the structural relation of `Relations.Scope`; foundational
ν* = 1/t* only). -/
theorem rel2_prop10_L1 : PostHocFidelity.FoundNu → L2_prop10 → PostHocFidelity.L1_prop10 :=
  fun hNu h => PostHocFidelity.rel_prop10 hNu h.2

#relation_audit rel2_prop10_L1 [NIGBottleneck.lam_scores, NIGBottleneck.lamLoss_finite_nonneg,
  NIGBottleneck.optimum_y₁_minus, NIGBottleneck.optimum_y₁_plus, NIGBottleneck.optimum_y₂,
  NIGBottleneck.lamMinus_le_lamPlus, NIGBottleneck.unique_original_minimizer, NIGBottleneck.lambda_reverses_order]

/-! ## proposition-11
The six L2 statements restate, clause for clause and with the same hypotheses, exactly the six B2
declarations in `B2_prop11`; in particular L2 states the lower bound ν₀α(γ−γ₀)²/(2s) ≤ R_{p₀}(x) for every
p₀ and x (no restriction γ_x ≠ γ₀), as B2 does. -/

def L2_prop11 : Prop := PostHocFidelity.B2_prop11

theorem rel2_prop11 : PostHocFidelity.B2_prop11 ↔ L2_prop11 := Iff.rfl

/-- L2 ⇒ L1 for proposition-11 (through the structural relation of `Relations.Scope`). -/
theorem rel2_prop11_L1 : L2_prop11 → PostHocFidelity.L1_prop11 := PostHocFidelity.rel_prop11

#relation_audit rel2_prop11_L1 [NIGBottleneck.hierarchicalKL_ge_mean_term, NIGBottleneck.regularizerR_ge,
  NIGBottleneck.selected_at_x₀, NIGBottleneck.selected_not_determined_by_prior_law,
  NIGBottleneck.regularizerR_diverges, NIGBottleneck.regularizerR_not_determined_by_prior_law]

/-- What L2 adds to L1 in proposition-11 beyond a weaker-looking scope is only the γ = γ₀ case, i.e.
nonnegativity of R: L1 together with `0 ≤ R` gives L2's regularizer bound. -/
theorem prop11_L2_bound_of_L1_and_nonneg (hL1 : PostHocFidelity.L1_prop11)
    (hnn : ∀ (p₀ : Parameters) (x : QuotientState), 0 ≤ regularizerR p₀ x) :
    ∀ (p₀ : Parameters) (x : QuotientState),
      p₀.nu * x.alpha * (x.gamma - p₀.gamma) ^ 2 / (2 * x.s) ≤ regularizerR p₀ x :=
  PostHocFidelity.prop11_B2_bound_of_L1_and_nonneg hL1 hnn

#relation_audit prop11_L2_bound_of_L1_and_nonneg [NIGBottleneck.regularizerR_ge,
  NIGBottleneck.hierarchicalKL_ge_mean_term]

/-! ## proposition-12
Beyond `B2_prop12`, L2 states: klDiv(Pred p, Pred p₀) ≤ ofReal KL(p‖p₀) (`klDiv_predictiveLaw_le`); equality forces NIG(p)=NIG(p₀) (`nigLaw_eq_of_klDiv_eq`); mKJ(x,x₀)=ofReal KL(nr x‖nr x₀)
(`klDiv_nonred`) and mKV(x,x₀)=ofReal I(x,x₀) with 0≤I (`mixKLV_eq`). -/

def ExtraProp12 : Prop :=
  (∀ p p₀ : Parameters, klDiv (predictiveLaw p) (predictiveLaw p₀) ≤ ENNReal.ofReal (hierarchicalKL p p₀))
  ∧ (∀ p p₀ : Parameters, klDiv (predictiveLaw p) (predictiveLaw p₀) = ENNReal.ofReal (hierarchicalKL p p₀) →
      nigLaw p = nigLaw p₀)
  ∧ (∀ x x₀ : QuotientState, mixKLJoint x x₀ = ENNReal.ofReal (hierarchicalKL (nonredParams x) (nonredParams x₀)))
  ∧ (∀ x x₀ : QuotientState, mixKLV x x₀ = ENNReal.ofReal (igKLForm x x₀) ∧ 0 ≤ igKLForm x x₀)

def L2_prop12 : Prop := PostHocFidelity.B2_prop12 ∧ ExtraProp12

theorem rel2_prop12 : (PostHocFidelity.B2_prop12 ∧ ExtraProp12) ↔ L2_prop12 := Iff.rfl

#relation_audit rel2_prop12 [NIGBottleneck.klDiv_predictiveLaw_le, NIGBottleneck.predictiveKL_le_regularizerR,
  NIGBottleneck.nigLaw_eq_of_klDiv_eq, NIGBottleneck.predictiveKL_eq_iff, NIGBottleneck.mixKLV_ignores_gamma,
  NIGBottleneck.klDiv_nonred, NIGBottleneck.mixKLV_eq, NIGBottleneck.mixKLJoint_eq,
  NIGBottleneck.mix_depend_on_prior_predictive, NIGBottleneck.mix_ne_regularizerR]

theorem ExtraProp12_holds : ExtraProp12 :=
  ⟨fun p p₀ => klDiv_predictiveLaw_le p₀ p, fun p p₀ h => nigLaw_eq_of_klDiv_eq p p₀ h, klDiv_nonred, mixKLV_eq⟩

/-! ## proposition-13
Beyond `B2_prop13`, L2 states the t-coordinate form of "not a local minimizer": for t ≠ t* and ε>0
there is t' with |t'−t|<ε and 𝒥(φ_x(t'))<𝒥(φ_x(t)) (`nonselected_not_local_min`). The finiteness hypothesis
of these statements is carried only by a scoping sentence; it is present in B2 (and in L2_form). -/

def ExtraProp13 : Prop :=
  ∀ (p₀ : Parameters) (x : QuotientState) {Y : Type} (L : ReconstructionLoss Y) (w : PositiveReal) (y : Y),
    L (quotientLaw x) y ≠ ⊥ ∧ L (quotientLaw x) y ≠ ⊤ → ∀ (t : PositiveReal), (t : ℝ) ≠ selT p₀ x → ∀ (ε : ℝ), 0 < ε →
      ∃ t' : PositiveReal, |(t' : ℝ) - t| < ε
        ∧ originalObjective L (fiberParameters x t') p₀ w y < originalObjective L (fiberParameters x t) p₀ w y

def L2_prop13 : Prop := PostHocFidelity.B2_prop13 ∧ ExtraProp13

theorem rel2_prop13 : (PostHocFidelity.B2_prop13 ∧ ExtraProp13) ↔ L2_prop13 := Iff.rfl

#relation_audit rel2_prop13 [NIGBottleneck.reconstruction_blind, NIGBottleneck.split_on_fiber,
  NIGBottleneck.objective_gap, NIGBottleneck.nonselected_not_local_min, NIGBottleneck.nonselected_not_local_min_coords,
  NIGBottleneck.nonselected_valid, NIGBottleneck.split_unbounded, NIGBottleneck.objective_bot,
  NIGBottleneck.objective_top]

theorem ExtraProp13_holds : ExtraProp13 :=
  fun p₀ x {_} L w y h t hne ε hε => nonselected_not_local_min p₀ x L w y h t hne ε hε

end PostHocL2Audit
