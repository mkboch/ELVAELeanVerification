import Official.M19
import Official.M22
import Official.M23
import PostHoc.Relations.Scope

/-!
# L1 ↔ B2 formal relation certificates, group D

Items: proposition-9, proposition-12, proposition-13 (propositions 10 and 11 are in `Scope`).
Method as in `GroupA`.
-/

-- cosmetic only: long statement lines are kept verbatim-readable
set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory NIGBottleneck

namespace PostHocFidelity

/-! ## proposition-9

L1_form: the transformations are written field by field. "Moltiplied by κ²" for u_var, u_epi, V_z is stated for
α>1 (where they are defined). "No general invariance" and "orderings can change" are existential statements. -/

def l1ScaleP (κ : ℝ) (hκ : κ ≠ 0) (p : Parameters) : Parameters :=
  ⟨κ * p.gamma, p.nu, p.alpha, κ ^ 2 * p.beta, p.nu_pos, p.alpha_pos, by have := p.beta_pos; positivity⟩
def l1ScaleX (κ : ℝ) (hκ : κ ≠ 0) (x : QuotientState) : QuotientState :=
  ⟨κ * x.gamma, x.alpha, κ ^ 2 * x.s, x.alpha_pos, by have := x.s_pos; positivity⟩
def l1CenterX (p₀ : Parameters) (κ : ℝ) (hκ : κ ≠ 0) (x : QuotientState) : QuotientState :=
  ⟨p₀.gamma + κ * (x.gamma - p₀.gamma), x.alpha, κ ^ 2 * x.s, x.alpha_pos, by have := x.s_pos; positivity⟩

/-- A prior centered at 0, for the existential clauses. -/
def centeredPrior : Parameters := ⟨0, 1, 1, 1, one_pos, one_pos, one_pos⟩

def L1_prop9 : Prop :=
  (∀ (κ : ℝ) (hκ : κ ≠ 0) (p₀ : Parameters) (x : QuotientState),
      l1Q (l1ScaleP κ hκ p₀) (l1ScaleX κ hκ x) = l1Q p₀ x
      ∧ l1TA (l1ScaleP κ hκ p₀).alpha (l1d (l1ScaleP κ hκ p₀) (l1ScaleX κ hκ x)) = l1TA p₀.alpha (l1d p₀ x)
      ∧ l1PhiA (l1ScaleP κ hκ p₀).alpha (l1d (l1ScaleP κ hκ p₀) (l1ScaleX κ hκ x)) = l1PhiA p₀.alpha (l1d p₀ x)
      ∧ regularizerR (l1ScaleP κ hκ p₀) (l1ScaleX κ hκ x) = regularizerR p₀ x
      ∧ (l1ScaleX κ hκ x).s = κ ^ 2 * x.s
      ∧ (l1ScaleX κ hκ x).s / (l1ScaleX κ hκ x).alpha = κ ^ 2 * (x.s / x.alpha)
      ∧ l1b (l1ScaleP κ hκ p₀) = κ ^ 2 * l1b p₀)
  ∧ (∀ (κ : ℝ) (hκ : κ ≠ 0) (p : Parameters), quotientCoordinates (l1ScaleP κ hκ p) = l1ScaleX κ hκ (quotientCoordinates p))
  ∧ (∀ (κ : ℝ) (hκ : κ ≠ 0) (p : Parameters), 1 < p.alpha →
      l1uVar (l1ScaleP κ hκ p) = κ ^ 2 * l1uVar p ∧ l1uEpi (l1ScaleP κ hκ p) = κ ^ 2 * l1uEpi p
      ∧ l1Vz (l1ScaleP κ hκ p) = κ ^ 2 * l1Vz p)
  ∧ (∀ (p₀ : Parameters) (κ : ℝ) (hκ : κ ≠ 0) (x : QuotientState),
      l1Q p₀ (l1ScaleX κ hκ x) = x.alpha * ((κ * x.gamma - p₀.gamma) ^ 2 + l1b p₀) / (κ ^ 2 * x.s)
      ∧ l1Q p₀ (l1ScaleX κ hκ x) = ((x.gamma - p₀.gamma / κ) ^ 2 + l1b p₀ / κ ^ 2) / (x.s / x.alpha))
  ∧ (∃ (p₀ : Parameters) (x : QuotientState) (κ : ℝ) (hκ : κ ≠ 0), l1Q p₀ (l1ScaleX κ hκ x) ≠ l1Q p₀ x)
  ∧ (∀ (p₀ : Parameters), p₀.gamma = 0 → ∀ (x : QuotientState) {κ κ' : ℝ} (hκ : 0 < κ) (hκκ : κ < κ'),
      l1Q p₀ (l1ScaleX κ' (by linarith) x) < l1Q p₀ (l1ScaleX κ hκ.ne' x)
      ∧ l1TA p₀.alpha (l1d p₀ (l1ScaleX κ hκ.ne' x)) < l1TA p₀.alpha (l1d p₀ (l1ScaleX κ' (by linarith) x)))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) {κ κ' : ℝ} (hκ : 0 < κ) (hκκ : κ < κ'),
      l1Q p₀ (l1CenterX p₀ κ' (by linarith) x) < l1Q p₀ (l1CenterX p₀ κ hκ.ne' x)
      ∧ l1TA p₀.alpha (l1d p₀ (l1CenterX p₀ κ hκ.ne' x)) < l1TA p₀.alpha (l1d p₀ (l1CenterX p₀ κ' (by linarith) x)))
  ∧ (∃ (p₀ : Parameters) (x₁ x₂ : QuotientState) (κ κ' : ℝ) (hκ : κ ≠ 0) (hκ' : κ' ≠ 0),
      l1Q p₀ (l1ScaleX κ hκ x₁) < l1Q p₀ (l1ScaleX κ hκ x₂) ∧ l1Q p₀ (l1ScaleX κ' hκ' x₂) < l1Q p₀ (l1ScaleX κ' hκ' x₁))

def B2_prop9 : Prop :=
  (∀ (κ : ℝ) (hκ : κ ≠ 0) (p : Parameters), quotientCoordinates (scaleParams κ hκ p) = scaleState κ hκ (quotientCoordinates p))
  ∧ (∀ (κ : ℝ) (hκ : κ ≠ 0) (p₀ : Parameters) (x : QuotientState),
      (scaleState κ hκ x).s = κ ^ 2 * x.s ∧ (scaleState κ hκ x).s / (scaleState κ hκ x).alpha = κ ^ 2 * (x.s / x.alpha)
      ∧ bParam (scaleParams κ hκ p₀) = κ ^ 2 * bParam p₀)
  ∧ (∀ (κ : ℝ) (hκ : κ ≠ 0) (p₀ : Parameters) (x : QuotientState), scoreQ (scaleParams κ hκ p₀) (scaleState κ hκ x) = scoreQ p₀ x)
  ∧ (∀ (κ : ℝ) (hκ : κ ≠ 0) (p₀ : Parameters) (x : QuotientState),
      selT (scaleParams κ hκ p₀) (scaleState κ hκ x) = selT p₀ x ∧ selNu (scaleParams κ hκ p₀) (scaleState κ hκ x) = selNu p₀ x)
  ∧ (∀ (κ : ℝ) (hκ : κ ≠ 0) (p₀ : Parameters) (x : QuotientState),
      regularizerR (scaleParams κ hκ p₀) (scaleState κ hκ x) = regularizerR p₀ x)
  ∧ (∀ (κ : ℝ) (hκ : κ ≠ 0) (p : Parameters), 1 < p.alpha →
      uVar (scaleParams κ hκ p) = κ ^ 2 * uVar p ∧ uEpi (scaleParams κ hκ p) = κ ^ 2 * uEpi p
      ∧ totalVar (scaleParams κ hκ p) = κ ^ 2 * totalVar p)
  ∧ (∀ (p₀ : Parameters) (κ : ℝ) (hκ : κ ≠ 0) (x : QuotientState),
      scoreQ p₀ (rescaleState κ hκ x) = x.alpha * ((κ * x.gamma - p₀.gamma) ^ 2 + bParam p₀) / (κ ^ 2 * x.s)
      ∧ scoreQ p₀ (rescaleState κ hκ x) = ((x.gamma - p₀.gamma / κ) ^ 2 + bParam p₀ / κ ^ 2) / (x.s / x.alpha))
  ∧ (∀ (p₀ : Parameters), p₀.gamma = 0 → ∀ (x : QuotientState) {κ κ' : ℝ} (hκ : 0 < κ) (hκκ : κ < κ'),
      scoreQ p₀ (rescaleState κ' (by linarith) x) < scoreQ p₀ (rescaleState κ hκ.ne' x)
      ∧ selT p₀ (rescaleState κ hκ.ne' x) < selT p₀ (rescaleState κ' (by linarith) x))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) {κ κ' : ℝ} (hκ : 0 < κ) (hκκ : κ < κ'),
      scoreQ p₀ (rescaleAboutCenter p₀ κ hκ.ne' x) = ((x.gamma - p₀.gamma) ^ 2 + bParam p₀ / κ ^ 2) / (x.s / x.alpha)
      ∧ scoreQ p₀ (rescaleAboutCenter p₀ κ' (by linarith) x) < scoreQ p₀ (rescaleAboutCenter p₀ κ hκ.ne' x)
      ∧ selT p₀ (rescaleAboutCenter p₀ κ hκ.ne' x) < selT p₀ (rescaleAboutCenter p₀ κ' (by linarith) x))
  ∧ (∀ (p₀ : Parameters), p₀.gamma = 0 → ∀ (x : QuotientState), scoreQ p₀ (rescaleState 2 two_ne_zero x) ≠ scoreQ p₀ x)
  ∧ (∀ (p₀ : Parameters), p₀.gamma = 0 → ∃ x₁ x₂ κ κ', ∃ (hκ : κ ≠ 0) (hκ' : κ' ≠ 0),
      scoreQ p₀ (rescaleState κ hκ x₁) < scoreQ p₀ (rescaleState κ hκ x₂)
      ∧ scoreQ p₀ (rescaleState κ' hκ' x₂) < scoreQ p₀ (rescaleState κ' hκ' x₁)
      ∧ selT p₀ (rescaleState κ hκ x₂) < selT p₀ (rescaleState κ hκ x₁)
      ∧ selT p₀ (rescaleState κ' hκ' x₁) < selT p₀ (rescaleState κ' hκ' x₂))

theorem rel_prop9 : B2_prop9 → L1_prop9 := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨fun κ hκ p₀ x => ⟨h3 κ hκ p₀ x, (h4 κ hκ p₀ x).1, (h4 κ hκ p₀ x).2, h5 κ hκ p₀ x, (h2 κ hκ p₀ x).1,
      (h2 κ hκ p₀ x).2.1, (h2 κ hκ p₀ x).2.2⟩, h1, h6, h7, ?_, h8, fun p₀ x κ κ' hκ hκκ => ⟨(h9 p₀ x hκ hκκ).2.1,
      (h9 p₀ x hκ hκκ).2.2⟩, ?_⟩
  · exact ⟨centeredPrior, someState, 2, two_ne_zero, h10 centeredPrior rfl someState⟩
  · obtain ⟨x₁, x₂, κ, κ', hκ, hκ', hq1, hq2, -, -⟩ := h11 centeredPrior rfl
    exact ⟨centeredPrior, x₁, x₂, κ, κ', hκ, hκ', hq1, hq2⟩

#relation_audit rel_prop9 [NIGBottleneck.quotientCoordinates_scaleParams, NIGBottleneck.scale_s_w_b,
  NIGBottleneck.scoreQ_scale, NIGBottleneck.selT_selNu_scale, NIGBottleneck.regularizerR_scale,
  NIGBottleneck.uncertainty_scale, NIGBottleneck.scoreQ_rescale, NIGBottleneck.rescale_monotone,
  NIGBottleneck.rescaleAboutCenter_monotone, NIGBottleneck.no_general_invariance, NIGBottleneck.rescale_reverses_order]

theorem B2_prop9_holds : B2_prop9 :=
  ⟨quotientCoordinates_scaleParams, scale_s_w_b, scoreQ_scale, selT_selNu_scale, regularizerR_scale, uncertainty_scale,
    scoreQ_rescale, rescale_monotone, fun p₀ x _ _ hκ hκκ => rescaleAboutCenter_monotone p₀ x hκ hκκ,
    no_general_invariance, rescale_reverses_order⟩

theorem L1_prop9_holds : L1_prop9 := rel_prop9 B2_prop9_holds

/-! ## proposition-12

L1_form: KL is Mathlib `klDiv` (finite = `≠ ⊤`); f_x is `l1PredLaw`; IG laws are `l1IGLaw`; the joint laws have the
literal product densities; x₀ = `l1x0 p₀`. "In general not R" is existential. -/

def l1JointNR (x : QuotientState) : Measure (ℝ × ℝ) :=
  volume.withDensity (fun q => ENNReal.ofReal (l1IGDensity x.alpha x.s q.1 * l1NormalDensity x.gamma q.1 q.2))

def L1_prop12 : Prop :=
  (∀ (p₀ : Parameters) (x : QuotientState), klDiv (l1PredLaw x) (l1PredLaw (l1x0 p₀)) ≠ ⊤
      ∧ (klDiv (l1PredLaw x) (l1PredLaw (l1x0 p₀))).toReal ≤ regularizerR p₀ x
      ∧ ((klDiv (l1PredLaw x) (l1PredLaw (l1x0 p₀))).toReal = regularizerR p₀ x ↔ x = l1x0 p₀))
  ∧ (∀ p₀ : Parameters, (klDiv (l1PredLaw (l1x0 p₀)) (l1PredLaw (l1x0 p₀))).toReal = 0 ∧ regularizerR p₀ (l1x0 p₀) = 0)
  ∧ (∀ (x x' x₀ : QuotientState), x.alpha = x'.alpha → x.s = x'.s →
      klDiv (l1IGLaw x.alpha x.s) (l1IGLaw x₀.alpha x₀.s) = klDiv (l1IGLaw x'.alpha x'.s) (l1IGLaw x₀.alpha x₀.s))
  ∧ (∀ (x x₀ : QuotientState), klDiv (l1JointNR x) (l1JointNR x₀)
      = klDiv (l1IGLaw x.alpha x.s) (l1IGLaw x₀.alpha x₀.s) + ENNReal.ofReal (x.alpha * (x.gamma - x₀.gamma) ^ 2 / (2 * x.s)))
  ∧ (∀ (p₀ p₀' : Parameters), predictiveLaw p₀ = predictiveLaw p₀' → ∀ x : QuotientState,
      klDiv (l1IGLaw x.alpha x.s) (l1IGLaw (l1x0 p₀).alpha (l1x0 p₀).s) = klDiv (l1IGLaw x.alpha x.s) (l1IGLaw (l1x0 p₀').alpha (l1x0 p₀').s)
      ∧ klDiv (l1JointNR x) (l1JointNR (l1x0 p₀)) = klDiv (l1JointNR x) (l1JointNR (l1x0 p₀')))
  ∧ (∃ (p₀ : Parameters) (x : QuotientState),
      regularizerR p₀ x ≠ (klDiv (l1IGLaw x.alpha x.s) (l1IGLaw (l1x0 p₀).alpha (l1x0 p₀).s)).toReal
      ∧ regularizerR p₀ x ≠ (klDiv (l1JointNR x) (l1JointNR (l1x0 p₀))).toReal)

def B2_prop12 : Prop :=
  (∀ (p₀ : Parameters) (x : QuotientState), predictiveKL p₀ x ≠ ⊤ ∧ (predictiveKL p₀ x).toReal ≤ regularizerR p₀ x)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), (predictiveKL p₀ x).toReal = regularizerR p₀ x ↔ x = priorQuotient p₀)
  ∧ (∀ (x x' x₀ : QuotientState), x.alpha = x'.alpha → x.s = x'.s → mixKLV x x₀ = mixKLV x' x₀)
  ∧ (∀ (x x₀ : QuotientState), mixKLJoint x x₀ = mixKLV x x₀ + ENNReal.ofReal (x.alpha * (x.gamma - x₀.gamma) ^ 2 / (2 * x.s)))
  ∧ (∀ (p₀ p₀' : Parameters), predictiveLaw p₀ = predictiveLaw p₀' → ∀ (x : QuotientState),
      mixKLV x (priorQuotient p₀) = mixKLV x (priorQuotient p₀') ∧ mixKLJoint x (priorQuotient p₀) = mixKLJoint x (priorQuotient p₀'))
  ∧ (∀ (x₀ x : QuotientState), x.gamma ≠ x₀.gamma → ∃ n, ∃ (hn : 0 < n), priorQuotient (priorFamily x₀ n hn) = x₀
      ∧ regularizerR (priorFamily x₀ n hn) x ≠ (mixKLV x x₀).toReal ∧ regularizerR (priorFamily x₀ n hn) x ≠ (mixKLJoint x x₀).toReal)

/-- Foundational, not proposition-12 targets: R vanishes at the prior's state (M07 `minimizedKL_priorQuotient`);
the vanishing of the predictive KL at x₀ then follows from the equality case. -/
def Found12 : Prop := ∀ p₀ : Parameters, regularizerR p₀ (priorQuotient p₀) = 0

theorem rel_prop12 : Found12 → B2_prop12 → L1_prop12 := by
  rintro h0 ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨fun p₀ x => ⟨(h1 p₀ x).1, (h1 p₀ x).2, h2 p₀ x⟩, fun p₀ => ⟨((h2 p₀ (priorQuotient p₀)).mpr rfl).trans (h0 p₀), h0 p₀⟩, h3, h4, h5, ?_⟩
  obtain ⟨n, hn, hq, hne1, hne2⟩ := h6 someState otherState (by norm_num [someState, otherState])
  refine ⟨priorFamily someState n hn, otherState, ?_, ?_⟩
  · have : l1x0 (priorFamily someState n hn) = someState := hq
    rw [this]; exact hne1
  · have : l1x0 (priorFamily someState n hn) = someState := hq
    rw [this]; exact hne2

#relation_audit rel_prop12 [NIGBottleneck.predictiveKL_le_regularizerR, NIGBottleneck.predictiveKL_eq_iff,
  NIGBottleneck.klDiv_predictiveLaw_le, NIGBottleneck.nigLaw_eq_of_klDiv_eq, NIGBottleneck.mixKLV_ignores_gamma,
  NIGBottleneck.mixKLV_eq, NIGBottleneck.mixKLJoint_eq, NIGBottleneck.mix_depend_on_prior_predictive,
  NIGBottleneck.mix_ne_regularizerR]

theorem B2_prop12_holds : B2_prop12 :=
  ⟨predictiveKL_le_regularizerR, predictiveKL_eq_iff, mixKLV_ignores_gamma, mixKLJoint_eq,
    mix_depend_on_prior_predictive, mix_ne_regularizerR⟩

theorem L1_prop12_holds : L1_prop12 := rel_prop12 (fun p₀ => minimizedKL_priorQuotient p₀) B2_prop12_holds

/-! ## proposition-13

L1_form: "not a local minimizer of J₄" is read in the (ν,β) coordinates of the fiber points (γ,α fixed): every
neighborhood contains a point with strictly smaller objective. "Finite hierarchical KL" is `klDiv ≠ ⊤`.
"Arbitrarily large" ratio: for every K some fiber point exceeds K. The −∞ case adds that every fiber point
attains the infimum (so minimizers need not be selected). -/

def L1_prop13 : Prop :=
  ∀ (p₀ : Parameters) (x : QuotientState),
    (∀ {Y : Type} (L : ReconstructionLoss Y) (y : Y) (t t' : PositiveReal),
        L (predictiveLaw (fiberParameters x t)) y = L (predictiveLaw (fiberParameters x t')) y)
    ∧ (∀ {Y : Type} (L : ReconstructionLoss Y) (w : PositiveReal) (y : Y), L (l1PredLaw x) y ≠ ⊥ → L (l1PredLaw x) y ≠ ⊤ →
        ∀ t : PositiveReal,
          originalObjective L (fiberParameters x t) p₀ w y
            = originalObjective L (fiberParameters x (l1tStar p₀ x)) p₀ w y
              + ((w.val * l1Gap p₀.alpha t (l1TA p₀.alpha (l1d p₀ x)) : ℝ) : EReal)
          ∧ ((t : ℝ) ≠ l1TA p₀.alpha (l1d p₀ x) →
              originalObjective L (fiberParameters x (l1tStar p₀ x)) p₀ w y < originalObjective L (fiberParameters x t) p₀ w y
              ∧ ∀ ε : ℝ, 0 < ε → ∃ t' : PositiveReal, |(fiberParameters x t').nu - (fiberParameters x t).nu| < ε
                  ∧ |(fiberParameters x t').beta - (fiberParameters x t).beta| < ε
                  ∧ originalObjective L (fiberParameters x t') p₀ w y < originalObjective L (fiberParameters x t) p₀ w y))
    ∧ (∀ t : PositiveReal, quotientCoordinates (fiberParameters x t) = x ∧ predictiveLaw (fiberParameters x t) = l1PredLaw x
        ∧ klDiv (nigLaw (fiberParameters x t)) (nigLaw p₀) ≠ ⊤)
    ∧ (1 < x.alpha → (∀ t : PositiveReal, l1uEpi (fiberParameters x t) / l1uVar (fiberParameters x t) = t)
        ∧ ∀ K : ℝ, ∃ t : PositiveReal, K < l1uEpi (fiberParameters x t) / l1uVar (fiberParameters x t))
    ∧ (∀ {Y : Type} (L : ReconstructionLoss Y) (w : PositiveReal) (y : Y), L (l1PredLaw x) y = ⊥ →
        ∀ t : PositiveReal, originalObjective L (fiberParameters x t) p₀ w y = ⊥
          ∧ originalObjective L (fiberParameters x t) p₀ w y = ⨅ q, originalObjective L q p₀ w y)
    ∧ (∀ {Y : Type} (L : ReconstructionLoss Y) (w : PositiveReal) (y : Y), (∀ μ, L μ y = ⊤) →
        ∀ p : Parameters, originalObjective L p p₀ w y = ⊤)

def B2_prop13 : Prop :=
  (∀ (x : QuotientState) {Y : Type} (L : ReconstructionLoss Y) (y : Y) (t t' : PositiveReal),
      L (predictiveLaw (fiberParameters x t)) y = L (predictiveLaw (fiberParameters x t')) y)
  ∧ (∀ (x : QuotientState), 1 < x.alpha → ∀ (t : PositiveReal), uEpi (fiberParameters x t) / uVar (fiberParameters x t) = t)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) {Y : Type} (L : ReconstructionLoss Y) (w : PositiveReal) (y : Y),
      L (quotientLaw x) y ≠ ⊥ ∧ L (quotientLaw x) y ≠ ⊤ → ∀ (t : PositiveReal),
        originalObjective L (fiberParameters x t) p₀ w y = originalObjective L (fiberParameters x (selTPos p₀ x)) p₀ w y
          + ((w.val * fiberGap p₀ x t : ℝ) : EReal)
        ∧ ((t : ℝ) ≠ selT p₀ x → originalObjective L (fiberParameters x (selTPos p₀ x)) p₀ w y
            < originalObjective L (fiberParameters x t) p₀ w y))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) {Y : Type} (L : ReconstructionLoss Y) (w : PositiveReal) (y : Y),
      L (quotientLaw x) y ≠ ⊥ ∧ L (quotientLaw x) y ≠ ⊤ → ∀ (t : PositiveReal), (t : ℝ) ≠ selT p₀ x → ∀ (ε : ℝ), 0 < ε →
        ∃ t', |(fiberParameters x t').nu - (fiberParameters x t).nu| < ε ∧
          |(fiberParameters x t').beta - (fiberParameters x t).beta| < ε ∧
          originalObjective L (fiberParameters x t') p₀ w y < originalObjective L (fiberParameters x t) p₀ w y)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) (t : PositiveReal), quotientCoordinates (fiberParameters x t) = x ∧
      predictiveLaw (fiberParameters x t) = quotientLaw x ∧
      Integrable (fun h => Real.log (nigDensity (fiberParameters x t) h / nigDensity p₀ h)) (nigLaw (fiberParameters x t)))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), 1 < x.alpha → ∀ (K : ℝ), ∃ t,
      K < uEpi (fiberParameters x t) / uVar (fiberParameters x t)
      ∧ (boundM p₀.alpha p₀.nu < uEpi (fiberParameters x t) / uVar (fiberParameters x t) → (t : ℝ) ≠ selT p₀ x))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState) {Y : Type} (L : ReconstructionLoss Y) (w : PositiveReal) (y : Y),
      L (quotientLaw x) y = ⊥ → ∀ (t : PositiveReal), originalObjective L (fiberParameters x t) p₀ w y = ⊥
        ∧ originalObjective L (fiberParameters x t) p₀ w y = ⨅ q, originalObjective L q p₀ w y)
  ∧ (∀ (p₀ : Parameters) {Y : Type} (L : ReconstructionLoss Y) (w : PositiveReal) (y : Y), (∀ (μ : Measure ℝ), L μ y = ⊤) →
      ∀ (p : Parameters), originalObjective L p p₀ w y = ⊤ ∧ originalObjective L p p₀ w y = ⨅ q, originalObjective L q p₀ w y)

/-- Foundational, not a proposition-13 target: the NIG KL is finite (M22 `klDiv_nigLaw`). -/
def Found13 : Prop := ∀ p p₀ : Parameters, klDiv (nigLaw p) (nigLaw p₀) = ENNReal.ofReal (hierarchicalKL p p₀)

theorem rel_prop13 : Found13 → B2_prop13 → L1_prop13 := by
  rintro hK ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ p₀ x
  refine ⟨fun L y t t' => h1 x L y t t', fun L w y hb ht t => ⟨(h3 p₀ x L w y ⟨hb, ht⟩ t).1, fun hne =>
      ⟨(h3 p₀ x L w y ⟨hb, ht⟩ t).2 hne, h4 p₀ x L w y ⟨hb, ht⟩ t hne⟩⟩,
    fun t => ⟨(h5 p₀ x t).1, (h5 p₀ x t).2.1, by rw [hK]; exact ENNReal.ofReal_ne_top⟩,
    fun hα => ⟨h2 x hα, fun K => (h6 p₀ x hα K).imp fun t ht => ht.1⟩,
    fun L w y hb t => h7 p₀ x L w y hb t, fun L w y htop p => (h8 p₀ L w y htop p).1⟩

#relation_audit rel_prop13 [NIGBottleneck.reconstruction_blind, NIGBottleneck.split_on_fiber,
  NIGBottleneck.objective_fiber_eq, NIGBottleneck.objective_gap, NIGBottleneck.nonselected_not_local_min,
  NIGBottleneck.nonselected_not_local_min_coords, NIGBottleneck.nonselected_valid, NIGBottleneck.split_unbounded,
  NIGBottleneck.objective_bot, NIGBottleneck.objective_top]

theorem B2_prop13_holds : B2_prop13 :=
  ⟨fun x {_} L y t t' => reconstruction_blind x L y t t', split_on_fiber,
    fun p₀ x {_} L w y h t => objective_gap p₀ x L w y h t,
    fun p₀ x {_} L w y h t hne ε hε => nonselected_not_local_min_coords p₀ x L w y h t hne ε hε, nonselected_valid,
    split_unbounded, fun p₀ x {_} L w y h t => objective_bot p₀ x L w y h t,
    fun p₀ {_} L w y h p => objective_top p₀ L w y h p⟩

theorem L1_prop13_holds : L1_prop13 := rel_prop13 klDiv_nigLaw B2_prop13_holds

end PostHocFidelity
