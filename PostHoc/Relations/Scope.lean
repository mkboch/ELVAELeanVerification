import Official.M20
import Official.M21
import PostHoc.Relations.GroupC2

/-!
# proposition-10 and proposition-11: exact scope certificates

This module is the Lean part of `08_prop10_prop11_scope` (a byte-identical copy is stored there as
`ScopeCorollaries.lean`). For each proposition it gives:
* `L1_prop10` / `L1_prop11`: the literal L1 statement as a proposition schema;
* `B2_prop10` / `B2_prop11`: the types of the B2 declarations;
* `rel_*`: a structural proof that the B2 statement implies the L1 statement, audited to exclude the
  item's target theorems;
* a precise account of what B2 adds:
  - proposition-10: a pure quantifier gap ∀ prior vs ∃ prior (`forall_exists_gap`);
  - proposition-11: the extra γ = γ₀ case, which is equivalent to `0 ≤ R(x)`. B2's bound follows
    from L1's
    bound together with nonnegativity of R (`prop11_B2_bound_of_L1_and_nonneg`).
-/

-- cosmetic only: long statement lines are kept verbatim-readable
set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory NIGBottleneck

namespace PostHocFidelity

/-! ## proposition-10

L1_form (existential, as written): there exist one complete prior p₀, finite nonnegative losses (one input type
with two inputs y₁, y₂), and two weights w, w′ such that the original objective J₄ has unique global minimizers
p₁, p₂ (weight w; inputs y₁, y₂) and p₁′, p₂′ (weight w′). Their allocations ν are ordered oppositely:
ν(p₁) < ν(p₂) but ν(p₂′) < ν(p₁′). "Optimizers" = global minimizers of J₄. "Allocation" = the ν coordinate of the
optimizer. -/

def IsUniqueMinimizer (L : ReconstructionLoss Bool) (p₀ : Parameters) (w : PositiveReal) (y : Bool)
    (p : Parameters) : Prop :=
  ∀ q, originalObjective L q p₀ w y = ⨅ r, originalObjective L r p₀ w y ↔ q = p

def L1_prop10 : Prop :=
  ∃ (p₀ : Parameters) (L : ReconstructionLoss Bool) (w w' : PositiveReal) (p₁ p₂ p₁' p₂' : Parameters),
    (∀ μ y, 0 ≤ L μ y ∧ L μ y ≠ ⊤)
    ∧ IsUniqueMinimizer L p₀ w true p₁ ∧ IsUniqueMinimizer L p₀ w false p₂
    ∧ IsUniqueMinimizer L p₀ w' true p₁' ∧ IsUniqueMinimizer L p₀ w' false p₂'
    ∧ p₁.nu < p₂.nu ∧ p₂'.nu < p₁'.nu

/-- B2 (M20 `lambda_reverses_order`, for every complete prior). -/
def B2_prop10 : Prop :=
  ∀ p₀ : Parameters,
    (∀ (μ : Measure ℝ) (y : Bool), 0 ≤ lamLoss p₀ μ y ∧ lamLoss p₀ μ y ≠ ⊤)
    ∧ UniqueOptimum p₀ (lamMinus p₀) true (lamX₁ p₀) ∧ UniqueOptimum p₀ (lamMinus p₀) false (lamX₂ p₀)
    ∧ UniqueOptimum p₀ (lamPlus p₀) true (priorQuotient p₀) ∧ UniqueOptimum p₀ (lamPlus p₀) false (lamX₂ p₀)
    ∧ selNu p₀ (lamX₁ p₀) < selNu p₀ (lamX₂ p₀) ∧ selNu p₀ (lamX₂ p₀) < selNu p₀ (priorQuotient p₀)
    ∧ (∀ p, originalObjective (lamLoss p₀) p p₀ (lamMinus p₀) true = ⨅ q, originalObjective (lamLoss p₀) q p₀ (lamMinus p₀) true
        ↔ p = fiberParameters (lamX₁ p₀) (selTPos p₀ (lamX₁ p₀)))
    ∧ (∀ p, originalObjective (lamLoss p₀) p p₀ (lamPlus p₀) true = ⨅ q, originalObjective (lamLoss p₀) q p₀ (lamPlus p₀) true
        ↔ p = fiberParameters (priorQuotient p₀) (selTPos p₀ (priorQuotient p₀)))
    ∧ (∀ w : PositiveReal, w.val ≤ (lamPlus p₀).val → ∀ p,
        originalObjective (lamLoss p₀) p p₀ w false = ⨅ q, originalObjective (lamLoss p₀) q p₀ w false
          ↔ p = fiberParameters (lamX₂ p₀) (selTPos p₀ (lamX₂ p₀)))
    ∧ ∀ (x : QuotientState) (t : PositiveReal), (fiberParameters x t).nu = 1 / (t : ℝ)

/-- Foundational, not a proposition-10 target: ν_sel = 1/t_* (M06 `selNu_eq_inv_selT`). -/
def FoundNu : Prop := ∀ (p₀ : Parameters) (x : QuotientState), selNu p₀ x = 1 / selT p₀ x

/-- A concrete admissible complete prior (needed only to witness the existential). -/
def somePrior : Parameters := ⟨0, 1, 1, 1, one_pos, one_pos, one_pos⟩

theorem rel_prop10 : FoundNu → B2_prop10 → L1_prop10 := by
  intro hNu hB
  obtain ⟨hL, -, -, -, -, h12, h2bar, hm1, hp1, hy2, hnu⟩ := hB somePrior
  set p₀ := somePrior
  -- weights: w = λ₋, w′ = λ₊ ; λ₋ ≤ λ₊ follows from the defining formulas (R₁ > 0 is read off λ₋ > 0)
  have hR : 0 < regularizerR p₀ (lamX₁ p₀) := by
    have h := (lamMinus p₀).2
    change 0 < 1 / (2 * regularizerR p₀ (lamX₁ p₀)) at h
    have := one_div_pos.mp h
    linarith
  have hle : (lamMinus p₀).val ≤ (lamPlus p₀).val := by
    change 1 / (2 * regularizerR p₀ (lamX₁ p₀)) ≤ 2 / regularizerR p₀ (lamX₁ p₀)
    rw [div_le_div_iff₀ (by positivity) hR]
    nlinarith
  refine ⟨p₀, lamLoss p₀, lamMinus p₀, lamPlus p₀,
    fiberParameters (lamX₁ p₀) (selTPos p₀ (lamX₁ p₀)), fiberParameters (lamX₂ p₀) (selTPos p₀ (lamX₂ p₀)),
    fiberParameters (priorQuotient p₀) (selTPos p₀ (priorQuotient p₀)),
    fiberParameters (lamX₂ p₀) (selTPos p₀ (lamX₂ p₀)), hL, hm1, hy2 _ hle, hp1, hy2 _ le_rfl, ?_, ?_⟩
  · rw [hnu, hnu]
    change 1 / selT p₀ (lamX₁ p₀) < 1 / selT p₀ (lamX₂ p₀)
    rw [← hNu, ← hNu]
    exact h12
  · rw [hnu, hnu]
    change 1 / selT p₀ (lamX₂ p₀) < 1 / selT p₀ (priorQuotient p₀)
    rw [← hNu, ← hNu]
    exact h2bar

#relation_audit rel_prop10 [NIGBottleneck.lam_scores, NIGBottleneck.lamLoss_finite_nonneg,
  NIGBottleneck.optimum_y₁_minus, NIGBottleneck.optimum_y₁_plus, NIGBottleneck.optimum_y₂,
  NIGBottleneck.unique_original_minimizer, NIGBottleneck.lambda_reverses_order]

theorem B2_prop10_holds : B2_prop10 := lambda_reverses_order

theorem FoundNu_holds : FoundNu := selNu_eq_inv_selT

theorem L1_prop10_holds : L1_prop10 := rel_prop10 FoundNu_holds B2_prop10_holds

/-- What B2 adds to L1 is exactly a quantifier change. For every predicate P on complete priors,
`(∀ p₀, P p₀) → ∃ p₀, P p₀`; and there is a predicate for which the converse fails. (So the B2 ⇒ L1 direction
is pure logic. The L1 ⇒ B2 direction cannot be pure logic: it needs the construction for every prior.) -/
theorem forall_exists_gap :
    (∀ P : Parameters → Prop, (∀ p₀, P p₀) → ∃ p₀, P p₀)
    ∧ ∃ P : Parameters → Prop, (∃ p₀, P p₀) ∧ ¬ ∀ p₀, P p₀ :=
  ⟨fun P h => ⟨somePrior, h somePrior⟩,
    ⟨fun p => p.gamma = 0, ⟨somePrior, rfl⟩, fun h => by
      have := h ⟨1, 1, 1, 1, one_pos, one_pos, one_pos⟩
      norm_num at this⟩⟩

/-! ## proposition-11

L1_form: the family members are `l1Family x₀ n` (prior with predictive coordinates x₀ and ν₀ = n). In item 2 the
hypothesis γ ≠ γ₀ is a genuine restriction of the quantifier ("at every fixed state x … with γ≠γ₀"). -/

def L1_prop11 : Prop :=
  (∃ (x₀ : QuotientState) (n n' : ℝ) (hn : 0 < n) (hn' : 0 < n'),
      predictiveLaw (l1Family x₀ n hn) = predictiveLaw (l1Family x₀ n' hn')
      ∧ fiberParameters x₀ (l1tStar (l1Family x₀ n hn) x₀) ≠ fiberParameters x₀ (l1tStar (l1Family x₀ n' hn') x₀))
  ∧ (∃ (x₀ x : QuotientState) (n n' : ℝ) (hn : 0 < n) (hn' : 0 < n'),
      predictiveLaw (l1Family x₀ n hn) = predictiveLaw (l1Family x₀ n' hn')
      ∧ regularizerR (l1Family x₀ n hn) x ≠ regularizerR (l1Family x₀ n' hn') x)
  ∧ (∀ (x₀ : QuotientState) (n : ℝ) (hn : 0 < n),
      l1x0 (l1Family x₀ n hn) = x₀ ∧ fiberParameters x₀ (l1tStar (l1Family x₀ n hn) x₀) = l1Family x₀ n hn)
  ∧ (∀ (x₀ : QuotientState) (n : ℝ) (hn : 0 < n) (x : QuotientState), x.gamma ≠ x₀.gamma →
      n * x.alpha * (x.gamma - x₀.gamma) ^ 2 / (2 * x.s) ≤ regularizerR (l1Family x₀ n hn) x)
  ∧ (∀ (x₀ x : QuotientState), x.gamma ≠ x₀.gamma → ∀ K : ℝ,
      ∃ N, ∀ (n : ℝ) (hn : 0 < n), N ≤ n → K < regularizerR (l1Family x₀ n hn) x)

def B2_prop11 : Prop :=
  (∀ (p₀ p : Parameters), p₀.nu * p.alpha * (p.gamma - p₀.gamma) ^ 2 / (2 * p.beta) ≤ hierarchicalKL p p₀)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), p₀.nu * x.alpha * (x.gamma - p₀.gamma) ^ 2 / (2 * x.s) ≤ regularizerR p₀ x)
  ∧ (∀ (x₀ : QuotientState) (n : ℝ) (hn : 0 < n),
      priorQuotient (priorFamily x₀ n hn) = x₀ ∧ fiberParameters x₀ (selTPos (priorFamily x₀ n hn) x₀) = priorFamily x₀ n hn)
  ∧ (∀ (x₀ : QuotientState), predictiveLaw (priorFamily x₀ 1 one_pos) = predictiveLaw (priorFamily x₀ 2 two_pos)
      ∧ fiberParameters x₀ (selTPos (priorFamily x₀ 1 one_pos) x₀) ≠ fiberParameters x₀ (selTPos (priorFamily x₀ 2 two_pos) x₀))
  ∧ (∀ (x₀ x : QuotientState), x.gamma ≠ x₀.gamma → ∀ (K : ℝ),
      ∃ N, ∀ (n : ℝ) (hn : 0 < n), N ≤ n → K < regularizerR (priorFamily x₀ n hn) x)
  ∧ (∀ (x₀ x : QuotientState), x.gamma ≠ x₀.gamma →
      ∃ n n', ∃ (hn : 0 < n) (hn' : 0 < n'), predictiveLaw (priorFamily x₀ n hn) = predictiveLaw (priorFamily x₀ n' hn')
        ∧ regularizerR (priorFamily x₀ n hn) x ≠ regularizerR (priorFamily x₀ n' hn') x)

/-- A concrete quotient state and a second state with a different location. -/
def someState : QuotientState := ⟨0, 1, 1, one_pos, one_pos⟩
def otherState : QuotientState := ⟨1, 1, 1, one_pos, one_pos⟩

theorem rel_prop11 : B2_prop11 → L1_prop11 := by
  rintro ⟨-, hR, hsel, hnot, hdiv, hRnot⟩
  refine ⟨⟨someState, 1, 2, one_pos, two_pos, (hnot someState).1, (hnot someState).2⟩, ?_, hsel, ?_, hdiv⟩
  · obtain ⟨n, n', hn, hn', h1, h2⟩ := hRnot someState otherState (by norm_num [someState, otherState])
    exact ⟨someState, otherState, n, n', hn, hn', h1, h2⟩
  · intro x₀ n hn x _
    exact hR (l1Family x₀ n hn) x

#relation_audit rel_prop11 [NIGBottleneck.hierarchicalKL_ge_mean_term, NIGBottleneck.regularizerR_ge,
  NIGBottleneck.selected_at_x₀, NIGBottleneck.selected_not_determined_by_prior_law,
  NIGBottleneck.regularizerR_diverges, NIGBottleneck.regularizerR_not_determined_by_prior_law]

theorem B2_prop11_holds : B2_prop11 :=
  ⟨hierarchicalKL_ge_mean_term, regularizerR_ge, selected_at_x₀, selected_not_determined_by_prior_law,
    regularizerR_diverges, regularizerR_not_determined_by_prior_law⟩

theorem L1_prop11_holds : L1_prop11 := rel_prop11 B2_prop11_holds

/-- Every complete prior belongs to the fixed-marginal family of its own predictive coordinates. -/
lemma prior_mem_family (p₀ : Parameters) : l1Family (l1x0 p₀) p₀.nu p₀.nu_pos = p₀ := by
  obtain ⟨g, n, a, b, hn, ha, hb⟩ := p₀
  simp only [l1Family, l1x0, Parameters.mk.injEq, true_and]
  field_simp

/-- The scope difference in proposition-11 is exactly the case γ = γ₀, where the bound reads 0 ≤ R(x).
L1's bound (with γ ≠ γ₀), together with nonnegativity of R, yields B2's bound for every prior and every state.
Nonnegativity of R is a foundational fact (minimized KL ≥ 0, M07 `minimizedKL_nonneg`), not a
proposition-11 target. -/
theorem prop11_B2_bound_of_L1_and_nonneg (hL1 : L1_prop11)
    (hnn : ∀ (p₀ : Parameters) (x : QuotientState), 0 ≤ regularizerR p₀ x) :
    ∀ (p₀ : Parameters) (x : QuotientState),
      p₀.nu * x.alpha * (x.gamma - p₀.gamma) ^ 2 / (2 * x.s) ≤ regularizerR p₀ x := by
  intro p₀ x
  by_cases hγ : x.gamma = p₀.gamma
  · rw [hγ, sub_self]
    simpa using hnn p₀ x
  · have h := hL1.2.2.2.1 (l1x0 p₀) p₀.nu p₀.nu_pos x hγ
    rw [prior_mem_family] at h
    exact h

#relation_audit prop11_B2_bound_of_L1_and_nonneg [NIGBottleneck.regularizerR_ge,
  NIGBottleneck.hierarchicalKL_ge_mean_term]

theorem prop11_scope_extension_is_nonnegativity :
    ∀ (p₀ : Parameters) (x : QuotientState),
      p₀.nu * x.alpha * (x.gamma - p₀.gamma) ^ 2 / (2 * x.s) ≤ regularizerR p₀ x :=
  prop11_B2_bound_of_L1_and_nonneg L1_prop11_holds (fun p₀ x => minimizedKL_nonneg p₀ x)

end PostHocFidelity
