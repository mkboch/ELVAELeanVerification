import PostHoc.Relations.GroupA
import PostHoc.Relations.Scope
import PostHoc.PaperAudit.Selector
import Official.M15
import Official.M21

/-!
# Paper audit: proposition 2, proposition 10, proposition 11 and theorem 6 (Sections 3.1, 5.3, 6.3)

Post-arXiv paper-wide verification. The `L1_*`, `B2_*` and `rel_*` objects are the post-hoc relation
schemas of `PostHoc.Relations`; this module adds paper-level statements about them.
-/

noncomputable section

open MeasureTheory InformationTheory NIGBottleneck PostHocFidelity

namespace PaperAudit

/-! ## Proposition 2: what the target-excluding relation does and does not establish -/

/-- Proposition 2, formula correspondence: L1's literal closed form `K` and fiber formula `F`
coincide with B2's `nigKLClosedForm` and `fiberKLFormula` for all admissible parameters. The proof
uses no B2 theorem (definitional equality; audited below). -/
theorem paper_prop2_formula_correspondence :
    (∀ p p₀ : Parameters, l1K p p₀ = nigKLClosedForm p p₀)
      ∧ ∀ (p₀ : Parameters) (x : QuotientState) (t : ℝ),
          l1F p₀ x.gamma x.alpha x.s t = fiberKLFormula p₀ x t :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

#relation_audit paper_prop2_formula_correspondence [NIGBottleneck.integrable_nigLogRatio,
  NIGBottleneck.hierarchicalKL_eq_closedForm, NIGBottleneck.fiberKL_eq]

/-- Proposition 2, scope of the assumption of `rel_prop2`: its hypothesis `Found_prop2` (the
identification of the B2 log-ratio integral with Mathlib's KL divergence) already entails that every
NIG–NIG divergence is finite, which is part of proposition 2's own claim. -/
theorem paper_prop2_found_entails_finiteness (h : Found_prop2) :
    ∀ p p₀ : Parameters, klDiv (nigLaw p) (nigLaw p₀) ≠ ⊤ := by
  intro p p₀
  rw [h.1 p p₀]
  exact ENNReal.ofReal_ne_top

/-! ## Proposition 10: quantifier scope -/

/-- Proposition 10: B2's universally quantified reversal construction implies L1's existential claim
(given only the foundational identity `ν_sel = 1/t_*`). No converse is claimed. -/
theorem paper_prop10_B2_implies_L1 : B2_prop10 → L1_prop10 :=
  rel_prop10 FoundNu_holds

/-- Proposition 10: the B2 ⇒ L1 step is a quantifier specialization (`∀ p₀` to `∃ p₀`), which is not
reversible in general. -/
theorem paper_prop10_quantifier_gap :
    (∀ P : Parameters → Prop, (∀ p₀, P p₀) → ∃ p₀, P p₀)
      ∧ ∃ P : Parameters → Prop, (∃ p₀, P p₀) ∧ ¬ ∀ p₀, P p₀ :=
  forall_exists_gap

/-! ## Proposition 11: the lower bound and its domain -/

/-- Proposition 11 (B2 clause, all states): `R(q) ≥ ν₀ α (γ−γ₀)² / (2c)`. -/
theorem paper_prop11_B2_bound (p₀ : Parameters) (q : QuotientState) :
    p₀.nu * q.alpha * (q.gamma - p₀.gamma) ^ 2 / (2 * q.s) ≤ regularizerR p₀ q :=
  regularizerR_ge p₀ q

/-- Proposition 11: at `γ = γ₀` the added case of the B2 clause is exactly `R(q) ≥ 0`. -/
theorem paper_prop11_added_case (p₀ : Parameters) (q : QuotientState) (hγ : q.gamma = p₀.gamma) :
    (p₀.nu * q.alpha * (q.gamma - p₀.gamma) ^ 2 / (2 * q.s) ≤ regularizerR p₀ q)
      ↔ 0 ≤ regularizerR p₀ q := by
  rw [hγ, sub_self]
  simp

/-- Proposition 11: `R(q) ≥ 0`, because `R(q)` is the (real value of the) KL divergence of NIG laws
at the selected point. -/
theorem paper_prop11_R_nonneg (p₀ : Parameters) (q : QuotientState) :
    0 ≤ regularizerR p₀ q
      ∧ regularizerR p₀ q
        = (klDiv (nigLaw (paperFiberParams q (paperNuCan p₀ q) (paper_eq12_pos p₀ q)))
            (nigLaw p₀)).toReal :=
  ⟨regularizerR_nonneg p₀ q, by
    rw [(paper_R_is_fiber_minimum p₀ q).1, hierarchicalKL_eq_toReal_klDiv]⟩

/-- Proposition 11 (reverse direction): L1's clause (restricted to `γ ≠ γ₀`) together with `R ≥ 0`
yields B2's unrestricted clause. -/
theorem paper_prop11_reverse :
    L1_prop11 → (∀ (p₀ : Parameters) (q : QuotientState), 0 ≤ regularizerR p₀ q) →
      ∀ (p₀ : Parameters) (q : QuotientState),
        p₀.nu * q.alpha * (q.gamma - p₀.gamma) ^ 2 / (2 * q.s) ≤ regularizerR p₀ q :=
  prop11_B2_bound_of_L1_and_nonneg

/-- Proposition 11: B2 implies L1. -/
theorem paper_prop11_B2_implies_L1 : B2_prop11 → L1_prop11 := rel_prop11

/-! ## Theorem 6: the boundary `A = 0` -/

/-- Theorem 6: `A = α₀ > 0` for every admissible complete prior, so `A = 0` is outside the modeled
prior domain. -/
theorem paper_thm6_A_pos (p₀ : Parameters) : 0 < p₀.alpha := p₀.alpha_pos

theorem paper_thm6_A_zero_not_admissible : ¬ ∃ p₀ : Parameters, p₀.alpha = 0 := by
  rintro ⟨p₀, h⟩
  exact (p₀.alpha_pos.ne') h

/-- Theorem 6: the formal statement of the monotonicity of `M(A, n)` in `A` covers the formula-level
boundary `A = 0` (B2 `boundM_strictMono_A` with `0 ≤ A`). -/
theorem paper_thm6_formula_boundary {n A' : ℝ} (hn : 0 < n) (hA' : 0 < A') :
    boundM 0 n < boundM A' n :=
  boundM_strictMono_A le_rfl hA' hn

/-- Theorem 6 on the admissible domain: for complete priors with the same `n = ν₀`, `M` is strictly
increasing in `A = α₀`; every such `A` is positive. -/
theorem paper_thm6_admissible_monotone (p₀ p₀' : Parameters) (hn : p₀.nu = p₀'.nu)
    (hA : p₀.alpha < p₀'.alpha) :
    boundM p₀.alpha p₀.nu < boundM p₀'.alpha p₀'.nu := by
  rw [← hn]
  exact boundM_strictMono_A p₀.alpha_pos.le hA p₀.nu_pos

end PaperAudit
