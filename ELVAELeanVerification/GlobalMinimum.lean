import Mathlib
import ELVAELeanVerification.ObjectiveDerivative

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Unique global minimum of the ELVAE fiber objective

This module proves that the canonical selector `nuCan alpha0 B`
is the unique global minimizer of the fiber-restricted objective
on the admissible domain `ν > 0`, assuming `B > 0`.

The proof establishes:

1. the stationary quadratic factors around `nuCan`;
2. it is negative before `nuCan`;
3. it is positive after `nuCan`;
4. therefore the derivative of the actual fiber objective is
   negative before `nuCan` and positive after it;
5. hence the objective decreases up to `nuCan` and increases
   after `nuCan`;
6. `nuCan` is therefore the unique global minimizer on `(0, ∞)`.
-/

namespace ELVAE

/--
The stationary quadratic factors around its canonical positive root.
-/
theorem stationaryQuadratic_factor_nuCan
    (alpha0 B x : ℝ)
    (hB : 0 < B) :
    stationaryQuadratic alpha0 B x
      =
    (x - nuCan alpha0 B) *
      (x + nuCan alpha0 B +
        (2 * alpha0 + 1 - 2 * B)) := by
  have hroot :=
    nuCan_satisfies_stationary_quadratic alpha0 B hB
  unfold stationaryQuadratic
  nlinarith [hroot]

/--
The second factor in the quadratic factorization is positive
throughout the positive domain.
-/
theorem canonical_root_shift_positive
    (alpha0 B : ℝ)
    (hB : 0 < B) :
    0 <
      nuCan alpha0 B +
        (2 * alpha0 + 1 - 2 * B) := by
  have hr :
      0 < nuCan alpha0 B :=
    nuCan_positive alpha0 B hB
  have hroot :=
    nuCan_satisfies_stationary_quadratic alpha0 B hB
  have hprod :
      nuCan alpha0 B *
        (nuCan alpha0 B +
          (2 * alpha0 + 1 - 2 * B))
        =
      2 * B := by
    nlinarith [hroot]
  have hmul :
      0 <
        nuCan alpha0 B *
          (nuCan alpha0 B +
            (2 * alpha0 + 1 - 2 * B)) := by
    rw [hprod]
    nlinarith
  rcases mul_pos_iff.mp hmul with h | h
  · exact h.2
  · nlinarith [hr, h.1]

/--
Before the canonical root, the stationary quadratic is negative.
-/
theorem stationaryQuadratic_neg_before_nuCan
    (alpha0 B x : ℝ)
    (hB : 0 < B)
    (hx : 0 < x)
    (hxlt : x < nuCan alpha0 B) :
    stationaryQuadratic alpha0 B x < 0 := by
  have hfactor :=
    stationaryQuadratic_factor_nuCan alpha0 B x hB
  have hshift :=
    canonical_root_shift_positive alpha0 B hB
  have hsecond :
      0 <
        x + nuCan alpha0 B +
          (2 * alpha0 + 1 - 2 * B) := by
    nlinarith [hx, hshift]
  rw [hfactor]
  exact
    mul_neg_of_neg_of_pos
      (sub_neg.mpr hxlt)
      hsecond

/--
After the canonical root, the stationary quadratic is positive.
-/
theorem stationaryQuadratic_pos_after_nuCan
    (alpha0 B x : ℝ)
    (hB : 0 < B)
    (hx : 0 < x)
    (hxgt : nuCan alpha0 B < x) :
    0 < stationaryQuadratic alpha0 B x := by
  have hfactor :=
    stationaryQuadratic_factor_nuCan alpha0 B x hB
  have hshift :=
    canonical_root_shift_positive alpha0 B hB
  have hsecond :
      0 <
        x + nuCan alpha0 B +
          (2 * alpha0 + 1 - 2 * B) := by
    nlinarith [hx, hshift]
  rw [hfactor]
  exact
    mul_pos
      (sub_pos.mpr hxgt)
      hsecond

/--
The derivative expression is negative before the canonical point.
-/
theorem stationaryDerivative_neg_before_nuCan
    (alpha0 B x : ℝ)
    (hB : 0 < B)
    (hx : 0 < x)
    (hxlt : x < nuCan alpha0 B) :
    stationaryDerivative alpha0 B x < 0 := by
  have hmult :
      0 < 2 * x ^ 2 * (1 + x) :=
    derivative_multiplier_positive x hx
  have hquad :
      stationaryQuadratic alpha0 B x < 0 :=
    stationaryQuadratic_neg_before_nuCan
      alpha0 B x hB hx hxlt
  have hproduct :
      2 * x ^ 2 * (1 + x) *
          stationaryDerivative alpha0 B x < 0 := by
    rw [derivative_multiplier_identity alpha0 B x hx]
    exact hquad
  rcases mul_neg_iff.mp hproduct with h | h
  · exact h.2
  · nlinarith [hmult, h.1]

/--
The derivative expression is positive after the canonical point.
-/
theorem stationaryDerivative_pos_after_nuCan
    (alpha0 B x : ℝ)
    (hB : 0 < B)
    (hx : 0 < x)
    (hxgt : nuCan alpha0 B < x) :
    0 < stationaryDerivative alpha0 B x := by
  have hmult :
      0 < 2 * x ^ 2 * (1 + x) :=
    derivative_multiplier_positive x hx
  have hquad :
      0 < stationaryQuadratic alpha0 B x :=
    stationaryQuadratic_pos_after_nuCan
      alpha0 B x hB hx hxgt
  have hproduct :
      0 <
        2 * x ^ 2 * (1 + x) *
          stationaryDerivative alpha0 B x := by
    rw [derivative_multiplier_identity alpha0 B x hx]
    exact hquad
  rcases mul_pos_iff.mp hproduct with h | h
  · exact h.2
  · nlinarith [hmult, h.1]

/--
The derivative of the actual fiber objective is negative
strictly before the canonical selector.
-/
theorem fiberObjective_deriv_neg_before_nuCan
    (alpha0 B x : ℝ)
    (hB : 0 < B)
    (hx : 0 < x)
    (hxlt : x < nuCan alpha0 B) :
    deriv
        (fun y : ℝ => fiberObjective alpha0 B y)
        x < 0 := by
  rw [fiberObjective_deriv alpha0 B x hx]
  exact
    stationaryDerivative_neg_before_nuCan
      alpha0 B x hB hx hxlt

/--
The derivative of the actual fiber objective is positive
strictly after the canonical selector.
-/
theorem fiberObjective_deriv_pos_after_nuCan
    (alpha0 B x : ℝ)
    (hB : 0 < B)
    (hx : 0 < x)
    (hxgt : nuCan alpha0 B < x) :
    0 <
      deriv
        (fun y : ℝ => fiberObjective alpha0 B y)
        x := by
  rw [fiberObjective_deriv alpha0 B x hx]
  exact
    stationaryDerivative_pos_after_nuCan
      alpha0 B x hB hx hxgt

/--
Every positive point distinct from `nuCan` has strictly larger
fiber objective value.

This is the strict global-minimum statement.
-/
theorem fiberObjective_strict_global_min
    (alpha0 B x : ℝ)
    (hB : 0 < B)
    (hx : 0 < x)
    (hne : x ≠ nuCan alpha0 B) :
    fiberObjective alpha0 B (nuCan alpha0 B)
      <
    fiberObjective alpha0 B x := by
  have hr :
      0 < nuCan alpha0 B :=
    nuCan_positive alpha0 B hB
  by_cases hxlt : x < nuCan alpha0 B
  · have hcont :
        ContinuousOn
          (fun y : ℝ => fiberObjective alpha0 B y)
          (Set.Icc x (nuCan alpha0 B)) := by
      intro y hy
      have hypos : 0 < y :=
        lt_of_lt_of_le hx hy.1
      exact
        (fiberObjective_hasDerivAt
          alpha0 B y hypos).continuousAt.continuousWithinAt
    have hanti :
        StrictAntiOn
          (fun y : ℝ => fiberObjective alpha0 B y)
          (Set.Icc x (nuCan alpha0 B)) := by
      refine
        strictAntiOn_of_deriv_neg
          (convex_Icc x (nuCan alpha0 B))
          hcont
          ?_
      intro y hy
      have hyoo :
          y ∈ Set.Ioo x (nuCan alpha0 B) := by
        simpa using hy
      have hypos : 0 < y :=
        lt_trans hx hyoo.1
      exact
        fiberObjective_deriv_neg_before_nuCan
          alpha0 B y hB hypos hyoo.2
    have hxmem :
        x ∈ Set.Icc x (nuCan alpha0 B) :=
      ⟨le_rfl, hxlt.le⟩
    have hrmem :
        nuCan alpha0 B ∈
          Set.Icc x (nuCan alpha0 B) :=
      ⟨hxlt.le, le_rfl⟩
    exact hanti hxmem hrmem hxlt
  · have hrle : nuCan alpha0 B ≤ x :=
      le_of_not_gt hxlt
    have hrx : nuCan alpha0 B < x :=
      lt_of_le_of_ne hrle (Ne.symm hne)
    have hcont :
        ContinuousOn
          (fun y : ℝ => fiberObjective alpha0 B y)
          (Set.Icc (nuCan alpha0 B) x) := by
      intro y hy
      have hypos : 0 < y :=
        lt_of_lt_of_le hr hy.1
      exact
        (fiberObjective_hasDerivAt
          alpha0 B y hypos).continuousAt.continuousWithinAt
    have hmono :
        StrictMonoOn
          (fun y : ℝ => fiberObjective alpha0 B y)
          (Set.Icc (nuCan alpha0 B) x) := by
      refine
        strictMonoOn_of_deriv_pos
          (convex_Icc (nuCan alpha0 B) x)
          hcont
          ?_
      intro y hy
      have hyoo :
          y ∈ Set.Ioo (nuCan alpha0 B) x := by
        simpa using hy
      have hypos : 0 < y :=
        lt_trans hr hyoo.1
      exact
        fiberObjective_deriv_pos_after_nuCan
          alpha0 B y hB hypos hyoo.1
    have hrmem :
        nuCan alpha0 B ∈
          Set.Icc (nuCan alpha0 B) x :=
      ⟨le_rfl, hrx.le⟩
    have hxmem :
        x ∈ Set.Icc (nuCan alpha0 B) x :=
      ⟨hrx.le, le_rfl⟩
    exact hmono hrmem hxmem hrx

/--
Non-strict global-minimum form.
-/
theorem fiberObjective_global_min
    (alpha0 B x : ℝ)
    (hB : 0 < B)
    (hx : 0 < x) :
    fiberObjective alpha0 B (nuCan alpha0 B)
      ≤
    fiberObjective alpha0 B x := by
  by_cases h :
      x = nuCan alpha0 B
  · rw [h]
  · exact
      (fiberObjective_strict_global_min
        alpha0 B x hB hx h).le

/--
Equality with the minimum occurs exactly at the canonical selector.
-/
theorem fiberObjective_eq_min_iff
    (alpha0 B x : ℝ)
    (hB : 0 < B)
    (hx : 0 < x) :
    fiberObjective alpha0 B x
        =
      fiberObjective alpha0 B (nuCan alpha0 B)
      ↔
    x = nuCan alpha0 B := by
  constructor
  · intro heq
    by_contra hne
    have hstrict :=
      fiberObjective_strict_global_min
        alpha0 B x hB hx hne
    nlinarith
  · intro h
    rw [h]

/--
Final theorem: `nuCan` is the unique global minimizer of the
restricted objective over the positive real domain.
-/
theorem nuCan_unique_global_minimizer
    (alpha0 B : ℝ)
    (hB : 0 < B) :
    (∀ x : ℝ,
      0 < x →
      fiberObjective alpha0 B (nuCan alpha0 B)
        ≤
      fiberObjective alpha0 B x)
    ∧
    (∀ x : ℝ,
      0 < x →
      fiberObjective alpha0 B x
          =
        fiberObjective alpha0 B (nuCan alpha0 B) →
      x = nuCan alpha0 B) := by
  constructor
  · intro x hx
    exact
      fiberObjective_global_min
        alpha0 B x hB hx
  · intro x hx heq
    exact
      (fiberObjective_eq_min_iff
        alpha0 B x hB hx).mp heq

end ELVAE