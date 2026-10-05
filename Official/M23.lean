import Mathlib
import Official.M03
import Official.M05
import Official.M06
import Official.M08
import Official.M11
import Official.M15

/-!
# Nonselected points, local descent, and infinite-loss qualifications

Fix a quotient state `x`. (1) Reconstruction functionals take the same value
at every point of `F_x`. (2) With a finite reconstruction value and `λ > 0`, every nonselected point
has objective larger than the selected point by exactly `λ` times the gap, and is neither a global
nor a local minimizer (moving a small distance along the fiber toward `t_*` strictly decreases the
objective). (3) Every nonselected point is an admissible hierarchy with the same predictive law and
finite hierarchical KL; for `α > 1` its ratio `u_epi/u_var = t` is unbounded on the fiber, so the
bound of `Official.M15` is a consequence of selection. (4) With reconstruction value `−∞` on a
fiber, or an identically `+∞` loss, every point of the fiber has objective `−∞`, resp. `+∞`, so
conclusions that all minimizers are selected need the finite-loss qualification.
-/

noncomputable section

namespace NIGBottleneck

open Filter Set

section Phi

/-- `φ(u) = u − 1 − log u` is strictly decreasing on `(0, 1]`. -/
lemma phi_strictAnti {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v ≤ 1) :
    v - 1 - Real.log v < u - 1 - Real.log u := by
  have hv0 : 0 < v := by linarith
  have h := Real.log_lt_sub_one_of_pos (div_pos hu hv0) (by
    intro h; rw [div_eq_one_iff_eq hv0.ne'] at h; linarith)
  rw [Real.log_div hu.ne' hv0.ne'] at h
  have : (u / v - 1) ≤ u - v := by
    rw [div_sub_one hv0.ne', div_le_iff₀ hv0]
    nlinarith
  linarith

/-- `φ(u) = u − 1 − log u` is strictly increasing on `[1, ∞)`. -/
lemma phi_strictMono {u v : ℝ} (hu : 1 ≤ u) (huv : u < v) :
    u - 1 - Real.log u < v - 1 - Real.log v := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have h := Real.log_lt_sub_one_of_pos (div_pos hv0 hu0) (by
    intro h; rw [div_eq_one_iff_eq hu0.ne'] at h; linarith)
  rw [Real.log_div hv0.ne' hu0.ne'] at h
  have : (v / u - 1) ≤ v - u := by
    rw [div_sub_one hu0.ne', div_le_iff₀ hu0]
    nlinarith
  linarith

end Phi

variable (p₀ : Parameters) (x : QuotientState)

/-- Moving strictly toward `t_*` along the fiber strictly decreases the gap. -/
theorem fiberGap_lt_toward (t t' : ℝ) (ht : 0 < t)
    (hbetween : (t < t' ∧ t' ≤ selT p₀ x) ∨ (selT p₀ x ≤ t' ∧ t' < t)) :
    fiberGap p₀ x t' < fiberGap p₀ x t := by
  have hts := selT_pos p₀ x
  have hA := p₀.alpha_pos
  have h1 : 0 < 1 + selT p₀ x := by linarith
  unfold fiberGap
  rcases hbetween with ⟨h, h'⟩ | ⟨h, h'⟩
  · have ht' : 0 < t' := by linarith
    have e1 := phi_strictAnti (u := (1 + t) / (1 + selT p₀ x)) (v := (1 + t') / (1 + selT p₀ x))
      (by positivity) (div_lt_div_of_pos_right (by linarith) h1)
      (by rw [div_le_one h1]; linarith)
    have e2 := phi_strictAnti (u := t / selT p₀ x) (v := t' / selT p₀ x) (by positivity)
      (div_lt_div_of_pos_right h hts) (by rw [div_le_one hts]; linarith)
    nlinarith
  · have e1 := phi_strictMono (u := (1 + t') / (1 + selT p₀ x)) (v := (1 + t) / (1 + selT p₀ x))
      (by rw [le_div_iff₀ h1]; linarith) (div_lt_div_of_pos_right (by linarith) h1)
    have e2 := phi_strictMono (u := t' / selT p₀ x) (v := t / selT p₀ x)
      (by rw [le_div_iff₀ hts]; linarith) (div_lt_div_of_pos_right h' hts)
    nlinarith

variable {Y : Type*} (L : ReconstructionLoss Y) (w : PositiveReal) (y : Y)

/-- Reconstruction functionals of the specified kind assign exactly the
same value to every point of `F_x`; they cannot distinguish the fiber coordinate, whereas the
uncertainty split `u_epi/u_var = t` (for `α > 1`) does vary with it. -/
theorem reconstruction_blind (t t' : PositiveReal) :
    L (predictiveLaw (fiberParameters x t)) y = L (predictiveLaw (fiberParameters x t')) y := by
  rw [predictiveLaw_fiberParameters, predictiveLaw_fiberParameters]

omit L w y in
theorem split_on_fiber (hα : 1 < x.alpha) (t : PositiveReal) :
    uEpi (fiberParameters x t) / uVar (fiberParameters x t) = t := by
  have ht := t.property
  have hs := x.s_pos
  have h1 : 1 + (t : ℝ) ≠ 0 := by linarith
  have h2 : x.alpha - 1 ≠ 0 := by linarith
  rw [uEpi_fiber x hα, uVar_fiber x hα]
  field_simp

lemma objective_fiber_eq (hfin : L (quotientLaw x) y ≠ ⊥ ∧ L (quotientLaw x) y ≠ ⊤)
    (t : PositiveReal) :
    originalObjective L (fiberParameters x t) p₀ w y
      = ((L (quotientLaw x) y).toReal + w.val * regularizerR p₀ x
          + w.val * fiberGap p₀ x t : ℝ) := by
  rw [originalObjective_fiber, fiberKL_sub_regularizerR, reducedObjective, quotientLoss,
    EReal.coe_add, EReal.coe_add, EReal.coe_toReal hfin.2 hfin.1]

/-- With a finite reconstruction value and `λ > 0`, every point of the
fiber has objective equal to the selected objective plus `λ` times the gap, strictly larger at
every nonselected point. -/
theorem objective_gap (hfin : L (quotientLaw x) y ≠ ⊥ ∧ L (quotientLaw x) y ≠ ⊤)
    (t : PositiveReal) :
    originalObjective L (fiberParameters x t) p₀ w y
        = originalObjective L (fiberParameters x (selTPos p₀ x)) p₀ w y
          + ((w.val * fiberGap p₀ x t : ℝ) : EReal)
      ∧ ((t : ℝ) ≠ selT p₀ x → originalObjective L (fiberParameters x (selTPos p₀ x)) p₀ w y
          < originalObjective L (fiberParameters x t) p₀ w y) := by
  have hsel : originalObjective L (fiberParameters x (selTPos p₀ x)) p₀ w y
      = ((L (quotientLaw x) y).toReal + w.val * regularizerR p₀ x : ℝ) := by
    rw [originalObjective_selected, reducedObjective, quotientLoss, EReal.coe_add,
      EReal.coe_toReal hfin.2 hfin.1]
  have hfib := objective_fiber_eq p₀ x L w y hfin t
  refine ⟨by rw [hfib, hsel, ← EReal.coe_add], fun hne => ?_⟩
  rw [hsel, hfib, EReal.coe_lt_coe_iff]
  have := fiberGap_pos p₀ x t t.property hne
  have := mul_pos w.property this
  linarith

/-- No nonselected point is a global minimizer, nor a local one:
arbitrarily close to it on the fiber (in `t`, hence in `(ν, β) = (1/t, s/(1+t))`) there are points
with strictly smaller objective. -/
theorem nonselected_not_local_min (hfin : L (quotientLaw x) y ≠ ⊥ ∧ L (quotientLaw x) y ≠ ⊤)
    (t : PositiveReal) (hne : (t : ℝ) ≠ selT p₀ x) (ε : ℝ) (hε : 0 < ε) :
    ∃ t' : PositiveReal, |(t' : ℝ) - t| < ε
      ∧ originalObjective L (fiberParameters x t') p₀ w y
        < originalObjective L (fiberParameters x t) p₀ w y := by
  have ht := t.property
  have hts := selT_pos p₀ x
  set δ := min (ε / 2) (|selT p₀ x - t| / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by
    have : selT p₀ x - t ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    positivity)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδd : δ ≤ |selT p₀ x - t| / 2 := min_le_right _ _
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- move right, toward `t_*`
    have habs : |selT p₀ x - t| = selT p₀ x - t := abs_of_pos (by linarith)
    refine ⟨⟨t + δ, by linarith⟩, by simp [abs_of_pos hδ0, hδε], ?_⟩
    rw [objective_fiber_eq p₀ x L w y hfin, objective_fiber_eq p₀ x L w y hfin,
      EReal.coe_lt_coe_iff]
    have := mul_lt_mul_of_pos_left (fiberGap_lt_toward p₀ x t (t + δ) ht
      (Or.inl ⟨by linarith, by linarith⟩)) w.property
    simp only
    linarith
  · -- move left, toward `t_*`
    have habs : |selT p₀ x - t| = t - selT p₀ x := by
      rw [abs_sub_comm]; exact abs_of_pos (by linarith)
    refine ⟨⟨t - δ, by linarith⟩, by simp [abs_of_pos hδ0, hδε], ?_⟩
    rw [objective_fiber_eq p₀ x L w y hfin, objective_fiber_eq p₀ x L w y hfin,
      EReal.coe_lt_coe_iff]
    have := mul_lt_mul_of_pos_left (fiberGap_lt_toward p₀ x t (t - δ) ht
      (Or.inr ⟨by linarith, by linarith⟩)) w.property
    simp only
    linarith

/-- A nonselected point is not a local minimizer of `J₄` in the
parameter coordinates either: arbitrarily close to it in `(ν, β) = (1/t, s/(1+t))` (with `γ, α`
fixed) there are points of the fiber with strictly smaller objective. -/
theorem nonselected_not_local_min_coords
    (hfin : L (quotientLaw x) y ≠ ⊥ ∧ L (quotientLaw x) y ≠ ⊤)
    (t : PositiveReal) (hne : (t : ℝ) ≠ selT p₀ x) (ε : ℝ) (hε : 0 < ε) :
    ∃ t' : PositiveReal, |(fiberParameters x t').nu - (fiberParameters x t).nu| < ε
      ∧ |(fiberParameters x t').beta - (fiberParameters x t).beta| < ε
      ∧ originalObjective L (fiberParameters x t') p₀ w y
        < originalObjective L (fiberParameters x t) p₀ w y := by
  have ht := t.property
  have hc1 : ContinuousAt (fun u : ℝ => 1 / u) t := continuousAt_const.div continuousAt_id ht.ne'
  have hc2 : ContinuousAt (fun u : ℝ => x.s / (1 + u)) t :=
    continuousAt_const.div (continuousAt_const.add continuousAt_id) (by linarith)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.mp hc1 ε hε
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousAt_iff.mp hc2 ε hε
  obtain ⟨t', ht', hlt⟩ :=
    nonselected_not_local_min p₀ x L w y hfin t hne (min δ1 δ2) (lt_min hδ1 hδ2)
  refine ⟨t', ?_, ?_, hlt⟩
  · have := h1 (x := (t' : ℝ)) (by rw [Real.dist_eq]; exact lt_of_lt_of_le ht' (min_le_left _ _))
    rw [Real.dist_eq] at this
    exact this
  · have := h2 (x := (t' : ℝ)) (by rw [Real.dist_eq]; exact lt_of_lt_of_le ht' (min_le_right _ _))
    rw [Real.dist_eq] at this
    exact this

omit L w y in
/-- Every admissible nonselected point is a valid hierarchy with the
same predictive law and finite (integrable log-ratio) hierarchical KL. -/
theorem nonselected_valid (t : PositiveReal) :
    quotientCoordinates (fiberParameters x t) = x
      ∧ predictiveLaw (fiberParameters x t) = quotientLaw x
      ∧ MeasureTheory.Integrable
          (fun h => Real.log (nigDensity (fiberParameters x t) h / nigDensity p₀ h))
          (nigLaw (fiberParameters x t)) :=
  ⟨quotientCoordinates_fiberParameters x t, predictiveLaw_fiberParameters x t,
    integrable_nigLogRatio _ p₀⟩

omit L w y in
/-- For `α > 1`, the ratio `u_epi/u_var = t` is unbounded on the fiber;
in particular it exceeds `M(A,n)` at some nonselected point, so the bound of `Official.M15` is a
consequence of selection, not a property of the whole fiber. -/
theorem split_unbounded (hα : 1 < x.alpha) (K : ℝ) :
    ∃ t : PositiveReal, K < uEpi (fiberParameters x t) / uVar (fiberParameters x t)
      ∧ (boundM p₀.alpha p₀.nu < uEpi (fiberParameters x t) / uVar (fiberParameters x t)
          → (t : ℝ) ≠ selT p₀ x) := by
  refine ⟨⟨|K| + 1, by positivity⟩, ?_, ?_⟩
  · rw [split_on_fiber x hα]
    have := le_abs_self K
    change K < |K| + 1
    linarith
  · intro h heq
    rw [split_on_fiber x hα, heq] at h
    exact absurd h (not_lt.mpr (selT_lt_boundM p₀ x).2.le)

/-- If the reconstruction value on the fiber is `−∞`, every point of the
fiber has objective `−∞` (so every point, selected or not, is a global minimizer). -/
theorem objective_bot (hbot : L (quotientLaw x) y = ⊥) (t : PositiveReal) :
    originalObjective L (fiberParameters x t) p₀ w y = ⊥
      ∧ originalObjective L (fiberParameters x t) p₀ w y = ⨅ q, originalObjective L q p₀ w y := by
  have h : originalObjective L (fiberParameters x t) p₀ w y = ⊥ := by
    rw [originalObjective, predictiveLaw_fiberParameters, hbot, EReal.bot_add]
  exact ⟨h, le_antisymm (h ▸ bot_le) (iInf_le _ _)⟩

/-- With an identically `+∞` reconstruction loss, every point has
objective `+∞`, so every point, selected or not, is a (trivial) minimizer. -/
theorem objective_top (htop : ∀ μ, L μ y = ⊤) (p : Parameters) :
    originalObjective L p p₀ w y = ⊤
      ∧ originalObjective L p p₀ w y = ⨅ q, originalObjective L q p₀ w y := by
  have h : ∀ q, originalObjective L q p₀ w y = ⊤ := fun q => by
    rw [originalObjective, htop, EReal.top_add_coe]
  refine ⟨h p, ?_⟩
  rw [h p]
  exact (iInf_eq_top.mpr fun q => h q).symm

end NIGBottleneck
