import Mathlib
import PostHoc.E1.M01

/-! -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NS1

def def_019 (a : ℝ) : ℝ :=
  deriv (fun s : ℝ => Real.log (Real.Gamma s)) a

private def def_020 (a u : ℝ) : ℝ :=
  Real.exp (-u) * u ^ (a - 1)

private def def_021 (a u : ℝ) : ℝ :=
  def_020 a u * Real.log u

private theorem thm_001 {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioi (0 : ℝ), def_020 a u) = Real.Gamma a := by
  exact (Real.Gamma_eq_integral ha).symm

private theorem thm_002 {a : ℝ} (ha : 0 < a) :
    Integrable (def_020 a) (volume.restrict (Ioi (0 : ℝ))) := by
  by_contra h
  have hz := integral_undef h
  rw [thm_001 ha] at hz
  exact (ne_of_gt (Real.Gamma_pos_of_pos ha)) hz

private theorem thm_003 {u : ℝ} (hu : 0 < u) (a : ℝ) :
    0 ≤ def_020 a u := by
  unfold def_020
  positivity

private theorem thm_004 {u : ℝ} (hu : 0 < u)
    (a r : ℝ) :
    def_020 a u * u ^ r = def_020 (a + r) u := by
  unfold def_020
  rw [mul_assoc, ← Real.rpow_add hu]
  congr 2
  ring

private theorem thm_005 {u r : ℝ} (hu : 0 < u) (hr : 0 < r) :
    |Real.log u| ≤ (u ^ r + u ^ (-r)) / r := by
  have hp := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu r)
  have hn := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu (-r))
  rw [Real.log_rpow hu r] at hp
  rw [Real.log_rpow hu (-r)] at hn
  apply (le_div_iff₀ hr).2
  have habs : |Real.log u| * r = |Real.log u * r| := by
    rw [abs_mul, abs_of_pos hr]
  rw [habs]
  apply abs_le.mpr
  constructor
  · nlinarith [Real.rpow_pos_of_pos hu r]
  · nlinarith [Real.rpow_pos_of_pos hu (-r)]

private theorem thm_006 {a : ℝ} (ha : 0 < a) :
    Integrable (def_021 a) (volume.restrict (Ioi (0 : ℝ))) := by
  let r := a / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hap : 0 < a + r := by dsimp [r]; linarith
  have ham : 0 < a - r := by dsimp [r]; linarith
  have hi :
      Integrable
        (fun u => (def_020 (a + r) u + def_020 (a - r) u) / r)
        (volume.restrict (Ioi (0 : ℝ))) :=
    ((thm_002 hap).add
      (thm_002 ham)).div_const r
  apply hi.mono'
  · unfold def_021 def_020
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    calc
      ‖def_021 a u‖ =
          def_020 a u * |Real.log u| := by
        simp only [def_021, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (thm_003 hu a)]
      _ ≤ def_020 a u * ((u ^ r + u ^ (-r)) / r) :=
        mul_le_mul_of_nonneg_left (thm_005 hu hr)
          (thm_003 hu a)
      _ = (def_020 a u * u ^ r +
          def_020 a u * u ^ (-r)) / r := by ring
      _ = (def_020 (a + r) u + def_020 (a - r) u) / r := by
        rw [thm_004 hu a r, thm_004 hu a (-r)]
        rfl

private theorem thm_007 {u l s h : ℝ}
    (hu : 0 < u) (hls : l ≤ s) (hsh : s ≤ h) :
    u ^ s ≤ u ^ l + u ^ h := by
  by_cases hu1 : u ≤ 1
  · have ht : u ^ s ≤ u ^ l :=
      Real.rpow_le_rpow_of_exponent_ge hu hu1 hls
    exact ht.trans (le_add_of_nonneg_right (Real.rpow_nonneg hu.le h))
  · have ht : u ^ s ≤ u ^ h :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hu1)) hsh
    exact ht.trans (le_add_of_nonneg_left (Real.rpow_nonneg hu.le l))

private theorem thm_008 {u l s h : ℝ}
    (hu : 0 < u) (hls : l ≤ s) (hsh : s ≤ h) :
    ‖def_021 s u‖ ≤
      ‖def_021 l u‖ + ‖def_021 h u‖ := by
  have hp : u ^ (s - 1) ≤ u ^ (l - 1) + u ^ (h - 1) :=
    thm_007 hu (by linarith) (by linarith)
  have hm :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (-u)))
      (norm_nonneg (Real.log u))
  simp only [def_021, norm_mul,
    Real.norm_of_nonneg (thm_003 hu s),
    Real.norm_of_nonneg (thm_003 hu l),
    Real.norm_of_nonneg (thm_003 hu h)]
  simpa only [def_020, mul_add, add_mul] using hm

private theorem thm_009 {u : ℝ} (hu : 0 < u) (s : ℝ) :
    HasDerivAt (fun a => def_020 a u) (def_021 s u) s := by
  have hd :=
    (((hasDerivAt_id s).sub_const 1).const_mul (Real.log u)).exp
  simpa only [def_021, def_020, Real.rpow_def_of_pos hu,
    id_eq, mul_one, mul_assoc] using hd.const_mul (Real.exp (-u))

private theorem thm_010 {a : ℝ} (ha : 0 < a) :
    HasDerivAt Real.Gamma
      (∫ u in Ioi (0 : ℝ), def_021 a u) a := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let S := Ioo (a / 2) (3 * a / 2)
  let bound := fun u =>
    ‖def_021 (a / 2) u‖ + ‖def_021 (3 * a / 2) u‖
  have hS : S ∈ 𝓝 a :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas :
      ∀ᶠ s in 𝓝 a, AEStronglyMeasurable (def_020 s) μ :=
    Eventually.of_forall fun s => by
      unfold def_020
      fun_prop
  have hmeas' : AEStronglyMeasurable (def_021 a) μ := by
    unfold def_021 def_020
    fun_prop
  have hbound_int : Integrable bound μ :=
    (thm_006 (by linarith : 0 < a / 2)).norm.add
      (thm_006 (by linarith : 0 < 3 * a / 2)).norm
  have hbound :
      ∀ᵐ u ∂μ, ∀ s ∈ S, ‖def_021 s u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro s hs
    exact thm_008 hu hs.1.le hs.2.le
  have hdiff :
      ∀ᵐ u ∂μ, ∀ s ∈ S,
        HasDerivAt (fun v => def_020 v u) (def_021 s u) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro s _
    exact thm_009 hu s
  have hd :
      HasDerivAt (fun s => ∫ u, def_020 s u ∂μ)
        (∫ u, def_021 a u ∂μ) a :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le hS hmeas
      (thm_002 ha) hmeas' hbound hbound_int hdiff).2
  have he :
      Real.Gamma =ᶠ[𝓝 a] fun s => ∫ u, def_020 s u ∂μ := by
    filter_upwards [Ioi_mem_nhds ha] with s hs
    exact (thm_001 hs).symm
  exact hd.congr_of_eventuallyEq he

private theorem thm_011 {a : ℝ} (ha : 0 < a) :
    def_019 a =
      (∫ u in Ioi (0 : ℝ), def_021 a u) / Real.Gamma a := by
  unfold def_019
  exact ((thm_010 ha).log
    (ne_of_gt (Real.Gamma_pos_of_pos ha))).deriv

private theorem thm_012 {a : ℝ} (ha : a ≠ 0) :
    Real.Gamma (a + 1) = a * Real.Gamma a :=
  Real.Gamma_add_one ha

private theorem thm_013 (a b : abb_001) (x : ℝ) :
    0 ≤ def_001 (a : ℝ) (b : ℝ) x := by
  change 0 ≤ if 0 < x then
    (b : ℝ) ^ (a : ℝ) / Real.Gamma (a : ℝ) *
      x ^ (-(a : ℝ) - 1) * Real.exp (-(b : ℝ) / x) else 0
  split_ifs with hx
  · exact mul_nonneg
      (mul_nonneg
        (div_nonneg (Real.rpow_nonneg b.property.le _)
          (Real.Gamma_pos_of_pos a.property).le)
        (Real.rpow_nonneg hx.le _))
      (Real.exp_nonneg _)
  · exact le_rfl

private theorem thm_014 (a b : abb_001) :
    Measurable (def_001 (a : ℝ) (b : ℝ)) := by
  change Measurable (fun x : ℝ => if 0 < x then
    (b : ℝ) ^ (a : ℝ) / Real.Gamma (a : ℝ) *
      x ^ (-(a : ℝ) - 1) * Real.exp (-(b : ℝ) / x) else 0)
  apply Measurable.ite measurableSet_Ioi
  · fun_prop
  · exact measurable_const

private theorem thm_015 (a b : abb_001) (f : ℝ → ℝ) :
    (∫ x, f x ∂def_002 a b) =
      ∫ x in Ioi (0 : ℝ), def_001 (a : ℝ) (b : ℝ) x * f x := by
  have hm :
      Measurable (fun x => ENNReal.ofReal
        (def_001 (a : ℝ) (b : ℝ) x)) :=
    (thm_014 a b).ennreal_ofReal
  have hf :
      ∀ᵐ x ∂(volume : Measure ℝ),
        ENNReal.ofReal (def_001 (a : ℝ) (b : ℝ) x) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hw :
      (∫ x, f x ∂def_002 a b) =
        ∫ x, (ENNReal.ofReal
          (def_001 (a : ℝ) (b : ℝ) x)).toReal • f x := by
    exact integral_withDensity_eq_integral_toReal_smul hm hf f
  rw [hw]
  simp_rw [ENNReal.toReal_ofReal (thm_013 a b _), smul_eq_mul]
  calc
    (∫ x, def_001 (a : ℝ) (b : ℝ) x * f x) =
        ∫ x, (Ioi (0 : ℝ)).indicator
          (fun x => def_001 (a : ℝ) (b : ℝ) x * f x) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : 0 < x
      · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
      · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
        simp only [def_001, ite_eq_right hx, zero_mul]
    _ = _ := integral_indicator measurableSet_Ioi

private theorem thm_016 {a b u : ℝ}
    (hb : 0 < b) (hu : 0 < u) :
    (b / u ^ 2) * def_001 a b (b / u) =
      (Real.Gamma a)⁻¹ * def_020 a u := by
  have hb0 := ne_of_gt hb
  have hu0 := ne_of_gt hu
  have hquot : -b / (b / u) = -u := by
    field_simp
  have hbpow : b ^ a * b ^ (-a - 1) = b⁻¹ := by
    rw [← Real.rpow_add hb]
    have he : a + (-a - 1) = (-1 : ℝ) := by ring
    rw [he, Real.rpow_neg_one]
  have hupow : u ^ (-a - 1) = (u ^ (a - 1) * u ^ 2)⁻¹ := by
    have he : -a - 1 = -((a - 1) + 2) := by ring
    rw [he, Real.rpow_neg hu.le, Real.rpow_add hu]
    norm_num
  change b / u ^ 2 *
    (if 0 < b / u then
      b ^ a / Real.Gamma a * (b / u) ^ (-a - 1) * Real.exp (-b / (b / u))
      else 0) = (Real.Gamma a)⁻¹ * def_020 a u
  rw [ite_eq_left (div_pos hb hu), hquot,
    Real.div_rpow hb.le hu.le, hupow, div_inv_eq_mul]
  calc
    _ = ((u ^ 2)⁻¹ * u ^ 2) *
        ((b * (b ^ a * b ^ (-a - 1))) *
          ((Real.Gamma a)⁻¹ * def_020 a u)) := by
      unfold def_020
      ring
    _ = (b * (b ^ a * b ^ (-a - 1))) *
        ((Real.Gamma a)⁻¹ * def_020 a u) := by
      rw [inv_mul_cancel₀ (pow_ne_zero 2 hu0), one_mul]
    _ = _ := by
      rw [hbpow, mul_inv_cancel₀ hb0, one_mul]

private theorem thm_017 (a b : abb_001) (f : ℝ → ℝ) :
    (∫ x, f x ∂def_002 a b) =
      (Real.Gamma (a : ℝ))⁻¹ *
        ∫ u in Ioi (0 : ℝ), def_020 (a : ℝ) u * f ((b : ℝ) / u) := by
  have hb : 0 < (b : ℝ) := b.property
  have himage :
      (fun u : ℝ => (b : ℝ) / u) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact div_pos hb hu
    · intro hx
      refine ⟨(b : ℝ) / x, div_pos hb hx, ?_⟩
      field_simp
  have hinj : InjOn (fun u : ℝ => (b : ℝ) / u) (Ioi (0 : ℝ)) := by
    intro u hu v hv huv
    have he := (div_eq_div_iff (ne_of_gt hu) (ne_of_gt hv)).mp huv
    nlinarith
  have hderiv :
      ∀ u ∈ Ioi (0 : ℝ),
        HasDerivAt (fun v : ℝ => (b : ℝ) / v) (-(b : ℝ) / u ^ 2) u := by
    intro u hu
    have hd :=
      (hasDerivAt_const u (b : ℝ)).div (hasDerivAt_id u) (ne_of_gt hu)
    change HasDerivAt (fun v : ℝ => (b : ℝ) / v)
      ((0 * u - (b : ℝ) * 1) / u ^ 2) u at hd
    simpa only [zero_mul, mul_one, zero_sub] using hd
  have hderivWithin :
      ∀ u ∈ Ioi (0 : ℝ),
        HasDerivWithinAt (fun v : ℝ => (b : ℝ) / v)
          (-(b : ℝ) / u ^ 2) (Ioi (0 : ℝ)) u :=
    fun u hu => (hderiv u hu).hasDerivWithinAt
  have hchange :
      (∫ x in (fun u : ℝ => (b : ℝ) / u) '' Ioi (0 : ℝ),
        def_001 (a : ℝ) (b : ℝ) x * f x) =
      ∫ u in Ioi (0 : ℝ),
        |-(b : ℝ) / u ^ 2| •
          (def_001 (a : ℝ) (b : ℝ) ((b : ℝ) / u) *
            f ((b : ℝ) / u)) := by
    solve_by_elim [integral_image_eq_integral_abs_deriv_smul, measurableSet_Ioi]
  rw [himage] at hchange
  rw [thm_015, hchange]
  calc
    _ = ∫ u in Ioi (0 : ℝ), (Real.Gamma (a : ℝ))⁻¹ *
        (def_020 (a : ℝ) u * f ((b : ℝ) / u)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      have habs : |-(b : ℝ) / u ^ 2| = (b : ℝ) / u ^ 2 := by
        rw [abs_div, abs_neg, abs_of_pos hb, abs_of_nonneg (sq_nonneg u)]
      rw [smul_eq_mul, habs, ← mul_assoc,
        thm_016 hb hu, mul_assoc]
    _ = _ := integral_const_mul _ _

theorem thm_018 (a b : abb_001) :
    (∫ x : ℝ, x⁻¹ ∂def_002 a b) = (a : ℝ) / (b : ℝ) := by
  rw [thm_017]
  have he :
      (∫ u in Ioi (0 : ℝ),
        def_020 (a : ℝ) u * ((b : ℝ) / u)⁻¹) =
      ∫ u in Ioi (0 : ℝ), (b : ℝ)⁻¹ * def_020 ((a : ℝ) + 1) u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hm : def_020 (a : ℝ) u * u =
        def_020 ((a : ℝ) + 1) u := by
      simpa using thm_004 hu (a : ℝ) 1
    calc
      _ = (b : ℝ)⁻¹ * (def_020 (a : ℝ) u * u) := by
        field_simp
      _ = _ := by rw [hm]
  rw [he, integral_const_mul,
    thm_001 (by linarith [a.property] : 0 < (a : ℝ) + 1),
    thm_012 (ne_of_gt a.property)]
  have hg := ne_of_gt (Real.Gamma_pos_of_pos a.property)
  have hb := ne_of_gt b.property
  field_simp

private theorem thm_019 (a b : abb_001) (k : ℝ) :
    (∫ x : ℝ, (Real.log x + k) ∂def_002 a b) =
      Real.log (b : ℝ) - def_019 (a : ℝ) + k := by
  rw [thm_017]
  have he :
      (∫ u in Ioi (0 : ℝ),
        def_020 (a : ℝ) u * (Real.log ((b : ℝ) / u) + k)) =
      ∫ u in Ioi (0 : ℝ),
        (Real.log (b : ℝ) + k) * def_020 (a : ℝ) u -
          def_021 (a : ℝ) u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [Real.log_div (ne_of_gt b.property) (ne_of_gt hu)]
    unfold def_021
    ring
  rw [he, integral_sub
    ((thm_002 a.property).const_mul (Real.log (b : ℝ) + k))
    (thm_006 a.property)]
  rw [integral_const_mul, thm_001 a.property,
    thm_011 a.property]
  have hg := ne_of_gt (Real.Gamma_pos_of_pos a.property)
  calc
    _ = (Real.log (b : ℝ) + k) *
        (Real.Gamma (a : ℝ) * (Real.Gamma (a : ℝ))⁻¹) -
        (∫ u in Ioi (0 : ℝ), def_021 (a : ℝ) u) /
          Real.Gamma (a : ℝ) := by ring
    _ = _ := by
      rw [mul_inv_cancel₀ hg, mul_one]
      ring

theorem thm_020 (a b : abb_001) :
    (∫ x : ℝ, Real.log x ∂def_002 a b) =
      Real.log (b : ℝ) - def_019 (a : ℝ) := by
  simpa only [add_zero] using thm_019 a b 0

private theorem thm_021 (a b : abb_001) :
    Integrable (fun _ : ℝ => (1 : ℝ)) (def_002 a b) := by
  have hv : (∫ _ : ℝ, (1 : ℝ) ∂def_002 a b) = 1 := by
    rw [thm_017]
    simp only [mul_one]
    rw [thm_001 a.property,
      inv_mul_cancel₀ (ne_of_gt (Real.Gamma_pos_of_pos a.property))]
  by_contra h
  have hz := integral_undef h
  rw [hv] at hz
  exact one_ne_zero hz

theorem thm_022 (a b : abb_001) :
    Integrable Real.log (def_002 a b) := by
  let k : ℝ := 1 - (Real.log (b : ℝ) - def_019 (a : ℝ))
  have hv :
      (∫ x : ℝ, (Real.log x + k) ∂def_002 a b) = 1 := by
    rw [thm_019]
    dsimp only [k]
    ring
  have hi : Integrable (fun x : ℝ => Real.log x + k) (def_002 a b) := by
    by_contra h
    have hz := integral_undef h
    rw [hv] at hz
    exact one_ne_zero hz
  have hc : Integrable (fun _ : ℝ => k) (def_002 a b) := by
    simpa only [mul_one] using (thm_021 a b).const_mul k
  have hsub :
      Integrable (fun x : ℝ => (Real.log x + k) - k) (def_002 a b) :=
    hi.sub hc
  simpa only [add_sub_cancel_right] using hsub

theorem thm_023 (a b : abb_001) (ha : 1 < (a : ℝ)) :
    (∫ x : ℝ, x ∂def_002 a b) = (b : ℝ) / ((a : ℝ) - 1) := by
  have ham : 0 < (a : ℝ) - 1 := by linarith
  rw [thm_017]
  have he :
      (∫ u in Ioi (0 : ℝ),
        def_020 (a : ℝ) u * ((b : ℝ) / u)) =
      ∫ u in Ioi (0 : ℝ), (b : ℝ) * def_020 ((a : ℝ) - 1) u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    have hm : def_020 ((a : ℝ) - 1) u * u =
        def_020 (a : ℝ) u := by
      simpa using thm_004 hu ((a : ℝ) - 1) 1
    rw [← hm]
    calc
      _ = (b : ℝ) * def_020 ((a : ℝ) - 1) u * (u * u⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt hu), mul_one]
  rw [he, integral_const_mul, thm_001 ham]
  have hstep :
      Real.Gamma (a : ℝ) =
        ((a : ℝ) - 1) * Real.Gamma ((a : ℝ) - 1) := by
    simpa using thm_012 (ne_of_gt ham)
  rw [hstep]
  have hg := ne_of_gt (Real.Gamma_pos_of_pos ham)
  calc
    _ = ((b : ℝ) / ((a : ℝ) - 1)) *
        (Real.Gamma ((a : ℝ) - 1) * (Real.Gamma ((a : ℝ) - 1))⁻¹) := by
      rw [mul_inv_rev]
      ring
    _ = _ := by rw [mul_inv_cancel₀ hg, mul_one]

theorem thm_024 (a b : abb_001) :
    Integrable (fun x : ℝ => x⁻¹) (def_002 a b) := by
  by_contra h
  have hz := integral_undef h
  rw [thm_018] at hz
  exact (ne_of_gt (div_pos a.property b.property)) hz

theorem thm_025 (a b : abb_001) (ha : 1 < (a : ℝ)) :
    Integrable (fun x : ℝ => x) (def_002 a b) := by
  by_contra h
  have hz := integral_undef h
  rw [thm_023 a b ha] at hz
  exact (ne_of_gt (div_pos b.property (sub_pos.mpr ha))) hz

theorem thm_026 (a b c : abb_001) (x : ℝ) :
    def_001 (a : ℝ) ((c : ℝ) * (b : ℝ)) ((c : ℝ) * x) =
      def_001 (a : ℝ) (b : ℝ) x / (c : ℝ) := by
  have hc : 0 < (c : ℝ) := c.property
  have hc0 : (c : ℝ) ≠ 0 := ne_of_gt hc
  by_cases hx : 0 < x
  · have hquot :
        -((c : ℝ) * (b : ℝ)) / ((c : ℝ) * x) = -(b : ℝ) / x := by
      apply (div_eq_div_iff
        (mul_ne_zero hc0 (ne_of_gt hx)) (ne_of_gt hx)).2
      ring
    have hpow :
        (c : ℝ) ^ (a : ℝ) * (c : ℝ) ^ (-(a : ℝ) - 1) =
          (c : ℝ)⁻¹ := by
      rw [← Real.rpow_add hc]
      have hexp : (a : ℝ) + (-(a : ℝ) - 1) = (-1 : ℝ) := by ring
      rw [hexp, Real.rpow_neg_one]
    simp only [def_001, ite_eq_left hx,
      ite_eq_left (mul_pos hc hx)]
    change
      ((c : ℝ) * (b : ℝ)) ^ (a : ℝ) / Real.Gamma (a : ℝ) *
          ((c : ℝ) * x) ^ (-(a : ℝ) - 1) *
          Real.exp (-((c : ℝ) * (b : ℝ)) / ((c : ℝ) * x)) =
        ((b : ℝ) ^ (a : ℝ) / Real.Gamma (a : ℝ) *
          x ^ (-(a : ℝ) - 1) * Real.exp (-(b : ℝ) / x)) / (c : ℝ)
    rw [Real.mul_rpow hc.le b.property.le, Real.mul_rpow hc.le hx.le, hquot]
    calc
      _ = ((c : ℝ) ^ (a : ℝ) * (c : ℝ) ^ (-(a : ℝ) - 1)) *
          ((b : ℝ) ^ (a : ℝ) / Real.Gamma (a : ℝ) *
            x ^ (-(a : ℝ) - 1) * Real.exp (-(b : ℝ) / x)) := by ring
      _ = _ := by rw [hpow]; ring
  · have hcx : ¬ 0 < (c : ℝ) * x :=
      not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hc.le (le_of_not_gt hx))
    simp only [def_001, ite_eq_right hcx, ite_eq_right hx, zero_div]

theorem thm_027 (a b c : abb_001) (y : ℝ) :
    def_001 (a : ℝ) ((c : ℝ) * (b : ℝ)) y =
      (c : ℝ)⁻¹ *
        def_001 (a : ℝ) (b : ℝ) (y / (c : ℝ)) := by
  have hc0 : (c : ℝ) ≠ 0 := ne_of_gt c.property
  have hcancel : (c : ℝ) * (y / (c : ℝ)) = y := by
    calc
      _ = y * ((c : ℝ) * (c : ℝ)⁻¹) := by ring
      _ = y := by rw [mul_inv_cancel₀ hc0, mul_one]
  have hs := thm_026 a b c (y / (c : ℝ))
  rw [hcancel] at hs
  calc
    _ = def_001 (a : ℝ) (b : ℝ) (y / (c : ℝ)) / (c : ℝ) := hs
    _ = _ := by ring

private theorem thm_028 (μ : Measure ℝ) (f : ℝ → ℝ)
    (g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    Measure.map f (μ.withDensity (fun x => g (f x))) =
      (Measure.map f μ).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs]
  symm
  calc
    (∫⁻ y in s, g y ∂Measure.map f μ) =
        ∫⁻ y, s.indicator g y ∂Measure.map f μ := by
      rw [lintegral_indicator hs]
    _ = ∫⁻ x, s.indicator g (f x) ∂μ := by
      apply lintegral_map <;> fun_prop
    _ = ∫⁻ x, (f ⁻¹' s).indicator (fun x => g (f x)) x ∂μ := by
      apply lintegral_congr
      intro x
      by_cases hx : f x ∈ s <;> simp [hx]
    _ = _ := by
      rw [lintegral_indicator (hf hs)]

private theorem thm_029 {c : ℝ} (hc : 0 < c) :
    Measure.map (fun x : ℝ => c * x) volume = ENNReal.ofReal c⁻¹ • volume := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.smul_apply]
  change volume ((fun x : ℝ => c * x) ⁻¹' s) =
    ENNReal.ofReal c⁻¹ * volume s
  have h :
      volume ((fun x : ℝ => c * x) ⁻¹' s) =
        ENNReal.ofReal |c⁻¹| * volume s :=
    Real.volume_preimage_mul_left hc0 s
  simpa only [abs_of_pos (inv_pos.mpr hc)] using h

theorem thm_030 (a b c : abb_001) :
    Measure.map (fun x : ℝ => (c : ℝ) * x) (def_002 a b) =
      def_002 a ⟨(c : ℝ) * (b : ℝ), mul_pos c.property b.property⟩ := by
  have hc : 0 < (c : ℝ) := c.property
  have hc0 : (c : ℝ) ≠ 0 := ne_of_gt hc
  let g : ℝ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (def_001 (a : ℝ) (b : ℝ) (y / (c : ℝ)))
  have hg : Measurable g := by
    dsimp only [g]
    exact ((thm_014 a b).comp (by fun_prop)).ennreal_ofReal
  have hcomp :
      (fun x : ℝ => g ((c : ℝ) * x)) =
        fun x => ENNReal.ofReal (def_001 (a : ℝ) (b : ℝ) x) := by
    funext x
    dsimp only [g]
    have hx : (c : ℝ) * x / (c : ℝ) = x := by field_simp
    rw [hx]
  unfold def_002
  rw [← hcomp, thm_028 volume _ g (by fun_prop) hg,
    thm_029 hc]
  ext s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs,
    Measure.restrict_smul, lintegral_smul_measure]
  calc
    ENNReal.ofReal (c : ℝ)⁻¹ * ∫⁻ y in s, g y =
        ∫⁻ y in s, ENNReal.ofReal (c : ℝ)⁻¹ * g y :=
      (lintegral_const_mul _ hg).symm
    _ = _ := by
      apply lintegral_congr
      intro y
      dsimp only [g]
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
        ← thm_027 a b c y]

end NS1
