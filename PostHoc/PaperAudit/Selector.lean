import PostHoc.PaperAudit.Equations
import Official.M08

/-!
# Paper audit: prior-relative selector and exact reduction (Eqs. (10)–(13), Section 3.2)

Post-arXiv paper-wide verification. The paper writes the selector in `ν` with `B = ν₀/2 + (α/c)[β₀ +
(ν₀/2)(γ−γ₀)²]` (Eq. (11)) and `ν_can = B − α₀ − 1/2 + √((B − α₀ − 1/2)² + 2B)` (Eq. (12)). The
formal corpus writes the same selector in `t = 1/ν` through `d = ν₀ + 2αB'/c` with `B' = β₀ +
(ν₀/2)(γ−γ₀)²`, so `d = 2B`.
-/

noncomputable section

open MeasureTheory InformationTheory NIGBottleneck

namespace PaperAudit

variable (p₀ : Parameters) (q : QuotientState)

/-- Paper Eq. (11). -/
def paperB : ℝ :=
  p₀.nu / 2 + q.alpha / q.s * (p₀.beta + p₀.nu / 2 * (q.gamma - p₀.gamma) ^ 2)

/-- Paper Eq. (12). -/
def paperNuCan : ℝ :=
  paperB p₀ q - p₀.alpha - 1 / 2
    + Real.sqrt ((paperB p₀ q - p₀.alpha - 1 / 2) ^ 2 + 2 * paperB p₀ q)

/-- Paper Eq. (13). -/
def paperBetaCan : ℝ :=
  q.s * paperNuCan p₀ q / (1 + paperNuCan p₀ q)

/-- Eq. (11): `B ≥ ν₀/2 > 0` for every admissible prior and quotient state. -/
theorem paper_eq11_B_pos : p₀.nu / 2 ≤ paperB p₀ q ∧ 0 < paperB p₀ q := by
  have := q.alpha_pos
  have := q.s_pos
  have hB := priorB_pos p₀ q
  have hn := p₀.nu_pos
  have h : 0 < q.alpha / q.s * (p₀.beta + p₀.nu / 2 * (q.gamma - p₀.gamma) ^ 2) := by
    unfold priorB at hB
    positivity
  unfold paperB
  constructor <;> linarith

/-- The paper's `2B` is the formal corpus's `d`. -/
theorem selD_eq_two_paperB : selD p₀ q = 2 * paperB p₀ q := by
  unfold selD paperB priorB
  ring

/-- Eq. (12): the paper's closed form is the formal selector `ν_sel = Φ_A(d)`. -/
theorem paper_eq12_nuCan : paperNuCan p₀ q = selNu p₀ q := by
  have hB := (paper_eq11_B_pos p₀ q).2
  rw [selNu, PhiA, selD_eq_two_paperB, selDisc, paperNuCan]
  set B := paperB p₀ q
  set A := p₀.alpha
  have hX : 0 ≤ (B - A - 1 / 2) ^ 2 + 2 * B := by positivity
  have h4 : (2 * B - 2 * A - 1) ^ 2 + 4 * (2 * B) = 4 * ((B - A - 1 / 2) ^ 2 + 2 * B) := by ring
  rw [h4, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
  ring

/-- Eq. (12) is well defined and positive: `ν_can > 0`. -/
theorem paper_eq12_pos : 0 < paperNuCan p₀ q := by
  rw [paper_eq12_nuCan, selNu_eq_inv_selT]
  exact one_div_pos.mpr (selT_pos p₀ q)

/-- Eq. (13): `β_can = cν_can/(1+ν_can)` is the formal selected `β_sel = c/(1 + t_*)`. -/
theorem paper_eq13_betaCan : paperBetaCan p₀ q = selBeta p₀ q := by
  have ht := selT_pos p₀ q
  rw [paperBetaCan, paper_eq12_nuCan, selNu_eq_inv_selT, selBeta]
  have h1 : 1 + selT p₀ q ≠ 0 := by linarith
  field_simp
  ring

/-- The paper's selected point `(γ, ν_can, α, β_can)` is the formal selected representative. -/
theorem paper_selected_point :
    paperFiberParams q (paperNuCan p₀ q) (paper_eq12_pos p₀ q)
      = fiberParameters q (selTPos p₀ q) := by
  rw [paperFiberParams_eq]
  congr 1
  apply Subtype.ext
  simp only [selTPos]
  rw [paper_eq12_nuCan, selNu_eq_inv_selT, one_div_one_div]

/-- Eq. (10): on the fiber `β = cν/(1+ν)`, `ν > 0`, the forward divergence to the complete prior has
the unique minimizer `ν = ν_can`, with `β = β_can`: every other fiber point has strictly larger
divergence. -/
theorem paper_eq10_unique_argmin (ν : ℝ) (hν : 0 < ν) (hne : ν ≠ paperNuCan p₀ q) :
    (klDiv (nigLaw (paperFiberParams q (paperNuCan p₀ q) (paper_eq12_pos p₀ q))) (nigLaw p₀)).toReal
      < (klDiv (nigLaw (paperFiberParams q ν hν)) (nigLaw p₀)).toReal := by
  rw [← hierarchicalKL_eq_toReal_klDiv, ← hierarchicalKL_eq_toReal_klDiv, paper_selected_point,
    paperFiberParams_eq]
  have hne' : ((⟨1 / ν, one_div_pos.mpr hν⟩ : PositiveReal) : ℝ) ≠ selT p₀ q := by
    intro h
    apply hne
    rw [paper_eq12_nuCan, selNu_eq_inv_selT]
    simp only at h
    rw [← h, one_div_one_div]
  exact fiberKL_selected_lt p₀ q _ hne'

/-- Section 3.2: the reduced regularizer `R(q)` is the divergence at the selected point, i.e. the
minimum of the divergence over the fiber. -/
theorem paper_R_is_fiber_minimum :
    regularizerR p₀ q
        = hierarchicalKL (paperFiberParams q (paperNuCan p₀ q) (paper_eq12_pos p₀ q)) p₀
      ∧ ∀ ν (hν : 0 < ν), regularizerR p₀ q ≤ hierarchicalKL (paperFiberParams q ν hν) p₀ := by
  refine ⟨by rw [paper_selected_point]; rfl, fun ν hν => ?_⟩
  have h := regularizerR_le_hierarchicalKL p₀ (paperFiberParams q ν hν)
  rwa [(paper_eq9_fiber q).1] at h

/-- Section 3.2: for every positive KL weight, the reduced three-coordinate objective `J₃(q) = ℓ(q)
+ λ R(q)` has the same infimum as the original four-coordinate objective. -/
theorem paper_reduction_same_infimum {Y : Type*} (L : ReconstructionLoss Y) (w : PositiveReal)
    (y : Y) :
    ⨅ p, originalObjective L p p₀ w y = ⨅ x, reducedObjective L p₀ w x y :=
  iInf_originalObjective_eq L p₀ w y

end PaperAudit
