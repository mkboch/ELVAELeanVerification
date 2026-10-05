import PostHoc.Relations.GroupC

/-!
# L1 ↔ B2 formal relation certificates, group C2

Items: proposition-7, proposition-6, proposition-8. Method as in `GroupA`.
-/

-- cosmetic only: long statement lines are kept verbatim-readable
set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory NIGBottleneck Filter Topology Asymptotics Set

namespace PostHocFidelity

/-! ## proposition-7

L1, clause by clause:

L1_form: the score and t_* along each family are written literally as functions of the varying prior parameter
(δ² = e ≥ 0, w > 0), together with the identity that these are the selected values of the actual priors. ν_sel is
written 1/t_* (L1 theorem-2: ν_sel = 1/t_*). "Maximal possible value" is T_A(n), with t_* < T_A(n) for every
admissible score. The last sentence ("ties … can be distinguished") is not formalized: it is an informal remark
with no definite mathematical content. -/

def l1QB (e w b : ℝ) : ℝ := (e + b) / w
def l1QN (s₀ e w n : ℝ) : ℝ := (e + 2 * s₀ / (n + 1)) / w

def L1_prop7 : Prop :=
  (∀ (A n g₀ b : ℝ) (hb : 0 < b) (hA : 0 < A) (hn : 0 < n) (x : QuotientState),
      l1TA A (l1d (priorOfCoords g₀ b A n hb hA hn) x) = l1tQ A n (l1QB ((x.gamma - g₀) ^ 2) (x.s / x.alpha) b))
  ∧ (∀ e w : ℝ, Tendsto (l1QB e w) (𝓝[>] 0) (𝓝 (e / w)))
  ∧ (∀ e w : ℝ, 0 < w → Tendsto (fun b => l1QB e w b / b) atTop (𝓝 (1 / w)))
  ∧ (∀ A n w : ℝ, 0 < A → 0 < n → Tendsto (fun b => l1tQ A n (l1QB 0 w b)) (𝓝[>] 0) (𝓝 (l1TA A n))
      ∧ ∀ Q : ℝ, 0 < Q → l1tQ A n Q < l1TA A n)
  ∧ (∀ A n : ℝ, 0 < A → 0 < n → ∀ e₁ e₂ w₁ w₂ : ℝ, 0 ≤ e₂ → 0 < w₁ → w₁ < w₂ →
      ∀ᶠ b in atTop, l1QB e₂ w₂ b < l1QB e₁ w₁ b ∧ l1tQ A n (l1QB e₁ w₁ b) < l1tQ A n (l1QB e₂ w₂ b))
  ∧ (∀ A n e w : ℝ, 0 < n → 0 ≤ e → 0 < w →
      (fun b => l1tQ A n (l1QB e w b)) ~[atTop] (fun b => w / (n * b))
      ∧ (fun b => 1 / l1tQ A n (l1QB e w b)) ~[atTop] (fun b => n * b / w))
  ∧ (∀ (x₀ x : QuotientState) (n : ℝ) (hn : 0 < n),
      l1TA (l1Family x₀ n hn).alpha (l1d (l1Family x₀ n hn) x)
        = l1tQ x₀.alpha n (l1QN x₀.s ((x.gamma - x₀.gamma) ^ 2) (x.s / x.alpha) n))
  ∧ (∀ s₀ e w : ℝ, Tendsto (l1QN s₀ e w) (𝓝[>] 0) (𝓝 ((e + 2 * s₀) / w))
      ∧ Tendsto (l1QN s₀ e w) atTop (𝓝 (e / w)))
  ∧ (∀ A s₀ e w : ℝ, 0 < A → 0 < s₀ → 0 ≤ e → 0 < w →
      (fun n => l1tQ A n (l1QN s₀ e w n)) ~[𝓝[>] 0] (fun n => (2 * A + 1) / (n * (1 + (e + 2 * s₀) / w)))
      ∧ (fun n => 1 / l1tQ A n (l1QN s₀ e w n)) ~[𝓝[>] 0] (fun n => n * (1 + (e + 2 * s₀) / w) / (2 * A + 1)))
  ∧ (∀ A s₀ e w : ℝ, 0 < s₀ → 0 ≤ e → 0 < w →
      (fun n => l1tQ A n (l1QN s₀ e w n)) ~[atTop] (fun n => 1 / (n * (1 + e / w)))
      ∧ (fun n => 1 / l1tQ A n (l1QN s₀ e w n)) ~[atTop] (fun n => n * (1 + e / w)))
  ∧ (∀ A s₀ e w : ℝ, 0 < A → 0 < s₀ → 0 ≤ e → 0 < w →
      Tendsto (fun n => l1tQ A n (l1QN s₀ e w n) / (1 + l1tQ A n (l1QN s₀ e w n))) (𝓝[>] 0) (𝓝 1)
      ∧ Tendsto (fun n => l1tQ A n (l1QN s₀ e w n) / (1 + l1tQ A n (l1QN s₀ e w n))) atTop (𝓝 0))
  ∧ (∀ (x₀ x : QuotientState), 1 < x.alpha → ∀ (n : ℝ) (hn : 0 < n),
      l1uEpi (fiberParameters x (l1tStar (l1Family x₀ n hn) x)) / l1Vz (fiberParameters x (l1tStar (l1Family x₀ n hn) x))
        = l1tQ x₀.alpha n (l1QN x₀.s ((x.gamma - x₀.gamma) ^ 2) (x.s / x.alpha) n)
          / (1 + l1tQ x₀.alpha n (l1QN x₀.s ((x.gamma - x₀.gamma) ^ 2) (x.s / x.alpha) n)))

def B2_prop7 : Prop :=
  (∀ (A n g₀ b : ℝ) (hb : 0 < b) (hA : 0 < A) (hn : 0 < n) (x : QuotientState),
      selT (priorOfCoords g₀ b A n hb hA hn) x = tB A n ((x.gamma - g₀) ^ 2) (x.s / x.alpha) b)
  ∧ (∀ (e w : ℝ), Tendsto (scoreB e w) (𝓝[>] 0) (𝓝 (e / w)))
  ∧ (∀ (e w : ℝ), 0 < w → Tendsto (fun b => scoreB e w b / b) atTop (𝓝 (1 / w)))
  ∧ (∀ (A n w : ℝ), 0 < A → 0 < n → Tendsto (tB A n 0 w) (𝓝[>] 0) (𝓝 (TA A n))
      ∧ ∀ (Q : ℝ), 0 < Q → tOfScore A n Q < TA A n)
  ∧ (∀ (A n : ℝ), 0 < A → 0 < n → ∀ (e₁ e₂ w₁ w₂ : ℝ), 0 ≤ e₂ → 0 < w₁ → w₁ < w₂ →
      ∀ᶠ (b : ℝ) in atTop, scoreB e₂ w₂ b < scoreB e₁ w₁ b ∧ tB A n e₁ w₁ b < tB A n e₂ w₂ b)
  ∧ (∀ (A n e w : ℝ), 0 < n → 0 ≤ e → 0 < w →
      (tB A n e w ~[atTop] fun b => w / (n * b)) ∧ (fun b => 1 / tB A n e w b) ~[atTop] fun b => n * b / w)
  ∧ (∀ (x₀ x : QuotientState) (n : ℝ) (hn : 0 < n),
      selT (priorFamily x₀ n hn) x = tN x₀.alpha x₀.s ((x.gamma - x₀.gamma) ^ 2) (x.s / x.alpha) n)
  ∧ (∀ (s₀ e w : ℝ), Tendsto (scoreN s₀ e w) (𝓝[>] 0) (𝓝 (scoreLow s₀ e w)))
  ∧ (∀ (s₀ e w : ℝ), Tendsto (scoreN s₀ e w) atTop (𝓝 (scoreHigh e w)))
  ∧ (∀ {A s₀ e w : ℝ}, 0 < A → 0 < s₀ → 0 ≤ e → 0 < w →
      (tN A s₀ e w ~[𝓝[>] 0] fun n => (2 * A + 1) / (n * (1 + scoreLow s₀ e w)))
      ∧ (fun n => 1 / tN A s₀ e w n) ~[𝓝[>] 0] fun n => n * (1 + scoreLow s₀ e w) / (2 * A + 1))
  ∧ (∀ {A s₀ e w : ℝ}, 0 < s₀ → 0 ≤ e → 0 < w →
      (tN A s₀ e w ~[atTop] fun n => 1 / (n * (1 + scoreHigh e w)))
      ∧ (fun n => 1 / tN A s₀ e w n) ~[atTop] fun n => n * (1 + scoreHigh e w))
  ∧ (∀ {A s₀ e w : ℝ}, 0 < A → 0 < s₀ → 0 ≤ e → 0 < w →
      Tendsto (fun n => tN A s₀ e w n / (1 + tN A s₀ e w n)) (𝓝[>] 0) (𝓝 1)
      ∧ Tendsto (fun n => tN A s₀ e w n / (1 + tN A s₀ e w n)) atTop (𝓝 0))
  ∧ (∀ (x₀ x : QuotientState), 1 < x.alpha → ∀ (n : ℝ) (hn : 0 < n),
      uEpi (fiberParameters x (selTPos (priorFamily x₀ n hn) x)) / totalVar (fiberParameters x (selTPos (priorFamily x₀ n hn) x))
        = tN x₀.alpha x₀.s ((x.gamma - x₀.gamma) ^ 2) (x.s / x.alpha) n
          / (1 + tN x₀.alpha x₀.s ((x.gamma - x₀.gamma) ^ 2) (x.s / x.alpha) n))

theorem rel_prop7 : B2_prop7 → L1_prop7 := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun s₀ e w => ⟨h8 s₀ e w, h9 s₀ e w⟩, fun _ _ _ _ hA hs he hw => h10 hA hs he hw,
    fun _ _ _ _ hs he hw => h11 hs he hw, fun _ _ _ _ hA hs he hw => h12 hA hs he hw, h13⟩

#relation_audit rel_prop7 [NIGBottleneck.tendsto_mul_TA_zero, NIGBottleneck.tendsto_mul_TA_atTop,
  NIGBottleneck.TA_isEquivalent_zero, NIGBottleneck.TA_isEquivalent_atTop, NIGBottleneck.selT_geometric_family,
  NIGBottleneck.scoreB_tendsto_zero, NIGBottleneck.scoreB_div_tendsto_atTop, NIGBottleneck.tB_tendsto_max,
  NIGBottleneck.eventually_ordered_by_w, NIGBottleneck.tB_isEquivalent_atTop, NIGBottleneck.selT_marginal_family,
  NIGBottleneck.scoreN_tendsto_zero, NIGBottleneck.scoreN_tendsto_atTop, NIGBottleneck.tN_isEquivalent_zero,
  NIGBottleneck.tN_isEquivalent_atTop, NIGBottleneck.epistemic_fraction_limits,
  NIGBottleneck.epistemic_fraction_marginal_family]

theorem B2_prop7_holds : B2_prop7 :=
  ⟨selT_geometric_family, scoreB_tendsto_zero, scoreB_div_tendsto_atTop, tB_tendsto_max, eventually_ordered_by_w,
    tB_isEquivalent_atTop, selT_marginal_family, scoreN_tendsto_zero, scoreN_tendsto_atTop,
    fun hA hs he hw => tN_isEquivalent_zero hA hs he hw, fun hs he hw => tN_isEquivalent_atTop hs he hw,
    fun hA hs he hw => epistemic_fraction_limits hA hs he hw, epistemic_fraction_marginal_family⟩

theorem L1_prop7_holds : L1_prop7 := rel_prop7 B2_prop7_holds

/-! ## proposition-6

L1, clauses:

L1_form: "need not imply" and "is insufficient" and "not universal" are existential counterexample statements.
 is read as: a single-coordinate collection with a strictly
smaller score than the mean score of a two-coordinate collection can have a strictly smaller (not larger) t,
and symmetrically for ν. The aggregate ratio uses `aggRatio` (the L1 formula at the selected points); its
weighted forms are written literally. -/

def L1_prop6 : Prop :=
  (∀ p p' : Parameters, p.alpha = p'.alpha → p.nu = p'.nu → ∀ x x' : QuotientState,
      (l1Q p x < l1Q p' x' ↔ l1PhiA p.alpha (l1d p x) < l1PhiA p'.alpha (l1d p' x'))
      ∧ (l1PhiA p.alpha (l1d p x) < l1PhiA p'.alpha (l1d p' x') ↔ l1TA p'.alpha (l1d p' x') < l1TA p.alpha (l1d p x)))
  ∧ (∀ (p p' : Parameters) (x x' : QuotientState), l1Q p x ≤ l1Q p' x' → p.nu ≤ p'.nu → p'.alpha ≤ p.alpha →
      l1PhiA p.alpha (l1d p x) ≤ l1PhiA p'.alpha (l1d p' x') ∧ l1TA p'.alpha (l1d p' x') ≤ l1TA p.alpha (l1d p x))
  ∧ (∃ (p p' : Parameters) (x x' : QuotientState), l1Q p x < l1Q p' x'
      ∧ l1PhiA p'.alpha (l1d p' x') < l1PhiA p.alpha (l1d p x))
  ∧ (∀ {ι : Type} [Fintype ι] (A n Q Q' c : ι → ℝ), (∀ i, 0 < A i) → (∀ i, 0 < n i) → (∀ i, 0 < Q i) →
      (∀ i, Q i ≤ Q' i) → (∀ i, 0 ≤ c i) →
      ∑ i, c i * l1tQ (A i) (n i) (Q' i) ≤ ∑ i, c i * l1tQ (A i) (n i) (Q i)
      ∧ ∑ i, c i * l1nuQ (A i) (n i) (Q i) ≤ ∑ i, c i * l1nuQ (A i) (n i) (Q' i))
  ∧ (∀ A n : ℝ, 0 < A → 0 < n →
      (∃ ε, 0 < ε ∧ ε < 1 ∧ 2 - ε < (1 + 3) / 2 ∧ l1tQ A n (2 - ε) < (l1tQ A n 1 + l1tQ A n 3) / 2)
      ∧ (∃ ε, 0 < ε ∧ ε < 1 ∧ (1 + 3) / 2 < 2 + ε ∧ l1nuQ A n (2 + ε) < (l1nuQ A n 1 + l1nuQ A n 3) / 2))
  ∧ (∀ {ι : Type} [Fintype ι] (p₀ : ι → Parameters) (x : ι → QuotientState) (c : ι → ℝ), (∀ i, 1 < (x i).alpha) →
      aggRatio p₀ x c
        = (∑ i, c i * ((x i).s / ((x i).alpha - 1)) * (l1TA (p₀ i).alpha (l1d (p₀ i) (x i)) / (1 + l1TA (p₀ i).alpha (l1d (p₀ i) (x i)))))
          / (∑ i, c i * ((x i).s / ((x i).alpha - 1)) * (1 / (1 + l1TA (p₀ i).alpha (l1d (p₀ i) (x i)))))
      ∧ aggRatio p₀ x c
        = (∑ i, c i * l1uVar (fiberParameters (x i) (l1tStar (p₀ i) (x i))) * l1TA (p₀ i).alpha (l1d (p₀ i) (x i)))
          / (∑ i, c i * l1uVar (fiberParameters (x i) (l1tStar (p₀ i) (x i)))))
  ∧ (∀ {ι : Type} [Fintype ι] [Nonempty ι] (a t t' : ι → ℝ), (∀ i, 0 < a i) → (∀ i, 0 < t i) → (∀ i, t i ≤ t' i) →
      (∑ i, a i * (t i / (1 + t i))) / (∑ i, a i * (1 / (1 + t i)))
        ≤ (∑ i, a i * (t' i / (1 + t' i))) / (∑ i, a i * (1 / (1 + t' i)))
      ∧ ((∃ k, t k < t' k) → (∑ i, a i * (t i / (1 + t i))) / (∑ i, a i * (1 / (1 + t i)))
        < (∑ i, a i * (t' i / (1 + t' i))) / (∑ i, a i * (1 / (1 + t' i)))))
  ∧ (∃ (p₀ : Parameters) (x₁ x₂ : Fin 2 → QuotientState) (c₁ c₂ : Fin 2 → ℝ),
      (∀ i, 1 < (x₁ i).alpha ∧ 1 < (x₂ i).alpha) ∧ (∀ i, 0 < c₁ i ∧ 0 < c₂ i)
      ∧ (∀ i, l1TA p₀.alpha (l1d p₀ (x₁ i)) < l1TA p₀.alpha (l1d p₀ (x₂ i)))
      ∧ aggRatio (fun _ => p₀) x₂ c₂ < aggRatio (fun _ => p₀) x₁ c₁)

def B2_prop6 : Prop :=
  (∀ (p p' : Parameters), p.alpha = p'.alpha → p.nu = p'.nu → ∀ (x x' : QuotientState),
      (scoreQ p x < scoreQ p' x' ↔ selNu p x < selNu p' x') ∧ (selNu p x < selNu p' x' ↔ selT p' x' < selT p x))
  ∧ (∀ (p p' : Parameters) (x x' : QuotientState), scoreQ p x ≤ scoreQ p' x' → p.nu ≤ p'.nu → p'.alpha ≤ p.alpha →
      selNu p x ≤ selNu p' x' ∧ selT p' x' ≤ selT p x)
  ∧ (∃ p p' x x', p.alpha = p'.alpha ∧ scoreQ p x < scoreQ p' x' ∧ selNu p' x' < selNu p x)
  ∧ (∀ {ι : Type} [Fintype ι] (A n Q Q' c : ι → ℝ), (∀ (i : ι), 0 < A i) → (∀ (i : ι), 0 < n i) →
      (∀ (i : ι), 0 < Q i) → (∀ (i : ι), Q i ≤ Q' i) → (∀ (i : ι), 0 ≤ c i) →
      ∑ i, c i * tOfScore (A i) (n i) (Q' i) ≤ ∑ i, c i * tOfScore (A i) (n i) (Q i) ∧
        ∑ i, c i * nuOfScore (A i) (n i) (Q i) ≤ ∑ i, c i * nuOfScore (A i) (n i) (Q' i))
  ∧ (∀ {A n : ℝ}, 0 < A → 0 < n →
      (∃ ε, 0 < ε ∧ ε < 1 ∧ tOfScore A n (2 - ε) < (tOfScore A n 1 + tOfScore A n 3) / 2) ∧
        ∃ ε, 0 < ε ∧ ε < 1 ∧ nuOfScore A n (2 + ε) < (nuOfScore A n 1 + nuOfScore A n 3) / 2)
  ∧ (∀ {ι : Type} [Fintype ι] (p₀ : ι → Parameters) (x : ι → QuotientState) (c : ι → ℝ), (∀ (i : ι), 1 < (x i).alpha) →
      aggRatio p₀ x c =
          (∑ i, c i * ((x i).s / ((x i).alpha - 1)) * (selT (p₀ i) (x i) / (1 + selT (p₀ i) (x i)))) /
            ∑ i, c i * ((x i).s / ((x i).alpha - 1)) * (1 / (1 + selT (p₀ i) (x i))) ∧
        aggRatio p₀ x c =
          (∑ i, c i * uVar (selParams (p₀ i) (x i)) * selT (p₀ i) (x i)) / ∑ i, c i * uVar (selParams (p₀ i) (x i)))
  ∧ (∀ {ι : Type} [Fintype ι] [Nonempty ι] (a t t' : ι → ℝ), (∀ (i : ι), 0 < a i) → (∀ (i : ι), 0 < t i) →
      (∀ (i : ι), t i ≤ t' i) → ratioOfT a t ≤ ratioOfT a t' ∧ ((∃ k, t k < t' k) → ratioOfT a t < ratioOfT a t'))
  ∧ (∃ p₀ x₁ x₂ c₁ c₂, p₀.alpha = 3 ∧ p₀.nu = 1 ∧ 4 < boundM p₀.alpha p₀.nu ∧
      (∀ (i : Fin 2), (x₁ i).alpha = 2 ∧ (x₂ i).alpha = 2) ∧
      (∀ (i : Fin 2), selT p₀ (x₁ i) = pairT₁ i ∧ selT p₀ (x₂ i) = pairT₂ i) ∧
      (∀ (i : Fin 2), pairT₁ i < pairT₂ i) ∧ (∀ (i : Fin 2), 0 < c₁ i ∧ 0 < c₂ i) ∧
      aggRatio (fun _ => p₀) x₂ c₂ < aggRatio (fun _ => p₀) x₁ c₁)

theorem rel_prop6 : B2_prop6 → L1_prop6 := by
  rintro ⟨h1, h2, ⟨p, p', x, x', -, hq, hn⟩, h4, h5, h6, h7, ⟨p₀, x₁, x₂, c₁, c₂, -, -, -, ha, ht, hlt, hc, hagg⟩⟩
  refine ⟨h1, h2, ⟨p, p', x, x', hq, hn⟩, h4, fun A n hA hn => ?_, h6, h7, ⟨p₀, x₁, x₂, c₁, c₂, ?_, hc, ?_, hagg⟩⟩
  · obtain ⟨⟨ε, hε0, hε1, hlt1⟩, ⟨ε', hε0', hε1', hlt2⟩⟩ := h5 hA hn
    exact ⟨⟨ε, hε0, hε1, by linarith, hlt1⟩, ⟨ε', hε0', hε1', by linarith, hlt2⟩⟩
  · intro i
    rw [(ha i).1, (ha i).2]
    norm_num
  · intro i
    have h1' := (ht i).1
    have h2' := (ht i).2
    change selT p₀ (x₁ i) < selT p₀ (x₂ i)
    rw [h1', h2']
    exact hlt i

#relation_audit rel_prop6 [NIGBottleneck.equal_calibration_order, NIGBottleneck.sufficient_order,
  NIGBottleneck.score_order_insufficient, NIGBottleneck.weighted_sums_order,
  NIGBottleneck.mean_score_same_mean_allocation_differs, NIGBottleneck.mean_score_reversal,
  NIGBottleneck.exists_state_score, NIGBottleneck.aggregate_ratio_formula, NIGBottleneck.ratioOfT_mono,
  NIGBottleneck.weight_control_needed]

theorem B2_prop6_holds : B2_prop6 :=
  ⟨equal_calibration_order, sufficient_order, score_order_insufficient,
    fun A n Q Q' c hA hn hQ hQQ hc => weighted_sums_order A n Q Q' c hA hn hQ hQQ hc,
    fun hA hn => mean_score_reversal hA hn, fun p₀ x c hx => aggregate_ratio_formula p₀ x c hx,
    fun a t t' ha ht htt => ratioOfT_mono a t t' ha ht htt, weight_control_needed⟩

theorem L1_prop6_holds : L1_prop6 := rel_prop6 B2_prop6_holds

/-! ## proposition-8

L1_form: t_*, ν_sel, u_var and u_epi along the states (γ,α,s) are written as the literal functions of s
(t_*(s) = T_A(n + D/s), ν_sel(s) = Φ_A(n + D/s), u_var = s/((α−1)(1+t_*)), u_epi = st_*/((α−1)(1+t_*))), together
with the identity that they are the selected values for every s > 0. The O and ∼ statements are about these
functions. "Uniformly bounded ratio" is theorem-6 and is not repeated. -/

def l1tS (A n D s : ℝ) : ℝ := l1TA A (n + D / s)
def l1nuS (A n D s : ℝ) : ℝ := l1PhiA A (n + D / s)
def l1uVarS (A n D a s : ℝ) : ℝ := s / (a * (1 + l1tS A n D s))
def l1uEpiS (A n D a s : ℝ) : ℝ := s * l1tS A n D s / (a * (1 + l1tS A n D s))
def l1C (p₀ : Parameters) (γ α : ℝ) : ℝ := α * ((γ - p₀.gamma) ^ 2 + l1b p₀)

def L1_prop8 : Prop :=
  (∀ (p₀ : Parameters) (γ α s : ℝ) (hα : 0 < α) (hs : 0 < s),
      l1Q p₀ ⟨γ, α, s, hα, hs⟩ = l1C p₀ γ α / s
      ∧ p₀.nu * l1C p₀ γ α = 2 * α * (p₀.beta + p₀.nu / 2 * (γ - p₀.gamma) ^ 2)
      ∧ l1TA p₀.alpha (l1d p₀ ⟨γ, α, s, hα, hs⟩) = l1tS p₀.alpha p₀.nu (p₀.nu * l1C p₀ γ α) s
      ∧ l1PhiA p₀.alpha (l1d p₀ ⟨γ, α, s, hα, hs⟩) = l1nuS p₀.alpha p₀.nu (p₀.nu * l1C p₀ γ α) s)
  ∧ (∀ C : ℝ, 0 < C → Tendsto (fun s => C / s) (𝓝[>] 0) atTop)
  ∧ (∀ {A n D : ℝ}, 0 < A → 0 < n → 0 < D →
      (fun s => l1tS A n D s - s / D) =O[𝓝[>] 0] (fun s => s ^ 2)
      ∧ (fun s => l1nuS A n D s - (D / s + n - 2 * A)) =O[𝓝[>] 0] (fun s => s))
  ∧ (∀ {A n D : ℝ}, 0 < n → 0 < D → ∀ C : ℝ, Tendsto (fun s => C / s) atTop (𝓝 0)
      ∧ Tendsto (l1tS A n D) atTop (𝓝 (l1M A n)) ∧ Tendsto (l1nuS A n D) atTop (𝓝 (1 / l1M A n)))
  ∧ (∀ (p₀ : Parameters) (γ α s : ℝ) (hα : 1 < α) (hs : 0 < s),
      l1uVar (fiberParameters ⟨γ, α, s, by linarith, hs⟩ (l1tStar p₀ ⟨γ, α, s, by linarith, hs⟩))
        = l1uVarS p₀.alpha p₀.nu (p₀.nu * l1C p₀ γ α) (α - 1) s
      ∧ l1uEpi (fiberParameters ⟨γ, α, s, by linarith, hs⟩ (l1tStar p₀ ⟨γ, α, s, by linarith, hs⟩))
        = l1uEpiS p₀.alpha p₀.nu (p₀.nu * l1C p₀ γ α) (α - 1) s)
  ∧ (∀ {A n D : ℝ}, 0 < A → 0 < n → 0 < D → ∀ a : ℝ, 0 < a →
      (l1uVarS A n D a ~[𝓝[>] 0] fun s => s / a) ∧ (l1uEpiS A n D a ~[𝓝[>] 0] fun s => s ^ 2 / (D * a)))
  ∧ (∀ {A n D : ℝ}, 0 < n → 0 < D → ∀ a : ℝ, 0 < a →
      (l1uVarS A n D a ~[atTop] fun s => s / (a * (1 + l1M A n)))
      ∧ (l1uEpiS A n D a ~[atTop] fun s => s * l1M A n / (a * (1 + l1M A n))))
  ∧ (∀ {A n D : ℝ}, 0 < n → 0 < D → ∀ a : ℝ, 0 < a → ∀ K : ℝ,
      ∃ s, 0 < s ∧ K < l1uVarS A n D a s ∧ K < l1uEpiS A n D a s)

def B2_prop8 : Prop :=
  (∀ (p₀ : Parameters) (γ α s : ℝ) (hα : 0 < α) (hs : 0 < s),
      scoreQ p₀ ⟨γ, α, s, hα, hs⟩ = scaleC p₀ γ α / s ∧
      p₀.nu * scaleC p₀ γ α = 2 * α * priorB p₀ ⟨γ, α, s, hα, hs⟩ ∧
      selT p₀ ⟨γ, α, s, hα, hs⟩ = tScale p₀.alpha p₀.nu (p₀.nu * scaleC p₀ γ α) s ∧
      selNu p₀ ⟨γ, α, s, hα, hs⟩ = nuScale p₀.alpha p₀.nu (p₀.nu * scaleC p₀ γ α) s)
  ∧ (∀ (C : ℝ), 0 < C → Tendsto (fun s => C / s) (𝓝[>] 0) atTop)
  ∧ (∀ {A n D : ℝ}, 0 < A → 0 < n → 0 < D → (fun s => tScale A n D s - s / D) =O[𝓝[>] 0] fun s => s ^ 2)
  ∧ (∀ {A n D : ℝ}, 0 < A → 0 < n → 0 < D → (fun s => nuScale A n D s - (D / s + n - 2 * A)) =O[𝓝[>] 0] fun s => s)
  ∧ (∀ {A n D : ℝ}, 0 < n → 0 < D → ∀ (C : ℝ), Tendsto (fun s => C / s) atTop (𝓝 0) ∧
      Tendsto (tScale A n D) atTop (𝓝 (boundM A n)) ∧ Tendsto (nuScale A n D) atTop (𝓝 (1 / boundM A n)))
  ∧ (∀ (p₀ : Parameters) (γ α s : ℝ) (hα : 1 < α) (hs : 0 < s),
      uVar (selParams p₀ ⟨γ, α, s, by linarith, hs⟩) = uVarScale p₀.alpha p₀.nu (p₀.nu * scaleC p₀ γ α) (α - 1) s ∧
      uEpi (selParams p₀ ⟨γ, α, s, by linarith, hs⟩) = uEpiScale p₀.alpha p₀.nu (p₀.nu * scaleC p₀ γ α) (α - 1) s)
  ∧ (∀ {A n D : ℝ}, 0 < A → 0 < n → 0 < D → ∀ (a : ℝ), 0 < a →
      (uVarScale A n D a ~[𝓝[>] 0] fun s => s / a) ∧ (uEpiScale A n D a ~[𝓝[>] 0] fun s => s ^ 2 / (D * a)))
  ∧ (∀ {A n D : ℝ}, 0 < n → 0 < D → ∀ (a : ℝ), 0 < a →
      (uVarScale A n D a ~[atTop] fun s => s / (a * (1 + boundM A n))) ∧
        (uEpiScale A n D a ~[atTop] fun s => s * boundM A n / (a * (1 + boundM A n))))
  ∧ (∀ {A n D : ℝ}, 0 < n → 0 < D → ∀ (a : ℝ), 0 < a → ∀ (K : ℝ),
      ∃ s, 0 < s ∧ K < uVarScale A n D a s ∧ K < uEpiScale A n D a s)

/-- Foundational for proposition-8 (theorem-6 target, not a proposition-8 target): M equals its literal formula. -/
def FoundM : Prop := ∀ (A n : ℝ), boundM A n = (2 * A + 1 - n + √((n - 2 * A - 1) ^ 2 + 4 * n)) / (2 * n)

theorem rel_prop8 : FoundM → B2_prop8 → L1_prop8 := by
  rintro hM ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hM' : ∀ A n, l1M A n = boundM A n := fun A n => (hM A n).symm
  refine ⟨h1, h2, fun hA hn hD => ⟨h3 hA hn hD, h4 hA hn hD⟩, fun hn hD C => ?_, h6, h7, fun hn hD a ha => ?_, h9⟩
  · simp only [hM']; exact h5 hn hD C
  · simp only [hM']; exact h8 hn hD a ha

#relation_audit rel_prop8 [NIGBottleneck.scale_family, NIGBottleneck.score_tendsto_zero,
  NIGBottleneck.tScale_isBigO_zero, NIGBottleneck.nuScale_isBigO_zero, NIGBottleneck.scale_limits_atTop,
  NIGBottleneck.uncertainty_scale_family, NIGBottleneck.uncertainty_isEquivalent_zero,
  NIGBottleneck.uncertainty_isEquivalent_atTop, NIGBottleneck.summands_unbounded]

theorem B2_prop8_holds : B2_prop8 :=
  ⟨scale_family, score_tendsto_zero, fun hA hn hD => tScale_isBigO_zero hA hn hD,
    fun hA hn hD => nuScale_isBigO_zero hA hn hD, fun hn hD C => scale_limits_atTop hn hD C, uncertainty_scale_family,
    fun hA hn hD a ha => uncertainty_isEquivalent_zero hA hn hD a ha,
    fun hn hD a ha => uncertainty_isEquivalent_atTop hn hD a ha, fun hn hD a ha K => summands_unbounded hn hD a ha K⟩

theorem L1_prop8_holds : L1_prop8 := rel_prop8 boundM_eq B2_prop8_holds

end PostHocFidelity
