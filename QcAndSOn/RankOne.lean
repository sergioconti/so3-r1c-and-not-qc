/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import QcAndSOn.Charts

/-!
# Rank-one convexity of `W₀` near `SO(3)` (Section 4)

* `eventually_nonneg_mode₁₂₃`: `P ≥ 0` near `(0, c, b)` for each Šverák mode `c ⊗ b`
  (modes 1 and 3 from the charts in `Charts`, mode 2 by the symmetry `Pc_swap`, eq. (3.6));
* `eventually_Pc_nonneg`: `P (symU e) c b ≥ 0` for all `c, b` and all `e` near `0`
  (Step 1 of Proposition 4.2: compactness on the product of unit spheres + Lemma 3.1);
* `gM_nonneg_near_SO`, `W0_rankOneConvex_near_SO`: Proposition 4.2.
-/

open Matrix Filter Topology Set

noncomputable section

namespace QcSOn

/-- The space of reduced variables `(e, c, b)`. -/
abbrev RV := Mat 3 3 × (Fin 3 → ℝ) × (Fin 3 → ℝ)

/-- The reduced second variation as a function on `RV`. -/
def PcR (z : RV) : ℝ := Pc (symU z.1) z.2.1 z.2.2

lemma continuous_PcR : Continuous PcR := continuous_Pc

/-- Transfer of local nonnegativity through a chart. -/
lemma eventually_nonneg_of_chart {p : RV} {φ : RV → Fin 10 → ℝ} {s : RV → ℝ}
    (Pk : (Fin 10 → ℝ) → ℝ) (hφ : ContinuousAt φ p) (hφp : φ p = 0)
    (hP : ∀ᶠ y in 𝓝 0, 0 ≤ Pk y) (hs : ∀ᶠ z in 𝓝 p, 0 ≤ s z ∧ PcR z = s z * Pk (φ z)) :
    ∀ᶠ z in 𝓝 p, 0 ≤ PcR z := by
  have h1 : ∀ᶠ z in 𝓝 p, 0 ≤ Pk (φ z) := by
    have h := hφ.tendsto; rw [hφp] at h; exact h.eventually hP
  filter_upwards [h1, hs] with z hz hsz
  rw [hsz.2]; exact mul_nonneg hsz.1 hz

/-- Chart of mode `k` (proof of Proposition 4.2): the six upper entries of `e` followed by four
normalized coordinates of `c` and `b`. -/
def chart (e : Mat 3 3) (x : Fin 4 → ℝ) : Fin 10 → ℝ :=
  ![e 0 0, e 0 1, e 0 2, e 1 1, e 1 2, e 2 2, x 0, x 1, x 2, x 3]

lemma symU_eq_symY (e : Mat 3 3) (x : Fin 4 → ℝ) : symU e = symY (chart e x) := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma continuousAt_chart {p : RV} {x : RV → Fin 4 → ℝ} (hx : ContinuousAt x p) :
    ContinuousAt (fun z => chart z.1 (x z)) p := by
  refine continuousAt_pi.2 fun i => ?_
  have hE : ∀ i j, ContinuousAt (fun z : RV => z.1 i j) p := fun i j =>
    ((continuous_id.matrix_elem i j).comp continuous_fst).continuousAt
  have hx' : ∀ i, ContinuousAt (fun z => x z i) p := fun i => (continuousAt_pi.1 hx) i
  fin_cases i
  exacts [hE 0 0, hE 0 1, hE 0 2, hE 1 1, hE 1 2, hE 2 2, hx' 0, hx' 1, hx' 2, hx' 3]

/-- Coordinates of the chart of mode 1. -/
def x₁ (c b : Fin 3 → ℝ) : Fin 4 → ℝ := ![c 1 / c 0, c 2 / c 0, b 1 / b 0, b 2 / b 0]
/-- Coordinates of the chart of mode 3. -/
def x₃ (c b : Fin 3 → ℝ) : Fin 4 → ℝ := ![c 0 / c 2, c 1 / c 2, b 1 / b 0 - 1, b 2 / b 0]

lemma Pc_chart₁ (e : Mat 3 3) {c b : Fin 3 → ℝ} (hc : c 0 ≠ 0) (hb : b 0 ≠ 0) :
    Pc (symU e) c b = c 0 ^ 2 * b 0 ^ 2 * P1 (chart e (x₁ c b)) := by
  set y := chart e (x₁ c b)
  have hc' : c = c 0 • ![1, y 6, y 7] := by
    ext i; fin_cases i <;> simp [y, chart, x₁] <;> field_simp
  have hb' : b = b 0 • ![1, y 8, y 9] := by
    ext i; fin_cases i <;> simp [y, chart, x₁] <;> field_simp
  rw [symU_eq_symY e (x₁ c b)]
  exact (congrArg₂ (Pc (symY y)) hc' hb').trans (Pc_smul _ _ _ _ _)

lemma Pc_chart₃ (e : Mat 3 3) {c b : Fin 3 → ℝ} (hc : c 2 ≠ 0) (hb : b 0 ≠ 0) :
    Pc (symU e) c b = c 2 ^ 2 * b 0 ^ 2 * P3 (chart e (x₃ c b)) := by
  set y := chart e (x₃ c b)
  have hc' : c = c 2 • ![y 6, y 7, 1] := by
    ext i; fin_cases i <;> simp [y, chart, x₃] <;> field_simp
  have hb' : b = b 0 • ![1, 1 + y 8, y 9] := by
    ext i; fin_cases i <;> simp [y, chart, x₃] <;> field_simp
  rw [symU_eq_symY e (x₃ c b)]
  exact (congrArg₂ (Pc (symY y)) hc' hb').trans (Pc_smul _ _ _ _ _)

lemma eventually_c_ne {c b : Fin 3 → ℝ} (i : Fin 3) (h : c i ≠ 0) :
    ∀ᶠ z in 𝓝 ((0 : Mat 3 3), c, b), z.2.1 i ≠ 0 := by
  have : ContinuousAt (fun z : RV => z.2.1 i) ((0 : Mat 3 3), c, b) := by fun_prop
  exact this.eventually_ne h

lemma eventually_b_ne {c b : Fin 3 → ℝ} (i : Fin 3) (h : b i ≠ 0) :
    ∀ᶠ z in 𝓝 ((0 : Mat 3 3), c, b), z.2.2 i ≠ 0 := by
  have : ContinuousAt (fun z : RV => z.2.2 i) ((0 : Mat 3 3), c, b) := by fun_prop
  exact this.eventually_ne h

lemma continuousAt_c_div {c b : Fin 3 → ℝ} (i j : Fin 3) (h : c j ≠ 0) :
    ContinuousAt (fun z : RV => z.2.1 i / z.2.1 j) ((0 : Mat 3 3), c, b) :=
  ContinuousAt.div (by fun_prop) (by fun_prop) h

lemma continuousAt_b_div {c b : Fin 3 → ℝ} (i j : Fin 3) (h : b j ≠ 0) :
    ContinuousAt (fun z : RV => z.2.2 i / z.2.2 j) ((0 : Mat 3 3), c, b) :=
  ContinuousAt.div (by fun_prop) (by fun_prop) h

/-- Mode `e₁ ⊗ e₁`. -/
lemma eventually_nonneg_mode₁ {c b : Fin 3 → ℝ} (hc : c 0 ≠ 0) (hb : b 0 ≠ 0)
    (hc1 : c 1 = 0) (hc2 : c 2 = 0) (hb1 : b 1 = 0) (hb2 : b 2 = 0) :
    ∀ᶠ z in 𝓝 ((0 : Mat 3 3), c, b), 0 ≤ PcR z := by
  have h0 := (eventually_c_ne (b := b) 0 hc).and (eventually_b_ne (c := c) 0 hb)
  refine eventually_nonneg_of_chart P1 (φ := fun z => chart z.1 (x₁ z.2.1 z.2.2))
    (s := fun z => z.2.1 0 ^ 2 * z.2.2 0 ^ 2) (continuousAt_chart ?_) ?_ P1_eventually_nonneg ?_
  · refine continuousAt_pi.2 fun i => ?_
    fin_cases i
    exacts [continuousAt_c_div 1 0 hc, continuousAt_c_div 2 0 hc, continuousAt_b_div 1 0 hb,
      continuousAt_b_div 2 0 hb]
  · ext i; fin_cases i <;> simp [chart, x₁, hc1, hc2, hb1, hb2]
  · filter_upwards [h0] with z ⟨hz1, hz2⟩
    exact ⟨by positivity, Pc_chart₁ z.1 hz1 hz2⟩

lemma symU_zero : symU 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-! ### The symmetry exchanging the first two coordinates

`g` is invariant under `e ↦ Π e Π` with `Π` the permutation matrix exchanging `e₁` and `e₂`;
hence `P(Π e Π, Π c, Π b) = P(e, c, b)` (eq. (3.6)), and mode 2 follows from mode 1. -/

/-- The permutation matrix `Π` exchanging `e₁` and `e₂`. -/
def swapM : Mat 3 3 := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

lemma symU_swap (E : Mat 3 3) : symU (swapM * symU E * swapM) =
    !![E 1 1, E 0 1, E 1 2; E 0 1, E 0 0, E 0 2; E 1 2, E 0 2, E 2 2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [symU, swapM, Matrix.mul_apply, Fin.sum_univ_three]

lemma swapM_mulVec (c : Fin 3 → ℝ) : swapM *ᵥ c = ![c 1, c 0, c 2] := by
  ext i; fin_cases i <;> simp [swapM, mulVec, dotProduct, Fin.sum_univ_three]

lemma symU_apply (E : Mat 3 3) :
    symU E = !![E 0 0, E 0 1, E 0 2; E 0 1, E 1 1, E 1 2; E 0 2, E 1 2, E 2 2] := rfl

/-- The symmetry (3.6): `P(Π e Π, Π c, Π b) = P(e, c, b)`. -/
lemma Pc_swap (e : Mat 3 3) (c b : Fin 3 → ℝ) :
    Pc (symU (swapM * symU e * swapM)) (swapM *ᵥ c) (swapM *ᵥ b) = Pc (symU e) c b := by
  rw [symU_swap, swapM_mulVec, swapM_mulVec, symU_apply e]
  have hd : det (1 + (2 : ℝ) • !![e 1 1, e 0 1, e 1 2; e 0 1, e 0 0, e 0 2; e 1 2, e 0 2, e 2 2]) =
      det (1 + (2 : ℝ) • !![e 0 0, e 0 1, e 0 2; e 0 1, e 1 1, e 1 2; e 0 2, e 1 2, e 2 2]) := by
    simp [det_fin_three]; ring
  have ha : ![c 1, c 0, c 2] ⬝ᵥ (cof (1 + (2 : ℝ) • !![e 1 1, e 0 1, e 1 2; e 0 1, e 0 0, e 0 2;
      e 1 2, e 0 2, e 2 2]) *ᵥ ![c 1, c 0, c 2]) =
      c ⬝ᵥ (cof (1 + (2 : ℝ) • !![e 0 0, e 0 1, e 0 2; e 0 1, e 1 1, e 1 2; e 0 2, e 1 2, e 2 2]) *ᵥ
        c) := by
    simp [cof, adjugate_fin_three, mulVec, dotProduct, Fin.sum_univ_three]; ring
  have hq : Qg !![e 1 1, e 0 1, e 1 2; e 0 1, e 0 0, e 0 2; e 1 2, e 0 2, e 2 2]
      (symPart (vecMulVec ![c 1, c 0, c 2] ![b 1, b 0, b 2])) =
      Qg !![e 0 0, e 0 1, e 0 2; e 0 1, e 1 1, e 1 2; e 0 2, e 1 2, e 2 2]
        (symPart (vecMulVec c b)) := by
    simp [Qg, symPart, vecMulVec_apply]; ring
  have hl : Lg !![e 1 1, e 0 1, e 1 2; e 0 1, e 0 0, e 0 2; e 1 2, e 0 2, e 2 2]
      (vecMulVec ![b 1, b 0, b 2] ![b 1, b 0, b 2]) =
      Lg !![e 0 0, e 0 1, e 0 2; e 0 1, e 1 1, e 1 2; e 0 2, e 1 2, e 2 2] (vecMulVec b b) := by
    simp [Lg, vecMulVec_apply]; ring
  rw [Pc, Pc, hd, ha, hq, hl]

/-- The symmetry on reduced variables. -/
def swapRV (z : RV) : RV := (swapM * symU z.1 * swapM, swapM *ᵥ z.2.1, swapM *ᵥ z.2.2)

lemma PcR_swap (z : RV) : PcR (swapRV z) = PcR z := Pc_swap z.1 z.2.1 z.2.2

lemma continuous_swapRV : Continuous swapRV :=
  ((continuous_const.matrix_mul (continuous_symU.comp continuous_fst)).matrix_mul
    continuous_const).prodMk ((continuous_const.matrix_mulVec (continuous_fst.comp
      continuous_snd)).prodMk (continuous_const.matrix_mulVec (continuous_snd.comp continuous_snd)))

/-- Mode `e₂ ⊗ e₂`, by symmetry from mode `e₁ ⊗ e₁`. -/
lemma eventually_nonneg_mode₂ {c b : Fin 3 → ℝ} (hc : c 1 ≠ 0) (hb : b 1 ≠ 0)
    (hc0 : c 0 = 0) (hc2 : c 2 = 0) (hb0 : b 0 = 0) (hb2 : b 2 = 0) :
    ∀ᶠ z in 𝓝 ((0 : Mat 3 3), c, b), 0 ≤ PcR z := by
  have h1 := eventually_nonneg_mode₁ (c := swapM *ᵥ c) (b := swapM *ᵥ b)
    (by simpa [swapM_mulVec] using hc) (by simpa [swapM_mulVec] using hb)
    (by simp [swapM_mulVec, hc0]) (by simp [swapM_mulVec, hc2]) (by simp [swapM_mulVec, hb0])
    (by simp [swapM_mulVec, hb2])
  have hp : swapRV ((0 : Mat 3 3), c, b) = ((0 : Mat 3 3), swapM *ᵥ c, swapM *ᵥ b) := by
    simp [swapRV, symU_zero]
  rw [← hp] at h1
  filter_upwards [(continuous_swapRV.tendsto _).eventually h1] with z hz
  rwa [PcR_swap] at hz

/-- Mode `e₃ ⊗ (e₁ + e₂)`. -/
lemma eventually_nonneg_mode₃ {c b : Fin 3 → ℝ} (hc : c 2 ≠ 0) (hb : b 0 ≠ 0)
    (hc0 : c 0 = 0) (hc1 : c 1 = 0) (hb1 : b 0 = b 1) (hb2 : b 2 = 0) :
    ∀ᶠ z in 𝓝 ((0 : Mat 3 3), c, b), 0 ≤ PcR z := by
  have h0 := (eventually_c_ne (b := b) 2 hc).and (eventually_b_ne (c := c) 0 hb)
  refine eventually_nonneg_of_chart P3 (φ := fun z => chart z.1 (x₃ z.2.1 z.2.2))
    (s := fun z => z.2.1 2 ^ 2 * z.2.2 0 ^ 2) (continuousAt_chart ?_) ?_ P3_eventually_nonneg ?_
  · refine continuousAt_pi.2 fun i => ?_
    fin_cases i
    exacts [continuousAt_c_div 0 2 hc, continuousAt_c_div 1 2 hc,
      (continuousAt_b_div 1 0 hb).sub continuousAt_const, continuousAt_b_div 2 0 hb]
  · ext i; fin_cases i <;> simp [chart, x₃, hc0, hc1, hb2, ← hb1, hb]
  · filter_upwards [h0] with z ⟨hz1, hz2⟩
    exact ⟨by positivity, Pc_chart₃ z.1 hz1 hz2⟩

lemma ne_zero_of_sumSq_eq_one {c : Fin 3 → ℝ} (hc : ∑ i, c i ^ 2 = 1) : c ≠ 0 := by
  rintro rfl; simp at hc

/-- `P ≥ 0` near `(0, c, b)` for every `(c, b)` on the product of unit spheres. -/
lemma eventually_nonneg_at {c b : Fin 3 → ℝ} (hc : ∑ i, c i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1) :
    ∀ᶠ z in 𝓝 ((0 : Mat 3 3), c, b), 0 ≤ PcR z := by
  have h0 : PcR ((0 : Mat 3 3), c, b) = 2 * sosQ c b := by
    simp only [PcR]; rw [symU_zero, Pc_zero]
  rcases (sosQ_nonneg c b).lt_or_eq with hpos | hzero
  · have : (0 : ℝ) < PcR ((0 : Mat 3 3), c, b) := by rw [h0]; linarith
    exact ((continuous_PcR.tendsto _).eventually (lt_mem_nhds this)).mono fun z hz => hz.le
  · simp only [Fin.sum_univ_three] at hc hb
    rcases sosQ_eq_zero (ne_zero_of_sumSq_eq_one (by simpa [Fin.sum_univ_three] using hc))
      (ne_zero_of_sumSq_eq_one (by simpa [Fin.sum_univ_three] using hb)) hzero.symm with
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · refine eventually_nonneg_mode₁ ?_ ?_ h1 h2 h3 h4
      · intro h; rw [h, h1, h2] at hc; norm_num at hc
      · intro h; rw [h, h3, h4] at hb; norm_num at hb
    · refine eventually_nonneg_mode₂ ?_ ?_ h1 h2 h3 h4
      · intro h; rw [h, h1, h2] at hc; norm_num at hc
      · intro h; rw [h, h3, h4] at hb; norm_num at hb
    · refine eventually_nonneg_mode₃ ?_ ?_ h1 h2 h3 h4
      · intro h; rw [h, h1, h2] at hc; norm_num at hc
      · intro h; rw [← h3, h, h4] at hb; norm_num at hb

/-- Every vector is zero or a positive multiple of a unit vector. -/
lemma eq_zero_or_smul_unit (c : Fin 3 → ℝ) :
    c = 0 ∨ ∃ r : ℝ, 0 < r ∧ ∃ u : Fin 3 → ℝ, ∑ i, u i ^ 2 = 1 ∧ c = r • u := by
  by_cases h : c = 0
  · exact Or.inl h
  · right
    have hs : 0 < ∑ i, c i ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (by simpa using hi)).symm)
        (Finset.single_le_sum (fun j _ => sq_nonneg (c j)) (Finset.mem_univ i))
    set r := √(∑ i, c i ^ 2)
    have hr : 0 < r := Real.sqrt_pos.2 hs
    refine ⟨r, hr, r⁻¹ • c, ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, inv_pow,
        Real.sq_sqrt hs.le, r]
      exact inv_mul_cancel₀ hs.ne'
    · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

/-- **Local nonnegativity of the reduced second variation** (Step 1 of Proposition 4.2): for `e`
near `0`, `P (symU e) c b ≥ 0` for all `c, b`. -/
lemma eventually_Pc_nonneg : ∀ᶠ E in 𝓝 (0 : Mat 3 3), ∀ c b, 0 ≤ Pc (symU E) c b := by
  set S := {u : Fin 3 → ℝ | ∑ i, u i ^ 2 = 1}
  have hK : IsCompact (S ×ˢ S) := (isCompact_sumSq_eq_one 3).prod (isCompact_sumSq_eq_one 3)
  have h := hK.eventually_forall_of_forall_eventually (x₀ := (0 : Mat 3 3))
    (P := fun E p => 0 ≤ Pc (symU E) p.1 p.2) fun p hp => eventually_nonneg_at hp.1 hp.2
  filter_upwards [h] with E hE c b
  rcases eq_zero_or_smul_unit c with rfl | ⟨r, -, u, hu, rfl⟩
  · have := Pc_smul (symU E) 0 b 0 1
    simp only [zero_smul, one_smul] at this
    rw [this]; norm_num
  rcases eq_zero_or_smul_unit b with rfl | ⟨s, -, v, hv, rfl⟩
  · have := Pc_smul (symU E) (r • u) 0 1 0
    simp only [zero_smul, one_smul] at this
    rw [this]; norm_num
  rw [Pc_smul]
  exact mul_nonneg (by positivity) (hE (u, v) ⟨hu, hv⟩)

/-- **Proposition 4.2** (local rank-one convexity), pointwise form: there is an open
neighbourhood `U` of `SO(3)` on which `D²W₀(G)[a⊗b, a⊗b] = gM G (a⊗b) ≥ 0`. -/
theorem gM_nonneg_near_SO :
    ∃ U : Set (Mat 3 3), IsOpen U ∧ SO 3 ⊆ U ∧
      ∀ G ∈ U, ∀ a b : Fin 3 → ℝ, 0 ≤ gM G (vecMulVec a b) := by
  have hdet : ∀ᶠ E in 𝓝 (0 : Mat 3 3), 0 < det (1 + (2 : ℝ) • symU E) := by
    have hc : Continuous fun E : Mat 3 3 => det (1 + (2 : ℝ) • symU E) :=
      (continuous_const.add (continuous_symU.const_smul (2 : ℝ))).matrix_det
    have h1 : (0 : ℝ) < det (1 + (2 : ℝ) • symU (0 : Mat 3 3)) := by rw [symU_zero]; simp
    exact (hc.tendsto 0).eventually (lt_mem_nhds h1)
  obtain ⟨V, hV, hVo, hV0⟩ := eventually_nhds_iff.1 (eventually_Pc_nonneg.and hdet)
  -- Step 2: `U = {F : ½ (FᵀF - Id) ∈ V}` (on `V`, `det (FᵀF) = det (Id + 2e) > 0`)
  refine ⟨strain ⁻¹' V, hVo.preimage continuous_strain, fun G hG => ?_, ?_⟩
  · have : Gᵀ * G = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).1 hG.1
    simpa [Set.mem_preimage, strain, this] using hV0
  · intro G hG a b
    obtain ⟨hP, hd⟩ := hV _ hG
    rw [symU_eq_self (strain_transpose G)] at hP hd
    rw [one_add_two_smul_strain] at hd
    have h := hP (Gᵀ *ᵥ a) b
    rw [← det_mul_gM] at h
    exact (mul_nonneg_iff_of_pos_left hd).1 h

/-- **Proposition 4.2** (local rank-one convexity). There is an open neighbourhood `U` of `SO(3)`
such that `W₀` is convex along every rank-one segment contained in `U`. -/
theorem W0_rankOneConvex_near_SO :
    ∃ U : Set (Mat 3 3), IsOpen U ∧ SO 3 ⊆ U ∧
      ∀ (F : Mat 3 3) (a b : Fin 3 → ℝ) (I : Set ℝ), I.OrdConnected →
        (∀ t ∈ I, F + t • vecMulVec a b ∈ U) →
        ConvexOn ℝ I fun t => W0 (F + t • vecMulVec a b) := by
  obtain ⟨U, hU, hSO, hpos⟩ := gM_nonneg_near_SO
  exact ⟨U, hU, hSO, fun F a b I hI hIU =>
    convexOn_W0_line F _ hI.convex fun t ht => hpos _ (hIU t ht) a b⟩

end QcSOn
