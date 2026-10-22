/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import QcAndSOn.RankOne

/-!
# Globalization (Section 6)

We modify `W₀` away from `SO(3)` by adding `K Φ`, where `Φ = χ ∘ γ_σ` with
* `g₀ F = |F - cof F|² + (det F - 1)²` and `γ_σ F = g₀ F + σ |F|²` (eq. (6.1)), a convex quadratic
  function of the minors `T(F) = (F, cof F, det F)`, frame indifferent, with `γ_σ = 3σ` on `SO(3)`;
* `χ s = ∫_{4σ}^s 4 η(r) (r - 4σ)³ dr`, with `η` a smooth nondecreasing step (`η = 0` on
  `(-∞, 4σ]`, `η = 1` on `[5σ, ∞)`); `χ` is `C^∞`, `χ = 0` on `(-∞, 4σ]`, `χ' ≥ 0`, `χ'' ≥ 0`.

Since the minors are affine along rank-one lines (eq. (1.5): `det_line`, `cof_line`),
`t ↦ γ_σ (F + t a⊗b)` is a quadratic polynomial with leading coefficient `≥ σ |a⊗b|²`.

Lemma 6.1: (i) `g0_nonneg`, `g0_eq_zero_iff`; (ii) `gam_mul_of_mem_SO`, `gam_of_mem_SO`,
`g0_le_gam`, `frob_le_gam`; (iii) `gam_line`, `gam2_ge`; (iv) `exists_sigma`;
(v) `exists_gM_lower`. The proof of Theorem 1.1 is `exists_globalization` (with `Main.main`).
-/

open Matrix Filter Topology Set
open scoped ContDiff

noncomputable section

namespace QcSOn

/-! ### The squared Frobenius norm -/

/-- The squared Frobenius norm `|X|² = tr (Xᵀ X)`. -/
def frob (X : Mat 3 3) : ℝ := trace (Xᵀ * X)

lemma frob_eq (X : Mat 3 3) : frob X = ∑ i, ∑ j, X i j ^ 2 := by
  simp only [frob, trace, diag, mul_apply, transpose_apply, sq]
  rw [Finset.sum_comm]

lemma frob_nonneg (X : Mat 3 3) : 0 ≤ frob X := by
  rw [frob_eq]; positivity

lemma sq_le_frob (X : Mat 3 3) (i j : Fin 3) : X i j ^ 2 ≤ frob X := by
  rw [frob_eq]
  exact (Finset.single_le_sum (f := fun j => X i j ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, X i j ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i))

lemma eq_zero_of_frob_eq_zero {X : Mat 3 3} (h : frob X = 0) : X = 0 := by
  ext i j
  have := sq_le_frob X i j
  have : X i j ^ 2 = 0 := le_antisymm (h ▸ this) (sq_nonneg _)
  simpa using this

lemma frob_mul_left {Q : Mat 3 3} (hQ : Qᵀ * Q = 1) (X : Mat 3 3) : frob (Q * X) = frob X := by
  simp only [frob, transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul]

lemma continuous_frob : Continuous frob :=
  (continuous_id.matrix_transpose.matrix_mul continuous_id).matrix_trace

/-- The Frobenius inner product. -/
def ip (X Y : Mat 3 3) : ℝ := ∑ i, ∑ j, X i j * Y i j

lemma frob_add_smul (X Y : Mat 3 3) (t : ℝ) :
    frob (X + t • Y) = frob X + t * (2 * ip X Y) + t ^ 2 * frob Y := by
  simp only [frob_eq, ip, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

/-! ### Cofactors of rotations (eq. (1.4)) -/

lemma cof_eq_self_of_mem_SO {Q : Mat 3 3} (hQ : Q ∈ SO 3) : cof Q = Q := by
  have h1 : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).1 hQ.1
  have h3 : Q * Qᵀ = 1 := mul_eq_one_comm.mp h1
  have hd : det Q = 1 := hQ.2
  calc cof Q = (adjugate Q * (Q * Qᵀ))ᵀ := by rw [h3, Matrix.mul_one, cof]
    _ = Q := by rw [← Matrix.mul_assoc, adjugate_mul, hd, one_smul, Matrix.one_mul,
      transpose_transpose]

lemma cof_mul_of_mem_SO {Q : Mat 3 3} (hQ : Q ∈ SO 3) (F : Mat 3 3) :
    cof (Q * F) = Q * cof F := by
  rw [cof_mul, cof_eq_self_of_mem_SO hQ]

/-! ### Minors along rank-one lines (eq. (1.5)) -/

lemma det_line (F : Mat 3 3) (a b : Fin 3 → ℝ) (t : ℝ) :
    det (F + t • vecMulVec a b) = det F + t * (det (F + vecMulVec a b) - det F) := by
  simp only [det_fin_three, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  ring

lemma cof_line (F : Mat 3 3) (a b : Fin 3 → ℝ) (t : ℝ) :
    cof (F + t • vecMulVec a b) = cof F + t • (cof (F + vecMulVec a b) - cof F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cof, adjugate_fin_three, vecMulVec_apply] <;> ring

/-! ### The functions `g₀` and `γ_σ` (eq. (6.1)) and Lemma 6.1 -/

/-- `g₀ F = |F - cof F|² + (det F - 1)²`; it vanishes exactly on `SO(3)` (Lemma 6.1(i)). -/
def g0 (F : Mat 3 3) : ℝ := frob (F - cof F) + (det F - 1) ^ 2

/-- `γ_σ F = g₀ F + σ |F|²`, a convex quadratic function of `(F, cof F, det F)`. -/
def gam (σ : ℝ) (F : Mat 3 3) : ℝ := g0 F + σ * frob F

lemma g0_nonneg (F : Mat 3 3) : 0 ≤ g0 F :=
  add_nonneg (frob_nonneg _) (sq_nonneg _)

lemma continuous_g0 : Continuous g0 := by
  unfold g0
  exact (continuous_frob.comp (continuous_id.sub continuous_cof)).add
    ((continuous_id.matrix_det.sub continuous_const).pow 2)

lemma continuous_gam (σ : ℝ) : Continuous (gam σ) :=
  continuous_g0.add (continuous_const.mul continuous_frob)

lemma g0_le_gam {σ : ℝ} (hσ : 0 ≤ σ) (F : Mat 3 3) : g0 F ≤ gam σ F := by
  unfold gam
  have := frob_nonneg F
  nlinarith

lemma frob_le_gam (σ : ℝ) (F : Mat 3 3) : σ * frob F ≤ gam σ F := by
  unfold gam
  have := g0_nonneg F
  linarith

lemma mem_SO_of_g0_eq_zero {F : Mat 3 3} (h : g0 F = 0) : F ∈ SO 3 := by
  have h1 := frob_nonneg (F - cof F)
  have h2 := sq_nonneg (det F - 1)
  have hf : frob (F - cof F) = 0 := by unfold g0 at h; linarith
  have hd : det F = 1 := by
    have : (det F - 1) ^ 2 = 0 := by unfold g0 at h; linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  have hF : F = cof F := sub_eq_zero.1 (eq_zero_of_frob_eq_zero hf)
  have hT : Fᵀ * F = 1 :=
    calc Fᵀ * F = (cof F)ᵀ * F := by rw [← hF]
      _ = 1 := by rw [cof, transpose_transpose, adjugate_mul, hd, one_smul]
  exact ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).2 hT, hd⟩

lemma g0_of_mem_SO {Q : Mat 3 3} (hQ : Q ∈ SO 3) : g0 Q = 0 := by
  have h0 : frob (0 : Mat 3 3) = 0 := by simp [frob]
  have hd : det Q = 1 := hQ.2
  simp [g0, cof_eq_self_of_mem_SO hQ, h0, hd]

/-- **Lemma 6.1(i)**: `g₀ F = 0` iff `F ∈ SO(3)`. -/
lemma g0_eq_zero_iff (F : Mat 3 3) : g0 F = 0 ↔ F ∈ SO 3 :=
  ⟨mem_SO_of_g0_eq_zero, g0_of_mem_SO⟩

/-- Lemma 6.1(ii): `γ_σ = 3σ` on `SO(3)`. -/
lemma gam_of_mem_SO (σ : ℝ) {Q : Mat 3 3} (hQ : Q ∈ SO 3) : gam σ Q = 3 * σ := by
  have h1 : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).1 hQ.1
  have hc : cof Q = Q := cof_eq_self_of_mem_SO hQ
  have h3 : frob Q = 3 := by simp [frob, h1]
  have h0 : frob (0 : Mat 3 3) = 0 := by simp [frob]
  have hd : det Q = 1 := hQ.2
  simp only [gam, g0, hc, sub_self, h0, h3, hd]
  ring

/-- Lemma 6.1(ii): `γ_σ` is frame indifferent. -/
lemma gam_mul_of_mem_SO (σ : ℝ) {Q : Mat 3 3} (hQ : Q ∈ SO 3) (F : Mat 3 3) :
    gam σ (Q * F) = gam σ F := by
  have h1 : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).1 hQ.1
  have hd : det Q = 1 := hQ.2
  simp only [gam, g0, cof_mul_of_mem_SO hQ, ← Matrix.mul_sub, frob_mul_left h1, det_mul, hd,
    one_mul]

/-- First-order coefficient of `γ` along the line `F + t a⊗b`. -/
def gam1 (σ : ℝ) (F : Mat 3 3) (a b : Fin 3 → ℝ) : ℝ :=
  2 * ip (F - cof F) (vecMulVec a b - (cof (F + vecMulVec a b) - cof F))
    + 2 * (det F - 1) * (det (F + vecMulVec a b) - det F)
    + σ * (2 * ip F (vecMulVec a b))

/-- Second-order coefficient of `γ` along the line `F + t a⊗b`. -/
def gam2 (σ : ℝ) (F : Mat 3 3) (a b : Fin 3 → ℝ) : ℝ :=
  frob (vecMulVec a b - (cof (F + vecMulVec a b) - cof F))
    + (det (F + vecMulVec a b) - det F) ^ 2
    + σ * frob (vecMulVec a b)

/-- Lemma 6.1(iii): `t ↦ γ_σ (F + t a⊗b)` is a polynomial of degree at most two. -/
lemma gam_line (σ : ℝ) (F : Mat 3 3) (a b : Fin 3 → ℝ) (t : ℝ) :
    gam σ (F + t • vecMulVec a b) = gam σ F + t * gam1 σ F a b + t ^ 2 * gam2 σ F a b := by
  have h1 : F + t • vecMulVec a b - cof (F + t • vecMulVec a b) =
      (F - cof F) + t • (vecMulVec a b - (cof (F + vecMulVec a b) - cof F)) := by
    rw [cof_line]; module
  simp only [gam, g0, gam1, gam2]
  rw [h1, det_line, frob_add_smul, frob_add_smul]
  ring

/-- Lemma 6.1(iii): its second derivative `2 gam2` is at least `2σ |a⊗b|²`. -/
lemma gam2_ge (σ : ℝ) (F : Mat 3 3) (a b : Fin 3 → ℝ) :
    σ * frob (vecMulVec a b) ≤ gam2 σ F a b := by
  unfold gam2
  have := frob_nonneg (vecMulVec a b - (cof (F + vecMulVec a b) - cof F))
  have := sq_nonneg (det (F + vecMulVec a b) - det F)
  linarith

/-! ### Choice of `σ` -/

/-- The compact cube `{F : |F i j| ≤ r}`. -/
def cube (r : ℝ) : Set (Mat 3 3) := {F | ∀ i j, F i j ∈ Icc (-r) r}

lemma isCompact_cube (r : ℝ) : IsCompact (cube r) := by
  have : cube r = Set.univ.pi fun _ : Fin 3 => Set.univ.pi fun _ : Fin 3 => Icc (-r) r := by
    ext F
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc

lemma mem_cube_of_frob_le {F : Mat 3 3} {r : ℝ} (hr : 0 ≤ r) (h : frob F ≤ r ^ 2) :
    F ∈ cube r := by
  intro i j
  have := (sq_le_frob F i j).trans h
  constructor <;> nlinarith

/-- **Lemma 6.1(iv)**: for `σ` small, `{γ_σ ≤ 5σ}` is contained in the given neighbourhood `U` of
`SO(3)`. (We use the compact set `cube 3 \ U ⊇ {|F|² ≤ 5} \ U` and `σ = m/6`.) -/
lemma exists_sigma {U : Set (Mat 3 3)} (hU : IsOpen U) (hSO : SO 3 ⊆ U) :
    ∃ σ > 0, ∀ F, gam σ F ≤ 5 * σ → F ∈ U := by
  set K := cube 3 \ U
  have hK : IsCompact K := (isCompact_cube 3).diff hU
  obtain ⟨m, hm, hmK⟩ : ∃ m > 0, ∀ F ∈ K, m ≤ g0 F := by
    rcases K.eq_empty_or_nonempty with h | hne
    · exact ⟨1, one_pos, by simp [h]⟩
    obtain ⟨F0, hF0, hmin⟩ := hK.exists_isMinOn hne continuous_g0.continuousOn
    exact ⟨g0 F0, lt_of_le_of_ne (g0_nonneg F0) fun h =>
      hF0.2 (hSO (mem_SO_of_g0_eq_zero h.symm)), fun F hF => hmin hF⟩
  have hσ : (0 : ℝ) < m / 6 := by positivity
  refine ⟨m / 6, hσ, fun F hF => ?_⟩
  by_contra hFU
  have h8 : frob F ≤ 5 := by
    have := (frob_le_gam _ F).trans hF
    have : m / 6 * frob F ≤ m / 6 * 5 := by linarith
    exact le_of_mul_le_mul_left this hσ
  have hc : F ∈ cube 3 := mem_cube_of_frob_le (by norm_num) (by linarith)
  have := hmK F ⟨hc, hFU⟩
  have := g0_le_gam hσ.le F
  linarith

/-! ### Polynomial growth of the second variation (Lemma 6.1(v)) -/

/-! `Qg e X` is quadratic and `Lg e Y` is cubic in `e`; we extract the homogeneous parts by
evaluating at `0`, `±e` and `±2e`. -/

def Qg1 (e X : Mat 3 3) : ℝ := (Qg e X - Qg (-e) X) / 2
def Qg2 (e X : Mat 3 3) : ℝ := (Qg e X + Qg (-e) X) / 2 - Qg 0 X
def Lg3 (e Y : Mat 3 3) : ℝ :=
  ((Lg ((2 : ℝ) • e) Y - Lg (-((2 : ℝ) • e)) Y) / 2 - (Lg e Y - Lg (-e) Y)) / 6
def Lg1 (e Y : Mat 3 3) : ℝ := (Lg e Y - Lg (-e) Y) / 2 - Lg3 e Y
def Lg2 (e Y : Mat 3 3) : ℝ := (Lg e Y + Lg (-e) Y) / 2 - Lg 0 Y

lemma Qg_smul_left (c : ℝ) (e X : Mat 3 3) :
    Qg (c • e) X = Qg 0 X + c * Qg1 e X + c ^ 2 * Qg2 e X := by
  simp only [Qg1, Qg2, Qg, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Matrix.neg_apply]
  ring

lemma Lg_smul_left (c : ℝ) (e Y : Mat 3 3) :
    Lg (c • e) Y = Lg 0 Y + c * Lg1 e Y + c ^ 2 * Lg2 e Y + c ^ 3 * Lg3 e Y := by
  simp only [Lg1, Lg2, Lg3, Lg, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply,
    Matrix.neg_apply]
  ring

lemma frob_smul (c : ℝ) (X : Mat 3 3) : frob (c • X) = c ^ 2 * frob X := by
  simp only [frob_eq, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring

lemma symPart_smul (s : ℝ) (X : Mat 3 3) : symPart (s • X) = s • symPart X := by
  simp only [symPart, transpose_smul, ← smul_add, smul_smul, mul_comm s]

lemma gM_smul (G A : Mat 3 3) (s : ℝ) : gM G (s • A) = s ^ 2 * gM G A := by
  have h2 : (1 / 2 : ℝ) • ((s • A)ᵀ * (s • A)) = (s ^ 2) • ((1 / 2 : ℝ) • (Aᵀ * A)) := by
    rw [transpose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, smul_smul]
    ring_nf
  rw [gM, mul_smul_comm, symPart_smul, h2, Qg_smul, Lg_smul, gM]; ring

/-- The homogenized second variation: `l⁶ gM (l⁻¹ H) A = gMh l H A` (`gM_homog`). -/
def gMh (l : ℝ) (H A : Mat 3 3) : ℝ :=
  2 * (l ^ 4 * Qg 0 (symPart (Hᵀ * A))
      + l ^ 2 * Qg1 ((1 / 2 : ℝ) • (Hᵀ * H - l ^ 2 • 1)) (symPart (Hᵀ * A))
      + Qg2 ((1 / 2 : ℝ) • (Hᵀ * H - l ^ 2 • 1)) (symPart (Hᵀ * A)))
    + 2 * (l ^ 6 * Lg 0 ((1 / 2 : ℝ) • (Aᵀ * A))
      + l ^ 4 * Lg1 ((1 / 2 : ℝ) • (Hᵀ * H - l ^ 2 • 1)) ((1 / 2 : ℝ) • (Aᵀ * A))
      + l ^ 2 * Lg2 ((1 / 2 : ℝ) • (Hᵀ * H - l ^ 2 • 1)) ((1 / 2 : ℝ) • (Aᵀ * A))
      + Lg3 ((1 / 2 : ℝ) • (Hᵀ * H - l ^ 2 • 1)) ((1 / 2 : ℝ) • (Aᵀ * A)))

lemma gM_homog {l : ℝ} (hl : l ≠ 0) (H A : Mat 3 3) : l ^ 6 * gM (l⁻¹ • H) A = gMh l H A := by
  have hE : strain (l⁻¹ • H) = (l⁻¹ ^ 2) • ((1 / 2 : ℝ) • (Hᵀ * H - l ^ 2 • 1)) := by
    rw [strain, transpose_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    match_scalars <;> field_simp
  have hX : symPart ((l⁻¹ • H)ᵀ * A) = l⁻¹ • symPart (Hᵀ * A) := by
    rw [transpose_smul, smul_mul_assoc, symPart_smul]
  rw [gM, hE, hX, Qg_smul, Qg_smul_left, Lg_smul_left, gMh]
  field_simp

lemma continuous_gMh : Continuous fun p : ℝ × Mat 3 3 × Mat 3 3 => gMh p.1 p.2.1 p.2.2 := by
  have hH : Continuous fun p : ℝ × Mat 3 3 × Mat 3 3 => p.2.1 := continuous_snd.fst
  have hA : Continuous fun p : ℝ × Mat 3 3 × Mat 3 3 => p.2.2 := continuous_snd.snd
  have hl : Continuous fun p : ℝ × Mat 3 3 × Mat 3 3 => p.1 := continuous_fst
  have hX : Continuous fun p : ℝ × Mat 3 3 × Mat 3 3 => symPart (p.2.1ᵀ * p.2.2) :=
    continuous_symPart.comp (hH.matrix_transpose.matrix_mul hA)
  have hAA : Continuous fun p : ℝ × Mat 3 3 × Mat 3 3 => p.2.2ᵀ * p.2.2 :=
    hA.matrix_transpose.matrix_mul hA
  have hY : Continuous fun p : ℝ × Mat 3 3 × Mat 3 3 => (1 / 2 : ℝ) • (p.2.2ᵀ * p.2.2) :=
    hAA.const_smul (1 / 2 : ℝ)
  have hHH : Continuous fun p : ℝ × Mat 3 3 × Mat 3 3 => p.2.1ᵀ * p.2.1 - p.1 ^ 2 • (1 : Mat 3 3) :=
    (hH.matrix_transpose.matrix_mul hH).sub ((hl.pow 2).smul continuous_const)
  have hE : Continuous fun p : ℝ × Mat 3 3 × Mat 3 3 =>
      (1 / 2 : ℝ) • (p.2.1ᵀ * p.2.1 - p.1 ^ 2 • (1 : Mat 3 3)) :=
    hHH.const_smul (1 / 2 : ℝ)
  unfold gMh Qg1 Qg2 Lg1 Lg2 Lg3
  have hc0 : Continuous fun _ : ℝ × Mat 3 3 × Mat 3 3 => (0 : Mat 3 3) := continuous_const
  have h2E := hE.const_smul (2 : ℝ)
  have := continuous_Qg_comp hc0 hX
  have := continuous_Qg_comp hE hX
  have := continuous_Qg_comp hE.neg hX
  have := continuous_Lg_comp hc0 hY
  have := continuous_Lg_comp hE hY
  have := continuous_Lg_comp hE.neg hY
  have := continuous_Lg_comp h2E hY
  have := continuous_Lg_comp h2E.neg hY
  fun_prop

/-- **Lemma 6.1(v)** (growth bound): `D²W₀(G)[A, A] ≥ -C (1 + |G|²)³ |A|²`. -/
lemma exists_gM_lower :
    ∃ C, 0 ≤ C ∧ ∀ G A : Mat 3 3, -(C * (1 + frob G) ^ 3 * frob A) ≤ gM G A := by
  set S : Set (ℝ × Mat 3 3 × Mat 3 3) := Icc 0 1 ×ˢ (cube 1 ×ˢ {A | frob A = 1})
  have hS : IsCompact S := isCompact_Icc.prod ((isCompact_cube 1).prod
    ((isCompact_cube 1).of_isClosed_subset (isClosed_eq continuous_frob continuous_const)
      fun A hA => mem_cube_of_frob_le zero_le_one (by rw [hA]; norm_num)))
  obtain ⟨C₀, hC₀⟩ := hS.exists_bound_of_continuousOn continuous_gMh.continuousOn
  set C := max C₀ 0
  refine ⟨C, le_max_right _ _, fun G A => ?_⟩
  -- normalize `A`
  rcases (frob_nonneg A).eq_or_lt with hA0 | hApos
  · have hA : A = 0 := eq_zero_of_frob_eq_zero hA0.symm
    have := gM_smul G 0 0
    simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      at this
    rw [hA, this]; simp [frob]
  set s := √(frob A)
  have hs : 0 < s := Real.sqrt_pos.2 hApos
  set B := s⁻¹ • A
  have hB : frob B = 1 := by
    rw [frob_smul, inv_pow, Real.sq_sqrt hApos.le, inv_mul_cancel₀ hApos.ne']
  have hAB : gM G A = frob A * gM G B := by
    have hA' : A = s • B := by simp only [B, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    have hs2 : s ^ 2 = frob A := Real.sq_sqrt hApos.le
    calc gM G A = gM G (s • B) := by rw [← hA']
      _ = frob A * gM G B := by rw [gM_smul, hs2]
  -- normalize `G`
  have hG0 := frob_nonneg G
  set r := √(1 + frob G)
  have hr : 1 ≤ r := Real.one_le_sqrt.2 (by linarith)
  have hr2 : r ^ 2 = 1 + frob G := Real.sq_sqrt (by linarith)
  set l := r⁻¹
  have hl : 0 < l := inv_pos.2 (by linarith)
  have hl1 : l ≤ 1 := inv_le_one_of_one_le₀ hr
  have hH : l • G ∈ cube 1 := by
    refine mem_cube_of_frob_le zero_le_one ?_
    rw [frob_smul, inv_pow, hr2, one_pow, inv_mul_le_one₀ (by linarith)]
    linarith
  have hbd := hC₀ (l, l • G, B) ⟨⟨hl.le, hl1⟩, hH, hB⟩
  have hhom := gM_homog hl.ne' (l • G) B
  rw [smul_smul, inv_mul_cancel₀ hl.ne', one_smul] at hhom
  simp only [Real.norm_eq_abs] at hbd
  have hGB : -(C * (1 + frob G) ^ 3) ≤ gM G B := by
    have h1 : -C ≤ l ^ 6 * gM G B := by
      rw [hhom]; linarith [neg_abs_le (gMh l (l • G) B), le_max_left C₀ 0]
    have h2 : r ^ 6 * l ^ 6 = 1 := by rw [← mul_pow, mul_inv_cancel₀ (by linarith), one_pow]
    have h3 : (1 + frob G) ^ 3 = r ^ 6 := by rw [← hr2]; ring
    rw [h3]
    have : r ^ 6 * (-C) ≤ r ^ 6 * (l ^ 6 * gM G B) := mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [← mul_assoc, h2, one_mul] at this
    linarith
  rw [hAB]
  have := mul_le_mul_of_nonneg_left hGB hApos.le
  linarith

/-! ### The cutoff `χ` -/

/-- The smooth nondecreasing step `η(r) = smoothTransition ((r - 4σ)/σ)`, with `η = 0` on
`(-∞, 4σ]` and `η = 1` on `[5σ, ∞)`. -/
def eta (σ r : ℝ) : ℝ := Real.smoothTransition ((r - 4 * σ) / σ)

/-- `χ'(s) = 4 η(s) (s - 4σ)³`. -/
def chi1 (σ s : ℝ) : ℝ := 4 * eta σ s * (s - 4 * σ) ^ 3

/-- The cutoff `χ(s) = ∫_{4σ}^s 4 η(r) (r - 4σ)³ dr` of the proof of Theorem 1.1. -/
def chi (σ s : ℝ) : ℝ := ∫ r in (4 * σ)..s, chi1 σ r

lemma contDiff_chi1 (σ : ℝ) : ContDiff ℝ ∞ (chi1 σ) := by
  have hη : ContDiff ℝ ∞ (eta σ) :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_id.sub contDiff_const).div_const σ)
  exact (contDiff_const.mul hη).mul ((contDiff_id.sub contDiff_const).pow 3)

lemma eta_of_le {σ s : ℝ} (hσ : 0 < σ) (hs : s ≤ 4 * σ) : eta σ s = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hσ.le)

lemma eta_of_ge {σ s : ℝ} (hσ : 0 < σ) (hs : 5 * σ ≤ s) : eta σ s = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hσ]; linarith)

lemma chi1_of_le {σ s : ℝ} (hσ : 0 < σ) (hs : s ≤ 4 * σ) : chi1 σ s = 0 := by
  simp [chi1, eta_of_le hσ hs]

/-- `χ'(s) = 4 (s - 4σ)³` for `s ≥ 5σ`. -/
lemma chi1_of_ge {σ s : ℝ} (hσ : 0 < σ) (hs : 5 * σ ≤ s) : chi1 σ s = 4 * (s - 4 * σ) ^ 3 := by
  simp [chi1, eta_of_ge hσ hs]

/-- `χ' ≥ 0`. -/
lemma chi1_nonneg {σ : ℝ} (hσ : 0 < σ) (s : ℝ) : 0 ≤ chi1 σ s := by
  rcases le_or_gt s (4 * σ) with hs | hs
  · rw [chi1_of_le hσ hs]
  · exact mul_nonneg (mul_nonneg (by norm_num) (Real.smoothTransition.nonneg _))
      (pow_nonneg (by linarith) 3)

/-- `χ'` is nondecreasing, i.e. `χ` is convex. -/
lemma chi1_monotone {σ : ℝ} (hσ : 0 < σ) : Monotone (chi1 σ) := by
  intro s s' h
  rcases le_or_gt s (4 * σ) with hs | hs
  · rw [chi1_of_le hσ hs]; exact chi1_nonneg hσ s'
  · have hη : eta σ s ≤ eta σ s' :=
      Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hσ.le)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hη (by norm_num))
      (pow_le_pow_left₀ (by linarith) (by linarith) 3) (pow_nonneg (by linarith) 3)
      (mul_nonneg (by norm_num) (Real.smoothTransition.nonneg _))

lemma hasDerivAt_chi (σ s : ℝ) : HasDerivAt (chi σ) (chi1 σ s) s :=
  ((contDiff_chi1 σ).continuous.integral_hasStrictDerivAt (4 * σ) s).hasDerivAt

lemma hasDerivAt_chi1 (σ s : ℝ) : HasDerivAt (chi1 σ) (deriv (chi1 σ) s) s :=
  ((contDiff_chi1 σ).differentiable (by simp) s).hasDerivAt

/-- `χ'' ≥ 0`. -/
lemma deriv_chi1_nonneg {σ : ℝ} (hσ : 0 < σ) (s : ℝ) : 0 ≤ deriv (chi1 σ) s :=
  (chi1_monotone hσ).deriv_nonneg

/-- `χ = 0` on `(-∞, 4σ]`. -/
lemma chi_of_le {σ s : ℝ} (hσ : 0 < σ) (hs : s ≤ 4 * σ) : chi σ s = 0 := by
  rw [chi, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
  intro r hr
  rw [Set.uIcc_of_ge hs] at hr
  exact chi1_of_le hσ hr.2

lemma contDiff_chi (σ : ℝ) : ContDiff ℝ ∞ (chi σ) := by
  have h : deriv (chi σ) = chi1 σ := funext fun s => (hasDerivAt_chi σ s).deriv
  exact contDiff_infty_iff_deriv.2 ⟨fun s => (hasDerivAt_chi σ s).differentiableAt,
    h ▸ contDiff_chi1 σ⟩

/-- `W₀` is smooth (in the entries of the matrix). -/
lemma contDiff_W0 : ContDiff ℝ ∞ (fun X : Fin 3 → Fin 3 → ℝ => W0 (Matrix.of X)) := by
  simp only [W0, g, strain, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply,
    Fin.sum_univ_three, transpose_apply, of_apply, Matrix.one_apply, smul_eq_mul]
  fun_prop

lemma contDiff_gam (σ : ℝ) : ContDiff ℝ ∞ (fun X : Fin 3 → Fin 3 → ℝ => gam σ (Matrix.of X)) := by
  simp only [gam, g0, frob, cof, trace, diag, Matrix.sub_apply, Matrix.mul_apply,
    Fin.sum_univ_three, transpose_apply, of_apply, adjugate_fin_three, det_fin_three]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const]
  fun_prop

/-! ### Globalization -/

/-- **Proof of Theorem 1.1** (Section 6). If `D²W₀(G)[a⊗b, a⊗b] ≥ 0` for `G` in an open
neighbourhood `U` of `SO(3)`, then `W = W₀ + K χ ∘ γ_σ` is `C^∞` (as a function of the entries;
`Mat 3 3` carries no norm instance), frame indifferent and rank-one convex, and `W = W₀` near
`SO(3)`. -/
theorem exists_globalization (U : Set (Mat 3 3)) (hU : IsOpen U) (hSO : SO 3 ⊆ U)
    (hpos : ∀ G ∈ U, ∀ a b : Fin 3 → ℝ, 0 ≤ gM G (vecMulVec a b)) :
    ∃ W : Mat 3 3 → ℝ, Continuous W ∧ ContDiff ℝ ∞ (fun X : Fin 3 → Fin 3 → ℝ => W (Matrix.of X)) ∧
      FrameIndifferent W ∧ RankOneConvex W ∧ ∀ᶠ F in 𝓝ˢ (SO 3), W F = W0 F := by
  obtain ⟨σ, hσ, hσU⟩ := exists_sigma hU hSO
  obtain ⟨C, hC0, hC⟩ := exists_gM_lower
  set K := 27 * C / σ ^ 4 + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  set Φ : Mat 3 3 → ℝ := fun F => K * chi σ (gam σ F)
  refine ⟨W0 + Φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_W0.add (continuous_const.mul
      ((contDiff_chi σ).continuous.comp (continuous_gam σ)))
  · exact contDiff_W0.add (contDiff_const.mul ((contDiff_chi σ).comp (contDiff_gam σ)))
  · refine frameIndifferent_W0.add fun Q hQ F => ?_
    simp only [Φ, gam_mul_of_mem_SO σ hQ]
  · -- rank-one convexity: `f'' ≥ 0` for `f(t) = W(F + tA)`
    intro F a b
    set A := vecMulVec a b
    set g1 := gam1 σ F a b
    set g2 := gam2 σ F a b
    have hg2 : σ * frob A ≤ g2 := gam2_ge σ F a b
    have hA0 := frob_nonneg A
    -- `h(t) = γ_σ (F + tA)`
    set q : ℝ → ℝ := fun t => gam σ (F + t • A)
    have hq : ∀ t, HasDerivAt q (g1 + 2 * t * g2) t := fun t => by
      have : q = fun t => gam σ F + t * g1 + t ^ 2 * g2 := funext fun t => gam_line σ F a b t
      rw [this]
      exact (((hasDerivAt_id t).mul_const g1).const_add _).add
        ((hasDerivAt_pow 2 t).mul_const g2) |>.congr_deriv (by simp)
    have hq' : ∀ t, HasDerivAt (fun t => g1 + 2 * t * g2) (2 * g2) t := fun t =>
      ((((hasDerivAt_id t).const_mul 2).mul_const g2).const_add g1).congr_deriv (by ring)
    set f' : ℝ → ℝ := fun t => d1 (F + t • A) A + K * (chi1 σ (q t) * (g1 + 2 * t * g2))
    set f'' : ℝ → ℝ := fun t => gM (F + t • A) A
      + K * (deriv (chi1 σ) (q t) * (g1 + 2 * t * g2) * (g1 + 2 * t * g2)
        + chi1 σ (q t) * (2 * g2))
    have hf : ∀ t, HasDerivAt (fun t => (W0 + Φ) (F + t • A)) (f' t) t := fun t =>
      (hasDerivAt_W0_line F A t).add (((hasDerivAt_chi σ (q t)).comp t (hq t)).const_mul K)
    have hf' : ∀ t, HasDerivAt f' (f'' t) t := fun t =>
      (hasDerivAt_d1_line F A t).add
        ((((hasDerivAt_chi1 σ (q t)).comp t (hq t)).mul (hq' t)).const_mul K)
    refine convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (fun t _ => (hf t).continuousAt.continuousWithinAt)
      (fun t _ => (hf t).hasDerivWithinAt) (fun t _ => (hf' t).hasDerivWithinAt)
      fun t _ => ?_
    set G := F + t • A
    have hg2' : 0 ≤ g2 := le_trans (by positivity) hg2
    have hχ2 : 0 ≤ deriv (chi1 σ) (q t) * (g1 + 2 * t * g2) * (g1 + 2 * t * g2) := by
      rw [mul_assoc]; exact mul_nonneg (deriv_chi1_nonneg hσ _) (mul_self_nonneg _)
    have hχ1 : 0 ≤ chi1 σ (q t) := chi1_nonneg hσ _
    by_cases hlt : gam σ G < 5 * σ
    · -- near `SO(3)`: Proposition 4.2
      have := hpos G (hσU G hlt.le) a b
      have : 0 ≤ K * (deriv (chi1 σ) (q t) * (g1 + 2 * t * g2) * (g1 + 2 * t * g2)
          + chi1 σ (q t) * (2 * g2)) := by positivity
      simp only [f'']; linarith
    · -- away from `SO(3)`: `χ'(h) h''` dominates the growth of `D²W₀`
      push Not at hlt
      have hqt : q t = gam σ G := rfl
      set p := gam σ G - 4 * σ
      have hχ : chi1 σ (q t) = 4 * p ^ 3 := chi1_of_ge hσ (by rw [hqt]; exact hlt)
      have hGC := hC G A
      have hγ := frob_le_gam σ G
      have hG0 := frob_nonneg G
      -- `1 + |G|² ≤ 6 γ / (5σ)` and `p ≥ γ / 5`
      have h1 : 1 + frob G ≤ 6 * gam σ G / (5 * σ) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have h3 : gam σ G / 5 ≤ p := by simp only [p]; linarith
      have hp0 : 0 ≤ p := by simp only [p]; linarith
      have key : C * (1 + frob G) ^ 3 * frob A ≤ K * (chi1 σ (q t) * (2 * g2)) := by
        calc C * (1 + frob G) ^ 3 * frob A ≤ C * (6 * gam σ G / (5 * σ)) ^ 3 * frob A := by
              gcongr
          _ = 27 * C / σ ^ 4 * (8 * (gam σ G / 5) ^ 3 * (σ * frob A)) := by
              field_simp; ring
          _ ≤ K * (8 * p ^ 3 * g2) := by
              have e1 : (gam σ G / 5) ^ 3 ≤ p ^ 3 := pow_le_pow_left₀ (by linarith) h3 3
              have e2 : 27 * C / σ ^ 4 ≤ K := by linarith
              have hγ0 : 0 ≤ gam σ G := by linarith
              exact mul_le_mul e2 (mul_le_mul (by linarith) hg2 (by positivity)
                (mul_nonneg (by norm_num) (pow_nonneg hp0 3))) (by positivity) hK0
          _ = K * (chi1 σ (q t) * (2 * g2)) := by rw [hχ]; ring
      have : 0 ≤ K * (deriv (chi1 σ) (q t) * (g1 + 2 * t * g2) * (g1 + 2 * t * g2)) := by
        positivity
      simp only [f'']; nlinarith
  · -- `W = W₀` on the open set `{γ_σ < 4σ} ⊇ SO(3)`
    have hopen : IsOpen {F : Mat 3 3 | gam σ F < 4 * σ} :=
      isOpen_lt (continuous_gam σ) continuous_const
    have hsub : SO 3 ⊆ {F : Mat 3 3 | gam σ F < 4 * σ} := fun Q hQ => by
      change gam σ Q < 4 * σ
      rw [gam_of_mem_SO σ hQ]; linarith
    filter_upwards [hopen.mem_nhdsSet.2 hsub] with F hF
    simp only [Pi.add_apply, Φ, add_eq_left]
    rw [chi_of_le hσ (le_of_lt hF), mul_zero]

end QcSOn
