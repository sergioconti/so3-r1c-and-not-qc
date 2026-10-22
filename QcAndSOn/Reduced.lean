/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import QcAndSOn.SecondVariation

/-!
# The reduced second variation (Section 3)

By frame indifference, `D²W₀(G)[a⊗b, a⊗b]` only depends on `e = ½ (GᵀG - Id)`, `c = Gᵀa` and `b`;
using `|a|² = cᵀ cof(Id + 2e) c / det(Id + 2e)` and clearing the denominator we obtain the
polynomial `Pc e c b = 2 det(Id+2e) Q_e(c⊙b) + (cᵀ cof(Id+2e) c) L_e(b⊗b)` of eq. (3.4), with
`det (GᵀG) · D²W₀(G)[a⊗b, a⊗b] = Pc (½ (GᵀG - Id)) (Gᵀa) b` (`det_mul_gM`, Lemma 3.3).

* `cof`, `transpose_mul_cof`, `cof_mul_transpose`, `cof_transpose`, `cof_mul`: eq. (1.3);
* `Pc_zero`: at `e = 0`, `Pc 0 c b = 2 Q(c,b)`, with `Q(c,b)` the sum of squares of Lemma 3.1;
* `sosQ_eq_zero`: zero set of `Q` (the three Šverák modes, Lemma 3.1);
* `Pc_smul`: `Pc e (λc) (μb) = λ²μ² Pc e c b` (Lemma 3.3).
-/

open Matrix

noncomputable section

namespace QcSOn

/-! ### Cofactors (eq. (1.3)) -/

/-- The cofactor matrix `cof F = (adj F)ᵀ`. -/
def cof (F : Mat 3 3) : Mat 3 3 := (adjugate F)ᵀ

lemma transpose_mul_cof (F : Mat 3 3) : Fᵀ * cof F = det F • (1 : Mat 3 3) := by
  rw [cof, ← transpose_mul, adjugate_mul, transpose_smul, transpose_one]

lemma cof_mul_transpose (F : Mat 3 3) : cof F * Fᵀ = det F • (1 : Mat 3 3) := by
  rw [cof, ← transpose_mul, mul_adjugate, transpose_smul, transpose_one]

lemma cof_transpose (F : Mat 3 3) : cof Fᵀ = (cof F)ᵀ := by
  simp only [cof, adjugate_transpose]

lemma cof_mul (A B : Mat 3 3) : cof (A * B) = cof A * cof B := by
  rw [cof, cof, cof, adjugate_mul_distrib, transpose_mul]

lemma cof_one : cof (1 : Mat 3 3) = 1 := by
  rw [cof, adjugate_one, transpose_one]

lemma continuous_cof : Continuous (cof : Mat 3 3 → Mat 3 3) :=
  continuous_id.matrix_adjugate.matrix_transpose

/-! ### The polynomial `P` -/

/-- The symmetric matrix with the upper triangular entries of `E`. -/
def symU (E : Mat 3 3) : Mat 3 3 :=
  !![E 0 0, E 0 1, E 0 2; E 0 1, E 1 1, E 1 2; E 0 2, E 1 2, E 2 2]

lemma symU_eq_self {E : Mat 3 3} (hE : Eᵀ = E) : symU E = E := by
  have h : ∀ i j, E j i = E i j := fun i j => by rw [← transpose_apply E i j, hE]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symU, h 0 1, h 0 2, h 1 2]

/-- The reduced second variation `P(e,c,b) = 2 det(Id+2e) Q_e(c⊙b) + (cᵀ cof(Id+2e) c) L_e(b⊗b)`
(eq. (3.4)), with `c ⊙ b = sym (c ⊗ b)`. -/
def Pc (e : Mat 3 3) (c b : Fin 3 → ℝ) : ℝ :=
  2 * det (1 + (2 : ℝ) • e) * Qg e (symPart (vecMulVec c b))
    + (c ⬝ᵥ (cof (1 + (2 : ℝ) • e) *ᵥ c)) * Lg e (vecMulVec b b)

lemma Lg_smul (e X : Mat 3 3) (s : ℝ) : Lg e (s • X) = s * Lg e X := by
  simp only [Lg, Matrix.smul_apply, smul_eq_mul]; ring

lemma Qg_smul (e X : Mat 3 3) (s : ℝ) : Qg e (s • X) = s ^ 2 * Qg e X := by
  simp only [Qg, Matrix.smul_apply, smul_eq_mul]; ring

lemma one_add_two_smul_strain (G : Mat 3 3) : 1 + (2 : ℝ) • strain G = Gᵀ * G := by
  rw [strain, smul_smul]; norm_num

/-- `(Gᵀa)ᵀ cof(GᵀG) (Gᵀa) = det(GᵀG) |a|²`, from `cof(GᵀG) = (cof G)ᵀ cof G` and
`(cof G) Gᵀ = det G · Id`. -/
lemma cof_quadratic (G : Mat 3 3) (a : Fin 3 → ℝ) :
    (Gᵀ *ᵥ a) ⬝ᵥ (cof (Gᵀ * G) *ᵥ (Gᵀ *ᵥ a)) = det (Gᵀ * G) * (a ⬝ᵥ a) := by
  have h : G * cof (Gᵀ * G) * Gᵀ = det (Gᵀ * G) • (1 : Mat 3 3) :=
    calc G * cof (Gᵀ * G) * Gᵀ = (cof G * Gᵀ)ᵀ * (cof G * Gᵀ) := by
          rw [cof_mul, cof_transpose, transpose_mul, transpose_transpose]
          simp only [Matrix.mul_assoc]
      _ = det (Gᵀ * G) • (1 : Mat 3 3) := by
          rw [cof_mul_transpose, transpose_smul, transpose_one, smul_mul_smul_comm, Matrix.one_mul,
            det_mul, det_transpose]
  rw [mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, ← mulVec_transpose, mulVec_mulVec,
    h, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

lemma symPart_vecMulVec (c b : Fin 3 → ℝ) :
    symPart (vecMulVec c b) = (1 / 2 : ℝ) • (vecMulVec c b + vecMulVec b c) := by
  rw [symPart, transpose_vecMulVec]

/-- **Lemma 3.3** (reduction): `det(GᵀG) · D²W₀(G)[a⊗b, a⊗b] = P(½(GᵀG - Id), Gᵀa, b)`. -/
lemma det_mul_gM (G : Mat 3 3) (a b : Fin 3 → ℝ) :
    det (Gᵀ * G) * gM G (vecMulVec a b) = Pc (strain G) (Gᵀ *ᵥ a) b := by
  have h1 : Gᵀ * vecMulVec a b = vecMulVec (Gᵀ *ᵥ a) b := by
    rw [mul_vecMulVec]
  have h2 : (vecMulVec a b)ᵀ * vecMulVec a b = (a ⬝ᵥ a) • vecMulVec b b := by
    rw [transpose_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_smul]
  rw [gM, Pc, h1, h2, smul_smul, Lg_smul, one_add_two_smul_strain, cof_quadratic]
  ring

/-- Homogeneity in `c` and `b` (Lemma 3.3). -/
lemma Pc_smul (e : Mat 3 3) (c b : Fin 3 → ℝ) (l μ : ℝ) :
    Pc e (l • c) (μ • b) = l ^ 2 * μ ^ 2 * Pc e c b := by
  have h1 : symPart (vecMulVec (l • c) (μ • b)) = (l * μ) • symPart (vecMulVec c b) := by
    simp only [symPart, smul_vecMulVec, vecMulVec_smul, transpose_smul, smul_add, smul_smul]
    rw [mul_comm μ l, mul_comm (1 / 2 : ℝ)]
  have h2 : vecMulVec (μ • b) (μ • b) = (μ * μ) • vecMulVec b b := by
    simp only [smul_vecMulVec, vecMulVec_smul, smul_smul]
  rw [Pc, Pc, h1, h2, Qg_smul, Lg_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

lemma continuous_symU : Continuous symU := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> exact continuous_id.matrix_elem _ _

lemma continuous_Lg_comp {α : Type*} [TopologicalSpace α] {e X : α → Mat 3 3}
    (he : Continuous e) (hX : Continuous X) : Continuous fun a => Lg (e a) (X a) := by
  have he' : ∀ i j, Continuous fun a => e a i j := fun i j => (continuous_apply_apply i j).comp he
  have hX' : ∀ i j, Continuous fun a => X a i j := fun i j => (continuous_apply_apply i j).comp hX
  unfold Lg; fun_prop

lemma continuous_symPart : Continuous symPart := by
  unfold symPart
  exact (continuous_id.add continuous_id.matrix_transpose).const_smul (1 / 2 : ℝ)

lemma continuous_Pc : Continuous fun p : Mat 3 3 × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
    Pc (symU p.1) p.2.1 p.2.2 := by
  have hS : Continuous fun p : Mat 3 3 × (Fin 3 → ℝ) × (Fin 3 → ℝ) => symU p.1 :=
    continuous_symU.comp continuous_fst
  have hc : Continuous fun p : Mat 3 3 × (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.2.1 := by fun_prop
  have hb : Continuous fun p : Mat 3 3 × (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.2.2 := by fun_prop
  have h1 : Continuous fun p : Mat 3 3 × (Fin 3 → ℝ) × (Fin 3 → ℝ) => 1 + (2 : ℝ) • symU p.1 :=
    continuous_const.add (hS.const_smul (2 : ℝ))
  unfold Pc
  exact ((continuous_const.mul h1.matrix_det).mul (continuous_Qg_comp hS
    (continuous_symPart.comp (hc.matrix_vecMulVec hb)))).add
    ((hc.dotProduct ((continuous_cof.comp h1).matrix_mulVec hc)).mul
      (continuous_Lg_comp hS (hb.matrix_vecMulVec hb)))

/-- The sum of squares `Q(c,b)` of Lemma 3.1 (with `a = c`). -/
def sosQ (c b : Fin 3 → ℝ) : ℝ :=
  (c 0 * b 1) ^ 2 + (c 1 * b 0) ^ 2 + ((c 0 - c 1) * b 2 + c 2 * (b 0 - b 1)) ^ 2
    + (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) * b 2 ^ 2

/-- `P(0,c,b) = 2 Q(c,b) = 2 · sosQ c b` (Lemmas 3.1 and 3.3). -/
lemma Pc_zero (c b : Fin 3 → ℝ) : Pc 0 c b = 2 * sosQ c b := by
  rw [Pc, smul_zero, add_zero, det_one, cof_one, one_mulVec]
  simp only [sosQ, Qg, Lg, symPart, dotProduct, Fin.sum_univ_three, vecMulVec_apply,
    Matrix.add_apply, Matrix.smul_apply, transpose_apply, Matrix.zero_apply, smul_eq_mul]
  ring

lemma sosQ_nonneg (c b : Fin 3 → ℝ) : 0 ≤ sosQ c b := by
  unfold sosQ; positivity

/-- **Zero set** of `Q` (Lemma 3.1): for `c, b ≠ 0`, `Q(c,b) = 0` iff `c ⊗ b` is a multiple of
`e₁⊗e₁`, `e₂⊗e₂` or `e₃⊗(e₁+e₂)`. -/
lemma sosQ_eq_zero {c b : Fin 3 → ℝ} (hc : c ≠ 0) (hb : b ≠ 0) (h : sosQ c b = 0) :
    (c 1 = 0 ∧ c 2 = 0 ∧ b 1 = 0 ∧ b 2 = 0) ∨ (c 0 = 0 ∧ c 2 = 0 ∧ b 0 = 0 ∧ b 2 = 0) ∨
      (c 0 = 0 ∧ c 1 = 0 ∧ b 0 = b 1 ∧ b 2 = 0) := by
  unfold sosQ at h
  have n1 := sq_nonneg (c 0 * b 1)
  have n2 := sq_nonneg (c 1 * b 0)
  have n3 := sq_nonneg ((c 0 - c 1) * b 2 + c 2 * (b 0 - b 1))
  have n4 : 0 ≤ (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) * b 2 ^ 2 := by positivity
  have t1 : (c 0 * b 1) ^ 2 = 0 := by linarith
  have t2 : (c 1 * b 0) ^ 2 = 0 := by linarith
  have t3 : ((c 0 - c 1) * b 2 + c 2 * (b 0 - b 1)) ^ 2 = 0 := by linarith
  have t4 : (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) * b 2 ^ 2 = 0 := by linarith
  have hc' : c 0 ≠ 0 ∨ c 1 ≠ 0 ∨ c 2 ≠ 0 := by
    by_contra h'; push Not at h'
    exact hc (funext fun i => by fin_cases i <;> simp [h'])
  have hb' : b 0 ≠ 0 ∨ b 1 ≠ 0 ∨ b 2 ≠ 0 := by
    by_contra h'; push Not at h'
    exact hb (funext fun i => by fin_cases i <;> simp [h'])
  -- `b₂ = 0`
  have hb2 : b 2 = 0 := by
    rcases mul_eq_zero.1 t4 with h4 | h4
    · exfalso
      have h00 : c 0 = 0 := by nlinarith [sq_nonneg (c 0), sq_nonneg (c 1), sq_nonneg (c 2)]
      have h01 : c 1 = 0 := by nlinarith [sq_nonneg (c 0), sq_nonneg (c 1), sq_nonneg (c 2)]
      have h02 : c 2 = 0 := by nlinarith [sq_nonneg (c 0), sq_nonneg (c 1), sq_nonneg (c 2)]
      rcases hc' with h | h | h
      · exact h h00
      · exact h h01
      · exact h h02
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4
  have e1 : c 0 * b 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 t1
  have e2 : c 1 * b 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 t2
  have e3 : c 2 * (b 0 - b 1) = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 t3
    rw [hb2, mul_zero, zero_add] at this; exact this
  by_cases h2 : c 2 = 0
  · by_cases h0 : c 0 = 0
    · have h1 : c 1 ≠ 0 := by tauto
      have hb0 : b 0 = 0 := by simpa [h1] using e2
      exact Or.inr (Or.inl ⟨h0, h2, hb0, hb2⟩)
    · have hb1 : b 1 = 0 := by simpa [h0] using e1
      have hb0 : b 0 ≠ 0 := by tauto
      have h1 : c 1 = 0 := by simpa [hb0] using e2
      exact Or.inl ⟨h1, h2, hb1, hb2⟩
  · have hb01 : b 0 = b 1 := by
      rcases mul_eq_zero.1 e3 with h | h
      · exact absurd h h2
      · linarith
    have hb0 : b 0 ≠ 0 := by
      intro h0; rcases hb' with h | h | h
      · exact h h0
      · exact h (hb01 ▸ h0)
      · exact h hb2
    have h1 : c 1 = 0 := by simpa [hb0] using e2
    have h0 : c 0 = 0 := by simpa [hb01 ▸ hb0] using e1
    exact Or.inr (Or.inr ⟨h0, h1, hb01, hb2⟩)

end QcSOn
