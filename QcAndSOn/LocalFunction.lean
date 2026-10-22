/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import QcAndSOn.Defs

/-!
# The local function `W₀` (Section 3)

`g : Sym(3) → ℝ` is the explicit quartic polynomial of eq. (3.1) of the paper (only the entries
`e₁₁, e₂₂, e₃₃, e₁₂, e₁₃, e₂₃` are used) and `W₀ F = g (½ (Fᵀ F - Id))` (eq. (3.2)).
-/

open Matrix

noncomputable section

namespace QcSOn

/-- The symmetric part `sym F = ½ (F + Fᵀ)`. -/
def symPart (F : Mat 3 3) : Mat 3 3 := (1 / 2 : ℝ) • (F + Fᵀ)

/-- The Green–St. Venant strain `e = ½ (Fᵀ F - Id)`. -/
def strain (F : Mat 3 3) : Mat 3 3 := (1 / 2 : ℝ) • (Fᵀ * F - 1)

lemma strain_transpose (F : Mat 3 3) : (strain F)ᵀ = strain F := by
  simp [strain, transpose_sub, transpose_mul]

/-- The quartic polynomial of eq. (3.1) of the paper,
`g(e) = 2e₃₃ + q(e) + e₁₁e₂₂(e₁₁ + e₂₂ + e₁₃ + e₂₃) + (e₁₃ + e₂₃)²(e₁₁ + e₂₂ - 4e₁₂) + 3|e|⁴`,
with `q(e) = 4e₁₂² - 2e₁₁e₂₂ + 4(e₁₃ - e₂₃)²` (eq. (2.1)), in terms of the upper triangular
entries of `e` (for symmetric `e`, `|e|² = e₁₁² + e₂₂² + e₃₃² + 2(e₁₂² + e₁₃² + e₂₃²)`). -/
def g (e : Mat 3 3) : ℝ :=
  let e11 := e 0 0; let e22 := e 1 1; let e33 := e 2 2
  let e12 := e 0 1; let e13 := e 0 2; let e23 := e 1 2
  2 * e33 + (4 * e12 ^ 2 - 2 * e11 * e22 + 4 * (e13 - e23) ^ 2)
    + e11 * e22 * (e11 + e22 + e13 + e23) + (e13 + e23) ^ 2 * (e11 + e22 - 4 * e12)
    + 3 * (e11 ^ 2 + e22 ^ 2 + e33 ^ 2 + 2 * (e12 ^ 2 + e13 ^ 2 + e23 ^ 2)) ^ 2

/-- The local energy `W₀ F = g (½ (Fᵀ F - Id))` (eq. (3.2)). -/
def W0 (F : Mat 3 3) : ℝ := g (strain F)

lemma continuous_g : Continuous g := by
  unfold g; fun_prop

lemma continuous_strain : Continuous strain := by
  have h : Continuous fun F : Mat 3 3 => Fᵀ * F - 1 :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).sub continuous_const
  exact h.const_smul (1 / 2 : ℝ)

lemma continuous_W0 : Continuous W0 :=
  continuous_g.comp continuous_strain

@[simp] lemma W0_one : W0 1 = 0 := by
  simp [W0, g, strain]

/-- `W₀` is frame indifferent (indeed `O(3)`-invariant). -/
lemma frameIndifferent_W0 : FrameIndifferent W0 := by
  intro Q hQ F
  have hQ' : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).1 hQ.1
  simp only [W0, strain, Matrix.transpose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ', Matrix.one_mul]

end QcSOn
