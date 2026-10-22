/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import QcAndSOn.Reduced
import QcAndSOn.LocalMin

/-!
# Nondegeneracy at the modes (Lemma 3.4)

For the modes `k = 1, 3` we use the chart (3.7) (mode 2 follows by the symmetry (3.6), see
`RankOne.Pc_swap`) `y ∈ ℝ¹⁰ ↦ (E(y), c⁽ᵏ⁾(y), b⁽ᵏ⁾(y))`, where `E(y) = symY y` is the symmetric
matrix with upper triangular entries `y 0, …, y 5` (the entries of `e`), and show
`Pk y := P(E(y), c⁽ᵏ⁾(y), b⁽ᵏ⁾(y)) ≥ 0` for `y` near `0` (`Pk_eventually_nonneg`), via
`eventually_nonneg_of_expansion` (Lemma 4.1): `Pk (t y) = t² Qk y + t³ Rk t y`, where
`Qk y = yᵀ A_k y` with the matrices `A_k` of Lemma 3.4, and an explicit LDLᵀ certificate for
`Qk y - |y|²/4`. The expansion is assembled from second-order expansions of the four factors
`D = det(Id+2e)`, `α = cᵀ cof(Id+2e) c`, `Ly = L_e(b⊗b)`, `Qx = Q_e(c⊙b)` (see the README).
-/

open Matrix Filter Topology

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
-- the expansions of the quartic `g` are long polynomials
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

noncomputable section

namespace QcSOn

/-- The symmetric matrix `E(y)` with upper triangular entries `y 0, …, y 5`. -/
def symY (y : Fin 10 → ℝ) : Mat 3 3 := !![y 0, y 1, y 2; y 1, y 3, y 4; y 2, y 4, y 5]

/-- Remainder in the product of two second-order expansions. -/
def jetRem (a0 a1 a2 A b0 b1 b2 B t : ℝ) : ℝ :=
  a1 * b2 + a2 * b1 + a0 * B + A * b0 + t * (a2 * b2 + a1 * B + A * b1)
    + t ^ 2 * (a2 * B + A * b2) + t ^ 3 * (A * B)

lemma jet_mul (a0 a1 a2 A b0 b1 b2 B t : ℝ) :
    (a0 + t * a1 + t ^ 2 * a2 + t ^ 3 * A) * (b0 + t * b1 + t ^ 2 * b2 + t ^ 3 * B) =
      a0 * b0 + t * (a0 * b1 + a1 * b0) + t ^ 2 * (a0 * b2 + a1 * b1 + a2 * b0)
        + t ^ 3 * jetRem a0 a1 a2 A b0 b1 b2 B t := by
  unfold jetRem; ring

/-! ### The determinant factor (common to all charts) -/

def Dd_1 (y : Fin 10 → ℝ) : ℝ :=
  2 * (y 0) + 2 * (y 3) + 2 * (y 5)

def Dd_2 (y : Fin 10 → ℝ) : ℝ :=
  -4 * (y 1) ^ 2 - 4 * (y 2) ^ 2 - 4 * (y 4) ^ 2 + 4 * (y 0) * (y 3) + 4 * (y 0) * (y 5)
  + 4 * (y 3) * (y 5)

def Dd_R (_t : ℝ) (y : Fin 10 → ℝ) : ℝ :=
  -8 * (y 0) * (y 4) ^ 2 - 8 * (y 1) ^ 2 * (y 5) - 8 * (y 2) ^ 2 * (y 3)
  + 8 * (y 0) * (y 3) * (y 5) + 16 * (y 1) * (y 2) * (y 4)

lemma Dd_jet (t : ℝ) (y : Fin 10 → ℝ) :
    det (1 + (2 : ℝ) • symY (t • y)) =
      1 + t * Dd_1 y + t ^ 2 * Dd_2 y + t ^ 3 * Dd_R t y := by
  simp [symY, Pi.smul_apply, smul_eq_mul, det_fin_three, cof, adjugate_fin_three, dotProduct, mulVec, Fin.sum_univ_three, vecMulVec_apply, Lg, Qg, Dd_1, Dd_2, Dd_R, Matrix.one_apply]
  ring

lemma continuous_Dd_R : Continuous fun p : ℝ × (Fin 10 → ℝ) => Dd_R p.1 p.2 := by
  unfold Dd_R; fun_prop

/-! ### Mode 1: `c⁽1⁾(y) = ![1, y 6, y 7]`, `b⁽1⁾(y) = ![1, y 8, y 9]` -/

/-- The reduced second variation `P_1` in the chart of mode 1. -/
def P1 (y : Fin 10 → ℝ) : ℝ := Pc (symY y) ![1, y 6, y 7] ![1, y 8, y 9]

def al1_1 (y : Fin 10 → ℝ) : ℝ :=
  2 * (y 3) + 2 * (y 5)

def al1_2 (y : Fin 10 → ℝ) : ℝ :=
  -4 * (y 4) ^ 2 + (y 6) ^ 2 + (y 7) ^ 2 - 4 * (y 1) * (y 6) - 4 * (y 2) * (y 7)
  + 4 * (y 3) * (y 5)

def al1_R (t : ℝ) (y : Fin 10 → ℝ) : ℝ :=
  2 * (y 0) * (y 6) ^ 2 + 2 * (y 0) * (y 7) ^ 2 + 2 * (y 3) * (y 7) ^ 2 + 2 * (y 5) * (y 6) ^ 2
  - 4 * t * (y 1) ^ 2 * (y 7) ^ 2 - 4 * t * (y 2) ^ 2 * (y 6) ^ 2 + 8 * (y 1) * (y 4) * (y 7)
  - 8 * (y 1) * (y 5) * (y 6) - 8 * (y 2) * (y 3) * (y 7) + 8 * (y 2) * (y 4) * (y 6)
  - 4 * (y 4) * (y 6) * (y 7) + 4 * t * (y 0) * (y 3) * (y 7) ^ 2
  + 4 * t * (y 0) * (y 5) * (y 6) ^ 2 - 8 * t * (y 0) * (y 4) * (y 6) * (y 7)
  + 8 * t * (y 1) * (y 2) * (y 6) * (y 7)

lemma al1_jet (t : ℝ) (y : Fin 10 → ℝ) :
    ![1, (t • y) 6, (t • y) 7] ⬝ᵥ (cof (1 + (2 : ℝ) • symY (t • y)) *ᵥ ![1, (t • y) 6, (t • y) 7]) =
      1 + t * al1_1 y + t ^ 2 * al1_2 y + t ^ 3 * al1_R t y := by
  simp [symY, Pi.smul_apply, smul_eq_mul, det_fin_three, cof, adjugate_fin_three, dotProduct, mulVec, Fin.sum_univ_three, vecMulVec_apply, Lg, Qg, al1_1, al1_2, al1_R, Matrix.one_apply, transpose_apply]
  ring

lemma continuous_al1_R : Continuous fun p : ℝ × (Fin 10 → ℝ) => al1_R p.1 p.2 := by
  unfold al1_R; fun_prop

def ly1_1 (y : Fin 10 → ℝ) : ℝ :=
  -2 * (y 3)

def ly1_2 (y : Fin 10 → ℝ) : ℝ :=
  (y 2) ^ 2 + (y 3) ^ 2 + (y 4) ^ 2 + 2 * (y 9) ^ 2 + 2 * (y 0) * (y 3) + 8 * (y 1) * (y 8)
  + (y 2) * (y 3) + 2 * (y 2) * (y 4) + 8 * (y 2) * (y 9) + (y 3) * (y 4) - 8 * (y 4) * (y 9)

def ly1_R (t : ℝ) (y : Fin 10 → ℝ) : ℝ :=
  12 * (y 0) ^ 3 + 24 * (y 0) * (y 1) ^ 2 + 24 * (y 0) * (y 2) ^ 2 + 12 * (y 0) * (y 3) ^ 2
  + 24 * (y 0) * (y 4) ^ 2 + 12 * (y 0) * (y 5) ^ 2 - 2 * (y 0) * (y 8) ^ 2
  - 4 * (y 2) ^ 2 * (y 8) - 4 * (y 4) ^ 2 * (y 8) + t * (y 0) ^ 2 * (y 8) ^ 2
  + 48 * t * (y 1) ^ 3 * (y 8) + t * (y 2) ^ 2 * (y 8) ^ 2 + 48 * t * (y 2) ^ 3 * (y 9)
  + t * (y 4) ^ 2 * (y 8) ^ 2 + 12 * t ^ 2 * (y 3) ^ 3 * (y 8) ^ 2
  + 12 * t ^ 2 * (y 5) ^ 3 * (y 9) ^ 2 + 2 * (y 0) * (y 2) * (y 9) + (y 0) * (y 3) * (y 9)
  + 2 * (y 0) * (y 4) * (y 9) - 8 * (y 1) * (y 2) * (y 9) - 8 * (y 1) * (y 4) * (y 9)
  + 2 * (y 2) * (y 3) * (y 9) - 8 * (y 2) * (y 4) * (y 8) - 8 * (y 2) * (y 8) * (y 9)
  + 2 * (y 3) * (y 4) * (y 9) + 8 * (y 4) * (y 8) * (y 9) + t * (y 0) * (y 2) * (y 8) ^ 2
  + 2 * t * (y 0) * (y 3) * (y 8) ^ 2 + t * (y 0) * (y 4) * (y 8) ^ 2
  + 24 * t * (y 0) ^ 2 * (y 1) * (y 8) + 24 * t * (y 0) ^ 2 * (y 2) * (y 9)
  + 48 * t * (y 1) * (y 2) ^ 2 * (y 8) + 24 * t * (y 1) * (y 3) ^ 2 * (y 8)
  + 48 * t * (y 1) * (y 4) ^ 2 * (y 8) + 24 * t * (y 1) * (y 5) ^ 2 * (y 8)
  + 48 * t * (y 1) ^ 2 * (y 2) * (y 9) + 24 * t * (y 2) * (y 3) ^ 2 * (y 9)
  + 2 * t * (y 2) * (y 4) * (y 8) ^ 2 + 48 * t * (y 2) * (y 4) ^ 2 * (y 9)
  + 24 * t * (y 2) * (y 5) ^ 2 * (y 9) + 12 * t ^ 2 * (y 0) ^ 2 * (y 3) * (y 8) ^ 2
  + 12 * t ^ 2 * (y 0) ^ 2 * (y 5) * (y 9) ^ 2 + 24 * t ^ 2 * (y 1) ^ 2 * (y 3) * (y 8) ^ 2
  + 24 * t ^ 2 * (y 1) ^ 2 * (y 5) * (y 9) ^ 2 + 24 * t ^ 2 * (y 2) ^ 2 * (y 3) * (y 8) ^ 2
  + 24 * t ^ 2 * (y 2) ^ 2 * (y 5) * (y 9) ^ 2 + 24 * t ^ 2 * (y 3) * (y 4) ^ 2 * (y 8) ^ 2
  + 12 * t ^ 2 * (y 3) * (y 5) ^ 2 * (y 8) ^ 2 + 12 * t ^ 2 * (y 3) ^ 2 * (y 5) * (y 9) ^ 2
  + 24 * t ^ 2 * (y 4) ^ 2 * (y 5) * (y 9) ^ 2 + 48 * t ^ 2 * (y 4) ^ 3 * (y 8) * (y 9)
  + 2 * t * (y 0) * (y 2) * (y 8) * (y 9) + t * (y 0) * (y 3) * (y 8) * (y 9)
  + 2 * t * (y 0) * (y 4) * (y 8) * (y 9) - 8 * t * (y 1) * (y 2) * (y 8) * (y 9)
  - 8 * t * (y 1) * (y 4) * (y 8) * (y 9) + 2 * t * (y 2) * (y 3) * (y 8) * (y 9)
  + 2 * t * (y 3) * (y 4) * (y 8) * (y 9) + 24 * t ^ 2 * (y 0) ^ 2 * (y 4) * (y 8) * (y 9)
  + 48 * t ^ 2 * (y 1) ^ 2 * (y 4) * (y 8) * (y 9)
  + 48 * t ^ 2 * (y 2) ^ 2 * (y 4) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 3) ^ 2 * (y 4) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 4) * (y 5) ^ 2 * (y 8) * (y 9)

lemma ly1_jet (t : ℝ) (y : Fin 10 → ℝ) :
    Lg (symY (t • y)) (vecMulVec ![1, (t • y) 8, (t • y) 9] ![1, (t • y) 8, (t • y) 9]) =
      0 + t * ly1_1 y + t ^ 2 * ly1_2 y + t ^ 3 * ly1_R t y := by
  simp [symY, Pi.smul_apply, smul_eq_mul, det_fin_three, cof, adjugate_fin_three, dotProduct, mulVec, Fin.sum_univ_three, vecMulVec_apply, Lg, Qg, ly1_1, ly1_2, ly1_R]
  ring

lemma continuous_ly1_R : Continuous fun p : ℝ × (Fin 10 → ℝ) => ly1_R p.1 p.2 := by
  unfold ly1_R; fun_prop

def qx1_1 (y : Fin 10 → ℝ) : ℝ :=
  (y 3)

def qx1_2 (y : Fin 10 → ℝ) : ℝ :=
  18 * (y 0) ^ 2 + 12 * (y 1) ^ 2 + 12 * (y 2) ^ 2 + 6 * (y 3) ^ 2 + 12 * (y 4) ^ 2
  + 6 * (y 5) ^ 2 + (y 6) ^ 2 + (y 7) ^ 2 + (y 8) ^ 2 + (y 9) ^ 2 + (y 2) * (y 7) + (y 2) * (y 9)
  + (y 3) * (y 7) / 2 + (y 3) * (y 9) / 2 + (y 4) * (y 7) + (y 4) * (y 9) + 2 * (y 7) * (y 9)

def qx1_R (t : ℝ) (y : Fin 10 → ℝ) : ℝ :=
  (y 0) * (y 7) ^ 2 / 4 + (y 0) * (y 9) ^ 2 / 4 - (y 1) * (y 7) ^ 2 - (y 1) * (y 9) ^ 2
  + (y 3) * (y 7) ^ 2 / 4 + (y 3) * (y 9) ^ 2 / 4 - 2 * (y 6) * (y 9) ^ 2 - 2 * (y 7) ^ 2 * (y 8)
  + 3 * t * (y 0) ^ 2 * (y 6) ^ 2 + 3 * t * (y 0) ^ 2 * (y 7) ^ 2 + 3 * t * (y 0) ^ 2 * (y 8) ^ 2
  + 3 * t * (y 0) ^ 2 * (y 9) ^ 2 + 18 * t * (y 1) ^ 2 * (y 6) ^ 2 + 6 * t * (y 1) ^ 2 * (y 7) ^ 2
  + 18 * t * (y 1) ^ 2 * (y 8) ^ 2 + 6 * t * (y 1) ^ 2 * (y 9) ^ 2 + 6 * t * (y 2) ^ 2 * (y 6) ^ 2
  + 18 * t * (y 2) ^ 2 * (y 7) ^ 2 + 6 * t * (y 2) ^ 2 * (y 8) ^ 2
  + 18 * t * (y 2) ^ 2 * (y 9) ^ 2 + 3 * t * (y 3) ^ 2 * (y 6) ^ 2 + 3 * t * (y 3) ^ 2 * (y 7) ^ 2
  + 3 * t * (y 3) ^ 2 * (y 8) ^ 2 + 3 * t * (y 3) ^ 2 * (y 9) ^ 2 + 6 * t * (y 4) ^ 2 * (y 6) ^ 2
  + 6 * t * (y 4) ^ 2 * (y 7) ^ 2 + 6 * t * (y 4) ^ 2 * (y 8) ^ 2 + 6 * t * (y 4) ^ 2 * (y 9) ^ 2
  + 3 * t * (y 5) ^ 2 * (y 6) ^ 2 + 3 * t * (y 5) ^ 2 * (y 7) ^ 2 + 3 * t * (y 5) ^ 2 * (y 8) ^ 2
  + 3 * t * (y 5) ^ 2 * (y 9) ^ 2 + t * (y 6) ^ 2 * (y 9) ^ 2 + t * (y 7) ^ 2 * (y 8) ^ 2
  + 24 * (y 0) * (y 1) * (y 6) + 24 * (y 0) * (y 1) * (y 8) + 24 * (y 0) * (y 2) * (y 7)
  + 24 * (y 0) * (y 2) * (y 9) + 2 * (y 0) * (y 6) * (y 8) + (y 0) * (y 7) * (y 9) / 2
  - 2 * (y 1) * (y 7) * (y 9) - 2 * (y 2) * (y 6) * (y 7) + (y 2) * (y 6) * (y 8)
  - (y 2) * (y 6) * (y 9) - (y 2) * (y 7) * (y 8) - 2 * (y 2) * (y 8) * (y 9)
  + 2 * (y 3) * (y 6) * (y 8) + (y 3) * (y 6) * (y 9) / 2 + (y 3) * (y 7) * (y 8) / 2
  + (y 3) * (y 7) * (y 9) / 2 - 2 * (y 4) * (y 6) * (y 7) + (y 4) * (y 6) * (y 8)
  - (y 4) * (y 6) * (y 9) - (y 4) * (y 7) * (y 8) - 2 * (y 4) * (y 8) * (y 9)
  - 2 * (y 6) * (y 7) * (y 9) - 2 * (y 7) * (y 8) * (y 9) + t * (y 0) * (y 6) * (y 9) ^ 2 / 2
  + t * (y 0) * (y 7) ^ 2 * (y 8) / 2 + 6 * t * (y 0) ^ 2 * (y 6) * (y 8)
  + 6 * t * (y 0) ^ 2 * (y 7) * (y 9) - 2 * t * (y 1) * (y 6) * (y 9) ^ 2
  - 2 * t * (y 1) * (y 7) ^ 2 * (y 8) + 36 * t * (y 1) ^ 2 * (y 6) * (y 8)
  + 12 * t * (y 1) ^ 2 * (y 7) * (y 9) - 2 * t * (y 2) * (y 6) ^ 2 * (y 9)
  - 2 * t * (y 2) * (y 7) * (y 8) ^ 2 + 12 * t * (y 2) ^ 2 * (y 6) * (y 8)
  + 36 * t * (y 2) ^ 2 * (y 7) * (y 9) + t * (y 3) * (y 6) * (y 9) ^ 2 / 2
  + t * (y 3) * (y 7) ^ 2 * (y 8) / 2 + 6 * t * (y 3) ^ 2 * (y 6) * (y 8)
  + 6 * t * (y 3) ^ 2 * (y 7) * (y 9) - 2 * t * (y 4) * (y 6) ^ 2 * (y 9)
  - 2 * t * (y 4) * (y 7) * (y 8) ^ 2 + 12 * t * (y 4) ^ 2 * (y 6) * (y 8)
  + 12 * t * (y 4) ^ 2 * (y 7) * (y 9) + 6 * t * (y 5) ^ 2 * (y 6) * (y 8)
  + 6 * t * (y 5) ^ 2 * (y 7) * (y 9) + t ^ 2 * (y 0) * (y 6) ^ 2 * (y 8) ^ 2
  + t ^ 2 * (y 0) * (y 6) ^ 2 * (y 9) ^ 2 / 4 + t ^ 2 * (y 0) * (y 7) ^ 2 * (y 8) ^ 2 / 4
  - t ^ 2 * (y 1) * (y 6) ^ 2 * (y 9) ^ 2 - t ^ 2 * (y 1) * (y 7) ^ 2 * (y 8) ^ 2
  + t ^ 2 * (y 3) * (y 6) ^ 2 * (y 9) ^ 2 / 4 + t ^ 2 * (y 3) * (y 7) ^ 2 * (y 8) ^ 2 / 4
  + 6 * t ^ 3 * (y 0) ^ 2 * (y 6) ^ 2 * (y 8) ^ 2 + 3 * t ^ 3 * (y 0) ^ 2 * (y 6) ^ 2 * (y 9) ^ 2
  + 3 * t ^ 3 * (y 0) ^ 2 * (y 7) ^ 2 * (y 8) ^ 2 + 6 * t ^ 3 * (y 0) ^ 2 * (y 7) ^ 2 * (y 9) ^ 2
  + 12 * t ^ 3 * (y 1) ^ 2 * (y 6) ^ 2 * (y 8) ^ 2 + 6 * t ^ 3 * (y 1) ^ 2 * (y 6) ^ 2 * (y 9) ^ 2
  + 6 * t ^ 3 * (y 1) ^ 2 * (y 7) ^ 2 * (y 8) ^ 2 + 12 * t ^ 3 * (y 1) ^ 2 * (y 7) ^ 2 * (y 9) ^ 2
  + 12 * t ^ 3 * (y 2) ^ 2 * (y 6) ^ 2 * (y 8) ^ 2 + 6 * t ^ 3 * (y 2) ^ 2 * (y 6) ^ 2 * (y 9) ^ 2
  + 6 * t ^ 3 * (y 2) ^ 2 * (y 7) ^ 2 * (y 8) ^ 2 + 12 * t ^ 3 * (y 2) ^ 2 * (y 7) ^ 2 * (y 9) ^ 2
  + 18 * t ^ 3 * (y 3) ^ 2 * (y 6) ^ 2 * (y 8) ^ 2 + 3 * t ^ 3 * (y 3) ^ 2 * (y 6) ^ 2 * (y 9) ^ 2
  + 3 * t ^ 3 * (y 3) ^ 2 * (y 7) ^ 2 * (y 8) ^ 2 + 6 * t ^ 3 * (y 3) ^ 2 * (y 7) ^ 2 * (y 9) ^ 2
  + 12 * t ^ 3 * (y 4) ^ 2 * (y 6) ^ 2 * (y 8) ^ 2
  + 18 * t ^ 3 * (y 4) ^ 2 * (y 6) ^ 2 * (y 9) ^ 2
  + 18 * t ^ 3 * (y 4) ^ 2 * (y 7) ^ 2 * (y 8) ^ 2
  + 12 * t ^ 3 * (y 4) ^ 2 * (y 7) ^ 2 * (y 9) ^ 2 + 6 * t ^ 3 * (y 5) ^ 2 * (y 6) ^ 2 * (y 8) ^ 2
  + 3 * t ^ 3 * (y 5) ^ 2 * (y 6) ^ 2 * (y 9) ^ 2 + 3 * t ^ 3 * (y 5) ^ 2 * (y 7) ^ 2 * (y 8) ^ 2
  + 18 * t ^ 3 * (y 5) ^ 2 * (y 7) ^ 2 * (y 9) ^ 2 + 24 * t * (y 0) * (y 3) * (y 6) * (y 8)
  + 24 * t * (y 0) * (y 4) * (y 6) * (y 9) + 24 * t * (y 0) * (y 4) * (y 7) * (y 8)
  + 24 * t * (y 0) * (y 5) * (y 7) * (y 9) + t * (y 0) * (y 6) * (y 7) * (y 8) / 2
  + t * (y 0) * (y 6) * (y 7) * (y 9) / 2 + t * (y 0) * (y 6) * (y 8) * (y 9) / 2
  + t * (y 0) * (y 7) * (y 8) * (y 9) / 2 + 24 * t * (y 1) * (y 2) * (y 6) * (y 7)
  + 24 * t * (y 1) * (y 2) * (y 6) * (y 9) + 24 * t * (y 1) * (y 2) * (y 7) * (y 8)
  + 24 * t * (y 1) * (y 2) * (y 8) * (y 9) - 2 * t * (y 1) * (y 6) * (y 7) * (y 9)
  - 2 * t * (y 1) * (y 7) * (y 8) * (y 9) - t * (y 2) * (y 6) * (y 7) * (y 8)
  - t * (y 2) * (y 6) * (y 8) * (y 9) + t * (y 3) * (y 6) * (y 7) * (y 9) / 2
  + t * (y 3) * (y 7) * (y 8) * (y 9) / 2 - t * (y 4) * (y 6) * (y 7) * (y 8)
  - t * (y 4) * (y 6) * (y 8) * (y 9) + 2 * t * (y 6) * (y 7) * (y 8) * (y 9)
  + t ^ 2 * (y 0) * (y 6) * (y 7) * (y 8) ^ 2 / 2 + t ^ 2 * (y 0) * (y 6) ^ 2 * (y 8) * (y 9) / 2
  + 24 * t ^ 2 * (y 1) * (y 3) * (y 6) * (y 8) ^ 2
  + 24 * t ^ 2 * (y 1) * (y 3) * (y 6) ^ 2 * (y 8)
  + 24 * t ^ 2 * (y 1) * (y 4) * (y 6) ^ 2 * (y 9)
  + 24 * t ^ 2 * (y 1) * (y 4) * (y 7) * (y 8) ^ 2
  + 24 * t ^ 2 * (y 2) * (y 4) * (y 6) * (y 9) ^ 2
  + 24 * t ^ 2 * (y 2) * (y 4) * (y 7) ^ 2 * (y 8)
  + 24 * t ^ 2 * (y 2) * (y 5) * (y 7) * (y 9) ^ 2
  + 24 * t ^ 2 * (y 2) * (y 5) * (y 7) ^ 2 * (y 9) + t ^ 2 * (y 2) * (y 6) * (y 7) * (y 8) ^ 2
  + t ^ 2 * (y 2) * (y 6) ^ 2 * (y 8) * (y 9) + t ^ 2 * (y 4) * (y 6) * (y 7) * (y 8) ^ 2
  + t ^ 2 * (y 4) * (y 6) ^ 2 * (y 8) * (y 9) + t ^ 2 * (y 0) * (y 6) * (y 7) * (y 8) * (y 9) / 2
  + 24 * t ^ 2 * (y 1) * (y 4) * (y 6) * (y 7) * (y 8)
  + 24 * t ^ 2 * (y 1) * (y 4) * (y 6) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 1) * (y 5) * (y 6) * (y 7) * (y 9)
  + 24 * t ^ 2 * (y 1) * (y 5) * (y 7) * (y 8) * (y 9)
  - 2 * t ^ 2 * (y 1) * (y 6) * (y 7) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 2) * (y 3) * (y 6) * (y 7) * (y 8)
  + 24 * t ^ 2 * (y 2) * (y 3) * (y 6) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 2) * (y 4) * (y 6) * (y 7) * (y 9)
  + 24 * t ^ 2 * (y 2) * (y 4) * (y 7) * (y 8) * (y 9)
  + t ^ 2 * (y 3) * (y 6) * (y 7) * (y 8) * (y 9) / 2
  + 6 * t ^ 3 * (y 0) ^ 2 * (y 6) * (y 7) * (y 8) * (y 9)
  + 12 * t ^ 3 * (y 1) ^ 2 * (y 6) * (y 7) * (y 8) * (y 9)
  + 12 * t ^ 3 * (y 2) ^ 2 * (y 6) * (y 7) * (y 8) * (y 9)
  + 24 * t ^ 3 * (y 3) * (y 4) * (y 6) * (y 7) * (y 8) ^ 2
  + 24 * t ^ 3 * (y 3) * (y 4) * (y 6) ^ 2 * (y 8) * (y 9)
  + 6 * t ^ 3 * (y 3) ^ 2 * (y 6) * (y 7) * (y 8) * (y 9)
  + 24 * t ^ 3 * (y 4) * (y 5) * (y 6) * (y 7) * (y 9) ^ 2
  + 24 * t ^ 3 * (y 4) * (y 5) * (y 7) ^ 2 * (y 8) * (y 9)
  + 36 * t ^ 3 * (y 4) ^ 2 * (y 6) * (y 7) * (y 8) * (y 9)
  + 6 * t ^ 3 * (y 5) ^ 2 * (y 6) * (y 7) * (y 8) * (y 9)
  + 24 * t ^ 3 * (y 3) * (y 5) * (y 6) * (y 7) * (y 8) * (y 9)

lemma qx1_jet (t : ℝ) (y : Fin 10 → ℝ) :
    Qg (symY (t • y)) (symPart (vecMulVec ![1, (t • y) 6, (t • y) 7] ![1, (t • y) 8, (t • y) 9])) =
      0 + t * qx1_1 y + t ^ 2 * qx1_2 y + t ^ 3 * qx1_R t y := by
  simp [symY, Pi.smul_apply, smul_eq_mul, det_fin_three, cof, adjugate_fin_three, dotProduct, mulVec, Fin.sum_univ_three, vecMulVec_apply, Lg, Qg, qx1_1, qx1_2, qx1_R, symPart, Matrix.add_apply, Matrix.smul_apply, transpose_apply]
  ring

lemma continuous_qx1_R : Continuous fun p : ℝ × (Fin 10 → ℝ) => qx1_R p.1 p.2 := by
  unfold qx1_R; fun_prop

/-- The quadratic part `yᵀ A_1 y` of `P1`. -/
def Q1 (y : Fin 10 → ℝ) : ℝ :=
  2 * ((1) * qx1_2 y + Dd_1 y * qx1_1 y + Dd_2 y * (0))
    + ((1) * ly1_2 y + al1_1 y * ly1_1 y + al1_2 y * (0))

/-- The cubic remainder of `P1`. -/
def R1 (t : ℝ) (y : Fin 10 → ℝ) : ℝ :=
  2 * jetRem (1) (Dd_1 y) (Dd_2 y) (Dd_R t y) (0) (qx1_1 y) (qx1_2 y) (qx1_R t y) t
    + jetRem (1) (al1_1 y) (al1_2 y) (al1_R t y) (0) (ly1_1 y) (ly1_2 y)
      (ly1_R t y) t

lemma P1_expand (t : ℝ) (y : Fin 10 → ℝ) :
    P1 (t • y) = t ^ 2 * Q1 y + t ^ 3 * R1 t y := by
  have h0 : 2 * ((1) * (0)) + (1) * (0) = (0 : ℝ) := by norm_num
  have h1 : 2 * ((1) * qx1_1 y + Dd_1 y * (0)) + ((1) * ly1_1 y + al1_1 y * (0)) = 0 := by
    simp only [qx1_1, Dd_1, ly1_1, al1_1]; ring
  have e : P1 (t • y) = 2 * (det (1 + (2 : ℝ) • symY (t • y)) * Qg (symY (t • y)) (symPart (vecMulVec ![1, (t • y) 6, (t • y) 7] ![1, (t • y) 8, (t • y) 9])))
      + (![1, (t • y) 6, (t • y) 7] ⬝ᵥ (cof (1 + (2 : ℝ) • symY (t • y)) *ᵥ ![1, (t • y) 6, (t • y) 7])) * Lg (symY (t • y)) (vecMulVec ![1, (t • y) 8, (t • y) 9] ![1, (t • y) 8, (t • y) 9]) := by
    simp only [P1, Pc]; ring
  rw [e, Dd_jet, qx1_jet, al1_jet, ly1_jet, jet_mul, jet_mul, Q1, R1]
  linear_combination h0 + t * h1

/-- Positive definiteness of `A_1 - ¼ Id`: an LDLᵀ certificate. -/
lemma Q1_cert (y : Fin 10 → ℝ) :
    Q1 y - 1/4 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 + y 4 ^ 2 + y 5 ^ 2 + y 6 ^ 2 + y 7 ^ 2 + y 8 ^ 2 + y 9 ^ 2) =
      143 / 4 * ((y 0) + 12 * (y 3) / 143) ^ 2
      + 95 / 4 * ((y 1) + 16 * (y 8) / 95) ^ 2
      + 99 / 4 * ((y 2) + 2 * (y 3) / 99 + 4 * (y 4) / 99 + 4 * (y 7) / 99 + 20 * (y 9) / 99) ^ 2
      + 64289 / 5148 * ((y 3) + 2470 * (y 4) / 64289 + 2470 * (y 7) / 64289 + 2054 * (y 9) / 64289) ^ 2
      + 69844285 / 2828716 * ((y 4) + 28024 * (y 7) / 735203 - 9100968 * (y 9) / 69844285) ^ 2
      + 47 / 4 * ((y 5)) ^ 2
      + 7 / 4 * ((y 6)) ^ 2
      + 4867889 / 2940812 * ((y 7) + 5603092 * (y 9) / 4867889) ^ 2
      + 409 / 380 * ((y 8)) ^ 2
      + 212493277 / 1849797820 * ((y 9)) ^ 2 := by
  simp only [Q1, qx1_2, qx1_1, Dd_1, Dd_2, ly1_2, ly1_1, al1_1, al1_2]
  ring

lemma P1_eventually_nonneg : ∀ᶠ y in 𝓝 0, 0 ≤ P1 y := by
  refine eventually_nonneg_of_expansion (P1) (Q1) (R1) ?_ (m := 1/4) (by norm_num)
    (fun y => ?_) P1_expand
  · unfold R1 jetRem
    have := continuous_Dd_R; have := continuous_qx1_R; have := continuous_al1_R
    have := continuous_ly1_R
    unfold Dd_1 Dd_2 qx1_1 qx1_2 al1_1 al1_2 ly1_1 ly1_2
    fun_prop
  · have h := Q1_cert y
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    have : 0 ≤ Q1 y - 1/4 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 + y 4 ^ 2 + y 5 ^ 2 + y 6 ^ 2 + y 7 ^ 2 + y 8 ^ 2 + y 9 ^ 2) := by rw [h]; positivity
    norm_num at this ⊢
    linarith

/-! ### Mode 3: `c⁽3⁾(y) = ![y 6, y 7, 1]`, `b⁽3⁾(y) = ![1, 1 + y 8, y 9]` -/

/-- The reduced second variation `P_3` in the chart of mode 3. -/
def P3 (y : Fin 10 → ℝ) : ℝ := Pc (symY y) ![y 6, y 7, 1] ![1, 1 + y 8, y 9]

def al3_1 (y : Fin 10 → ℝ) : ℝ :=
  2 * (y 0) + 2 * (y 3)

def al3_2 (y : Fin 10 → ℝ) : ℝ :=
  -4 * (y 1) ^ 2 + (y 6) ^ 2 + (y 7) ^ 2 + 4 * (y 0) * (y 3) - 4 * (y 2) * (y 6)
  - 4 * (y 4) * (y 7)

def al3_R (t : ℝ) (y : Fin 10 → ℝ) : ℝ :=
  2 * (y 0) * (y 7) ^ 2 + 2 * (y 3) * (y 6) ^ 2 + 2 * (y 5) * (y 6) ^ 2 + 2 * (y 5) * (y 7) ^ 2
  - 4 * t * (y 2) ^ 2 * (y 7) ^ 2 - 4 * t * (y 4) ^ 2 * (y 6) ^ 2 - 8 * (y 0) * (y 4) * (y 7)
  + 8 * (y 1) * (y 2) * (y 7) + 8 * (y 1) * (y 4) * (y 6) - 4 * (y 1) * (y 6) * (y 7)
  - 8 * (y 2) * (y 3) * (y 6) + 4 * t * (y 0) * (y 5) * (y 7) ^ 2
  + 4 * t * (y 3) * (y 5) * (y 6) ^ 2 - 8 * t * (y 1) * (y 5) * (y 6) * (y 7)
  + 8 * t * (y 2) * (y 4) * (y 6) * (y 7)

lemma al3_jet (t : ℝ) (y : Fin 10 → ℝ) :
    ![(t • y) 6, (t • y) 7, 1] ⬝ᵥ (cof (1 + (2 : ℝ) • symY (t • y)) *ᵥ ![(t • y) 6, (t • y) 7, 1]) =
      1 + t * al3_1 y + t ^ 2 * al3_2 y + t ^ 3 * al3_R t y := by
  simp [symY, Pi.smul_apply, smul_eq_mul, det_fin_three, cof, adjugate_fin_three, dotProduct, mulVec, Fin.sum_univ_three, vecMulVec_apply, Lg, Qg, al3_1, al3_2, al3_R, Matrix.one_apply, transpose_apply]
  ring

lemma continuous_al3_R : Continuous fun p : ℝ × (Fin 10 → ℝ) => al3_R p.1 p.2 := by
  unfold al3_R; fun_prop

def ly3_1 (y : Fin 10 → ℝ) : ℝ :=
  -2 * (y 0) + 8 * (y 1) - 2 * (y 3)

def ly3_2 (y : Fin 10 → ℝ) : ℝ :=
  (y 0) ^ 2 - 2 * (y 2) ^ 2 + (y 3) ^ 2 - 2 * (y 4) ^ 2 + 2 * (y 9) ^ 2 + (y 0) * (y 2)
  + 4 * (y 0) * (y 3) + (y 0) * (y 4) - 4 * (y 0) * (y 8) + 8 * (y 1) * (y 8) + (y 2) * (y 3)
  - 4 * (y 2) * (y 4) + (y 3) * (y 4)

def ly3_R (t : ℝ) (y : Fin 10 → ℝ) : ℝ :=
  12 * (y 0) ^ 3 + 48 * (y 1) ^ 3 + 12 * (y 3) ^ 3 + 24 * (y 0) * (y 1) ^ 2
  + 24 * (y 0) * (y 2) ^ 2 + 12 * (y 0) * (y 3) ^ 2 + 24 * (y 0) * (y 4) ^ 2
  + 12 * (y 0) * (y 5) ^ 2 - 2 * (y 0) * (y 8) ^ 2 + 24 * (y 0) ^ 2 * (y 1)
  + 12 * (y 0) ^ 2 * (y 3) + 2 * (y 0) ^ 2 * (y 8) + 48 * (y 1) * (y 2) ^ 2
  + 24 * (y 1) * (y 3) ^ 2 + 48 * (y 1) * (y 4) ^ 2 + 24 * (y 1) * (y 5) ^ 2
  + 24 * (y 1) ^ 2 * (y 3) + 24 * (y 2) ^ 2 * (y 3) - 2 * (y 2) ^ 2 * (y 8)
  + 24 * (y 3) * (y 4) ^ 2 + 12 * (y 3) * (y 5) ^ 2 - 2 * (y 4) ^ 2 * (y 8)
  + t * (y 0) ^ 2 * (y 8) ^ 2 + 48 * t * (y 1) ^ 3 * (y 8) + t * (y 2) ^ 2 * (y 8) ^ 2
  + 48 * t * (y 2) ^ 3 * (y 9) + 24 * t * (y 3) ^ 3 * (y 8) + t * (y 4) ^ 2 * (y 8) ^ 2
  + 48 * t * (y 4) ^ 3 * (y 9) + 12 * t ^ 2 * (y 3) ^ 3 * (y 8) ^ 2
  + 12 * t ^ 2 * (y 5) ^ 3 * (y 9) ^ 2 + 2 * (y 0) * (y 2) * (y 8) + 4 * (y 0) * (y 2) * (y 9)
  + 4 * (y 0) * (y 3) * (y 8) + 2 * (y 0) * (y 3) * (y 9) + 2 * (y 0) * (y 4) * (y 8)
  + 4 * (y 0) * (y 4) * (y 9) - 16 * (y 1) * (y 2) * (y 9) - 16 * (y 1) * (y 4) * (y 9)
  + 4 * (y 2) * (y 3) * (y 9) - 4 * (y 2) * (y 4) * (y 8) - 8 * (y 2) * (y 8) * (y 9)
  + 4 * (y 3) * (y 4) * (y 9) + 8 * (y 4) * (y 8) * (y 9) + t * (y 0) * (y 2) * (y 8) ^ 2
  + 2 * t * (y 0) * (y 3) * (y 8) ^ 2 + t * (y 0) * (y 4) * (y 8) ^ 2
  + 24 * t * (y 0) ^ 2 * (y 1) * (y 8) + 24 * t * (y 0) ^ 2 * (y 2) * (y 9)
  + 24 * t * (y 0) ^ 2 * (y 3) * (y 8) + 24 * t * (y 0) ^ 2 * (y 4) * (y 9)
  + 48 * t * (y 1) * (y 2) ^ 2 * (y 8) + 24 * t * (y 1) * (y 3) ^ 2 * (y 8)
  + 48 * t * (y 1) * (y 4) ^ 2 * (y 8) + 24 * t * (y 1) * (y 5) ^ 2 * (y 8)
  + 48 * t * (y 1) ^ 2 * (y 2) * (y 9) + 48 * t * (y 1) ^ 2 * (y 3) * (y 8)
  + 48 * t * (y 1) ^ 2 * (y 4) * (y 9) + 24 * t * (y 2) * (y 3) ^ 2 * (y 9)
  + 2 * t * (y 2) * (y 4) * (y 8) ^ 2 + 48 * t * (y 2) * (y 4) ^ 2 * (y 9)
  + 24 * t * (y 2) * (y 5) ^ 2 * (y 9) + 48 * t * (y 2) ^ 2 * (y 3) * (y 8)
  + 48 * t * (y 2) ^ 2 * (y 4) * (y 9) + 48 * t * (y 3) * (y 4) ^ 2 * (y 8)
  + 24 * t * (y 3) * (y 5) ^ 2 * (y 8) + 24 * t * (y 3) ^ 2 * (y 4) * (y 9)
  + 24 * t * (y 4) * (y 5) ^ 2 * (y 9) + 12 * t ^ 2 * (y 0) ^ 2 * (y 3) * (y 8) ^ 2
  + 12 * t ^ 2 * (y 0) ^ 2 * (y 5) * (y 9) ^ 2 + 24 * t ^ 2 * (y 1) ^ 2 * (y 3) * (y 8) ^ 2
  + 24 * t ^ 2 * (y 1) ^ 2 * (y 5) * (y 9) ^ 2 + 24 * t ^ 2 * (y 2) ^ 2 * (y 3) * (y 8) ^ 2
  + 24 * t ^ 2 * (y 2) ^ 2 * (y 5) * (y 9) ^ 2 + 24 * t ^ 2 * (y 3) * (y 4) ^ 2 * (y 8) ^ 2
  + 12 * t ^ 2 * (y 3) * (y 5) ^ 2 * (y 8) ^ 2 + 12 * t ^ 2 * (y 3) ^ 2 * (y 5) * (y 9) ^ 2
  + 24 * t ^ 2 * (y 4) ^ 2 * (y 5) * (y 9) ^ 2 + 48 * t ^ 2 * (y 4) ^ 3 * (y 8) * (y 9)
  + 2 * t * (y 0) * (y 2) * (y 8) * (y 9) + t * (y 0) * (y 3) * (y 8) * (y 9)
  + 2 * t * (y 0) * (y 4) * (y 8) * (y 9) - 8 * t * (y 1) * (y 2) * (y 8) * (y 9)
  - 8 * t * (y 1) * (y 4) * (y 8) * (y 9) + 2 * t * (y 2) * (y 3) * (y 8) * (y 9)
  + 2 * t * (y 3) * (y 4) * (y 8) * (y 9) + 24 * t ^ 2 * (y 0) ^ 2 * (y 4) * (y 8) * (y 9)
  + 48 * t ^ 2 * (y 1) ^ 2 * (y 4) * (y 8) * (y 9)
  + 48 * t ^ 2 * (y 2) ^ 2 * (y 4) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 3) ^ 2 * (y 4) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 4) * (y 5) ^ 2 * (y 8) * (y 9)

lemma ly3_jet (t : ℝ) (y : Fin 10 → ℝ) :
    Lg (symY (t • y)) (vecMulVec ![1, 1 + (t • y) 8, (t • y) 9] ![1, 1 + (t • y) 8, (t • y) 9]) =
      0 + t * ly3_1 y + t ^ 2 * ly3_2 y + t ^ 3 * ly3_R t y := by
  simp [symY, Pi.smul_apply, smul_eq_mul, det_fin_three, cof, adjugate_fin_three, dotProduct, mulVec, Fin.sum_univ_three, vecMulVec_apply, Lg, Qg, ly3_1, ly3_2, ly3_R]
  ring

lemma continuous_ly3_R : Continuous fun p : ℝ × (Fin 10 → ℝ) => ly3_R p.1 p.2 := by
  unfold ly3_R; fun_prop

def qx3_1 (y : Fin 10 → ℝ) : ℝ :=
  (y 0) - 4 * (y 1) + (y 3)

def qx3_2 (y : Fin 10 → ℝ) : ℝ :=
  6 * (y 0) ^ 2 + 12 * (y 1) ^ 2 + 24 * (y 2) ^ 2 + 6 * (y 3) ^ 2 + 24 * (y 4) ^ 2 + 6 * (y 5) ^ 2
  + (y 6) ^ 2 + (y 7) ^ 2 + (y 8) ^ 2 + (y 0) * (y 7) + (y 0) * (y 8) - 4 * (y 1) * (y 8)
  + 24 * (y 2) * (y 4) - 2 * (y 2) * (y 6) - 2 * (y 2) * (y 7) + (y 3) * (y 6) + (y 3) * (y 8)
  - 2 * (y 4) * (y 6) - 2 * (y 4) * (y 7)

def qx3_R (t : ℝ) (y : Fin 10 → ℝ) : ℝ :=
  (y 0) * (y 7) ^ 2 + (y 0) * (y 8) ^ 2 / 4 + 6 * (y 0) ^ 2 * (y 8) - (y 1) * (y 8) ^ 2
  + 12 * (y 1) ^ 2 * (y 8) + 12 * (y 2) ^ 2 * (y 8) + (y 3) * (y 6) ^ 2 + (y 3) * (y 8) ^ 2 / 4
  + 6 * (y 3) ^ 2 * (y 8) + 36 * (y 4) ^ 2 * (y 8) + 6 * (y 5) ^ 2 * (y 8) + 2 * (y 6) ^ 2 * (y 8)
  + 21 * t * (y 0) ^ 2 * (y 6) ^ 2 + 9 * t * (y 0) ^ 2 * (y 7) ^ 2 + 3 * t * (y 0) ^ 2 * (y 8) ^ 2
  + 6 * t * (y 0) ^ 2 * (y 9) ^ 2 + 30 * t * (y 1) ^ 2 * (y 6) ^ 2
  + 30 * t * (y 1) ^ 2 * (y 7) ^ 2 + 6 * t * (y 1) ^ 2 * (y 8) ^ 2
  + 12 * t * (y 1) ^ 2 * (y 9) ^ 2 + 18 * t * (y 2) ^ 2 * (y 6) ^ 2
  + 18 * t * (y 2) ^ 2 * (y 7) ^ 2 + 6 * t * (y 2) ^ 2 * (y 8) ^ 2
  + 12 * t * (y 2) ^ 2 * (y 9) ^ 2 + 9 * t * (y 3) ^ 2 * (y 6) ^ 2
  + 21 * t * (y 3) ^ 2 * (y 7) ^ 2 + 3 * t * (y 3) ^ 2 * (y 8) ^ 2 + 6 * t * (y 3) ^ 2 * (y 9) ^ 2
  + 18 * t * (y 4) ^ 2 * (y 6) ^ 2 + 18 * t * (y 4) ^ 2 * (y 7) ^ 2
  + 18 * t * (y 4) ^ 2 * (y 8) ^ 2 + 12 * t * (y 4) ^ 2 * (y 9) ^ 2
  + 9 * t * (y 5) ^ 2 * (y 6) ^ 2 + 9 * t * (y 5) ^ 2 * (y 7) ^ 2 + 3 * t * (y 5) ^ 2 * (y 8) ^ 2
  + 18 * t * (y 5) ^ 2 * (y 9) ^ 2 + t * (y 6) ^ 2 * (y 8) ^ 2 + t * (y 6) ^ 2 * (y 9) ^ 2
  + t * (y 7) ^ 2 * (y 9) ^ 2 + 24 * (y 0) * (y 2) * (y 6) + 24 * (y 0) * (y 4) * (y 6)
  + 2 * (y 0) * (y 6) * (y 7) + (y 0) * (y 6) * (y 9) + 3 * (y 0) * (y 7) * (y 8) / 2
  + (y 0) * (y 7) * (y 9) + 24 * (y 1) * (y 2) * (y 6) + 24 * (y 1) * (y 2) * (y 7)
  + 24 * (y 1) * (y 4) * (y 6) + 24 * (y 1) * (y 4) * (y 7) - 4 * (y 1) * (y 6) * (y 9)
  - 4 * (y 1) * (y 7) * (y 9) + 24 * (y 2) * (y 3) * (y 7) + 24 * (y 2) * (y 4) * (y 8)
  + 24 * (y 2) * (y 5) * (y 9) + (y 2) * (y 6) * (y 7) - 5 * (y 2) * (y 6) * (y 8)
  + (y 2) * (y 7) * (y 8) + 24 * (y 3) * (y 4) * (y 7) + 2 * (y 3) * (y 6) * (y 7)
  + (y 3) * (y 6) * (y 8) / 2 + (y 3) * (y 6) * (y 9) + (y 3) * (y 7) * (y 9)
  + 24 * (y 4) * (y 5) * (y 9) + (y 4) * (y 6) * (y 7) - 5 * (y 4) * (y 6) * (y 8)
  + (y 4) * (y 7) * (y 8) - 2 * (y 6) * (y 8) * (y 9) + 2 * (y 7) * (y 8) * (y 9)
  + 24 * t * (y 0) * (y 1) * (y 6) ^ 2 + t * (y 0) * (y 7) * (y 8) ^ 2 / 2
  + 2 * t * (y 0) * (y 7) ^ 2 * (y 8) + t * (y 0) * (y 7) ^ 2 * (y 9) / 2
  + 6 * t * (y 0) ^ 2 * (y 6) * (y 7) + 6 * t * (y 0) ^ 2 * (y 6) * (y 9)
  + 6 * t * (y 0) ^ 2 * (y 7) * (y 9) + 24 * t * (y 1) * (y 3) * (y 7) ^ 2
  + 36 * t * (y 1) ^ 2 * (y 6) * (y 7) + 12 * t * (y 1) ^ 2 * (y 6) * (y 9)
  + 12 * t * (y 1) ^ 2 * (y 7) * (y 9) - 2 * t * (y 2) * (y 6) * (y 8) ^ 2
  - t * (y 2) * (y 6) ^ 2 * (y 9) + t * (y 2) * (y 7) * (y 8) ^ 2 - t * (y 2) * (y 7) ^ 2 * (y 9)
  + 12 * t * (y 2) ^ 2 * (y 6) * (y 7) + 36 * t * (y 2) ^ 2 * (y 6) * (y 9)
  + 12 * t * (y 2) ^ 2 * (y 7) * (y 9) + t * (y 3) * (y 6) ^ 2 * (y 9) / 2
  + 6 * t * (y 3) ^ 2 * (y 6) * (y 7) + 6 * t * (y 3) ^ 2 * (y 6) * (y 9)
  + 6 * t * (y 3) ^ 2 * (y 7) * (y 9) - 2 * t * (y 4) * (y 6) * (y 8) ^ 2
  - t * (y 4) * (y 6) ^ 2 * (y 9) + t * (y 4) * (y 7) * (y 8) ^ 2 - t * (y 4) * (y 7) ^ 2 * (y 9)
  + 12 * t * (y 4) ^ 2 * (y 6) * (y 7) + 12 * t * (y 4) ^ 2 * (y 6) * (y 9)
  + 36 * t * (y 4) ^ 2 * (y 7) * (y 9) + 6 * t * (y 5) ^ 2 * (y 6) * (y 7)
  + 6 * t * (y 5) ^ 2 * (y 6) * (y 9) + 6 * t * (y 5) ^ 2 * (y 7) * (y 9)
  - 2 * t * (y 6) * (y 7) * (y 9) ^ 2 + t ^ 2 * (y 0) * (y 6) ^ 2 * (y 9) ^ 2 / 4
  + t ^ 2 * (y 0) * (y 7) ^ 2 * (y 8) ^ 2 + t ^ 2 * (y 0) * (y 7) ^ 2 * (y 9) ^ 2 / 4
  + 6 * t ^ 2 * (y 0) ^ 2 * (y 6) ^ 2 * (y 8) + 12 * t ^ 2 * (y 0) ^ 2 * (y 7) ^ 2 * (y 8)
  - t ^ 2 * (y 1) * (y 6) ^ 2 * (y 9) ^ 2 - t ^ 2 * (y 1) * (y 7) ^ 2 * (y 9) ^ 2
  + 36 * t ^ 2 * (y 1) ^ 2 * (y 6) ^ 2 * (y 8) + 24 * t ^ 2 * (y 1) ^ 2 * (y 7) ^ 2 * (y 8)
  + 12 * t ^ 2 * (y 2) ^ 2 * (y 6) ^ 2 * (y 8) + 24 * t ^ 2 * (y 2) ^ 2 * (y 7) ^ 2 * (y 8)
  + t ^ 2 * (y 3) * (y 6) ^ 2 * (y 9) ^ 2 / 4 + t ^ 2 * (y 3) * (y 7) ^ 2 * (y 9) ^ 2 / 4
  + 6 * t ^ 2 * (y 3) ^ 2 * (y 6) ^ 2 * (y 8) + 36 * t ^ 2 * (y 3) ^ 2 * (y 7) ^ 2 * (y 8)
  + 12 * t ^ 2 * (y 4) ^ 2 * (y 6) ^ 2 * (y 8) + 24 * t ^ 2 * (y 4) ^ 2 * (y 7) ^ 2 * (y 8)
  + 6 * t ^ 2 * (y 5) ^ 2 * (y 6) ^ 2 * (y 8) + 12 * t ^ 2 * (y 5) ^ 2 * (y 7) ^ 2 * (y 8)
  + 3 * t ^ 3 * (y 0) ^ 2 * (y 6) ^ 2 * (y 8) ^ 2 + 3 * t ^ 3 * (y 0) ^ 2 * (y 6) ^ 2 * (y 9) ^ 2
  + 6 * t ^ 3 * (y 0) ^ 2 * (y 7) ^ 2 * (y 8) ^ 2 + 3 * t ^ 3 * (y 0) ^ 2 * (y 7) ^ 2 * (y 9) ^ 2
  + 18 * t ^ 3 * (y 1) ^ 2 * (y 6) ^ 2 * (y 8) ^ 2 + 6 * t ^ 3 * (y 1) ^ 2 * (y 6) ^ 2 * (y 9) ^ 2
  + 12 * t ^ 3 * (y 1) ^ 2 * (y 7) ^ 2 * (y 8) ^ 2 + 6 * t ^ 3 * (y 1) ^ 2 * (y 7) ^ 2 * (y 9) ^ 2
  + 6 * t ^ 3 * (y 2) ^ 2 * (y 6) ^ 2 * (y 8) ^ 2 + 18 * t ^ 3 * (y 2) ^ 2 * (y 6) ^ 2 * (y 9) ^ 2
  + 12 * t ^ 3 * (y 2) ^ 2 * (y 7) ^ 2 * (y 8) ^ 2 + 6 * t ^ 3 * (y 2) ^ 2 * (y 7) ^ 2 * (y 9) ^ 2
  + 3 * t ^ 3 * (y 3) ^ 2 * (y 6) ^ 2 * (y 8) ^ 2 + 3 * t ^ 3 * (y 3) ^ 2 * (y 6) ^ 2 * (y 9) ^ 2
  + 18 * t ^ 3 * (y 3) ^ 2 * (y 7) ^ 2 * (y 8) ^ 2 + 3 * t ^ 3 * (y 3) ^ 2 * (y 7) ^ 2 * (y 9) ^ 2
  + 6 * t ^ 3 * (y 4) ^ 2 * (y 6) ^ 2 * (y 8) ^ 2 + 6 * t ^ 3 * (y 4) ^ 2 * (y 6) ^ 2 * (y 9) ^ 2
  + 12 * t ^ 3 * (y 4) ^ 2 * (y 7) ^ 2 * (y 8) ^ 2
  + 18 * t ^ 3 * (y 4) ^ 2 * (y 7) ^ 2 * (y 9) ^ 2 + 3 * t ^ 3 * (y 5) ^ 2 * (y 6) ^ 2 * (y 8) ^ 2
  + 3 * t ^ 3 * (y 5) ^ 2 * (y 6) ^ 2 * (y 9) ^ 2 + 6 * t ^ 3 * (y 5) ^ 2 * (y 7) ^ 2 * (y 8) ^ 2
  + 3 * t ^ 3 * (y 5) ^ 2 * (y 7) ^ 2 * (y 9) ^ 2 + 24 * t * (y 0) * (y 1) * (y 6) * (y 7)
  + 24 * t * (y 0) * (y 3) * (y 6) * (y 7) + 24 * t * (y 0) * (y 4) * (y 6) * (y 8)
  + 24 * t * (y 0) * (y 5) * (y 6) * (y 9) + 2 * t * (y 0) * (y 6) * (y 7) * (y 8)
  + t * (y 0) * (y 6) * (y 7) * (y 9) / 2 + t * (y 0) * (y 6) * (y 8) * (y 9) / 2
  + t * (y 0) * (y 7) * (y 8) * (y 9) / 2 + 24 * t * (y 1) * (y 2) * (y 6) * (y 8)
  + 24 * t * (y 1) * (y 3) * (y 6) * (y 7) + 48 * t * (y 1) * (y 4) * (y 6) * (y 8)
  + 24 * t * (y 1) * (y 4) * (y 7) * (y 8) + 24 * t * (y 1) * (y 5) * (y 6) * (y 9)
  + 24 * t * (y 1) * (y 5) * (y 7) * (y 9) - 2 * t * (y 1) * (y 6) * (y 8) * (y 9)
  - 2 * t * (y 1) * (y 7) * (y 8) * (y 9) + 24 * t * (y 2) * (y 3) * (y 7) * (y 8)
  + 24 * t * (y 2) * (y 4) * (y 6) * (y 9) + 24 * t * (y 2) * (y 4) * (y 7) * (y 9)
  + t * (y 2) * (y 6) * (y 7) * (y 8) - 2 * t * (y 2) * (y 6) * (y 7) * (y 9)
  + 48 * t * (y 3) * (y 4) * (y 7) * (y 8) + 24 * t * (y 3) * (y 5) * (y 7) * (y 9)
  + 2 * t * (y 3) * (y 6) * (y 7) * (y 8) + t * (y 3) * (y 6) * (y 7) * (y 9) / 2
  + t * (y 3) * (y 6) * (y 8) * (y 9) / 2 + t * (y 3) * (y 7) * (y 8) * (y 9) / 2
  + 24 * t * (y 4) * (y 5) * (y 8) * (y 9) + t * (y 4) * (y 6) * (y 7) * (y 8)
  - 2 * t * (y 4) * (y 6) * (y 7) * (y 9) + 24 * t ^ 2 * (y 0) * (y 1) * (y 6) ^ 2 * (y 8)
  + 24 * t ^ 2 * (y 0) * (y 2) * (y 6) ^ 2 * (y 9) + t ^ 2 * (y 0) * (y 6) * (y 7) * (y 9) ^ 2 / 2
  + t ^ 2 * (y 0) * (y 7) ^ 2 * (y 8) * (y 9) / 2 + 6 * t ^ 2 * (y 0) ^ 2 * (y 6) * (y 7) * (y 8)
  + 6 * t ^ 2 * (y 0) ^ 2 * (y 7) * (y 8) * (y 9) + 24 * t ^ 2 * (y 1) * (y 2) * (y 6) ^ 2 * (y 9)
  + 24 * t ^ 2 * (y 1) * (y 3) * (y 7) ^ 2 * (y 8)
  + 24 * t ^ 2 * (y 1) * (y 4) * (y 6) * (y 8) ^ 2
  + 24 * t ^ 2 * (y 1) * (y 4) * (y 7) ^ 2 * (y 9) - 2 * t ^ 2 * (y 1) * (y 6) * (y 7) * (y 9) ^ 2
  + 36 * t ^ 2 * (y 1) ^ 2 * (y 6) * (y 7) * (y 8)
  + 12 * t ^ 2 * (y 1) ^ 2 * (y 7) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 2) * (y 5) * (y 6) * (y 9) ^ 2 - 2 * t ^ 2 * (y 2) * (y 6) ^ 2 * (y 8) * (y 9)
  + t ^ 2 * (y 2) * (y 7) ^ 2 * (y 8) * (y 9) + 12 * t ^ 2 * (y 2) ^ 2 * (y 6) * (y 7) * (y 8)
  + 12 * t ^ 2 * (y 2) ^ 2 * (y 7) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 3) * (y 4) * (y 7) * (y 8) ^ 2
  + 24 * t ^ 2 * (y 3) * (y 4) * (y 7) ^ 2 * (y 9) + t ^ 2 * (y 3) * (y 6) * (y 7) * (y 9) ^ 2 / 2
  + 6 * t ^ 2 * (y 3) ^ 2 * (y 6) * (y 7) * (y 8) + 6 * t ^ 2 * (y 3) ^ 2 * (y 7) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 4) * (y 5) * (y 7) * (y 9) ^ 2 - 2 * t ^ 2 * (y 4) * (y 6) ^ 2 * (y 8) * (y 9)
  + t ^ 2 * (y 4) * (y 7) ^ 2 * (y 8) * (y 9) + 12 * t ^ 2 * (y 4) ^ 2 * (y 6) * (y 7) * (y 8)
  + 36 * t ^ 2 * (y 4) ^ 2 * (y 7) * (y 8) * (y 9) + 6 * t ^ 2 * (y 5) ^ 2 * (y 6) * (y 7) * (y 8)
  + 6 * t ^ 2 * (y 5) ^ 2 * (y 7) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 0) * (y 3) * (y 6) * (y 7) * (y 8)
  + 24 * t ^ 2 * (y 0) * (y 4) * (y 6) * (y 7) * (y 9)
  + t ^ 2 * (y 0) * (y 6) * (y 7) * (y 8) * (y 9) / 2
  + 24 * t ^ 2 * (y 1) * (y 2) * (y 6) * (y 7) * (y 9)
  + 48 * t ^ 2 * (y 1) * (y 3) * (y 6) * (y 7) * (y 8)
  + 24 * t ^ 2 * (y 1) * (y 4) * (y 6) * (y 7) * (y 9)
  + 24 * t ^ 2 * (y 1) * (y 5) * (y 6) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 2) * (y 3) * (y 6) * (y 7) * (y 9)
  + 24 * t ^ 2 * (y 2) * (y 4) * (y 6) * (y 8) * (y 9)
  - t ^ 2 * (y 2) * (y 6) * (y 7) * (y 8) * (y 9)
  + 24 * t ^ 2 * (y 3) * (y 5) * (y 7) * (y 8) * (y 9)
  - t ^ 2 * (y 4) * (y 6) * (y 7) * (y 8) * (y 9)
  + 24 * t ^ 3 * (y 1) * (y 2) * (y 6) ^ 2 * (y 8) * (y 9)
  + 24 * t ^ 3 * (y 1) * (y 3) * (y 6) * (y 7) * (y 8) ^ 2
  + 24 * t ^ 3 * (y 2) * (y 4) * (y 6) * (y 7) * (y 9) ^ 2
  + 24 * t ^ 3 * (y 3) * (y 4) * (y 7) ^ 2 * (y 8) * (y 9)
  + 24 * t ^ 3 * (y 1) * (y 4) * (y 6) * (y 7) * (y 8) * (y 9)
  + 24 * t ^ 3 * (y 2) * (y 3) * (y 6) * (y 7) * (y 8) * (y 9)

lemma qx3_jet (t : ℝ) (y : Fin 10 → ℝ) :
    Qg (symY (t • y)) (symPart (vecMulVec ![(t • y) 6, (t • y) 7, 1] ![1, 1 + (t • y) 8, (t • y) 9])) =
      0 + t * qx3_1 y + t ^ 2 * qx3_2 y + t ^ 3 * qx3_R t y := by
  simp [symY, Pi.smul_apply, smul_eq_mul, det_fin_three, cof, adjugate_fin_three, dotProduct, mulVec, Fin.sum_univ_three, vecMulVec_apply, Lg, Qg, qx3_1, qx3_2, qx3_R, symPart, Matrix.add_apply, Matrix.smul_apply, transpose_apply]
  ring

lemma continuous_qx3_R : Continuous fun p : ℝ × (Fin 10 → ℝ) => qx3_R p.1 p.2 := by
  unfold qx3_R; fun_prop

/-- The quadratic part `yᵀ A_3 y` of `P3`. -/
def Q3 (y : Fin 10 → ℝ) : ℝ :=
  2 * ((1) * qx3_2 y + Dd_1 y * qx3_1 y + Dd_2 y * (0))
    + ((1) * ly3_2 y + al3_1 y * ly3_1 y + al3_2 y * (0))

/-- The cubic remainder of `P3`. -/
def R3 (t : ℝ) (y : Fin 10 → ℝ) : ℝ :=
  2 * jetRem (1) (Dd_1 y) (Dd_2 y) (Dd_R t y) (0) (qx3_1 y) (qx3_2 y) (qx3_R t y) t
    + jetRem (1) (al3_1 y) (al3_2 y) (al3_R t y) (0) (ly3_1 y) (ly3_2 y)
      (ly3_R t y) t

lemma P3_expand (t : ℝ) (y : Fin 10 → ℝ) :
    P3 (t • y) = t ^ 2 * Q3 y + t ^ 3 * R3 t y := by
  have h0 : 2 * ((1) * (0)) + (1) * (0) = (0 : ℝ) := by norm_num
  have h1 : 2 * ((1) * qx3_1 y + Dd_1 y * (0)) + ((1) * ly3_1 y + al3_1 y * (0)) = 0 := by
    simp only [qx3_1, Dd_1, ly3_1, al3_1]; ring
  have e : P3 (t • y) = 2 * (det (1 + (2 : ℝ) • symY (t • y)) * Qg (symY (t • y)) (symPart (vecMulVec ![(t • y) 6, (t • y) 7, 1] ![1, 1 + (t • y) 8, (t • y) 9])))
      + (![(t • y) 6, (t • y) 7, 1] ⬝ᵥ (cof (1 + (2 : ℝ) • symY (t • y)) *ᵥ ![(t • y) 6, (t • y) 7, 1])) * Lg (symY (t • y)) (vecMulVec ![1, 1 + (t • y) 8, (t • y) 9] ![1, 1 + (t • y) 8, (t • y) 9]) := by
    simp only [P3, Pc]; ring
  rw [e, Dd_jet, qx3_jet, al3_jet, ly3_jet, jet_mul, jet_mul, Q3, R3]
  linear_combination h0 + t * h1

/-- Positive definiteness of `A_3 - ¼ Id`: an LDLᵀ certificate. -/
lemma Q3_cert (y : Fin 10 → ℝ) :
    Q3 y - 1/4 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 + y 4 ^ 2 + y 5 ^ 2 + y 6 ^ 2 + y 7 ^ 2 + y 8 ^ 2 + y 9 ^ 2) =
      51 / 4 * ((y 0) + 2 * (y 2) / 51 + 8 * (y 3) / 51 + 2 * (y 4) / 51 + 8 * (y 5) / 51 + 4 * (y 7) / 51
        - 4 * (y 8) / 51) ^ 2
      + 95 / 4 * ((y 1) - 32 * (y 5) / 95) ^ 2
      + 9329 / 204 * ((y 2) + 86 * (y 3) / 9329 + 236 * (y 4) / 491 - 16 * (y 5) / 9329 - 408 * (y 6) / 9329
        - 416 * (y 7) / 9329 + 8 * (y 8) / 9329) ^ 2
      + 463927 / 37316 * ((y 3) + 190 * (y 4) / 10789 + 1464 * (y 5) / 10789 + 38004 * (y 6) / 463927
        - 5152 * (y 7) / 463927 + 4 * (y 8) / 43) ^ 2
      + 1517435 / 43156 * ((y 4) - 32 * (y 5) / 15973 - 480 * (y 6) / 15973 - 480 * (y 7) / 15973) ^ 2
      + 51667733 / 6069740 * ((y 5) - 872480 * (y 6) / 51667733 - 872480 * (y 7) / 51667733) ^ 2
      + 13729495521 / 8886850076 * ((y 6) - 331936128 * (y 7) / 4576498507 - 826683728 * (y 8) / 13729495521) ^ 2
      + 28132564605 / 18305994028 * ((y 7) + 16 * (y 8) / 285) ^ 2
      + 1771 / 1140 * ((y 8)) ^ 2
      + 7 / 4 * ((y 9)) ^ 2 := by
  simp only [Q3, qx3_2, qx3_1, Dd_1, Dd_2, ly3_2, ly3_1, al3_1, al3_2]
  ring

lemma P3_eventually_nonneg : ∀ᶠ y in 𝓝 0, 0 ≤ P3 y := by
  refine eventually_nonneg_of_expansion (P3) (Q3) (R3) ?_ (m := 1/4) (by norm_num)
    (fun y => ?_) P3_expand
  · unfold R3 jetRem
    have := continuous_Dd_R; have := continuous_qx3_R; have := continuous_al3_R
    have := continuous_ly3_R
    unfold Dd_1 Dd_2 qx3_1 qx3_2 al3_1 al3_2 ly3_1 ly3_2
    fun_prop
  · have h := Q3_cert y
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    have : 0 ≤ Q3 y - 1/4 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 + y 4 ^ 2 + y 5 ^ 2 + y 6 ^ 2 + y 7 ^ 2 + y 8 ^ 2 + y 9 ^ 2) := by rw [h]; positivity
    norm_num at this ⊢
    linarith

end QcSOn
