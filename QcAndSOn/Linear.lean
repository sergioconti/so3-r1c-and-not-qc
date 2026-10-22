/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import QcAndSOn.SecondVariation
import QcAndSOn.Sverak

/-!
# The geometrically linear case (Section 2 of the paper)

A quartic polynomial `fL F = gL (sym F)`, which is invariant under the addition of
skew-symmetric matrices, rank-one convex, and not quasiconvex (Theorem 2.1).

* `qL`, `gL`, `fL`: the polynomials `q`, `g_lin`, `f` of eqs. (2.1)–(2.3) (`gL` uses the upper
  triangular entries);
* `gL_line`: the expansion of `gL (e + s m)` in powers of `s`, with coefficients `c1L`, `c2L`,
  `c3L`, `c4L`;
* Lemma 2.3 (minimizers): `fL_min`: `fL ≥ minL = (575 - 193√193)/5832`, with equality iff
  `sym F = eMin (±α) = ±α (M₁ + M₂) + w_* M₃`; Step 1 `gL_sub_gPlane` (projection onto `L_sym`),
  Step 2 `gPlane_sub_minL`, `gPlane_eq_minL`;
* Lemma 2.5 (rank-one convexity): `two_c2L_eq` (eq. (2.5)), Step 1 `qL_symPart_vecMulVec`
  (eq. (2.6)), Step 2 `linid` and `linprod` (eqs. (2.8), (2.7)), Step 3 `cubD2_ge`, Step 4
  `D2gL_nonneg`; then `rankOneConvex_fL`;
* Lemma 2.4 (failure of quasiconvexity): `integral_quartic_phi`
  (`⨍_Y (cos² x₁ + cos² x₂ + cos² (x₁ + x₂))² = 21/8`), `average_fL_phi`
  (`⨍_Y fL (ε ∇φ) = -ε³/4 + 63 ε⁴/32` for Šverák's test function `φ`), `not_quasiconvex_fL`;
* `linear_main`: Theorem 2.1.
-/

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace QcSOn

/-! ### Definitions -/

/-- The quadratic form `q(e) = 4e₁₂² - 2e₁₁e₂₂ + 4(e₁₃ - e₂₃)²` of eq. (2.1) (upper triangular
entries). -/
def qL (e : Mat 3 3) : ℝ :=
  4 * e 0 1 ^ 2 - 2 * e 0 0 * e 1 1 + 4 * (e 0 2 - e 1 2) ^ 2

/-- `|e|²` for symmetric `e`, in terms of the upper triangular entries. -/
def nL (e : Mat 3 3) : ℝ :=
  e 0 0 ^ 2 + e 1 1 ^ 2 + e 2 2 ^ 2 + 2 * (e 0 1 ^ 2 + e 0 2 ^ 2 + e 1 2 ^ 2)

/-- The linear functional `v(e) = e₁₃ + e₂₃` (`r(e) = e₁₁`, `s(e) = e₂₂`). -/
def vL (e : Mat 3 3) : ℝ := e 0 2 + e 1 2

/-- `g_lin(e) = q(e) + e₁₁ e₂₂ (e₁₃ + e₂₃) + ¾ |e|⁴` (eq. (2.2)). -/
def gL (e : Mat 3 3) : ℝ := qL e + e 0 0 * e 1 1 * vL e + 3 / 4 * nL e ^ 2

/-- The energy `f(F) = g_lin(sym F)` of Theorem 2.1 (eq. (2.3)). -/
def fL (F : Mat 3 3) : ℝ := gL (symPart F)

/-! ### Invariance and continuity -/

lemma symPart_add_skew (F A : Mat 3 3) (hA : A.transpose = -A) :
    symPart (F + A) = symPart F := by
  ext i j
  have : A j i = -A i j := by simpa using congrFun (congrFun hA i) j
  simp [symPart, this]
  ring

/-- `fL` is invariant under infinitesimal rotations. -/
lemma fL_add_skew (F A : Mat 3 3) (hA : A.transpose = -A) : fL (F + A) = fL F := by
  rw [fL, symPart_add_skew F A hA, fL]

lemma continuous_fL : Continuous fL := by
  unfold fL gL qL nL vL symPart; fun_prop

/-- The linear energy `fL F = g_lin(sym F)` is smooth (in the entries of the matrix). -/
lemma contDiff_fL : ContDiff ℝ ∞ (fun X : Fin 3 → Fin 3 → ℝ => fL (Matrix.of X)) := by
  simp only [fL, gL, qL, nL, vL, symPart, Matrix.smul_apply,
    Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul]
  fun_prop

/-! ### Lemma 2.3: the minimizers

With `M₁ = e₁⊗e₁`, `M₂ = e₂⊗e₂`, `M₃ = e₃⊙(e₁+e₂)` (eq. (2.4)), the minimizers of `g_lin` are
`e_± = ±α (M₁ + M₂) + w_* M₃`, `w_* = (11 - √193)/18`, `α = √(w_*(w_* - 2))`.
Step 1: projecting `e` onto `L_sym = span {M₁, M₂, M₃}` does not increase `g_lin` (`gL_sub_gPlane`).
Step 2: on `L_sym`, with `e = r M₁ + s M₂ + w M₃`, `g_lin = gPlane r s w`, and
`gPlane r s w - min = ½ (r-s)² (2-w) + ¾ (r²+s²+w² - (2-w)/3)² + ½ (w - w_*)² (w₁ - w)` with
`w₁ = 11/6 - 2 w_* > 2` (`gPlane_sub_minL`); for `w > 2`, `gPlane ≥ 0`. -/

/-- `w_* = (11 - √193)/18`, the negative root of `9w² - 11w - 2`. -/
def wStar : ℝ := (11 - √193) / 18

/-- `α = √(w_*(w_* - 2))`. -/
def alphaL : ℝ := √(wStar * (wStar - 2))

/-- The minimum value `(575 - 193√193)/5832` of `fL`. -/
def minL : ℝ := (575 - 193 * √193) / 5832

/-- `a (M₁ + M₂) + w_* M₃`; the minimizers are `eMin α` and `eMin (-α)`. -/
def eMin (a : ℝ) : Mat 3 3 := !![a, 0, wStar / 2; 0, a, wStar / 2; wStar / 2, wStar / 2, 0]

/-- `g_lin` on `L_sym`: `g_lin(r M₁ + s M₂ + w M₃) = -2rs + rsw + ¾ (r² + s² + w²)²`. -/
def gPlane (r s w : ℝ) : ℝ := r * s * (w - 2) + 3 / 4 * (r ^ 2 + s ^ 2 + w ^ 2) ^ 2

lemma sqrt193_sq : √193 ^ 2 = 193 := Real.sq_sqrt (by norm_num)

lemma sqrt193_gt : 25 / 2 < √193 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma wStar_lt : wStar < -1 / 12 := by
  unfold wStar; linarith [sqrt193_gt]

lemma wStar_quad : 9 * wStar ^ 2 - 11 * wStar - 2 = 0 := by
  unfold wStar; linear_combination (1 / 36) * sqrt193_sq

lemma alphaL_sq : alphaL ^ 2 = wStar * (wStar - 2) :=
  Real.sq_sqrt (by nlinarith [wStar_lt])

lemma minL_neg : minL < 0 := by
  unfold minL; nlinarith [sqrt193_gt]

/-- Step 1: `g_lin(e) - g_lin(Pe)` is a sum of nonnegative terms; here
`|e|² - |Pe|² = e₃₃² + 2e₁₂² + (e₁₃ - e₂₃)²` and `|Pe|² = r² + s² + v²`. -/
lemma gL_sub_gPlane (e : Mat 3 3) :
    gL e - gPlane (e 0 0) (e 1 1) (vL e) = 4 * e 0 1 ^ 2 + 4 * (e 0 2 - e 1 2) ^ 2
      + 3 / 4 * (e 2 2 ^ 2 + 2 * e 0 1 ^ 2 + (e 0 2 - e 1 2) ^ 2) ^ 2
      + 3 / 2 * ((e 2 2 ^ 2 + 2 * e 0 1 ^ 2 + (e 0 2 - e 1 2) ^ 2)
        * (e 0 0 ^ 2 + e 1 1 ^ 2 + vL e ^ 2)) := by
  simp only [gL, qL, nL, vL, gPlane]; ring

/-- Step 2: the key identity on `L_sym`. -/
lemma gPlane_sub_minL (r s w : ℝ) :
    gPlane r s w - minL = (r - s) ^ 2 * (2 - w) / 2
      + 3 / 4 * (r ^ 2 + s ^ 2 + w ^ 2 - (2 - w) / 3) ^ 2
      + (w - wStar) ^ 2 * ((11 / 6 - 2 * wStar) - w) / 2 := by
  simp only [gPlane, minL, wStar]
  linear_combination (-(2 * √193 + 54 * w - 33) / 11664) * sqrt193_sq

lemma gPlane_nonneg_of_two_lt {r s w : ℝ} (hw : 2 < w) : 0 ≤ gPlane r s w := by
  unfold gPlane
  have h1 : 0 ≤ (r + s) ^ 2 / 2 * (w - 2) := by have := sq_nonneg (r + s); positivity
  have h2 : 0 ≤ (r ^ 2 + s ^ 2) / 2 * (3 * w ^ 2 - w + 2) := by
    have : 0 < 3 * w ^ 2 - w + 2 := by nlinarith [sq_nonneg (w - 1 / 6)]
    positivity
  nlinarith [sq_nonneg (r ^ 2 + s ^ 2), mul_nonneg (add_nonneg (sq_nonneg r) (sq_nonneg s))
    (sq_nonneg w)]

lemma minL_le_gPlane (r s w : ℝ) : minL ≤ gPlane r s w := by
  rcases le_or_gt w 2 with hw | hw
  · have h := gPlane_sub_minL r s w
    have h1 : 0 ≤ (r - s) ^ 2 * (2 - w) / 2 := by
      have := sq_nonneg (r - s); have : 0 ≤ 2 - w := by linarith
      positivity
    have h3 : 0 ≤ (w - wStar) ^ 2 * ((11 / 6 - 2 * wStar) - w) / 2 := by
      have := sq_nonneg (w - wStar); have : 0 ≤ (11 / 6 - 2 * wStar) - w := by
        linarith [wStar_lt]
      positivity
    nlinarith [sq_nonneg (r ^ 2 + s ^ 2 + w ^ 2 - (2 - w) / 3)]
  · linarith [gPlane_nonneg_of_two_lt (r := r) (s := s) hw, minL_neg]

/-- Equality in Step 2: `gPlane r s w = min` only at `r = s = ±α`, `w = w_*`. -/
lemma gPlane_eq_minL {r s w : ℝ} (h : gPlane r s w = minL) :
    w = wStar ∧ r = s ∧ (r = alphaL ∨ r = -alphaL) := by
  have hw : w ≤ 2 := by
    by_contra hw; push Not at hw
    linarith [gPlane_nonneg_of_two_lt (r := r) (s := s) hw, minL_neg]
  have hid := gPlane_sub_minL r s w
  rw [h, sub_self] at hid
  have h1 : 0 ≤ (r - s) ^ 2 * (2 - w) / 2 := by
    have := sq_nonneg (r - s); have : 0 ≤ 2 - w := by linarith
    positivity
  have hw1 : 0 < (11 / 6 - 2 * wStar) - w := by linarith [wStar_lt]
  have h3 : 0 ≤ (w - wStar) ^ 2 * ((11 / 6 - 2 * wStar) - w) / 2 := by
    have := sq_nonneg (w - wStar); positivity
  have h2 := sq_nonneg (r ^ 2 + s ^ 2 + w ^ 2 - (2 - w) / 3)
  have e3 : (w - wStar) ^ 2 * ((11 / 6 - 2 * wStar) - w) = 0 := by nlinarith
  have hws : w = wStar := by
    have := (mul_eq_zero.1 e3).resolve_right hw1.ne'
    exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
  subst hws
  have e1 : (r - s) ^ 2 * (2 - wStar) = 0 := by nlinarith
  have hrs : r = s := by
    have := (mul_eq_zero.1 e1).resolve_right (by linarith [wStar_lt])
    exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
  subst hrs
  have e2 : r ^ 2 + r ^ 2 + wStar ^ 2 - (2 - wStar) / 3 = 0 := by
    have : (r ^ 2 + r ^ 2 + wStar ^ 2 - (2 - wStar) / 3) ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  have hr : r ^ 2 = alphaL ^ 2 := by
    rw [alphaL_sq]; linear_combination e2 / 2 - wStar_quad / 6
  exact ⟨rfl, rfl, sq_eq_sq_iff_eq_or_eq_neg.1 hr⟩

lemma gL_eMin (a : ℝ) (ha : a ^ 2 = alphaL ^ 2) : gL (eMin a) = minL := by
  have h : gL (eMin a) = gPlane a a wStar := by
    simp [gL, qL, nL, vL, gPlane, eMin]; ring
  have hid := gPlane_sub_minL a a wStar
  rw [h]
  have : a ^ 2 + a ^ 2 + wStar ^ 2 - (2 - wStar) / 3 = 0 := by
    rw [ha, alphaL_sq]; linear_combination wStar_quad / 3
  rw [this] at hid
  linarith [show (a - a) ^ 2 = 0 by ring, show (wStar - wStar) ^ 2 = 0 by ring, hid]

/-- **Lemma 2.3** (minimizers of the linear energy). `fL ≥ (575 - 193√193)/5832`, with equality
if and only if `sym F = ±α (M₁ + M₂) + w_* M₃`. -/
theorem fL_min (F : Mat 3 3) :
    minL ≤ fL F ∧ (fL F = minL ↔ symPart F = eMin alphaL ∨ symPart F = eMin (-alphaL)) := by
  set e := symPart F with he
  have hsym : ∀ i j, e j i = e i j := fun i j => by
    simp only [e, symPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]; ring
  have hP := gL_sub_gPlane e
  have hX := sq_nonneg (e 2 2 ^ 2 + 2 * e 0 1 ^ 2 + (e 0 2 - e 1 2) ^ 2)
  have hXN : 0 ≤ (e 2 2 ^ 2 + 2 * e 0 1 ^ 2 + (e 0 2 - e 1 2) ^ 2)
      * (e 0 0 ^ 2 + e 1 1 ^ 2 + vL e ^ 2) := by positivity
  have ha := sq_nonneg (e 0 1)
  have hd := sq_nonneg (e 0 2 - e 1 2)
  have hG := minL_le_gPlane (e 0 0) (e 1 1) (vL e)
  have hge : gPlane (e 0 0) (e 1 1) (vL e) ≤ gL e := by linarith
  refine ⟨hG.trans hge, fun h => ?_, fun h => ?_⟩
  · change gL e = minL at h
    -- equality in Step 1: `e₁₂ = 0`, `e₁₃ = e₂₃`, `e₃₃ = 0`
    have hX0 : (e 2 2 ^ 2 + 2 * e 0 1 ^ 2 + (e 0 2 - e 1 2) ^ 2) ^ 2 = 0 := by linarith
    have hX1 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hX0
    have h22 := sq_nonneg (e 2 2)
    have q1 : e 0 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith)
    have q2 : e 0 2 = e 1 2 :=
      sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith))
    have q3 : e 2 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith)
    -- equality in Step 2
    obtain ⟨hw, hrs, hr⟩ := gPlane_eq_minL (show gPlane (e 0 0) (e 1 1) (vL e) = minL by linarith)
    have h02 : e 0 2 = wStar / 2 := by unfold vL at hw; linarith
    have hE : ∀ a, e 0 0 = a → e = eMin a := fun a ha => by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [eMin, ha, ← hrs, q1, q3, h02, ← q2, hsym 0 1, hsym 0 2, hsym 1 2]
    rcases hr with hr | hr
    · exact Or.inl (hE _ hr)
    · exact Or.inr (hE _ hr)
  · change gL e = minL
    rcases h with h | h <;> rw [h]
    · exact gL_eMin _ rfl
    · exact gL_eMin _ (by ring)

/-! ### Expansion along lines -/

/-- Polarization of `|e|²`. -/
def ipL (e m : Mat 3 3) : ℝ :=
  e 0 0 * m 0 0 + e 1 1 * m 1 1 + e 2 2 * m 2 2
    + 2 * (e 0 1 * m 0 1 + e 0 2 * m 0 2 + e 1 2 * m 1 2)

/-- Polarization of `q`. -/
def bqL (e m : Mat 3 3) : ℝ :=
  4 * e 0 1 * m 0 1 - (e 0 0 * m 1 1 + e 1 1 * m 0 0) + 4 * (e 0 2 - e 1 2) * (m 0 2 - m 1 2)

/-- `Dg_lin(e)[m]`. -/
def c1L (e m : Mat 3 3) : ℝ :=
  2 * bqL e m + (m 0 0 * e 1 1 * vL e + e 0 0 * m 1 1 * vL e + e 0 0 * e 1 1 * vL m)
    + 3 * nL e * ipL e m

/-- `½ D²g_lin(e)[m, m]`. -/
def c2L (e m : Mat 3 3) : ℝ :=
  qL m + (m 0 0 * m 1 1 * vL e + m 0 0 * e 1 1 * vL m + e 0 0 * m 1 1 * vL m)
    + 3 * ipL e m ^ 2 + 3 / 2 * nL e * nL m

/-- `⅙ D³g_lin(e)[m, m, m]`. -/
def c3L (e m : Mat 3 3) : ℝ := m 0 0 * m 1 1 * vL m + 3 * ipL e m * nL m

/-- `1/24 D⁴g_lin[m, m, m, m]`. -/
def c4L (m : Mat 3 3) : ℝ := 3 / 4 * nL m ^ 2

lemma gL_line (e m : Mat 3 3) (s : ℝ) :
    gL (e + s • m) = gL e + c1L e m * s + c2L e m * s ^ 2 + c3L e m * s ^ 3 + c4L m * s ^ 4 := by
  simp only [gL, qL, nL, vL, c1L, c2L, c3L, c4L, bqL, ipL, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- The second derivative along the line, evaluated at a shifted base point. -/
lemma c2L_line (e m : Mat 3 3) (t : ℝ) :
    2 * c2L (e + t • m) m = 2 * c2L e m + 6 * c3L e m * t + 12 * c4L m * t ^ 2 := by
  simp only [c2L, c3L, c4L, qL, nL, vL, ipL, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- A quartic polynomial with nonnegative second derivative is convex. -/
lemma convexOn_quartic (c0 c1 c2 c3 c4 : ℝ) (h : ∀ t, 0 ≤ 2 * c2 + 6 * c3 * t + 12 * c4 * t ^ 2) :
    ConvexOn ℝ univ fun t => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4 := by
  have h1 : ∀ t, HasDerivAt (fun t => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4)
      (c1 + 2 * c2 * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3) t := fun t =>
    hasDerivAt_of_expansion (fun s => c2 + c3 * (3 * t + s) + c4 * (6 * t ^ 2 + 4 * t * s + s ^ 2))
      (by fun_prop) fun s => by ring
  have h2 : ∀ t, HasDerivAt (fun t => c1 + 2 * c2 * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3)
      (2 * c2 + 6 * c3 * t + 12 * c4 * t ^ 2) t := fun t =>
    hasDerivAt_of_expansion (fun s => 3 * c3 + c4 * (12 * t + 4 * s)) (by fun_prop)
      fun s => by ring
  exact convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    (fun t _ => (h1 t).continuousAt.continuousWithinAt) (fun t _ => (h1 t).hasDerivWithinAt)
    (fun t _ => (h2 t).hasDerivWithinAt) (fun t _ => h t)

/-! ### Lemma 2.5: rank-one convexity

With `e = sym F`, `M = a ⊙ b = sym (a ⊗ b)` and `β = (a₁b₂, a₂b₁, (a₁ - a₂)b₃ + a₃(b₁ - b₂))`,
`D²f(F)[a⊗b, a⊗b] = D²g_lin(e)[M,M] = 2 q(M) + D²(rsv)(e)[M,M] + ¾ D²(|·|⁴)(e)[M,M]`. -/

/-- `D²(rsv)(e)[M,M] = 2 (r(e) s(M) v(M) + s(e) r(M) v(M) + v(e) r(M) s(M))`. -/
def cubD2 (e M : Mat 3 3) : ℝ :=
  2 * (e 0 0 * (M 1 1 * vL M) + e 1 1 * (M 0 0 * vL M) + vL e * (M 0 0 * M 1 1))

/-- `D²(|·|⁴)(e)[M,M] = 4 |e|²|M|² + 8 ⟨e, M⟩²`. -/
def quartD2 (e M : Mat 3 3) : ℝ := 4 * nL e * nL M + 8 * ipL e M ^ 2

/-- `|β|² = (a₁b₂)² + (a₂b₁)² + ((a₁ - a₂)b₃ + a₃(b₁ - b₂))²`. -/
def bL (a b : Fin 3 → ℝ) : ℝ :=
  (a 0 * b 1) ^ 2 + (a 1 * b 0) ^ 2 + ((a 0 - a 1) * b 2 + a 2 * (b 0 - b 1)) ^ 2

lemma bL_nonneg (a b : Fin 3 → ℝ) : 0 ≤ bL a b := by unfold bL; positivity

/-- Eq. (2.5): `D²g_lin(e)[M,M] = 2 q(M) + D²(rsv)(e)[M,M] + ¾ D²(|·|⁴)(e)[M,M]`. -/
lemma two_c2L_eq (e M : Mat 3 3) :
    2 * c2L e M = 2 * qL M + cubD2 e M + 3 / 4 * quartD2 e M := by
  simp only [c2L, cubD2, quartD2]; ring

lemma symPart_vecMulVec_apply (a b : Fin 3 → ℝ) (i j : Fin 3) :
    symPart (Matrix.vecMulVec a b) i j = (a i * b j + a j * b i) / 2 := by
  simp [symPart, Matrix.vecMulVec_apply]; ring

/-- `|a ⊙ b|² = ½ (|a|²|b|² + (a · b)²) ≥ ½ |a|²|b|²`. -/
lemma nL_symPart_vecMulVec (a b : Fin 3 → ℝ) :
    (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) * (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2)
      ≤ 2 * nL (symPart (Matrix.vecMulVec a b)) := by
  have hn : 2 * nL (symPart (Matrix.vecMulVec a b)) =
      (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) * (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2)
        + (a 0 * b 0 + a 1 * b 1 + a 2 * b 2) ^ 2 := by
    simp only [nL, symPart_vecMulVec_apply]; ring
  rw [hn]; nlinarith [sq_nonneg (a 0 * b 0 + a 1 * b 1 + a 2 * b 2)]

/-- **Step 1** (eq. (2.6)): `q(a ⊙ b) = |β|²`. -/
lemma qL_symPart_vecMulVec (a b : Fin 3 → ℝ) : qL (symPart (Matrix.vecMulVec a b)) = bL a b := by
  simp only [qL, bL, symPart_vecMulVec_apply]; ring

lemma cs3 (u1 u2 u3 w1 w2 w3 : ℝ) :
    (u1 * w1 + u2 * w2 + u3 * w3) ^ 2 ≤
      (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (w1 ^ 2 + w2 ^ 2 + w3 ^ 2) := by
  nlinarith [sq_nonneg (u1 * w2 - u2 * w1), sq_nonneg (u1 * w3 - u3 * w1),
    sq_nonneg (u2 * w3 - u3 * w2)]

/-- Cauchy–Schwarz bound for the terms of (2.8): if `Y = u · β` with `|u|² ≤ |a|²|b|²` and
`|β|² ≤ B`, then `Y² ≤ |a|²|b|² B`. -/
lemma sq_le_of_cs3 {u1 u2 u3 w1 w2 w3 Y AB B : ℝ}
    (hY : Y = u1 * w1 + u2 * w2 + u3 * w3)
    (hu : u1 ^ 2 + u2 ^ 2 + u3 ^ 2 ≤ AB) (hw : w1 ^ 2 + w2 ^ 2 + w3 ^ 2 ≤ B) :
    Y ^ 2 ≤ AB * B := by
  rw [hY]
  exact (cs3 u1 u2 u3 w1 w2 w3).trans (mul_le_mul hu hw (by positivity) (by
    nlinarith [sq_nonneg u1, sq_nonneg u2, sq_nonneg u3]))

/-- **Step 2**, eq. (2.8): `r(M) s(M) = β₁β₂` and
`r(M) v(M) = ½ a₁b₁ β₃ + a₁b₃ β₂ + a₃b₁ β₁` (and, by the symmetry exchanging `e₁` and `e₂`,
`s(M) v(M) = -½ a₂b₂ β₃ + a₂b₃ β₁ + a₃b₂ β₂`). -/
lemma linid (a b : Fin 3 → ℝ) :
    let M := symPart (Matrix.vecMulVec a b)
    M 0 0 * M 1 1 = (a 0 * b 1) * (a 1 * b 0) ∧
    M 0 0 * vL M = a 0 * b 0 / 2 * ((a 0 - a 1) * b 2 + a 2 * (b 0 - b 1))
      + a 0 * b 2 * (a 1 * b 0) + a 2 * b 0 * (a 0 * b 1) ∧
    M 1 1 * vL M = -(a 1 * b 1 / 2) * ((a 0 - a 1) * b 2 + a 2 * (b 0 - b 1))
      + a 1 * b 2 * (a 0 * b 1) + a 2 * b 1 * (a 1 * b 0) := by
  simp only [vL, symPart_vecMulVec_apply]
  refine ⟨by ring, by ring, by ring⟩

/-- **Step 2**, eq. (2.7): `(r(M)s(M))² + (r(M)v(M))² + (s(M)v(M))² ≤ 3 |a|²|b|² |β|²`. -/
lemma linprod (a b : Fin 3 → ℝ) :
    let M := symPart (Matrix.vecMulVec a b)
    (M 0 0 * M 1 1) ^ 2 + (M 0 0 * vL M) ^ 2 + (M 1 1 * vL M) ^ 2
      ≤ 3 * ((a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) * (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2)) * bL a b := by
  obtain ⟨h1, h2, h3⟩ := linid a b
  intro M
  set a1 := a 0; set a2 := a 1; set a3 := a 2; set b1 := b 0; set b2 := b 1; set b3 := b 2
  -- `|a|²|b|² = ∑ aᵢ² bⱼ²` dominates each of the sums of squares below
  have e1 : (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * (b1 ^ 2 + b2 ^ 2 + b3 ^ 2) =
      (a1 * b1) ^ 2 + (a1 * b2) ^ 2 + (a1 * b3) ^ 2 + (a2 * b1) ^ 2 + (a2 * b2) ^ 2
        + (a2 * b3) ^ 2 + (a3 * b1) ^ 2 + (a3 * b2) ^ 2 + (a3 * b3) ^ 2 := by ring
  have p1 := sq_nonneg (a1 * b1); have p2 := sq_nonneg (a1 * b2); have p3 := sq_nonneg (a1 * b3)
  have p4 := sq_nonneg (a2 * b1); have p5 := sq_nonneg (a2 * b2); have p6 := sq_nonneg (a2 * b3)
  have p7 := sq_nonneg (a3 * b1); have p8 := sq_nonneg (a3 * b2); have p9 := sq_nonneg (a3 * b3)
  have q3 := sq_nonneg ((a1 - a2) * b3 + a3 * (b1 - b2))
  have hB : bL a b = (a1 * b2) ^ 2 + (a2 * b1) ^ 2 + ((a1 - a2) * b3 + a3 * (b1 - b2)) ^ 2 := rfl
  have hY := sq_le_of_cs3
    (AB := (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)) (B := bL a b)
    (u1 := a1 * b1 / 2) (u2 := a1 * b3) (u3 := a3 * b1)
    (w1 := (a1 - a2) * b3 + a3 * (b1 - b2)) (w2 := a2 * b1) (w3 := a1 * b2)
    h2 (by rw [e1]; linarith) (by rw [hB]; linarith)
  have hX := sq_le_of_cs3
    (AB := (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)) (B := bL a b)
    (u1 := -(a2 * b2 / 2)) (u2 := a2 * b3) (u3 := a3 * b2)
    (w1 := (a1 - a2) * b3 + a3 * (b1 - b2)) (w2 := a1 * b2) (w3 := a2 * b1)
    h3 (by rw [e1]; linarith) (by rw [hB]; linarith)
  have hZ : (M 0 0 * M 1 1) ^ 2 ≤ (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)
      * bL a b := by
    rw [h1, show (a1 * b2 * (a2 * b1)) ^ 2 = (a2 * b1) ^ 2 * (a1 * b2) ^ 2 by ring]
    exact mul_le_mul (by rw [e1]; linarith) (by rw [hB]; linarith) (sq_nonneg _) (by positivity)
  linarith

/-- **Step 3**: `D²(rsv)(e)[M,M] ≥ -2√6 |M| |β| |e|`. -/
lemma cubD2_ge (e : Mat 3 3) (a b : Fin 3 → ℝ) :
    -(2 * √6 * √(nL (symPart (Matrix.vecMulVec a b))) * √(bL a b) * √(nL e))
      ≤ cubD2 e (symPart (Matrix.vecMulVec a b)) := by
  set M := symPart (Matrix.vecMulVec a b)
  set AB := (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) * (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2)
  have hAB : 0 ≤ AB := by positivity
  have hB := bL_nonneg a b
  have hM : AB ≤ 2 * nL M := nL_symPart_vecMulVec a b
  have hnM : 0 ≤ nL M := by linarith
  have hne : 0 ≤ nL e := by unfold nL; positivity
  -- `M₁, M₂, M₃` are orthonormal: `r(e)² + s(e)² + v(e)² ≤ |e|²`
  have hE : vL e ^ 2 + e 1 1 ^ 2 + e 0 0 ^ 2 ≤ nL e := by
    simp only [nL, vL]; nlinarith [sq_nonneg (e 0 2 - e 1 2), sq_nonneg (e 0 1)]
  have hsq : cubD2 e M ^ 2 ≤ 24 * nL M * bL a b * nL e := by
    have h := (cs3 (vL e) (e 1 1) (e 0 0) (M 0 0 * M 1 1) (M 0 0 * vL M) (M 1 1 * vL M)).trans
      (mul_le_mul hE (linprod a b) (by positivity) hne)
    have : 3 * AB * bL a b ≤ 3 * (2 * nL M) * bL a b := by gcongr
    calc cubD2 e M ^ 2 = 4 * (vL e * (M 0 0 * M 1 1) + e 1 1 * (M 0 0 * vL M)
          + e 0 0 * (M 1 1 * vL M)) ^ 2 := by unfold cubD2; ring
      _ ≤ 4 * (nL e * (3 * (2 * nL M) * bL a b)) := by
          gcongr; exact h.trans (mul_le_mul_of_nonneg_left (by linarith [this]) hne)
      _ = 24 * nL M * bL a b * nL e := by ring
  have hR : (2 * √6 * √(nL M) * √(bL a b) * √(nL e)) ^ 2 = 24 * nL M * bL a b * nL e := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hnM,
      Real.sq_sqrt hB, Real.sq_sqrt hne]
    ring
  exact (abs_le_of_sq_le_sq' (hR ▸ hsq) (by positivity)).1

/-- **Step 4** (Lemma 2.5): `D²g_lin(e)[a⊙b, a⊙b] ≥ (√2 |β| - √3 |M| |e|)² ≥ 0`. -/
lemma D2gL_nonneg (e : Mat 3 3) (a b : Fin 3 → ℝ) :
    0 ≤ 2 * c2L e (symPart (Matrix.vecMulVec a b)) := by
  set M := symPart (Matrix.vecMulVec a b)
  have hB := bL_nonneg a b
  have hnM : 0 ≤ nL M := by
    have := nL_symPart_vecMulVec a b
    have : 0 ≤ (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) * (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) := by positivity
    linarith
  have hne : 0 ≤ nL e := by unfold nL; positivity
  -- `D²(|·|⁴)(e)[M,M] ≥ 4 |e|²|M|²`
  have h4 : 4 * nL e * nL M ≤ quartD2 e M := by
    unfold quartD2; nlinarith [sq_nonneg (ipL e M)]
  have h6 : √6 = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hsq : 2 * bL a b - 2 * √6 * √(nL M) * √(bL a b) * √(nL e) + 3 * nL M * nL e =
      (√2 * √(bL a b) - √3 * √(nL M) * √(nL e)) ^ 2 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hX := Real.sq_sqrt hB; have hY := Real.sq_sqrt hnM; have hZ := Real.sq_sqrt hne
    rw [h6]
    linear_combination (-(√(bL a b) ^ 2)) * h2 - 2 * hX - (√(nL M) ^ 2 * √(nL e) ^ 2) * h3
      - 3 * √(nL e) ^ 2 * hY - 3 * nL M * hZ
  rw [two_c2L_eq, qL_symPart_vecMulVec]
  nlinarith [cubD2_ge e a b, sq_nonneg (√2 * √(bL a b) - √3 * √(nL M) * √(nL e))]

/-- **Rank-one convexity** of `fL` (Theorem 2.1, from Lemma 2.5). -/
theorem rankOneConvex_fL : RankOneConvex fL := by
  intro F a b
  have hline : ∀ t : ℝ, symPart (F + t • Matrix.vecMulVec a b) =
      symPart F + t • symPart (Matrix.vecMulVec a b) := fun t => by
    ext i j; simp [symPart]; ring
  have hfun : (fun t : ℝ => fL (F + t • Matrix.vecMulVec a b)) = fun t =>
      gL (symPart F) + c1L (symPart F) (symPart (Matrix.vecMulVec a b)) * t
        + c2L (symPart F) (symPart (Matrix.vecMulVec a b)) * t ^ 2
        + c3L (symPart F) (symPart (Matrix.vecMulVec a b)) * t ^ 3
        + c4L (symPart (Matrix.vecMulVec a b)) * t ^ 4 := funext fun t => by
    rw [fL, hline, gL_line]
  rw [hfun]
  exact convexOn_quartic _ _ _ _ _ fun t => by
    rw [← c2L_line]; exact D2gL_nonneg (symPart F + t • symPart (Matrix.vecMulVec a b)) a b

/-! ### The integral of the quartic term -/

lemma intervalIntegral_cos_sq_two_pi : ∫ t in (0)..(2 * π), cos t ^ 2 = π := by
  simp [integral_cos_sq]

lemma intervalIntegral_cos_pow_four_two_pi : ∫ t in (0)..(2 * π), cos t ^ 4 = 3 * π / 4 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, integral_cos_pow, intervalIntegral_cos_sq_two_pi]
  simp; ring

lemma intervalIntegral_sin_mul_cos_pow_three_two_pi :
    ∫ t in (0)..(2 * π), sin t * cos t ^ 3 = 0 := by
  simpa using integral_sin_pow_mul_cos_pow_odd (a := 0) (b := 2 * π) 1 1

lemma intervalIntegral_sin_mul_cos_two_pi : ∫ t in (0)..(2 * π), sin t * cos t = 0 := by
  simp [integral_sin_mul_cos₁]

/-- Fubini on the period cell for a product of functions of `x₀` and `x₁`. -/
lemma setIntegral_periodCube_mul (f g : ℝ → ℝ) :
    ∫ x in periodCube 3, f (x 0) * g (x 1) =
      (∫ t in (0)..(2 * π), f t) * (∫ t in (0)..(2 * π), g t) * (2 * π) := by
  have := setIntegral_periodCube_prod (n := 3) ![f, g, fun _ => 1]
  simp [Fin.prod_univ_three] at this
  simpa using this

/-- The quartic term on Šverák's plane as a sum of products of functions of `x₀` and `x₁`. -/
lemma quartic_phi_eq (x : Fin 3 → ℝ) :
    (cos (x 0) ^ 2 + cos (x 1) ^ 2 + cos (x 0 + x 1) ^ 2) ^ 2 =
      8 * (cos (x 0) ^ 4 * cos (x 1) ^ 4) - 4 * (cos (x 0) ^ 4 * cos (x 1) ^ 2)
        - 4 * (cos (x 0) ^ 2 * cos (x 1) ^ 4) + 8 * (cos (x 0) ^ 2 * cos (x 1) ^ 2) + 1
        - 8 * ((sin (x 0) * cos (x 0) ^ 3) * (sin (x 1) * cos (x 1) ^ 3))
        - 4 * ((sin (x 0) * cos (x 0)) * (sin (x 1) * cos (x 1))) := by
  rw [cos_add]
  set c0 := cos (x 0); set c1 := cos (x 1); set s0 := sin (x 0); set s1 := sin (x 1)
  linear_combination
    (6 * c0 ^ 2 * c1 ^ 2 * s1 ^ 2 - c0 ^ 2 * s1 ^ 4 + 2 * c0 ^ 2 * s1 ^ 2
      - 4 * c0 * c1 * s0 * s1 ^ 3 + 2 * c1 ^ 2 * s1 ^ 2 + s0 ^ 2 * s1 ^ 4 + s1 ^ 4)
      * sin_sq_add_cos_sq (x 0)
    + (-7 * c0 ^ 4 * c1 ^ 2 + c0 ^ 4 * s1 ^ 2 - c0 ^ 4 + 4 * c0 ^ 3 * c1 * s0 * s1
      + 6 * c0 ^ 2 * c1 ^ 2 - 2 * c0 ^ 2 * s1 ^ 2 - 4 * c0 * c1 * s0 * s1 + c1 ^ 2 + s1 ^ 2 + 1)
      * sin_sq_add_cos_sq (x 1)

/-- `⨍_Y (cos² x₁ + cos² x₂ + cos² (x₁ + x₂))² = 21/8`. -/
lemma integral_quartic_phi :
    ∫ x in periodCube 3, (cos (x 0) ^ 2 + cos (x 1) ^ 2 + cos (x 0 + x 1) ^ 2) ^ 2
      = 21 / 8 * (2 * π) ^ 3 := by
  have hI : ∀ {g : (Fin 3 → ℝ) → ℝ}, Continuous g → IntegrableOn g (periodCube 3) :=
    integrableOn_periodCube
  simp_rw [quartic_phi_eq]
  rw [integral_sub, integral_sub, integral_add, integral_add, integral_sub, integral_sub]
  rotate_left
  all_goals first
    | exact (hI (by fun_prop))
    | skip
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, setIntegral_const,
    setIntegral_periodCube_mul (fun t => cos t ^ 4) (fun t => cos t ^ 4),
    setIntegral_periodCube_mul (fun t => cos t ^ 4) (fun t => cos t ^ 2),
    setIntegral_periodCube_mul (fun t => cos t ^ 2) (fun t => cos t ^ 4),
    setIntegral_periodCube_mul (fun t => cos t ^ 2) (fun t => cos t ^ 2),
    setIntegral_periodCube_mul (fun t => sin t * cos t ^ 3) (fun t => sin t * cos t ^ 3),
    setIntegral_periodCube_mul (fun t => sin t * cos t) (fun t => sin t * cos t),
    intervalIntegral_cos_pow_four_two_pi, intervalIntegral_cos_sq_two_pi,
    intervalIntegral_sin_mul_cos_pow_three_two_pi, intervalIntegral_sin_mul_cos_two_pi,
    Measure.real, volume_periodCube, ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul]
  ring

/-! ### Lemma 2.4: failure of quasiconvexity -/

/-- `fL` on the gradient of Šverák's test function `ε φ`. -/
lemma fL_grad_phi (ε : ℝ) (x : Fin 3 → ℝ) :
    fL (0 + grad (ε • phi) x) =
      -2 * ε ^ 2 * (cos (x 0) * cos (x 1))
        + ε ^ 3 * (cos (x 0) * cos (x 1) * -cos (x 0 + x 1))
        + 3 / 4 * ε ^ 4 * (cos (x 0) ^ 2 + cos (x 1) ^ 2 + cos (x 0 + x 1) ^ 2) ^ 2 := by
  rw [zero_add, grad_smul_phi]
  simp [fL, gL, qL, nL, vL, symPart, HL]
  ring

/-- **Lemma 2.4**: the periodic average of `fL (ε ∇φ)` is `-ε³/4 + 63 ε⁴/32`. -/
theorem average_fL_phi (ε : ℝ) :
    ((2 * π) ^ 3)⁻¹ * ∫ x in periodCube 3, fL (0 + grad (ε • phi) x) =
      -ε ^ 3 / 4 + 63 / 32 * ε ^ 4 := by
  have hI : ∀ {g : (Fin 3 → ℝ) → ℝ}, Continuous g → IntegrableOn g (periodCube 3) :=
    integrableOn_periodCube
  simp_rw [fL_grad_phi]
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_cos_cos, integral_rsu, integral_quartic_phi]
  rotate_left
  all_goals first
    | exact (hI (by fun_prop)).const_mul _
    | exact ((hI (by fun_prop)).const_mul _).add ((hI (by fun_prop)).const_mul _)
    | skip
  have hπ := Real.pi_pos
  field_simp
  ring

/-- **Lemma 2.4**: `fL` is not quasiconvex: the periodic average of `fL (ε ∇φ)` is negative for
`0 < ε < 8/63`; we take `ε = 1/16`. -/
theorem not_quasiconvex_fL : ¬ Quasiconvex fL := by
  intro hqc
  have h1 := hqc.le_average_periodic continuous_fL 0 (contDiff_phi.const_smul (1 / 16 : ℝ))
    (isPeriodic_smul_phi (1 / 16))
  have h2 := average_fL_phi (1 / 16)
  have hf0 : fL 0 = 0 := by simp [fL, gL, qL, nL, vL, symPart]
  change fL 0 ≤ ((2 * π) ^ 3)⁻¹ * ∫ x in periodCube 3, fL (0 + grad ((1 / 16 : ℝ) • phi) x)
    at h1
  rw [h2, hf0] at h1
  norm_num at h1

/-! ### Theorem 2.1 -/

/-- **Theorem 2.1.** The quartic polynomial `fL F = gL (sym F)` is invariant under the addition
of skew-symmetric matrices, rank-one convex, and not quasiconvex. -/
theorem linear_main :
    (∀ F A : Mat 3 3, A.transpose = -A → fL (F + A) = fL F) ∧ RankOneConvex fL ∧
      ¬ Quasiconvex fL :=
  ⟨fL_add_skew, rankOneConvex_fL, not_quasiconvex_fL⟩

end QcSOn
