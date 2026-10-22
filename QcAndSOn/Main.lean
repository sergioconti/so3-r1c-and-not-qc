/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import QcAndSOn.Sverak
import QcAndSOn.Global

/-!
# A frame-indifferent rank-one convex function which is not quasiconvex

Main theorem (Theorem 1.1 of the paper). The proof combines
* `gM_nonneg_near_SO` (Proposition 4.2, file `RankOne`),
* `exists_globalization` (Section 6, file `Global`),
* `not_quasiconvex_of_eventuallyEq` (Section 5, file `Sverak`), which uses
  `Quasiconvex.le_average_periodic` (Lemma 1.2, file `Periodic`).
-/

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace QcSOn

/-! ### Main theorem -/

/-- **Theorem 1.1.** There is a function `W : ℝ^{3×3} → ℝ` of class `C^∞` which is frame
indifferent and rank-one convex, but not quasiconvex. Moreover `W = W₀` in a neighbourhood of
`SO(3)`. (`C^∞` is stated for `X ↦ W (Matrix.of X)` on `Fin 3 → Fin 3 → ℝ`, since `Mat 3 3` carries
no norm instance; all norms on this finite-dimensional space are equivalent.) -/
theorem main :
    ∃ W : Mat 3 3 → ℝ, Continuous W ∧ ContDiff ℝ ∞ (fun X : Fin 3 → Fin 3 → ℝ => W (Matrix.of X)) ∧
      FrameIndifferent W ∧ RankOneConvex W ∧ ¬ Quasiconvex W ∧
      ∀ᶠ F in 𝓝ˢ (SO 3), W F = W0 F := by
  obtain ⟨U, hU, hSO, hpos⟩ := gM_nonneg_near_SO
  obtain ⟨W, hc, hc2, hfi, hrc, heq⟩ := exists_globalization U hU hSO hpos
  have h1 : (1 : Mat 3 3) ∈ SO 3 := (Matrix.specialOrthogonalGroup (Fin 3) ℝ).one_mem
  exact ⟨W, hc, hc2, hfi, hrc, not_quasiconvex_of_eventuallyEq hc (heq.filter_mono
    (nhds_le_nhdsSet h1)), heq⟩

end QcSOn
