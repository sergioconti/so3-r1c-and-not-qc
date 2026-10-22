/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import Mathlib

/-!
# Nonnegativity near a nondegenerate minimum

If `f (t • n) = t² Q n + t³ R t n` with `R` continuous and `Q n ≥ m |n|²` (`m > 0`), then `f ≥ 0`
in a neighbourhood of `0`. This is Lemma 4.1 of the paper.
-/

open Filter Topology Set

namespace QcSOn

/-- The unit sphere `{u : ∑ uᵢ² = 1}` is compact. -/
lemma isCompact_sumSq_eq_one (N : ℕ) : IsCompact {u : Fin N → ℝ | ∑ i, u i ^ 2 = 1} := by
  refine (isCompact_closedBall (0 : Fin N → ℝ) 1).of_isClosed_subset
    (isClosed_eq (by fun_prop) continuous_const) fun u hu => ?_
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have : u i ^ 2 ≤ 1 := hu ▸ Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)

theorem eventually_nonneg_of_expansion {N : ℕ} (f Q : (Fin N → ℝ) → ℝ)
    (R : ℝ → (Fin N → ℝ) → ℝ) (hR : Continuous fun p : ℝ × (Fin N → ℝ) => R p.1 p.2)
    {m : ℝ} (hm : 0 < m) (hQ : ∀ n, m * ∑ i, n i ^ 2 ≤ Q n)
    (hf : ∀ (t : ℝ) (n : Fin N → ℝ), f (t • n) = t ^ 2 * Q n + t ^ 3 * R t n) :
    ∀ᶠ n in 𝓝 0, 0 ≤ f n := by
  set S := {u : Fin N → ℝ | ∑ i, u i ^ 2 = 1}
  obtain ⟨C₀, hC₀⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod
    (isCompact_sumSq_eq_one N)).exists_bound_of_continuousOn hR.continuousOn
  set C := max C₀ 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ S, ‖R p.1 p.2‖ ≤ C := fun p hp =>
    (hC₀ p hp).trans (le_max_left _ _)
  set ρ : (Fin N → ℝ) → ℝ := fun n => √(∑ i, n i ^ 2)
  have hρ : Continuous ρ := by fun_prop
  have hρ0 : ρ 0 = 0 := by simp [ρ]
  set δ := min 1 (m / (C + 1))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  filter_upwards [(hρ.tendsto 0).eventually (gt_mem_nhds (hρ0 ▸ hδ))] with n hn
  have hsum : 0 ≤ ∑ i, n i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases h0 : ρ n = 0
  · have : ∑ i, n i ^ 2 = 0 := by simpa [ρ, Real.sqrt_eq_zero hsum] using h0
    have hn0 : n = 0 := funext fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (n j)).1 this i
        (Finset.mem_univ i)
      simpa using this
    subst hn0
    have := hf 0 0
    simp at this
    simp [this]
  · have hρpos : 0 < ρ n := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
    set u := (ρ n)⁻¹ • n
    have hnu : n = ρ n • u := by simp [u, smul_smul, mul_inv_cancel₀ h0]
    have hu : u ∈ S := by
      change ∑ i, u i ^ 2 = 1
      simp only [u, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      rw [inv_pow, Real.sq_sqrt hsum, inv_mul_cancel₀]
      intro h; exact h0 (by simp [ρ, h])
    have hδ1 : ρ n ≤ 1 := hn.le.trans (min_le_left _ _)
    have hδm : ρ n * (C + 1) ≤ m := by
      have := hn.le.trans (min_le_right _ _)
      rwa [le_div_iff₀ (by positivity)] at this
    have hRb : -C ≤ R (ρ n) u := by
      have := hC (ρ n, u) ⟨⟨by linarith, hδ1⟩, hu⟩
      rw [Real.norm_eq_abs] at this
      exact neg_le_of_abs_le this
    have hQu : m ≤ Q u := by simpa [show ∑ i, u i ^ 2 = 1 from hu] using hQ u
    rw [hnu, hf]
    have h3 : 0 ≤ ρ n ^ 2 * (m - ρ n * C) := by
      apply mul_nonneg (sq_nonneg _); nlinarith
    nlinarith [pow_pos hρpos 2, pow_pos hρpos 3]

end QcSOn
