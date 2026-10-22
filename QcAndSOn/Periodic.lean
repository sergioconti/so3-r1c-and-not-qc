/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import QcAndSOn.PeriodicAvg

/-!
# Periodic test functions (Lemma 1.2)

If `f` is continuous and quasiconvex, then `f F ≤ ⨍_{(0,2π)ⁿ} f (F + ∇ψ)` for every smooth
`(0,2π)ⁿ`-periodic `ψ`.

Proof (standard): test quasiconvexity with `u = χ_δ · ψ(L j x)/(L j)`, `L = 2π`, where `χ_δ` is a
smooth cutoff, `= 1` on `[δ, 1-δ]ⁿ` and supported in `(0,1)ⁿ`, and `j` is large depending on `δ`.
Then `∇u` is bounded independently of `δ, j`, and `∇u(x) = ∇ψ(L j x)` on `(δ, 1-δ)ⁿ`, so
`∫ f(F + ∇u) = ∫_{(0,1)ⁿ} f(F + ∇ψ(L j x)) dx + O(1 - (1-2δ)ⁿ)`, and the first term is the periodic
average (`setIntegral_cell_one_scaled`).
-/

open MeasureTheory Set Real Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace QcSOn

/-- The period cell `(0, 2π)ⁿ`. -/
def periodCube (n : ℕ) : Set (Fin n → ℝ) := univ.pi fun _ => Ioo 0 (2 * π)

/-- `ψ : ℝⁿ → ℝᵐ` is `2π`-periodic in each variable. -/
def IsPeriodic {m n : ℕ} (ψ : (Fin n → ℝ) → (Fin m → ℝ)) : Prop :=
  ∀ (x : Fin n → ℝ) (j : Fin n), ψ (x + (2 * π) • Pi.single j 1) = ψ x

lemma IsPer.fderiv {m n : ℕ} {ℓ : ℝ} {ψ : (Fin n → ℝ) → (Fin m → ℝ)} (hp : IsPer ℓ ψ) :
    IsPer ℓ (fderiv ℝ ψ) := fun x i => by
  have : (fun y => ψ (y + ℓ • Pi.single i 1)) = ψ := funext fun y => hp y i
  rw [← fderiv_comp_add_right, this]

lemma IsPer.isPer_grad {m n : ℕ} {ℓ : ℝ} {ψ : (Fin n → ℝ) → (Fin m → ℝ)} (hp : IsPer ℓ ψ) :
    IsPer ℓ (grad ψ) := fun x i => by
  simp only [QcSOn.grad, hp.fderiv x i]

lemma continuous_grad {m n : ℕ} {ψ : (Fin n → ℝ) → (Fin m → ℝ)} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (grad ψ) := by
  have hc := hψ.continuous_fderiv one_ne_zero
  exact continuous_matrix fun i j => (continuous_apply i).comp (hc.clm_apply continuous_const)

lemma abs_grad_le {m n : ℕ} (ψ : (Fin n → ℝ) → (Fin m → ℝ)) (x : Fin n → ℝ) (i : Fin m)
    (j : Fin n) : |grad ψ x i j| ≤ ‖fderiv ℝ ψ x‖ := by
  calc |grad ψ x i j| ≤ ‖fderiv ℝ ψ x (Pi.single j 1)‖ := by
        rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i
    _ ≤ ‖fderiv ℝ ψ x‖ * ‖(Pi.single j 1 : Fin n → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ ψ x‖ * 1 := by
        gcongr
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
        by_cases h : k = j <;> simp [h]
    _ = _ := mul_one _

/-- **Lemma 1.2** (periodic test functions). If `f` is continuous and quasiconvex and `ψ` is smooth
and `(0,2π)ⁿ`-periodic, then `f F ≤ ⨍_{(0,2π)ⁿ} f (F + ∇ψ)`. -/
theorem Quasiconvex.le_average_periodic {m n : ℕ} {f : Mat m n → ℝ} (hf : Continuous f)
    (hqc : Quasiconvex f) (F : Mat m n) {ψ : (Fin n → ℝ) → (Fin m → ℝ)} (hψ : ContDiff ℝ ∞ ψ)
    (hper : IsPeriodic ψ) :
    f F ≤ ((2 * π) ^ n)⁻¹ * ∫ x in periodCube n, f (F + grad ψ x) := by
  set L := 2 * π with hLdef
  have hL : 0 < L := by positivity
  have hL1 : 1 ≤ L := by linarith [Real.pi_gt_three]
  have hp : IsPer L ψ := hper
  set h : (Fin n → ℝ) → ℝ := fun y => f (F + grad ψ y)
  have hgc : Continuous (grad ψ) := continuous_grad (hψ.of_le (by norm_num))
  have hhc : Continuous h := hf.comp (continuous_const.add hgc)
  have hhp : IsPer L h := fun x i => by simp only [h, hp.isPer_grad x i]
  set A := (L ^ n)⁻¹ * ∫ x in periodCube n, h x
  -- bounds on `ψ` and `Dψ`
  obtain ⟨B0, hB0⟩ := IsPer.exists_bound hL (h := fun x => ‖ψ x‖)
    (fun x i => by simp only [hp x i]) (continuous_norm.comp hψ.continuous)
  obtain ⟨B1, hB1⟩ := IsPer.exists_bound hL (h := fun x => ‖fderiv ℝ ψ x‖)
    (fun x i => by simp only [hp.fderiv x i])
    (continuous_norm.comp (hψ.continuous_fderiv (by norm_num)))
  have hB0' : ∀ x, ‖ψ x‖ ≤ B0 := fun x => (le_abs_self _).trans (hB0 x)
  have hB1' : ∀ x, ‖fderiv ℝ ψ x‖ ≤ B1 := fun x => (le_abs_self _).trans (hB1 x)
  have hB00 : 0 ≤ B0 := (norm_nonneg _).trans (hB0' 0)
  set M := B1 + B0
  -- bound for `f` on a box around `F`
  set K : Set (Mat m n) := {G | ∀ i k, G i k ∈ Icc (F i k - M) (F i k + M)}
  have hK : IsCompact K := by
    have : K = Set.univ.pi fun i => Set.univ.pi fun k => Icc (F i k - M) (F i k + M) := by
      ext G
      exact ⟨fun hG i _ k _ => hG i k, fun hG i k => hG i (mem_univ _) k (mem_univ _)⟩
    rw [this]; exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hmemK : ∀ G : Mat m n, (∀ i k, |G i k| ≤ M) → F + G ∈ K := fun G hG i k => by
    have := abs_le.1 (hG i k)
    simp only [Matrix.add_apply, mem_Icc]; constructor <;> linarith
  have hfK : ∀ G : Mat m n, (∀ i k, |G i k| ≤ M) → |f (F + G)| ≤ B := fun G hG => by
    simpa [Real.norm_eq_abs] using hB _ (hmemK G hG)
  -- the unit cube
  have hU1 : volume (unitCube n) = 1 := by
    rw [unitCube, Real.volume_pi_Ioo (a := fun _ => 0) (b := fun _ => 1)]; simp
  have : IsFiniteMeasure (volume.restrict (unitCube n)) :=
    isFiniteMeasure_restrict.2 (by rw [hU1]; simp)
  have hUcell : unitCube n =ᵐ[volume] cell n 1 :=
    Measure.univ_pi_Ioo_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm
  have hPcell : periodCube n =ᵐ[volume] cell n L :=
    Measure.univ_pi_Ioo_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm
  -- key estimate for each `δ`
  have key : ∀ δ ∈ Ioo (0 : ℝ) (1 / 4), f F ≤ A + 2 * B * (1 - (1 - 2 * δ) ^ n) := by
    rintro δ ⟨hδ0, hδ1⟩
    set c : Fin n → ℝ := fun _ => 1 / 2
    let χ : ContDiffBump c := ⟨1 / 2 - δ, 1 / 2 - δ / 2, by linarith, by linarith⟩
    have hχc : ContDiff ℝ ∞ χ := χ.contDiff
    obtain ⟨Cχ, hCχ⟩ := (hχc.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
      (χ.hasCompactSupport.fderiv (𝕜 := ℝ))
    have hCχ0 : 0 ≤ Cχ := (norm_nonneg _).trans (hCχ 0)
    set j : ℕ := ⌈Cχ⌉₊ + 1
    have hj : 0 < j := Nat.succ_pos _
    have hjC : Cχ ≤ j := (Nat.le_ceil Cχ).trans (by exact_mod_cast Nat.le_succ _)
    set s := L * j
    have hs : 0 < s := by positivity
    have hsC : Cχ ≤ s := hjC.trans (le_mul_of_one_le_left (by positivity) hL1)
    set v : (Fin n → ℝ) → (Fin m → ℝ) := fun x => s⁻¹ • ψ (s • x)
    set u : (Fin n → ℝ) → (Fin m → ℝ) := fun x => χ x • v x
    have hψd : ∀ y, HasFDerivAt ψ (fderiv ℝ ψ y) y := fun y =>
      ((hψ.differentiable (by norm_num)) y).hasFDerivAt
    have hv : ∀ x, HasFDerivAt v (fderiv ℝ ψ (s • x)) x := fun x => by
      exact (((hψd (s • x)).comp x ((hasFDerivAt_id x).const_smul s)).const_smul s⁻¹).congr_fderiv
        (by ext1 e; simp [smul_smul, inv_mul_cancel₀ hs.ne'])
    have hu : ∀ x, HasFDerivAt u (χ x • fderiv ℝ ψ (s • x) + (fderiv ℝ χ x).smulRight (v x)) x :=
      fun x => ((hχc.differentiable (by norm_num) x).hasFDerivAt).smul (hv x)
    have hgu : ∀ x i k, grad u x i k =
        χ x * grad ψ (s • x) i k + fderiv ℝ χ x (Pi.single k 1) * v x i := fun x i k => by
      simp [QcSOn.grad, (hu x).fderiv]
    -- properties of `u`
    have hsub : closedBall c (1 / 2 - δ / 2) ⊆ unitCube n := fun x hx i _ => by
      have := (dist_pi_le_iff (by linarith)).1 hx i
      rw [Real.dist_eq] at this
      have := abs_le.1 this
      simp only [c] at this
      exact ⟨by linarith, by linarith⟩
    have hv_smooth : ContDiff ℝ ∞ v :=
      ContDiff.const_smul s⁻¹ (hψ.comp (ContDiff.const_smul s contDiff_id))
    have hu_smooth : ContDiff ℝ ∞ u := hχc.smul hv_smooth
    have hu_cs : HasCompactSupport u := χ.hasCompactSupport.smul_right
    have hu_supp : tsupport u ⊆ unitCube n :=
      (tsupport_smul_subset_left _ _).trans (by rw [χ.tsupport_eq]; exact hsub)
    -- `∇u = ∇ψ(s x)` on the inner cube
    set I := ball c (1 / 2 - δ)
    have hIU : I ⊆ unitCube n := (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith))).trans hsub
    have hinner : ∀ x ∈ I, grad u x = grad ψ (s • x) := fun x hx => by
      have h1 : χ x = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hx)
      have h2 : fderiv ℝ χ x = 0 := by
        have : (χ : (Fin n → ℝ) → ℝ) =ᶠ[𝓝 x] fun _ => 1 := by
          filter_upwards [isOpen_ball.mem_nhds hx] with y hy
          exact χ.one_of_mem_closedBall (ball_subset_closedBall hy)
        rw [this.fderiv_eq]; simp
      ext i k; rw [hgu, h1, h2]; simp
    -- uniform bounds
    have hgψ : ∀ y i k, |grad ψ y i k| ≤ B1 := fun y i k => (abs_grad_le ψ y i k).trans (hB1' y)
    have hgψM : ∀ y i k, |grad ψ y i k| ≤ M := fun y i k => (hgψ y i k).trans (by linarith)
    have hguM : ∀ x i k, |grad u x i k| ≤ M := fun x i k => by
      rw [hgu]
      have e1 : |χ x * grad ψ (s • x) i k| ≤ B1 := by
        rw [abs_mul, abs_of_nonneg (χ.nonneg)]
        calc χ x * |grad ψ (s • x) i k| ≤ 1 * B1 :=
              mul_le_mul χ.le_one (hgψ _ i k) (abs_nonneg _) zero_le_one
          _ = B1 := one_mul _
      have e2 : |fderiv ℝ χ x (Pi.single k 1) * v x i| ≤ B0 := by
        have hd : |fderiv ℝ χ x (Pi.single k 1)| ≤ Cχ := by
          rw [← Real.norm_eq_abs]
          refine ((fderiv ℝ χ x).le_opNorm _).trans ?_
          have : ‖(Pi.single k 1 : Fin n → ℝ)‖ ≤ 1 :=
            (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => by by_cases hl : l = k <;> simp [hl]
          calc ‖fderiv ℝ χ x‖ * ‖(Pi.single k 1 : Fin n → ℝ)‖ ≤ Cχ * 1 :=
                mul_le_mul (hCχ x) this (norm_nonneg _) hCχ0
            _ = Cχ := mul_one _
        have hvx : |v x i| ≤ s⁻¹ * B0 := by
          rw [← Real.norm_eq_abs]
          refine (norm_le_pi_norm (v x) i).trans ?_
          simp only [v, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs]
          exact mul_le_mul_of_nonneg_left (hB0' _) (by positivity)
        rw [abs_mul]
        calc |fderiv ℝ χ x (Pi.single k 1)| * |v x i| ≤ Cχ * (s⁻¹ * B0) :=
              mul_le_mul hd hvx (abs_nonneg _) hCχ0
          _ = (Cχ / s) * B0 := by ring
          _ ≤ 1 * B0 := mul_le_mul_of_nonneg_right ((div_le_one hs).2 hsC) hB00
          _ = B0 := one_mul _
      exact (abs_add_le _ _).trans (by linarith)
    -- integrals
    set g1 : (Fin n → ℝ) → ℝ := fun x => f (F + grad u x)
    set g0 : (Fin n → ℝ) → ℝ := fun x => h (s • x)
    have hgu_c : Continuous (grad u) := continuous_grad (hu_smooth.of_le (by norm_num))
    have hg1c : Continuous g1 := hf.comp (continuous_const.add hgu_c)
    have hg0c : Continuous g0 := hhc.comp (continuous_const_smul s)
    have hg1i : IntegrableOn g1 (unitCube n) :=
      Integrable.of_bound hg1c.aestronglyMeasurable B
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfK _ (hguM x))
    have hqcu := hqc F u hu_smooth hu_cs hu_supp hg1i
    have hg0i : IntegrableOn g0 (unitCube n) :=
      Integrable.of_bound hg0c.aestronglyMeasurable B
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfK _ (hgψM _))
    have hA : ∫ x in unitCube n, g0 x = A := by
      rw [setIntegral_congr_set hUcell, setIntegral_cell_one_scaled hL hhp hhc hj,
        ← setIntegral_congr_set hPcell]
    -- error term
    set E := fun x => g1 x - g0 x
    have hEi : IntegrableOn E (unitCube n) := hg1i.sub hg0i
    have hE0 : ∫ x in unitCube n ∩ I, E x = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun x hx => by
        simp only [E, g1, g0, h, hinner x hx.2, sub_self]
    have hvolI : volume.real I = (1 - 2 * δ) ^ n := by
      rw [measureReal_def, Real.volume_pi_ball c (by linarith), Fintype.card_fin,
        ENNReal.toReal_ofReal (by apply pow_nonneg; linarith)]
      ring_nf
    have hvolD : volume.real (unitCube n \ I) = 1 - (1 - 2 * δ) ^ n := by
      rw [measureReal_sdiff hIU isOpen_ball.measurableSet (by rw [hU1]; simp), measureReal_def,
        hU1, hvolI]
      simp
    have hEb : ‖∫ x in unitCube n \ I, E x‖ ≤ 2 * B * (1 - (1 - 2 * δ) ^ n) := by
      rw [← hvolD]
      refine norm_setIntegral_le_of_norm_le_const
        (measure_lt_top_of_subset sdiff_subset (by rw [hU1]; simp)) fun x _ => ?_
      rw [Real.norm_eq_abs]
      have := hfK _ (hguM x); have := hfK _ (hgψM (s • x))
      simp only [E, g1, g0, h]
      exact (abs_sub _ _).trans (by linarith)
    have hsplit : ∫ x in unitCube n, g1 x = A + ∫ x in unitCube n \ I, E x := by
      have h1 := integral_inter_add_sdiff (t := I) isOpen_ball.measurableSet hEi
      rw [hE0, zero_add] at h1
      have h2 := integral_sub hg1i hg0i
      simp only [E] at h1 ⊢
      linarith [hA]
    calc f F ≤ ∫ x in unitCube n, g1 x := hqcu
      _ = A + ∫ x in unitCube n \ I, E x := hsplit
      _ ≤ A + 2 * B * (1 - (1 - 2 * δ) ^ n) := by
        have := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hEb)
        linarith
  -- let `δ → 0`
  have hlim : Tendsto (fun δ : ℝ => A + 2 * B * (1 - (1 - 2 * δ) ^ n)) (𝓝[>] 0) (𝓝 A) := by
    have hc : Continuous fun δ : ℝ => A + 2 * B * (1 - (1 - 2 * δ) ^ n) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsGT (by norm_num)) key)

end QcSOn
