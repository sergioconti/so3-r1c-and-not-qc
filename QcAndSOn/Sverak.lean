/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import QcAndSOn.Periodic
import QcAndSOn.LocalFunction

/-!
# Failure of quasiconvexity at the identity (Section 5)

* `W0_L`: Lemma 3.2, the expansion of `W₀(Id + εH)` for `H` in Šverák's plane `L`;
* `grad_smul_phi`: `∇(εφ) = ε HL`, with `HL x ∈ L`;
* `average_W0_phi_neg`: Proposition 5.1;
* `not_quasiconvex_of_eventuallyEq`: a continuous function which coincides with `W₀` near `Id`
  is not quasiconvex (the remark after Proposition 5.1; uses Lemma 1.2).
-/

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace QcSOn

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Lemma 3.2 -/

/-- The quartic-and-higher remainder `p(ε, r, s, u)` in Lemma 3.2. -/
def PL (ε r s u : ℝ) : ℝ :=
  (3 * r ^ 4 + 3 * s ^ 4 + 5 * u ^ 4 / 2 + r * s ^ 3 + r * u ^ 3 / 2 + 13 * r ^ 2 * s ^ 2 / 2
    + 13 * r ^ 2 * u ^ 2 / 2 + r ^ 3 * s + s * u ^ 3 / 2 + 13 * s ^ 2 * u ^ 2 / 2
    + 2 * r * s * u ^ 2 + r * s ^ 2 * u / 2 + r ^ 2 * s * u / 2)
  + ε * (6 * r ^ 5 + 6 * s ^ 5 + u ^ 5 / 4 + r * s ^ 4 / 4 + 27 * r * u ^ 4 / 4
    + 13 * r ^ 2 * s ^ 3 / 2 + r ^ 2 * u ^ 3 / 4 + 13 * r ^ 3 * s ^ 2 / 2 + 25 * r ^ 3 * u ^ 2 / 2
    + r ^ 4 * s / 4 + 27 * s * u ^ 4 / 4 + s ^ 2 * u ^ 3 / 4 + 25 * s ^ 3 * u ^ 2 / 2
    + 7 * r * s ^ 2 * u ^ 2 + 7 * r ^ 2 * s * u ^ 2 + r ^ 2 * s ^ 2 * u / 4)
  + ε^2 * (9 * r ^ 6 / 2 + 9 * s ^ 6 / 2 + 25 * u ^ 6 / 4 + 13 * r ^ 2 * s ^ 4 / 8
    + 99 * r ^ 2 * u ^ 4 / 8 + 6 * r ^ 3 * s ^ 3 + 13 * r ^ 4 * s ^ 2 / 8 + 85 * r ^ 4 * u ^ 2 / 8
    + 99 * s ^ 2 * u ^ 4 / 8 + 85 * s ^ 4 * u ^ 2 / 8 + 6 * r * s * u ^ 4 + 6 * r * s ^ 3 * u ^ 2
    + 13 * r ^ 2 * s ^ 2 * u ^ 2 / 2 + 6 * r ^ 3 * s * u ^ 2)
  + ε^3 * (3 * r ^ 7 / 2 + 3 * s ^ 7 / 2 + 6 * r * u ^ 6 + 3 * r ^ 3 * s ^ 4 / 2 + 9 * r ^ 3 * u ^ 4
    + 3 * r ^ 4 * s ^ 3 / 2 + 9 * r ^ 5 * u ^ 2 / 2 + 6 * s * u ^ 6 + 9 * s ^ 3 * u ^ 4
    + 9 * s ^ 5 * u ^ 2 / 2 + 3 * r * s ^ 2 * u ^ 4 + 3 * r * s ^ 4 * u ^ 2 / 2
    + 3 * r ^ 2 * s * u ^ 4 + 3 * r ^ 2 * s ^ 3 * u ^ 2 + 3 * r ^ 3 * s ^ 2 * u ^ 2
    + 3 * r ^ 4 * s * u ^ 2 / 2)
  + ε^4 * (3 * r ^ 8 / 16 + 3 * s ^ 8 / 16 + 3 * u ^ 8 + 3 * r ^ 2 * u ^ 6 + 3 * r ^ 4 * s ^ 4 / 8
    + 9 * r ^ 4 * u ^ 4 / 4 + 3 * r ^ 6 * u ^ 2 / 4 + 3 * s ^ 2 * u ^ 6 + 9 * s ^ 4 * u ^ 4 / 4
    + 3 * s ^ 6 * u ^ 2 / 4 + 3 * r ^ 2 * s ^ 2 * u ^ 4 / 2 + 3 * r ^ 2 * s ^ 4 * u ^ 2 / 4
    + 3 * r ^ 4 * s ^ 2 * u ^ 2 / 4)

/-- **Lemma 3.2** (expansion on Šverák's plane `L`). -/
lemma W0_L (ε r s u : ℝ) :
    W0 (1 + ε • !![r, 0, 0; 0, s, 0; u, u, 0]) =
      -2 * ε ^ 2 * r * s + ε ^ 3 * r * s * u + ε ^ 4 * PL ε r s u := by
  simp [W0, g, strain, PL, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
  ring

lemma continuous_PL : Continuous fun p : ℝ × ℝ × ℝ × ℝ => PL p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  unfold PL; fun_prop

/-- Šverák's test function `φ(x) = (sin x₁, sin x₂, -sin(x₁ + x₂))`. -/
def phi (x : Fin 3 → ℝ) : Fin 3 → ℝ := ![sin (x 0), sin (x 1), -sin (x 0 + x 1)]

lemma contDiff_phi : ContDiff ℝ ∞ phi := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact (show ContDiff ℝ ∞ fun x : Fin 3 → ℝ => sin (x 0) by fun_prop)
  · exact (show ContDiff ℝ ∞ fun x : Fin 3 → ℝ => sin (x 1) by fun_prop)
  · exact (show ContDiff ℝ ∞ fun x : Fin 3 → ℝ => -sin (x 0 + x 1) by fun_prop)

lemma isPeriodic_smul_phi (ε : ℝ) : IsPeriodic (ε • phi) := by
  intro x j
  ext i
  fin_cases j <;> fin_cases i <;>
    simp [phi, ← add_assoc, add_right_comm _ (2 * π)]

/-! ### The gradient of `φ` -/

/-- Entries of the Jacobian as directional derivatives. -/
lemma grad_apply_eq_deriv {m n : ℕ} {ψ : (Fin n → ℝ) → (Fin m → ℝ)} {x : Fin n → ℝ}
    (hψ : DifferentiableAt ℝ ψ x) (i : Fin m) (j : Fin n) :
    grad ψ x i j = deriv (fun t : ℝ => ψ (x + t • Pi.single j 1) i) 0 := by
  have hline :
      HasDerivAt (fun t : ℝ => x + t • (Pi.single j 1 : Fin n → ℝ)) (Pi.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (Pi.single j 1 : Fin n → ℝ)).const_add x
  have hψ' : DifferentiableAt ℝ ψ (x + (0:ℝ) • (Pi.single j 1 : Fin n → ℝ)) := by simpa using hψ
  have h := (hasDerivAt_pi.1 (hψ'.hasFDerivAt.comp_hasDerivAt (0:ℝ) hline) i).deriv
  simp only [Function.comp_def] at h
  rw [h]
  simp [grad]

lemma deriv_sin_affine (g : ℝ → ℝ) (hg : ∀ t, g t = g 0 + t) :
    deriv (fun t => sin (g t)) 0 = cos (g 0) := by
  have : (fun t => sin (g t)) = fun t => sin (g 0 + t) := funext fun t => by rw [← hg]
  rw [this]
  simpa using (((hasDerivAt_id (0:ℝ)).const_add (g 0)).sin).deriv

lemma deriv_sin_add (a : ℝ) : deriv (fun t => sin (a + t)) 0 = cos a := by
  simpa using deriv_sin_affine (fun t => a + t) fun t => by ring

lemma deriv_sin_add_add (a b : ℝ) : deriv (fun t => sin (a + t + b)) 0 = cos (a + b) := by
  simpa using deriv_sin_affine (fun t => a + t + b) fun t => by ring

lemma deriv_sin_add_add' (a b : ℝ) : deriv (fun t => sin (a + (b + t))) 0 = cos (a + b) := by
  simpa using deriv_sin_affine (fun t => a + (b + t)) fun t => by ring

/-- The gradient of `φ`: it lies in Šverák's plane `L`. -/
def HL (x : Fin 3 → ℝ) : Mat 3 3 :=
  !![cos (x 0), 0, 0; 0, cos (x 1), 0; -cos (x 0 + x 1), -cos (x 0 + x 1), 0]

lemma grad_smul_phi (ε : ℝ) (x : Fin 3 → ℝ) : grad (ε • phi) x = ε • HL x := by
  have hd : DifferentiableAt ℝ (ε • phi) x :=
    ((contDiff_phi.const_smul ε).differentiable (by simp)) x
  ext i j
  rw [grad_apply_eq_deriv hd]
  fin_cases i <;> fin_cases j <;>
    simp [phi, HL, deriv_sin_add, deriv_sin_add_add, deriv_sin_add_add']

lemma norm_HL_le (x : Fin 3 → ℝ) : ‖HL x‖ ≤ 1 := by
  rw [Matrix.norm_le_iff zero_le_one]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [HL, abs_cos_le_one]

/-! ### Integrals over the period cell -/

lemma measurableSet_periodCube (n : ℕ) : MeasurableSet (periodCube n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

lemma volume_periodCube (n : ℕ) : volume (periodCube n) = ENNReal.ofReal ((2 * π) ^ n) := by
  rw [periodCube, Real.volume_pi_Ioo]
  simp [ENNReal.ofReal_pow, Real.pi_pos.le]

lemma integrableOn_periodCube {n : ℕ} {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) :
    IntegrableOn g (periodCube n) :=
  (hg.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    (pi_mono fun _ _ => Ioo_subset_Icc_self)

/-- Fubini on the period cell for functions of product form. -/
lemma setIntegral_periodCube_prod {n : ℕ} (f : Fin n → ℝ → ℝ) :
    ∫ x in periodCube n, ∏ i, f i (x i) = ∏ i, ∫ t in (0)..(2 * π), f i t := by
  rw [periodCube, volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo]

lemma integral_cos_x0 : ∫ x in periodCube 3, cos (x 0) = 0 := by
  have := setIntegral_periodCube_prod (n := 3) ![cos, fun _ => 1, fun _ => 1]
  simp [Fin.prod_univ_three] at this
  simpa using this

lemma integral_cos_x1 : ∫ x in periodCube 3, cos (x 1) = 0 := by
  have := setIntegral_periodCube_prod (n := 3) ![fun _ => 1, cos, fun _ => 1]
  simp [Fin.prod_univ_three] at this
  simpa using this

lemma integral_cos_cos : ∫ x in periodCube 3, cos (x 0) * cos (x 1) = 0 := by
  have := setIntegral_periodCube_prod (n := 3) ![cos, cos, fun _ => 1]
  simp [Fin.prod_univ_three] at this
  simpa using this

lemma integral_rsu :
    ∫ x in periodCube 3, cos (x 0) * cos (x 1) * -cos (x 0 + x 1) = -(2 * π ^ 3) := by
  have h1 : ∫ x in periodCube 3, cos (x 0) ^ 2 * cos (x 1) ^ 2 = 2 * π ^ 3 := by
    convert setIntegral_periodCube_prod (n := 3)
      ![fun t => cos t ^ 2, fun t => cos t ^ 2, fun _ => 1] using 1
    · simp [Fin.prod_univ_three]
    · simp [Fin.prod_univ_three, integral_cos_sq]; ring
  have h2 : ∫ x in periodCube 3, sin (x 0) * cos (x 0) * (sin (x 1) * cos (x 1)) = 0 := by
    convert setIntegral_periodCube_prod (n := 3)
      ![fun t => sin t * cos t, fun t => sin t * cos t, fun _ => 1] using 1
    · simp [Fin.prod_univ_three]
    · simp [Fin.prod_univ_three, integral_sin_mul_cos₁]
  have e : ∀ x : Fin 3 → ℝ, cos (x 0) * cos (x 1) * -cos (x 0 + x 1) =
      -(cos (x 0) ^ 2 * cos (x 1) ^ 2) + sin (x 0) * cos (x 0) * (sin (x 1) * cos (x 1)) := by
    intro x; rw [cos_add]; ring
  simp_rw [e]
  rw [integral_add, integral_neg, h1, h2]
  · ring
  · exact (integrableOn_periodCube (by fun_prop)).neg
  · exact integrableOn_periodCube (by fun_prop)

/-! ### Proposition 5.1 -/

/-- **Proposition 5.1.** For every neighbourhood `V` of `Id` there is `ε > 0` such that
`Id + ε ∇φ` takes values in `V` and `∫_{(0,2π)³} W₀ (Id + ε ∇φ) < 0`
(the average is `-ε³/4 + O(ε⁴)`). -/
theorem average_W0_phi_neg (V : Set (Mat 3 3)) (hV : V ∈ 𝓝 (1 : Mat 3 3)) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ x, 1 + grad (ε • phi) x ∈ V) ∧
      ∫ x in periodCube 3, W0 (1 + grad (ε • phi) x) < 0 := by
  -- uniform bound on the remainder `PL`
  obtain ⟨M, hM⟩ : ∃ M, ∀ ε r s u : ℝ, |ε| ≤ 1 → |r| ≤ 1 → |s| ≤ 1 → |u| ≤ 1 →
      |PL ε r s u| ≤ M := by
    have hK : IsCompact
        (Icc (-1 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))) :=
      isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_PL.continuousOn
    exact ⟨M, fun ε r s u hε hr hs hu =>
      hM (ε, r, s, u) ⟨abs_le.1 hε, abs_le.1 hr, abs_le.1 hs, abs_le.1 hu⟩⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 0 0 (by simp) (by simp) (by simp) (by simp))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hπ := Real.pi_pos
  set c := M * (2 * π) ^ 3 + 1 with hc
  have hc0 : 0 < c := by positivity
  set ε := min (1 / 2) (min (δ / 2) (π ^ 3 / c)) with hεdef
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hεδ : ε < δ := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hεc : ε * c ≤ π ^ 3 := by
    have : ε ≤ π ^ 3 / c := (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ hc0] at this
  refine ⟨ε, hε0, fun x => hball ?_, ?_⟩
  · -- `Id + ε ∇φ` stays in the ball
    rw [Metric.mem_ball, dist_eq_norm, grad_smul_phi, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hε0]
    calc ε * ‖HL x‖ ≤ ε * 1 := by gcongr; exact norm_HL_le x
      _ < δ := by linarith
  · -- the integral is `-2 π³ ε³ + ε⁴ J` with `|J| ≤ M (2π)³`
    set P : (Fin 3 → ℝ) → ℝ := fun x => PL ε (cos (x 0)) (cos (x 1)) (-cos (x 0 + x 1))
    have hP : Continuous P := continuous_PL.comp
      (f := fun x : Fin 3 → ℝ => (ε, cos (x 0), cos (x 1), -cos (x 0 + x 1))) (by fun_prop)
    have hint : ∀ x, W0 (1 + grad (ε • phi) x) =
        (-2 * ε ^ 2) * (cos (x 0) * cos (x 1))
        + ε ^ 3 * (cos (x 0) * cos (x 1) * -cos (x 0 + x 1)) + ε ^ 4 * P x := by
      intro x; rw [grad_smul_phi, HL, W0_L]; ring
    have hI : ∀ {g : (Fin 3 → ℝ) → ℝ}, Continuous g → IntegrableOn g (periodCube 3) :=
      integrableOn_periodCube
    simp_rw [hint]
    rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_cos_cos, integral_rsu]
    rotate_left
    all_goals first
      | exact (hI (by fun_prop)).const_mul _
      | exact ((hI (by fun_prop)).const_mul _).add ((hI (by fun_prop)).const_mul _)
      | exact (hI hP).const_mul _
      | skip
    have hJ : |∫ x in periodCube 3, P x| ≤ M * (2 * π) ^ 3 := by
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := P) (C := M)
        (by rw [volume_periodCube]; exact ENNReal.ofReal_lt_top) fun x _ =>
          hM _ _ _ _ (by rw [abs_of_pos hε0]; linarith) (abs_cos_le_one _) (abs_cos_le_one _)
            (by rw [abs_neg]; exact abs_cos_le_one _)
      rwa [Measure.real, volume_periodCube, ENNReal.toReal_ofReal (by positivity),
        Real.norm_eq_abs] at this
    have h1 : ε * (∫ x in periodCube 3, P x) ≤ ε * (M * (2 * π) ^ 3) :=
      mul_le_mul_of_nonneg_left (le_of_abs_le hJ) hε0.le
    have h2 : ε * (M * (2 * π) ^ 3) < 2 * π ^ 3 := by nlinarith
    have h3 : 0 < ε ^ 3 := by positivity
    have h4 := mul_lt_mul_of_pos_left (h1.trans_lt h2) h3
    nlinarith

/-- Any continuous function which coincides with `W₀` near `Id` is not quasiconvex
(the remark after Proposition 5.1). -/
theorem not_quasiconvex_of_eventuallyEq {f : Mat 3 3 → ℝ} (hf : Continuous f)
    (hfW : ∀ᶠ F in 𝓝 (1 : Mat 3 3), f F = W0 F) : ¬ Quasiconvex f := by
  intro hqc
  obtain ⟨ε, -, hin, hneg⟩ := average_W0_phi_neg _ hfW
  have h1 := hqc.le_average_periodic (ψ := ε • phi) hf 1 (contDiff_phi.const_smul ε)
    (isPeriodic_smul_phi ε)
  have heq : ∫ x in periodCube 3, f (1 + grad (ε • phi) x) =
      ∫ x in periodCube 3, W0 (1 + grad (ε • phi) x) :=
    setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
      fun x _ => hin x
  rw [heq, show f 1 = W0 1 from hfW.self_of_nhds, W0_one] at h1
  have : 0 < ((2 * π) ^ 3)⁻¹ := by positivity
  nlinarith

end QcSOn
