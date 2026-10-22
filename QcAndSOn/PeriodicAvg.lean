/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import QcAndSOn.Defs

/-!
# Averages of periodic functions

For `h` continuous and `L`-periodic in each variable and `j ≥ 1`,
`∫_{[0,1)ⁿ} h(L j x) dx = L⁻ⁿ ∫_{[0,L)ⁿ} h` (`setIntegral_cell_one_scaled`).

Proof: `[0,ℓ)ⁿ` is a fundamental domain of the lattice `ℓ ℤⁿ` (`ZSpan`), so integrals of
`ℓ`-periodic functions over translates of `[0,ℓ)ⁿ` agree; then average the identity
`∫_{[0,1)ⁿ} g(x+a) dx = ∫_{[0,1)ⁿ} g` over `a ∈ [0,1/j)ⁿ` and use Fubini.
-/

open MeasureTheory Set Filter Topology
open scoped Pointwise

noncomputable section

namespace QcSOn

variable {n : ℕ}

/-- The half-open cell `[0, ℓ)ⁿ`. -/
def cell (n : ℕ) (ℓ : ℝ) : Set (Fin n → ℝ) := univ.pi fun _ => Ico 0 ℓ

/-- `h` is `ℓ`-periodic in each variable. -/
def IsPer {α : Type*} (ℓ : ℝ) (h : (Fin n → ℝ) → α) : Prop :=
  ∀ (x : Fin n → ℝ) (i : Fin n), h (x + ℓ • Pi.single i 1) = h x

lemma IsPer.nat_mul {α : Type*} {ℓ : ℝ} {h : (Fin n → ℝ) → α} (hp : IsPer ℓ h) (k : ℕ) :
    IsPer (k * ℓ) h := by
  intro x i
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, add_smul, ← add_assoc, hp, ih]

/-- The basis `ℓ eᵢ`. -/
def latBasis (n : ℕ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).map (LinearEquiv.smulOfNeZero ℝ (Fin n → ℝ) ℓ hℓ)

lemma latBasis_apply {ℓ : ℝ} (hℓ : ℓ ≠ 0) (i : Fin n) :
    latBasis n hℓ i = ℓ • Pi.single i 1 := by
  simp [latBasis]

lemma latBasis_repr {ℓ : ℝ} (hℓ : ℓ ≠ 0) (x : Fin n → ℝ) (i : Fin n) :
    (latBasis n hℓ).repr x i = ℓ⁻¹ * x i := by
  simp [latBasis, Units.smul_def]

lemma fundamentalDomain_latBasis {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ZSpan.fundamentalDomain (latBasis n hℓ.ne') = cell n ℓ := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, latBasis_repr, cell, Set.mem_pi, Set.mem_univ,
    forall_const, mem_Ico]
  refine forall_congr' fun i => ?_
  rw [← div_eq_inv_mul, le_div_iff₀ hℓ, div_lt_iff₀ hℓ, zero_mul, one_mul]

lemma IsPer.add_lattice {α : Type*} {ℓ : ℝ} (hℓ : ℓ ≠ 0) {h : (Fin n → ℝ) → α}
    (hp : IsPer ℓ h) {v : Fin n → ℝ} (hv : v ∈ Submodule.span ℤ (range (latBasis n hℓ)))
    (x : Fin n → ℝ) : h (v + x) = h x := by
  induction hv using Submodule.span_induction generalizing x with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    rw [latBasis_apply, add_comm]; exact hp x i
  | zero => simp
  | add u w _ _ hu hw => rw [add_assoc, hu, hw]
  | smul z v _ hv' =>
    induction z using Int.induction_on generalizing x with
    | zero => simp
    | succ k ih => rw [add_smul, one_smul, add_comm _ v, add_assoc, hv', ih]
    | pred k ih =>
      rw [← hv' ((-(k : ℤ) - 1) • v + x), ← add_assoc]
      convert ih x using 3
      rw [sub_smul, one_smul]; abel

/-- Integrals of periodic functions over translated cells agree. -/
lemma setIntegral_cell_add {ℓ : ℝ} (hℓ : 0 < ℓ) {h : (Fin n → ℝ) → ℝ} (hp : IsPer ℓ h)
    (a : Fin n → ℝ) : ∫ x in cell n ℓ, h (x + a) = ∫ x in cell n ℓ, h x := by
  have hD := ZSpan.isAddFundamentalDomain (latBasis n hℓ.ne') (volume : Measure (Fin n → ℝ))
  rw [fundamentalDomain_latBasis hℓ] at hD
  have : VAddInvariantMeasure (Submodule.span ℤ (range (latBasis n hℓ.ne'))) (Fin n → ℝ)
      volume := ⟨fun g s _ => measure_preimage_add volume (g : Fin n → ℝ) s⟩
  have hD' := hD.vadd_of_comm a
  have hf : ∀ (g : Submodule.span ℤ (range (latBasis n hℓ.ne'))) (x : Fin n → ℝ),
      h (g +ᵥ x) = h x := fun g x => hp.add_lattice hℓ.ne' g.2 x
  rw [← hD'.setIntegral_eq hD hf]
  simp_rw [add_comm _ a]
  rw [← (measurePreserving_add_left volume a).setIntegral_image_emb
    (measurableEmbedding_addLeft a)]
  rfl

lemma IsPer.exists_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {h : (Fin n → ℝ) → ℝ} (hp : IsPer ℓ h)
    (hc : Continuous h) : ∃ B, ∀ x, |h x| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => ℓ))
    |>.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨B, fun x => ?_⟩
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (latBasis n hℓ.ne') x
  rw [fundamentalDomain_latBasis hℓ] at hv
  rw [← hp.add_lattice hℓ.ne' v.2 x]
  have hmem : (v : Fin n → ℝ) + x ∈ Icc (0 : Fin n → ℝ) fun _ => ℓ :=
    ⟨fun i => (hv i (mem_univ i)).1, fun i => (hv i (mem_univ i)).2.le⟩
  simpa [Real.norm_eq_abs] using hB _ hmem

lemma measurableSet_cell (ℓ : ℝ) : MeasurableSet (cell n ℓ) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma volume_cell {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : volume (cell n ℓ) = ENNReal.ofReal (ℓ ^ n) := by
  rw [cell, Real.volume_pi_Ico (a := fun _ => 0) (b := fun _ => ℓ)]
  simp [ENNReal.ofReal_pow hℓ]

lemma measureReal_cell {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : volume.real (cell n ℓ) = ℓ ^ n := by
  rw [measureReal_def, volume_cell hℓ, ENNReal.toReal_ofReal (by positivity)]

/-- **Averages of periodic functions**: `∫_{[0,1)ⁿ} h(L j x) dx = L⁻ⁿ ∫_{[0,L)ⁿ} h`. -/
theorem setIntegral_cell_one_scaled {L : ℝ} (hL : 0 < L) {h : (Fin n → ℝ) → ℝ} (hp : IsPer L h)
    (hc : Continuous h) {j : ℕ} (hj : 0 < j) :
    ∫ x in cell n 1, h ((L * j) • x) = (L ^ n)⁻¹ * ∫ x in cell n L, h x := by
  set g : (Fin n → ℝ) → ℝ := fun x => h ((L * j) • x)
  have hjR : (0 : ℝ) < j := Nat.cast_pos.2 hj
  have hgj : IsPer (j : ℝ)⁻¹ g := fun x i => by
    simp only [g, smul_add, smul_smul]
    rw [show L * j * (j : ℝ)⁻¹ = L by field_simp]
    exact hp _ i
  have hg1 : IsPer 1 g := by simpa [mul_inv_cancel₀ hjR.ne'] using hgj.nat_mul j
  have hgc : Continuous g := hc.comp (continuous_const_smul _)
  obtain ⟨B, hB⟩ := hgj.exists_bound (inv_pos.2 hjR) hgc
  set s1 := cell n 1
  set sj := cell n (j : ℝ)⁻¹
  have : IsFiniteMeasure (volume.restrict sj) :=
    isFiniteMeasure_restrict.2 (by rw [volume_cell (by positivity)]; simp)
  have : IsFiniteMeasure (volume.restrict s1) :=
    isFiniteMeasure_restrict.2 (by rw [volume_cell zero_le_one]; simp)
  -- average the translation identity over `a ∈ sj`
  have e1 : ∫ a in sj, ∫ x in s1, g (x + a) = (j : ℝ)⁻¹ ^ n * ∫ x in s1, g x := by
    have : ∀ a, ∫ x in s1, g (x + a) = ∫ x in s1, g x := fun a => setIntegral_cell_add one_pos hg1 a
    simp_rw [this]
    rw [setIntegral_const, smul_eq_mul, measureReal_cell (by positivity)]
  have hint : Integrable (Function.uncurry fun a x => g (x + a))
      ((volume.restrict sj).prod (volume.restrict s1)) := by
    refine Integrable.of_bound ?_ B (Eventually.of_forall fun p => ?_)
    · exact (hgc.comp (continuous_snd.add continuous_fst)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hB _
  have e2 : ∫ x in s1, ∫ a in sj, g (x + a) = ∫ a in sj, g a := by
    have : ∀ x, ∫ a in sj, g (x + a) = ∫ a in sj, g a := fun x => by
      simp_rw [add_comm x]; exact setIntegral_cell_add (inv_pos.2 hjR) hgj x
    simp_rw [this]
    rw [setIntegral_const, smul_eq_mul, measureReal_cell zero_le_one, one_pow, one_mul]
  have e3 : (j : ℝ)⁻¹ ^ n * ∫ x in s1, g x = ∫ a in sj, g a := by
    rw [← e1, integral_integral_swap hint, e2]
  -- scaling
  have e4 : ∫ a in sj, g a = (((L * j) ^ n)⁻¹) * ∫ x in cell n L, h x := by
    have hmem : ∀ x : Fin n → ℝ, x ∈ sj ↔ (L * j) • x ∈ cell n L := fun x => by
      simp only [sj, cell, Set.mem_pi, Set.mem_univ, forall_const, mem_Ico, Pi.smul_apply,
        smul_eq_mul]
      refine forall_congr' fun i => ?_
      have hLj : 0 < L * j := by positivity
      have e : (j : ℝ)⁻¹ = L / (L * j) := by field_simp
      rw [mul_nonneg_iff_of_pos_left hLj, e, lt_div_iff₀' hLj]
    rw [← integral_indicator (measurableSet_cell _), ← integral_indicator (measurableSet_cell _)]
    have : (sj.indicator g) = fun x => (cell n L).indicator h ((L * j) • x) := by
      ext x
      by_cases hx : x ∈ sj
      · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).1 hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (mt (hmem x).2 hx)]
    rw [this, Measure.integral_comp_smul, Module.finrank_fin_fun, smul_eq_mul,
      abs_of_pos (by positivity)]
  rw [e4] at e3
  have hjn : ((j : ℝ)⁻¹ ^ n) ≠ 0 := by positivity
  calc ∫ x in s1, g x = ((j : ℝ)⁻¹ ^ n)⁻¹ * ((j : ℝ)⁻¹ ^ n * ∫ x in s1, g x) := by
        field_simp
    _ = (L ^ n)⁻¹ * ∫ x in cell n L, h x := by
        rw [e3, mul_pow]; field_simp
        rw [div_pow, one_pow, div_mul_cancel₀ _ (by positivity), one_mul]

end QcSOn
