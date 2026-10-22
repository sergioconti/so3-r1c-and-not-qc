/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import Mathlib

/-!
# Basic definitions: quasiconvexity, rank-one convexity, frame indifference

Matrices are `Mat m n := Matrix (Fin m) (Fin n) ℝ`; maps `ψ : ℝⁿ → ℝᵐ` are modelled on
`Fin n → ℝ` (so that `volume` is the product Lebesgue measure and the unit cube has volume `1`).

* `QcSOn.grad ψ x`, the Jacobian matrix `(∂_j ψ_i (x))_{ij}`;
* `QcSOn.Quasiconvex f`: `f F ≤ ⨍_{(0,1)ⁿ} f (F + ∇ψ)` for all `F` and all
  `ψ ∈ C^∞_c((0,1)ⁿ; ℝᵐ)` with `f (F + ∇ψ)` integrable (eq. (1.1) of the paper);
* `QcSOn.RankOneConvex f`: `t ↦ f (F + t a ⊗ b)` is convex for all `F, a, b`;
* `QcSOn.FrameIndifferent f`: `f (Q F) = f F` for all `Q ∈ SO(n)` (eq. (1.2)).
-/

open MeasureTheory Set
open scoped ContDiff

noncomputable section

namespace QcSOn

/-- Real `m × n` matrices. -/
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- `SO(n)` as a set of matrices. -/
abbrev SO (n : ℕ) : Set (Mat n n) := Matrix.specialOrthogonalGroup (Fin n) ℝ

/-- The Jacobian matrix of `ψ : ℝⁿ → ℝᵐ` at `x`: `grad ψ x i j = ∂_j ψ_i (x)`. -/
def grad {m n : ℕ} (ψ : (Fin n → ℝ) → (Fin m → ℝ)) (x : Fin n → ℝ) : Mat m n :=
  Matrix.of fun i j => fderiv ℝ ψ x (Pi.single j 1) i

/-- The open unit cube `(0,1)ⁿ`. -/
def unitCube (n : ℕ) : Set (Fin n → ℝ) := univ.pi fun _ => Ioo 0 1

/-- **Quasiconvexity** (Morrey): for every `F` and every smooth `ψ` with compact support in the
open unit cube such that `f (F + ∇ψ)` is integrable on the cube,
`f F ≤ ∫_{(0,1)ⁿ} f (F + ∇ψ)` (the cube has volume one, so this is the average). The
integrability assumption makes the definition independent of Mathlib's convention that the integral
of a non-integrable function is `0`. -/
def Quasiconvex {m n : ℕ} (f : Mat m n → ℝ) : Prop :=
  ∀ (F : Mat m n) (ψ : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ unitCube n → IntegrableOn (fun x => f (F + grad ψ x)) (unitCube n) →
    f F ≤ ∫ x in unitCube n, f (F + grad ψ x)

/-- **Rank-one convexity**: `f` is convex along every rank-one line `t ↦ F + t a ⊗ b`. -/
def RankOneConvex {m n : ℕ} (f : Mat m n → ℝ) : Prop :=
  ∀ (F : Mat m n) (a : Fin m → ℝ) (b : Fin n → ℝ),
    ConvexOn ℝ univ fun t : ℝ => f (F + t • Matrix.vecMulVec a b)

/-- **Frame indifference**: `f (Q F) = f F` for every rotation `Q`. -/
def FrameIndifferent {n : ℕ} (f : Mat n n → ℝ) : Prop :=
  ∀ Q ∈ SO n, ∀ F : Mat n n, f (Q * F) = f F

lemma FrameIndifferent.add {n : ℕ} {f g : Mat n n → ℝ} (hf : FrameIndifferent f)
    (hg : FrameIndifferent g) : FrameIndifferent (f + g) := fun Q hQ F => by
  simp [hf Q hQ F, hg Q hQ F]

end QcSOn
