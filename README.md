# A frame-indifferent rank-one convex function which is not quasiconvex

This repository contains a Lean 4 / Mathlib formalization of the main results of the paper

> S. Conti, G. Dolzmann, P. Dondl, *A frame-indifferent rank-one convex function in three
> dimensions which is not quasiconvex*, which will appear in arXiv and/or cvgmt.org soon. The precise reference will be inserted in a revised version of this file.

The main result (Theorem 1.1 of the paper) is:

> There is a function `W : ℝ^{3×3} → ℝ` of class `C^∞` which is frame indifferent
> (`W(QF) = W(F)` for all `Q ∈ SO(3)`), rank-one convex, but not quasiconvex.
> Moreover `W` coincides near `SO(3)` with the explicit polynomial `W₀(F) = g(½(FᵀF - Id))`,
> where `g` is an explicit quartic polynomial on symmetric matrices.

The formal proof is complete: it contains no `sorry` and uses only the three standard axioms of
Lean/Mathlib (`propext`, `Classical.choice`, `Quot.sound`).

## What exactly is proved

The statement is in [`QcAndSOn/Statement.lean`](QcAndSOn/Statement.lean). This file imports
only Mathlib and is meant to be read by a human. It defines

* `SO3`: the rotation group, i.e. Mathlib's `Matrix.specialOrthogonalGroup (Fin 3) ℝ`;
* `grad φ x`: the gradient matrix `(∂ⱼ φᵢ(x))ᵢⱼ` of `φ : ℝ³ → ℝ³`;
* `Quasiconvex W`: `W F ≤ ∫_{(0,1)³} W (F + ∇φ)` for every matrix `F` and every smooth `φ`
  with compact support in the open unit cube such that `W (F + ∇φ)` is integrable on the cube
  (Morrey's definition). For continuous `W` the integrability assumption is always satisfied;
  it ensures that `¬ Quasiconvex W` does not rely on Mathlib's convention that the integral of a
  non-integrable function is `0`;
* `RankOneConvex W`: `t ↦ W (F + t a ⊗ b)` is convex on `ℝ` for all `F`, `a`, `b`;
* `FrameIndifferent W`: `W (Q F) = W F` for all `Q ∈ SO(3)`;

and the proposition

```lean
def Statement : Prop :=
  ∃ W : M3 → ℝ, ContDiff ℝ ∞ (fun X : Fin 3 → Fin 3 → ℝ => W (Matrix.of X)) ∧
    FrameIndifferent W ∧ RankOneConvex W ∧ ¬ Quasiconvex W
```

(`C^∞` is stated in terms of the nine matrix entries, since Mathlib puts no norm on `Matrix`.)
The internal theorem `QcSOn.main` additionally shows that `W` coincides with the explicit
polynomial `W₀(F) = g(½ (Fᵀ F - Id))` of eq. (3.2) in a neighbourhood of `SO(3)`.

The theorem `MainResult.statement_holds : MainResult.Statement` is proved in
[`QcAndSOn/Proof.lean`](QcAndSOn/Proof.lean), which imports the statement and the rest of the
development.

`Statement.lean` also contains a second statement, for the geometrically linear example of
Section 2 of the paper (Theorem 2.1):

```lean
def LinearStatement : Prop :=
  ∃ f : M3 → ℝ, ContDiff ℝ ∞ (fun X : Fin 3 → Fin 3 → ℝ => f (Matrix.of X)) ∧
    (∀ F A : M3, Aᵀ = -A → f (F + A) = f F) ∧ RankOneConvex f ∧ ¬ Quasiconvex f
```

It is proved as `MainResult.linearStatement_holds` in `Proof.lean`, with the explicit quartic
polynomial `QcSOn.fL F = g_lin(½ (F + Fᵀ))` of eq. (2.3) (`QcAndSOn/Linear.lean`).

## Building and checking

### Requirements

* [elan](https://github.com/leanprover/elan) (the Lean version manager). The Lean version
  (`v4.34.1`) is pinned in `lean-toolchain` and is installed automatically.
* `git` and `curl`, and about 5 GB of free disk space for Mathlib.

### Build

```sh
git clone https://github.com/sergioconti/so3-r1c-and-not-qc.git
cd so3-r1c-and-not-qc
lake exe cache get     # download precompiled Mathlib (strongly recommended)
lake build
```

With the Mathlib cache, `lake build` takes about five minutes (mostly for the file
`Charts.lean`). Without the cache, Mathlib itself is
compiled first, which takes much longer.

### Check

1. **Read the statement.** Check that the definitions in `QcAndSOn/Statement.lean` are the
   intended mathematical notions. This is the only file whose content one has to trust.
2. **Build.** `lake build` must finish with `Build completed successfully`. The build prints
   ```
   info: QcAndSOn/Proof.lean:…: 'MainResult.statement_holds' depends on axioms:
     [propext, Classical.choice, Quot.sound]
   ```
   (and the same line for `MainResult.linearStatement_holds`), which shows that no `sorry` (it would appear as `sorryAx`) and no additional axioms are used.
   The same check can be done by hand with
   ```sh
   lake env lean QcAndSOn/Proof.lean
   ```
3. **Optional:** `grep -rn "sorry\|axiom" QcAndSOn/` finds only the `#print axioms` commands in
   `Proof.lean` and the comments next to them.

## Structure of the proof

Numbers of sections, equations and lemmas refer to the arXiv version of the paper.

| File | Content (paper section) |
| --- | --- |
| `Statement.lean` | Mathlib-only statement of the main result |
| `Proof.lean` | Derives `MainResult.Statement` from `QcSOn.main` and `MainResult.LinearStatement` from `QcSOn.linear_main` |
| `Defs.lean` | Basic definitions used internally (same as in `Statement.lean`) |
| `LocalFunction.lean` | The polynomials `g` and `W₀(F) = g(½(FᵀF - Id))`, frame indifference (§3) |
| `SecondVariation.lean` | `L_e`, `Q_e`; second derivative of `W₀` along lines, eq. (3.3); convexity from `f'' ≥ 0` |
| `Reduced.lean` | Cofactor identities (1.3); the polynomial `P(e, c, b)` (3.4), Lemma 3.1 (zero set at the identity), Lemma 3.3 |
| `LocalMin.lean` | Nondegenerate minima: Lemma 4.1 |
| `Charts.lean` | The charts (3.7), local expansions, the matrices `A_k` and `LDLᵀ` certificates (Lemma 3.4) |
| `RankOne.lean` | Symmetry (3.6); rank-one convexity of `W₀` near `SO(3)`, Proposition 4.2 |
| `Sverak.lean` | Lemma 3.2; Šverák's test function, failure of quasiconvexity of `W₀`, Proposition 5.1 (§5) |
| `PeriodicAvg.lean`, `Periodic.lean` | Periodic test functions, Lemma 1.2 |
| `Global.lean` | Minors along rank-one lines (1.5), Lemma 6.1, the smooth cutoff `χ`, the globalization (§6) |
| `Main.lean` | Assembly: `QcSOn.main` (Theorem 1.1) |
| `Linear.lean` | The geometrically linear example `fL F = g_lin(sym F)` (§2): Lemma 2.3 (minimizers, `QcSOn.fL_min`), Lemma 2.4, Lemma 2.5 (Steps 1–4), Theorem 2.1 `QcSOn.linear_main` |

## Relation to the paper

* **Statements.** `Statement.lean` states Theorems 1.1 and 2.1 in the simplified form "there is
  a `C^∞` function `ℝ^{3×3} → ℝ` which is frame indifferent (respectively, invariant under the
  addition of skew-symmetric matrices), rank-one convex and not quasiconvex". The internal
  theorem `QcSOn.main` also states that `W = W₀` near `SO(3)`; `QcSOn.linear_main` is stated for
  the explicit polynomial `QcSOn.fL`. The failure of quasiconvexity at `F = Id` (respectively
  `F = 0`) is shown in `QcSOn.not_quasiconvex_of_eventuallyEq` (respectively
  `QcSOn.not_quasiconvex_fL`).
* **Quasiconvexity.** The paper defines quasiconvexity (1.1) for continuous functions. The formal
  definition requires (1.1) only for those test functions `ψ` for which `f (F + ∇ψ)` is
  integrable on `(0,1)ⁿ`. For continuous `f` this is always the case; the assumption ensures that
  the formal statements do not depend on Mathlib's convention that the integral of a
  non-integrable function is `0`.
* **Notation.** The formalization follows the paper closely and uses the same objects:
  `strain F = ½ (Fᵀ F - Id)` is `e`, `g` and `W0` are `g` and `W₀` of (3.1), (3.2),
  `Lg e` and `Qg e` are `L_e` and `Q_e`, `Pc e c b` is `P(e, c, b)` of (3.4), `cof` is the
  cofactor matrix, and `Charts.lean` uses the charts (3.7).
* **Cutoff.** The cutoff of Section 6 is `χ(s) = ∫_{4σ}^s 4 η(r) (r - 4σ)³ dr`, where
  `η(r) = smoothTransition ((r - 4σ)/σ)` is Mathlib's smooth transition function, rescaled to
  `[4σ, 5σ]`.
* **Polynomial identities.** All polynomial identities, including the `LDLᵀ` decompositions
  `yᵀ (A_k - ¼ Id) y = Σⱼ dⱼ (ℓⱼ · y)²` in Lemma 3.4, are checked by Lean's `ring` tactic, and
  `dⱼ > 0` by normalization of rational numbers. To keep these checks fast, `P_k(t y)` is
  expanded factor by factor: each of `det(Id + 2e)`, `cᵀ cof(Id + 2e) c`, `L_e(b ⊗ b)` and
  `Q_e(c ⊙ b)` (at `e = E(t y)`) is written as `φ₀ + t φ₁(y) + t² φ₂(y) + t³ φ_R(t, y)`, and
  the expansions are multiplied.
* **Versions.** The proofs have been checked with Lean `v4.34.1` and Mathlib `v4.34.1`
  (commit `d13f23b`), as pinned in `lean-toolchain` and `lake-manifest.json`.

## Citation

If you use this code, please cite the paper above.

## Authorship and license

The Lean code in this repository was written entirely by the AI model
Claude Opus 5.5 (Anthropic), using Claude Code, under the guidance of the authors of the paper,
Sergio Conti, Georg Dolzmann and Patrick Dondl, who specified the statements and the proof
strategy and checked the formal statements in `QcAndSOn/Statement.lean`. The correctness of the
proofs is checked by the Lean kernel.

Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl.
Released under the Apache License 2.0, see [`LICENSE`](LICENSE).
