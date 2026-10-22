/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import QcAndSOn.Statement
import QcAndSOn.Main
import QcAndSOn.Linear

/-!
# Proof of the main result

The statement `MainResult.Statement` (file `QcAndSOn/Statement.lean`, which imports only Mathlib)
follows from `QcSOn.main`, whose definitions coincide with those of `Statement.lean`;
`MainResult.LinearStatement` follows from `QcSOn.linear_main`.
-/

/-- **Theorem 1.1**: a `C^∞`, frame-indifferent, rank-one convex function on `ℝ^{3×3}` which is
not quasiconvex. (`QcSOn.main` moreover gives `W = W₀ = g(½ (Fᵀ F - Id))` near `SO(3)`.) -/
theorem MainResult.statement_holds : MainResult.Statement := by
  obtain ⟨W, -, hcd, hfi, hrc, hqc, -⟩ := QcSOn.main
  exact ⟨W, hcd, hfi, hrc, hqc⟩

-- Only the standard axioms `propext`, `Classical.choice`, `Quot.sound` are used.
#print axioms MainResult.statement_holds

/-- **Theorem 2.1**: a `C^∞` function on `ℝ^{3×3}` depending only on `sym F` which is rank-one
convex but not quasiconvex (namely the quartic polynomial `fL F = g_lin(sym F)`). -/
theorem MainResult.linearStatement_holds : MainResult.LinearStatement :=
  ⟨QcSOn.fL, QcSOn.contDiff_fL, QcSOn.linear_main⟩

-- Only the standard axioms `propext`, `Classical.choice`, `Quot.sound` are used.
#print axioms MainResult.linearStatement_holds

-- Lemma 2.3 (minimizers of the linear energy) also uses only the standard axioms.
#print axioms QcSOn.fL_min
