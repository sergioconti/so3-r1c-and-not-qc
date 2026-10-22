/-
Copyright (c) 2026 Sergio Conti, Georg Dolzmann, Patrick Dondl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergio Conti, Georg Dolzmann, Patrick Dondl.
The code was written by Claude Opus 5.5 (Anthropic), under the guidance of the authors.
-/
import QcAndSOn.LocalFunction

/-!
# The second variation of `W₀` along rank-one lines

`g` is a quartic polynomial, so `g (e + X) = g e + Lg e X + Qg e X + Cg e X + Kg X` with
`Lg e X = Dg(e)[X]`, `Qg e X = ½ D²g(e)[X,X]` (the `L_e`, `Q_e` of Section 3 of the paper),
`Cg e X = ⅙ D³g(e)[X,X,X]`, `Kg X = 1/24 D⁴g[X,X,X,X]`; we also use `Bg e Z X = D²g(e)[Z,X]`,
`Ng e Z X = ½ D³g(e)[Z,Z,X]` and `Tg Z X = ⅙ D⁴g[Z,Z,Z,X]`,
so that `Lg (e + Z) X = Lg e X + Bg e Z X + Ng e Z X + Tg Z X`. In these polynomials only the upper
triangular entries of the arguments enter.

Main result: `convexOn_W0_line`: if `gM (F + t A) A ≥ 0` for `t` in a convex set `D`, where
`gM G A = 2 Qg e S + 2 Lg e K`, `e = ½ (GᵀG - Id)`, `S = sym (GᵀA)`, `K = ½ AᵀA`, is the second
derivative of `t ↦ W₀ (G + t A)` at `t = 0` (eq. (3.3)), then `t ↦ W₀ (F + t A)` is convex on `D`.
-/

open Matrix Filter Topology Asymptotics

noncomputable section

namespace QcSOn

/-! ### Multilinear pieces of `g` -/

def Lg (e X : Mat 3 3) : ℝ :=
  2 * (X 2 2) - 2 * (e 0 0) * (X 1 1) + (e 0 0) ^ 2 * (X 1 1) + 12 * (e 0 0) ^ 3 * (X 0 0)
  + 8 * (e 0 1) * (X 0 1) + 48 * (e 0 1) ^ 3 * (X 0 1) + 8 * (e 0 2) * (X 0 2)
  - 8 * (e 0 2) * (X 1 2) + (e 0 2) ^ 2 * (X 0 0) - 4 * (e 0 2) ^ 2 * (X 0 1)
  + (e 0 2) ^ 2 * (X 1 1) + 48 * (e 0 2) ^ 3 * (X 0 2) - 2 * (e 1 1) * (X 0 0)
  + (e 1 1) ^ 2 * (X 0 0) + 12 * (e 1 1) ^ 3 * (X 1 1) - 8 * (e 1 2) * (X 0 2)
  + 8 * (e 1 2) * (X 1 2) + (e 1 2) ^ 2 * (X 0 0) - 4 * (e 1 2) ^ 2 * (X 0 1)
  + (e 1 2) ^ 2 * (X 1 1) + 48 * (e 1 2) ^ 3 * (X 1 2) + 12 * (e 2 2) ^ 3 * (X 2 2)
  + 24 * (e 0 0) * (e 0 1) ^ 2 * (X 0 0) + 2 * (e 0 0) * (e 0 2) * (X 0 2)
  + (e 0 0) * (e 0 2) * (X 1 1) + 2 * (e 0 0) * (e 0 2) * (X 1 2)
  + 24 * (e 0 0) * (e 0 2) ^ 2 * (X 0 0) + 2 * (e 0 0) * (e 1 1) * (X 0 0)
  + (e 0 0) * (e 1 1) * (X 0 2) + 2 * (e 0 0) * (e 1 1) * (X 1 1) + (e 0 0) * (e 1 1) * (X 1 2)
  + 12 * (e 0 0) * (e 1 1) ^ 2 * (X 0 0) + 2 * (e 0 0) * (e 1 2) * (X 0 2)
  + (e 0 0) * (e 1 2) * (X 1 1) + 2 * (e 0 0) * (e 1 2) * (X 1 2)
  + 24 * (e 0 0) * (e 1 2) ^ 2 * (X 0 0) + 12 * (e 0 0) * (e 2 2) ^ 2 * (X 0 0)
  + 24 * (e 0 0) ^ 2 * (e 0 1) * (X 0 1) + 24 * (e 0 0) ^ 2 * (e 0 2) * (X 0 2)
  + 12 * (e 0 0) ^ 2 * (e 1 1) * (X 1 1) + 24 * (e 0 0) ^ 2 * (e 1 2) * (X 1 2)
  + 12 * (e 0 0) ^ 2 * (e 2 2) * (X 2 2) - 8 * (e 0 1) * (e 0 2) * (X 0 2)
  - 8 * (e 0 1) * (e 0 2) * (X 1 2) + 48 * (e 0 1) * (e 0 2) ^ 2 * (X 0 1)
  + 24 * (e 0 1) * (e 1 1) ^ 2 * (X 0 1) - 8 * (e 0 1) * (e 1 2) * (X 0 2)
  - 8 * (e 0 1) * (e 1 2) * (X 1 2) + 48 * (e 0 1) * (e 1 2) ^ 2 * (X 0 1)
  + 24 * (e 0 1) * (e 2 2) ^ 2 * (X 0 1) + 48 * (e 0 1) ^ 2 * (e 0 2) * (X 0 2)
  + 24 * (e 0 1) ^ 2 * (e 1 1) * (X 1 1) + 48 * (e 0 1) ^ 2 * (e 1 2) * (X 1 2)
  + 24 * (e 0 1) ^ 2 * (e 2 2) * (X 2 2) + (e 0 2) * (e 1 1) * (X 0 0)
  + 2 * (e 0 2) * (e 1 1) * (X 0 2) + 2 * (e 0 2) * (e 1 1) * (X 1 2)
  + 24 * (e 0 2) * (e 1 1) ^ 2 * (X 0 2) + 2 * (e 0 2) * (e 1 2) * (X 0 0)
  - 8 * (e 0 2) * (e 1 2) * (X 0 1) + 2 * (e 0 2) * (e 1 2) * (X 1 1)
  + 48 * (e 0 2) * (e 1 2) ^ 2 * (X 0 2) + 24 * (e 0 2) * (e 2 2) ^ 2 * (X 0 2)
  + 24 * (e 0 2) ^ 2 * (e 1 1) * (X 1 1) + 48 * (e 0 2) ^ 2 * (e 1 2) * (X 1 2)
  + 24 * (e 0 2) ^ 2 * (e 2 2) * (X 2 2) + (e 1 1) * (e 1 2) * (X 0 0)
  + 2 * (e 1 1) * (e 1 2) * (X 0 2) + 2 * (e 1 1) * (e 1 2) * (X 1 2)
  + 24 * (e 1 1) * (e 1 2) ^ 2 * (X 1 1) + 12 * (e 1 1) * (e 2 2) ^ 2 * (X 1 1)
  + 24 * (e 1 1) ^ 2 * (e 1 2) * (X 1 2) + 12 * (e 1 1) ^ 2 * (e 2 2) * (X 2 2)
  + 24 * (e 1 2) * (e 2 2) ^ 2 * (X 1 2) + 24 * (e 1 2) ^ 2 * (e 2 2) * (X 2 2)

def Qg (e X : Mat 3 3) : ℝ :=
  4 * (X 0 1) ^ 2 + 4 * (X 0 2) ^ 2 + 4 * (X 1 2) ^ 2 + (e 0 0) * (X 0 2) ^ 2
  + (e 0 0) * (X 1 1) ^ 2 + (e 0 0) * (X 1 2) ^ 2 + 18 * (e 0 0) ^ 2 * (X 0 0) ^ 2
  + 12 * (e 0 0) ^ 2 * (X 0 1) ^ 2 + 12 * (e 0 0) ^ 2 * (X 0 2) ^ 2
  + 6 * (e 0 0) ^ 2 * (X 1 1) ^ 2 + 12 * (e 0 0) ^ 2 * (X 1 2) ^ 2 + 6 * (e 0 0) ^ 2 * (X 2 2) ^ 2
  - 4 * (e 0 1) * (X 0 2) ^ 2 - 4 * (e 0 1) * (X 1 2) ^ 2 + 12 * (e 0 1) ^ 2 * (X 0 0) ^ 2
  + 72 * (e 0 1) ^ 2 * (X 0 1) ^ 2 + 24 * (e 0 1) ^ 2 * (X 0 2) ^ 2
  + 12 * (e 0 1) ^ 2 * (X 1 1) ^ 2 + 24 * (e 0 1) ^ 2 * (X 1 2) ^ 2
  + 12 * (e 0 1) ^ 2 * (X 2 2) ^ 2 + 12 * (e 0 2) ^ 2 * (X 0 0) ^ 2
  + 24 * (e 0 2) ^ 2 * (X 0 1) ^ 2 + 72 * (e 0 2) ^ 2 * (X 0 2) ^ 2
  + 12 * (e 0 2) ^ 2 * (X 1 1) ^ 2 + 24 * (e 0 2) ^ 2 * (X 1 2) ^ 2
  + 12 * (e 0 2) ^ 2 * (X 2 2) ^ 2 + (e 1 1) * (X 0 0) ^ 2 + (e 1 1) * (X 0 2) ^ 2
  + (e 1 1) * (X 1 2) ^ 2 + 6 * (e 1 1) ^ 2 * (X 0 0) ^ 2 + 12 * (e 1 1) ^ 2 * (X 0 1) ^ 2
  + 12 * (e 1 1) ^ 2 * (X 0 2) ^ 2 + 18 * (e 1 1) ^ 2 * (X 1 1) ^ 2
  + 12 * (e 1 1) ^ 2 * (X 1 2) ^ 2 + 6 * (e 1 1) ^ 2 * (X 2 2) ^ 2
  + 12 * (e 1 2) ^ 2 * (X 0 0) ^ 2 + 24 * (e 1 2) ^ 2 * (X 0 1) ^ 2
  + 24 * (e 1 2) ^ 2 * (X 0 2) ^ 2 + 12 * (e 1 2) ^ 2 * (X 1 1) ^ 2
  + 72 * (e 1 2) ^ 2 * (X 1 2) ^ 2 + 12 * (e 1 2) ^ 2 * (X 2 2) ^ 2
  + 6 * (e 2 2) ^ 2 * (X 0 0) ^ 2 + 12 * (e 2 2) ^ 2 * (X 0 1) ^ 2
  + 12 * (e 2 2) ^ 2 * (X 0 2) ^ 2 + 6 * (e 2 2) ^ 2 * (X 1 1) ^ 2
  + 12 * (e 2 2) ^ 2 * (X 1 2) ^ 2 + 18 * (e 2 2) ^ 2 * (X 2 2) ^ 2 - 2 * (X 0 0) * (X 1 1)
  - 8 * (X 0 2) * (X 1 2) + 2 * (e 0 0) * (X 0 0) * (X 1 1) + (e 0 0) * (X 0 2) * (X 1 1)
  + 2 * (e 0 0) * (X 0 2) * (X 1 2) + (e 0 0) * (X 1 1) * (X 1 2)
  - 8 * (e 0 1) * (X 0 2) * (X 1 2) + 2 * (e 0 2) * (X 0 0) * (X 0 2)
  + (e 0 2) * (X 0 0) * (X 1 1) + 2 * (e 0 2) * (X 0 0) * (X 1 2)
  - 8 * (e 0 2) * (X 0 1) * (X 0 2) - 8 * (e 0 2) * (X 0 1) * (X 1 2)
  + 2 * (e 0 2) * (X 0 2) * (X 1 1) + 2 * (e 0 2) * (X 1 1) * (X 1 2)
  + (e 1 1) * (X 0 0) * (X 0 2) + 2 * (e 1 1) * (X 0 0) * (X 1 1) + (e 1 1) * (X 0 0) * (X 1 2)
  + 2 * (e 1 1) * (X 0 2) * (X 1 2) + 2 * (e 1 2) * (X 0 0) * (X 0 2)
  + (e 1 2) * (X 0 0) * (X 1 1) + 2 * (e 1 2) * (X 0 0) * (X 1 2)
  - 8 * (e 1 2) * (X 0 1) * (X 0 2) - 8 * (e 1 2) * (X 0 1) * (X 1 2)
  + 2 * (e 1 2) * (X 0 2) * (X 1 1) + 2 * (e 1 2) * (X 1 1) * (X 1 2)
  + 48 * (e 0 0) * (e 0 1) * (X 0 0) * (X 0 1) + 48 * (e 0 0) * (e 0 2) * (X 0 0) * (X 0 2)
  + 24 * (e 0 0) * (e 1 1) * (X 0 0) * (X 1 1) + 48 * (e 0 0) * (e 1 2) * (X 0 0) * (X 1 2)
  + 24 * (e 0 0) * (e 2 2) * (X 0 0) * (X 2 2) + 96 * (e 0 1) * (e 0 2) * (X 0 1) * (X 0 2)
  + 48 * (e 0 1) * (e 1 1) * (X 0 1) * (X 1 1) + 96 * (e 0 1) * (e 1 2) * (X 0 1) * (X 1 2)
  + 48 * (e 0 1) * (e 2 2) * (X 0 1) * (X 2 2) + 48 * (e 0 2) * (e 1 1) * (X 0 2) * (X 1 1)
  + 96 * (e 0 2) * (e 1 2) * (X 0 2) * (X 1 2) + 48 * (e 0 2) * (e 2 2) * (X 0 2) * (X 2 2)
  + 48 * (e 1 1) * (e 1 2) * (X 1 1) * (X 1 2) + 24 * (e 1 1) * (e 2 2) * (X 1 1) * (X 2 2)
  + 48 * (e 1 2) * (e 2 2) * (X 1 2) * (X 2 2)

def Cg (e X : Mat 3 3) : ℝ :=
  12 * (e 0 0) * (X 0 0) ^ 3 + 48 * (e 0 1) * (X 0 1) ^ 3 + 48 * (e 0 2) * (X 0 2) ^ 3
  + 12 * (e 1 1) * (X 1 1) ^ 3 + 48 * (e 1 2) * (X 1 2) ^ 3 + 12 * (e 2 2) * (X 2 2) ^ 3
  + (X 0 0) * (X 0 2) ^ 2 + (X 0 0) * (X 1 1) ^ 2 + (X 0 0) * (X 1 2) ^ 2 + (X 0 0) ^ 2 * (X 1 1)
  - 4 * (X 0 1) * (X 0 2) ^ 2 - 4 * (X 0 1) * (X 1 2) ^ 2 + (X 0 2) ^ 2 * (X 1 1)
  + (X 1 1) * (X 1 2) ^ 2 + 24 * (e 0 0) * (X 0 0) * (X 0 1) ^ 2
  + 24 * (e 0 0) * (X 0 0) * (X 0 2) ^ 2 + 12 * (e 0 0) * (X 0 0) * (X 1 1) ^ 2
  + 24 * (e 0 0) * (X 0 0) * (X 1 2) ^ 2 + 12 * (e 0 0) * (X 0 0) * (X 2 2) ^ 2
  + 24 * (e 0 1) * (X 0 0) ^ 2 * (X 0 1) + 48 * (e 0 1) * (X 0 1) * (X 0 2) ^ 2
  + 24 * (e 0 1) * (X 0 1) * (X 1 1) ^ 2 + 48 * (e 0 1) * (X 0 1) * (X 1 2) ^ 2
  + 24 * (e 0 1) * (X 0 1) * (X 2 2) ^ 2 + 24 * (e 0 2) * (X 0 0) ^ 2 * (X 0 2)
  + 48 * (e 0 2) * (X 0 1) ^ 2 * (X 0 2) + 24 * (e 0 2) * (X 0 2) * (X 1 1) ^ 2
  + 48 * (e 0 2) * (X 0 2) * (X 1 2) ^ 2 + 24 * (e 0 2) * (X 0 2) * (X 2 2) ^ 2
  + 12 * (e 1 1) * (X 0 0) ^ 2 * (X 1 1) + 24 * (e 1 1) * (X 0 1) ^ 2 * (X 1 1)
  + 24 * (e 1 1) * (X 0 2) ^ 2 * (X 1 1) + 24 * (e 1 1) * (X 1 1) * (X 1 2) ^ 2
  + 12 * (e 1 1) * (X 1 1) * (X 2 2) ^ 2 + 24 * (e 1 2) * (X 0 0) ^ 2 * (X 1 2)
  + 48 * (e 1 2) * (X 0 1) ^ 2 * (X 1 2) + 48 * (e 1 2) * (X 0 2) ^ 2 * (X 1 2)
  + 24 * (e 1 2) * (X 1 1) ^ 2 * (X 1 2) + 24 * (e 1 2) * (X 1 2) * (X 2 2) ^ 2
  + 12 * (e 2 2) * (X 0 0) ^ 2 * (X 2 2) + 24 * (e 2 2) * (X 0 1) ^ 2 * (X 2 2)
  + 24 * (e 2 2) * (X 0 2) ^ 2 * (X 2 2) + 12 * (e 2 2) * (X 1 1) ^ 2 * (X 2 2)
  + 24 * (e 2 2) * (X 1 2) ^ 2 * (X 2 2) + (X 0 0) * (X 0 2) * (X 1 1)
  + 2 * (X 0 0) * (X 0 2) * (X 1 2) + (X 0 0) * (X 1 1) * (X 1 2)
  - 8 * (X 0 1) * (X 0 2) * (X 1 2) + 2 * (X 0 2) * (X 1 1) * (X 1 2)

def Kg (X : Mat 3 3) : ℝ :=
  3 * (X 0 0) ^ 4 + 12 * (X 0 1) ^ 4 + 12 * (X 0 2) ^ 4 + 3 * (X 1 1) ^ 4 + 12 * (X 1 2) ^ 4
  + 3 * (X 2 2) ^ 4 + 12 * (X 0 0) ^ 2 * (X 0 1) ^ 2 + 12 * (X 0 0) ^ 2 * (X 0 2) ^ 2
  + 6 * (X 0 0) ^ 2 * (X 1 1) ^ 2 + 12 * (X 0 0) ^ 2 * (X 1 2) ^ 2 + 6 * (X 0 0) ^ 2 * (X 2 2) ^ 2
  + 24 * (X 0 1) ^ 2 * (X 0 2) ^ 2 + 12 * (X 0 1) ^ 2 * (X 1 1) ^ 2
  + 24 * (X 0 1) ^ 2 * (X 1 2) ^ 2 + 12 * (X 0 1) ^ 2 * (X 2 2) ^ 2
  + 12 * (X 0 2) ^ 2 * (X 1 1) ^ 2 + 24 * (X 0 2) ^ 2 * (X 1 2) ^ 2
  + 12 * (X 0 2) ^ 2 * (X 2 2) ^ 2 + 12 * (X 1 1) ^ 2 * (X 1 2) ^ 2
  + 6 * (X 1 1) ^ 2 * (X 2 2) ^ 2 + 12 * (X 1 2) ^ 2 * (X 2 2) ^ 2

def Bg (e Z X : Mat 3 3) : ℝ :=
  -2 * (X 0 0) * (Z 1 1) + 8 * (X 0 1) * (Z 0 1) + 8 * (X 0 2) * (Z 0 2) - 8 * (X 0 2) * (Z 1 2)
  - 2 * (X 1 1) * (Z 0 0) - 8 * (X 1 2) * (Z 0 2) + 8 * (X 1 2) * (Z 1 2)
  + 2 * (e 0 0) * (X 0 0) * (Z 1 1) + 2 * (e 0 0) * (X 0 2) * (Z 0 2)
  + (e 0 0) * (X 0 2) * (Z 1 1) + 2 * (e 0 0) * (X 0 2) * (Z 1 2)
  + 2 * (e 0 0) * (X 1 1) * (Z 0 0) + (e 0 0) * (X 1 1) * (Z 0 2)
  + 2 * (e 0 0) * (X 1 1) * (Z 1 1) + (e 0 0) * (X 1 1) * (Z 1 2)
  + 2 * (e 0 0) * (X 1 2) * (Z 0 2) + (e 0 0) * (X 1 2) * (Z 1 1)
  + 2 * (e 0 0) * (X 1 2) * (Z 1 2) + 36 * (e 0 0) ^ 2 * (X 0 0) * (Z 0 0)
  + 24 * (e 0 0) ^ 2 * (X 0 1) * (Z 0 1) + 24 * (e 0 0) ^ 2 * (X 0 2) * (Z 0 2)
  + 12 * (e 0 0) ^ 2 * (X 1 1) * (Z 1 1) + 24 * (e 0 0) ^ 2 * (X 1 2) * (Z 1 2)
  + 12 * (e 0 0) ^ 2 * (X 2 2) * (Z 2 2) - 8 * (e 0 1) * (X 0 2) * (Z 0 2)
  - 8 * (e 0 1) * (X 0 2) * (Z 1 2) - 8 * (e 0 1) * (X 1 2) * (Z 0 2)
  - 8 * (e 0 1) * (X 1 2) * (Z 1 2) + 24 * (e 0 1) ^ 2 * (X 0 0) * (Z 0 0)
  + 144 * (e 0 1) ^ 2 * (X 0 1) * (Z 0 1) + 48 * (e 0 1) ^ 2 * (X 0 2) * (Z 0 2)
  + 24 * (e 0 1) ^ 2 * (X 1 1) * (Z 1 1) + 48 * (e 0 1) ^ 2 * (X 1 2) * (Z 1 2)
  + 24 * (e 0 1) ^ 2 * (X 2 2) * (Z 2 2) + 2 * (e 0 2) * (X 0 0) * (Z 0 2)
  + (e 0 2) * (X 0 0) * (Z 1 1) + 2 * (e 0 2) * (X 0 0) * (Z 1 2)
  - 8 * (e 0 2) * (X 0 1) * (Z 0 2) - 8 * (e 0 2) * (X 0 1) * (Z 1 2)
  + 2 * (e 0 2) * (X 0 2) * (Z 0 0) - 8 * (e 0 2) * (X 0 2) * (Z 0 1)
  + 2 * (e 0 2) * (X 0 2) * (Z 1 1) + (e 0 2) * (X 1 1) * (Z 0 0)
  + 2 * (e 0 2) * (X 1 1) * (Z 0 2) + 2 * (e 0 2) * (X 1 1) * (Z 1 2)
  + 2 * (e 0 2) * (X 1 2) * (Z 0 0) - 8 * (e 0 2) * (X 1 2) * (Z 0 1)
  + 2 * (e 0 2) * (X 1 2) * (Z 1 1) + 24 * (e 0 2) ^ 2 * (X 0 0) * (Z 0 0)
  + 48 * (e 0 2) ^ 2 * (X 0 1) * (Z 0 1) + 144 * (e 0 2) ^ 2 * (X 0 2) * (Z 0 2)
  + 24 * (e 0 2) ^ 2 * (X 1 1) * (Z 1 1) + 48 * (e 0 2) ^ 2 * (X 1 2) * (Z 1 2)
  + 24 * (e 0 2) ^ 2 * (X 2 2) * (Z 2 2) + 2 * (e 1 1) * (X 0 0) * (Z 0 0)
  + (e 1 1) * (X 0 0) * (Z 0 2) + 2 * (e 1 1) * (X 0 0) * (Z 1 1) + (e 1 1) * (X 0 0) * (Z 1 2)
  + (e 1 1) * (X 0 2) * (Z 0 0) + 2 * (e 1 1) * (X 0 2) * (Z 0 2)
  + 2 * (e 1 1) * (X 0 2) * (Z 1 2) + 2 * (e 1 1) * (X 1 1) * (Z 0 0)
  + (e 1 1) * (X 1 2) * (Z 0 0) + 2 * (e 1 1) * (X 1 2) * (Z 0 2)
  + 2 * (e 1 1) * (X 1 2) * (Z 1 2) + 12 * (e 1 1) ^ 2 * (X 0 0) * (Z 0 0)
  + 24 * (e 1 1) ^ 2 * (X 0 1) * (Z 0 1) + 24 * (e 1 1) ^ 2 * (X 0 2) * (Z 0 2)
  + 36 * (e 1 1) ^ 2 * (X 1 1) * (Z 1 1) + 24 * (e 1 1) ^ 2 * (X 1 2) * (Z 1 2)
  + 12 * (e 1 1) ^ 2 * (X 2 2) * (Z 2 2) + 2 * (e 1 2) * (X 0 0) * (Z 0 2)
  + (e 1 2) * (X 0 0) * (Z 1 1) + 2 * (e 1 2) * (X 0 0) * (Z 1 2)
  - 8 * (e 1 2) * (X 0 1) * (Z 0 2) - 8 * (e 1 2) * (X 0 1) * (Z 1 2)
  + 2 * (e 1 2) * (X 0 2) * (Z 0 0) - 8 * (e 1 2) * (X 0 2) * (Z 0 1)
  + 2 * (e 1 2) * (X 0 2) * (Z 1 1) + (e 1 2) * (X 1 1) * (Z 0 0)
  + 2 * (e 1 2) * (X 1 1) * (Z 0 2) + 2 * (e 1 2) * (X 1 1) * (Z 1 2)
  + 2 * (e 1 2) * (X 1 2) * (Z 0 0) - 8 * (e 1 2) * (X 1 2) * (Z 0 1)
  + 2 * (e 1 2) * (X 1 2) * (Z 1 1) + 24 * (e 1 2) ^ 2 * (X 0 0) * (Z 0 0)
  + 48 * (e 1 2) ^ 2 * (X 0 1) * (Z 0 1) + 48 * (e 1 2) ^ 2 * (X 0 2) * (Z 0 2)
  + 24 * (e 1 2) ^ 2 * (X 1 1) * (Z 1 1) + 144 * (e 1 2) ^ 2 * (X 1 2) * (Z 1 2)
  + 24 * (e 1 2) ^ 2 * (X 2 2) * (Z 2 2) + 12 * (e 2 2) ^ 2 * (X 0 0) * (Z 0 0)
  + 24 * (e 2 2) ^ 2 * (X 0 1) * (Z 0 1) + 24 * (e 2 2) ^ 2 * (X 0 2) * (Z 0 2)
  + 12 * (e 2 2) ^ 2 * (X 1 1) * (Z 1 1) + 24 * (e 2 2) ^ 2 * (X 1 2) * (Z 1 2)
  + 36 * (e 2 2) ^ 2 * (X 2 2) * (Z 2 2) + 48 * (e 0 0) * (e 0 1) * (X 0 0) * (Z 0 1)
  + 48 * (e 0 0) * (e 0 1) * (X 0 1) * (Z 0 0) + 48 * (e 0 0) * (e 0 2) * (X 0 0) * (Z 0 2)
  + 48 * (e 0 0) * (e 0 2) * (X 0 2) * (Z 0 0) + 24 * (e 0 0) * (e 1 1) * (X 0 0) * (Z 1 1)
  + 24 * (e 0 0) * (e 1 1) * (X 1 1) * (Z 0 0) + 48 * (e 0 0) * (e 1 2) * (X 0 0) * (Z 1 2)
  + 48 * (e 0 0) * (e 1 2) * (X 1 2) * (Z 0 0) + 24 * (e 0 0) * (e 2 2) * (X 0 0) * (Z 2 2)
  + 24 * (e 0 0) * (e 2 2) * (X 2 2) * (Z 0 0) + 96 * (e 0 1) * (e 0 2) * (X 0 1) * (Z 0 2)
  + 96 * (e 0 1) * (e 0 2) * (X 0 2) * (Z 0 1) + 48 * (e 0 1) * (e 1 1) * (X 0 1) * (Z 1 1)
  + 48 * (e 0 1) * (e 1 1) * (X 1 1) * (Z 0 1) + 96 * (e 0 1) * (e 1 2) * (X 0 1) * (Z 1 2)
  + 96 * (e 0 1) * (e 1 2) * (X 1 2) * (Z 0 1) + 48 * (e 0 1) * (e 2 2) * (X 0 1) * (Z 2 2)
  + 48 * (e 0 1) * (e 2 2) * (X 2 2) * (Z 0 1) + 48 * (e 0 2) * (e 1 1) * (X 0 2) * (Z 1 1)
  + 48 * (e 0 2) * (e 1 1) * (X 1 1) * (Z 0 2) + 96 * (e 0 2) * (e 1 2) * (X 0 2) * (Z 1 2)
  + 96 * (e 0 2) * (e 1 2) * (X 1 2) * (Z 0 2) + 48 * (e 0 2) * (e 2 2) * (X 0 2) * (Z 2 2)
  + 48 * (e 0 2) * (e 2 2) * (X 2 2) * (Z 0 2) + 48 * (e 1 1) * (e 1 2) * (X 1 1) * (Z 1 2)
  + 48 * (e 1 1) * (e 1 2) * (X 1 2) * (Z 1 1) + 24 * (e 1 1) * (e 2 2) * (X 1 1) * (Z 2 2)
  + 24 * (e 1 1) * (e 2 2) * (X 2 2) * (Z 1 1) + 48 * (e 1 2) * (e 2 2) * (X 1 2) * (Z 2 2)
  + 48 * (e 1 2) * (e 2 2) * (X 2 2) * (Z 1 2)

def Ng (e Z X : Mat 3 3) : ℝ :=
  (X 0 0) * (Z 0 2) ^ 2 + (X 0 0) * (Z 1 1) ^ 2 + (X 0 0) * (Z 1 2) ^ 2
  - 4 * (X 0 1) * (Z 0 2) ^ 2 - 4 * (X 0 1) * (Z 1 2) ^ 2 + (X 1 1) * (Z 0 0) ^ 2
  + (X 1 1) * (Z 0 2) ^ 2 + (X 1 1) * (Z 1 2) ^ 2 + 36 * (e 0 0) * (X 0 0) * (Z 0 0) ^ 2
  + 24 * (e 0 0) * (X 0 0) * (Z 0 1) ^ 2 + 24 * (e 0 0) * (X 0 0) * (Z 0 2) ^ 2
  + 12 * (e 0 0) * (X 0 0) * (Z 1 1) ^ 2 + 24 * (e 0 0) * (X 0 0) * (Z 1 2) ^ 2
  + 12 * (e 0 0) * (X 0 0) * (Z 2 2) ^ 2 + 24 * (e 0 1) * (X 0 1) * (Z 0 0) ^ 2
  + 144 * (e 0 1) * (X 0 1) * (Z 0 1) ^ 2 + 48 * (e 0 1) * (X 0 1) * (Z 0 2) ^ 2
  + 24 * (e 0 1) * (X 0 1) * (Z 1 1) ^ 2 + 48 * (e 0 1) * (X 0 1) * (Z 1 2) ^ 2
  + 24 * (e 0 1) * (X 0 1) * (Z 2 2) ^ 2 + 24 * (e 0 2) * (X 0 2) * (Z 0 0) ^ 2
  + 48 * (e 0 2) * (X 0 2) * (Z 0 1) ^ 2 + 144 * (e 0 2) * (X 0 2) * (Z 0 2) ^ 2
  + 24 * (e 0 2) * (X 0 2) * (Z 1 1) ^ 2 + 48 * (e 0 2) * (X 0 2) * (Z 1 2) ^ 2
  + 24 * (e 0 2) * (X 0 2) * (Z 2 2) ^ 2 + 12 * (e 1 1) * (X 1 1) * (Z 0 0) ^ 2
  + 24 * (e 1 1) * (X 1 1) * (Z 0 1) ^ 2 + 24 * (e 1 1) * (X 1 1) * (Z 0 2) ^ 2
  + 36 * (e 1 1) * (X 1 1) * (Z 1 1) ^ 2 + 24 * (e 1 1) * (X 1 1) * (Z 1 2) ^ 2
  + 12 * (e 1 1) * (X 1 1) * (Z 2 2) ^ 2 + 24 * (e 1 2) * (X 1 2) * (Z 0 0) ^ 2
  + 48 * (e 1 2) * (X 1 2) * (Z 0 1) ^ 2 + 48 * (e 1 2) * (X 1 2) * (Z 0 2) ^ 2
  + 24 * (e 1 2) * (X 1 2) * (Z 1 1) ^ 2 + 144 * (e 1 2) * (X 1 2) * (Z 1 2) ^ 2
  + 24 * (e 1 2) * (X 1 2) * (Z 2 2) ^ 2 + 12 * (e 2 2) * (X 2 2) * (Z 0 0) ^ 2
  + 24 * (e 2 2) * (X 2 2) * (Z 0 1) ^ 2 + 24 * (e 2 2) * (X 2 2) * (Z 0 2) ^ 2
  + 12 * (e 2 2) * (X 2 2) * (Z 1 1) ^ 2 + 24 * (e 2 2) * (X 2 2) * (Z 1 2) ^ 2
  + 36 * (e 2 2) * (X 2 2) * (Z 2 2) ^ 2 + 2 * (X 0 0) * (Z 0 0) * (Z 1 1)
  + (X 0 0) * (Z 0 2) * (Z 1 1) + 2 * (X 0 0) * (Z 0 2) * (Z 1 2) + (X 0 0) * (Z 1 1) * (Z 1 2)
  - 8 * (X 0 1) * (Z 0 2) * (Z 1 2) + 2 * (X 0 2) * (Z 0 0) * (Z 0 2)
  + (X 0 2) * (Z 0 0) * (Z 1 1) + 2 * (X 0 2) * (Z 0 0) * (Z 1 2)
  - 8 * (X 0 2) * (Z 0 1) * (Z 0 2) - 8 * (X 0 2) * (Z 0 1) * (Z 1 2)
  + 2 * (X 0 2) * (Z 0 2) * (Z 1 1) + 2 * (X 0 2) * (Z 1 1) * (Z 1 2)
  + (X 1 1) * (Z 0 0) * (Z 0 2) + 2 * (X 1 1) * (Z 0 0) * (Z 1 1) + (X 1 1) * (Z 0 0) * (Z 1 2)
  + 2 * (X 1 1) * (Z 0 2) * (Z 1 2) + 2 * (X 1 2) * (Z 0 0) * (Z 0 2)
  + (X 1 2) * (Z 0 0) * (Z 1 1) + 2 * (X 1 2) * (Z 0 0) * (Z 1 2)
  - 8 * (X 1 2) * (Z 0 1) * (Z 0 2) - 8 * (X 1 2) * (Z 0 1) * (Z 1 2)
  + 2 * (X 1 2) * (Z 0 2) * (Z 1 1) + 2 * (X 1 2) * (Z 1 1) * (Z 1 2)
  + 48 * (e 0 0) * (X 0 1) * (Z 0 0) * (Z 0 1) + 48 * (e 0 0) * (X 0 2) * (Z 0 0) * (Z 0 2)
  + 24 * (e 0 0) * (X 1 1) * (Z 0 0) * (Z 1 1) + 48 * (e 0 0) * (X 1 2) * (Z 0 0) * (Z 1 2)
  + 24 * (e 0 0) * (X 2 2) * (Z 0 0) * (Z 2 2) + 48 * (e 0 1) * (X 0 0) * (Z 0 0) * (Z 0 1)
  + 96 * (e 0 1) * (X 0 2) * (Z 0 1) * (Z 0 2) + 48 * (e 0 1) * (X 1 1) * (Z 0 1) * (Z 1 1)
  + 96 * (e 0 1) * (X 1 2) * (Z 0 1) * (Z 1 2) + 48 * (e 0 1) * (X 2 2) * (Z 0 1) * (Z 2 2)
  + 48 * (e 0 2) * (X 0 0) * (Z 0 0) * (Z 0 2) + 96 * (e 0 2) * (X 0 1) * (Z 0 1) * (Z 0 2)
  + 48 * (e 0 2) * (X 1 1) * (Z 0 2) * (Z 1 1) + 96 * (e 0 2) * (X 1 2) * (Z 0 2) * (Z 1 2)
  + 48 * (e 0 2) * (X 2 2) * (Z 0 2) * (Z 2 2) + 24 * (e 1 1) * (X 0 0) * (Z 0 0) * (Z 1 1)
  + 48 * (e 1 1) * (X 0 1) * (Z 0 1) * (Z 1 1) + 48 * (e 1 1) * (X 0 2) * (Z 0 2) * (Z 1 1)
  + 48 * (e 1 1) * (X 1 2) * (Z 1 1) * (Z 1 2) + 24 * (e 1 1) * (X 2 2) * (Z 1 1) * (Z 2 2)
  + 48 * (e 1 2) * (X 0 0) * (Z 0 0) * (Z 1 2) + 96 * (e 1 2) * (X 0 1) * (Z 0 1) * (Z 1 2)
  + 96 * (e 1 2) * (X 0 2) * (Z 0 2) * (Z 1 2) + 48 * (e 1 2) * (X 1 1) * (Z 1 1) * (Z 1 2)
  + 48 * (e 1 2) * (X 2 2) * (Z 1 2) * (Z 2 2) + 24 * (e 2 2) * (X 0 0) * (Z 0 0) * (Z 2 2)
  + 48 * (e 2 2) * (X 0 1) * (Z 0 1) * (Z 2 2) + 48 * (e 2 2) * (X 0 2) * (Z 0 2) * (Z 2 2)
  + 24 * (e 2 2) * (X 1 1) * (Z 1 1) * (Z 2 2) + 48 * (e 2 2) * (X 1 2) * (Z 1 2) * (Z 2 2)

def Tg (Z X : Mat 3 3) : ℝ :=
  12 * (X 0 0) * (Z 0 0) ^ 3 + 48 * (X 0 1) * (Z 0 1) ^ 3 + 48 * (X 0 2) * (Z 0 2) ^ 3
  + 12 * (X 1 1) * (Z 1 1) ^ 3 + 48 * (X 1 2) * (Z 1 2) ^ 3 + 12 * (X 2 2) * (Z 2 2) ^ 3
  + 24 * (X 0 0) * (Z 0 0) * (Z 0 1) ^ 2 + 24 * (X 0 0) * (Z 0 0) * (Z 0 2) ^ 2
  + 12 * (X 0 0) * (Z 0 0) * (Z 1 1) ^ 2 + 24 * (X 0 0) * (Z 0 0) * (Z 1 2) ^ 2
  + 12 * (X 0 0) * (Z 0 0) * (Z 2 2) ^ 2 + 24 * (X 0 1) * (Z 0 0) ^ 2 * (Z 0 1)
  + 48 * (X 0 1) * (Z 0 1) * (Z 0 2) ^ 2 + 24 * (X 0 1) * (Z 0 1) * (Z 1 1) ^ 2
  + 48 * (X 0 1) * (Z 0 1) * (Z 1 2) ^ 2 + 24 * (X 0 1) * (Z 0 1) * (Z 2 2) ^ 2
  + 24 * (X 0 2) * (Z 0 0) ^ 2 * (Z 0 2) + 48 * (X 0 2) * (Z 0 1) ^ 2 * (Z 0 2)
  + 24 * (X 0 2) * (Z 0 2) * (Z 1 1) ^ 2 + 48 * (X 0 2) * (Z 0 2) * (Z 1 2) ^ 2
  + 24 * (X 0 2) * (Z 0 2) * (Z 2 2) ^ 2 + 12 * (X 1 1) * (Z 0 0) ^ 2 * (Z 1 1)
  + 24 * (X 1 1) * (Z 0 1) ^ 2 * (Z 1 1) + 24 * (X 1 1) * (Z 0 2) ^ 2 * (Z 1 1)
  + 24 * (X 1 1) * (Z 1 1) * (Z 1 2) ^ 2 + 12 * (X 1 1) * (Z 1 1) * (Z 2 2) ^ 2
  + 24 * (X 1 2) * (Z 0 0) ^ 2 * (Z 1 2) + 48 * (X 1 2) * (Z 0 1) ^ 2 * (Z 1 2)
  + 48 * (X 1 2) * (Z 0 2) ^ 2 * (Z 1 2) + 24 * (X 1 2) * (Z 1 1) ^ 2 * (Z 1 2)
  + 24 * (X 1 2) * (Z 1 2) * (Z 2 2) ^ 2 + 12 * (X 2 2) * (Z 0 0) ^ 2 * (Z 2 2)
  + 24 * (X 2 2) * (Z 0 1) ^ 2 * (Z 2 2) + 24 * (X 2 2) * (Z 0 2) ^ 2 * (Z 2 2)
  + 12 * (X 2 2) * (Z 1 1) ^ 2 * (Z 2 2) + 24 * (X 2 2) * (Z 1 2) ^ 2 * (Z 2 2)

/-- `g (e + s S + s² K)`, expanded to second order in `s`. -/
lemma g_expand (e S K : Mat 3 3) (s : ℝ) :
    g (e + s • S + s ^ 2 • K) = g e + s * Lg e S
      + s ^ 2 * (Lg e K + Qg e (S + s • K) + s * Cg e (S + s • K) + s ^ 2 * Kg (S + s • K)) := by
  simp only [g, Lg, Qg, Cg, Kg, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- `Lg (e + s S + s² K) (S + 2 s K)`, expanded to first order in `s`. -/
lemma Lg_expand (e S K : Mat 3 3) (s : ℝ) :
    Lg (e + s • S + s ^ 2 • K) (S + (2 * s) • K) = Lg e S + s * (2 * Qg e S + 2 * Lg e K)
      + s ^ 2 * (2 * Bg e S K + Bg e K S + 2 * s * Bg e K K
        + Ng e (S + s • K) (S + (2 * s) • K) + s * Tg (S + s • K) (S + (2 * s) • K)) := by
  simp only [Lg, Qg, Bg, Ng, Tg, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ### Derivatives along lines -/

/-- If `φ (t + s) = φ t + s L + s² R(s)` with `R` continuous, then `φ' (t) = L`. -/
lemma hasDerivAt_of_expansion {φ : ℝ → ℝ} {t L : ℝ} (R : ℝ → ℝ) (hR : Continuous R)
    (h : ∀ s, φ (t + s) = φ t + s * L + s ^ 2 * R s) : HasDerivAt φ L t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have h1 : Tendsto (fun s => s * R s) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun s => s * R s := continuous_id.mul hR
    simpa using hc.tendsto 0
  have h2 : (fun s => s * R s * s) =o[𝓝 0] fun s => (1 : ℝ) * s :=
    (isLittleO_one_iff ℝ |>.2 h1).mul_isBigO (isBigO_refl _ _)
  refine (h2.congr_left fun s => ?_).congr_right fun s => one_mul s
  rw [h s, smul_eq_mul]; ring

/-- `½ ((G + s A)ᵀ (G + s A) - Id) = e + s S + s² K` with `e = ½ (GᵀG - Id)`, `S = sym (GᵀA)`,
`K = ½ AᵀA`. -/
lemma strain_line (G A : Mat 3 3) (s : ℝ) :
    strain (G + s • A) = strain G + s • symPart (Gᵀ * A) + s ^ 2 • ((1 / 2 : ℝ) • (Aᵀ * A)) := by
  simp only [strain, symPart, transpose_add, transpose_smul, transpose_mul, transpose_transpose,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  module

/-- First derivative of `t ↦ W₀ (G + t A)` at `t = 0`: `L_e(S)`. -/
def d1 (G A : Mat 3 3) : ℝ := Lg (strain G) (symPart (Gᵀ * A))

/-- Second derivative of `t ↦ W₀ (G + t A)` at `t = 0`, i.e.
`D²W₀(G)[A,A] = 2 Q_e(S) + 2 L_e(K)` (eq. (3.3)). -/
def gM (G A : Mat 3 3) : ℝ :=
  2 * Qg (strain G) (symPart (Gᵀ * A)) + 2 * Lg (strain G) ((1 / 2 : ℝ) • (Aᵀ * A))

lemma continuous_Qg_comp {α : Type*} [TopologicalSpace α] {E X : α → Mat 3 3}
    (hE : Continuous E) (hX : Continuous X) : Continuous fun a => Qg (E a) (X a) := by
  have hE' : ∀ i j, Continuous fun a => E a i j := fun i j => (continuous_apply_apply i j).comp hE
  have hX' : ∀ i j, Continuous fun a => X a i j := fun i j => (continuous_apply_apply i j).comp hX
  unfold Qg; fun_prop

lemma continuous_Cg_comp {α : Type*} [TopologicalSpace α] {E X : α → Mat 3 3}
    (hE : Continuous E) (hX : Continuous X) : Continuous fun a => Cg (E a) (X a) := by
  have hE' : ∀ i j, Continuous fun a => E a i j := fun i j => (continuous_apply_apply i j).comp hE
  have hX' : ∀ i j, Continuous fun a => X a i j := fun i j => (continuous_apply_apply i j).comp hX
  unfold Cg; fun_prop

lemma continuous_Kg_comp {α : Type*} [TopologicalSpace α] {X : α → Mat 3 3}
    (hX : Continuous X) : Continuous fun a => Kg (X a) := by
  have hX' : ∀ i j, Continuous fun a => X a i j := fun i j => (continuous_apply_apply i j).comp hX
  unfold Kg; fun_prop

lemma continuous_Ng_comp {α : Type*} [TopologicalSpace α] {E Z X : α → Mat 3 3}
    (hE : Continuous E) (hZ : Continuous Z) (hX : Continuous X) :
    Continuous fun a => Ng (E a) (Z a) (X a) := by
  have hE' : ∀ i j, Continuous fun a => E a i j := fun i j => (continuous_apply_apply i j).comp hE
  have hZ' : ∀ i j, Continuous fun a => Z a i j := fun i j => (continuous_apply_apply i j).comp hZ
  have hX' : ∀ i j, Continuous fun a => X a i j := fun i j => (continuous_apply_apply i j).comp hX
  unfold Ng; fun_prop

lemma continuous_Tg_comp {α : Type*} [TopologicalSpace α] {Z X : α → Mat 3 3}
    (hZ : Continuous Z) (hX : Continuous X) : Continuous fun a => Tg (Z a) (X a) := by
  have hZ' : ∀ i j, Continuous fun a => Z a i j := fun i j => (continuous_apply_apply i j).comp hZ
  have hX' : ∀ i j, Continuous fun a => X a i j := fun i j => (continuous_apply_apply i j).comp hX
  unfold Tg; fun_prop

lemma hasDerivAt_W0_line (F A : Mat 3 3) (t : ℝ) :
    HasDerivAt (fun t => W0 (F + t • A)) (d1 (F + t • A) A) t := by
  set G := F + t • A
  set e := strain G
  set S := symPart (Gᵀ * A)
  set K := (1 / 2 : ℝ) • (Aᵀ * A)
  refine hasDerivAt_of_expansion
    (fun s => Lg e K + Qg e (S + s • K) + s * Cg e (S + s • K) + s ^ 2 * Kg (S + s • K)) ?_
    fun s => ?_
  · have hY : Continuous fun s : ℝ => S + s • K :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact ((continuous_const.add (continuous_Qg_comp continuous_const hY)).add
      (continuous_id.mul (continuous_Cg_comp continuous_const hY))).add
      ((continuous_id.pow 2).mul (continuous_Kg_comp hY))
  · have hG : F + (t + s) • A = G + s • A := by simp only [G, add_smul]; abel
    change W0 (F + (t + s) • A) = W0 G + s * d1 G A + _
    rw [hG]
    simp only [W0, d1]
    rw [strain_line, g_expand]

lemma hasDerivAt_d1_line (F A : Mat 3 3) (t : ℝ) :
    HasDerivAt (fun t => d1 (F + t • A) A) (gM (F + t • A) A) t := by
  set G := F + t • A
  set e := strain G
  set S := symPart (Gᵀ * A)
  set K := (1 / 2 : ℝ) • (Aᵀ * A)
  refine hasDerivAt_of_expansion
    (fun s => 2 * Bg e S K + Bg e K S + 2 * s * Bg e K K + Ng e (S + s • K) (S + (2 * s) • K)
      + s * Tg (S + s • K) (S + (2 * s) • K))
    ?_ fun s => ?_
  · have hY : Continuous fun s : ℝ => S + s • K :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hX : Continuous fun s : ℝ => S + (2 * s) • K :=
      continuous_const.add ((continuous_const.mul continuous_id).smul continuous_const)
    exact (((continuous_const.add continuous_const).add (continuous_const.mul continuous_id
      |>.mul continuous_const)).add (continuous_Ng_comp continuous_const hY hX)).add
      (continuous_id.mul (continuous_Tg_comp hY hX))
  · have hG : F + (t + s) • A = G + s • A := by simp only [G, add_smul]; abel
    have hS : symPart ((G + s • A)ᵀ * A) = S + (2 * s) • K := by
      simp only [S, K, symPart, transpose_add, transpose_smul, transpose_mul, transpose_transpose,
        add_mul, smul_mul_assoc]
      module
    change d1 (F + (t + s) • A) A = d1 G A + s * gM G A + _
    rw [hG]
    simp only [d1, gM]
    rw [strain_line, hS, Lg_expand]

/-- **Convexity along rank-one (indeed all) lines from the second variation.** -/
lemma convexOn_W0_line (F A : Mat 3 3) {D : Set ℝ} (hD : Convex ℝ D)
    (hg : ∀ t ∈ D, 0 ≤ gM (F + t • A) A) : ConvexOn ℝ D fun t => W0 (F + t • A) :=
  convexOn_of_hasDerivWithinAt2_nonneg hD
    (fun t _ => (hasDerivAt_W0_line F A t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_W0_line F A t).hasDerivWithinAt)
    (fun t _ => (hasDerivAt_d1_line F A t).hasDerivWithinAt)
    (fun t ht => hg t (interior_subset ht))

end QcSOn
