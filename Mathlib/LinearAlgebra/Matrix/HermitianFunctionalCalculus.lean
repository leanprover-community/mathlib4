/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.LinearAlgebra.Matrix.PosDef

/-
This file provides the functional calculus for Hermitian matrices over an RCLike field 𝕜. Given a
function f : 𝕜 → 𝕜 and Hermitian matrix A : Matrix n n 𝕜, we define f(A) naturally using the
diagonalization of f, and prove that there is a polynomial p over 𝕜 such that p(A) = f(A).

## Tags

spectral theorem, diagonalization theorem, functional calculus
-/
