/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.Algebra.Module.SpanRank
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.RingTheory.FiniteType
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Nontriviality.Core
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Minimal polynomials on a finite algebra

This file proves the bound on the degree of a minimal polynomial on an algebra
that is finite as a module.

-/

@[expose] public section

variable {A B : Type*} [CommRing A] [Ring B] [Algebra A B] [Module.Finite A B] (x : B)

open Polynomial

namespace minpoly

variable (A) in
theorem natDegree_le_spanFinrank :
    (minpoly A x).natDegree ≤ (⊤ : Submodule A B).spanFinrank := by
  rcases LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero _ (Algebra.lmul A _ x) with
    ⟨f, f_monic, f_deg, f_aeval⟩
  refine f_deg ▸ (natDegree_le_natDegree <| minpoly.min _ _ f_monic ?_)
  rw [aeval_algHom_apply] at f_aeval
  exact Algebra.lmul_injective (R := A) <| by simpa using f_aeval

theorem natDegree_le [Module.Free A B] : (minpoly A x).natDegree ≤ Module.finrank A B := by
  nontriviality A
  simpa [Module.finrank_eq_spanFinrank_of_free] using natDegree_le_spanFinrank A x

theorem degree_le [Module.Free A B] : (minpoly A x).degree ≤ Module.finrank A B :=
  degree_le_of_natDegree_le <| natDegree_le x

end minpoly
