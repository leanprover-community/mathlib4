/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Eric Wieser
-/
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.LinearAlgebra.Basis.HasCanonicalBasis


/-! # Notation for partial derivatives

This file introduces some custom notation for partial derivatives. In order to make this
as flexible as possible (e.g. we would like to have consistent notation that works for
`ℝ × ℝ`, `Fin 2 → ℝ` and `EuclideanSpace ℝ (Fin 2)`), we work on abstract vector spaces
equiped with a `HasCanonicalBasis` instance.

We introduce two different notations
- Whenever the index `i` is subscriptable, we can use `∂ᵢ[ℝ] f` to denote the `i-th` partial
  derivative. This works for e.g `i : Fin n`.
- In general, if the basis is indexed by a type `ι`, then we can use `∂[i; ℝ] f` for the
  `i`-th partial derivative.

-/

universe u v w u' v' w'

namespace HasCanonicalBasis
/--
The partial derivative of a function `F : V → 𝕜`.

`partialDeriv 𝕜 F i tx` return the partial derivative of function `F : V → 𝕜`
with respect to the `i`-th component of the canonical basis of `V` at point `tx : V`.

This can be written using the following notations:
- `(∂ᵢ[ℝ] f) tx` if the index `i` is subscriptable,
- `(∂[i;ℝ] f) tx` in general.
-/
@[simp, nolint unusedArguments] -- we need `HasCanonicalBasis 𝕜 V ι f` to make the notation work
noncomputable def partialDeriv (𝕜 : Type u) {V : Type v} {ι : Type w} {E : Type*}
    {f : ι → V} [NontriviallyNormedField 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [HasCanonicalBasis 𝕜 V ι f] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : V → E) (i : ι) (tx : V) : E :=
  lineDeriv 𝕜 F tx (f i)

section Notation

open Mathlib Lean Meta Tactic Elab

/-
Define the partial derivative notations. Note that we need to use a macro
rather than the `notation` command since we need to use the subscript parser
`subscriptTerm`.
-/

@[inherit_doc partialDeriv]
scoped syntax:100 "∂" noWs subscriptTerm noWs "[" term "]" term:max : term

@[inherit_doc partialDeriv]
scoped syntax:100 "∂[" term ";" term "]" term:max : term

macro_rules
  | `(∂$i:subscript[$𝕜] $f) => `(partialDeriv $𝕜 $f $i)
  | `(∂[$i:term; $𝕜:term] $f) => `(partialDeriv $𝕜 $f $i)

end Notation

end HasCanonicalBasis

open scoped HasCanonicalBasis


section demos
--Here we demo some examples of this notation.

example (f : ℝ → ℝ) (hf : f = 0) : (∂₀[ℝ] f) 0 = 0 := by
  simp [hf, Pi.zero_def, lineDeriv, deriv_const]

example : (∂₀[ℝ] fun (x : ℝ × ℝ) => x.1) 0 = 1 := by
  simp [Pi.zero_def, lineDeriv]


example : (∂[0; ℝ] (fun (x : ℝ × ℝ) => x.1)) 0 = 1 := by
  simp [Pi.zero_def, lineDeriv]

example (n : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ∑ (i : Fin n), (∂ᵢ[ℝ] f) x = ∑ (i : Fin n), (∂[i; ℝ] f) x := by
  rfl

end demos
