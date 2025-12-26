/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# `Module.End R M` is a central algebra

This file shows that the algebra of endomorphisms on a free module
over a commutative semiring is central.

* `Module.End.exists_apply_eq_smul`:
in the noncommutative case, the center of `End R M` consists of homotheties with central ratio.

-/

open Module Free

namespace Algebra.IsCentral

open Module.Free Module.Basis

variable {R M : Type*} [AddCommMonoid M]

section

variable [Semiring R] [Module R M] [Free R M]

/-- The center of endomorphisms on a free module
consists of homotheties with central ratio. -/
theorem _root_.Module.End.exists_apply_eq_smul
    (f : End R M) (hf : f ∈ Subsemiring.center (End R M)) :
    ∃ a ∈ Subsemiring.center R, ∀ x, f x = a • x := by
  rcases subsingleton_or_nontrivial M
  · refine ⟨1, by simp, ?_⟩
    intro; apply Subsingleton.allEq
  let b := Free.chooseBasis R M
  let i := b.index_nonempty.some
  simp_rw [Subsemiring.mem_center_iff] at hf ⊢
  suffices _ by
    refine ⟨b.coord i (f (b i)),
      fun r ↦ by simpa using congr(b.coord i $(this (r • b i))),
      this⟩
  intro y
  simpa using congr($(hf ((b.coord i).smulRight y)) (b i)).symm

end

variable [CommSemiring R] [Module R M] [Free R M]

/-- The center of endomorphisms on a free module is trivial,
in other words, it is a central algebra. -/
public instance : IsCentral R (End R M) where
  out T hT := by
    nontriviality M
    let b := chooseBasis R M
    let i := b.index_nonempty.some
    refine ⟨b.coord i (T (b i)), LinearMap.ext fun y ↦ ?_⟩
    simpa using congr($(Subalgebra.mem_center_iff.mp hT <| (b.coord i).smulRight y) (b i))

end Algebra.IsCentral
