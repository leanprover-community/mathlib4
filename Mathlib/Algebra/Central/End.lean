/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# `Module.End R M` is a central algebra

This file shows that the algebra of endomorphisms on a free module is central.
-/

open Module

variable {R S M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Free R M]
  [CommSemiring S] [Module S M] [SMulCommClass R S M] [Algebra S R] [IsScalarTower S R M]

public theorem Module.End.mem_subsemiringCenter_iff {f : End R M} :
    f ∈ Subsemiring.center (End R M) ↔
      ∃ (α : R) (hα : α ∈ Subsemiring.center R), f = smulLeft α hα :=
  mem_center_iff

public theorem Module.End.mem_subalgebraCenter_iff {f : End R M} :
    f ∈ Subalgebra.center S (End R M) ↔
      ∃ (α : R) (hα : α ∈ Subalgebra.center S R), f = smulLeft α hα :=
  mem_center_iff

namespace Algebra.IsCentral

/-- The center of endomorphisms on a free module is trivial,
in other words, it is a central algebra. -/
public instance [IsCentral S R] : IsCentral S (End R M) where out T hT :=
  have ⟨_, h, _⟩ := T.mem_subalgebraCenter_iff.mp hT
  have ⟨y, _⟩ := center_eq_bot S R ▸ h
  ⟨y, by aesop⟩

end Algebra.IsCentral
