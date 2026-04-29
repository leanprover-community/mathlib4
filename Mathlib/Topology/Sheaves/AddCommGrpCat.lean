/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib.Topology.Sheaves.Abelian

/-!
# Sheaves of abelian groups.

Results for sheaves of abelian groups on topological spaces.

-/

@[expose] public section

universe u

open TopologicalSpace Opposite CategoryTheory TopCat
open scoped AlgebraicGeometry

variable {X : TopCat.{u}} {U : Opens X}

namespace TopCat

set_option backward.isDefEq.respectTransparency false in
theorem Presheaf.sections_exact_of_exact
    {S : ShortComplex (Presheaf AddCommGrpCat.{u} X)}
    (hS : S.Exact) {s : S.X₂.obj (Opposite.op U)} (h : S.g.app (Opposite.op U) s = 0) :
    ∃ (t : S.X₁.obj (Opposite.op U)), S.f.app (Opposite.op U) t = s := by
  dsimp [Presheaf] at S
  let F := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U)
  exact (ShortComplex.ab_exact_iff (S.map F)).mp (((Functor.exact_tfae F).out 1 3 rfl rfl).mpr
    ⟨inferInstance, inferInstance⟩ S hS) _ h

lemma Sheaf.sections_exact_of_left_exact {S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)}
    (hS : S.Exact) (hf : Mono S.f) (s : S.X₂.obj.obj (Opposite.op U))
    (h : S.g.hom.app (Opposite.op U) s = 0) :
    ∃ (t : S.X₁.obj.obj (Opposite.op U)), S.f.hom.app (Opposite.op U) t = s :=
  Presheaf.sections_exact_of_exact
    (((Functor.preservesFiniteLimits_tfae (Sheaf.forget ..)).out 1 3 rfl rfl).mpr
    inferInstance S ⟨hS, hf⟩).left h

lemma Presheaf.restrict_sum {V : Opens X} {F : Presheaf AddCommGrpCat X} (h : V ≤ U)
    (s t : F.obj (op U)) : (s + t) |_ V = s |_ V + t |_ V := by
  delta Presheaf.restrictOpen Presheaf.restrict
  cat_disch

end TopCat
