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

open TopologicalSpace Opposite CategoryTheory
open scoped AlgebraicGeometry

namespace TopCat

variable {X : TopCat.{u}} {U : Opens X}

set_option backward.isDefEq.respectTransparency false in
theorem Presheaf.ShortComplex.sections_exact_of_exact
    {S : ShortComplex (Presheaf AddCommGrpCat.{u} X)}
    (hS : S.Exact) {s : S.X₂.obj (op U)} (h : S.g.app (op U) s = 0) :
    ∃ (t : S.X₁.obj (op U)), S.f.app (op U) t = s := by
  dsimp [Presheaf] at S
  let F := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  exact (ShortComplex.ab_exact_iff (S.map F)).mp (((Functor.exact_tfae F).out 1 3 rfl rfl).mpr
    ⟨inferInstance, inferInstance⟩ S hS) _ h

lemma Presheaf.restrict_sum {V : Opens X} {F : Presheaf AddCommGrpCat X} (h : V ≤ U)
    (s t : F.obj (op U)) : (s + t) |_ V = s |_V + t |_V := by
  delta Presheaf.restrictOpen Presheaf.restrict
  cat_disch

lemma Sheaf.ShortComplex.Exact.sections_exact_of_mono_f {S : ShortComplex (Sheaf AddCommGrpCat X)}
    (hS : S.Exact) (hf : Mono S.f) (s : S.X₂.obj.obj (op U)) (h : S.g.hom.app (op U) s = 0) :
    ∃ (t : S.X₁.obj.obj (op U)), S.f.hom.app (op U) t = s :=
  Presheaf.ShortComplex.sections_exact_of_exact (((Functor.preservesFiniteLimits_tfae
  (forget AddCommGrpCat X)).out 1 3 rfl rfl).mpr (inferInstanceAs (Limits.PreservesFiniteLimits
  (forget AddCommGrpCat X))) S ⟨hS, hf⟩).left h

end TopCat
