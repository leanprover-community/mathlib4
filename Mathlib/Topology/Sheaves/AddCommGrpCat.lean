/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.Limits

/-!
# Sheaves of abelian groups.

Results for sheaves of abelian groups on topological spaces, in preparation for sheaf cohomology.
- `TopCat.Sheaf.AddCommGrpCat.Γ` : (Γ U) is the functor `(Sheaf AddCommGrpCat X) ⥤ AddCommGrpCat`
  that sends 𝓕 to 𝓕(U) and and sends a morphism f: 𝓕 ⟶ 𝓖 to f(U): 𝓕(U) ⟶ 𝓖(U)
-/

@[expose] public section

universe u v w

noncomputable section

open TopologicalSpace Opposite CategoryTheory AlgebraicGeometry

namespace TopCat

variable {X : TopCat.{u}} {U V : Opens X} {C : Type v} [Category.{w} C]

instance [Abelian C] : Abelian (Presheaf C X) := inferInstanceAs (Abelian (_ ⥤ _))

instance : Abelian (Sheaf AddCommGrpCat X) := inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

instance : (Sheaf.forget AddCommGrpCat X).Additive where

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance : IsGrothendieckAbelian.{u} (Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

instance : EnoughInjectives (Sheaf AddCommGrpCat.{u} X) := IsGrothendieckAbelian.enoughInjectives

instance : HasExt.{u} (Sheaf AddCommGrpCat.{u} X) :=
  hasExt_of_enoughInjectives (Sheaf AddCommGrpCat X)

theorem Presheaf.addCommGrpCat_shortExact_app_zero {S : ShortComplex (Presheaf AddCommGrpCat.{u} X)}
    {s : S.X₂.obj (op U)} (h : S.g.app (op U) s = 0) (hS : S.Exact) :
    ∃(t : S.X₁.obj (op U)), S.f.app (op U) t = s := by
  dsimp [Presheaf] at S
  let F := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  apply (ShortComplex.ab_exact_iff (S.map F)).mp
  · have := ((Functor.exact_tfae F).out 1 3).mpr
    exact this ⟨inferInstance, inferInstance⟩ S hS
  exact h

namespace Sheaf.AddCommGrpCat

/-- Given an open subset U of X, Γ U is the functor that sends a sheaf 𝓕 to 𝓕(U) and sends a
  morphism f: 𝓕 ⟶ 𝓖 to f(U): 𝓕(U) ⟶ 𝓖(U) -/
abbrev Γ (U : Opens X) : (Sheaf AddCommGrpCat X) ⥤ AddCommGrpCat :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op U)

lemma Γ.map_app {F G : Sheaf AddCommGrpCat X} (g : F ⟶ G) :
    (Γ U).map g = g.val.app (op U) := rfl

lemma restrict_sum {F : Sheaf AddCommGrpCat X} (h : V ≤ U) (s t : F.val.obj (op U)) :
    (s + t) |_ V = s |_V + t |_V := by
  delta Presheaf.restrictOpen Presheaf.restrict
  aesop_cat

lemma shortExact_app_zero {S : ShortComplex (Sheaf AddCommGrpCat X)} (s : S.X₂.val.obj (op U))
    (h : S.g.val.app (op U) s = 0) (hS : S.ShortExact) :
    ∃(t : S.X₁.val.obj (op U)), S.f.val.app (op U) t = s := by
  have := ((Functor.preservesFiniteLimits_tfae (forget AddCommGrpCat X)).out 1 3).mpr
    (inferInstanceAs (Limits.PreservesFiniteLimits (forget AddCommGrpCat X)))
  exact Presheaf.addCommGrpCat_shortExact_app_zero h (this S ⟨hS.1, hS.2⟩).left

end TopCat.Sheaf.AddCommGrpCat
