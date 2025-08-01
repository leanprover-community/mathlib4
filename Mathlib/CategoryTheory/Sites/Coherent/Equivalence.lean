/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.CategoryTheory.Sites.Equivalence
/-!

# Coherence and equivalence of categories

This file proves that the coherent and regular topologies transfer nicely along equivalences of
categories.
-/

namespace CategoryTheory

variable {C : Type*} [Category C]

open GrothendieckTopology

namespace Equivalence

variable {D : Type*} [Category D]

section Coherent

variable [Precoherent C]

/-- `Precoherent` is preserved by equivalence of categories. -/
theorem precoherent (e : C ≌ D) : Precoherent D := e.inverse.reflects_precoherent

instance [EssentiallySmall C] :
    Precoherent (SmallModel C) := (equivSmallModel C).precoherent

instance (e : C ≌ D) : haveI := precoherent e
    e.inverse.IsDenseSubsite (coherentTopology D) (coherentTopology C) where
  functorPushforward_mem_iff := by
    rw [coherentTopology.eq_induced e.inverse]
    simp only [Functor.mem_inducedTopology_sieves_iff, implies_true]

variable (A : Type*) [Category A]

/--
Equivalent precoherent categories give equivalent coherent toposes.
-/
@[simps!]
def sheafCongrPrecoherent (e : C ≌ D) : haveI := e.precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A := e.sheafCongr _ _ _

open Presheaf

/--
The coherent sheaf condition can be checked after precomposing with the equivalence.
-/
theorem precoherent_isSheaf_iff (e : C ≌ D) (F : Cᵒᵖ ⥤ A) : haveI := e.precoherent
    IsSheaf (coherentTopology C) F ↔ IsSheaf (coherentTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF ↦ ((e.sheafCongrPrecoherent A).functor.obj ⟨F, hF⟩).cond, fun hF ↦ ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
  · exact (e.sheafCongrPrecoherent A).inverse.obj ⟨e.inverse.op ⋙ F, hF⟩ |>.cond
  · exact Functor.isoWhiskerRight e.op.unitIso F

/--
The coherent sheaf condition on an essentially small site can be checked after precomposing with
the equivalence with a small category.
-/
theorem precoherent_isSheaf_iff_of_essentiallySmall [EssentiallySmall C] (F : Cᵒᵖ ⥤ A) :
    IsSheaf (coherentTopology C) F ↔
      IsSheaf (coherentTopology (SmallModel C)) ((equivSmallModel C).inverse.op ⋙ F) :=
  precoherent_isSheaf_iff _ _ _

end Coherent

section Regular

variable [Preregular C]

/-- `Preregular` is preserved by equivalence of categories. -/
theorem preregular (e : C ≌ D) : Preregular D := e.inverse.reflects_preregular

instance [EssentiallySmall C] :
    Preregular (SmallModel C) := (equivSmallModel C).preregular

instance (e : C ≌ D) : haveI := preregular e
    e.inverse.IsDenseSubsite (regularTopology D) (regularTopology C) where
  functorPushforward_mem_iff := by
    rw [regularTopology.eq_induced e.inverse]
    simp only [Functor.mem_inducedTopology_sieves_iff, implies_true]

variable (A : Type*) [Category A]

/--
Equivalent preregular categories give equivalent regular toposes.
-/
@[simps!]
def sheafCongrPreregular (e : C ≌ D) : haveI := e.preregular
    Sheaf (regularTopology C) A ≌ Sheaf (regularTopology D) A := e.sheafCongr _ _ _

open Presheaf

/--
The regular sheaf condition can be checked after precomposing with the equivalence.
-/
theorem preregular_isSheaf_iff (e : C ≌ D) (F : Cᵒᵖ ⥤ A) : haveI := e.preregular
    IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF ↦ ((e.sheafCongrPreregular A).functor.obj ⟨F, hF⟩).cond, fun hF ↦ ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
  · exact (e.sheafCongrPreregular A).inverse.obj ⟨e.inverse.op ⋙ F, hF⟩ |>.cond
  · exact Functor.isoWhiskerRight e.op.unitIso F

/--
The regular sheaf condition on an essentially small site can be checked after precomposing with
the equivalence with a small category.
-/
theorem preregular_isSheaf_iff_of_essentiallySmall [EssentiallySmall C] (F : Cᵒᵖ ⥤ A) :
    IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology (SmallModel C))
    ((equivSmallModel C).inverse.op ⋙ F) := preregular_isSheaf_iff _ _ _

end Regular

end Equivalence

end CategoryTheory
