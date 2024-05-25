/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.CategoryTheory.Sites.Equivalence
/-!

# Coherence and equivalence of categories

This file proves that the coherent and regular topologies transfer nicely along equivalences of
categories.
-/

namespace CategoryTheory

variable {C : Type*} [Category C]

open GrothendieckTopology

namespace Equivalence

variable {D : Type*} [Category D]
variable (e : C ≌ D)

section Coherent

variable [Precoherent C]

/-- `Precoherent` is preserved by equivalence of categories. -/
theorem precoherent : Precoherent D := e.inverse.reflects_precoherent

instance [EssentiallySmall C] :
    Precoherent (SmallModel C) := (equivSmallModel C).precoherent

instance : haveI := precoherent e
    e.TransportsGrothendieckTopology (coherentTopology C) (coherentTopology D) where
  eq_inducedTopology := coherentTopology.eq_induced e.inverse

variable (A : Type*) [Category A]

/--
Equivalent precoherent categories give equivalent coherent toposes.
-/
@[simps!]
def sheafCongrPrecoherent : haveI := e.precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A := e.sheafCongr _ _ _

open Presheaf

/--
The coherent sheaf condition can be checked after precomposing with the equivalence.
-/
theorem precoherent_isSheaf_iff (F : Cᵒᵖ ⥤ A) : haveI := e.precoherent
    IsSheaf (coherentTopology C) F ↔ IsSheaf (coherentTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF ↦ ((e.sheafCongrPrecoherent A).functor.obj ⟨F, hF⟩).cond, fun hF ↦ ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
  · exact (e.sheafCongrPrecoherent A).inverse.obj ⟨e.inverse.op ⋙ F, hF⟩ |>.cond
  · exact isoWhiskerRight e.op.unitIso F

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

/-- `Preregular` is preserved by equivalence of categories. -/
theorem preregular : Preregular D := e.inverse.reflects_preregular

instance [EssentiallySmall C] :
    Preregular (SmallModel C) := (equivSmallModel C).preregular

instance : haveI := preregular e
    e.TransportsGrothendieckTopology (regularTopology C) (regularTopology D) where
  eq_inducedTopology := regularTopology.eq_induced e.inverse

variable (A : Type*) [Category A]

/--
Equivalent preregular categories give equivalent regular toposes.
-/
@[simps!]
def sheafCongrPreregular : haveI := e.preregular
    Sheaf (regularTopology C) A ≌ Sheaf (regularTopology D) A := e.sheafCongr _ _ _

open Presheaf

/--
The regular sheaf condition can be checked after precomposing with the equivalence.
-/
theorem preregular_isSheaf_iff (F : Cᵒᵖ ⥤ A) : haveI := e.preregular
    IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF ↦ ((e.sheafCongrPreregular A).functor.obj ⟨F, hF⟩).cond, fun hF ↦ ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
  · exact (e.sheafCongrPreregular A).inverse.obj ⟨e.inverse.op ⋙ F, hF⟩ |>.cond
  · exact isoWhiskerRight e.op.unitIso F

/--
The regular sheaf condition on an essentially small site can be checked after precomposing with
the equivalence with a small category.
-/
theorem preregular_isSheaf_iff_of_essentiallySmall [EssentiallySmall C] (F : Cᵒᵖ ⥤ A) :
    IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology (SmallModel C))
    ((equivSmallModel C).inverse.op ⋙ F) := preregular_isSheaf_iff _ _ _

end Regular

end Equivalence
