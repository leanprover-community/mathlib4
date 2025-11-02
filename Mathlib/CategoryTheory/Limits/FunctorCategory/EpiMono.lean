/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Monomorphisms and epimorphisms in functor categories

A natural transformation `f : F ⟶ G` between functors `K ⥤ C`
is a mono (resp. epi) iff for all `k : K`, `f.app k` is,
at least when `C` has pullbacks (resp. pushouts),
see `NatTrans.mono_iff_mono_app` and `NatTrans.epi_iff_epi_app`.

-/

universe v v' v'' u u' u''

namespace CategoryTheory

open Limits Functor

variable {K : Type u} [Category.{v} K] {C : Type u'} [Category.{v'} C]
  {D : Type u''} [Category.{v''} D] {F G : K ⥤ C} (f : F ⟶ G)
section

variable [HasPullbacks C]

instance [Mono f] (k : K) : Mono (f.app k) :=
  inferInstanceAs (Mono (((evaluation K C).obj k).map f))

lemma NatTrans.mono_iff_mono_app : Mono f ↔ ∀ (k : K), Mono (f.app k) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ mono_of_mono_app _⟩

instance [Mono f] (H : C ⥤ D) [H.PreservesMonomorphisms] :
    Mono (whiskerRight f H) := by
  have : ∀ X, Mono ((whiskerRight f H).app X) := by intros; dsimp; infer_instance
  apply NatTrans.mono_of_mono_app

end

section

variable [HasPushouts C]

instance [Epi f] (k : K) : Epi (f.app k) :=
  inferInstanceAs (Epi (((evaluation K C).obj k).map f))

lemma NatTrans.epi_iff_epi_app : Epi f ↔ ∀ (k : K), Epi (f.app k) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ epi_of_epi_app _⟩

instance [Epi f] (H : C ⥤ D) [H.PreservesEpimorphisms] :
    Epi (whiskerRight f H) := by
  have : ∀ X, Epi ((whiskerRight f H).app X) := by intros; dsimp; infer_instance
  apply NatTrans.epi_of_epi_app

end

end CategoryTheory
