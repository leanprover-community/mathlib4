/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.MorphismProperty.Pushouts
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory
import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Grothendieck abelian categories have enough injectives

TODO

-/

universe w v u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C]

namespace IsDetecting

lemma isIso_iff_of_mono {S : Set C} (hS : IsDetecting S)
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    IsIso f ↔ ∀ (s : S), Function.Surjective ((coyoneda.obj (op s.1)).map f) := by
  constructor
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    rintro ⟨A, _⟩
    exact (h A).2
  · intro hf
    apply hS
    rintro A hA g
    apply existsUnique_of_exists_of_unique
    · exact hf ⟨A, hA⟩ g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_mono f, h₁, h₂]

end IsDetecting

namespace Abelian

namespace IsGrothendieckAbelian

variable [Abelian C]  [IsGrothendieckAbelian.{w} C]

inductive generatingMonomorphisms (G : C) : MorphismProperty C
  | mono (X : Subobject G) : generatingMonomorphisms G X.arrow

variable (G : C)

abbrev generatingMonomorphismsPushouts := (generatingMonomorphisms G).pushouts

variable {G} (hG : IsSeparator G)

namespace transfiniteComposition

include hG

lemma exists_generatingMonomorphismsPushouts {X Y : C} (p : X ⟶ Y) [Mono p]
    (hp : ¬ IsIso p) :
    ∃ (X' : C) (i : X ⟶ X') (p' : X' ⟶ Y) (hi : generatingMonomorphismsPushouts G i)
      (hi' : ¬ IsIso i) (hp' : Mono p'), i ≫ p' = p := by
  rw [hG.isDetector.isIso_iff_of_mono] at hp
  simp only [coyoneda_obj_obj, Subtype.forall, Set.mem_singleton_iff, forall_eq,
    Function.Surjective, not_forall, not_exists] at hp
  obtain ⟨f, hf⟩ := hp
  let φ : pushout (pullback.fst f p) (pullback.snd f p) ⟶ Y :=
    pushout.desc f p pullback.condition
  refine ⟨pushout (pullback.fst f p) (pullback.snd f p), pushout.inr _ _, φ,
    ⟨_, _, _, (Subobject.underlyingIso _).hom ≫ pullback.snd _ _,
    pushout.inl _ _, ⟨Subobject.mk (pullback.fst f p)⟩,
    (IsPushout.of_hasPushout (pullback.fst f p) (pullback.snd f p)).flip.of_iso
      ((Subobject.underlyingIso _).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩, ?_, ?_, by simp [φ]⟩
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    obtain ⟨a, ha⟩ := (h G).2 (pushout.inl _ _)
    exact hf a (by simpa [φ] using ha =≫ φ)
  · sorry

end transfiniteComposition

end IsGrothendieckAbelian

end Abelian

end CategoryTheory
