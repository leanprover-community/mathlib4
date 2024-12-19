/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.MorphismProperty.Pushouts
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Grothendieck abelian categories have enough injectives

TODO

-/

universe w v u

namespace CategoryTheory

open Category Opposite Limits

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

variable {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {j : X ⟶ Y} {g : B ⟶ Y}
  [HasBinaryBiproduct B X]

namespace CommSq

variable (h : CommSq f i j g)

@[simps]
noncomputable def shortComplex : ShortComplex C where
  f := biprod.lift i (-f)
  g := biprod.desc g j
  zero := by simp [h.w]

end CommSq

namespace IsPushout

variable (h : IsPushout f i j g)

noncomputable def isColimitCokernelCoforkShortComplex :
    IsColimit (CokernelCofork.ofπ _ h.shortComplex.zero) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun b hb ↦ h.desc (biprod.inr ≫ b) (biprod.inl ≫ b) (by
      dsimp at hb
      simp only [biprod.lift_eq, Preadditive.neg_comp,
        Preadditive.sub_comp, assoc, ← sub_eq_add_neg, sub_eq_zero] at hb
      exact hb.symm)) (by aesop_cat) (fun _ _ _ hm ↦ by
        refine h.hom_ext (by simpa using biprod.inr ≫= hm)
          (by simpa using biprod.inl ≫= hm))

lemma epi_shortComplex_g : Epi h.shortComplex.g := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro _ b hb
  exact Cofork.IsColimit.hom_ext h.isColimitCokernelCoforkShortComplex
    (by simpa using hb)

end IsPushout

end Preadditive

section Abelian

namespace IsPushout

variable [Abelian C] {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {j : X ⟶ Y} {g : B ⟶ Y}

lemma shortComplex_exact (h : IsPushout f i j g) : h.shortComplex.Exact :=
  h.shortComplex.exact_of_g_is_cokernel
    h.isColimitCokernelCoforkShortComplex

lemma hom_eq_add_up_to_refinements (h : IsPushout f i j g) {T : C} (y : T ⟶ Y) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (b : T' ⟶ B) (x : T' ⟶ X),
      π ≫ y = b ≫ g + x ≫ j := by
  have := h.epi_shortComplex_g
  obtain ⟨T', π, _, z, hz⟩ := surjective_up_to_refinements_of_epi h.shortComplex.g y
  refine ⟨T', π, inferInstance, z ≫ biprod.fst, z ≫ biprod.snd, ?_⟩
  simp only [hz, assoc, ← Preadditive.comp_add]
  congr
  aesop_cat

lemma mono_of_isPushout_of_isPullback_of_mono {A B X Y : C}
    {f : A ⟶ X} {i : A ⟶ B} {j : X ⟶ Y} {g : B ⟶ Y}
    (h₁ : IsPushout f i j g) {Z : C} {j' : X ⟶ Z} {g' : B ⟶ Z}
    (h₂ : IsPullback f i j' g') (k : Y ⟶ Z)
    (fac₁ : j ≫ k = j') (fac₂ : g ≫ k = g') [Mono i] [Mono j'] : Mono k :=
  Preadditive.mono_of_cancel_zero _ (fun {T₀} y hy ↦ by
    obtain ⟨T₁, π, _, b, x, eq⟩ := hom_eq_add_up_to_refinements h₁ y
    have fac₃ : x ≫ j' = (-b) ≫ g' := by
      rw [Preadditive.neg_comp, ← add_eq_zero_iff_eq_neg, ← fac₂, ← fac₁,
        ← assoc, ← assoc, ← Preadditive.add_comp,
        add_comm, ← eq, assoc, hy, comp_zero]
    have fac₃ : (-x) ≫ j' = b ≫ g' := by
      rw [Preadditive.neg_comp, neg_eq_iff_add_eq_zero, add_comm, ← fac₂, ← fac₁,
        ← assoc, ← assoc, ← Preadditive.add_comp, ← eq, assoc, hy, comp_zero]
    obtain ⟨x', hx'⟩ : ∃ x', π ≫ y = x' ≫ j := by
      refine ⟨x + h₂.lift (-x) b fac₃ ≫ f, ?_⟩
      rw [eq, Preadditive.add_comp, assoc, h₁.w, IsPullback.lift_snd_assoc, add_comm]
    rw [← cancel_epi π, comp_zero, reassoc_of% hx', fac₁] at hy
    obtain rfl := zero_of_comp_mono _ hy
    rw [zero_comp] at hx'
    rw [← cancel_epi π, hx', comp_zero])

end IsPushout

end Abelian

namespace Abelian

variable [Abelian C]


end Abelian

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

variable [Abelian C]

inductive generatingMonomorphisms (G : C) : MorphismProperty C
  | mono (X : Subobject G) : generatingMonomorphisms G X.arrow

variable (G : C)

abbrev generatingMonomorphismsPushouts := (generatingMonomorphisms G).pushouts

variable {G} (hG : IsSeparator G)

namespace transfiniteComposition

include hG

lemma exists_generatingMonomorphismsPushouts {X Y : C} (p : X ⟶ Y) [Mono p]
    (hp : ¬ IsIso p) :
    ∃ (X' : C) (i : X ⟶ X') (p' : X' ⟶ Y) (_ : generatingMonomorphismsPushouts G i)
      (_ : ¬ IsIso i) (_ : Mono p'), i ≫ p' = p := by
  rw [hG.isDetector.isIso_iff_of_mono] at hp
  simp only [coyoneda_obj_obj, Subtype.forall, Set.mem_singleton_iff, forall_eq,
    Function.Surjective, not_forall, not_exists] at hp
  obtain ⟨f, hf⟩ := hp
  let φ : pushout (pullback.fst p f) (pullback.snd p f) ⟶ Y :=
    pushout.desc p f pullback.condition
  refine ⟨pushout (pullback.fst p f) (pullback.snd p f), pushout.inl _ _, φ,
    ⟨_, _, _, (Subobject.underlyingIso _).hom ≫ pullback.fst _ _,
    pushout.inr _ _, ⟨Subobject.mk (pullback.snd p f)⟩,
    (IsPushout.of_hasPushout (pullback.fst p f) (pullback.snd p f)).of_iso
      ((Subobject.underlyingIso _).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩, ?_, ?_, by simp [φ]⟩
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    obtain ⟨a, ha⟩ := (h G).2 (pushout.inr _ _)
    exact hf a (by simpa [φ] using ha =≫ φ)
  · exact (IsPushout.of_hasPushout _ _).mono_of_isPushout_of_isPullback_of_mono
      (IsPullback.of_hasPullback p f) φ (by simp [φ]) (by simp [φ])

variable [IsGrothendieckAbelian.{w} C]

end transfiniteComposition

end IsGrothendieckAbelian

end Abelian

end CategoryTheory
