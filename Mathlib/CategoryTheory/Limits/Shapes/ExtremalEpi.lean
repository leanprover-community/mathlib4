/-
Copyright (c) 2020 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
import Mathlib.CategoryTheory.Category.Factorisation
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.MorphismProperty.MonoFactorization

/-!
# Extremal epimorphisms

In this file, we define extremal epimorphisms. A extremal epimorphism is an epimorphism `f`
such that it doesn't factor through any non-trivial monomorphism.
One of the main interests in this notion is that if a category with equalizers has images
`f = e ≫ m`, then `e` is an extremal epimorphism.

We also show that all strong epimorphisms are extremal, the converse holds when appropriate
pullbacks exist.

## References

* <https://ncatlab.org/nlab/show/extremal+epimorphism>
-/

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]
variable {P Q : C}

-- A extremal epi `f` is an epi that doesn't factor through any non-trivial monomorphism.
class ExtremalEpi (f : P ⟶ Q) : Prop where
  -- The epimorphism condition on `f`
  epi : Epi f := by infer_instance
  -- The left lifting property with respect to all monomorphism -/
  isIso_of_monoFactor : ∀ (d : MonoFactorisation f), IsIso d.m

instance (priority := 100) epi_of_extremalEpi (f : P ⟶ Q) [ExtremalEpi f] : Epi f :=
  ExtremalEpi.epi

section

variable {R : C} (f : P ⟶ Q) (g : Q ⟶ R)

/-- An isomorphism is in particular an extremal epimorphism. -/
instance (priority := 100) extremalEpi_of_isIso [IsIso f] : ExtremalEpi f where
  isIso_of_monoFactor d := by
    constructor
    use inv f ≫ d.e; constructor
    · apply (cancel_mono d.m (g := d.m ≫ inv f ≫ d.e) (h := 𝟙 _)).1; aesop_cat
    · aesop_cat

theorem ExtremalEpi.of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) [h : ExtremalEpi f] : ExtremalEpi g :=
  { epi := by rw [Arrow.iso_w' e]; infer_instance
    isIso_of_monoFactor d := by
        let fac : MonoFactorisation f := ⟨d.I, d.m ≫ e.inv.right, e.hom.left ≫ d.e, by aesop_cat⟩
        have := h.isIso_of_monoFactor fac
        exact IsIso.of_isIso_comp_right d.m e.inv.right }

theorem ExtremalEpi.iff_of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) : ExtremalEpi f ↔ ExtremalEpi g := by
  constructor <;> intro
  exacts [ExtremalEpi.of_arrow_iso e, ExtremalEpi.of_arrow_iso e.symm]

end

/-- A extremal epimorphism that is a monomorphism is an isomorphism. -/
theorem isIso_of_mono_of_extremalEpi (f : P ⟶ Q) [Mono f] [ExtremalEpi f] : IsIso f :=
  ExtremalEpi.isIso_of_monoFactor ⟨P, f, 𝟙 _, id_comp f⟩

section

variable (C)

/-- A extremal epi category is a category in which every epimorphism is extremal. -/
class ExtremalEpiCategory : Prop where
  /-- A extremal epi category is a category in which every epimorphism is extremal. -/
  extremalEpi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], ExtremalEpi f

end

theorem extremalEpi_of_epi [ExtremalEpiCategory C] (f : P ⟶ Q) [Epi f] : ExtremalEpi f :=
  ExtremalEpiCategory.extremalEpi_of_epi _

section

attribute [local instance] extremalEpi_of_epi

instance (priority := 100) balanced_of_extremalEpiCategory [ExtremalEpiCategory C] :
    Balanced C where
  isIso_of_mono_of_epi _ _ _ := isIso_of_mono_of_extremalEpi _

end

section

-- Strong epimorphisms are extremal
instance extremalEpi_of_strongEpi {X Y : C} (f : X ⟶ Y) [StrongEpi f] : ExtremalEpi f where
  isIso_of_monoFactor d := by
    let square : CommSq d.e f d.m (𝟙 _) := ⟨by rw [d.fac]; aesop_cat⟩
    have : IsSplitEpi d.m := .mk' ⟨square.lift , square.fac_right⟩
    apply isIso_of_mono_of_isSplitEpi d.m

lemma hasLift_of_extremalEpi {X Y A B : C} {f : X ⟶ Y} [ExtremalEpi f] {g : A ⟶ B} [Mono g]
    {i : X ⟶ A} {h : Y ⟶ B} [HasPullback h g] (sq : CommSq i f g h) : sq.HasLift := by
  let l := pullback.lift f i (w := sq.w.symm)
  let fs := pullback.fst h g
  let sn := pullback.snd h g
  have isIso_f := ExtremalEpi.isIso_of_monoFactor
    ⟨pullback h g, fs, pullback.lift f i (w := sq.w.symm), pullback.lift_fst f i (w := sq.w.symm)⟩
  have faa : f ≫ inv fs = l := by aesop_cat
  refine CommSq.HasLift.mk' ⟨inv fs ≫ sn , ?_, ?_⟩
  · rw [← assoc, faa, pullback.lift_snd f i (w := sq.w.symm)]
  · rw [assoc, (cancel_epi fs (g := inv fs ≫ sn ≫ g)).1 (by simp; rw [pullback.condition])]

--  For a category with pullbacks, extremal epimorphisms are strong
instance strongEpi_of_extremalEpi [HasPullbacks C] {X Y : C} (f : X ⟶ Y) [ExtremalEpi f] :
    StrongEpi f where
  llp A B g := .mk fun sq ↦ hasLift_of_extremalEpi sq

end

end CategoryTheory
