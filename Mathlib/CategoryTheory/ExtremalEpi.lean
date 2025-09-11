/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi

/-!
# Extremal epimorphisms

An extremal epimorphism `p : X ⟶ Y` is an epimorphism which does not factor
through any proper subobject of `Y`. In case the category has equalizers,
we show that a morphism `p : X ⟶ Y` which does not factor through
any proper subobject of `Y` is automatically an epimorphism, and also
an extremal epimorphism. We also show that a strong epimorphism
is an extremal epimorphism, and that both notions coincide when
the category has pullbacks.

## References

* https://ncatlab.org/nlab/show/extremal+epimorphism

-/

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- An extremal epimorphism `f : X ⟶ Y` is an epimorphism which does not
factor through any proper subobject of `Y`. -/
class ExtremalEpi (f : X ⟶ Y) : Prop extends Epi f where
  isIso (f) {Z : C} (p : X ⟶ Z) (i : Z ⟶ Y) (fac : p ≫ i = f) [Mono i] : IsIso i

variable (f : X ⟶ Y)

lemma ExtremalEpi.subobject_eq_top [ExtremalEpi f]
    {A : Subobject Y} (hA : Subobject.Factors A f) : A = ⊤ := by
  rw [← Subobject.isIso_arrow_iff_eq_top]
  exact isIso f (Subobject.factorThru A f hA) _ (by simp)

lemma ExtremalEpi.mk_of_hasEqualizers [HasEqualizers C]
    (hf : ∀ ⦃Z : C⦄ (p : X ⟶ Z) (i : Z ⟶ Y) (_ : p ≫ i = f) [Mono i], IsIso i) :
    ExtremalEpi f where
  left_cancellation {Z} p q h := by
    have := hf (equalizer.lift f h) (equalizer.ι p q) (by simp)
    rw [← cancel_epi (equalizer.ι p q), equalizer.condition]
  isIso := by tauto

instance [StrongEpi f] : ExtremalEpi f where
  isIso {Z} p i fac _ := by
    have sq : CommSq p f i (𝟙 Y) := { }
    exact ⟨sq.lift, by simp [← cancel_mono i], by simp⟩

lemma extremalEpi_iff_strongEpi_of_hasPullbacks [HasPullbacks C] :
    ExtremalEpi f ↔ StrongEpi f := by
  refine ⟨fun _ ↦ ⟨inferInstance, fun A B i _ ↦ ⟨fun {t b} sq ↦ ⟨⟨?_⟩⟩⟩⟩,
    fun _ ↦ inferInstance⟩
  have := ExtremalEpi.isIso f (pullback.lift _ _ sq.w)
    (pullback.snd _ _) (by simp)
  exact
    { l := inv (pullback.snd i b) ≫ pullback.fst _ _
      fac_left := by
        rw [← cancel_mono i, sq.w, Category.assoc, Category.assoc]
        congr 1
        rw [← cancel_epi (pullback.snd i b), IsIso.hom_inv_id_assoc,
          pullback.condition]
      fac_right := by simp [pullback.condition] }

end CategoryTheory
