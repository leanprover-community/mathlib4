/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton
-/
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Images in the category of types

In this file, it is shown that the category of types has categorical images,
and that these agree with the range of a function.

-/

universe v u

namespace CategoryTheory.Limits.Types

variable {α β : Type u} (f : α ⟶ β)

section

-- implementation of `HasImage`
/-- the image of a morphism in Type is just `Set.range f` -/
def Image : Type u :=
  Set.range f

instance [Inhabited α] : Inhabited (Image f) where default := ⟨f default, ⟨_, rfl⟩⟩

/-- the inclusion of `Image f` into the target -/
def Image.ι : Image f ⟶ β :=
  Subtype.val

instance : Mono (Image.ι f) :=
  (mono_iff_injective _).2 Subtype.val_injective

variable {f}

/-- the universal property for the image factorisation -/
noncomputable def Image.lift (F' : MonoFactorisation f) : Image f ⟶ F'.I :=
  (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : Image f → F'.I)

theorem Image.lift_fac (F' : MonoFactorisation f) : Image.lift F' ≫ F'.m = Image.ι f := by
  funext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl

end

/-- the factorisation of any morphism in Type through a mono. -/
def monoFactorisation : MonoFactorisation f where
  I := Image f
  m := Image.ι f
  e := Set.rangeFactorization f

/-- the factorisation through a mono has the universal property of the image. -/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := Image.lift
  lift_fac := Image.lift_fac

instance : HasImage f :=
  HasImage.mk ⟨_, isImage f⟩

instance : HasImages (Type u) where
  has_image := by infer_instance

instance : HasImageMaps (Type u) where
  has_image_map {f g} st :=
    HasImageMap.transport st (monoFactorisation f.hom) (isImage g.hom)
      (fun x => ⟨st.right x.1, ⟨st.left (Classical.choose x.2), by
        have p := st.w
        replace p := congr_fun p (Classical.choose x.2)
        simp only [Functor.id_obj, Functor.id_map, types_comp_apply] at p
        rw [p, Classical.choose_spec x.2]⟩⟩) rfl

variable {F : ℕᵒᵖ ⥤ Type u} {c : Cone F}
  (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))

private noncomputable def limitOfSurjectionsSurjective.preimage
    (a : F.obj ⟨0⟩) : (n : ℕ) → F.obj ⟨n⟩
    | 0 => a
    | n+1 => (hF n (preimage a n)).choose

include hF in
open limitOfSurjectionsSurjective in
/-- Auxiliary lemma. Use `limit_of_surjections_surjective` instead. -/
lemma surjective_π_app_zero_of_surjective_map_aux :
    Function.Surjective ((limitCone F).π.app ⟨0⟩) := by
  intro a
  refine ⟨⟨fun ⟨n⟩ ↦ preimage hF a n, ?_⟩, rfl⟩
  intro ⟨n⟩ ⟨m⟩ ⟨⟨⟨(h : m ≤ n)⟩⟩⟩
  induction h with
  | refl =>
    erw [CategoryTheory.Functor.map_id, types_id_apply]
  | @step p h ih =>
    rw [← ih]
    have h' : m ≤ p := h
    erw [CategoryTheory.Functor.map_comp (f := (homOfLE (Nat.le_succ p)).op) (g := (homOfLE h').op),
      types_comp_apply, (hF p _).choose_spec]
    rfl

/--
Given surjections `⋯ ⟶ Xₙ₊₁ ⟶ Xₙ ⟶ ⋯ ⟶ X₀`, the projection map `lim Xₙ ⟶ X₀` is surjective.
-/
lemma surjective_π_app_zero_of_surjective_map
    (hc : IsLimit c)
    (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) :
    Function.Surjective (c.π.app ⟨0⟩) := by
  let i := hc.conePointUniqueUpToIso (limitConeIsLimit F)
  have : c.π.app ⟨0⟩ = i.hom ≫ (limitCone F).π.app ⟨0⟩ := by simp [i]
  rw [this]
  apply Function.Surjective.comp
  · exact surjective_π_app_zero_of_surjective_map_aux hF
  · rw [← epi_iff_surjective]
    infer_instance

end CategoryTheory.Limits.Types
