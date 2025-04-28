/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Effectiveness of descent

-/

universe t v' v u' u

namespace CategoryTheory

open Opposite

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The property that a pseudofunctor `(LocallyDiscrete Cᵒᵖ)` to `Cat` has
effective descent relative to a family of morphisms `f i : X i ⟶ S` in `C`. -/
abbrev HasEffectiveDescentRelativeTo : Prop := (F.toDescentData f).IsEquivalence

lemma toDescentData_fullyFaithful_iff :
    Nonempty (F.toDescentData f).FullyFaithful ↔
      ∀ (M N : F.obj (.mk (op S))),
        Presieve.IsSheafFor (F.presheafHom M N)
          (Presieve.ofArrows (X := Over.mk (𝟙 S)) (fun (i : ι) ↦ Over.mk (f i))
            (fun (i : ι) ↦ Over.homMk (f i))) := by
  trans ∀ (M N : F.obj (.mk (op S))),
      Function.Bijective ((F.toDescentData f).map : (M ⟶ N) → _)
  · exact ⟨fun ⟨h⟩ ↦ h.map_bijective, fun h ↦ ⟨{
        preimage {M N}:= (Equiv.ofBijective _ (h M N)).invFun
        preimage_map := (Equiv.ofBijective _ (h _ _)).left_inv
        map_preimage := (Equiv.ofBijective _ (h _ _)).right_inv
      }⟩⟩
  · refine forall_congr' (fun M ↦ forall_congr' (fun N ↦ ?_))
    -- instead we need a variant of `isSheafFor_arrows_iff`
    rw [Presieve.isSheafFor_iff_bijective_toCompatible]
    let R := (Presieve.ofArrows (X := Over.mk (𝟙 S)) (fun (i : ι) ↦ Over.mk (f i))
            (fun (i : ι) ↦ Over.homMk (f i)))
    let T := Subtype (Presieve.FamilyOfElements.Compatible (P := F.presheafHom M N) (R := R))
    let α : ((F.toDescentData f).obj M ⟶ (F.toDescentData f).obj N) ≃ T := {
      toFun g := ⟨fun Y f hf ↦ by
        sorry, sorry⟩
      invFun := sorry
      left_inv := sorry
      right_inv := sorry
    }
    let β : (M ⟶ N) ≃ (F.presheafHom M N).obj (op (Over.mk (𝟙 S))) :=
      Equiv.ofBijective _ (Functor.FullyFaithful.map_bijective
        (Functor.FullyFaithful.ofFullyFaithful (F.map (.toLoc (𝟙 (op S))))) M N)
    have : Function.comp α (F.toDescentData f).map =
      (Presieve.toCompatible (F.presheafHom M N) R).comp β := sorry
    rw [← Function.Bijective.of_comp_iff' α.bijective, this,
      Function.Bijective.of_comp_iff _ β.bijective]

class HasEffectiveDescent (J : GrothendieckTopology C) : Prop where
  hasEffectiveDescentRelativeTo_of_sieve_mem {S : C} (U : Sieve S) (hU : U ∈ J S) :
    F.HasEffectiveDescentRelativeTo (f := fun (i : U.arrows.category) ↦ i.obj.hom)

lemma hasEffectiveDescentRelativeTo_of_sieve_mem (J : GrothendieckTopology C)
    [F.HasEffectiveDescent J]
    {S : C} (U : Sieve S) (hU : U ∈ J S) :
    F.HasEffectiveDescentRelativeTo (f := fun (i : U.arrows.category) ↦ i.obj.hom) :=
  HasEffectiveDescent.hasEffectiveDescentRelativeTo_of_sieve_mem _ hU

instance (J : GrothendieckTopology C) [F.HasEffectiveDescent J] :
    F.HasDescentOfMorphisms J where
  isSheaf {S} M N := by
    rw [isSheaf_iff_isSheaf_of_type]
    rintro ⟨X, ⟨⟩, p : X ⟶ S⟩ U hU
    obtain ⟨U : Sieve X, rfl⟩ := (Sieve.overEquiv _).symm.surjective U
    simp only [J.mem_over_iff, Equiv.apply_symm_apply] at hU
    sorry

end Pseudofunctor

end CategoryTheory
