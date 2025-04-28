/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.Morphisms
import Mathlib.CategoryTheory.Sites.Descent.CodescentData

/-!
# Effectiveness of descent

-/

universe t w v' v u' u

namespace CategoryTheory

open Opposite
namespace Presieve

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Presieve X)

@[simps]
def toCompatible (s : P.obj (op X)) :
    Subtype (FamilyOfElements.Compatible (P := P) (R := R)) where
  val Y f hf := P.map f.op s
  property Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ fac := by
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp, fac]

lemma isSheafFor_iff_bijective_toCompatible (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) :
    IsSheafFor P R ↔ Function.Bijective (toCompatible P R) := by
  constructor
  · intro h
    constructor
    · intro s₁ s₂ hs
      simp only [Subtype.ext_iff] at hs
      apply h.isSeparatedFor.ext
      intro Y f hf
      exact congr_fun (congr_fun (congr_fun hs Y) f) hf
    · rintro ⟨x, hx⟩
      exact ⟨h.amalgamate x hx, by ext; funext; apply h.valid_glue⟩
  · intro h x hx
    apply existsUnique_of_exists_of_unique
    · obtain ⟨s, hs⟩ := h.surjective ⟨x, hx⟩
      simp only [Subtype.ext_iff] at hs
      exact ⟨s, fun Y f hf ↦ congr_fun (congr_fun (congr_fun hs Y) f) hf⟩
    · intro s₁ s₂ hs₁ hs₂
      apply h.injective
      ext
      funext Y f hf
      simp only [toCompatible_coe, hs₁ f hf, hs₂ f hf]

end Presieve

open Limits Bicategory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

-- to be moved
instance {X Y : C} (f : X ⟶ Y) [IsIso f] (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}) :
    (F.map (.toLoc f)).IsEquivalence := by
  let e : F.obj (.mk X) ≌ F.obj (.mk Y) :=
    Equivalence.mk (F.map (.toLoc f)) (F.map (.toLoc (inv f)))
    ((F.mapId _).symm ≪≫ F.mapComp' f.toLoc (inv f).toLoc (𝟙 _) (by
        rw [← Quiver.Hom.comp_toLoc, IsIso.hom_inv_id, Quiver.Hom.id_toLoc]))
    ((F.mapComp' (inv f).toLoc f.toLoc (𝟙 _) (by
        rw [← Quiver.Hom.comp_toLoc, IsIso.inv_hom_id, Quiver.Hom.id_toLoc])).symm ≪≫ F.mapId _)
  exact e.isEquivalence_functor

/-- If `F` is a pseudofunctor from `(LocallyDiscrete Cᵒᵖ)` to `Cat` and `f i : X i ⟶ S`
is a family of morphisms in `C`, this is the type of family of objects in `F.obj (X i)`
equipped with a descent datum relative to the morphisms `f i`. -/
abbrev DescentData :=
  ((mapLocallyDiscrete (Over.forget S).op).comp F).CodescentData
    (fun (i : ι) ↦ .mk (op (Over.mk (f i))))

/-- The functor `F.obj (.mk (op S)) ⥤ F.DescentData f`. -/
def toDescentData : F.obj (.mk (op S)) ⥤ F.DescentData f :=
  ((mapLocallyDiscrete (Over.forget S).op).comp F).toCodescentDataOfIsInitial
    (fun (i : ι) ↦ .mk (op (Over.mk (f i)))) (.mk (op (Over.mk (𝟙 _))))
      (IsInitial.ofUniqueHom
        (fun Z ↦ .toLoc (Quiver.Hom.op (Over.homMk Z.as.unop.hom)))
        (fun ⟨⟨Z⟩⟩ ⟨⟨m⟩⟩ ↦ by
          dsimp at m
          congr
          ext
          simpa using Over.w m))

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
