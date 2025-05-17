/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Effectiveness of descent

-/

universe t w v' v u' u

namespace CategoryTheory

open Opposite Limits Bicategory

-- to be moved
namespace Presieve

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (P : Cᵒᵖ ⥤ Type w) {S : C} {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

@[simps]
def Arrows.toCompatible (s : P.obj (op S)) :
    Subtype (Arrows.Compatible P f) where
  val i := P.map (f i).op s
  property i j Y pi pj w := by simp only [← FunctorToTypes.map_comp_apply, ← op_comp, w]

lemma isSheafFor_ofArrows_iff_bijective_toCompatible :
    IsSheafFor P (ofArrows _ f) ↔ Function.Bijective (Arrows.toCompatible P f) := by
  constructor
  · intro h
    constructor
    · intro s₁ s₂ hs
      simp only [Subtype.ext_iff] at hs
      apply h.isSeparatedFor.ext
      rintro _ _ ⟨i⟩
      exact congr_fun hs i
    · rw [isSheafFor_arrows_iff] at h
      rintro ⟨x, hx⟩
      obtain ⟨s, hs⟩ := (h x hx).exists
      exact ⟨s, by aesop⟩
  · rw [isSheafFor_arrows_iff]
    intro h x hx
    apply existsUnique_of_exists_of_unique
    · obtain ⟨s, hs⟩ := h.surjective ⟨x, hx⟩
      simp only [Subtype.ext_iff] at hs
      exact ⟨s, congr_fun hs⟩
    · intro s₁ s₂ hs i
      apply h.injective (by aesop)

lemma isSheaf_iff_isSheafFor_ofArrows :
    Presieve.IsSheaf J P ↔ ∀ ⦃ι : Type max u v⦄ ⦃S : C⦄ ⦃X : ι → C⦄ (f : ∀ i, X i ⟶ S)
        (_ : (Sieve.ofArrows _ f) ∈ J S),
        IsSheafFor P (ofArrows _ f) := by
  constructor
  · intro h ι S X f hf
    rw [isSheafFor_iff_generate]
    exact h _ hf
  · intro h S R hR
    let X (i : R.arrows.category) : C := i.1.left
    let f (i : R.arrows.category) : X i ⟶ S := i.1.hom
    have : Presieve.ofArrows _ f = R := by
      apply le_antisymm
      · rintro _ _ ⟨i⟩
        exact i.2
      · intro _ g hg
        rw [Sieve.arrows] at hg
        exact ⟨(⟨Over.mk g, hg⟩ : R.arrows.category)⟩
    rw [← this]
    apply h
    simpa [Sieve.ofArrows, this]

end Presieve

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

/-- The property that a pseudofunctor `(LocallyDiscrete Cᵒᵖ)` to `Cat` has
effective descent relative to a family of morphisms `f i : X i ⟶ S` in `C`. -/
abbrev HasEffectiveDescentRelativeTo : Prop := (F.toDescentData f).IsEquivalence

open LocallyDiscreteOpToCat

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
    rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompatible]
    let T := Subtype (Presieve.Arrows.Compatible (P := F.presheafHom M N)
      (B := Over.mk (𝟙 S)) (X := (fun (i : ι) ↦ Over.mk (f i)))
      (fun (i : ι) ↦ Over.homMk (f i)))
    let α : ((F.toDescentData f).obj M ⟶ (F.toDescentData f).obj N) ≃ T := {
      toFun φ := ⟨fun i ↦ φ.hom i, fun i j Z gi gj w ↦ by
        have := φ.comm Z.hom gi.left gj.left (Over.w gi) (Over.w gj)
        simp only [Functor.id_obj, toDescentData, DescentData.ofObj_obj,
          DescentData.ofObj_hom, Category.assoc] at this
        rw [← cancel_mono ((F.mapComp' (f j).op.toLoc gj.left.op.toLoc
          Z.hom.op.toLoc (by simp [← Over.w gj])).hom.app N)]
        simp [pullHom, this] ⟩
      invFun ψ :=
        { hom i := ψ.1 i
          comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
            have this := ψ.2 i₁ i₂ (Over.mk q) (Over.homMk f₁) (Over.homMk f₂)
              (by aesop)
            dsimp at this ⊢
            rw [map_eq_pullHom (ψ.1 i₁) f₁ q q (by aesop) (by aesop),
              map_eq_pullHom (ψ.1 i₂) f₂ q q (by aesop) (by aesop), this]
            simp [toDescentData] }
      left_inv _ := rfl
      right_inv _ := rfl
    }
    let β : (M ⟶ N) ≃ (F.presheafHom M N).obj (op (Over.mk (𝟙 S))) :=
      Equiv.ofBijective _ (Functor.FullyFaithful.map_bijective
        (Functor.FullyFaithful.ofFullyFaithful (F.map (.toLoc (𝟙 (op S))))) M N)
    have : Function.comp α (F.toDescentData f).map =
      (Presieve.Arrows.toCompatible _ _).comp β := by
        ext φ i
        simp [α, β, pullHom, toDescentData]
    rw [← Function.Bijective.of_comp_iff' α.bijective, this,
      Function.Bijective.of_comp_iff _ β.bijective]

class IsStack (J : GrothendieckTopology C) : Prop where
  hasEffectiveDescentRelativeTo_of_sieve_mem {S : C} (U : Sieve S) (hU : U ∈ J S) :
    F.HasEffectiveDescentRelativeTo (f := fun (i : U.arrows.category) ↦ i.obj.hom)

lemma hasEffectiveDescentRelativeTo_of_sieve_mem (J : GrothendieckTopology C)
    [F.IsStack J]
    {S : C} (U : Sieve S) (hU : U ∈ J S) :
    F.HasEffectiveDescentRelativeTo (f := fun (i : U.arrows.category) ↦ i.obj.hom) :=
  IsStack.hasEffectiveDescentRelativeTo_of_sieve_mem _ hU

instance (J : GrothendieckTopology C) [F.IsStack J] :
    F.IsPrestack J where
  isSheaf {S} M N := by
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_iff_isSheafFor_ofArrows]
    intro ι X Y f hf
    sorry

end Pseudofunctor

end CategoryTheory
