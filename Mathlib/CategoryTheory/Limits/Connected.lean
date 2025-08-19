/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Connected limits

A connected limit is a limit whose shape is a connected category.

We show that constant functors from a connected category have a limit
and a colimit. From this we deduce that a cocone `c` over a connected diagram
is a colimit cocone if and only if `colimMap c.ι` is an isomorphism (where
`c.ι : F ⟶ const c.pt` is the natural transformation that defines the
cocone).

We give examples of connected categories, and prove
that the functor given by `(X × -)` preserves any connected limit.
That is, any limit of shape `J` where `J` is a connected category is
preserved by the functor `(X × -)`.
-/


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

section Const

namespace Limits

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C] (X : C)

section

variable (J)

/-- The obvious cone of a constant functor. -/
@[simps]
def constCone : Cone ((Functor.const J).obj X) where
  pt := X
  π := 𝟙 _

/-- The obvious cocone of a constant functor. -/
@[simps]
def constCocone : Cocone ((Functor.const J).obj X) where
  pt := X
  ι := 𝟙 _

variable [IsConnected J]

/-- When `J` is a connected category, the limit of a
constant functor `J ⥤ C` with value `X : C` identifies to `X`. -/
def isLimitConstCone : IsLimit (constCone J X) where
  lift s := s.π.app (Classical.arbitrary _)
  fac s j := by
    dsimp
    rw [comp_id]
    exact constant_of_preserves_morphisms _
      (fun _ _ f ↦ by simpa using s.w f) _ _
  uniq s m hm := by simpa using hm (Classical.arbitrary _)

/-- When `J` is a connected category, the colimit of a
constant functor `J ⥤ C` with value `X : C` identifies to `X`. -/
def isColimitConstCocone : IsColimit (constCocone J X) where
  desc s := s.ι.app (Classical.arbitrary _)
  fac s j := by
    dsimp
    rw [id_comp]
    exact constant_of_preserves_morphisms _
      (fun _ _ f ↦ by simpa using (s.w f).symm) _ _
  uniq s m hm := by simpa using hm (Classical.arbitrary _)

instance hasLimit_const_of_isConnected : HasLimit ((Functor.const J).obj X) :=
  ⟨_, isLimitConstCone J X⟩

instance hasColimit_const_of_isConnected : HasColimit ((Functor.const J).obj X) :=
  ⟨_, isColimitConstCocone J X⟩

end

section

variable [IsConnected J]

/-- If `J` is connected, `F : J ⥤ C` and `c` is a cone on `F`, then to check that `c` is a
limit it is sufficient to check that `limMap c.π` is an isomorphism. The converse is also
true, see `Cone.isLimit_iff_isIso_limMap_π`. -/
def Cone.isLimitOfIsIsoLimMapπ {F : J ⥤ C} [HasLimit F] (c : Cone F)
    [IsIso (limMap c.π)] : IsLimit c := by
  refine IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext ((asIso (limMap c.π)).symm ≪≫
    (limit.isLimit _).conePointUniqueUpToIso (isLimitConstCone J c.pt)) ?_)
  intro j
  simp only [limit.cone_x, Functor.const_obj_obj, limit.cone_π, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, assoc, IsIso.eq_inv_comp, limMap_π]
  congr 1
  simp [← Iso.inv_comp_eq_id]

theorem IsLimit.isIso_limMap_π {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c) :
    IsIso (limMap c.π) := by
  suffices limMap c.π = ((limit.isLimit _).conePointUniqueUpToIso (isLimitConstCone J c.pt) ≪≫
      hc.conePointUniqueUpToIso (limit.isLimit _)).hom by
    rw [this]; infer_instance
  ext j
  simp only [limMap_π, Functor.const_obj_obj, limit.cone_x, constCone_pt, Iso.trans_hom, assoc,
    limit.conePointUniqueUpToIso_hom_comp]
  congr 1
  simp [← Iso.inv_comp_eq_id]

theorem Cone.isLimit_iff_isIso_limMap_π {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    Nonempty (IsLimit c) ↔ IsIso (limMap c.π) :=
  ⟨fun ⟨h⟩ ↦ IsLimit.isIso_limMap_π h, fun _ ↦ ⟨c.isLimitOfIsIsoLimMapπ⟩⟩

/-- If `J` is connected, `F : J ⥤ C` and `C` is a cocone on `F`, then to check that `c` is a
colimit it is sufficient to check that `colimMap c.ι` is an isomorphism. The converse is also
true, see `Cocone.isColimit_iff_isIso_colimMap_ι`. -/
def Cocone.isColimitOfIsIsoColimMapι {F : J ⥤ C} [HasColimit F] (c : Cocone F)
    [IsIso (colimMap c.ι)] : IsColimit c :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (asIso (colimMap c.ι) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone J c.pt)) (by simp))

theorem IsColimit.isIso_colimMap_ι {F : J ⥤ C} [HasColimit F] {c : Cocone F} (hc : IsColimit c) :
    IsIso (colimMap c.ι) := by
  suffices colimMap c.ι = ((colimit.isColimit _).coconePointUniqueUpToIso hc ≪≫
      (isColimitConstCocone J c.pt).coconePointUniqueUpToIso (colimit.isColimit _)).hom by
    rw [this]; infer_instance
  ext j
  simp only [ι_colimMap, Functor.const_obj_obj, colimit.cocone_x, Iso.trans_hom,
    colimit.comp_coconePointUniqueUpToIso_hom_assoc]
  congr 1
  simp [← Iso.comp_inv_eq_id]

theorem Cocone.isColimit_iff_isIso_colimMap_ι {F : J ⥤ C} [HasColimit F] (c : Cocone F) :
    Nonempty (IsColimit c) ↔ IsIso (colimMap c.ι) :=
  ⟨fun ⟨h⟩ ↦ IsColimit.isIso_colimMap_ι h, fun _ ↦ ⟨c.isColimitOfIsIsoColimMapι⟩⟩

end

end Limits

end Const

section Examples

instance widePullbackShape_connected (J : Type v₁) : IsConnected (WidePullbackShape J) := by
  apply IsConnected.of_induct
  · introv hp t
    cases j
    · exact hp
    · rwa [t (WidePullbackShape.Hom.term _)]

instance widePushoutShape_connected (J : Type v₁) : IsConnected (WidePushoutShape J) := by
  apply IsConnected.of_induct
  · introv hp t
    cases j
    · exact hp
    · rwa [← t (WidePushoutShape.Hom.init _)]

instance parallelPairInhabited : Inhabited WalkingParallelPair :=
  ⟨WalkingParallelPair.one⟩

instance parallel_pair_connected : IsConnected WalkingParallelPair := by
  apply IsConnected.of_induct
  · introv _ t
    cases j
    · rwa [t WalkingParallelPairHom.left]
    · assumption

end Examples

variable {C : Type u₂} [Category.{v₂} C]
variable [HasBinaryProducts C]
variable {J : Type v₂} [SmallCategory J]

namespace ProdPreservesConnectedLimits

/-- (Impl). The obvious natural transformation from (X × K -) to K. -/
@[simps]
def γ₂ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ K where app _ := Limits.prod.snd

/-- (Impl). The obvious natural transformation from (X × K -) to X -/
@[simps]
def γ₁ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ (Functor.const J).obj X where
  app _ := Limits.prod.fst

/-- (Impl).
Given a cone for (X × K -), produce a cone for K using the natural transformation `γ₂` -/
@[simps]
def forgetCone {X : C} {K : J ⥤ C} (s : Cone (K ⋙ prod.functor.obj X)) : Cone K where
  pt := s.pt
  π := s.π ≫ γ₂ X

end ProdPreservesConnectedLimits

open ProdPreservesConnectedLimits

/-- The functor `(X × -)` preserves any connected limit.
Note that this functor does not preserve the two most obvious disconnected limits - that is,
`(X × -)` does not preserve products or terminal object, eg `(X ⨯ A) ⨯ (X ⨯ B)` is not isomorphic to
`X ⨯ (A ⨯ B)` and `X ⨯ 1` is not isomorphic to `1`.
-/
lemma prod_preservesConnectedLimits [IsConnected J] (X : C) :
    PreservesLimitsOfShape J (prod.functor.obj X) where
  preservesLimit {K} :=
    { preserves := fun {c} l ↦ ⟨{
          lift := fun s ↦
            prod.lift (s.π.app (Classical.arbitrary _) ≫ Limits.prod.fst) (l.lift (forgetCone s))
          fac := fun s j ↦ by
            apply Limits.prod.hom_ext
            · erw [assoc, limMap_π, comp_id, limit.lift_π]
              exact (nat_trans_from_is_connected (s.π ≫ γ₁ X) j (Classical.arbitrary _)).symm
            · simp
          uniq := fun s m L ↦ by
            apply Limits.prod.hom_ext
            · erw [limit.lift_π, ← L (Classical.arbitrary J), assoc, limMap_π, comp_id]
              rfl
            · rw [limit.lift_π]
              apply l.uniq (forgetCone s)
              intro j
              simp [← L j] }⟩ }

end CategoryTheory
