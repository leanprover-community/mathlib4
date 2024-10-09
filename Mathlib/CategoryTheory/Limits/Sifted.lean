/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
/-!
# Sifted categories

A category `C` is Sifted if `C` is nonempty and the diagonal functor `C ⥤ C × C` is final.
Sifted categories can be caracterized as those such that the colimit functor `(C ⥤ Type) ⥤ Type `
preserves finite products. We achieve this characterization in this file, as well as providing some
API to produce `IsSifted` instances.

## Main results
- `colimPreservesFiniteProductsOfIsSifted`: The `Type`-valued colimit functor for sifted diagrams
  preserves finite products.
- `IsSiftedOfColimitPreservesFiniteProducts`: The converse: if the `Type`-valued colimit functor
  preserves finite producs, the category is sifted.
- `IsSiftedOfFinalFunctorFromSifted`: A category admitting a final functor from a sifted category is
  itself sifted.
- `IsSiftedOfIsFiltered`: A filtered category is sifted.
- `IsSiftedOfHasBinaryCoproductsAndNonempty`: A nonempty category with binary copreducts is sifted.

## References
- [nLab, *Sifted category*](https://ncatlab.org/nlab/show/sifted+category)
- [*Algebraic Theories*, Chapter 2.][Adámek_Rosický_Vitale_2010]
-/
noncomputable section

universe w v v₁ u u₁

namespace CategoryTheory

open MonoidalCategory Functor Limits


section ArbitraryUniverses

variable (C : Type u) [Category.{v} C]

/-- A category `C` `IsSiftedOrEmpty` if the diagonal functor `C ⥤ C × C` is final. -/
class IsSiftedOrEmpty : Prop where
  out : Final (diag C)

/-- A category `C` `IsSfited` if
1. the diagonal functor `C ⥤ C × C` is final.
2. there exists some object. -/
class IsSifted extends IsSiftedOrEmpty C : Prop where
  [Nonempty : Nonempty C]

attribute [instance] IsSifted.Nonempty
attribute [instance] IsSiftedOrEmpty.out

namespace IsSifted

variable {C}

/-- Being sifted is preserved by equivalences of categories -/
lemma IsSiftedOfEquiv [IsSifted C] {D : Type u₁} [Category.{v₁} D] (e : D ≌ C) : IsSifted D where
  out := by
    letI : D × D ≌ C × C:= Equivalence.prod e e
    have f : (e.inverse ⋙ diag D ⋙ this.functor ≅ diag C) :=
        NatIso.ofComponents (fun c ↦ by dsimp [this]
                                        exact Iso.prod (e.counitIso.app c) (e.counitIso.app c))
    apply final_iff_comp_equivalence _ this.functor|>.mpr
    apply final_iff_final_comp e.inverse _|>.mpr
    apply final_of_natIso f.symm
  Nonempty := ⟨e.inverse.obj (_root_.Nonempty.some IsSifted.Nonempty)⟩

/-- In particular a category is sifted iff and only if it is so when viewed as a small category -/
lemma IsSifted_iff_asSmallIsSifted : IsSifted C ↔ IsSifted (AsSmall.{w} C) where
  mp := fun _ ↦ IsSiftedOfEquiv AsSmall.equiv.symm
  mpr := fun _ ↦ IsSiftedOfEquiv AsSmall.equiv

/-- A sifted category is connected. -/
instance [IsSifted C]: IsConnected C :=
  isConnected_of_zigzag
    (by intro c₁ c₂
        have X : StructuredArrow (c₁, c₂) (diag C) :=
          letI S : Final (diag C) := by infer_instance
          Nonempty.some (S.out (c₁, c₂)).is_nonempty
        use [X.right, c₂]
        constructor
        · constructor
          · exact Zag.of_hom X.hom.fst
          · simp
            exact Zag.of_inv X.hom.snd
        · rfl)

/-- A category with binary coproducts is sifted or empty. -/
instance [HasBinaryCoproducts C] : IsSiftedOrEmpty C where
  out := by
    constructor
    rintro ⟨c₁, c₂⟩
    haveI : _root_.Nonempty <|StructuredArrow (c₁,c₂) (diag C) :=
      ⟨StructuredArrow.mk ((coprod.inl : c₁ ⟶ c₁ ⨿ c₂), (coprod.inr : c₂ ⟶ c₁ ⨿ c₂))⟩
    apply isConnected_of_zigzag
    rintro ⟨_, c, f⟩ ⟨_, c', g⟩
    dsimp only [const_obj_obj, diag_obj, prod_Hom] at f g
    use [StructuredArrow.mk
      ((coprod.inl : c₁ ⟶ c₁ ⨿ c₂), (coprod.inr : c₂ ⟶ c₁ ⨿ c₂)),
      StructuredArrow.mk (g.fst, g.snd)]
    simp only [colimit.cocone_x, diag_obj, Prod.mk.eta, List.chain_cons, List.Chain.nil, and_true,
      ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self,
      List.getLast_singleton]
    constructor
    exact ⟨Zag.of_inv <|StructuredArrow.homMk <|coprod.desc f.fst f.snd,
      Zag.of_hom <|StructuredArrow.homMk <|coprod.desc g.fst g.snd⟩
    · rfl

/-- A nonempty category with binary coproducts is sifted. -/
instance IsSiftedOfHasBinaryCoproductsAndNonempty [_root_.Nonempty C] [HasBinaryCoproducts C] :
    IsSifted C where

end IsSifted

section

variable {C}

/-- Introduce an auxiliary comparison between the chosen finite product and an
abstract categorical one. -/
-- Impl. note: we put this in a separate section here so that its content applies both to
-- types and presheaves.
@[simps!]
private def tensorProdToProdIso [ChosenFiniteProducts C] (X Y : C) : X ⊗ Y ≅ X ⨯ Y :=
  limit.isoLimitCone ((_: ChosenFiniteProducts _).product X Y)|>.symm

end

end ArbitraryUniverses

section SmallCategory

namespace IsSifted

variable {C : Type u} [SmallCategory.{u} C]

/-- We introducte an auxiliary external product on presheaves for convenience. -/
@[simps!]
private def externalProductFunctor : ((C ⥤ Type u) × (C ⥤ Type u) ⥤ C × C ⥤ Type u) :=
  prodFunctor ⋙ (whiskeringRight _ _ _).obj (tensor _)

private abbrev externalProduct (X Y : (C ⥤ Type u)) : (C × C ⥤ Type u) :=
  externalProductFunctor.obj <|Prod.mk X Y

local infixr:80 " ⊠ " => externalProduct

section

/-- An auxiliary isomorphism that shows that the tensor product in type preserves colimits -/
-- Implementation note: sadly this can not be derived from the `CartesianClosed` instance on Types.
private def preservesColimTensLeftType {E : Type u} : PreservesColimits (tensorLeft E) :=
  letI aux_iso : prod.functor.obj E ≅ tensorLeft E :=
    letI chosenprods : ChosenFiniteProducts (Type u) := by infer_instance
    NatIso.ofComponents (fun c ↦ by
      refine limit.isoLimitCone (chosenprods.product E c))
      (by intro a b f
          simp only [prod.functor_obj_obj, tensorLeft_obj, prod.functor_obj_map, tensorLeft_map]
          apply ChosenFiniteProducts.hom_ext <;>
          rw [Category.assoc] <;> erw [Limits.limit.isoLimitCone_hom_π]
          · simp only [prod.map_fst, Category.comp_id, Category.assoc,
            ChosenFiniteProducts.whiskerLeft_fst]
            erw [Limits.limit.isoLimitCone_hom_π]
          · simp only [prod.map_snd, Category.assoc, ChosenFiniteProducts.whiskerLeft_snd]
            erw [limit.isoLimitCone_hom_π_assoc])
  Limits.preservesColimitsOfNatIso aux_iso

variable (X Y : C ⥤ Type u)

attribute [local instance] preservesColimTensLeftType in
/-- An auxiliary isomorphisms that computes the colimit of a functor `C × C ⥤ Type`
that decomposes as an external product of two functors `C ⥤ Type` -/
private def colimBoxIsoColimTensColim : colimit (X ⊠ Y) ≅ (colimit X) ⊗ (colimit Y) :=
  letI : PreservesColimits (tensorRight Y) :=
    preservesColimitsOfNatIso (NatIso.ofComponents (fun _ ↦ β_ _ _) : tensorLeft Y ≅ tensorRight Y)
  calc colimit (X ⊠ Y)
    _ ≅ colimit <|(curry.obj _) ⋙ colim :=
      Limits.colimitIsoColimitCurryCompColim _
    _ ≅ colimit <| ((X ⋙ const C) ⋙ tensorRight Y) ⋙ colim :=
      HasColimit.isoOfNatIso <|
        isoWhiskerRight
          (NatIso.ofComponents
            (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)) :
              curry.obj (X ⊠ Y) ≅ (X ⋙ const C) ⋙ tensorRight Y)
          colim
    _ ≅ colimit <|colimit <| (X ⋙ const C) ⋙ tensorRight Y :=
      preservesColimitIso colim ((X ⋙ const C) ⋙ tensorRight Y)|>.symm
    _ ≅ colimit <|(tensorRight Y).obj <|colimit <|X ⋙ const C :=
      HasColimit.isoOfNatIso (preservesColimitIso (tensorRight Y) (X ⋙ const C)).symm
    _ ≅ colimit <|(const C ⋙ tensorRight Y).obj (colimit X) :=
      HasColimit.isoOfNatIso <| (tensorRight Y).mapIso (preservesColimitIso (const C) X).symm
    _ ≅ colimit <|Y ⋙ (tensorLeft (colimit X)) :=
      HasColimit.isoOfNatIso <|NatIso.ofComponents (fun _ ↦ Iso.refl _)
    _ ≅ (tensorLeft (colimit X)).obj (colimit Y) :=
      preservesColimitIso (tensorLeft (colimit X)) Y|>.symm

/-- Through the isomorphisms `colimBoxIsoColimTensColim` and `diagCompExternalProduct`,
the comparison map `colimit.pre (diag C)` is identified with the product comparison map for the
colimit functor. --/
private lemma factorisationProdComparisonColim :
    letI diagCompExternalProduct : X ⊗ Y ≅ diag C ⋙ X ⊠ Y := NatIso.ofComponents
      (fun c ↦ Iso.refl _)
    (HasColimit.isoOfNatIso (tensorProdToProdIso X Y)).inv ≫
      (HasColimit.isoOfNatIso diagCompExternalProduct).hom ≫ colimit.pre _ _ ≫
        (colimBoxIsoColimTensColim X Y).hom ≫ (tensorProdToProdIso _ _).hom =
          prodComparison colim X Y := by
  apply colimit.hom_ext; intro c
  -- First, we "bubble down" the maps to the colimits as much as we can
  dsimp [colimBoxIsoColimTensColim]
  simp only [Category.assoc, HasColimit.isoOfNatIso_ι_inv_assoc, Monoidal.tensorObj_obj,
    tensorProdToProdIso_inv, HasColimit.isoOfNatIso_ι_hom_assoc, comp_obj, diag_obj,
    externalProductFunctor_obj_obj, NatIso.ofComponents_hom_app, Iso.refl_hom, colimit.ι_pre_assoc,
    Category.id_comp]
  erw [colimitIsoColimitCurryCompColim_ι_hom_assoc]
  simp only [externalProductFunctor_obj_obj, HasColimit.isoOfNatIso_ι_hom_assoc, comp_obj,
    colim_obj, tensorRight_obj, isoWhiskerRight_hom, whiskerRight_app, NatIso.ofComponents_hom_app,
    colim_map, ι_preservesColimitsIso_inv_assoc, ι_colimMap_assoc, curry_obj_obj_obj,
    Monoidal.tensorObj_obj, const_obj_obj, Iso.refl_hom, Iso.symm_hom, mapIso_inv, tensorRight_map,
    Monoidal.whiskerRight_app, tensorLeft_obj, tensorLeft_map, Category.id_comp]
  slice_lhs 2 3 => rw [← NatTrans.vcomp_app, NatTrans.vcomp_eq_comp, ι_preservesColimitsIso_inv]
  simp only [comp_obj, tensorRight_map, Monoidal.whiskerRight_app, ← comp_whiskerRight,
    const_obj_obj, Category.assoc]
  slice_lhs 2 2 => rw [← NatTrans.vcomp_app, NatTrans.vcomp_eq_comp, ι_preservesColimitsIso_inv]
  simp only [const_map_app, Category.assoc]
  slice_lhs 2 3 => equals (colimit.ι X c) ⊗ (colimit.ι Y c) => aesop_cat
  -- Then we compose with the projections from the product.
  apply prod.hom_ext
  · simp only [Category.assoc, limit.isoLimitCone_inv_π, BinaryFan.π_app_left]
    erw [ChosenFiniteProducts.tensorHom_fst]
    dsimp [prodComparison]
    simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst, ι_colimMap]
    congr 0
  · simp only [Category.assoc, limit.isoLimitCone_inv_π, BinaryFan.π_app_right]
    erw [ChosenFiniteProducts.tensorHom_snd]
    dsimp [prodComparison]
    simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd, ι_colimMap]
    congr 0

variable [IsSifted C]

/-- If `C` is sifted, the canonical product comparison map for the `colim` functor
`(C ⥤ Type) ⥤ Type` is an isomorphism. -/
instance : IsIso (prodComparison colim X Y) := by
  rw [← factorisationProdComparisonColim]
  iterate apply IsIso.comp_isIso' <;> infer_instance

instance colimPreservesLimitsOfPairsOfIsSifted {X Y : C ⥤ Type u}:
    PreservesLimit (pair X Y) colim :=
  PreservesLimitPair.ofIsoProdComparison _ _ _

/-- Sifted colimits commute with binary products -/
instance colimPreservesBinaryProductsOfIsSifted :
    PreservesLimitsOfShape (Discrete WalkingPair) (colim : (C ⥤ _) ⥤ Type u) := by
  constructor
  intro F
  apply preservesLimitOfIsoDiagram colim (diagramIsoPair F).symm

/-- If `C` is sifted, the `colimit` functor `(C ⥤ Type) ⥤ Type` preserves terminal objects -/
instance colimPreservesTerminalObjectOfIsSifted :
    PreservesLimit (Functor.empty (C ⥤ Type u)) colim := by
  apply Limits.preservesTerminalOfIso
  symm
  apply (_ : ⊤_ (Type u) ≅ PUnit.{u +1}).trans
  · apply (Types.colimitConstPUnitIsoPUnit C).symm.trans
    apply HasColimit.isoOfNatIso
    apply IsTerminal.uniqueUpToIso _ terminalIsTerminal
    apply evaluationJointlyReflectsLimits
    intro k
    exact isLimitChangeEmptyCone _ Types.isTerminalPunit _ <|Iso.refl _
  · apply Types.isTerminalEquivIsoPUnit (⊤_ (Type u))|>.toFun
    exact terminalIsTerminal

instance colimPreservesLimitsOfShapePEmtyOfIsSifted :
    PreservesLimitsOfShape (Discrete PEmpty) (colim : (C ⥤ _) ⥤ Type u) :=
  preservesLimitsOfShapePemptyOfPreservesTerminal _

/-- Putting everything together, if `C` is sifted, the `colim` functor `(C ⥤ Type) ⥤ Type`
preserves finite products. -/
instance colimPreservesFiniteProductsOfIsSifted {J : Type*} [Fintype J] :
    PreservesLimitsOfShape (Discrete J) (colim : (C ⥤ _) ⥤ Type u ) :=
  preservesFiniteProductsOfPreservesBinaryAndTerminal _ J

end

section

open Opposite in
/-- If the `colim` functor `(C ⥤ Type) ⥤ Type` preserves binary products, then `C` is sifted or
empty. -/
theorem IsSiftedOrEmptyOfColimitPreservesBinaryProducts
    [PreservesLimitsOfShape (Discrete WalkingPair) (colim : (C ⥤ _) ⥤ Type u)] :
    IsSiftedOrEmpty C := by
  constructor
  apply cofinal_of_colimit_comp_coyoneda_iso_pUnit
  rintro ⟨c₁, c₂⟩
  calc colimit <|diag C ⋙ coyoneda.obj (op (c₁, c₂))
    _ ≅ colimit <|diag C ⋙ (coyoneda.obj (op c₁)) ⊠ (coyoneda.obj (op c₂)) :=
      HasColimit.isoOfNatIso <|isoWhiskerLeft _ <|NatIso.ofComponents (fun _ ↦ Iso.refl _)
    _ ≅ colimit (_ ⊗ _) := HasColimit.isoOfNatIso (NatIso.ofComponents (fun _ ↦ Iso.refl _)).symm
    _ ≅ colimit (_ ⨯ _) := HasColimit.isoOfNatIso <|tensorProdToProdIso _ _
    _ ≅ (colimit _) ⨯ (colimit _) := PreservesLimitPair.iso colim _ _
    _ ≅ PUnit ⨯ PUnit :=
      prod.mapIso (Coyoneda.colimitCoyonedaIso (op c₁)) (Coyoneda.colimitCoyonedaIso _)
    _ ≅ (⊤_ (Type u)) ⨯ PUnit := prod.mapIso (Types.terminalIso.{u}).symm <|Iso.refl _
    _ ≅ PUnit := Limits.prod.leftUnitor _

lemma IsSiftedOrEmptyOfColimitPreservesFiniteProducts
    [h : ∀ (n : ℕ), PreservesLimitsOfShape (Discrete (Fin n)) (colim : (C ⥤ _) ⥤ Type u)] :
    IsSiftedOrEmpty C := by
  rcases Finite.exists_equiv_fin WalkingPair with ⟨_, ⟨e⟩⟩
  haveI : PreservesLimitsOfShape (Discrete WalkingPair) (colim : (C ⥤ _) ⥤ Type u) :=
    preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) _
  exact @IsSiftedOrEmptyOfColimitPreservesBinaryProducts _ _ this

lemma NonemptyOfColimitPreservesLimitsOfShapeFinZero
    [PreservesLimitsOfShape (Discrete (Fin 0)) (colim : (C ⥤ _) ⥤ Type u)] :
    _root_.Nonempty C := by
  suffices connected : IsConnected C by infer_instance
  rw [Types.isConnected_iff_colimit_constPUnitFunctor_iso_pUnit]
  constructor
  haveI : PreservesLimitsOfShape (Discrete PEmpty) (colim : (C ⥤ _) ⥤ Type u) :=
    preservesLimitsOfShapeOfEquiv (Discrete.equivalence finZeroEquiv') _
  apply HasColimit.isoOfNatIso (_: Types.constPUnitFunctor C ≅ (⊤_ (C ⥤ Type u)))|>.trans
  · apply PreservesTerminal.iso colim|>.trans
    exact Types.terminalIso
  · apply IsTerminal.uniqueUpToIso _ terminalIsTerminal
    apply evaluationJointlyReflectsLimits
    intro _
    exact isLimitChangeEmptyCone _ Types.isTerminalPunit _ <|Iso.refl _

/-- If the `colim` functor `(C ⥤ Type) ⥤ Type` preserves finite products, then `C` is sifted. -/
theorem IsSiftedOfColimitPreservesFiniteProducts
    [h : ∀ (n : ℕ), PreservesLimitsOfShape (Discrete (Fin n)) (colim : (C ⥤ _) ⥤ Type u)] :
  IsSifted C := by
  haveI _ := @IsSiftedOrEmptyOfColimitPreservesFiniteProducts _ _ h
  haveI := @NonemptyOfColimitPreservesLimitsOfShapeFinZero _ _ (h 0)
  constructor

attribute [local instance] IsSiftedOfColimitPreservesFiniteProducts in
/-- A filtered category is sifted. -/
lemma IsSiftedOfIsFiltered [IsFiltered C] : IsSifted C := by
  infer_instance

/-- Auxiliary version of `IsSiftedOfFinalFunctorFromSifted` where everything is a small category. -/
theorem IsSiftedOfFinalFunctorFromSifted'
    {D : Type u} [SmallCategory.{u} D] [IsSifted C] (F : C ⥤ D) [Final F] : IsSifted D := by
  refine @IsSiftedOfColimitPreservesFiniteProducts _ _ ?_
  intro n
  constructor
  intro K
  have colim_comp_iso : (whiskeringLeft _ _ _).obj F ⋙ (colim : (C ⥤ _) ⥤ _) ≅
      (colim : (D ⥤ _) ⥤ Type u) :=
    NatIso.ofComponents
      (fun c ↦ Final.colimitIso F _)
      (by intro x y f
          dsimp [colimMap, Final.colimitIso]
          apply colimit.hom_ext
          intro t
          simp only [comp_obj, colimit.ι_pre_assoc]
          erw [IsColimit.ι_map]
          erw [IsColimit.ι_map_assoc]
          simp)
  apply preservesLimitOfNatIso K colim_comp_iso

end

end IsSifted

end SmallCategory

variable {C : Type u} [Category.{v} C]

/-- A functor admitting a final functor from a sifted category is sifted -/
theorem IsSifted.IsSiftedOfFinalFunctorFromSifted {D : Type u₁} [Category.{v₁} D] [IsSifted C]
    (F : C ⥤ D) [Final F] : IsSifted D := by
  rw [IsSifted_iff_asSmallIsSifted.{max u v}]
  rename_i C_sifted F_final
  rw [IsSifted_iff_asSmallIsSifted.{max u₁ v₁}] at C_sifted
  letI : (AsSmall.{max u₁ v₁} C) ⥤ (AsSmall.{max u v} D) :=
    AsSmall.equiv.inverse ⋙ F ⋙ AsSmall.equiv.functor
  have is_final : Final this := by infer_instance
  apply IsSiftedOfFinalFunctorFromSifted' this

end CategoryTheory
