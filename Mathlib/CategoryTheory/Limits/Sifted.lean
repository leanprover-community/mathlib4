/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.IsConnected
/-!
# Sifted categories

A category `C` is sifted if `C` is nonempty and the diagonal functor `C ⥤ C × C` is final.
Sifted categories can be characterized as those such that the colimit functor `(C ⥤ Type) ⥤ Type `
preserves finite products. We achieve this characterization in this file.

## Main results
- `isSifted_of_hasBinaryCoproducts_and_nonempty`: A nonempty category with binary coproducts is
  sifted.
- `IsSifted.colimPreservesFiniteProductsOfIsSifted`: The `Type`-valued colimit functor for sifted
  diagrams preserves finite products.
- `IsSifted.of_colimit_preservesFiniteProducts`: The converse: if the `Type`-valued colimit functor
  preserves finite products, the category is sifted.
- `IsSifted.of_final_functor_from_sifted`: A category admitting a final functor from a sifted
  category is itself sifted.

## References
- [nLab, *Sifted category*](https://ncatlab.org/nlab/show/sifted+category)
- [*Algebraic Theories*, Chapter 2.][Adamek_Rosicky_Vitale_2010]
-/

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory

open Limits Functor

section

variable (C : Type u) [Category.{v} C]

/-- A category `C` `IsSiftedOrEmpty` if the diagonal functor `C ⥤ C × C` is final. -/
abbrev IsSiftedOrEmpty : Prop := Final (diag C)

/-- A category `C` `IsSifted` if
1. the diagonal functor `C ⥤ C × C` is final.
2. there exists some object. -/
class IsSifted : Prop extends IsSiftedOrEmpty C where
  [nonempty : Nonempty C]

/- This instance is scoped since
- it applies unconditionally (which can be a performance drain),
- infers a *very* generic typeclass,
- and does so from a *very* specialised class. -/
attribute [scoped instance] IsSifted.nonempty

namespace IsSifted

variable {C}

/-- Being sifted is preserved by equivalences of categories -/
lemma isSifted_of_equiv [IsSifted C] {D : Type u₁} [Category.{v₁} D] (e : D ≌ C) : IsSifted D :=
  letI : Final (diag D) := by
    letI : D × D ≌ C × C:= Equivalence.prod e e
    have sq : (e.inverse ⋙ diag D ⋙ this.functor ≅ diag C) :=
        NatIso.ofComponents (fun c ↦ by dsimp [this]
                                        exact Iso.prod (e.counitIso.app c) (e.counitIso.app c))
    apply_rules [final_iff_comp_equivalence _ this.functor|>.mpr,
      final_iff_final_comp e.inverse _ |>.mpr, final_of_natIso sq.symm]
  letI : _root_.Nonempty D := ⟨e.inverse.obj (_root_.Nonempty.some IsSifted.nonempty)⟩
  ⟨⟩

/-- In particular a category is sifted iff and only if it is so when viewed as a small category -/
lemma isSifted_iff_asSmallIsSifted : IsSifted C ↔ IsSifted (AsSmall.{w} C) where
  mp _ := isSifted_of_equiv AsSmall.equiv.symm
  mpr _ := isSifted_of_equiv AsSmall.equiv

/-- A sifted category is connected. -/
instance [IsSifted C] : IsConnected C :=
  isConnected_of_zigzag
    (by intro c₁ c₂
        have X : StructuredArrow (c₁, c₂) (diag C) :=
          letI S : Final (diag C) := by infer_instance
          Nonempty.some (S.out (c₁, c₂)).is_nonempty
        use [X.right, c₂]
        constructor
        · constructor
          · exact Zag.of_hom X.hom.fst
          · simpa using Zag.of_inv X.hom.snd
        · rfl)

/-- A category with binary coproducts is sifted or empty. -/
instance [HasBinaryCoproducts C] : IsSiftedOrEmpty C := by
    constructor
    rintro ⟨c₁, c₂⟩
    haveI : _root_.Nonempty <| StructuredArrow (c₁,c₂) (diag C) :=
      ⟨.mk ((coprod.inl : c₁ ⟶ c₁ ⨿ c₂), (coprod.inr : c₂ ⟶ c₁ ⨿ c₂))⟩
    apply isConnected_of_zigzag
    rintro ⟨_, c, f⟩ ⟨_, c', g⟩
    dsimp only [const_obj_obj, diag_obj, prod_Hom] at f g
    use [.mk ((coprod.inl : c₁ ⟶ c₁ ⨿ c₂), (coprod.inr : c₂ ⟶ c₁ ⨿ c₂)), .mk (g.fst, g.snd)]
    simp only [colimit.cocone_x, diag_obj, Prod.mk.eta, List.isChain_cons_cons,
      List.isChain_singleton, and_true, ne_eq, reduceCtorEq, not_false_eq_true,
      List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
    exact ⟨⟨Zag.of_inv <| StructuredArrow.homMk <| coprod.desc f.fst f.snd,
      Zag.of_hom <| StructuredArrow.homMk <| coprod.desc g.fst g.snd⟩, rfl⟩

/-- A nonempty category with binary coproducts is sifted. -/
instance isSifted_of_hasBinaryCoproducts_and_nonempty [_root_.Nonempty C] [HasBinaryCoproducts C] :
    IsSifted C where

end IsSifted

end

section

variable {C : Type u} [Category.{v} C] [IsSiftedOrEmpty C] {D : Type u₁} [Category.{v₁} D]
  {D' : Type u₂} [Category.{v₂} D'] (F : C ⥤ D) (G : C ⥤ D')

instance [F.Final] [G.Final] : (F.prod' G).Final :=
  show (diag C ⋙ F.prod G).Final from final_comp _ _

end

noncomputable section SmallCategory

open MonoidalCategory CartesianMonoidalCategory

namespace IsSifted

variable {C : Type u} [SmallCategory C]

section

open scoped MonoidalCategory.ExternalProduct

variable (X Y : C ⥤ Type u)

/-- Through the isomorphisms `PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂` and
`externalProductCompDiagIso`, the comparison map `colimit.pre (X ⊠ Y) (diag C)` identifies with the
product comparison map for the colimit functor. -/
lemma factorization_prodComparison_colim :
    (HasColimit.isoOfNatIso ((externalProductCompDiagIso _ _).app (X, Y)).symm).hom ≫
      colimit.pre (X ⊠ Y) (diag C) ≫
        (PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂ X Y <| curriedTensor <| Type u).hom =
    CartesianMonoidalCategory.prodComparison colim X Y := by
  apply colimit.hom_ext
  intro j
  dsimp [externalProductBifunctor, CartesianMonoidalCategory.prodComparison,
    externalProductBifunctorCurried, externalProduct]
  cat_disch

variable [IsSifted C]

/-- If `C` is sifted, the canonical product comparison map for the `colim` functor
`(C ⥤ Type) ⥤ Type` is an isomorphism. -/
instance : IsIso (CartesianMonoidalCategory.prodComparison colim X Y) := by
  rw [← factorization_prodComparison_colim]
  infer_instance

instance colim_preservesLimits_pair_of_sSifted {X Y : C ⥤ Type u} :
    PreservesLimit (pair X Y) colim :=
  preservesLimit_pair_of_isIso_prodComparison _ _ _

/-- Sifted colimits commute with binary products -/
instance colim_preservesBinaryProducts_of_isSifted :
    PreservesLimitsOfShape (Discrete WalkingPair) (colim : (C ⥤ _) ⥤ Type u) := by
  constructor
  intro F
  apply preservesLimit_of_iso_diagram colim (diagramIsoPair F).symm

/-- If `C` is sifted, the `colimit` functor `(C ⥤ Type) ⥤ Type` preserves terminal objects -/
instance colim_preservesTerminal_of_isSifted :
    PreservesLimit (Functor.empty.{0} (C ⥤ Type u)) colim := by
  apply preservesTerminal_of_iso
  symm
  apply (_ : ⊤_ (Type u) ≅ PUnit.{u +1}).trans
  · apply_rules [(Types.colimitConstPUnitIsoPUnit C).symm.trans, HasColimit.isoOfNatIso,
      IsTerminal.uniqueUpToIso _ terminalIsTerminal, evaluationJointlyReflectsLimits]
    exact fun _ ↦ isLimitChangeEmptyCone _ Types.isTerminalPunit _ <| Iso.refl _
  · exact Types.isTerminalEquivIsoPUnit (⊤_ (Type u))|>.toFun terminalIsTerminal

instance colim_preservesLimitsOfShape_pempty_of_isSifted :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (colim : (C ⥤ _) ⥤ Type u) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

/-- If `C` is sifted, the `colim` functor `(C ⥤ Type) ⥤ Type` preserves finite products. -/
instance colim_preservesFiniteProducts_of_isSifted :
    PreservesFiniteProducts (colim : (C ⥤ _) ⥤ Type u ) :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal colim

end

section

variable (C)

open Opposite in
open scoped MonoidalCategory.ExternalProduct in
/-- If the `colim` functor `(C ⥤ Type) ⥤ Type` preserves binary products, then `C` is sifted or
empty. -/
theorem isSiftedOrEmpty_of_colim_preservesBinaryProducts
    [PreservesLimitsOfShape (Discrete WalkingPair) (colim : (C ⥤ Type u) ⥤ Type u)] :
    IsSiftedOrEmpty C := by
  apply final_of_colimit_comp_coyoneda_iso_pUnit
  rintro ⟨c₁, c₂⟩
  calc colimit <| diag C ⋙ coyoneda.obj (op (c₁, c₂))
    _ ≅ colimit <| _ ⋙ (coyoneda.obj _) ⊠ (coyoneda.obj _) :=
      HasColimit.isoOfNatIso <| isoWhiskerLeft _ <| .refl _
    _ ≅ colimit (_ ⊗ _) := HasColimit.isoOfNatIso <| .refl _
    _ ≅ (colimit _) ⊗ (colimit _) := CartesianMonoidalCategory.prodComparisonIso colim _ _
    _ ≅ PUnit ⊗ PUnit := (Coyoneda.colimitCoyonedaIso _) ⊗ᵢ (Coyoneda.colimitCoyonedaIso _)
    _ ≅ PUnit := λ_ _

lemma isSiftedOrEmpty_of_colim_preservesFiniteProducts
    [h : PreservesFiniteProducts (colim : (C ⥤ Type u) ⥤ Type u)] :
    IsSiftedOrEmpty C :=
  isSiftedOrEmpty_of_colim_preservesBinaryProducts C

lemma nonempty_of_colim_preservesLimitsOfShapeFinZero
    [PreservesLimitsOfShape (Discrete (Fin 0)) (colim : (C ⥤ Type u) ⥤ Type u)] :
    Nonempty C := by
  suffices connected : IsConnected C by infer_instance
  rw [Types.isConnected_iff_colimit_constPUnitFunctor_iso_pUnit]
  constructor
  haveI : PreservesLimitsOfShape (Discrete PEmpty) (colim : (C ⥤ _) ⥤ Type u) :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence finZeroEquiv') _
  apply HasColimit.isoOfNatIso (_: Types.constPUnitFunctor C ≅ (⊤_ (C ⥤ Type u)))|>.trans
  · apply PreservesTerminal.iso colim |>.trans
    exact Types.terminalIso
  · apply_rules [IsTerminal.uniqueUpToIso _ terminalIsTerminal, evaluationJointlyReflectsLimits]
    intro _
    exact isLimitChangeEmptyCone _ Types.isTerminalPunit _ <| Iso.refl _

/-- If the `colim` functor `(C ⥤ Type) ⥤ Type` preserves finite products, then `C` is sifted. -/
theorem of_colim_preservesFiniteProducts
    [h : PreservesFiniteProducts (colim : (C ⥤ Type u) ⥤ Type u)] :
    IsSifted C := by
  have := isSiftedOrEmpty_of_colim_preservesFiniteProducts C
  have := nonempty_of_colim_preservesLimitsOfShapeFinZero C
  constructor

variable {C}

/-- Auxiliary version of `IsSifted.of_final_functor_from_sifted` where everything is a
small category. -/
theorem of_final_functor_from_sifted'
    {D : Type u} [SmallCategory D] [IsSifted C] (F : C ⥤ D) [Final F] : IsSifted D := by
  have : PreservesFiniteProducts (colim : (D ⥤ Type u) ⥤ _) :=
    ⟨fun n ↦ preservesLimitsOfShape_of_natIso (Final.colimIso F)⟩
  exact of_colim_preservesFiniteProducts D

end

end IsSifted

end SmallCategory

variable {C : Type u} [Category.{v} C]

/-- A functor admitting a final functor from a sifted category is sifted. -/
theorem IsSifted.of_final_functor_from_sifted {D : Type u₁} [Category.{v₁} D] [h₁ : IsSifted C]
    (F : C ⥤ D) [Final F] : IsSifted D := by
  rw [isSifted_iff_asSmallIsSifted] at h₁ ⊢
  exact of_final_functor_from_sifted' <|
    AsSmall.equiv.{_, _, max u₁ v₁}.inverse ⋙ F ⋙ AsSmall.equiv.{_, _, max u v}.functor

end CategoryTheory
