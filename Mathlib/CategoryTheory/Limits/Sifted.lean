/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Limits.Final
/-!
# Sifted categories

A category `C` is sifted if `C` is nonempty and the diagonal functor `C ⥤ C × C` is final.
Sifted categories can be characterized as those such that the colimit functor `(C ⥤ Type) ⥤ Type `
preserves finite products.

## Main results
- `isSifted_of_hasBinaryCoproducts_and_nonempty`: A nonempty category with binary coproducts is
  sifted.

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

end CategoryTheory
