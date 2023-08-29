/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Idempotents.Karoubi

#align_import category_theory.idempotents.functor_categories from "leanprover-community/mathlib"@"31019c2504b17f85af7e0577585fad996935a317"

/-!
# Idempotent completeness and functor categories

In this file we define an instance `functor_category_isIdempotentComplete` expressing
that a functor category `J ⥤ C` is idempotent complete when the target category `C` is.

We also provide a fully faithful functor
`karoubiFunctorCategoryEmbedding : Karoubi (J ⥤ C)) : J ⥤ Karoubi C` for all categories
`J` and `C`.

-/


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

open CategoryTheory.Limits

namespace CategoryTheory

namespace Idempotents

variable {J C : Type*} [Category J] [Category C] (P Q : Karoubi (J ⥤ C)) (f : P ⟶ Q) (X : J)

@[reassoc (attr := simp)]
theorem app_idem : P.p.app X ≫ P.p.app X = P.p.app X :=
  congr_app P.idem X
#align category_theory.idempotents.app_idem CategoryTheory.Idempotents.app_idem

variable {P Q}

@[reassoc (attr := simp)]
theorem app_p_comp : P.p.app X ≫ f.f.app X = f.f.app X :=
  congr_app (p_comp f) X
#align category_theory.idempotents.app_p_comp CategoryTheory.Idempotents.app_p_comp

@[reassoc (attr := simp)]
theorem app_comp_p : f.f.app X ≫ Q.p.app X = f.f.app X :=
  congr_app (comp_p f) X
#align category_theory.idempotents.app_comp_p CategoryTheory.Idempotents.app_comp_p

@[reassoc]
theorem app_p_comm : P.p.app X ≫ f.f.app X = f.f.app X ≫ Q.p.app X :=
  congr_app (p_comm f) X
#align category_theory.idempotents.app_p_comm CategoryTheory.Idempotents.app_p_comm

variable (J C)

instance functor_category_isIdempotentComplete [IsIdempotentComplete C] :
    IsIdempotentComplete (J ⥤ C) := by
  refine' ⟨fun F p hp => _⟩
  -- ⊢ ∃ Y i e, i ≫ e = 𝟙 Y ∧ e ≫ i = p
  have hC := (isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent C).mp inferInstance
  -- ⊢ ∃ Y i e, i ≫ e = 𝟙 Y ∧ e ≫ i = p
  haveI : ∀ j : J, HasEqualizer (𝟙 _) (p.app j) := fun j => hC _ _ (congr_app hp j)
  -- ⊢ ∃ Y i e, i ≫ e = 𝟙 Y ∧ e ≫ i = p
  /- We construct the direct factor `Y` associated to `p : F ⟶ F` by computing
      the equalizer of the identity and `p.app j` on each object `(j : J)`.  -/
  let Y : J ⥤ C :=
    { obj := fun j => Limits.equalizer (𝟙 _) (p.app j)
      map := fun {j j'} φ =>
        equalizer.lift (Limits.equalizer.ι (𝟙 _) (p.app j) ≫ F.map φ)
          (by rw [comp_id, assoc, p.naturality φ, ← assoc, ← Limits.equalizer.condition, comp_id]) }
  let i : Y ⟶ F :=
    { app := fun j => equalizer.ι _ _
      naturality := fun _ _ _ => by rw [equalizer.lift_ι] }
  let e : F ⟶ Y :=
    { app := fun j =>
        equalizer.lift (p.app j) (by simpa only [comp_id] using (congr_app hp j).symm)
      naturality := fun j j' φ => equalizer.hom_ext (by simp) }
  use Y, i, e
  -- ⊢ i ≫ e = 𝟙 Y ∧ e ≫ i = p
  constructor
  -- ⊢ i ≫ e = 𝟙 Y
  · ext j
    -- ⊢ NatTrans.app (i ≫ e) j = NatTrans.app (𝟙 Y) j
    apply equalizer.hom_ext
    -- ⊢ NatTrans.app (i ≫ e) j ≫ equalizer.ι (𝟙 (F.obj j)) (NatTrans.app p j) = NatT …
    dsimp
    -- ⊢ (equalizer.ι (𝟙 (F.obj j)) (NatTrans.app p j) ≫ equalizer.lift (NatTrans.app …
    rw [assoc, equalizer.lift_ι, ← equalizer.condition, id_comp, comp_id]
    -- 🎉 no goals
  · ext j
    -- ⊢ NatTrans.app (e ≫ i) j = NatTrans.app p j
    simp
    -- 🎉 no goals
namespace KaroubiFunctorCategoryEmbedding

variable {J C}

/-- On objects, the functor which sends a formal direct factor `P` of a
functor `F : J ⥤ C` to the functor `J ⥤ Karoubi C` which sends `(j : J)` to
the corresponding direct factor of `F.obj j`. -/
@[simps]
def obj (P : Karoubi (J ⥤ C)) : J ⥤ Karoubi C where
  obj j := ⟨P.X.obj j, P.p.app j, congr_app P.idem j⟩
  map {j j'} φ :=
    { f := P.p.app j ≫ P.X.map φ
      comm := by
        simp only [NatTrans.naturality, assoc]
        -- ⊢ NatTrans.app P.p j ≫ P.X.map φ = NatTrans.app P.p j ≫ NatTrans.app P.p j ≫ N …
        have h := congr_app P.idem j
        -- ⊢ NatTrans.app P.p j ≫ P.X.map φ = NatTrans.app P.p j ≫ NatTrans.app P.p j ≫ N …
        rw [NatTrans.comp_app] at h
        -- ⊢ NatTrans.app P.p j ≫ P.X.map φ = NatTrans.app P.p j ≫ NatTrans.app P.p j ≫ N …
        erw [reassoc_of% h, reassoc_of% h] }
        -- 🎉 no goals
#align category_theory.idempotents.karoubi_functor_category_embedding.obj CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.obj

/-- Tautological action on maps of the functor `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`. -/
@[simps]
def map {P Q : Karoubi (J ⥤ C)} (f : P ⟶ Q) : obj P ⟶ obj Q
    where app j := ⟨f.f.app j, congr_app f.comm j⟩
#align category_theory.idempotents.karoubi_functor_category_embedding.map CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.map

end KaroubiFunctorCategoryEmbedding

/-- The tautological fully faithful functor `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`. -/
@[simps]
def karoubiFunctorCategoryEmbedding : Karoubi (J ⥤ C) ⥤ J ⥤ Karoubi C where
  obj := KaroubiFunctorCategoryEmbedding.obj
  map := KaroubiFunctorCategoryEmbedding.map
#align category_theory.idempotents.karoubi_functor_category_embedding CategoryTheory.Idempotents.karoubiFunctorCategoryEmbedding

instance : Full (karoubiFunctorCategoryEmbedding J C) where
  preimage {P Q} f :=
    { f :=
        { app := fun j => (f.app j).f
          naturality := fun j j' φ => by
            rw [← Karoubi.comp_p_assoc]
            -- ⊢ P.X.map φ ≫ (fun j => (NatTrans.app f j).f) j' = (NatTrans.app f j).f ≫ (((k …
            have h := hom_ext_iff.mp (f.naturality φ)
            -- ⊢ P.X.map φ ≫ (fun j => (NatTrans.app f j).f) j' = (NatTrans.app f j).f ≫ (((k …
            simp only [comp_f] at h
            -- ⊢ P.X.map φ ≫ (fun j => (NatTrans.app f j).f) j' = (NatTrans.app f j).f ≫ (((k …
            dsimp [karoubiFunctorCategoryEmbedding] at h
            -- ⊢ P.X.map φ ≫ (fun j => (NatTrans.app f j).f) j' = (NatTrans.app f j).f ≫ (((k …
            erw [← h, assoc, ← P.p.naturality_assoc φ, p_comp (f.app j')] }
            -- 🎉 no goals
      comm := by
        ext j
        -- ⊢ NatTrans.app (NatTrans.mk fun j => (NatTrans.app f j).f) j = NatTrans.app (P …
        exact (f.app j).comm }
        -- 🎉 no goals
  witness f := rfl

instance : Faithful (karoubiFunctorCategoryEmbedding J C) where
  map_injective h := by
    ext j
    -- ⊢ NatTrans.app a₁✝.f j = NatTrans.app a₂✝.f j
    exact hom_ext_iff.mp (congr_app h j)
    -- 🎉 no goals

/-- The composition of `(J ⥤ C) ⥤ Karoubi (J ⥤ C)` and `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`
equals the functor `(J ⥤ C) ⥤ (J ⥤ Karoubi C)` given by the composition with
`toKaroubi C : C ⥤ Karoubi C`. -/
theorem toKaroubi_comp_karoubiFunctorCategoryEmbedding :
    toKaroubi _ ⋙ karoubiFunctorCategoryEmbedding J C =
      (whiskeringRight J _ _).obj (toKaroubi C) := by
  apply Functor.ext
  -- ⊢ autoParam (∀ (X Y : J ⥤ C) (f : X ⟶ Y), (toKaroubi (J ⥤ C) ⋙ karoubiFunctorC …
  · intro X Y f
    -- ⊢ (toKaroubi (J ⥤ C) ⋙ karoubiFunctorCategoryEmbedding J C).map f = eqToHom (_ …
    ext j
    -- ⊢ (NatTrans.app ((toKaroubi (J ⥤ C) ⋙ karoubiFunctorCategoryEmbedding J C).map …
    dsimp [toKaroubi]
    -- ⊢ NatTrans.app f j = (NatTrans.app (eqToHom (_ : ?F.obj X = ?G.obj X)) j).f ≫  …
    simp only [eqToHom_app, eqToHom_refl]
    -- ⊢ NatTrans.app f j = (𝟙 ((KaroubiFunctorCategoryEmbedding.obj (Karoubi.mk X (𝟙 …
    erw [comp_id, id_comp]
    -- 🎉 no goals
  · intro X
    -- ⊢ (toKaroubi (J ⥤ C) ⋙ karoubiFunctorCategoryEmbedding J C).obj X = ((whiskeri …
    apply Functor.ext
    -- ⊢ autoParam (∀ (X_1 Y : J) (f : X_1 ⟶ Y), ((toKaroubi (J ⥤ C) ⋙ karoubiFunctor …
    · intro j j' φ
      -- ⊢ ((toKaroubi (J ⥤ C) ⋙ karoubiFunctorCategoryEmbedding J C).obj X).map φ = eq …
      ext
      -- ⊢ (((toKaroubi (J ⥤ C) ⋙ karoubiFunctorCategoryEmbedding J C).obj X).map φ).f  …
      dsimp
      -- ⊢ 𝟙 (X.obj j) ≫ X.map φ = 𝟙 (X.obj j) ≫ X.map φ ≫ 𝟙 (X.obj j')
      simp
      -- 🎉 no goals
    · intro j
      -- ⊢ ((toKaroubi (J ⥤ C) ⋙ karoubiFunctorCategoryEmbedding J C).obj X).obj j = (( …
      rfl
      -- 🎉 no goals
#align category_theory.idempotents.to_karoubi_comp_karoubi_functor_category_embedding CategoryTheory.Idempotents.toKaroubi_comp_karoubiFunctorCategoryEmbedding

end Idempotents

end CategoryTheory
