import Mathlib.CategoryTheory.Yoneda

namespace CategoryTheory
open Coyoneda

open Opposite

universe v₁ u₁ u₂
set_option autoImplicit false
variable (C : Type u₁) [Category.{v₁} C]

theorem Coyoneda.obj_map_id {X Y : C} (f : X ⟶ Y) :
    (coyoneda.obj (Opposite.op X)).map f (𝟙 X) = (coyoneda.map f.op).app Y (𝟙 Y) := by
  dsimp
  simp
/-- The "Yoneda evaluation" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
def coyonedaEvaluation : C × (C ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  evaluationUncurried C (Type v₁) ⋙ uliftFunctor.{u₁}

@[simp]
theorem coyonedaEvaluation_map_down (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (coyonedaEvaluation C).obj P) :
    ((coyonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

/-- The "Yoneda pairing" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `yoneda.op.obj X ⟶ F`, functorially in both `X` and `F`.
-/
def coyonedaPairing : C × (C ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  Functor.prod coyoneda.rightOp (𝟭 (C ⥤ Type v₁)) ⋙ Functor.hom (C ⥤ Type v₁)

-- Porting note: we need to provide this `@[ext]` lemma separately,
-- as `ext` will not look through the definition.
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext]
lemma coyonedaPairingExt {X : C × (C ⥤ Type v₁)} {x y : (coyonedaPairing C).obj X}
    (w : ∀ Y, x.app Y = y.app Y) : x = y :=
  NatTrans.ext _ _ (funext w)

@[simp]
theorem coyonedaPairing_map (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q) (β : (coyonedaPairing C).obj P) :
    (coyonedaPairing C).map α β = coyoneda.map α.1.op ≫ β ≫ α.2 :=
  rfl

/-- The Yoneda lemma asserts that that the Yoneda pairing
`(X : Cᵒᵖ, F : Cᵒᵖ ⥤ Type) ↦ (yoneda.obj (unop X) ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`.

See <https://stacks.math.columbia.edu/tag/001P>.
-/
def coyonedaLemma : coyonedaPairing C ≅ coyonedaEvaluation C where
  hom :=
    { app := fun F x => ULift.up ((x.app F.1) (𝟙 F.1))
      naturality := by
        intro X Y f
        simp only [coyonedaEvaluation]
        ext
        dsimp
        erw [Category.comp_id, ←FunctorToTypes.naturality]
        simp only [Category.id_comp f.1, coyoneda_obj_map] }
  inv :=
    { app := fun F x =>
        { app := fun X a => (F.2.map a) x.down
          naturality := by
            intro X Y f
            ext
            dsimp
            rw [FunctorToTypes.map_comp_apply] }
      naturality := by
        intro X Y f
        simp only [yoneda]
        ext
        dsimp
        rw [←FunctorToTypes.naturality X.snd Y.snd f.snd, FunctorToTypes.map_comp_apply] }
  hom_inv_id := by
    ext
    dsimp
    erw [← FunctorToTypes.naturality, Coyoneda.obj_map_id]
    simp only [coyoneda_map_app, Quiver.Hom.unop_op]
    erw [Category.comp_id]
  inv_hom_id := by
    ext
    dsimp
    rw [FunctorToTypes.map_id_apply, ULift.up_down]

variable {C}

/-- The isomorphism between `yoneda.obj X ⟶ F` and `F.obj (op X)`
(we need to insert a `ulift` to get the universes right!)
given by the Yoneda lemma.
-/
@[simps!]
def coyonedaSections (X : C) (F : C ⥤ Type v₁) :
    (coyoneda.obj (op X) ⟶ F) ≅ ULift.{u₁} (F.obj X) :=
  (coyonedaLemma C).app (X, F)

/-- We have a type-level equivalence between natural transformations from the yoneda embedding
and elements of `F.obj X`, without any universe switching.
-/
def coyonedaEquiv {X : C} {F : C ⥤ Type v₁} : (coyoneda.obj (op X) ⟶ F) ≃ F.obj X :=
  (coyonedaSections X F).toEquiv.trans Equiv.ulift

@[simp]
theorem coyonedaEquiv_apply {X : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F) :
    coyonedaEquiv f = f.app X (𝟙 X) :=
  rfl

@[simp]
theorem coyonedaEquiv_symm_app_apply {X : C} {F : C ⥤ Type v₁} (x : F.obj X) (Y : C)
    (f : X ⟶ Y) : (coyonedaEquiv.symm x).app Y f = F.map f x :=
  rfl


#exit
theorem coyonedaEquiv_naturality {X : Cᵒᵖ} {Y : C} {F : C ⥤ Type v₁}
    (f : coyoneda.obj X ⟶ F) (g : Y ⟶ X.unop) :
    F.map g (coyonedaEquiv f) = coyonedaEquiv (coyoneda.map g ≫ f) := by
  change (f.app (op X) ≫ F.map g.op) (𝟙 X) = f.app (op Y) (𝟙 Y ≫ g)
  rw [← f.naturality]
  dsimp
  simp
#align category_theory.yoneda_equiv_naturality CategoryTheory.yonedaEquiv_naturality

/-- When `C` is a small category, we can restate the isomorphism from `yoneda_sections`
without having to change universes.
-/
def yonedaSectionsSmall {C : Type u₁} [SmallCategory C] (X : C) (F : Cᵒᵖ ⥤ Type u₁) :
    (yoneda.obj X ⟶ F) ≅ F.obj (op X) :=
  yonedaSections X F ≪≫ uliftTrivial _
#align category_theory.yoneda_sections_small CategoryTheory.yonedaSectionsSmall

@[simp]
theorem yonedaSectionsSmall_hom {C : Type u₁} [SmallCategory C] (X : C) (F : Cᵒᵖ ⥤ Type u₁)
    (f : yoneda.obj X ⟶ F) : (yonedaSectionsSmall X F).hom f = f.app _ (𝟙 _) :=
  rfl
#align category_theory.yoneda_sections_small_hom CategoryTheory.yonedaSectionsSmall_hom

@[simp]
theorem yonedaSectionsSmall_inv_app_apply {C : Type u₁} [SmallCategory C] (X : C)
    (F : Cᵒᵖ ⥤ Type u₁) (t : F.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
    ((yonedaSectionsSmall X F).inv t).app Y f = F.map f.op t :=
  rfl
#align category_theory.yoneda_sections_small_inv_app_apply CategoryTheory.yonedaSectionsSmall_inv_app_apply

attribute [local ext] Functor.ext

/- Porting note: this used to be two calls to `tidy` -/
/-- The curried version of yoneda lemma when `C` is small. -/
def curriedYonedaLemma {C : Type u₁} [SmallCategory C] :
    (yoneda.op ⋙ coyoneda : Cᵒᵖ ⥤ (Cᵒᵖ ⥤ Type u₁) ⥤ Type u₁) ≅ evaluation Cᵒᵖ (Type u₁) := by
  refine eqToIso ?_ ≪≫ curry.mapIso
    (yonedaLemma C ≪≫ isoWhiskerLeft (evaluationUncurried Cᵒᵖ (Type u₁)) uliftFunctorTrivial) ≪≫
    eqToIso ?_
  · apply Functor.ext
    · intro X Y f
      ext
      simp
    · aesop_cat
  · apply Functor.ext
    · intro X Y f
      ext
      simp
    · intro X
      simp only [curry, yoneda, coyoneda, curryObj, yonedaPairing]
      aesop_cat
#align category_theory.curried_yoneda_lemma CategoryTheory.curriedYonedaLemma

/-- The curried version of yoneda lemma when `C` is small. -/
def curriedYonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft Cᵒᵖ (Cᵒᵖ ⥤ Type u₁)ᵒᵖ (Type u₁)).obj yoneda.op ≅ 𝟭 (Cᵒᵖ ⥤ Type u₁)
    := by
  refine eqToIso ?_ ≪≫ curry.mapIso (isoWhiskerLeft (Prod.swap _ _)
    (yonedaLemma C ≪≫ isoWhiskerLeft (evaluationUncurried Cᵒᵖ (Type u₁)) uliftFunctorTrivial :_))
    ≪≫ eqToIso ?_
  · apply Functor.ext
    · intro X Y f
      aesop_cat
  · apply Functor.ext
    · aesop_cat
#align category_theory.curried_yoneda_lemma' CategoryTheory.curriedYonedaLemma'

end CategoryTheory
