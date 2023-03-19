import Mathlib.CategoryTheory.Localization.Equivalence

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

namespace Functor
-- to be moved to CategoryTheory.Functor.Currying

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]

lemma uncurry_obj_curry_obj (F : C₁ × C₂ ⥤ D) : uncurry.obj (curry.obj F) = F := by
  refine' Functor.ext _ _
  . simp
  . intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩
    dsimp
    rw [← F.map_comp, Category.id_comp, Category.comp_id]
    aesop_cat

lemma curry_obj_injective {F₁ F₂ : C₁ × C₂ ⥤ D} (h : curry.obj F₁ = curry.obj F₂) : F₁ = F₂ := by
  rw [← uncurry_obj_curry_obj F₁, ← uncurry_obj_curry_obj F₂, h]

lemma curry_obj_uncurry_obj (F : C₁ ⥤ C₂ ⥤ D) : curry.obj (uncurry.obj F) = F := by
  refine' Functor.ext _ _
  . intro X₁
    exact Functor.ext (by simp) (by simp)
  . intros X₁ X₂ f
    aesop_cat

lemma uncurry_obj_injective {F₁ F₂ : C₁ ⥤ C₂ ⥤ D}
  (h : uncurry.obj F₁ = uncurry.obj F₂) : F₁ = F₂ := by
  rw [← curry_obj_uncurry_obj F₁, ← curry_obj_uncurry_obj F₂, h]

lemma flip_flip (F : C₁ ⥤ C₂ ⥤ D) : F.flip.flip = F := rfl

lemma flip_injective {F₁ F₂ : C₁ ⥤ C₂ ⥤ D} (h : F₁.flip = F₂.flip) : F₁ = F₂ := by
  rw [← flip_flip F₁, ← flip_flip F₂, h]

lemma uncurry_obj_curry_obj_flip_flip {C₁' : Type u₄} {C₂' : Type u₅}
  [Category.{v₄} C₁'] [Category.{v₅} C₂']
  (F₁ : C₁ ⥤ C₁') (F₂ : C₂ ⥤ C₂') (G : C₁' × C₂' ⥤ D) :
    uncurry.obj (F₂ ⋙ (F₁ ⋙ curry.obj G).flip).flip = (F₁.prod F₂) ⋙ G := by
  refine' Functor.ext _ _
  . simp
  . intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩
    dsimp
    simp only [Category.id_comp, Category.comp_id, ← G.map_comp]
    aesop_cat

lemma uncurry_obj_curry_obj_flip_flip' {C₁' : Type u₄} {C₂' : Type u₅}
  [Category.{v₄} C₁'] [Category.{v₅} C₂']
  (F₁ : C₁ ⥤ C₁') (F₂ : C₂ ⥤ C₂') (G : C₁' × C₂' ⥤ D) :
    uncurry.obj (F₁ ⋙ (F₂ ⋙ (curry.obj G).flip).flip) = (F₁.prod F₂) ⋙ G := by
  refine' Functor.ext _ _
  . simp
  . intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩
    dsimp
    simp only [Category.id_comp, Category.comp_id, ← G.map_comp]
    aesop_cat

end Functor

section
-- to be moved to CategoryTheory.Products.Basic

variable {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D₁] [Category.{v₄} D₂]

/-- The cartesian product of two natural isomorphisms. -/
@[simps]
def NatIso.prod {F F' : C₁ ⥤ D₁} {G G' : C₂ ⥤ D₂} (e₁ : F ≅ F') (e₂ : G ≅ G') :
    F.prod G ≅ F'.prod G' :=
{ hom := NatTrans.prod e₁.hom e₂.hom
  inv := NatTrans.prod e₁.inv e₂.inv }

namespace Equivalence

/-- The cartesian product of two equivalences of categories. -/
@[simps]
def prod (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂) : C₁ × C₂ ≌ D₁ × D₂ where
  functor := E₁.functor.prod E₂.functor
  inverse := E₁.inverse.prod E₂.inverse
  unitIso := NatIso.prod E₁.unitIso E₂.unitIso
  counitIso := NatIso.prod E₁.counitIso E₂.counitIso
  functor_unitIso_comp := by
    intro ⟨x₁, x₂⟩
    apply Prod.ext
    . dsimp
      simp
    . dsimp
      simp

end Equivalence

end

variable {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D₁] [Category.{v₄} D₂]
  (L₁ : C₁ ⥤ D₁) {W₁ : MorphismProperty C₁} [W₁.ContainsIdentities]
  (L₂ : C₂ ⥤ D₂) {W₂ : MorphismProperty C₂} [W₂.ContainsIdentities]

namespace Localization

namespace StrictUniversalPropertyFixedTarget

variable {E : Type u₅} [Category.{v₅} E]
  (F : C₁ × C₂ ⥤ E) (hF : (W₁.prod W₂).IsInvertedBy F)

/-- auxiliary definition for `prod_lift` -/
noncomputable def prod_lift₁  :
    W₁.Localization ⥤ C₂ ⥤ E := Construction.lift (curry.obj F) (fun _ _ f₁ hf₁ => by
  haveI : ∀ (X₂ : C₂), IsIso (((curry.obj F).map f₁).app X₂) :=
    fun X₂ => hF _ ⟨hf₁, MorphismProperty.ContainsIdentities.mem _ _⟩
  apply NatIso.isIso_of_isIso_app)

lemma prod_fac₁ :
  W₁.Q ⋙ prod_lift₁ F hF = curry.obj F :=
  Construction.fac _ _

/-- the lifting of a functor `F : C₁ × C₂ ⥤ E` inverting `W₁.prod W₂` to a functor
`W₁.Localization × W₂.Localization ⥤ E` -/
noncomputable def prod_lift :
    W₁.Localization × W₂.Localization ⥤ E := by
  refine' uncurry.obj (Construction.lift (prod_lift₁ F hF).flip _).flip
  intro _ _ f₂ hf₂
  haveI : ∀ (X₁ : W₁.Localization), IsIso (((Functor.flip (prod_lift₁ F hF)).map f₂).app X₁) := by
    intro X₁
    obtain ⟨X₁, rfl⟩ := (Construction.objEquiv W₁).surjective X₁
    exact (isIso_iff_of_arrow_mk_iso (((Functor.mapArrowFunctor _ _).mapIso
      (eqToIso (Functor.congr_obj (prod_fac₁ F hF) X₁))).app (Arrow.mk f₂))).2
        (hF _ ⟨MorphismProperty.ContainsIdentities.mem _ _, hf₂⟩)
  apply NatIso.isIso_of_isIso_app

lemma prod_fac₂ : W₂.Q ⋙ (curry.obj (prod_lift F hF)).flip = (prod_lift₁ F hF).flip := by
  simp only [prod_lift, Functor.curry_obj_uncurry_obj, Functor.flip_flip]
  apply Construction.fac

lemma prod_fac :
    (W₁.Q.prod W₂.Q) ⋙ prod_lift F hF = F := by
  rw [← Functor.uncurry_obj_curry_obj_flip_flip', prod_fac₂, Functor.flip_flip, prod_fac₁,
    Functor.uncurry_obj_curry_obj]

lemma prod_uniq (F₁ F₂ : (W₁.Localization × W₂.Localization ⥤ E))
    (h : (W₁.Q.prod W₂.Q) ⋙ F₁ = (W₁.Q.prod W₂.Q) ⋙ F₂) :
      F₁ = F₂ := by
  apply Functor.curry_obj_injective
  apply Construction.uniq
  apply Functor.flip_injective
  apply Construction.uniq
  apply Functor.flip_injective
  apply Functor.uncurry_obj_injective
  simpa only [Functor.uncurry_obj_curry_obj_flip_flip] using h

variable (W₁ W₂)

/-- the universal property of the localized category for products of two of the
constructed localized categories -/
noncomputable def prod :
    StrictUniversalPropertyFixedTarget (W₁.Q.prod W₂.Q) (W₁.prod W₂) E where
  inverts := (Localization.inverts W₁.Q W₁).prod (Localization.inverts W₂.Q W₂)
  lift := prod_lift
  fac := prod_fac
  uniq := prod_uniq

end StrictUniversalPropertyFixedTarget

variable (W₁ W₂)

@[nolint checkUnivs]
lemma Construction.prodIsLocalization :
    (W₁.Q.prod W₂.Q).IsLocalization (W₁.prod W₂) :=
  Functor.IsLocalization.mk' _ _
    (StrictUniversalPropertyFixedTarget.prod W₁ W₂)
    (StrictUniversalPropertyFixedTarget.prod W₁ W₂)

end Localization

open Localization

namespace Functor

namespace IsLocalization

variable (W₁ W₂)

instance prod [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] :
    (L₁.prod L₂).IsLocalization (W₁.prod W₂) := by
  haveI := Construction.prodIsLocalization W₁ W₂
  exact of_equivalence_target (W₁.Q.prod W₂.Q) (W₁.prod W₂) (L₁.prod L₂)
    ((uniq W₁.Q L₁ W₁).prod (uniq W₂.Q L₂ W₂))
    (NatIso.prod (compUniqFunctor W₁.Q L₁ W₁) (compUniqFunctor W₂.Q L₂ W₂))

end IsLocalization

end Functor

end CategoryTheory
