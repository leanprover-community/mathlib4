import Mathlib.CategoryTheory.Enriched.FunctorCategory

universe v v' u u'

namespace CategoryTheory

namespace Presheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [MonoidalCategory D] [MonoidalClosed D]

variable (F G : Cᵒᵖ ⥤ D)
  [∀ (X : C), Functor.HasEnrichedHoms (Over X)ᵒᵖ D]

noncomputable def internalHom.obj (X : Cᵒᵖ) : D :=
  ((Over.forget X.unop).op ⋙ F) ⟶[D] ((Over.forget X.unop).op ⋙ G)

section

noncomputable def internalHom.map {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    internalHom.obj F G X ⟶ internalHom.obj F G Y :=
  (Functor.whiskeringLeftEnrichedFunctor (Over.map f.unop).op D).map _ _

@[reassoc (attr := simp)]
lemma internalHom.map_app {X Y : Cᵒᵖ} (f : X ⟶ Y) {U : C} (φ : U ⟶ Y.unop) :
    map F G f ≫ Functor.enrichedHom.app _ _ (Opposite.op (Over.mk φ)) =
      Functor.enrichedHom.app _ _ (Opposite.op (Over.mk (φ ≫ f.unop))) := by
  sorry

end

lemma _root_.CategoryTheory.Over.mk_surjective {X : C} (Y : Over X) :
    ∃ (U : C) (f : U ⟶ X), Y = Over.mk f :=
  CostructuredArrow.mk_surjective Y

noncomputable def internalHom : Cᵒᵖ ⥤ D where
  obj := internalHom.obj F G
  map f := internalHom.map F G f
  map_id X := by
    apply Functor.enrichedHom.hom_ext
    rintro ⟨π⟩
    obtain ⟨U, π, rfl⟩ := Over.mk_surjective π
    dsimp
    simp
    congr 1
    simp
  map_comp {F₁ F₂ F₃} f g := by
    apply Functor.enrichedHom.hom_ext
    rintro ⟨π⟩
    obtain ⟨U, π, rfl⟩ := Over.mk_surjective π
    simp
    congr 1
    simp

/-

TODO: `K ⟶ internalHom F G ≃ (K ⊗ F ⟶ G)`

-/

end Presheaf

end CategoryTheory
