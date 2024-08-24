import Mathlib.CategoryTheory.Enriched.FunctorCategory

universe v v' u u'

namespace CategoryTheory

open Category MonoidalCategory

namespace Presheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ (X : C), Functor.HasEnrichedHoms (Over X)ᵒᵖ D]

section

variable (F G : Cᵒᵖ ⥤ D)

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
  apply Functor.enrichedHom.precomp_app

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
    simp only [internalHom.map_app, unop_id, id_comp]
    congr 1
    simp
  map_comp _ _ := by
    apply Functor.enrichedHom.hom_ext
    rintro ⟨π⟩
    obtain ⟨U, π, rfl⟩ := Over.mk_surjective π
    dsimp
    simp only [internalHom.map_app, unop_comp, assoc]
    congr 1
    simp

end

/-

TODO: `(K ⊗ F ⟶ G) ≃ K ⟶ internalHom F G`

-/

namespace internalHom

variable {K F G : Cᵒᵖ ⥤ D}

namespace homEquiv

section

variable (φ : F ⊗ K ⟶ G)

noncomputable def toFunApp (X : Cᵒᵖ) : K.obj X ⟶ (internalHom F G).obj X :=
  Functor.end_.lift _ (fun Y ↦ MonoidalClosed.curry
    ((_ ◁ K.map Y.unop.hom.op) ≫ φ.app (Opposite.op Y.unop.left))) sorry

@[reassoc (attr := simp)]
lemma toFunApp_app (X : Cᵒᵖ) {Y : C} (f : Y ⟶ X.unop) :
    toFunApp φ X ≫ Functor.enrichedHom.app _ _ (Opposite.op (Over.mk f)) =
      MonoidalClosed.curry
        ((_ ◁ K.map f.op) ≫ φ.app (Opposite.op Y)) := by
  simp [toFunApp, Functor.enrichedHom.app]

@[simps]
noncomputable def toFun : K ⟶ internalHom F G where
  app := toFunApp φ
  naturality := fun X Y f ↦ Functor.enrichedHom.hom_ext (fun ⟨Z⟩ ↦ by
    obtain ⟨Z, g, rfl⟩ := Over.mk_surjective Z
    dsimp
    rw [assoc, assoc, toFunApp_app]
    dsimp
    erw [internalHom.map_app]
    rw [toFunApp_app, ← MonoidalClosed.curry_natural_left, op_comp, Functor.map_comp,
      MonoidalCategory.whiskerLeft_comp, assoc]
    dsimp)

end

section

variable (ψ : K ⟶ internalHom F G)

noncomputable def invFunApp (X : Cᵒᵖ) : F.obj X ⊗ K.obj X ⟶ G.obj X :=
  MonoidalClosed.uncurry
    (ψ.app X ≫ Functor.enrichedHom.app _ _ (Opposite.op (Over.mk (𝟙 _))))

@[simp]
lemma curry_invFunApp (X : Cᵒᵖ) :
    MonoidalClosed.curry (invFunApp ψ X) =
      ψ.app X ≫ Functor.enrichedHom.app _ _ (Opposite.op (Over.mk (𝟙 _))) := by
  simp [invFunApp]

@[simps]
noncomputable def invFun : F ⊗ K ⟶ G where
  app := invFunApp ψ
  naturality := fun X Y f ↦ by
    dsimp [invFunApp]
    apply MonoidalClosed.curry_injective
    sorry

@[simp]
lemma toFun_invFun : toFun (invFun ψ) = ψ :=
  NatTrans.ext (by
    funext X
    refine Functor.enrichedHom.hom_ext (fun ⟨Y⟩ ↦ ?_)
    obtain ⟨Y, g, rfl⟩ := Over.mk_surjective Y
    dsimp
    rw [toFunApp_app, invFun_app]
    dsimp
    rw [MonoidalClosed.curry_natural_left, curry_invFunApp]
    dsimp
    rw [NatTrans.naturality_assoc]
    erw [map_app]
    congr 2
    simp)

end

@[simp]
lemma invFun_toFun (φ : F ⊗ K ⟶ G) : invFun (toFun φ) = φ := by
  ext X
  simp [invFunApp]

end homEquiv

noncomputable def homEquiv : (F ⊗ K ⟶ G) ≃ (K ⟶ internalHom F G) where
  toFun := homEquiv.toFun
  invFun := homEquiv.invFun
  left_inv _ := by simp
  right_inv _ := by simp

end internalHom


end Presheaf

end CategoryTheory
