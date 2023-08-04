import Mathlib.CategoryTheory.Limits.Presheaf

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

open Opposite

variable {C : Type u₁} [Category.{v₁} C] (A : Cᵒᵖ ⥤ Type v₁)

@[simps]
def tautologicalCocone : Cocone (CostructuredArrow.proj yoneda A ⋙ yoneda) where
  pt := A
  ι := { app := fun X => X.hom }

lemma yonedaEquiv_comp (X : C) (F G : Cᵒᵖ ⥤ Type v₁) (α : yoneda.obj X ⟶ F) (β : F ⟶ G)  :
    yonedaEquiv (α ≫ β) = β.app _ (yonedaEquiv α) :=
  rfl

lemma yonedaEquiv_comp' (X : Cᵒᵖ) (F G : Cᵒᵖ ⥤ Type v₁) (α : yoneda.obj (unop X) ⟶ F) (β : F ⟶ G)  :
    yonedaEquiv (α ≫ β) = β.app X (yonedaEquiv α) :=
  rfl

lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.map g (yonedaEquiv f) = yonedaEquiv (yoneda.map g.unop ≫ f) :=
  yonedaEquiv_naturality _ _

@[simp]
lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : yonedaEquiv (yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

lemma yonedaEquiv_symm_map (X Y : Cᵒᵖ) (f : X ⟶ Y) (t : A.obj X) :
    yonedaEquiv.symm (A.map f t) = yoneda.map f.unop ≫ yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

@[simps!]
def CostructuredArrow.precomp {Y Z : C} (f : Y ⟶ Z) (u : yoneda.obj Z ⟶ A) :
    CostructuredArrow.mk (yoneda.map f ≫ u) ⟶ CostructuredArrow.mk u :=
  CostructuredArrow.homMk f rfl

def isColimitTautologicalCocone : IsColimit (tautologicalCocone A) where
  desc := fun s => by
    refine' ⟨fun X t => yonedaEquiv (s.ι.app (CostructuredArrow.mk (yonedaEquiv.symm t))), _⟩
    intros X Y f
    ext t
    dsimp
    rw [yonedaEquiv_naturality', yonedaEquiv_symm_map]
    simpa using (s.ι.naturality (CostructuredArrow.precomp A f.unop (yonedaEquiv.symm t))).symm
  fac := by
    intro s t
    dsimp
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]
    dsimp only
    rw [Equiv.symm_apply_apply]
    rfl
  uniq := by
    intro s j h
    ext V x
    obtain ⟨t, rfl⟩ := yonedaEquiv.surjective x
    dsimp
    rw [Equiv.symm_apply_apply, ← yonedaEquiv_comp']
    exact congr_arg _ (h (CostructuredArrow.mk t))


end CategoryTheory.Limits
