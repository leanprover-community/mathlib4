
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Closed.FunctorToTypes

open CategoryTheory Simplicial MonoidalCategory MonoidalClosed

namespace SSet

instance : MonoidalClosed SSet := FunctorToTypes.monoidalClosed

noncomputable section

@[ext]
lemma ihom_ext (Y Z : SSet) (n : SimplexCategoryᵒᵖ)
    (a b : (((ihom Y).obj Z)).obj n) : a.app = b.app → a = b := fun h ↦ by
  apply Functor.ihom_ext
  intro m f; exact congr_fun (congr_fun h m) f

@[ext]
lemma ihom_ihom_ext (X Y Z : SSet) (n : SimplexCategoryᵒᵖ)
    (a b : ((ihom X).obj ((ihom Y).obj Z)).obj n) : a.app = b.app → a = b := fun h ↦ by
  apply Functor.ihom_ext
  intro m f; exact congr_fun (congr_fun h m) f

def ihom_iso_hom (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ⟶ (ihom (X ⊗ Y)).obj Z where
  app := fun n x ↦ by
    refine ⟨fun m f ⟨Xm, Ym⟩ ↦ (x.app m f Xm).app m (𝟙 m) Ym, ?_⟩
    · intro m l f g
      ext ⟨Xm, Ym⟩
      change
        (x.app l (g ≫ f) (X.map f Xm)).app l (𝟙 l) (Y.map f Ym) =
          Z.map f ((x.app m g Xm).app m (𝟙 m) Ym)
      have := (congr_fun (x.naturality f g) Xm)
      simp at this
      rw [this]
      exact congr_fun ((x.app m g Xm).naturality f (𝟙 m)) Ym

def ihom_iso_inv (X Y Z : SSet) : (ihom (X ⊗ Y)).obj Z ⟶ (ihom X).obj ((ihom Y).obj Z) where
  app := fun n x ↦ by
    refine ⟨?_, ?_⟩
    · intro m f Xm
      refine ⟨fun l g Yl ↦ x.app l (f ≫ g) (X.map g Xm, Yl), ?_⟩
      · intro l k g h
        ext Yl
        have := congr_fun (x.naturality g (f ≫ h)) (X.map h Xm, Yl)
        simp at this ⊢
        exact this
    · intro m l f g
      ext
      simp [ihom, Closed.rightAdj, FunctorToTypes.rightAdj, Functor.ihom, Functor.hom₂Functor]

/- [X, [Y, Z]] ≅ [X ⊗ Y, Z] -/
def ihom_iso (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ≅ (ihom (X ⊗ Y)).obj Z where
  hom := ihom_iso_hom X Y Z
  inv := ihom_iso_inv X Y Z
  hom_inv_id := by
    ext n x m f Xm l g Yl
    change (x.app l (f ≫ g) (X.map g Xm)).app l (𝟙 l) Yl = (x.app m f Xm).app l g Yl
    have := congr_fun (x.naturality g f) Xm
    dsimp [ihom, Closed.rightAdj, FunctorToTypes.rightAdj, Functor.ihom,
      Functor.hom₂Functor] at this
    rw [this]
    aesop
  inv_hom_id := by
    ext n x m f ⟨Xm, Ym⟩
    change ((X.ihom_iso_hom Y Z).app n ((X.ihom_iso_inv Y Z).app n x)).app m f (Xm, Ym) =
      x.app m f (Xm, Ym)
    simp [ihom_iso_hom, ihom_iso_inv]

@[simp]
lemma ihom_braid_hom_eq {X Y Z : SSet} {n m : SimplexCategoryᵒᵖ} {f : n ⟶ m}
    (a : ((ihom (Y ⊗ X)).obj Z).obj n) :
    (((MonoidalClosed.pre (β_ X Y).hom).app Z).app n a).app m f =
      (β_ X Y).hom.app m ≫ a.app m f := by
  ext ⟨Xm, Ym⟩
  change (((Y ⊗ X).ihom Z).map f a).app m (𝟙 m) (Ym, Xm) = a.app m f (Ym, Xm)
  simp [Functor.ihom]

@[simp]
lemma ihom_braid_inv_eq {X Y Z : SSet} {n m : SimplexCategoryᵒᵖ} {f : n ⟶ m}
    (a : ((ihom (X ⊗ Y)).obj Z).obj n) :
    (((MonoidalClosed.pre (β_ X Y).inv).app Z).app n a).app m f = (β_ X Y).inv.app m ≫ a.app m f := by
  ext ⟨Ym, Xm⟩
  change (((X ⊗ Y).ihom Z).map f a).app m (𝟙 m) (Xm, Ym) = a.app m f (Xm, Ym)
  simp [Functor.ihom]

/- [X ⊗ Y, Z] ≅ [Y ⊗ X, Z] -/
def ihom_braid_iso (X Y Z : SSet) : (ihom (X ⊗ Y)).obj Z ≅ (ihom (Y ⊗ X)).obj Z where
  hom := (MonoidalClosed.pre (β_ X Y).inv).app Z
  inv := (MonoidalClosed.pre (β_ X Y).hom).app Z
  hom_inv_id := by
    ext n x m f ⟨Xm, Ym⟩
    change ((
      (MonoidalClosed.pre (β_ X Y).hom).app Z).app n
      (((MonoidalClosed.pre (β_ X Y).inv).app Z).app n x)).app m f (Xm, Ym) = _
    rw [ihom_braid_hom_eq, ihom_braid_inv_eq]
    rfl
  inv_hom_id := by
    ext n x m f ⟨Ym, Xm⟩
    change ((
      (MonoidalClosed.pre (β_ X Y).inv).app Z).app n
      (((MonoidalClosed.pre (β_ X Y).hom).app Z).app n x)).app m f (Ym, Xm) = _
    rw [ihom_braid_inv_eq, ihom_braid_hom_eq]
    rfl

/- [X, [Y, Z]] ≅ [X ⊗ Y, Z] ≅ [Y ⊗ X, Z] ≅ [Y, [X, Z]] -/
def ihom_iso' (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ≅ (ihom Y).obj ((ihom X).obj Z) :=
  (ihom_iso X Y Z) ≪≫ (ihom_braid_iso X Y Z) ≪≫ (ihom_iso Y X Z).symm

end

end SSet
