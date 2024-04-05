import Mathlib

open CategoryTheory AlgebraicGeometry

universe v u

noncomputable section

namespace AlgebraicGeometry

def functorOfPoints : Scheme.{u} ⥤ CommRingCat.{u} ⥤ Type u where
  obj X := Scheme.Spec.rightOp ⋙ yoneda.obj X
  map f := whiskerLeft _ <| yoneda.map f

structure AffineOpenCover (X : Scheme.{u}) where
  α : Type v
  obj : α → CommRingCat.{u}
  map : (a : α) → Scheme.Spec.obj (.op (obj a)) ⟶ X
  f : X.carrier → α
  covers : ∀ x, x ∈ Set.range (map (f x)).1.base
  isOpen : ∀ x, IsOpenImmersion (map x) := by infer_instance

def AffineOpenCover.openCover {X : Scheme.{u}} (𝓤 : AffineOpenCover X) : X.OpenCover where
  J := 𝓤.α
  obj a := Scheme.Spec.obj <| .op <| 𝓤.obj a
  map := 𝓤.map
  f := 𝓤.f
  Covers := 𝓤.covers
  IsOpen := 𝓤.isOpen

def Scheme.affineOpenCover (X : Scheme.{u}) : AffineOpenCover.{u} X := by
  let 𝓤 := X.affineCover
  fconstructor
  · exact 𝓤.J
  · exact fun x => (X.local_affine x).choose_spec.choose
  · exact 𝓤.map
  · exact 𝓤.f
  · exact 𝓤.Covers
  · exact 𝓤.IsOpen

instance : Faithful functorOfPoints where
  map_injective := by
    intro X Y f g h
    apply X.affineOpenCover.openCover.hom_ext
    intro b
    dsimp [AffineOpenCover.openCover] at b
    let R := X.affineOpenCover.obj b
    apply_fun (fun e => e.app R (X.affineOpenCover.map b)) at h
    exact h
