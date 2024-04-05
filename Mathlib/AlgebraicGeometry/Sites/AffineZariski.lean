import Mathlib

open CategoryTheory AlgebraicGeometry

universe v u

noncomputable section

namespace AlgebraicGeometry

@[simps]
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

instance : Full functorOfPoints where
  preimage {X Y} f :=
    let 𝓤 := X.affineOpenCover
    𝓤.openCover.glueMorphisms (fun b => f.app (𝓤.obj b) (𝓤.map b)) <| by
      intro a b
      dsimp
      apply functorOfPoints.map_injective
      ext A e : 3
      dsimp [functorOfPoints] at e ⊢
      let P := Limits.pullback (𝓤.map a) (𝓤.map b)
      let fst : P ⟶ _ := Limits.pullback.fst
      let snd : P ⟶ _ := Limits.pullback.snd
      show e ≫ fst ≫ _ = e ≫ snd ≫ _
      simp only [← Category.assoc]
      obtain ⟨fst',hfst⟩ : ∃ t, Scheme.Spec.map t = e ≫ fst := Scheme.Spec.map_surjective _
      obtain ⟨snd',hsnd⟩ : ∃ t, Scheme.Spec.map t = e ≫ snd := Scheme.Spec.map_surjective _
      rw [← hfst, ← hsnd]
      have hfst' := congr_fun (f.naturality fst'.unop) (𝓤.map a)
      have hsnd' := congr_fun (f.naturality snd'.unop) (𝓤.map b)
      dsimp [functorOfPoints] at hfst' hsnd'
      rw [← hfst', ← hsnd', hfst, hsnd, Category.assoc, Category.assoc, Limits.pullback.condition]
  witness := sorry
