/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!

# The functor of points

Given a scheme `X`, the functor of points associated to `X` is the functor
from the category of commutative rings to types sending `R` to
`X(R) = Hom(Spec R, X)`.

This is of course functorial in `X` as well, providing a functor
`Scheme ⥤ CommRingCat ⥤ Type`.

We construct this functor in this file. It turns out that this functor is fully faithful,
which we also prove in this file.

## Definitions:

- Given `X : Scheme`, `X.functorOfPoints` is its associated functor of points.
- `schemeToFunctor` is the functor `Scheme ⥤ CommRingCat ⥤ Type` (with suitable universes).
- `schemeToFunctor` is provided with `Full` and `Faithful` instances.

## Projects

- Notation for `X.functorOfPoints`.
- `X.functorOfPoints` is a Zariski sheaf for any `X : Scheme`.
- Characterize the essential image of `schemeToFunctorOfPoints`.

-/

noncomputable section

namespace AlgebraicGeometry

universe v u

open CategoryTheory


/-- The functor of points associated to a scheme. -/
@[simps! obj map]
def Scheme.functorOfPoints (X : Scheme.{u}) : CommRingCat.{u} ⥤ Type u :=
  Spec.rightOp ⋙ yoneda.obj X

/-- A morphism of schemes induces a morphism on the functors of points. -/
@[simps! app]
def Scheme.mapFunctorOfPoints {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.functorOfPoints ⟶ Y.functorOfPoints :=
  whiskerLeft _ <| yoneda.map f

@[simp]
lemma Scheme.mapFunctorOfPoints_id (X : Scheme.{u}) :
    mapFunctorOfPoints (𝟙 X) = 𝟙 _ :=
  whiskerLeft_id _

@[simp]
lemma Scheme.mapFunctorOfPoints_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapFunctorOfPoints (f ≫ g) = mapFunctorOfPoints f ≫ mapFunctorOfPoints g :=
  by simp [mapFunctorOfPoints]

/-- The "functor of points" functor, which sends `X` to `X.functorOfPoints` on objects
and `f` to `Scheme.mapFunctorOfPoints f` on morphisms. -/
@[simps]
def schemeToFunctor : Scheme.{u} ⥤ CommRingCat.{u} ⥤ Type u where
  obj X := X.functorOfPoints
  map f := Scheme.mapFunctorOfPoints f

instance faithfulFunctorOfPoints : Faithful schemeToFunctor where
  map_injective := by
    intro X Y f g h
    let 𝓤 := X.affineOpenCover
    apply 𝓤.openCover.hom_ext
    intro j
    exact congr_arg (fun e => e.app (𝓤.obj j) (𝓤.map j)) h

/-- IMPLEMENTATION DETAIL: This is used to show the fullness of `schemeToFunctor`. -/
def homOfFunctorOfPoints {X Y : Scheme.{u}} (f : X.functorOfPoints ⟶ Y.functorOfPoints) :
    X ⟶ Y :=
  X.affineOpenCover.openCover.glueMorphisms (fun j => f.app _ <| X.affineOpenCover.map _) <| by
    intro i j
    apply schemeToFunctor.map_injective; ext A e : 3
    dsimp at e ⊢
    let 𝓤 := X.affineOpenCover
    obtain ⟨fst',hfst⟩ := Scheme.Spec.map_surjective
      (e ≫ (Limits.pullback.fst : Limits.pullback (𝓤.map i) (𝓤.map j) ⟶ _))
    obtain ⟨snd',hsnd⟩ := Scheme.Spec.map_surjective
      (e ≫ (Limits.pullback.snd : Limits.pullback (𝓤.map i) (𝓤.map j) ⟶ _))
    slice_lhs 1 2 => erw [← hfst]
    slice_rhs 1 2 => erw [← hsnd]
    have hi := congr_fun (f.naturality fst'.unop) (𝓤.map i)
    have hj := congr_fun (f.naturality snd'.unop) (𝓤.map j)
    dsimp at hi hj
    rw [← hi, ← hj]
    simp_rw [hfst, hsnd, Category.assoc, Limits.pullback.condition]

instance fullFunctorOfPoints : Full schemeToFunctor where
  preimage f := homOfFunctorOfPoints f
  witness := by
    intro X Y f
    ext A e : 3
    dsimp [homOfFunctorOfPoints] at e ⊢
    let 𝓤 := X.affineCover
    let 𝓥 := 𝓤.pullbackCover e
    let 𝓦 := 𝓥.affineRefinement
    let ι : 𝓦.openCover ⟶ 𝓥 := Scheme.OpenCover.fromAffineRefinement.{u,u} 𝓥
    apply 𝓦.openCover.hom_ext
    intro j
    dsimp
    have aux : 𝓦.map j ≫ e = ι.app j ≫ Limits.pullback.snd ≫ X.affineCover.map j.fst := by
      have := ι.w j
      dsimp at this
      rw [← this, Category.assoc]
      congr 1
      apply Limits.pullback.condition
    rw [reassoc_of% aux, Scheme.OpenCover.ι_glueMorphisms]
    let ⟨w,hw⟩ := Scheme.Spec.map_surjective (𝓦.map j)
    have := congr_fun (f.naturality w.unop) e
    dsimp at this
    rw [← hw, ← this, hw, aux]
    let ⟨w,hw⟩ := Scheme.Spec.map_surjective (ι.app j ≫ Limits.pullback.snd)
    simp only [← Category.assoc, ← hw]
    exact congr_fun (f.naturality w.unop) (X.affineCover.map j.fst) |>.symm

def IsBasicOpen {A B : CommRingCat.{u}} (ι : A ⟶ B) (f : A) : Prop :=
  letI : Algebra A B := RingHom.toAlgebra ι
  IsLocalization.Away f B

lemma isOpenImmersion_of_isBasicOpen
    {A B : CommRingCat.{u}} (ι : A ⟶ B) (f : A) (h : IsBasicOpen ι f) :
    IsOpenImmersion (Scheme.Spec.map ι.op) := by
  let _ : Algebra A B := RingHom.toAlgebra ι
  let _ : IsLocalization.Away f B := h
  let e' : Localization.Away f ≃ₐ[A] B := Localization.algEquiv _ B
  let B' := CommRingCat.of <| Localization.Away f
  let e : B' ≅ B := e'.toRingEquiv.toCommRingCatIso
  let ι' : A ⟶ B' := algebraMap A <| Localization.Away f
  have : ι = ι' ≫ e.hom := by
    ext t
    exact AlgHom.commutes e'.toAlgHom t |>.symm
  rw [this]
  simp only [op_comp, Functor.map_comp]
  suffices IsOpenImmersion (Scheme.Spec.map ι'.op) from inferInstance
  apply Scheme.basic_open_isOpenImmersion

structure indexedZariskiCover (A : CommRingCat.{u}) where
  J : Type v
  B : J → CommRingCat.{u}
  f : J → A
  ι (j : J) : A ⟶ B j
  isLocalizationAt (j : J) : IsBasicOpen (ι j) (f j)
  covers : Ideal.span (Set.range f) = ⊤

lemma indexedZariskiCover.exists_index
    {A : CommRingCat.{u}} (𝓤 : indexedZariskiCover A)
    (p : PrimeSpectrum A) : ∃ j : 𝓤.J, 𝓤.f j ∉ p.asIdeal := by
  by_contra! h
  apply p.IsPrime.ne_top
  suffices ⊤ ≤ p.asIdeal from Submodule.eq_top_iff'.mpr fun x ↦ this trivial
  rw [← 𝓤.covers, Ideal.span_le]
  rintro j ⟨j,rfl⟩
  apply h

def indexedZariskiCover.affineOpenCover {A : CommRingCat.{u}} (𝓤 : indexedZariskiCover A) :
    (Scheme.Spec.obj <| .op A).AffineOpenCover where
  J := 𝓤.J
  obj := 𝓤.B
  map j := Scheme.Spec.map <| 𝓤.ι j |>.op
  f := fun (p : PrimeSpectrum A) => (𝓤.exists_index p).choose
  Covers := fun (p : PrimeSpectrum A) => by
    let j := (𝓤.exists_index p).choose
    let _ : Algebra A (𝓤.B j) := RingHom.toAlgebra <| 𝓤.ι j
    let _ : IsLocalization.Away (𝓤.f j) (𝓤.B j) := 𝓤.isLocalizationAt j
    change p ∈ Set.range ⇑(PrimeSpectrum.comap (algebraMap A (𝓤.B j)))
    rw [PrimeSpectrum.localization_away_comap_range (𝓤.B j) (𝓤.f j)]
    exact (𝓤.exists_index p).choose_spec
  IsOpen j := isOpenImmersion_of_isBasicOpen _ (𝓤.f j) (𝓤.isLocalizationAt _)

theorem indexedZariskiCover.desc
    {X : Scheme.{u}}
    {A : CommRingCat.{u}}
    (𝓤 : indexedZariskiCover.{u} A)
    (b : (j : 𝓤.J) → X.functorOfPoints.obj (𝓤.B j))
    (hb : ∀ (i j : 𝓤.J) (C : CommRingCat.{u})
      (ιi : 𝓤.B i ⟶ C) (ιj : 𝓤.B j ⟶ C),
      𝓤.ι i ≫ ιi = 𝓤.ι j ≫ ιj →
      X.functorOfPoints.map ιi (b i) = X.functorOfPoints.map ιj (b j)) :
    X.functorOfPoints.obj A :=
  𝓤.affineOpenCover.openCover.glueMorphisms b <| by
    intro i j
    apply schemeToFunctor.map_injective
    ext A e : 3
    dsimp at e ⊢
    simp only [← Category.assoc]
    obtain ⟨fst,hfst⟩ := Scheme.Spec.map_surjective (e ≫ Limits.pullback.fst)
    obtain ⟨snd,hsnd⟩ := Scheme.Spec.map_surjective (e ≫ Limits.pullback.snd)
    rw [← hfst, ← hsnd]
    apply hb
    apply Quiver.Hom.op_inj
    apply Scheme.Spec.map_injective
    simp only [Opposite.unop_op, op_comp, Functor.map_comp]
    show Scheme.Spec.map fst ≫ _ = Scheme.Spec.map snd ≫ _
    simp_rw [hfst, hsnd, Category.assoc]
    congr 1
    exact Limits.pullback.condition

lemma indexedZariskiCover.restirct_desc
    {X : Scheme.{u}}
    {A : CommRingCat.{u}}
    (𝓤 : indexedZariskiCover.{u} A)
    (b : (j : 𝓤.J) → X.functorOfPoints.obj (𝓤.B j))
    (hb : ∀ (i j : 𝓤.J) (C : CommRingCat.{u})
      (ιi : 𝓤.B i ⟶ C) (ιj : 𝓤.B j ⟶ C),
      𝓤.ι i ≫ ιi = 𝓤.ι j ≫ ιj →
      X.functorOfPoints.map ιi (b i) = X.functorOfPoints.map ιj (b j)) (j : 𝓤.J) :
    X.functorOfPoints.map (𝓤.ι j) (𝓤.desc b hb) = b _ := by
  unfold indexedZariskiCover.desc
  apply Scheme.OpenCover.ι_glueMorphisms

lemma indexedZariskiCover.hom_ext
    {X : Scheme.{u}}
    {A : CommRingCat.{u}}
    (𝓤 : indexedZariskiCover.{u} A)
    (f g : X.functorOfPoints.obj A)
    (h : ∀ j : 𝓤.J, X.functorOfPoints.map (𝓤.ι j) f = X.functorOfPoints.map (𝓤.ι j) g) :
    f = g :=
  𝓤.affineOpenCover.openCover.hom_ext _ _ h

end AlgebraicGeometry
