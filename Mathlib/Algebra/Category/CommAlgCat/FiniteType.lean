/-
Copyright (c) 2025 Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHomProperties

/-!
# The category of finitely generated `R`-algebras

We define the category of finitely generated `R`-algebras and show it is essentially small.
-/

universe w v u

open CategoryTheory Limits

variable (R : Type u) [CommRing R]

/-- The category of finitely generated `R`-algebras. -/
abbrev FGAlgCat := ObjectProperty.FullSubcategory
  fun A : CommAlgCat.{v, u} R ↦ Algebra.FiniteType R A

instance (A : FGAlgCat R) : Algebra.FiniteType R A.1 := A.2

/-- (Implementation detail): A small skeleton of `FGAlgCat`. -/
structure FGAlgCatSkeleton : Type u where
  /-- The number of generators. -/
  n : ℕ
  /-- The defining ideal. -/
  I : Ideal (MvPolynomial (Fin n) R)

/-- (Implementation detail): Realisation of a `FGAlgCatSkeleton`. -/
noncomputable def FGAlgCatSkeleton.eval (A : FGAlgCatSkeleton R) : FGAlgCat.{u} R :=
  ⟨CommAlgCat.of R (MvPolynomial (Fin A.n) R ⧸ A.I), inferInstanceAs <| Algebra.FiniteType _ _⟩

lemma Algebra.FiniteType.exists_fgAlgCatSkeleton (A : Type v) [CommRing A] [Algebra R A]
    [h : Algebra.FiniteType R A] :
    ∃ (P : FGAlgCatSkeleton R), Nonempty (A ≃ₐ[R] P.eval.obj) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
  exact ⟨⟨n, RingHom.ker f⟩, ⟨(Ideal.quotientKerAlgEquivOfSurjective hf).symm⟩⟩

/-- Universe lift functor for finitely generated algebras. -/
def FGAlgCat.uliftFunctor : FGAlgCat.{v} R ⥤ FGAlgCat.{max v w} R where
  obj A := ⟨.of R <| ULift A.1, .equiv inferInstance ULift.algEquiv.symm⟩
  map {A B} f := CommAlgCat.ofHom <|
    ULift.algEquiv.symm.toAlgHom.comp <| f.hom.comp ULift.algEquiv.toAlgHom

/-- The universe lift functor for finitely generated algebras is fully faithful. -/
def FGAlgCat.fullyFaithfulUliftFunctor : (FGAlgCat.uliftFunctor R).FullyFaithful where
  preimage {A B} f :=
    CommAlgCat.ofHom <| ULift.algEquiv.toAlgHom.comp <| f.hom.comp ULift.algEquiv.symm.toAlgHom

instance : (FGAlgCat.uliftFunctor R).Full :=
  (FGAlgCat.fullyFaithfulUliftFunctor R).full

instance : (FGAlgCat.uliftFunctor R).Faithful :=
  (FGAlgCat.fullyFaithfulUliftFunctor R).faithful

/-- The category of finitely generated algebras is essentially small. -/
instance : EssentiallySmall.{u} (FGAlgCat.{v} R) := by
  suffices h : EssentiallySmall.{u} (FGAlgCat.{max u v} R) by
    exact essentiallySmall_of_fully_faithful (FGAlgCat.uliftFunctor R)
  rw [essentiallySmall_iff]
  refine ⟨?_, ?_⟩
  · let f := toSkeleton ∘ (FGAlgCat.uliftFunctor R).obj ∘ FGAlgCatSkeleton.eval R
    refine small_of_surjective (f := f) fun A ↦ ?_
    simp only [Function.comp_apply, f, toSkeleton_eq_iff]
    obtain ⟨P, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R
      ((fromSkeleton (FGAlgCat R)).obj A).obj
    exact ⟨P, ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk <| ULift.algEquiv.trans e.symm)⟩⟩
  · refine ⟨fun A B ↦ ?_⟩
    obtain ⟨PA, ⟨eA⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R A.obj
    obtain ⟨PB, ⟨eB⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R B.obj
    let f (g : A ⟶ B) (x : PA.eval.obj) : PB.eval.obj := eB (g.hom (eA.symm x))
    refine small_of_injective (f := f) fun u v h ↦ ?_
    ext a
    obtain ⟨a, rfl⟩ := eA.symm.surjective a
    exact eB.injective (congr_fun h a)

section Under

open RingHom

/-- The category of finitely generated `R`-algebras is equivalent to the category of
finite type ring homomorphisms from `R`. -/
def FGAlgCat.equivUnder (R : CommRingCat.{u}) :
    FGAlgCat R ≌ MorphismProperty.Under (toMorphismProperty FiniteType) ⊤ R where
  functor.obj A := ⟨(commAlgCatEquivUnder R).functor.obj A.obj,
    (RingHom.finiteType_algebraMap (A := R) (B := A.obj)).mpr A.2⟩
  functor.map {A B} f := ⟨(commAlgCatEquivUnder R).functor.map f, trivial, trivial⟩
  inverse.obj A := ⟨(commAlgCatEquivUnder R).inverse.obj A.1, A.2⟩
  inverse.map {A B} f := (commAlgCatEquivUnder R).inverse.map f.hom
  unitIso := NatIso.ofComponents fun A ↦
    ObjectProperty.isoMk _ (CommAlgCat.isoMk { toRingEquiv := .refl A.1, commutes' _ := rfl })
  counitIso := .refl _

variable {Q : MorphismProperty CommRingCat.{u}}

lemma essentiallySmall_of_le (hQ : Q ≤ toMorphismProperty FiniteType) (R : CommRingCat.{u}) :
    EssentiallySmall.{u} (MorphismProperty.Under Q ⊤ R) :=
  essentiallySmall_of_fully_faithful
    (MorphismProperty.Comma.changeProp _ _ hQ
      le_rfl le_rfl ⋙ (FGAlgCat.equivUnder R).inverse)

end Under
