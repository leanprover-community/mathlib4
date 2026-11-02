/-
Copyright (c) 2026 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.Algebra.Category.BialgCat.BimonEquivalence
public import Mathlib.CategoryTheory.Monoidal.Hopf_
public import Mathlib.Algebra.Category.HopfAlgCat.Monoidal


/-! # Equivalence of categories `HopfAlgCat R ≌ Hopf (ModuleCat R)` -/

@[expose] public section

universe u v

open CategoryTheory ModuleCat ComonObj MonObj Bimon MonModuleEquivalenceAlgebra RingTheory.LinearMap

variable {R : Type u} [CommRing R] (A : Type v) [Semiring A] [Bialgebra R A]

namespace CategoryTheory.HopfAlgCat

noncomputable instance (X : HopfAlgCat R) : BimonObj (ModuleCat.of R X) :=
  (bimonEquivalence.functor.obj ((forget₂ _ _).obj X)).bimon

noncomputable instance (X : HopfAlgCat R) : HopfObj (ModuleCat.of R X) where
  antipode := ModuleCat.ofHom (HopfAlgebraStruct.antipode R)
  antipode_left := ModuleCat.hom_ext HopfAlgebra.mul_antipode_rTensor_comul
  antipode_right := ModuleCat.hom_ext HopfAlgebra.mul_antipode_lTensor_comul

variable (R) in
/-- The natural functor from `R`-Hopf algebras to Hopf objects in the category of `R`-modules. -/
@[simps, instance_reducible]
noncomputable def toHopf : HopfAlgCat R ⥤ Hopf (ModuleCat R) where
  obj X := ⟨ModuleCat.of R X⟩
  map f := InducedCategory.homMk ((Bimon.toBimon R).map ((forget₂ _ _).map f))

/-- A Hopf object in the category of `R`-modules has a natural antipode. -/
noncomputable instance ofHopfObjHopfAlgebra (X : ModuleCat R) [HopfObj X] : HopfAlgebra R X where
  antipode := ModuleCat.Hom.hom (HopfObj.antipode (X:=X))
  mul_antipode_rTensor_comul := by
    have := congr(ModuleCat.Hom.hom $(HopfObj.antipode_left (X:=X)))
    simp only [ModuleCat.hom_comp] at this
    simp only [mul'_eq_μ_hom]
    exact this
  mul_antipode_lTensor_comul := by
    have := congr(ModuleCat.Hom.hom $(HopfObj.antipode_right (X:=X)))
    simp only [ModuleCat.hom_comp] at this
    simp only [mul'_eq_μ_hom]
    exact this

variable (R) in
/-- The natural functor from Hopf objects in the category of `R`-modules to `R`-Hopf algebras. -/
@[simp, instance_reducible]
noncomputable def ofHopf : Hopf (ModuleCat R) ⥤ HopfAlgCat R where
  obj X := .of R X.X
  map f := HopfAlgCat.ofHom <| ((ofBimon R).map ((inducedFunctor _).map f)).toBialgHom'


@[simps]
noncomputable def hopfEquivalence_unit (X : HopfAlgCat R) :
    (𝟭 (HopfAlgCat R)).obj X ≅ (toHopf R ⋙ ofHopf R).obj X where
  hom := HopfAlgCat.ofHom <| (Bimon.unit ((forget₂ _ (BialgCat R)).obj X)).hom.toBialgHom'
  inv := HopfAlgCat.ofHom <| (Bimon.unit ((forget₂ _ (BialgCat R)).obj X)).inv.toBialgHom'
  hom_inv_id := rfl
  inv_hom_id := rfl

@[simps]
noncomputable def hopfEquivalence_counit (X : Hopf (ModuleCat R)) :
    (ofHopf R ⋙ toHopf R).obj X ≅ (𝟭 (Hopf (ModuleCat R))).obj X where
  hom := InducedCategory.homMk (Bimon.counit X.toBimon).hom
  inv := InducedCategory.homMk (Bimon.counit X.toBimon).inv
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The natural category equivalence between `R`-Hopf algebras and Hopf objects in the
category of `R`-modules. -/
@[simps, instance_reducible]
noncomputable def hopfEquivalence : HopfAlgCat R ≌ Hopf (ModuleCat R) where
  functor := toHopf R
  inverse := ofHopf R
  unitIso := NatIso.ofComponents hopfEquivalence_unit
  counitIso := NatIso.ofComponents hopfEquivalence_counit

namespace hopfEquivalence

lemma mul_def (A : Hopf (ModuleCat R)) (x y : hopfEquivalence.inverse.obj A) :
    x * y = μ[A.X] (x ⊗ₜ y) := rfl

lemma hom_mul_eq_mul' (A : Type u) [Ring A] [HopfAlgebra R A] :
    μ[(hopfEquivalence.functor.obj (.of R A)).X].hom = LinearMap.mul' R A := rfl

lemma one_def (A : Hopf (ModuleCat R)) :
    1 = η[A.X] 1 := rfl

lemma hom_one_eq_algebra_linearMap (A : Type u) [Ring A] [HopfAlgebra R A] :
    η[(hopfEquivalence.functor.obj (.of R A)).X].hom = Algebra.linearMap R A := rfl

lemma comul_def (A : Hopf (ModuleCat R)) (x : hopfEquivalence.inverse.obj A) :
    δ x = Δ[A.X] x := rfl

lemma hom_comul_eq_comul (A : Type u) [Ring A] [HopfAlgebra R A] :
    Δ[(hopfEquivalence.functor.obj (.of R A)).X].hom = δ := rfl

lemma counit_def (A : Hopf (ModuleCat R)) (x : hopfEquivalence.inverse.obj A) :
    ε x = ε[A.X] x := rfl

lemma hom_counit_eq_counit (A : Type u) [Ring A] [HopfAlgebra R A] :
    ε[(hopfEquivalence.functor.obj (.of R A)).X].hom = (ε : _ →ₗ[R] _) := rfl

end hopfEquivalence

end CategoryTheory.HopfAlgCat
