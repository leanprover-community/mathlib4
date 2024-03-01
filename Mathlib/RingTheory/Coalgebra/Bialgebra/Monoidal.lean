import Mathlib.Algebra.Category.AlgebraCat.Symmetric
import Mathlib.RingTheory.TensorProduct
import Mathlib.RingTheory.Coalgebra.Bialgebra.Cat
import Mathlib.RingTheory.Coalgebra.Monoidal

universe v u

namespace Bialgebra
open scoped TensorProduct

variable {R A B C D : Type u} [CommRing R] [Ring A] [Ring B] [Ring C] [Ring D]
    [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]

set_option profiler true

lemma TensorProduct.counit_eq_toLinearMap :
    Coalgebra.counit (R := R) (A := A ⊗[R] B)
      = ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A)
      (Bialgebra.counitAlgHom R B))).toLinearMap := by
  simp only [Coalgebra.tensorProductCoalgebraStruct_counit, AlgHom.comp_toLinearMap,
    Algebra.TensorProduct.map_toLinearMap, Algebra.TensorProduct.lmul'_toLinearMap]
  rfl

lemma TensorProduct.comul_eq_toLinearMap :
  Coalgebra.comul (R := R) (A := A ⊗[R] B)
    = ((Algebra.TensorProduct.tensorTensorTensorComm R A A B B).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R A)
      (Bialgebra.comulAlgHom R B))).toLinearMap := by
  simp only [Coalgebra.tensorProductCoalgebraStruct_comul, AlgEquiv.toAlgHom_eq_coe,
    AlgHom.comp_toLinearMap, AlgEquiv.toAlgHom_toLinearMap,
    Algebra.TensorProduct.tensorTensorTensorComm_toLinearMap,
    Algebra.TensorProduct.map_toLinearMap]
  rfl

noncomputable instance {A B : Type u} [Ring A] [Ring B]
    [Bialgebra R A] [Bialgebra R B] : Bialgebra R (A ⊗[R] B) := by
  refine' Bialgebra.mk' R (A ⊗[R] B) _ (fun {x y} => _) _ (fun {x y} => _)
  <;> simp only [AlgHom.toLinearMap_apply, TensorProduct.counit_eq_toLinearMap,
    TensorProduct.comul_eq_toLinearMap]
  <;> simp only [map_one, map_mul]

@[simps! toLinearMap] noncomputable def TensorProduct.map (f : A →b[R] B) (g : C →b[R] D) :
    A ⊗[R] C →b[R] B ⊗[R] D :=
  { Coalgebra.TensorProduct.map f.toCoalgHom g.toCoalgHom,
      Algebra.TensorProduct.map f.toAlgHom g.toAlgHom with }

variable (A)

noncomputable abbrev lTensor (f : B →b[R] C) : A ⊗[R] B →b[R] A ⊗[R] C :=
  TensorProduct.map (BialgHom.id R A) f

noncomputable abbrev rTensor (f : B →b[R] C) : B ⊗[R] A →b[R] C ⊗[R] A :=
  TensorProduct.map f (BialgHom.id R A)

variable (R B C)

@[simps! toLinearMap] noncomputable def TensorProduct.assoc :
    (A ⊗[R] B) ⊗[R] C ≃b[R] A ⊗[R] (B ⊗[R] C) :=
  { Coalgebra.TensorProduct.assoc R A B C, Algebra.TensorProduct.assoc R A B C with
      map_one' := map_one (Algebra.TensorProduct.assoc R A B C)
      map_zero' := map_zero (Algebra.TensorProduct.assoc R A B C)
      map_comp_comul := sorry -- (Coalgebra.TensorProduct.assoc R A B C).toCoalgHom.map_comp_comul
    --- ^ughhhh something wrong with my homs and equivs? or my assoc??
  }

@[simps! toLinearMap] noncomputable def TensorProduct.lid : R ⊗[R] A ≃b[R] A :=
  { Coalgebra.TensorProduct.lid R A, Algebra.TensorProduct.lid R A with
    map_one' := map_one (Algebra.TensorProduct.lid R A)
    map_zero' := map_zero (Algebra.TensorProduct.lid R A)
     }

-- this works if I use an alg equiv that takes in 1 base ring . ?
@[simps! toLinearMap] noncomputable def TensorProduct.rid : A ⊗[R] R ≃b[R] A :=
  { Coalgebra.TensorProduct.rid R A, Algebra.TensorProduct.rid R R A with
    map_one' := map_one (Algebra.TensorProduct.rid R R A)
    map_mul' := sorry -- are you kidding meeeeeeeee
    map_zero' := map_zero (Algebra.TensorProduct.rid R R A) }

namespace MonoidalCategory
open TensorProduct CategoryTheory MonoidalCategory Bialgebra

@[simps] noncomputable instance : MonoidalCategoryStruct.{u} (BialgCat R) where
  tensorObj := fun X Y => BialgCat.of R (X ⊗[R] Y)
  whiskerLeft := fun X _ _ f => BialgCat.ofHom (lTensor X f)
  whiskerRight := fun f X => BialgCat.ofHom (rTensor X f)
  tensorHom := fun f g => BialgCat.ofHom (TensorProduct.map f g)
  tensorUnit := BialgCat.of R R
  associator := fun X Y Z => (TensorProduct.assoc R X Y Z).toBialgIso
  leftUnitor := fun X => (TensorProduct.lid R X).toBialgIso
  rightUnitor := fun X => (TensorProduct.rid R X).toBialgIso

set_option profiler true

@[simps] noncomputable def inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (BialgCat R) (AlgebraCat R)) where
  μIso := fun X Y => Iso.refl _
  whiskerLeft_eq := fun X Y Z f => by ext; rfl
  whiskerRight_eq := fun X f => by ext; rfl
  tensorHom_eq := fun f g => by ext; rfl
  εIso := Iso.refl _
  associator_eq := fun X Y Z => Algebra.TensorProduct.ext
      (Algebra.TensorProduct.ext (by ext; rfl) (by ext; rfl)) (by ext; rfl)
  leftUnitor_eq := fun X => Algebra.TensorProduct.ext rfl (by ext; rfl)
  rightUnitor_eq := fun X => Algebra.TensorProduct.ext (by ext; rfl) rfl

noncomputable instance : MonoidalCategory (BialgCat R) :=
  Monoidal.induced (forget₂ _ (AlgebraCat R)) (inducingFunctorData R)

#exit
open TensorProduct

variable (S : Type u) [CommRing S] [Algebra R S]

noncomputable instance instExtendScalars : Bialgebra S (S ⊗[R] A) :=
  { counit_one := sorry
    mul_compr₂_counit := sorry
    comul_one := sorry
    mul_compr₂_comul := sorry }

-- need a BialgHom.mk'
@[simps! toLinearMap] noncomputable def extendScalarsMap (f : A →b[R] B) :
    S ⊗[R] A →b[S] S ⊗[R] B :=
  { Coalgebra.extendScalarsMap S f.toCoalgHom with
    map_one' := by
      simp only [Coalgebra.extendScalarsMap_toLinearMap, Algebra.TensorProduct.one_def,
        AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.baseChange_tmul,
        BialgHom.toLinearMap_apply, _root_.map_one]
    map_mul' := by
      intro x y
      dsimp
      show (LinearMap.mul S (S ⊗[R] A)).compr₂ (LinearMap.baseChange S _) x y =
        (LinearMap.mul S (S ⊗[R] B)).compl₁₂ _ _ x y
      congr
      ext x y
      simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.compr₂_apply, LinearMap.mul_apply', Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        LinearMap.baseChange_tmul, BialgHom.toLinearMap_apply, _root_.map_mul,
        LinearMap.compl₁₂_apply]
    map_zero' := sorry
    commutes' := by
      intro r
      dsimp
      simp only [_root_.map_one]
    counit_comp := sorry
    map_comp_comul := sorry }

#exit
variable (S : Type u) [CommRing S] [Algebra R S] [Algebra R A] [Coalgebra R A] [Algebra R B]

/-(M ⊗[S] P) ⊗[R] Q ≃ₗ[S] M ⊗[S] P ⊗[R] Q-/
def idfk {A B : Type u} [Ring A] [Ring B] [Algebra R A] [Algebra R B] :
    S ⊗[R] (A ⊗[R] B) ≃ₗ[S] (S ⊗[R] A) ⊗[S] (S ⊗[R] B) :=
  (AlgebraTensorModule.assoc R R S S A B).symm ≪≫ₗ
  AlgebraTensorModule.congr (TensorProduct.rid S (S ⊗[R] A)).symm (LinearEquiv.refl R B)
  ≪≫ₗ (AlgebraTensorModule.assoc R S S (S ⊗[R] A) S B)

#check LinearMap.baseChange
#check
  ((AlgebraTensorModule.assoc R R S S A A).symm ≪≫ₗ
  AlgebraTensorModule.congr (TensorProduct.rid S (S ⊗[R] A)).symm (LinearEquiv.refl R A)
  ≪≫ₗ (AlgebraTensorModule.assoc R S S (S ⊗[R] A) S A)).toLinearMap ∘ₗ LinearMap.baseChange S (Coalgebra.comul (R := R) (A := A))
/- want
S ⊗[R] A \

S ⊗[R] A →ₗ[S] (S ⊗[R] A) ⊗[S] S ⊗[R] A-/
instance (S : Type u) [CommRing S] [Algebra R S] : CoalgebraStruct S (S ⊗[R] A) where
  comul := ((AlgebraTensorModule.assoc R R S S A A).symm ≪≫ₗ
  AlgebraTensorModule.congr (TensorProduct.rid S (S ⊗[R] A)).symm (LinearEquiv.refl R A)
  ≪≫ₗ (AlgebraTensorModule.assoc R S S (S ⊗[R] A) S A)).toLinearMap ∘ₗ LinearMap.baseChange S (Coalgebra.comul (R := R) (A := A))
  counit := _

#exit
instance hmmm (S : Type u) [CommRing S] : Bialgebra S (S ⊗[R] A) := by
  refine' Bialgebra.mk' _ _ _ _ _ _

end Bialgebra

@[simps] noncomputable def toMonObj (X : BialgCat R) : Mon_ (AlgebraCat R)ᵒᵖ where
  X := Opposite.op (AlgebraCat.of R X)
  one := (AlgebraCat.ofHom (Bialgebra.counitAlgHom R X)).op
  mul := (AlgebraCat.ofHom (Bialgebra.comulAlgHom R X)).op
  one_mul := by
    simp only [MonoidalCategory.whiskerRight, ← op_comp]
    congr 1
    exact AlgHom.toLinearMap_injective Coalgebra.rTensor_counit_comp_comul
  mul_one := by
    simp only [MonoidalCategory.whiskerLeft, ← op_comp]
    congr 1
    exact AlgHom.toLinearMap_injective Coalgebra.lTensor_counit_comp_comul
  mul_assoc := by
    simp only [MonoidalCategory.whiskerRight, MonoidalCategory.whiskerLeft, ← op_comp,
      MonoidalCategory.associator, Iso.op_hom, Iso.symm_hom]
    congr 1
    simp only [← Category.assoc, Iso.eq_comp_inv]
    exact AlgHom.toLinearMap_injective Coalgebra.coassoc

@[simps] def toMonMap {X Y : BialgCat R} (f : X ⟶ Y) : toMonObj Y ⟶ toMonObj X where
  hom := (AlgebraCat.ofHom f.toAlgHom).op
  one_hom := by
    simp only [toMonObj_X, toMonObj_one, ← op_comp]
    congr
    exact AlgHom.toLinearMap_injective f.counit_comp
  mul_hom := by
    simp only [toMonObj_X, toMonObj_mul, Opposite.unop_op, ← op_comp]
    congr 1
    exact AlgHom.toLinearMap_injective f.map_comp_comul.symm

@[simps] noncomputable def toMon : (BialgCat R)ᵒᵖ ⥤ Mon_ (AlgebraCat R)ᵒᵖ where
  obj := fun X => toMonObj X.unop
  map := fun f => toMonMap f.unop

@[simps] instance ofMonObjCoalgebraStruct (X : Mon_ (AlgebraCat R)ᵒᵖ) :
    CoalgebraStruct R X.X.unop where
  comul := X.mul.unop.toLinearMap
  counit := X.one.unop.toLinearMap

#exit
noncomputable abbrev monAlgebraOpToModule :
    Mon_ (AlgebraCat R)ᵒᵖ ⥤ Mon_ (ModuleCat R)ᵒᵖ :=
  (AlgebraCat.toModuleCatMonoidalFunctor R).mapOpposite.toLaxMonoidalFunctor.mapMon

noncomputable def toMonCompMonAlgebraOpToModule : toMon ⋙ monAlgebraOpToModule
    ≅ Functor.op (forget₂ (BialgCat R) (CoalgCat R)) ⋙ CoalgCat.toMon :=
  NatIso.ofComponents (fun X => sorry) sorry

end Bialgebra
