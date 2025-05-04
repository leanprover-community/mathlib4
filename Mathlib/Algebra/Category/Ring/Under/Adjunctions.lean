/-
Copyright (c) 2025 Ruiqi Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiqi Chen
-/
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Category.Ring.Adjunctions

/-!
# Adjunctions related to `Under (R : CommRingCat)`

In this file we provide functors `forgetRelative R S : Under S ⥤ Under R` for `S` an `R`-algebra,
`freeAbsolute R : Type u ⥤ Under R` the free functor given by polynomials over `R` and
`forget : Under R ⥤ Type u` the forgetful functor. And prove some basic facts including adjunctions
`tensorProd R S ⊣ forgetRelative R S` and `freeAbsolute R ⊣ forget`.
-/

noncomputable section

open TensorProduct CategoryTheory

universe u
variable {R S : CommRingCat.{u}}
variable [Algebra R S]

namespace CommRingCat

variable (R S) in
/-- The forgetful base change functor. -/
@[simps! map_right]
def forgetRelative : Under S ⥤ Under R := Under.map <| ofHom Algebra.algebraMap

/-- The adjunction between `tensorProd R S` and `forgetRelative R S`. -/
@[simps! unit_app counit_app]
def adjTensorForget : tensorProd R S ⊣ forgetRelative R S :=
  (Under.mapPushoutAdj (ofHom <| algebraMap R S)).ofNatIsoLeft ((R.tensorProdIsoPushout S).symm)

variable (R) in
/-- The free functor given by polynomials. -/
@[simps! map_right]
def freeAbsolute : Type u ⥤ Under R where
  obj σ := R.mkUnder <| MvPolynomial σ R
  map f := (MvPolynomial.rename f).toUnder
  map_id σ := congr_arg (fun x => x.toUnder) <| MvPolynomial.rename_id (σ := σ) (R := R)
  map_comp f g := congr_arg (fun x => x.toUnder) (MvPolynomial.rename_comp_rename (R := R) f g).symm

@[simp]
lemma freeAbsolute_obj (σ : Type u) : algebra ((freeAbsolute R).obj σ) = MvPolynomial.algebra :=
  mkUnder_eq <| MvPolynomial σ R

@[simp]
lemma freeAbsolute_map {σ τ : Type u} (f : σ ⟶ τ) :
    toAlgHom ((freeAbsolute R).map f) =
    (cast <| congr_arg₂
    (fun instA instB => @AlgHom R (MvPolynomial σ R) (MvPolynomial τ R) _ _ _ instA instB)
    (mkUnder_eq (MvPolynomial σ R)).symm
    (mkUnder_eq (MvPolynomial τ R)).symm) (MvPolynomial.rename f)
  := AlgHom.toUnder_eq (MvPolynomial.rename f)

/-- The forgetful functor `Under R ⥤ CommRingCat ⥤ Type`. -/
def forget : Under R ⥤ Type u := Under.forget R ⋙ HasForget.forget

lemma tensorProd_freeAbsolute_tauto : freeAbsolute R ⋙ R.tensorProd S = {
    obj σ := S.mkUnder <| S ⊗[R] (MvPolynomial σ R)
    map f := (Algebra.TensorProduct.map (AlgHom.id S S) (MvPolynomial.rename f)).toUnder
    map_id σ := by
      simp only
      have : MvPolynomial.rename (𝟙 σ) = AlgHom.id R (MvPolynomial σ R) :=
        MvPolynomial.rename_id (R := R) (σ := σ)
      rw [this, Algebra.TensorProduct.map_id]
      rfl
    map_comp f g := by
      simp only
      have : MvPolynomial.rename (R := R) (f ≫ g) =
        (MvPolynomial.rename g).comp (MvPolynomial.rename f) :=
        (MvPolynomial.rename_comp_rename f g).symm
      rw [this, Algebra.TensorProduct.map_id_comp, AlgHom.toUnder_comp]
    } := by
  apply CategoryTheory.Functor.ext
  · intro σ τ f
    unfold freeAbsolute tensorProd
    dsimp
    rw [AlgHom.toUnder_eq]
    -- find out the path induction
    have (ninstσ : Algebra R (MvPolynomial σ R)) (ninstτ : Algebra R (MvPolynomial τ R))
        (eqσ : ninstσ = MvPolynomial.algebra) (eqτ : ninstτ = MvPolynomial.algebra) :
        (@Algebra.TensorProduct.map _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (ninstσ) _ _ _ _ _ (ninstτ) (AlgHom.id S S)
        ((cast <| congr_arg₂ (fun instσ instτ => @AlgHom R (MvPolynomial σ R)
            (MvPolynomial τ R) _ _ _ instσ instτ)
        eqσ.symm eqτ.symm) (MvPolynomial.rename f))).toUnder =
        eqToHom (congr_arg
          (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial σ R) _ _ _
          (@Algebra.toModule _ _ _ _ inst)) <| eqσ) ≫
        (@Algebra.TensorProduct.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ MvPolynomial.algebra _ _ _ _ _
          MvPolynomial.algebra (AlgHom.id S S) (MvPolynomial.rename f)).toUnder ≫
        eqToHom (congr_arg
          (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial τ R) _ _ _
          (@Algebra.toModule _ _ _ _ inst)) <| eqτ).symm := by
      subst eqσ eqτ
      rfl
    exact this (algebra (R.mkUnder (MvPolynomial σ R))) (algebra (R.mkUnder (MvPolynomial τ R)))
      (mkUnder_eq (MvPolynomial σ R)) (mkUnder_eq (MvPolynomial τ R))

/-- We obtain `freeAbsolute S` by base changing `freeAbsolute R` using `⊗[R] S`. -/
def tensorProd_freeAbsolute : freeAbsolute R ⋙ R.tensorProd S ≅ freeAbsolute S := by
  -- To get rid of algebra_eq
  rw [tensorProd_freeAbsolute_tauto]
  exact (NatIso.ofComponents
    (fun σ => (MvPolynomial.algebraTensorAlgEquiv (σ := σ) R S).symm.toUnder)
    (fun {σ τ} f => by
      show (MvPolynomial.rename f).toUnder ≫
          (MvPolynomial.algebraTensorAlgEquiv R S).symm.toAlgHom.toUnder
          = (MvPolynomial.algebraTensorAlgEquiv R S).symm.toAlgHom.toUnder ≫
          (Algebra.TensorProduct.map (AlgHom.id S S) (MvPolynomial.rename f)).toUnder
      suffices (MvPolynomial.algebraTensorAlgEquiv R S).symm.toAlgHom.comp (MvPolynomial.rename f)
          = (Algebra.TensorProduct.map (AlgHom.id S S) (MvPolynomial.rename f)).comp
            (MvPolynomial.algebraTensorAlgEquiv R S).symm.toAlgHom from
        congr_arg (fun f => f.toUnder) this
      suffices (e : σ) →
          (MvPolynomial.algebraTensorAlgEquiv R S).symm.toAlgHom
          ((MvPolynomial.rename f) (MvPolynomial.X e))
          = (Algebra.TensorProduct.map (AlgHom.id S S) (MvPolynomial.rename f))
          ((MvPolynomial.algebraTensorAlgEquiv R S).symm.toAlgHom (MvPolynomial.X e)) from by
        exact MvPolynomial.algHom_ext this
      unfold MvPolynomial.algebraTensorAlgEquiv
      simp only [AlgEquiv.toAlgHom_eq_coe, MvPolynomial.rename_X, AlgHom.coe_coe,
        AlgEquiv.ofAlgHom_symm_apply, MvPolynomial.aeval_X, Algebra.TensorProduct.map_tmul,
        AlgHom.coe_id, id_eq, implies_true]
    )).symm

/-- A commutative ring is an algebra over `ℤ` which is commutative. -/
def Under_ℤ : Under (of (ULift.{u, 0} ℤ)) ≌ CommRingCat.{u} :=
  Under.equivalenceOfIsInitial isInitial

/-- The defined `freeAbsolute ℤ` is isomorphic to `free` -/
def freeAbsolute_ℤ_tauto : free ⋙ Under_ℤ.inverse ≅ freeAbsolute (of (ULift.{u, 0} ℤ)) where
  hom := {
    app σ := Under.homMk
      (CommRingCat.ofHom <| MvPolynomial.map <| Int.castRingHom (ULift.{u, 0} ℤ))
      (Limits.IsInitial.hom_ext isInitial _ _)
    naturality {σ τ} f := by
      apply Under.UnderMorphism.ext
      exact hom_ext <| MvPolynomial.map_comp_rename (Int.castRingHom (ULift.{u, 0} ℤ)) f
  }
  inv := {
    app σ := Under.homMk (CommRingCat.ofHom <| MvPolynomial.map RingHom.smulOneHom)
      (Limits.IsInitial.hom_ext isInitial _ _)
    naturality {σ τ} f := by
      apply Under.UnderMorphism.ext
      exact hom_ext <| MvPolynomial.map_comp_rename RingHom.smulOneHom f
  }
  hom_inv_id := by
    ext σ (x : MvPolynomial σ ℤ)
    show (MvPolynomial.map RingHom.smulOneHom)
      ((MvPolynomial.map (Int.castRingHom (ULift.{u, 0} ℤ))) x) = x
    rw [MvPolynomial.map_map _ (RingHom.smulOneHom (R := (ULift.{u, 0} ℤ)))]
    have : RingHom.smulOneHom.comp (Int.castRingHom (ULift.{u, 0} ℤ)) = RingHom.id ℤ := by aesop_cat
    rw [this]
    exact MvPolynomial.map_id x
  inv_hom_id := by
    ext σ (x : MvPolynomial σ (ULift.{u, 0} ℤ))
    show (MvPolynomial.map (Int.castRingHom (ULift.{u, 0} ℤ)))
      ((MvPolynomial.map RingHom.smulOneHom) x) = x
    rw [MvPolynomial.map_map]
    have : (Int.castRingHom (ULift.{u, 0} ℤ)).comp (RingHom.smulOneHom (R := ULift.{u, 0} ℤ))
        = RingHom.id (ULift.{u, 0} ℤ) := by aesop_cat
    rw [this]
    exact MvPolynomial.map_id x

instance (R : CommRingCat.{u}) : Algebra (of (ULift.{u, 0} ℤ)) R
  := RingHom.toAlgebra RingHom.smulOneHom

/-- The free forgetful adjunction of `Under R`. -/
def adjFreeForget : freeAbsolute R ⊣ forget :=
  (adj.comp (Under_ℤ.symm.toAdjunction.comp adjTensorForget)).ofNatIsoLeft
  (isoWhiskerRight freeAbsolute_ℤ_tauto ((of (ULift.{u, 0} ℤ)).tensorProd R)
      ≪≫ tensorProd_freeAbsolute)

end CommRingCat
