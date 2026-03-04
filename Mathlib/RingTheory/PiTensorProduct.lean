/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Data.Finset.NoncommProd

/-!
# Tensor product of `R`-algebras and rings

If `(Aᵢ)` is a family of `R`-algebras then the `R`-tensor product `⨂ᵢ Aᵢ` is an `R`-algebra as well
with structure map defined by `r ↦ r • 1`.

In particular if we take `R` to be `ℤ`, then this collapses into the tensor product of rings.
-/

@[expose] public section

open TensorProduct Function

variable {ι R' R : Type*} {A : ι → Type*}

namespace PiTensorProduct

noncomputable section AddCommMonoidWithOne

variable [CommSemiring R] [∀ i, AddCommMonoidWithOne (A i)] [∀ i, Module R (A i)]

instance instOne : One (⨂[R] i, A i) where
  one := tprod R 1

lemma one_def : 1 = tprod R (1 : Π i, A i) := rfl

instance instAddCommMonoidWithOne : AddCommMonoidWithOne (⨂[R] i, A i) where
  __ := inferInstanceAs% (AddCommMonoid (⨂[R] i, A i))
  __ := instOne

end AddCommMonoidWithOne

noncomputable section NonUnitalNonAssocSemiring

variable [CommSemiring R] [∀ i, NonUnitalNonAssocSemiring (A i)]
variable [∀ i, Module R (A i)] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)]

attribute [aesop safe] mul_add mul_smul_comm smul_mul_assoc add_mul in
/--
The multiplication in tensor product of rings is induced by `(xᵢ) * (yᵢ) = (xᵢ * yᵢ)`
-/
def mul : (⨂[R] i, A i) →ₗ[R] (⨂[R] i, A i) →ₗ[R] (⨂[R] i, A i) :=
  PiTensorProduct.piTensorHomMap₂ <| tprod R fun _ ↦ LinearMap.mul _ _

@[simp] lemma mul_tprod_tprod (x y : (i : ι) → A i) :
    mul (tprod R x) (tprod R y) = tprod R (x * y) := by
  simp only [mul, piTensorHomMap₂_tprod_tprod_tprod, LinearMap.mul_apply', Pi.mul_def]

instance instMul : Mul (⨂[R] i, A i) where
  mul x y := mul x y

lemma mul_def (x y : ⨂[R] i, A i) : x * y = mul x y := rfl

@[simp] lemma tprod_mul_tprod (x y : (i : ι) → A i) :
    tprod R x * tprod R y = tprod R (x * y) :=
  mul_tprod_tprod x y

theorem _root_.SemiconjBy.tprod {a₁ a₂ a₃ : Π i, A i}
    (ha : SemiconjBy a₁ a₂ a₃) :
    SemiconjBy (tprod R a₁) (tprod R a₂) (tprod R a₃) := by
  rw [SemiconjBy, tprod_mul_tprod, tprod_mul_tprod, ha]

nonrec theorem _root_.Commute.tprod {a₁ a₂ : Π i, A i} (ha : Commute a₁ a₂) :
    Commute (tprod R a₁) (tprod R a₂) :=
  ha.tprod

lemma smul_tprod_mul_smul_tprod (r s : R) (x y : Π i, A i) :
    (r • tprod R x) * (s • tprod R y) = (r * s) • tprod R (x * y) := by
  simp only [mul_def, map_smul, LinearMap.smul_apply, mul_tprod_tprod, mul_comm r s, mul_smul]

instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (⨂[R] i, A i) where
  __ := instMul
  __ := inferInstanceAs% (AddCommMonoid (⨂[R] i, A i))
  left_distrib _ _ _ := (mul _).map_add _ _
  right_distrib _ _ _ := mul.map_add₂ _ _ _
  zero_mul _ := mul.map_zero₂ _
  mul_zero _ := map_zero (mul _)

end NonUnitalNonAssocSemiring

noncomputable section NonAssocSemiring

variable [CommSemiring R] [∀ i, NonAssocSemiring (A i)]
variable [∀ i, Module R (A i)] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)]

protected lemma one_mul (x : ⨂[R] i, A i) : mul (tprod R 1) x = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod => simp
  | add _ _ h1 h2 => simp [map_add, h1, h2]

protected lemma mul_one (x : ⨂[R] i, A i) : mul x (tprod R 1) = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod => simp
  | add _ _ h1 h2 => simp [h1, h2]

instance instNonAssocSemiring : NonAssocSemiring (⨂[R] i, A i) where
  __ := instNonUnitalNonAssocSemiring
  one_mul := PiTensorProduct.one_mul
  mul_one := PiTensorProduct.mul_one

variable (R) in
/-- `PiTensorProduct.tprod` as a `MonoidHom`. -/
@[simps]
def tprodMonoidHom : (Π i, A i) →* ⨂[R] i, A i where
  toFun := tprod R
  map_one' := rfl
  map_mul' x y := (tprod_mul_tprod x y).symm

end NonAssocSemiring

noncomputable section NonUnitalSemiring

variable [CommSemiring R] [∀ i, NonUnitalSemiring (A i)]
variable [∀ i, Module R (A i)] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)]

protected lemma mul_assoc (x y z : ⨂[R] i, A i) : mul (mul x y) z = mul x (mul y z) := by
  -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext x y z
  dsimp [← mul_def]
  simpa only [tprod_mul_tprod] using congr_arg (tprod R) (mul_assoc x y z)

instance instNonUnitalSemiring : NonUnitalSemiring (⨂[R] i, A i) where
  __ := instNonUnitalNonAssocSemiring
  mul_assoc := PiTensorProduct.mul_assoc

end NonUnitalSemiring

noncomputable section Semiring

variable [CommSemiring R'] [CommSemiring R] [∀ i, Semiring (A i)]
variable [Algebra R' R] [∀ i, Algebra R (A i)] [∀ i, Algebra R' (A i)]
variable [∀ i, IsScalarTower R' R (A i)]

instance instSemiring : Semiring (⨂[R] i, A i) where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring

instance instAlgebra : Algebra R' (⨂[R] i, A i) where
  __ := hasSMul'
  algebraMap :=
  { toFun := (· • 1)
    map_one' := by simp
    map_mul' r s := show (r * s) • 1 = mul (r • 1) (s • 1) by
      rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.smul_apply, mul_comm,
        mul_smul]
      congr
      change (1 : ⨂[R] i, A i) = 1 * 1
      rw [mul_one]
    map_zero' := by simp
    map_add' := by simp [add_smul] }
  commutes' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change mul _ _ = mul _ _
    rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.smul_apply]
    change r • (1 * x) = r • (x * 1)
    rw [mul_one, one_mul]
  smul_def' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change _ = mul _ _
    rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply]
    change _ = r • (1 * x)
    rw [one_mul]

lemma algebraMap_apply (r : R') (i : ι) [DecidableEq ι] :
    algebraMap R' (⨂[R] i, A i) r = tprod R (Pi.mulSingle i (algebraMap R' (A i) r)) := by
  change r • tprod R 1 = _
  have : Pi.mulSingle i (algebraMap R' (A i) r) = update (fun i ↦ 1) i (r • 1) := by
    rw [Algebra.algebraMap_eq_smul_one]; rfl
  rw [this, ← smul_one_smul R r (1 : A i), MultilinearMap.map_update_smul, update_eq_self,
    smul_one_smul, Pi.one_def]

/--
The map `Aᵢ ⟶ ⨂ᵢ Aᵢ` given by `a ↦ 1 ⊗ ... ⊗ a ⊗ 1 ⊗ ...`
-/
@[simps]
def singleAlgHom [DecidableEq ι] (i : ι) : A i →ₐ[R] ⨂[R] i, A i where
  toFun a := tprod R (MonoidHom.mulSingle _ i a)
  map_one' := by simp only [map_one]; rfl
  map_mul' a a' := by simp [map_mul]
  map_zero' := MultilinearMap.map_update_zero _ _ _
  map_add' _ _ := MultilinearMap.map_update_add _ _ _ _ _
  commutes' r := show tprodCoeff R _ _ = r • tprodCoeff R _ _ by
    rw [Algebra.algebraMap_eq_smul_one, ← Pi.one_apply, MonoidHom.mulSingle_apply, Pi.mulSingle,
      smul_tprodCoeff]
    rfl

/--
Lifting a multilinear map to an algebra homomorphism from tensor product
-/
@[simps!]
def liftAlgHom {S : Type*} [Semiring S] [Algebra R S]
    (f : MultilinearMap R A S)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : (⨂[R] i, A i) →ₐ[R] S :=
  AlgHom.ofLinearMap (lift f) (show lift f (tprod R 1) = 1 by simp [one]) <|
    LinearMap.map_mul_iff _ |>.mpr <| by aesop

@[simp] lemma tprod_noncommProd {κ : Type*} (s : Finset κ) (x : κ → Π i, A i) (hx) :
    tprod R (s.noncommProd x hx) = s.noncommProd (fun k => tprod R (x k))
      (hx.imp fun _ _ => Commute.tprod) :=
  Finset.map_noncommProd s x _ (tprodMonoidHom R)

/-- To show two algebra morphisms from finite tensor products are equal, it suffices to show that
they agree on elements of the form $1 ⊗ ⋯ ⊗ a ⊗ 1 ⊗ ⋯$. -/
@[ext high]
theorem algHom_ext {S : Type*} [Finite ι] [DecidableEq ι] [Semiring S] [Algebra R S]
    ⦃f g : (⨂[R] i, A i) →ₐ[R] S⦄ (h : ∀ i, f.comp (singleAlgHom i) = g.comp (singleAlgHom i)) :
    f = g :=
  AlgHom.toLinearMap_injective <| PiTensorProduct.ext <| MultilinearMap.ext fun x =>
    suffices f.toMonoidHom.comp (tprodMonoidHom R) = g.toMonoidHom.comp (tprodMonoidHom R) from
      DFunLike.congr_fun this x
    MonoidHom.pi_ext fun i xi => DFunLike.congr_fun (h i) xi

end Semiring

noncomputable section Ring

variable [CommRing R] [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]

instance instRing : Ring (⨂[R] i, A i) where
  __ := instSemiring
  __ := inferInstanceAs% <| AddCommGroup (⨂[R] i, A i)

end Ring

noncomputable section CommSemiring

variable [CommSemiring R] [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)]

protected lemma mul_comm (x y : ⨂[R] i, A i) : mul x y = mul y x := by
  suffices mul (R := R) (A := A) = mul.flip from
    DFunLike.congr_fun (DFunLike.congr_fun this x) y
  ext x y
  dsimp
  simp only [mul_tprod_tprod, mul_tprod_tprod, mul_comm x y]

instance instCommSemiring : CommSemiring (⨂[R] i, A i) where
  __ := instSemiring
  __ := inferInstanceAs% <| AddCommMonoid (⨂[R] i, A i)
  mul_comm := PiTensorProduct.mul_comm

@[simp] lemma tprod_prod {κ : Type*} (s : Finset κ) (x : κ → Π i, A i) :
    tprod R (∏ k ∈ s, x k) = ∏ k ∈ s, tprod R (x k) :=
  map_prod (tprodMonoidHom R) x s

section

variable [Fintype ι]

variable (R ι)

/--
The algebra equivalence from the tensor product of the constant family with
value `R` to `R`, given by multiplication of the entries.
-/
noncomputable def constantBaseRingEquiv : (⨂[R] _ : ι, R) ≃ₐ[R] R :=
  letI toFun := lift (MultilinearMap.mkPiAlgebra R ι R)
  AlgEquiv.ofAlgHom
    (AlgHom.ofLinearMap
      toFun
      ((lift.tprod _).trans Finset.prod_const_one)
      (by
        -- one of these is required, the other is a performance optimization
        letI : IsScalarTower R (⨂[R] x : ι, R) (⨂[R] x : ι, R) :=
          IsScalarTower.right (R := R) (A := ⨂[R] (x : ι), R)
        letI : SMulCommClass R (⨂[R] x : ι, R) (⨂[R] x : ι, R) :=
          Algebra.to_smulCommClass (R := R) (A := ⨂[R] x : ι, R)
        rw [LinearMap.map_mul_iff]
        ext
        change toFun (tprod R _ * tprod R _) = toFun (tprod R _) * toFun (tprod R _)
        simp_rw [tprod_mul_tprod, toFun, lift.tprod, MultilinearMap.mkPiAlgebra_apply,
          Pi.mul_apply, Finset.prod_mul_distrib]))
    (Algebra.ofId _ _)
    (by ext)
    (by classical ext)

variable {R ι}

@[simp]
theorem constantBaseRingEquiv_tprod (x : ι → R) :
    constantBaseRingEquiv ι R (tprod R x) = ∏ i, x i := by
  simp [constantBaseRingEquiv]

@[simp]
theorem constantBaseRingEquiv_symm (r : R) :
    (constantBaseRingEquiv ι R).symm r = algebraMap _ _ r := rfl

end

end CommSemiring

noncomputable section CommRing

variable [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
instance instCommRing : CommRing (⨂[R] i, A i) where
  __ := instCommSemiring
  __ := inferInstanceAs% <| AddCommGroup (⨂[R] i, A i)

end CommRing

end PiTensorProduct
