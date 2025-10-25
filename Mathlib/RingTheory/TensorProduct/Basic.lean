/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Module.Rat
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The tensor product of R-algebras

This file provides results about the multiplicative structure on `A ⊗[R] B` when `R` is a
commutative (semi)ring and `A` and `B` are both `R`-algebras. On these tensor products,
multiplication is characterized by `(a₁ ⊗ₜ b₁) * (a₂ ⊗ₜ b₂) = (a₁ * a₂) ⊗ₜ (b₁ * b₂)`.

## Main declarations

- `Algebra.TensorProduct.semiring`: the ring structure on `A ⊗[R] B` for two `R`-algebras `A`, `B`.
- `Algebra.TensorProduct.leftAlgebra`: the `S`-algebra structure on `A ⊗[R] B`, for when `A` is
  additionally an `S` algebra.
- the structure isomorphisms
  * `Algebra.TensorProduct.lid : R ⊗[R] A ≃ₐ[R] A`
  * `Algebra.TensorProduct.rid : A ⊗[R] R ≃ₐ[S] A` (usually used with `S = R` or `S = A`)
  * `Algebra.TensorProduct.comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A`
  * `Algebra.TensorProduct.assoc : ((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C))`
- `Algebra.TensorProduct.liftEquiv`: a universal property for the tensor product of algebras.

## References

* [C. Kassel, *Quantum Groups* (§II.4)][Kassel1995]

-/

set_option linter.style.longFile 1700

assert_not_exists Equiv.Perm.cycleType

open scoped TensorProduct

open TensorProduct


namespace LinearMap

section liftBaseChange

variable {R M N} (A) [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
variable [AddCommMonoid N] [Module R M] [Module R N] [Module A N] [IsScalarTower R A N]

/--
If `M` is an `R`-module and `N` is an `A`-module, then `A`-linear maps `A ⊗[R] M →ₗ[A] N`
correspond to `R` linear maps `M →ₗ[R] N` by composing with `M → A ⊗ M`, `x ↦ 1 ⊗ x`.
-/
def liftBaseChangeEquiv : (M →ₗ[R] N) ≃ₗ[A] (A ⊗[R] M →ₗ[A] N) :=
  (LinearMap.ringLmapEquivSelf _ _ _).symm.trans (AlgebraTensorModule.lift.equiv _ _ _ _ _ _)

/-- If `N` is an `A` module, we may lift a linear map `M →ₗ[R] N` to `A ⊗[R] M →ₗ[A] N` -/
abbrev liftBaseChange (l : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] N :=
  LinearMap.liftBaseChangeEquiv A l

@[simp]
lemma liftBaseChange_tmul (l : M →ₗ[R] N) (x y) : l.liftBaseChange A (x ⊗ₜ y) = x • l y := rfl

lemma liftBaseChange_one_tmul (l : M →ₗ[R] N) (y) : l.liftBaseChange A (1 ⊗ₜ y) = l y := by simp

@[simp]
lemma liftBaseChangeEquiv_symm_apply (l : A ⊗[R] M →ₗ[A] N) (x) :
    (liftBaseChangeEquiv A).symm l x = l (1 ⊗ₜ x) := rfl

lemma liftBaseChange_comp {P} [AddCommMonoid P] [Module A P] [Module R P] [IsScalarTower R A P]
    (l : M →ₗ[R] N) (l' : N →ₗ[A] P) :
      l' ∘ₗ l.liftBaseChange A = (l'.restrictScalars R ∘ₗ l).liftBaseChange A := by
  ext
  simp

@[simp]
lemma range_liftBaseChange (l : M →ₗ[R] N) :
    LinearMap.range (l.liftBaseChange A) = Submodule.span A (LinearMap.range l) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on
    · simp
    · rw [LinearMap.liftBaseChange_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [map_add]
      exact add_mem ‹_› ‹_›
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp⟩

end liftBaseChange

end LinearMap

namespace Module.End

open LinearMap

variable (R M N : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The map `LinearMap.lTensorHom` which sends `f ↦ 1 ⊗ f` as a morphism of algebras. -/
@[simps!]
def lTensorAlgHom : Module.End R M →ₐ[R] Module.End R (N ⊗[R] M) :=
  .ofLinearMap (lTensorHom (M := N)) (lTensor_id N M) (lTensor_mul N)

/-- The map `LinearMap.rTensorHom` which sends `f ↦ f ⊗ 1` as a morphism of algebras. -/
@[simps!]
def rTensorAlgHom : Module.End R M →ₐ[R] Module.End R (M ⊗[R] N) :=
  .ofLinearMap (rTensorHom (M := N)) (rTensor_id N M) (rTensor_mul N)

end Module.End

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF
variable {R : Type uR} {R' : Type*} {S : Type uS} {T : Type*}
variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}

/-!
### The `R`-algebra structure on `A ⊗[R] B`
-/

section AddCommMonoidWithOne

variable [CommSemiring R]
variable [AddCommMonoidWithOne A] [Module R A]
variable [AddCommMonoidWithOne B] [Module R B]

instance : One (A ⊗[R] B) where one := 1 ⊗ₜ 1

theorem one_def : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ (1 : B) :=
  rfl

instance instAddCommMonoidWithOne : AddCommMonoidWithOne (A ⊗[R] B) where
  natCast n := n ⊗ₜ 1
  natCast_zero := by simp
  natCast_succ n := by simp [add_tmul, one_def]
  add_comm := add_comm

theorem natCast_def (n : ℕ) : (n : A ⊗[R] B) = (n : A) ⊗ₜ (1 : B) := rfl

theorem natCast_def' (n : ℕ) : (n : A ⊗[R] B) = (1 : A) ⊗ₜ (n : B) := by
  rw [natCast_def, ← nsmul_one, smul_tmul, nsmul_one]

end AddCommMonoidWithOne

section NonUnitalNonAssocSemiring

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/-- (Implementation detail)
The multiplication map on `A ⊗[R] B`,
as an `R`-bilinear map.
-/
@[irreducible]
def mul : A ⊗[R] B →ₗ[R] A ⊗[R] B →ₗ[R] A ⊗[R] B :=
  TensorProduct.map₂ (LinearMap.mul R A) (LinearMap.mul R B)

unseal mul in
@[simp]
theorem mul_apply (a₁ a₂ : A) (b₁ b₂ : B) :
    mul (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl

-- providing this instance separately makes some downstream code substantially faster
instance instMul : Mul (A ⊗[R] B) where
  mul a b := mul a b

unseal mul in
@[simp]
theorem tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : B) :
    a₁ ⊗ₜ[R] b₁ * a₂ ⊗ₜ[R] b₂ = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl

unseal mul in
theorem _root_.SemiconjBy.tmul {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (ha : SemiconjBy a₁ a₂ a₃) (hb : SemiconjBy b₁ b₂ b₃) :
    SemiconjBy (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) (a₃ ⊗ₜ[R] b₃) :=
  congr_arg₂ (· ⊗ₜ[R] ·) ha.eq hb.eq

nonrec theorem _root_.Commute.tmul {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : Commute a₁ a₂) (hb : Commute b₁ b₂) :
    Commute (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) :=
  ha.tmul hb

instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (A ⊗[R] B) where
  left_distrib a b c := by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]

-- we want `isScalarTower_right` to take priority since it's better for unification elsewhere
instance (priority := 100) isScalarTower_right [Monoid S] [DistribMulAction S A]
    [IsScalarTower S A A] [SMulCommClass R S A] : IsScalarTower S (A ⊗[R] B) (A ⊗[R] B) where
  smul_assoc r x y := by
    change r • x * y = r • (x * y)
    induction y with
    | zero => simp [smul_zero]
    | tmul a b => induction x with
      | zero => simp [smul_zero]
      | tmul a' b' =>
        dsimp
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', tmul_mul_tmul, smul_mul_assoc]
      | add x y hx hy => simp [smul_add, add_mul _, *]
    | add x y hx hy => simp [smul_add, mul_add _, *]

-- we want `Algebra.to_smulCommClass` to take priority since it's better for unification elsewhere
instance (priority := 100) sMulCommClass_right [Monoid S] [DistribMulAction S A]
    [SMulCommClass S A A] [SMulCommClass R S A] : SMulCommClass S (A ⊗[R] B) (A ⊗[R] B) where
  smul_comm r x y := by
    change r • (x * y) = x * r • y
    induction y with
    | zero => simp [smul_zero]
    | tmul a b => induction x with
      | zero => simp [smul_zero]
      | tmul a' b' =>
        dsimp
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', tmul_mul_tmul, mul_smul_comm]
      | add x y hx hy => simp [smul_add, add_mul _, *]
    | add x y hx hy => simp [smul_add, mul_add _, *]

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [CommSemiring R]
variable [NonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

protected theorem one_mul (x : A ⊗[R] B) : mul (1 ⊗ₜ 1) x = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp +contextual

protected theorem mul_one (x : A ⊗[R] B) : mul x (1 ⊗ₜ 1) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp +contextual

instance instNonAssocSemiring : NonAssocSemiring (A ⊗[R] B) where
  one_mul := Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mul_one
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := instAddCommMonoidWithOne

end NonAssocSemiring

section NonUnitalSemiring
variable [CommSemiring R]
variable [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

unseal mul in
protected theorem mul_assoc (x y z : A ⊗[R] B) : mul (mul x y) z = mul x (mul y z) := by
  -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext xa xb ya yb za zb
  exact congr_arg₂ (· ⊗ₜ ·) (mul_assoc xa ya za) (mul_assoc xb yb zb)

instance instNonUnitalSemiring : NonUnitalSemiring (A ⊗[R] B) where
  mul_assoc := Algebra.TensorProduct.mul_assoc

end NonUnitalSemiring

section Semiring
variable [CommSemiring R]
variable [Semiring A] [Algebra R A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra R C]

instance instSemiring : Semiring (A ⊗[R] B) where
  left_distrib a b c := by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]
  mul_assoc := Algebra.TensorProduct.mul_assoc
  one_mul := Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mul_one
  natCast_zero := AddMonoidWithOne.natCast_zero
  natCast_succ := AddMonoidWithOne.natCast_succ

@[simp]
theorem tmul_pow (a : A) (b : B) (k : ℕ) : a ⊗ₜ[R] b ^ k = (a ^ k) ⊗ₜ[R] (b ^ k) := by
  induction k with
  | zero => simp [one_def]
  | succ k ih => simp [pow_succ, ih]

/-- The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps]
def includeLeftRingHom : A →+* A ⊗[R] B where
  toFun a := a ⊗ₜ 1
  map_zero' := by simp
  map_add' := by simp [add_tmul]
  map_one' := rfl
  map_mul' := by simp

variable [CommSemiring S] [Algebra S A]

instance leftAlgebra [SMulCommClass R S A] : Algebra S (A ⊗[R] B) :=
  { commutes' := fun r x => by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply, includeLeftRingHom_apply]
      rw [algebraMap_eq_smul_one, ← smul_tmul', ← one_def, mul_smul_comm, smul_mul_assoc, mul_one,
        one_mul]
    smul_def' := fun r x => by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply, includeLeftRingHom_apply]
      rw [algebraMap_eq_smul_one, ← smul_tmul', smul_mul_assoc, ← one_def, one_mul]
    algebraMap := TensorProduct.includeLeftRingHom.comp (algebraMap S A) }

example : (Semiring.toNatAlgebra : Algebra ℕ (ℕ ⊗[ℕ] B)) = leftAlgebra := rfl

-- This is for the `undergrad.yaml` list.
/-- The tensor product of two `R`-algebras is an `R`-algebra. -/
instance instAlgebra : Algebra R (A ⊗[R] B) :=
  inferInstance

@[simp]
theorem algebraMap_apply [SMulCommClass R S A] (r : S) :
    algebraMap S (A ⊗[R] B) r = (algebraMap S A) r ⊗ₜ 1 :=
  rfl

theorem algebraMap_apply' (r : R) :
    algebraMap R (A ⊗[R] B) r = 1 ⊗ₜ algebraMap R B r := by
  rw [algebraMap_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]

/-- The `R`-algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
def includeLeft [SMulCommClass R S A] : A →ₐ[S] A ⊗[R] B :=
  { includeLeftRingHom with commutes' := by simp }

@[simp]
theorem includeLeft_apply [SMulCommClass R S A] (a : A) :
    (includeLeft : A →ₐ[S] A ⊗[R] B) a = a ⊗ₜ 1 :=
  rfl

/-- The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`. -/
def includeRight : B →ₐ[R] A ⊗[R] B where
  toFun b := 1 ⊗ₜ b
  map_zero' := by simp
  map_add' := by simp [tmul_add]
  map_one' := rfl
  map_mul' := by simp
  commutes' r := by simp only [algebraMap_apply']

@[simp]
theorem includeRight_apply (b : B) : (includeRight : B →ₐ[R] A ⊗[R] B) b = 1 ⊗ₜ b :=
  rfl

theorem includeLeftRingHom_comp_algebraMap :
    (includeLeftRingHom.comp (algebraMap R A) : R →+* A ⊗[R] B) =
      includeRight.toRingHom.comp (algebraMap R B) := by
  ext
  simp

section ext
variable [Algebra R S] [Algebra S C] [IsScalarTower R S A] [IsScalarTower R S C]

/-- A version of `TensorProduct.ext` for `AlgHom`.

Using this as the `@[ext]` lemma instead of `Algebra.TensorProduct.ext'` allows `ext` to apply
lemmas specific to `A →ₐ[S] _` and `B →ₐ[R] _`; notably this allows recursion into nested tensor
products of algebras.

See note [partially-applied ext lemmas]. -/
@[ext high]
theorem ext ⦃f g : (A ⊗[R] B) →ₐ[S] C⦄
    (ha : f.comp includeLeft = g.comp includeLeft)
    (hb : (f.restrictScalars R).comp includeRight = (g.restrictScalars R).comp includeRight) :
    f = g := by
  apply AlgHom.toLinearMap_injective
  ext a b
  have := congr_arg₂ HMul.hMul (AlgHom.congr_fun ha a) (AlgHom.congr_fun hb b)
  dsimp at *
  rwa [← map_mul, ← map_mul, tmul_mul_tmul, one_mul, mul_one] at this

theorem ext' {g h : A ⊗[R] B →ₐ[S] C} (H : ∀ a b, g (a ⊗ₜ b) = h (a ⊗ₜ b)) : g = h :=
  ext (AlgHom.ext fun _ => H _ _) (AlgHom.ext fun _ => H _ _)

end ext

end Semiring

section AddCommGroupWithOne
variable [CommSemiring R]
variable [AddCommGroupWithOne A] [Module R A]
variable [AddCommMonoidWithOne B] [Module R B]

instance instAddCommGroupWithOne : AddCommGroupWithOne (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instAddCommMonoidWithOne
  intCast z := z ⊗ₜ (1 : B)
  intCast_ofNat n := by simp [natCast_def]
  intCast_negSucc n := by simp [natCast_def, add_tmul, neg_tmul, one_def]

theorem intCast_def (z : ℤ) : (z : A ⊗[R] B) = (z : A) ⊗ₜ (1 : B) := rfl

end AddCommGroupWithOne

section NonUnitalNonAssocRing
variable [CommSemiring R]
variable [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

instance instNonUnitalNonAssocRing : NonUnitalNonAssocRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonUnitalNonAssocSemiring

end NonUnitalNonAssocRing

section NonAssocRing
variable [CommSemiring R]
variable [NonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

instance instNonAssocRing : NonAssocRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

end NonAssocRing

section NonUnitalRing
variable [CommSemiring R]
variable [NonUnitalRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

instance instNonUnitalRing : NonUnitalRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonUnitalSemiring

end NonUnitalRing

section CommSemiring
variable [CommSemiring R]
variable [CommSemiring A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

instance instCommSemiring : CommSemiring (A ⊗[R] B) where
  toSemiring := inferInstance
  mul_comm x y := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro a₁ b₁
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro a₂ b₂
        simp [mul_comm]
      · intro a₂ b₂ ha hb
        simp [mul_add, add_mul, ha, hb]
    · intro x₁ x₂ h₁ h₂
      simp [mul_add, add_mul, h₁, h₂]

end CommSemiring

section Ring
variable [CommSemiring R]
variable [Ring A] [Algebra R A]
variable [Semiring B] [Algebra R B]

instance instRing : Ring (A ⊗[R] B) where
  toSemiring := instSemiring
  __ := TensorProduct.addCommGroup
  __ := instNonAssocRing

theorem intCast_def' {B} [Ring B] [Algebra R B] (z : ℤ) : (z : A ⊗[R] B) = (1 : A) ⊗ₜ (z : B) := by
  rw [intCast_def, ← zsmul_one, smul_tmul, zsmul_one]

-- verify there are no diamonds
example : (instRing : Ring (A ⊗[R] B)).toAddCommGroup = addCommGroup := by
  with_reducible_and_instances rfl
-- fails at `with_reducible_and_instances rfl` https://github.com/leanprover-community/mathlib4/issues/10906
example : (Ring.toIntAlgebra _ : Algebra ℤ (ℤ ⊗[ℤ] A)) = leftAlgebra := rfl

end Ring

section CommRing
variable [CommSemiring R]
variable [CommRing A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

instance instCommRing : CommRing (A ⊗[R] B) :=
  { toRing := inferInstance
    mul_comm := mul_comm }

end CommRing

section RightAlgebra

variable [CommSemiring R]
variable [Semiring A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

/-- `S ⊗[R] T` has a `T`-algebra structure. This is not a global instance or else the action of
`S` on `S ⊗[R] S` would be ambiguous. -/
abbrev rightAlgebra : Algebra B (A ⊗[R] B) where
  smul b ab := TensorProduct.comm _ _ _ (b • (TensorProduct.comm _ _ _ ab))
  algebraMap := Algebra.TensorProduct.includeRight.toRingHom
  commutes' b ab := by
    induction ab with
    | zero => simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, mul_zero, zero_mul]
    | tmul x y =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one, mul_comm]
    | add x y _ _ =>
        simp_all only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, mul_add, add_mul]
  smul_def' b ab := by
    induction ab with
    | zero =>
        change (TensorProduct.comm R B A) _ = _
        simp only [map_zero, smul_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          includeRight_apply, mul_zero]
    | tmul a b =>
        change (TensorProduct.comm R B A) _ = _
        simp only [smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply,
          algebraMap_apply, id.map_eq_id, RingHom.id_apply, comm_tmul,
          tmul_mul_tmul]
    | add x y hx hy =>
        change (TensorProduct.comm R B A) _ = _ at ⊢ hx hy
        simp only [map_add, smul_add, mul_add, ← hx, ← hy]

attribute [local instance] TensorProduct.rightAlgebra

@[simp] lemma rightAlgebra.algebraMap_apply (b : B) : algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ b := rfl

instance right_isScalarTower : IsScalarTower R B (A ⊗[R] B) :=
  IsScalarTower.of_algebraMap_eq fun r => (Algebra.TensorProduct.includeRight.commutes r).symm

lemma right_algebraMap_apply (b : B) : algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ b := rfl

instance : SMulCommClass A B (A ⊗[R] B) where
  smul_comm a b x := x.induction_on (by simp)
    (fun _ _ ↦ by simp [Algebra.smul_def, right_algebraMap_apply, smul_tmul'])
    fun _ _ h₁ h₂ ↦ by simpa using congr($h₁ + $h₂)

instance : SMulCommClass B A (A ⊗[R] B) := .symm ..

end RightAlgebra

/-- Verify that typeclass search finds the ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely rings, by treating both as `ℤ`-algebras.
-/
example [Ring A] [Ring B] : Ring (A ⊗[ℤ] B) := by infer_instance

/-- Verify that typeclass search finds the CommRing structure on `A ⊗[ℤ] B`
when `A` and `B` are merely `CommRing`s, by treating both as `ℤ`-algebras.
-/
example [CommRing A] [CommRing B] : CommRing (A ⊗[ℤ] B) := by infer_instance

/-!
We now build the structure maps for the symmetric monoidal category of `R`-algebras.
-/

section Monoidal

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra S C]
variable [Semiring D] [Algebra R D]

/-- To check a linear map preserves multiplication, it suffices to check it on pure tensors. See
`algHomOfLinearMapTensorProduct` for a bundled version. -/
lemma _root_.LinearMap.map_mul_of_map_mul_tmul {f : A ⊗[R] B →ₗ[S] C}
    (hf : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (x y : A ⊗[R] B) : f (x * y) = f x * f y :=
  f.map_mul_iff.2 (by
    -- these instances are needed by the statement of `ext`, but not by the current definition.
    letI : Algebra R C := RestrictScalars.algebra R S C
    letI : IsScalarTower R S C := RestrictScalars.isScalarTower R S C
    ext
    dsimp
    exact hf _ _ _ _) x y

/-- Build an algebra morphism from a linear map out of a tensor product, and evidence that on pure
tensors, it preserves multiplication and the identity.

Note that we state `h_one` using `1 ⊗ₜ[R] 1` instead of `1` so that lemmas about `f` applied to pure
tensors can be directly applied by the caller (without needing `TensorProduct.one_def`).
-/
def algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B →ₐ[S] C :=
  AlgHom.ofLinearMap f h_one (f.map_mul_of_map_mul_tmul h_mul)

@[simp]
theorem algHomOfLinearMapTensorProduct_apply (f h_mul h_one x) :
    (algHomOfLinearMapTensorProduct f h_mul h_one : A ⊗[R] B →ₐ[S] C) x = f x :=
  rfl

/-- Build an algebra equivalence from a linear equivalence out of a tensor product, and evidence
that on pure tensors, it preserves multiplication and the identity.

Note that we state `h_one` using `1 ⊗ₜ[R] 1` instead of `1` so that lemmas about `f` applied to pure
tensors can be directly applied by the caller (without needing `TensorProduct.one_def`).
-/
def algEquivOfLinearEquivTensorProduct (f : A ⊗[R] B ≃ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B ≃ₐ[S] C :=
  { algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C) h_mul h_one, f with }

@[simp]
theorem algEquivOfLinearEquivTensorProduct_apply (f h_mul h_one x) :
    (algEquivOfLinearEquivTensorProduct f h_mul h_one : A ⊗[R] B ≃ₐ[S] C) x = f x :=
  rfl

variable [Algebra R C]
/-- Build an algebra equivalence from a linear equivalence out of a triple tensor product,
and evidence of multiplicativity on pure tensors.
-/
def algEquivOfLinearEquivTripleTensorProduct (f : A ⊗[R] B ⊗[R] C ≃ₗ[R] D)
    (h_mul :
      ∀ (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
        f ((a₁ * a₂) ⊗ₜ (b₁ * b₂) ⊗ₜ (c₁ * c₂)) = f (a₁ ⊗ₜ b₁ ⊗ₜ c₁) * f (a₂ ⊗ₜ b₂ ⊗ₜ c₂))
    (h_one : f (((1 : A) ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : C)) = 1) :
    A ⊗[R] B ⊗[R] C ≃ₐ[R] D :=
  AlgEquiv.ofLinearEquiv f h_one <| f.map_mul_iff.2 <| by
    ext
    dsimp
    exact h_mul _ _ _ _ _ _

@[simp]
theorem algEquivOfLinearEquivTripleTensorProduct_apply (f h_mul h_one x) :
    (algEquivOfLinearEquivTripleTensorProduct f h_mul h_one : A ⊗[R] B ⊗[R] C ≃ₐ[R] D) x = f x :=
  rfl

section lift
variable [IsScalarTower R S C]

/-- The forward direction of the universal property of tensor products of algebras; any algebra
morphism from the tensor product can be factored as the product of two algebra morphisms that
commute.

See `Algebra.TensorProduct.liftEquiv` for the fact that every morphism factors this way. -/
def lift (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) : (A ⊗[R] B) →ₐ[S] C :=
  algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.lift <|
      letI restr : (C →ₗ[S] C) →ₗ[S] _ :=
        { toFun := (·.restrictScalars R)
          map_add' := fun _ _ => LinearMap.ext fun _ => rfl
          map_smul' := fun _ _ => LinearMap.ext fun _ => rfl }
      LinearMap.flip <| (restr ∘ₗ LinearMap.mul S C ∘ₗ f.toLinearMap).flip ∘ₗ g)
    (fun a₁ a₂ b₁ b₂ => show f (a₁ * a₂) * g (b₁ * b₂) = f a₁ * g b₁ * (f a₂ * g b₂) by
      rw [map_mul, map_mul, (hfg a₂ b₁).mul_mul_mul_comm])
    (show f 1 * g 1 = 1 by rw [map_one, map_one, one_mul])

@[simp]
theorem lift_tmul (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y))
    (a : A) (b : B) :
    lift f g hfg (a ⊗ₜ b) = f a * g b :=
  rfl

@[simp]
theorem lift_includeLeft_includeRight :
    lift includeLeft includeRight (fun _ _ => (Commute.one_right _).tmul (Commute.one_left _)) =
      .id S (A ⊗[R] B) := by
  ext <;> simp

@[simp]
theorem lift_comp_includeLeft (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    (lift f g hfg).comp includeLeft = f :=
  AlgHom.ext <| by simp

@[simp]
theorem lift_comp_includeRight (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    ((lift f g hfg).restrictScalars R).comp includeRight = g :=
  AlgHom.ext <| by simp

/-- The universal property of the tensor product of algebras.

Pairs of algebra morphisms that commute are equivalent to algebra morphisms from the tensor product.

This is `Algebra.TensorProduct.lift` as an equivalence.

See also `GradedTensorProduct.liftEquiv` for an alternative commutativity requirement for graded
algebra. -/
@[simps]
def liftEquiv : {fg : (A →ₐ[S] C) × (B →ₐ[R] C) // ∀ x y, Commute (fg.1 x) (fg.2 y)}
    ≃ ((A ⊗[R] B) →ₐ[S] C) where
  toFun fg := lift fg.val.1 fg.val.2 fg.prop
  invFun f' := ⟨(f'.comp includeLeft, (f'.restrictScalars R).comp includeRight), fun _ _ =>
    ((Commute.one_right _).tmul (Commute.one_left _)).map f'⟩
  left_inv fg := by ext <;> simp
  right_inv f' := by ext <;> simp

end lift

end

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
variable [Semiring D] [Algebra R D]
variable [Semiring E] [Algebra R E] [Algebra S E] [IsScalarTower R S E]
variable [Semiring F] [Algebra R F]

section

variable (R A)

/-- The base ring is a left identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected nonrec def lid : R ⊗[R] A ≃ₐ[R] A :=
  algEquivOfLinearEquivTensorProduct (TensorProduct.lid R A) (by
    simp only [mul_smul, lid_tmul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    simp_rw [← mul_smul, mul_comm]
    simp)
    (by simp [Algebra.smul_def])

@[simp] theorem lid_toLinearEquiv :
    (TensorProduct.lid R A).toLinearEquiv = _root_.TensorProduct.lid R A := rfl

variable {R} {A} in
@[simp]
theorem lid_tmul (r : R) (a : A) : TensorProduct.lid R A (r ⊗ₜ a) = r • a := rfl

variable {A} in
@[simp]
theorem lid_symm_apply (a : A) : (TensorProduct.lid R A).symm a = 1 ⊗ₜ a := rfl

variable (S)

/-- The base ring is a right identity for the tensor product of algebra, up to algebra isomorphism.

Note that if `A` is commutative this can be instantiated with `S = A`.
-/
protected nonrec def rid : A ⊗[R] R ≃ₐ[S] A :=
  algEquivOfLinearEquivTensorProduct (AlgebraTensorModule.rid R S A)
    (fun a₁ a₂ r₁ r₂ => smul_mul_smul_comm r₁ a₁ r₂ a₂ |>.symm)
    (one_smul R _)

@[simp] theorem rid_toLinearEquiv :
    (TensorProduct.rid R S A).toLinearEquiv = AlgebraTensorModule.rid R S A := rfl

variable {R A} in
@[simp]
theorem rid_tmul (r : R) (a : A) : TensorProduct.rid R S A (a ⊗ₜ r) = r • a := rfl

variable {A} in
@[simp]
theorem rid_symm_apply (a : A) : (TensorProduct.rid R S A).symm a = a ⊗ₜ 1 := rfl

section CompatibleSMul

variable (R S A B : Type*) [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
variable [SMulCommClass R S A] [CompatibleSMul R S A B]

/-- If A and B are both R- and S-algebras and their actions on them commute,
and if the S-action on `A ⊗[R] B` can switch between the two factors, then there is a
canonical S-algebra homomorphism from `A ⊗[S] B` to `A ⊗[R] B`. -/
def mapOfCompatibleSMul : A ⊗[S] B →ₐ[S] A ⊗[R] B :=
  .ofLinearMap (_root_.TensorProduct.mapOfCompatibleSMul R S A B) rfl fun x ↦
    x.induction_on (by simp) (fun _ _ y ↦ y.induction_on (by simp) (by simp)
      fun _ _ h h' ↦ by simp only [mul_add, map_add, h, h'])
      fun _ _ h h' _ ↦ by simp only [add_mul, map_add, h, h']

@[simp] theorem mapOfCompatibleSMul_tmul (m n) : mapOfCompatibleSMul R S A B (m ⊗ₜ n) = m ⊗ₜ n :=
  rfl

theorem mapOfCompatibleSMul_surjective : Function.Surjective (mapOfCompatibleSMul R S A B) :=
  _root_.TensorProduct.mapOfCompatibleSMul_surjective R S A B

attribute [local instance] SMulCommClass.symm

/-- `mapOfCompatibleSMul R S A B` is also A-linear. -/
def mapOfCompatibleSMul' : A ⊗[S] B →ₐ[R] A ⊗[R] B :=
  .ofLinearMap (_root_.TensorProduct.mapOfCompatibleSMul' R S A B) rfl
    (map_mul <| mapOfCompatibleSMul R S A B)

/-- If the R- and S-actions on A and B satisfy `CompatibleSMul` both ways,
then `A ⊗[S] B` is canonically isomorphic to `A ⊗[R] B`. -/
def equivOfCompatibleSMul [CompatibleSMul S R A B] : A ⊗[S] B ≃ₐ[S] A ⊗[R] B where
  __ := mapOfCompatibleSMul R S A B
  invFun := mapOfCompatibleSMul S R A B
  __ := _root_.TensorProduct.equivOfCompatibleSMul R S A B

variable [Algebra R S] [CompatibleSMul R S S A] [CompatibleSMul S R S A]
omit [SMulCommClass R S A]

/-- If the R- and S- action on S and A satisfy `CompatibleSMul` both ways,
then `S ⊗[R] A` is canonically isomorphic to `A`. -/
def lidOfCompatibleSMul : S ⊗[R] A ≃ₐ[S] A :=
  (equivOfCompatibleSMul R S S A).symm.trans (TensorProduct.lid _ _)

theorem lidOfCompatibleSMul_tmul (s a) : lidOfCompatibleSMul R S A (s ⊗ₜ[R] a) = s • a := rfl

instance {R M N : Type*} [CommSemiring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module ℚ M] [Module ℚ N] : CompatibleSMul R ℚ M N where
  smul_tmul q m n := by
    suffices q.den • ((q • m) ⊗ₜ[R] n) = q.den • (m ⊗ₜ[R] (q • n)) from
      smul_right_injective (M ⊗[R] N) (c := q.den) q.den_nz <| by norm_cast
    rw [smul_tmul', ← tmul_smul, ← smul_assoc, ← smul_assoc, nsmul_eq_mul, Rat.den_mul_eq_num]
    norm_cast
    rw [smul_tmul]

end CompatibleSMul

section

variable (B)

unseal mul in
/-- The tensor product of R-algebras is commutative, up to algebra isomorphism.
-/
protected def comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A :=
  algEquivOfLinearEquivTensorProduct (_root_.TensorProduct.comm R A B) (fun _ _ _ _ => rfl) rfl

@[simp] theorem comm_toLinearEquiv :
    (Algebra.TensorProduct.comm R A B).toLinearEquiv = _root_.TensorProduct.comm R A B := rfl

variable {A B} in
@[simp]
theorem comm_tmul (a : A) (b : B) :
    TensorProduct.comm R A B (a ⊗ₜ b) = b ⊗ₜ a :=
  rfl

variable {A B} in
@[simp]
theorem comm_symm_tmul (a : A) (b : B) :
    (TensorProduct.comm R A B).symm (b ⊗ₜ a) = a ⊗ₜ b :=
  rfl

theorem comm_symm :
    (TensorProduct.comm R A B).symm = TensorProduct.comm R B A := by
  ext; rfl

@[simp]
lemma comm_comp_includeLeft :
    (TensorProduct.comm R A B : A ⊗[R] B →ₐ[R] B ⊗[R] A).comp includeLeft = includeRight := rfl

@[simp]
lemma comm_comp_includeRight :
    (TensorProduct.comm R A B : A ⊗[R] B →ₐ[R] B ⊗[R] A).comp includeRight = includeLeft := rfl

theorem adjoin_tmul_eq_top : adjoin R { t : A ⊗[R] B | ∃ a b, a ⊗ₜ[R] b = t } = ⊤ :=
  top_le_iff.mp <| (top_le_iff.mpr <| span_tmul_eq_top R A B).trans (span_le_adjoin R _)

end

section

variable {R A}

unseal mul in
theorem assoc_aux_1 (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C) :
    (TensorProduct.assoc R A B C) ((a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) ⊗ₜ[R] (c₁ * c₂)) =
      (TensorProduct.assoc R A B C) (a₁ ⊗ₜ[R] b₁ ⊗ₜ[R] c₁) *
        (TensorProduct.assoc R A B C) (a₂ ⊗ₜ[R] b₂ ⊗ₜ[R] c₂) :=
  rfl

theorem assoc_aux_2 : (TensorProduct.assoc R A B C) (1 ⊗ₜ[R] 1 ⊗ₜ[R] 1) = 1 :=
  rfl

variable (R A C D)

/-- The associator for tensor product of R-algebras, as an algebra isomorphism. -/
protected def assoc : A ⊗[S] C ⊗[R] D ≃ₐ[S] A ⊗[S] (C ⊗[R] D) :=
  AlgEquiv.ofLinearEquiv
    (AlgebraTensorModule.assoc R S S A C D)
    (by simp [Algebra.TensorProduct.one_def])
    ((LinearMap.map_mul_iff _).mpr <| by ext; simp)

@[simp] theorem assoc_toLinearEquiv :
    (TensorProduct.assoc R S A C D).toLinearEquiv = AlgebraTensorModule.assoc R S S A C D := rfl

variable {A C D}

@[simp]
theorem assoc_tmul (a : A) (b : C) (c : D) :
    TensorProduct.assoc R S A C D ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) := rfl

@[simp]
theorem assoc_symm_tmul (a : A) (b : C) (c : D) :
    (TensorProduct.assoc R S A C D).symm (a ⊗ₜ (b ⊗ₜ c)) = (a ⊗ₜ b) ⊗ₜ c := rfl

end

section

variable (T A B : Type*) [CommSemiring T] [CommSemiring A] [CommSemiring B]
  [Algebra R T] [Algebra R A] [Algebra R B] [Algebra T A] [IsScalarTower R T A] [Algebra S A]
  [IsScalarTower R S A] [Algebra S T] [IsScalarTower S T A]

/-- The natural isomorphism `A ⊗[S] (S ⊗[R] B) ≃ₐ[T] A ⊗[R] B`. -/
def cancelBaseChange : A ⊗[S] (S ⊗[R] B) ≃ₐ[T] A ⊗[R] B :=
  AlgEquiv.symm <| AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T A B).symm
    (by simp [Algebra.TensorProduct.one_def]) <|
      LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp)

@[simp]
lemma cancelBaseChange_tmul (a : A) (s : S) (b : B) :
    Algebra.TensorProduct.cancelBaseChange R S T A B (a ⊗ₜ (s ⊗ₜ b)) = (s • a) ⊗ₜ b :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S T a b s

@[simp]
lemma cancelBaseChange_symm_tmul (a : A) (b : B) :
    (Algebra.TensorProduct.cancelBaseChange R S T A B).symm (a ⊗ₜ b) = a ⊗ₜ (1 ⊗ₜ b) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S T a b

end

variable {R S A}

/-- The tensor product of a pair of algebra morphisms. -/
def map (f : A →ₐ[S] C) (g : B →ₐ[R] D) : A ⊗[R] B →ₐ[S] C ⊗[R] D :=
  algHomOfLinearMapTensorProduct (AlgebraTensorModule.map f.toLinearMap g.toLinearMap) (by simp)
    (by simp [one_def])

@[simp]
theorem map_tmul (f : A →ₐ[S] C) (g : B →ₐ[R] D) (a : A) (b : B) : map f g (a ⊗ₜ b) = f a ⊗ₜ g b :=
  rfl

@[simp]
theorem map_id : map (.id S A) (.id R B) = .id S _ :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

theorem map_comp
    (f₂ : C →ₐ[S] E) (f₁ : A →ₐ[S] C) (g₂ : D →ₐ[R] F) (g₁ : B →ₐ[R] D) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

lemma map_id_comp (g₂ : D →ₐ[R] F) (g₁ : B →ₐ[R] D) :
    map (AlgHom.id S A) (g₂.comp g₁) = (map (AlgHom.id S A) g₂).comp (map (AlgHom.id S A) g₁) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

lemma map_comp_id
    (f₂ : C →ₐ[S] E) (f₁ : A →ₐ[S] C) :
    map (f₂.comp f₁) (AlgHom.id R E) = (map f₂ (AlgHom.id R E)).comp (map f₁ (AlgHom.id R E)) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

@[simp]
theorem map_comp_includeLeft (f : A →ₐ[S] C) (g : B →ₐ[R] D) :
    (map f g).comp includeLeft = includeLeft.comp f :=
  AlgHom.ext <| by simp

@[simp]
theorem map_restrictScalars_comp_includeRight (f : A →ₐ[S] C) (g : B →ₐ[R] D) :
    ((map f g).restrictScalars R).comp includeRight = includeRight.comp g :=
  AlgHom.ext <| by simp

@[simp]
theorem map_comp_includeRight (f : A →ₐ[R] C) (g : B →ₐ[R] D) :
    (map f g).comp includeRight = includeRight.comp g :=
  map_restrictScalars_comp_includeRight f g

theorem map_range (f : A →ₐ[R] C) (g : B →ₐ[R] D) :
    (map f g).range = (includeLeft.comp f).range ⊔ (includeRight.comp g).range := by
  apply le_antisymm
  · rw [← map_top, ← adjoin_tmul_eq_top, ← adjoin_image, adjoin_le_iff]
    rintro _ ⟨_, ⟨a, b, rfl⟩, rfl⟩
    rw [map_tmul, ← mul_one (f a), ← one_mul (g b), ← tmul_mul_tmul]
    exact mul_mem_sup (AlgHom.mem_range_self _ a) (AlgHom.mem_range_self _ b)
  · rw [← map_comp_includeLeft f g, ← map_comp_includeRight f g]
    exact sup_le (AlgHom.range_comp_le_range _ _) (AlgHom.range_comp_le_range _ _)

lemma comm_comp_map (f : A →ₐ[R] C) (g : B →ₐ[R] D) :
    (TensorProduct.comm R C D : C ⊗[R] D →ₐ[R] D ⊗[R] C).comp (Algebra.TensorProduct.map f g) =
    (Algebra.TensorProduct.map g f).comp (TensorProduct.comm R A B).toAlgHom := by
  ext <;> rfl

lemma comm_comp_map_apply (f : A →ₐ[R] C) (g : B →ₐ[R] D) (x) :
    TensorProduct.comm R C D (Algebra.TensorProduct.map f g x) =
    (Algebra.TensorProduct.map g f) (TensorProduct.comm R A B x) :=
  congr($(comm_comp_map f g) x)

/-- Construct an isomorphism between tensor products of an S-algebra with an R-algebra
from S- and R- isomorphisms between the tensor factors.
-/
def congr (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) : A ⊗[R] B ≃ₐ[S] C ⊗[R] D :=
  AlgEquiv.ofAlgHom (map f g) (map f.symm g.symm)
    (ext' fun b d => by simp) (ext' fun a c => by simp)

@[simp] theorem congr_toLinearEquiv (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) :
    (Algebra.TensorProduct.congr f g).toLinearEquiv =
      TensorProduct.AlgebraTensorModule.congr f.toLinearEquiv g.toLinearEquiv := rfl

@[simp]
theorem congr_apply (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x) :
    congr f g x = (map (f : A →ₐ[S] C) (g : B →ₐ[R] D)) x :=
  rfl

@[simp]
theorem congr_symm_apply (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x) :
    (congr f g).symm x = (map (f.symm : C →ₐ[S] A) (g.symm : D →ₐ[R] B)) x :=
  rfl

@[simp]
theorem congr_refl : congr (.refl : A ≃ₐ[S] A) (.refl : B ≃ₐ[R] B) = .refl :=
  AlgEquiv.coe_algHom_injective <| map_id

theorem congr_trans
    (f₁ : A ≃ₐ[S] C) (f₂ : C ≃ₐ[S] E) (g₁ : B ≃ₐ[R] D) (g₂ : D ≃ₐ[R] F) :
    congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
  AlgEquiv.coe_algHom_injective <| map_comp f₂.toAlgHom f₁.toAlgHom g₂.toAlgHom g₁.toAlgHom

theorem congr_symm (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) : congr f.symm g.symm = (congr f g).symm := rfl

variable (R A B C) in
/-- Tensor product of algebras analogue of `mul_left_comm`.

This is the algebra version of `TensorProduct.leftComm`. -/
def leftComm : A ⊗[R] (B ⊗[R] C) ≃ₐ[R] B ⊗[R] (A ⊗[R] C) :=
  (Algebra.TensorProduct.assoc R R A B C).symm.trans <|
    (congr (Algebra.TensorProduct.comm R A B) .refl).trans <| TensorProduct.assoc R R B A C

@[simp]
theorem leftComm_tmul (m : A) (n : B) (p : C) :
    leftComm R A B C (m ⊗ₜ (n ⊗ₜ p)) = n ⊗ₜ (m ⊗ₜ p) :=
  rfl

@[simp]
theorem leftComm_symm_tmul (m : A) (n : B) (p : C) :
    (leftComm R A B C).symm (n ⊗ₜ (m ⊗ₜ p)) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl

@[simp]
theorem leftComm_toLinearEquiv : ↑(leftComm R A B C) = _root_.TensorProduct.leftComm R A B C :=
  LinearEquiv.toLinearMap_injective (by ext; rfl)

variable [CommSemiring T] [Algebra R T] [Algebra T A] [IsScalarTower R T A] [SMulCommClass S T A]
  [Algebra S T] [IsScalarTower S T A] [CommSemiring R'] [Algebra R R'] [Algebra R' T] [Algebra R' A]
  [Algebra R' B] [IsScalarTower R R' A] [SMulCommClass S R' A] [SMulCommClass R' S A]
  [IsScalarTower R' T A] [IsScalarTower R R' B]

variable (R R' S T A B C D) in
/-- Tensor product of algebras analogue of `mul_mul_mul_comm`.

This is the algebra version of `TensorProduct.AlgebraTensorModule.tensorTensorTensorComm`. -/
def tensorTensorTensorComm : A ⊗[R'] B ⊗[S] (C ⊗[R] D) ≃ₐ[T] A ⊗[S] C ⊗[R'] (B ⊗[R] D) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' S T A B C D)
    rfl (LinearMap.map_mul_iff _ |>.mpr <| by ext; simp)

@[simp]
theorem tensorTensorTensorComm_tmul (m : A) (n : B) (p : C) (q : D) :
    tensorTensorTensorComm R R' S T A B C D (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ p ⊗ₜ (n ⊗ₜ q) :=
  rfl

@[simp]
theorem tensorTensorTensorComm_symm_tmul (m : A) (n : C) (p : B) (q : D) :
    (tensorTensorTensorComm R R' S T A B C D).symm (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ p ⊗ₜ (n ⊗ₜ q) :=
  rfl

theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R R' S T A B C D).symm = tensorTensorTensorComm R S R' T A C B D := by
  ext; rfl

theorem tensorTensorTensorComm_toLinearEquiv :
    (tensorTensorTensorComm R R' S T A B C D).toLinearEquiv =
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' S T A B C D := rfl

@[simp]
theorem toLinearEquiv_tensorTensorTensorComm :
    (tensorTensorTensorComm R R R R A B C D).toLinearEquiv =
      _root_.TensorProduct.tensorTensorTensorComm R A B C D := by
  apply LinearEquiv.toLinearMap_injective
  ext; simp

lemma map_bijective {f : A →ₐ[R] B} {g : C →ₐ[R] D}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (map f g) :=
  _root_.TensorProduct.map_bijective hf hg

lemma includeLeft_bijective (h : Function.Bijective (algebraMap R B)) :
    Function.Bijective (includeLeft : A →ₐ[S] A ⊗[R] B) := by
  have : (includeLeft : A →ₐ[S] A ⊗[R] B).comp (TensorProduct.rid R S A).toAlgHom =
      map (.id S A) (Algebra.ofId R B) := by ext; simp
  rw [← Function.Bijective.of_comp_iff _ (TensorProduct.rid R S A).bijective]
  convert_to Function.Bijective (map (.id R A) (Algebra.ofId R B))
  · exact DFunLike.coe_fn_eq.mpr this
  · exact Algebra.TensorProduct.map_bijective Function.bijective_id h

lemma includeRight_bijective (h : Function.Bijective (algebraMap R A)) :
    Function.Bijective (includeRight : B →ₐ[R] A ⊗[R] B) := by
  rw [← Function.Bijective.of_comp_iff' (TensorProduct.comm R A B).bijective]
  exact Algebra.TensorProduct.includeLeft_bijective (S := R) h

end

end Monoidal

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [CommSemiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]

/-- If `A`, `B`, `C` are `R`-algebras, `A` and `C` are also `S`-algebras (forming a tower as
`·/S/R`), then the product map of `f : A →ₐ[S] C` and `g : B →ₐ[R] C` is an `S`-algebra
homomorphism.

This is just a special case of `Algebra.TensorProduct.lift` for when `C` is commutative. -/
abbrev productLeftAlgHom (f : A →ₐ[S] C) (g : B →ₐ[R] C) : A ⊗[R] B →ₐ[S] C :=
  lift f g (fun _ _ => Commute.all _ _)

lemma tmul_one_eq_one_tmul (r : R) : algebraMap R A r ⊗ₜ[R] 1 = 1 ⊗ₜ algebraMap R B r := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]

end

variable (R A B) in
lemma closure_range_union_range_eq_top [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] :
    Subring.closure (Set.range (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) ∪
      Set.range Algebra.TensorProduct.includeRight) = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  induction x with
  | zero => exact zero_mem _
  | tmul x y =>
    convert_to (Algebra.TensorProduct.includeLeftRingHom (R := R) x) *
      (Algebra.TensorProduct.includeRight y) ∈ _
    · simp
    · exact mul_mem (Subring.subset_closure (.inl ⟨x, rfl⟩))
        (Subring.subset_closure (.inr ⟨_, rfl⟩))
  | add x y _ _ => exact add_mem ‹_› ‹_›
section

variable [CommSemiring R] [Semiring A] [Semiring B] [CommSemiring S]
variable [Algebra R A] [Algebra R B] [Algebra R S]
variable (f : A →ₐ[R] S) (g : B →ₐ[R] S)
variable (R)

/-- `LinearMap.mul'` as an `AlgHom` over the algebra. -/
def lmul'' : S ⊗[R] S →ₐ[S] S :=
  algHomOfLinearMapTensorProduct
    { __ := LinearMap.mul' R S
      map_smul' := fun s x ↦ x.induction_on (by simp)
        (fun _ _ ↦ by simp [TensorProduct.smul_tmul', mul_assoc])
        fun x y hx hy ↦ by simp_all [mul_add] }
    (fun a₁ a₂ b₁ b₂ => by simp [mul_mul_mul_comm]) <| by simp

theorem lmul''_eq_lid_comp_mapOfCompatibleSMul :
    lmul'' R = (TensorProduct.lid S S).toAlgHom.comp (mapOfCompatibleSMul' _ _ _ _) := by
  ext; rfl

/-- `LinearMap.mul'` as an `AlgHom` over the base ring. -/
def lmul' : S ⊗[R] S →ₐ[R] S := (lmul'' R).restrictScalars R

variable {R}

theorem lmul'_toLinearMap : (lmul' R : _ →ₐ[R] S).toLinearMap = LinearMap.mul' R S :=
  rfl

@[simp]
theorem lmul'_apply_tmul (a b : S) : lmul' (S := S) R (a ⊗ₜ[R] b) = a * b :=
  rfl

@[simp]
theorem lmul'_comp_includeLeft : (lmul' R : _ →ₐ[R] S).comp includeLeft = AlgHom.id R S :=
  AlgHom.ext <| mul_one

@[simp]
theorem lmul'_comp_includeRight : (lmul' R : _ →ₐ[R] S).comp includeRight = AlgHom.id R S :=
  AlgHom.ext <| one_mul

lemma lmul'_comp_map (f : A →ₐ[R] S) (g : B →ₐ[R] S) :
    (lmul' R).comp (map f g) = lift f g (fun _ _ ↦ .all _ _) := by ext <;> rfl

variable (R S) in
/-- If multiplication by elements of S can switch between the two factors of `S ⊗[R] S`,
then `lmul''` is an isomorphism. -/
def lmulEquiv [CompatibleSMul R S S S] : S ⊗[R] S ≃ₐ[S] S :=
  .ofAlgHom (lmul'' R) includeLeft lmul'_comp_includeLeft <| AlgHom.ext fun x ↦ x.induction_on
    (by simp) (fun x y ↦ show (x * y) ⊗ₜ[R] 1 = x ⊗ₜ[R] y by
      rw [mul_comm, ← smul_eq_mul, smul_tmul, smul_eq_mul, mul_one])
    fun _ _ hx hy ↦ by simp_all [add_tmul]

theorem lmulEquiv_eq_lidOfCompatibleSMul [CompatibleSMul R S S S] :
    lmulEquiv R S = lidOfCompatibleSMul R S S :=
  AlgEquiv.coe_algHom_injective <| by ext; rfl

/-- If `S` is commutative, for a pair of morphisms `f : A →ₐ[R] S`, `g : B →ₐ[R] S`,
We obtain a map `A ⊗[R] B →ₐ[R] S` that commutes with `f`, `g` via `a ⊗ b ↦ f(a) * g(b)`.

This is a special case of `Algebra.TensorProduct.productLeftAlgHom` for when the two base rings are
the same.
-/
def productMap : A ⊗[R] B →ₐ[R] S := productLeftAlgHom f g

theorem productMap_eq_comp_map : productMap f g = (lmul' R).comp (TensorProduct.map f g) := by
  ext <;> rfl

@[simp]
theorem productMap_apply_tmul (a : A) (b : B) : productMap f g (a ⊗ₜ b) = f a * g b := rfl

theorem productMap_left_apply (a : A) : productMap f g (a ⊗ₜ 1) = f a := by
  simp

@[simp]
theorem productMap_left : (productMap f g).comp includeLeft = f :=
  lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)

theorem productMap_right_apply (b : B) :
    productMap f g (1 ⊗ₜ b) = g b := by simp

@[simp]
theorem productMap_right : (productMap f g).comp includeRight = g :=
  lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)

theorem productMap_range : (productMap f g).range = f.range ⊔ g.range := by
  rw [productMap_eq_comp_map, AlgHom.range_comp, map_range, map_sup, ← AlgHom.range_comp,
    ← AlgHom.range_comp,
    ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, lmul'_comp_includeLeft, lmul'_comp_includeRight,
    AlgHom.id_comp, AlgHom.id_comp]

end

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- If `M` is a `B`-module that is also an `A`-module, the canonical map
`M →ₗ[A] B ⊗[A] M` is injective. -/
lemma mk_one_injective_of_isScalarTower (M : Type*) [AddCommMonoid M]
    [Module R M] [Module S M] [IsScalarTower R S M] :
    Function.Injective (TensorProduct.mk R S M 1) := by
  apply Function.RightInverse.injective (g := LinearMap.liftBaseChange S LinearMap.id)
  intro m
  simp

end TensorProduct

end Algebra

lemma Algebra.baseChange_lmul {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    {A : Type*} [CommSemiring A] [Algebra R A] (f : B) :
    (Algebra.lmul R B f).baseChange A = Algebra.lmul A (A ⊗[R] B) (1 ⊗ₜ f) := by
  ext i
  simp

namespace LinearMap

variable (R A M N : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Module
open scoped TensorProduct

/-- The natural linear map $A ⊗ \text{Hom}_R(M, N) → \text{Hom}_A (M_A, N_A)$,
where $M_A$ and $N_A$ are the respective modules over $A$ obtained by extension of scalars.

See `LinearMap.tensorProductEnd` for this map specialized to endomorphisms,
and bundled as `A`-algebra homomorphism. -/
@[simps!]
def tensorProduct : A ⊗[R] (M →ₗ[R] N) →ₗ[A] (A ⊗[R] M) →ₗ[A] (A ⊗[R] N) :=
  TensorProduct.AlgebraTensorModule.lift <|
  { toFun := fun a ↦ a • baseChangeHom R A M N
    map_add' := by simp only [add_smul, forall_true_iff]
    map_smul' := by simp only [smul_assoc, RingHom.id_apply, forall_true_iff] }

/-- The natural `A`-algebra homomorphism $A ⊗ (\text{End}_R M) → \text{End}_A (A ⊗ M)$,
where `M` is an `R`-module, and `A` an `R`-algebra. -/
@[simps!]
def tensorProductEnd : A ⊗[R] (End R M) →ₐ[A] End A (A ⊗[R] M) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (LinearMap.tensorProduct R A M M)
    (fun a b f g ↦ by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, mul_comm a b, Module.End.mul_eq_comp,
        TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul, coe_restrictScalars,
        coe_mk, AddHom.coe_mk, mul_smul, smul_apply, baseChangeHom_apply, baseChange_comp,
        comp_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc])
    (by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, TensorProduct.AlgebraTensorModule.lift_apply,
        TensorProduct.lift.tmul, coe_restrictScalars, coe_mk, AddHom.coe_mk, one_smul,
        baseChangeHom_apply, baseChange_eq_ltensor, Module.End.one_eq_id,
        lTensor_id, LinearMap.id_apply])

end LinearMap

namespace Module

variable {R S A M N : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Algebra R S] [Algebra S A] [Algebra R A]
variable [Module R M] [Module S M] [Module A M] [Module R N]
variable [IsScalarTower R A M] [IsScalarTower S A M] [IsScalarTower R S M]

/-- The algebra homomorphism from `End M ⊗ End N` to `End (M ⊗ N)` sending `f ⊗ₜ g` to
the `TensorProduct.map f g`, the tensor product of the two maps.

This is an `AlgHom` version of `TensorProduct.AlgebraTensorModule.homTensorHomMap`. Like that
definition, this is generalized across many different rings; namely a tower of algebras `A/S/R`. -/
def endTensorEndAlgHom : End A M ⊗[R] End R N →ₐ[S] End A (M ⊗[R] N) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.homTensorHomMap R A S M N M N)
    (fun _f₁ _f₂ _g₁ _g₂ => AlgebraTensorModule.ext fun _m _n => rfl)
    (AlgebraTensorModule.ext fun _m _n => rfl)

theorem endTensorEndAlgHom_apply (f : End A M) (g : End R N) :
    endTensorEndAlgHom (R := R) (S := S) (A := A) (M := M) (N := N) (f ⊗ₜ[R] g)
      = AlgebraTensorModule.map f g :=
  rfl

end Module

namespace TensorProduct.Algebra

variable {R A B M : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [Semiring A] [Semiring B] [Module A M] [Module B M]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R A M] [IsScalarTower R B M]

/-- An auxiliary definition, used for constructing the `Module (A ⊗[R] B) M` in
`TensorProduct.Algebra.module` below. -/
def moduleAux : A ⊗[R] B →ₗ[R] M →ₗ[R] M :=
  TensorProduct.lift
    { toFun := fun a => a • (Algebra.lsmul R R M : B →ₐ[R] Module.End R M).toLinearMap
      map_add' := fun r t => by
        ext
        simp only [add_smul, LinearMap.add_apply]
      map_smul' := fun n r => by
        ext
        simp only [RingHom.id_apply, LinearMap.smul_apply, smul_assoc] }

theorem moduleAux_apply (a : A) (b : B) (m : M) : moduleAux (a ⊗ₜ[R] b) m = a • b • m :=
  rfl

variable [SMulCommClass A B M]

/-- If `M` is a representation of two different `R`-algebras `A` and `B` whose actions commute,
then it is a representation the `R`-algebra `A ⊗[R] B`.

An important example arises from a semiring `S`; allowing `S` to act on itself via left and right
multiplication, the roles of `R`, `A`, `B`, `M` are played by `ℕ`, `S`, `Sᵐᵒᵖ`, `S`. This example
is important because a submodule of `S` as a `Module` over `S ⊗[ℕ] Sᵐᵒᵖ` is a two-sided ideal.

NB: This is not an instance because in the case `B = A` and `M = A ⊗[R] A` we would have a diamond
of `smul` actions. Furthermore, this would not be a mere definitional diamond but a true
mathematical diamond in which `A ⊗[R] A` had two distinct scalar actions on itself: one from its
multiplication, and one from this would-be instance. Arguably we could live with this but in any
case the real fix is to address the ambiguity in notation, probably along the lines outlined here:
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.234773.20base.20change/near/240929258
-/
protected def module : Module (A ⊗[R] B) M where
  smul x m := moduleAux x m
  zero_smul m := by simp only [(· • ·), map_zero, LinearMap.zero_apply]
  smul_zero x := by simp only [(· • ·), map_zero]
  smul_add x m₁ m₂ := by simp only [(· • ·), map_add]
  add_smul x y m := by simp only [(· • ·), map_add, LinearMap.add_apply]
  one_smul m := by
    -- Porting note: was one `simp only`, not two
    simp only [(· • ·), Algebra.TensorProduct.one_def]
    simp only [moduleAux_apply, one_smul]
  mul_smul x y m := by
    refine TensorProduct.induction_on x ?_ ?_ ?_ <;> refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b
      simp only [(· • ·), zero_mul, map_zero, LinearMap.zero_apply]
    · intro z w _ _
      simp only [(· • ·), zero_mul, map_zero, LinearMap.zero_apply]
    · intro a b
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a₁ b₁ a₂ b₂
      -- Porting note: was one `simp only`, not two
      simp only [(· • ·), Algebra.TensorProduct.tmul_mul_tmul]
      simp only [moduleAux_apply, mul_smul, smul_comm a₁ b₂]
    · intro z w hz hw a b
      -- Porting note: was one `simp only`, but random stuff doesn't work
      simp only [(· • ·)] at hz hw ⊢
      simp only [moduleAux_apply, mul_add, LinearMap.map_add,
        LinearMap.add_apply, moduleAux_apply, hz, hw]
    · intro z w _ _
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b z w hz hw
      simp only [(· • ·)] at hz hw ⊢
      simp only [LinearMap.map_add, add_mul, LinearMap.add_apply, hz, hw]
    · intro u v _ _ z w hz hw
      simp only [(· • ·)] at hz hw ⊢
      simp only [add_mul, LinearMap.map_add, LinearMap.add_apply, hz, hw, add_add_add_comm]

attribute [local instance] TensorProduct.Algebra.module

theorem smul_def (a : A) (b : B) (m : M) : a ⊗ₜ[R] b • m = a • b • m :=
  rfl

section Lemmas

theorem linearMap_comp_mul' :
    Algebra.linearMap R (A ⊗[R] B) ∘ₗ LinearMap.mul' R R =
      map (Algebra.linearMap R A) (Algebra.linearMap R B) := by
  ext
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars, map_tmul,
    Algebra.linearMap_apply, map_one, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mul'_apply, mul_one, Algebra.TensorProduct.one_def]

end Lemmas

end TensorProduct.Algebra

open LinearMap in
lemma Submodule.map_range_rTensor_subtype_lid {R Q} [CommSemiring R] [AddCommMonoid Q]
    [Module R Q] {I : Submodule R R} :
    (range <| rTensor Q I.subtype).map (TensorProduct.lid R Q) = I • ⊤ := by
  rw [← map_top, ← map_coe_toLinearMap, ← Submodule.map_comp, map_top]
  refine le_antisymm ?_ fun q h ↦ Submodule.smul_induction_on h
    (fun r hr q _ ↦ ⟨⟨r, hr⟩ ⊗ₜ q, by simp⟩) (by simp +contextual [add_mem])
  rintro _ ⟨t, rfl⟩
  exact t.induction_on (by simp) (by simp +contextual [Submodule.smul_mem_smul])
    (by simp +contextual [add_mem])

section

variable {R M S T : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [Semiring S] [Algebra R S] [Ring T] [Algebra R T]

variable (R S M) in
theorem TensorProduct.mk_surjective (h : Function.Surjective (algebraMap R S)) :
    Function.Surjective (TensorProduct.mk R S M 1) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  obtain ⟨x, rfl⟩ := h x
  rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
  exact ⟨x • y, rfl⟩

variable (S) in
lemma TensorProduct.flip_mk_surjective (h : Function.Surjective (algebraMap R T)) :
    Function.Surjective ((TensorProduct.mk R S T).flip 1) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨s, t, rfl⟩
  obtain ⟨r, rfl⟩ := h t
  rw [Algebra.algebraMap_eq_smul_one, ← smul_tmul]
  exact ⟨r • s, rfl⟩

variable (T) in
lemma Algebra.TensorProduct.includeRight_surjective (h : Function.Surjective (algebraMap R S)) :
    Function.Surjective (includeRight : T →ₐ[R] S ⊗[R] T) :=
  TensorProduct.mk_surjective _ _ _ h

lemma Algebra.TensorProduct.includeLeft_surjective
    (S A : Type*) [CommSemiring S] [Semiring A] [Algebra S A] [Algebra R A]
    [SMulCommClass R S A] (h : Function.Surjective (algebraMap R T)) :
    Function.Surjective (includeLeft : A →ₐ[S] A ⊗[R] T) :=
  TensorProduct.flip_mk_surjective _ h

end

variable {R A B : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A]
  [NonUnitalNonAssocSemiring B] [Module R A] [Module R B] [SMulCommClass R A A]
  [SMulCommClass R B B] [IsScalarTower R A A] [IsScalarTower R B B]

@[simp]
theorem TensorProduct.Algebra.mul'_comp_tensorTensorTensorComm :
    LinearMap.mul' R (A ⊗[R] B) ∘ₗ tensorTensorTensorComm R A A B B =
      map (LinearMap.mul' R A) (LinearMap.mul' R B) := by
  ext
  simp

lemma LinearMap.mul'_tensor :
    mul' R (A ⊗[R] B) = map (mul' R A) (mul' R B) ∘ₗ tensorTensorTensorComm R A B A B :=
  ext_fourfold' <| by simp

lemma LinearMap.mulLeft_tmul (a : A) (b : B) :
    mulLeft R (a ⊗ₜ[R] b) = map (mulLeft R a) (mulLeft R b) := by
  ext; simp

lemma LinearMap.mulRight_tmul (a : A) (b : B) :
    mulRight R (a ⊗ₜ[R] b) = map (mulRight R a) (mulRight R b) := by
  ext; simp
