/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.RingTheory.TensorProduct.Maps

/-!

# Some results on tensor product of subalgebras

## Linear maps induced by multiplication for subalgebras

Let `R` be a commutative ring, `S` be a commutative `R`-algebra.
Let `A` and `B` be `R`-subalgebras in `S` (`Subalgebra R S`). We define some linear maps
induced by the multiplication in `S`, which are
mainly used in the definition of linearly disjointness.

- `Subalgebra.mulMap`: the natural `R`-algebra homomorphism `A ⊗[R] B →ₐ[R] S`
  induced by the multiplication in `S`, whose image is `A ⊔ B` (`Subalgebra.mulMap_range`).

- `Subalgebra.mulMap'`: the natural `R`-algebra homomorphism `A ⊗[R] B →ₗ[R] A ⊔ B`
  induced by multiplication in `S`, which is surjective (`Subalgebra.mulMap'_surjective`).

- `Subalgebra.lTensorBot`, `Subalgebra.rTensorBot`: the natural isomorphism of `R`-algebras between
  `i(R) ⊗[R] A` and `A`, resp. `A ⊗[R] i(R)` and `A`, induced by multiplication in `S`,
  here `i : R → S` is the structure map. They generalize `Algebra.TensorProduct.lid`
  and `Algebra.TensorProduct.rid`, as `i(R)` is not necessarily isomorphic to `R`.

  They are `Subalgebra` versions of `Submodule.lTensorOne` and `Submodule.rTensorOne`.

-/

open scoped TensorProduct

open Module

noncomputable section

variable {R S T : Type*}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S] [Semiring T] [Algebra R T]

namespace Subalgebra

variable (A : Subalgebra R S)

/-- If `A` is a subalgebra of `S/R`, there is the natural `R`-algebra isomorphism between
`i(R) ⊗[R] A` and `A` induced by multiplication in `S`, here `i : R → S` is the structure map.
This generalizes `Algebra.TensorProduct.lid` as `i(R)` is not necessarily isomorphic to `R`.

This is the `Subalgebra` version of `Submodule.lTensorOne` -/
def lTensorBot : (⊥ : Subalgebra R S) ⊗[R] A ≃ₐ[R] A := by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).lTensorOne ?_ ?_
  · rintro x y a b
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algebraMap R _ y' = y := Subtype.val_injective hy
    rw [← hx, ← hy, ← map_mul]
    erw [(toSubmodule A).lTensorOne_tmul x' a,
      (toSubmodule A).lTensorOne_tmul y' b,
      (toSubmodule A).lTensorOne_tmul (x' * y') (a * b)]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, mul_comm x' y']
  · exact Submodule.lTensorOne_one_tmul _

variable {A}

@[simp]
theorem lTensorBot_tmul (x : R) (a : A) : A.lTensorBot (algebraMap R _ x ⊗ₜ[R] a) = x • a :=
  (toSubmodule A).lTensorOne_tmul x a

@[simp]
theorem lTensorBot_one_tmul (a : A) : A.lTensorBot (1 ⊗ₜ[R] a) = a :=
  (toSubmodule A).lTensorOne_one_tmul a

@[simp]
theorem lTensorBot_symm_apply (a : A) : A.lTensorBot.symm a = 1 ⊗ₜ[R] a := rfl

variable (A) in
/-- If `A` is a subalgebra of `S/R`, there is the natural `R`-algebra isomorphism between
`A ⊗[R] i(R)` and `A` induced by multiplication in `S`, here `i : R → S` is the structure map.
This generalizes `Algebra.TensorProduct.rid` as `i(R)` is not necessarily isomorphic to `R`.

This is the `Subalgebra` version of `Submodule.rTensorOne` -/
def rTensorBot : A ⊗[R] (⊥ : Subalgebra R S) ≃ₐ[R] A := by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).rTensorOne ?_ ?_
  · rintro a b x y
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algebraMap R _ y' = y := Subtype.val_injective hy
    rw [← hx, ← hy, ← map_mul]
    erw [(toSubmodule A).rTensorOne_tmul x' a,
      (toSubmodule A).rTensorOne_tmul y' b,
      (toSubmodule A).rTensorOne_tmul (x' * y') (a * b)]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, mul_comm x' y']
  · exact Submodule.rTensorOne_tmul_one _

@[simp]
theorem rTensorBot_tmul (x : R) (a : A) : A.rTensorBot (a ⊗ₜ[R] algebraMap R _ x) = x • a :=
  (toSubmodule A).rTensorOne_tmul x a

@[simp]
theorem rTensorBot_tmul_one (a : A) : A.rTensorBot (a ⊗ₜ[R] 1) = a :=
  (toSubmodule A).rTensorOne_tmul_one a

@[simp]
theorem rTensorBot_symm_apply (a : A) : A.rTensorBot.symm a = a ⊗ₜ[R] 1 := rfl

variable (A)

@[simp]
theorem comm_trans_lTensorBot :
    (Algebra.TensorProduct.comm R _ _).trans A.lTensorBot = A.rTensorBot :=
  AlgEquiv.toLinearEquiv_injective (toSubmodule A).comm_trans_lTensorOne

@[simp]
theorem comm_trans_rTensorBot :
    (Algebra.TensorProduct.comm R _ _).trans A.rTensorBot = A.lTensorBot :=
  AlgEquiv.toLinearEquiv_injective (toSubmodule A).comm_trans_rTensorOne

end Subalgebra

namespace Algebra.TensorProduct

variable (R S T)

/-- Given `R`-algebras `S,T`, there is a natural `R`-linear isomorphism from `S ⊗[R] T` to
`S' ⊗[R] T'` where `S',T'` are the images of `S,T` in `S ⊗[R] T` respectively.
This is promoted to an `R`-algebra isomorphism `Algebra.TensorProduct.algEquivIncludeRange`. -/
def linearEquivIncludeRange :
    S ⊗[R] T ≃ₗ[R] (includeLeft : S →ₐ[R] S ⊗[R] T).range ⊗[R]
      (includeRight : T →ₐ[R] S ⊗[R] T).range := .ofLinear
  (_root_.TensorProduct.map
    includeLeft.toLinearMap.rangeRestrict includeRight.toLinearMap.rangeRestrict)
  ((LinearMap.range includeLeft).mulMap (LinearMap.range includeRight))
  (_root_.TensorProduct.ext' <| by
    rintro ⟨x', x, rfl : x ⊗ₜ 1 = x'⟩ ⟨y', y, rfl : 1 ⊗ₜ y = y'⟩
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    erw [Submodule.mulMap_tmul]
    rw [tmul_mul_tmul, mul_one, one_mul, _root_.TensorProduct.map_tmul]
    rfl)
  (_root_.TensorProduct.ext' fun x y ↦ by
    rw [LinearMap.comp_apply, LinearMap.id_apply, _root_.TensorProduct.map_tmul]
    erw [Submodule.mulMap_tmul]
    change (x ⊗ₜ 1) * (1 ⊗ₜ y) = _
    rw [tmul_mul_tmul, mul_one, one_mul])

theorem linearEquivIncludeRange_toLinearMap :
    (linearEquivIncludeRange R S T).toLinearMap =
      _root_.TensorProduct.map includeLeft.toLinearMap.rangeRestrict
        includeRight.toLinearMap.rangeRestrict := rfl

theorem linearEquivIncludeRange_symm_toLinearMap :
    (linearEquivIncludeRange R S T).symm.toLinearMap =
      (LinearMap.range includeLeft).mulMap (LinearMap.range includeRight) := rfl

@[simp]
theorem linearEquivIncludeRange_tmul (x y) :
    linearEquivIncludeRange R S T (x ⊗ₜ[R] y) =
      ((includeLeft : S →ₐ[R] S ⊗[R] T).rangeRestrict x) ⊗ₜ[R]
        ((includeRight : T →ₐ[R] S ⊗[R] T).rangeRestrict y) := rfl

@[simp]
theorem linearEquivIncludeRange_symm_tmul (x y) :
    (linearEquivIncludeRange R S T).symm (x ⊗ₜ[R] y) = x.1 * y.1 := rfl

/-- Given `R`-algebras `S,T`, there is a natural `R`-algebra isomorphism from `S ⊗[R] T` to
`S' ⊗[R] T'` where `S',T'` are the images of `S,T` in `S ⊗[R] T` respectively. -/
def algEquivIncludeRange :
    S ⊗[R] T ≃ₐ[R] (includeLeft : S →ₐ[R] S ⊗[R] T).range ⊗[R]
      (includeRight : T →ₐ[R] S ⊗[R] T).range :=
  algEquivOfLinearEquivTensorProduct (linearEquivIncludeRange R S T) (by simp) rfl

theorem algEquivIncludeRange_toAlgHom :
    (algEquivIncludeRange R S T).toAlgHom =
      map includeLeft.rangeRestrict includeRight.rangeRestrict := rfl

@[simp]
theorem algEquivIncludeRange_tmul (x y) :
    algEquivIncludeRange R S T (x ⊗ₜ[R] y) =
      ((includeLeft : S →ₐ[R] S ⊗[R] T).rangeRestrict x) ⊗ₜ[R]
        ((includeRight : T →ₐ[R] S ⊗[R] T).rangeRestrict y) := rfl

@[simp]
theorem algEquivIncludeRange_symm_tmul (x y) :
    (algEquivIncludeRange R S T).symm (x ⊗ₜ[R] y) = x.1 * y.1 := rfl

end Algebra.TensorProduct

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T]

variable (A B : Subalgebra R S)

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`,
there is the natural `R`-algebra homomorphism
`A ⊗[R] B →ₐ[R] S` induced by multiplication in `S`. -/
def Subalgebra.mulMap : A ⊗[R] B →ₐ[R] S := Algebra.TensorProduct.productMap A.val B.val

variable (R S T) in
theorem Algebra.TensorProduct.algEquivIncludeRange_symm_toAlgHom :
    (algEquivIncludeRange R S T).symm.toAlgHom =
      (includeLeft : S →ₐ[R] S ⊗[R] T).range.mulMap includeRight.range := rfl

namespace Subalgebra

@[simp]
theorem mulMap_tmul (a : A) (b : B) : mulMap A B (a ⊗ₜ[R] b) = a.1 * b.1 := rfl

theorem mulMap_map_comp_eq (f : S →ₐ[R] T) :
    (mulMap (A.map f) (B.map f)).comp
      (Algebra.TensorProduct.map (f.subalgebraMap A) (f.subalgebraMap B))
        = f.comp (mulMap A B) := by
  ext <;> simp

theorem mulMap_toLinearMap : (A.mulMap B).toLinearMap = (toSubmodule A).mulMap (toSubmodule B) :=
  rfl

theorem mulMap_comm : mulMap B A = (mulMap A B).comp (Algebra.TensorProduct.comm R B A) := by
  ext <;> simp

theorem mulMap_range : (A.mulMap B).range = A ⊔ B := by
  simp_rw [mulMap, Algebra.TensorProduct.productMap_range, Subalgebra.range_val]

theorem mulMap_bot_left_eq : mulMap ⊥ A = A.val.comp A.lTensorBot.toAlgHom :=
  AlgHom.toLinearMap_injective (toSubmodule A).mulMap_one_left_eq

theorem mulMap_bot_right_eq : mulMap A ⊥ = A.val.comp A.rTensorBot.toAlgHom :=
  AlgHom.toLinearMap_injective (toSubmodule A).mulMap_one_right_eq

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`,
there is the natural `R`-algebra homomorphism
`A ⊗[R] B →ₐ[R] A ⊔ B` induced by multiplication in `S`,
which is surjective (`Subalgebra.mulMap'_surjective`). -/
def mulMap' : A ⊗[R] B →ₐ[R] ↥(A ⊔ B) :=
  (equivOfEq _ _ (mulMap_range A B)).toAlgHom.comp (mulMap A B).rangeRestrict

variable {A B} in
@[simp]
theorem val_mulMap'_tmul (a : A) (b : B) : (mulMap' A B (a ⊗ₜ[R] b) : S) = a.1 * b.1 := rfl

theorem mulMap'_surjective : Function.Surjective (mulMap' A B) := by
  simp_rw [mulMap', AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe,
    EquivLike.comp_surjective, AlgHom.rangeRestrict_surjective]

end Subalgebra

end CommSemiring
