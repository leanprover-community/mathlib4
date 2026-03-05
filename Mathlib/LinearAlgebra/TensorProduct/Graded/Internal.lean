/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Graded.External
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Tactic.SuppressCompilation

/-!
# Graded tensor products over graded algebras

The graded tensor product $A \hat\otimes_R B$ is imbued with a multiplication defined on homogeneous
tensors by:

$$(a \otimes b) \cdot (a' \otimes b') = (-1)^{\deg a' \deg b} (a \cdot a') \otimes (b \cdot b')$$

where $A$ and $B$ are algebras graded by `ℕ`, `ℤ`, or `ι` (or more generally, any index
that satisfies `Module ι (Additive ℤˣ)`).

## Main results

* `GradedTensorProduct R 𝒜 ℬ`: for families of submodules of `A` and `B` that form a graded algebra,
  this is a type alias for `A ⊗[R] B` with the appropriate multiplication.
* `GradedTensorProduct.instAlgebra`: the ring structure induced by this multiplication.
* `GradedTensorProduct.liftEquiv`: a universal property for graded tensor products

## Notation

* `𝒜 ᵍ⊗[R] ℬ` is notation for `GradedTensorProduct R 𝒜 ℬ`.
* `a ᵍ⊗ₜ b` is notation for `GradedTensorProduct.tmul _ a b`.

## References

* https://math.stackexchange.com/q/202718/1896
* [*Algebra I*, Bourbaki : Chapter III, §4.7, example (2)][bourbaki1989]

## Implementation notes

We cannot put the multiplication on `A ⊗[R] B` directly as it would conflict with the existing
multiplication defined without the $(-1)^{\deg a' \deg b}$ term. Furthermore, the ring `A` may not
have a unique graduation, and so we need the chosen graduation `𝒜` to appear explicitly in the
type.

## TODO

* Show that the tensor product of graded algebras is itself a graded algebra.
* Determine if replacing the synonym with a single-field structure improves performance.
-/

@[expose] public section

suppress_compilation

open scoped TensorProduct

variable {R ι A B : Type*}
variable [CommSemiring ι] [DecidableEq ι]
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

open DirectSum


variable (R) in
/-- A Type synonym for `A ⊗[R] B`, but with multiplication as `TensorProduct.gradedMul`.

This has notation `𝒜 ᵍ⊗[R] ℬ`. -/
@[nolint unusedArguments]
def GradedTensorProduct
    (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] :
    Type _ :=
  A ⊗[R] B

namespace GradedTensorProduct

open TensorProduct

@[inherit_doc GradedTensorProduct]
scoped[TensorProduct] notation:100 𝒜 " ᵍ⊗[" R "] " ℬ:100 => GradedTensorProduct R 𝒜 ℬ

instance instAddCommGroupWithOne : AddCommGroupWithOne (𝒜 ᵍ⊗[R] ℬ) :=
  Algebra.TensorProduct.instAddCommGroupWithOne
instance : Module R (𝒜 ᵍ⊗[R] ℬ) := TensorProduct.leftModule

variable (R) in
/-- The casting equivalence to move between regular and graded tensor products. -/
def of : A ⊗[R] B ≃ₗ[R] 𝒜 ᵍ⊗[R] ℬ := LinearEquiv.refl _ _

@[simp]
theorem of_one : of R 𝒜 ℬ 1 = 1 := rfl

@[simp]
theorem of_symm_one : (of R 𝒜 ℬ).symm 1 = 1 := rfl

@[simp]
theorem of_symm_of (x : A ⊗[R] B) : (of R 𝒜 ℬ).symm (of R 𝒜 ℬ x) = x := rfl

@[simp]
theorem symm_of_of (x : 𝒜 ᵍ⊗[R] ℬ) : of R 𝒜 ℬ ((of R 𝒜 ℬ).symm x) = x := rfl

/-- Two linear maps from the graded tensor product agree if they agree on the underlying tensor
product. -/
@[ext]
theorem hom_ext {M} [AddCommMonoid M] [Module R M] ⦃f g : 𝒜 ᵍ⊗[R] ℬ →ₗ[R] M⦄
    (h : f ∘ₗ of R 𝒜 ℬ = (g ∘ₗ of R 𝒜 ℬ : A ⊗[R] B →ₗ[R] M)) :
    f = g :=
  h

variable (R) {𝒜 ℬ} in
/-- The graded tensor product of two elements of graded rings. -/
abbrev tmul (a : A) (b : B) : 𝒜 ᵍ⊗[R] ℬ := of R 𝒜 ℬ (a ⊗ₜ b)

@[inherit_doc]
notation:100 x " ᵍ⊗ₜ " y:100 => tmul _ x y

@[inherit_doc]
notation:100 x " ᵍ⊗ₜ[" R "] " y:100 => tmul R x y

variable (R) in
/-- An auxiliary construction to move between the graded tensor product of internally-graded objects
and the tensor product of direct sums. -/
noncomputable def auxEquiv : (𝒜 ᵍ⊗[R] ℬ) ≃ₗ[R] (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i) :=
  let fA := (decomposeAlgEquiv 𝒜).toLinearEquiv
  let fB := (decomposeAlgEquiv ℬ).toLinearEquiv
  (of R 𝒜 ℬ).symm.trans (TensorProduct.congr fA fB)

theorem auxEquiv_tmul (a : A) (b : B) :
    auxEquiv R 𝒜 ℬ (a ᵍ⊗ₜ b) = decompose 𝒜 a ⊗ₜ decompose ℬ b := rfl

set_option backward.isDefEq.respectTransparency false in
theorem auxEquiv_one : auxEquiv R 𝒜 ℬ 1 = 1 := by
  rw [← of_one, Algebra.TensorProduct.one_def, auxEquiv_tmul 𝒜 ℬ, DirectSum.decompose_one,
    DirectSum.decompose_one, Algebra.TensorProduct.one_def]

theorem auxEquiv_symm_one : (auxEquiv R 𝒜 ℬ).symm 1 = 1 :=
  (LinearEquiv.symm_apply_eq _).mpr (auxEquiv_one _ _).symm

variable [Module ι (Additive ℤˣ)]

/-- Auxiliary construction used to build the `Mul` instance and get distributivity of `+` and
`\smul`. -/
noncomputable def mulHom : (𝒜 ᵍ⊗[R] ℬ) →ₗ[R] (𝒜 ᵍ⊗[R] ℬ) →ₗ[R] (𝒜 ᵍ⊗[R] ℬ) := by
  letI fAB1 := auxEquiv R 𝒜 ℬ
  have := ((gradedMul R (𝒜 ·) (ℬ ·)).compl₁₂ fAB1.toLinearMap fAB1.toLinearMap).compr₂
    fAB1.symm.toLinearMap
  exact this

theorem mulHom_apply (x y : 𝒜 ᵍ⊗[R] ℬ) :
    mulHom 𝒜 ℬ x y
      = (auxEquiv R 𝒜 ℬ).symm (gradedMul R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) (auxEquiv R 𝒜 ℬ y)) :=
  rfl

/-- The multiplication on the graded tensor product.

See `GradedTensorProduct.coe_mul_coe` for a characterization on pure tensors. -/
instance : Mul (𝒜 ᵍ⊗[R] ℬ) where mul x y := mulHom 𝒜 ℬ x y

theorem mul_def (x y : 𝒜 ᵍ⊗[R] ℬ) : x * y = mulHom 𝒜 ℬ x y := rfl

-- Before https://github.com/leanprover-community/mathlib4/pull/8386 this was `@[simp]` but it times out when we try to apply it.
theorem auxEquiv_mul (x y : 𝒜 ᵍ⊗[R] ℬ) :
    auxEquiv R 𝒜 ℬ (x * y) = gradedMul R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) (auxEquiv R 𝒜 ℬ y) :=
  LinearEquiv.eq_symm_apply _ |>.mp rfl

instance instMonoid : Monoid (𝒜 ᵍ⊗[R] ℬ) where
  mul_one x := by
    rw [mul_def, mulHom_apply, auxEquiv_one, gradedMul_one, LinearEquiv.symm_apply_apply]
  one_mul x := by
    rw [mul_def, mulHom_apply, auxEquiv_one, one_gradedMul, LinearEquiv.symm_apply_apply]
  mul_assoc x y z := by
    simp_rw [mul_def, mulHom_apply, LinearEquiv.apply_symm_apply]
    rw [gradedMul_assoc]

instance instRing : Ring (𝒜 ᵍ⊗[R] ℬ) where
  __ := instAddCommGroupWithOne 𝒜 ℬ
  __ := instMonoid 𝒜 ℬ
  right_distrib x y z := by simp_rw [mul_def, LinearMap.map_add₂]
  left_distrib x y z := by simp_rw [mul_def, map_add]
  mul_zero x := by simp_rw [mul_def, map_zero]
  zero_mul x := by simp_rw [mul_def, LinearMap.map_zero₂]

set_option backward.isDefEq.respectTransparency false in
/-- The characterization of this multiplication on partially homogeneous elements. -/
theorem tmul_coe_mul_coe_tmul {j₁ i₂ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (b₁ : B) * (a₂ : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ) =
      (-1 : ℤˣ) ^ (j₁ * i₂) • ((a₁ * a₂ : A) ᵍ⊗ₜ (b₁ * b₂ : B)) := by
  dsimp only [mul_def, mulHom_apply, of_symm_of]
  dsimp [auxEquiv, tmul]
  rw [decompose_coe, decompose_coe]
  simp_rw [← lof_eq_of R]
  rw [tmul_of_gradedMul_of_tmul]
  simp_rw [lof_eq_of R]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_smul` to `LinearEquiv.map_smul`
  rw [@Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R, LinearEquiv.map_smul, map_smul,
    Int.cast_smul_eq_zsmul R, ← @Units.smul_def _ _ (_) (_)]
  rw [congr_symm_tmul]
  dsimp
  simp_rw [decompose_symm_mul, decompose_symm_of, Equiv.symm_apply_apply]

/-- A special case for when `b₁` has grade 0. -/
theorem tmul_zero_coe_mul_coe_tmul {i₂ : ι} (a₁ : A) (b₁ : ℬ 0) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (b₁ : B) * (a₂ : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ) =
      ((a₁ * a₂ : A) ᵍ⊗ₜ (b₁ * b₂ : B)) := by
  rw [tmul_coe_mul_coe_tmul, zero_mul, uzpow_zero, one_smul]

/-- A special case for when `a₂` has grade 0. -/
theorem tmul_coe_mul_zero_coe_tmul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 0) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (b₁ : B) * (a₂ : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ) =
      ((a₁ * a₂ : A) ᵍ⊗ₜ (b₁ * b₂ : B)) := by
  rw [tmul_coe_mul_coe_tmul, mul_zero, uzpow_zero, one_smul]

theorem tmul_one_mul_coe_tmul {i₂ : ι} (a₁ : A) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (1 : B) * (a₂ : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ) = (a₁ * a₂ : A) ᵍ⊗ₜ (b₂ : B) := by
  convert tmul_zero_coe_mul_coe_tmul 𝒜 ℬ a₁ (@GradedMonoid.GOne.one _ (ℬ ·) _ _) a₂ b₂
  rw [SetLike.coe_gOne, one_mul]

theorem tmul_coe_mul_one_tmul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (b₁ : B) * (1 : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ) = (a₁ : A) ᵍ⊗ₜ (b₁ * b₂ : B) := by
  convert tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ b₁ (@GradedMonoid.GOne.one _ (𝒜 ·) _ _) b₂
  rw [SetLike.coe_gOne, mul_one]

theorem tmul_one_mul_one_tmul (a₁ : A) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (1 : B) * (1 : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ) = (a₁ : A) ᵍ⊗ₜ (b₂ : B) := by
  convert tmul_coe_mul_zero_coe_tmul 𝒜 ℬ
    a₁ (GradedMonoid.GOne.one (A := (ℬ ·))) (GradedMonoid.GOne.one (A := (𝒜 ·))) b₂
  · rw [SetLike.coe_gOne, mul_one]
  · rw [SetLike.coe_gOne, one_mul]

/-- The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps]
def includeLeftRingHom : A →+* 𝒜 ᵍ⊗[R] ℬ where
  toFun a := a ᵍ⊗ₜ 1
  map_zero' := by simp
  map_add' := by simp [tmul, TensorProduct.add_tmul]
  map_one' := rfl
  map_mul' a₁ a₂ := by
    classical
    rw [← DirectSum.sum_support_decompose 𝒜 a₂, Finset.mul_sum]
    simp_rw [tmul, sum_tmul, map_sum, Finset.mul_sum]
    congr
    ext i
    rw [← SetLike.coe_gOne ℬ, tmul_coe_mul_coe_tmul, zero_mul, uzpow_zero, one_smul,
      SetLike.coe_gOne, one_mul]

instance instAlgebra : Algebra R (𝒜 ᵍ⊗[R] ℬ) where
  algebraMap := (includeLeftRingHom 𝒜 ℬ).comp (algebraMap R A)
  commutes' r x := by
    dsimp [mul_def, mulHom_apply, auxEquiv_tmul]
    simp_rw [DirectSum.decompose_algebraMap, DirectSum.decompose_one, algebraMap_gradedMul,
      gradedMul_algebraMap]
  smul_def' r x := by
    dsimp [mul_def, mulHom_apply, auxEquiv_tmul]
    simp_rw [DirectSum.decompose_algebraMap, DirectSum.decompose_one, algebraMap_gradedMul]
    -- Qualified `map_smul` to avoid a TC timeout https://github.com/leanprover-community/mathlib4/pull/8386
    rw [LinearEquiv.map_smul]
    simp

lemma algebraMap_def (r : R) : algebraMap R (𝒜 ᵍ⊗[R] ℬ) r = algebraMap R A r ᵍ⊗ₜ[R] 1 := rfl

theorem tmul_algebraMap_mul_coe_tmul {i₂ : ι} (a₁ : A) (r : R) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] algebraMap R B r * (a₂ : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ)
      = (a₁ * a₂ : A) ᵍ⊗ₜ (algebraMap R B r * b₂ : B) :=
  tmul_zero_coe_mul_coe_tmul 𝒜 ℬ a₁ (GAlgebra.toFun (A := (ℬ ·)) r) a₂ b₂

theorem tmul_coe_mul_algebraMap_tmul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (r : R) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (b₁ : B) * algebraMap R A r ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ)
      = (a₁ * algebraMap R A r : A) ᵍ⊗ₜ (b₁ * b₂ : B) :=
  tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ b₁ (GAlgebra.toFun (A := (𝒜 ·)) r) b₂

/-- The algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps!]
def includeLeft : A →ₐ[R] 𝒜 ᵍ⊗[R] ℬ where
  toRingHom := includeLeftRingHom 𝒜 ℬ
  commutes' _ := rfl

/-- The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`. -/
@[simps!]
def includeRight : B →ₐ[R] (𝒜 ᵍ⊗[R] ℬ) :=
  AlgHom.ofLinearMap (R := R) (A := B) (B := 𝒜 ᵍ⊗[R] ℬ)
    (f := {
       toFun := fun b => 1 ᵍ⊗ₜ b
       map_add' := by simp [tmul, TensorProduct.tmul_add]
       map_smul' := by simp [tmul, TensorProduct.tmul_smul] })
    (map_one := rfl)
    (map_mul := by
      rw [LinearMap.map_mul_iff]
      refine DirectSum.decompose_lhom_ext ℬ fun i₁ => ?_
      ext b₁ b₂ : 2
      dsimp
      rw [tmul_coe_mul_one_tmul])

lemma algebraMap_def' (r : R) : algebraMap R (𝒜 ᵍ⊗[R] ℬ) r = 1 ᵍ⊗ₜ[R] algebraMap R B r :=
  (includeRight 𝒜 ℬ).commutes r |>.symm

variable {C} [Ring C] [Algebra R C]

set_option backward.isDefEq.respectTransparency false in
/-- The forwards direction of the universal property; an algebra morphism out of the graded tensor
product can be assembled from maps on each component that (anti)commute on pure elements of the
corresponding graded algebras. -/
def lift (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h_anti_commutes : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a)) :
    (𝒜 ᵍ⊗[R] ℬ) →ₐ[R] C :=
  AlgHom.ofLinearMap
    (LinearMap.mul' R C
      ∘ₗ (TensorProduct.map f.toLinearMap g.toLinearMap)
      ∘ₗ ((of R 𝒜 ℬ).symm : 𝒜 ᵍ⊗[R] ℬ →ₗ[R] A ⊗[R] B))
    (by
      dsimp [Algebra.TensorProduct.one_def]
      simp only [map_one, mul_one])
    (by
      rw [LinearMap.map_mul_iff]
      ext a₁ : 3
      refine DirectSum.decompose_lhom_ext ℬ fun j₁ => ?_
      ext b₁ : 3
      refine DirectSum.decompose_lhom_ext 𝒜 fun i₂ => ?_
      ext a₂ b₂ : 2
      dsimp
      rw [tmul_coe_mul_coe_tmul]
      rw [@Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R, map_smul, map_smul, map_smul]
      rw [Int.cast_smul_eq_zsmul R, ← @Units.smul_def _ _ (_) (_)]
      rw [of_symm_of, map_tmul, LinearMap.mul'_apply]
      simp_rw [AlgHom.toLinearMap_apply, map_mul]
      simp_rw [mul_assoc (f a₁), ← mul_assoc _ _ (g b₂), h_anti_commutes, mul_smul_comm,
        smul_mul_assoc, smul_smul, Int.units_mul_self, one_smul])

@[simp]
theorem lift_tmul (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h_anti_commutes : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a))
    (a : A) (b : B) :
    lift 𝒜 ℬ f g h_anti_commutes (a ᵍ⊗ₜ b) = f a * g b :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The universal property of the graded tensor product; every algebra morphism uniquely factors
as a pair of algebra morphisms that anticommute with respect to the grading. -/
def liftEquiv :
    { fg : (A →ₐ[R] C) × (B →ₐ[R] C) //
        ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), fg.1 a * fg.2 b = (-1 : ℤˣ)^(j * i) • (fg.2 b * fg.1 a)} ≃
      ((𝒜 ᵍ⊗[R] ℬ) →ₐ[R] C) where
  toFun fg := lift 𝒜 ℬ _ _ fg.prop
  invFun F := ⟨(F.comp (includeLeft 𝒜 ℬ), F.comp (includeRight 𝒜 ℬ)), fun i j a b => by
    dsimp
    rw [← map_mul, ← map_mul F, tmul_coe_mul_coe_tmul, one_mul, mul_one, AlgHom.map_smul_of_tower,
      tmul_one_mul_one_tmul, smul_smul, Int.units_mul_self, one_smul]⟩
  left_inv fg := by ext <;> (dsimp; simp only [map_one, mul_one, one_mul])
  right_inv F := by
    apply AlgHom.toLinearMap_injective
    ext
    dsimp
    rw [← map_mul, tmul_one_mul_one_tmul]

/-- Two algebra morphism from the graded tensor product agree if their compositions with the left
and right inclusions agree. -/
@[ext]
lemma algHom_ext ⦃f g : (𝒜 ᵍ⊗[R] ℬ) →ₐ[R] C⦄
    (ha : f.comp (includeLeft 𝒜 ℬ) = g.comp (includeLeft 𝒜 ℬ))
    (hb : f.comp (includeRight 𝒜 ℬ) = g.comp (includeRight 𝒜 ℬ)) : f = g :=
  (liftEquiv 𝒜 ℬ).symm.injective <| Subtype.ext <| Prod.ext ha hb

set_option backward.isDefEq.respectTransparency false in
/-- The non-trivial symmetric braiding, sending $a \otimes b$ to
$(-1)^{\deg a' \deg b} (b \otimes a)$. -/
def comm : (𝒜 ᵍ⊗[R] ℬ) ≃ₐ[R] (ℬ ᵍ⊗[R] 𝒜) :=
  AlgEquiv.ofLinearEquiv
    (auxEquiv R 𝒜 ℬ ≪≫ₗ gradedComm R _ _ ≪≫ₗ (auxEquiv R ℬ 𝒜).symm)
    (fun x y => by
      dsimp
      simp_rw [auxEquiv_mul, gradedComm_gradedMul, LinearEquiv.symm_apply_eq,
        ← gradedComm_gradedMul, auxEquiv_mul, LinearEquiv.apply_symm_apply, gradedComm_gradedMul])

lemma auxEquiv_comm (x : 𝒜 ᵍ⊗[R] ℬ) :
    auxEquiv R ℬ 𝒜 (comm 𝒜 ℬ x) = gradedComm R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) :=
  LinearEquiv.eq_symm_apply _ |>.mp rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma comm_coe_tmul_coe {i j : ι} (a : 𝒜 i) (b : ℬ j) :
    comm 𝒜 ℬ (a ᵍ⊗ₜ b) = (-1 : ℤˣ) ^ (j * i) • (b ᵍ⊗ₜ a : ℬ ᵍ⊗[R] 𝒜) :=
  (auxEquiv R ℬ 𝒜).injective <| by
    simp_rw [auxEquiv_comm, auxEquiv_tmul, decompose_coe, ← lof_eq_of R, gradedComm_of_tmul_of,
      @Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R]
    -- Qualified `map_smul` to avoid a TC timeout https://github.com/leanprover-community/mathlib4/pull/8386
    rw [LinearEquiv.map_smul, auxEquiv_tmul]
    simp_rw [decompose_coe, lof_eq_of]

end GradedTensorProduct
