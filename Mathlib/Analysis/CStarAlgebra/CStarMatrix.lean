/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Matrix
import Mathlib.Topology.UniformSpace.Matrix

/-!
# Matrices with entries in a C⋆-algebra

This file creates a type copy of `Matrix m n A` called `CStarMatrix m n A` meant for vectors with
entries in a C⋆-algebra `A`. Its action on `WithCStarModule (n → A)` (via `Matrix.mulVec`) gives
it the operator norm, and this norm makes `CStarMatrix n n A` a C⋆-algebra.

## Main declarations

+ `CStarMatrix m n A`: the type copy
+ `CStarMatrix.instCStarRing`: square matrices with entries in a C⋆-algebra form a C⋆-algebra

## Implementation notes

The norm on this type induces the product uniformity and bornology, but these are not defeq to
`Pi.uniformSpace` and `Pi.instBornology`. Hence, we prove the equality to the Pi instances and
replace the uniformity and bornology by the Pi ones when registering the
`NormedAddCommGroup (CStarMatrix m n A)` instance. See the docstring of the `TopologyAux` section
below for more details.
-/

set_option maxSynthPendingDepth 2

open scoped ComplexOrder Topology Uniformity Bornology Matrix NNReal InnerProductSpace
  WithCStarModule

/-- Type copy `Matrix m n A` meant for matrices with entries in a C⋆-algebra. This is
a C⋆-algebra when `m = n`. This is an abbrev in order to inherit all instances from `Matrix`,
which includes the product uniformity, but not a norm. -/
def CStarMatrix (m : Type*) (n : Type*) (A : Type*) := Matrix m n A

namespace CStarMatrix

variable {m n A B R S : Type*}

section basic

variable (m n A) in
/-- The equivalence between `Matrix m n A` and `CStarMatrix m n A`. -/
def ofMatrix {m n A : Type*} : Matrix m n A ≃ CStarMatrix m n A := Equiv.refl _

lemma ofMatrix_apply {M : Matrix m n A} {i : m} : (ofMatrix M) i = M i := rfl

lemma ofMatrix_symm_apply {M : CStarMatrix m n A} {i : m} : (ofMatrix.symm M) i = M i := rfl

theorem ext_iff {M N : CStarMatrix m n A} : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩

@[ext]
lemma ext {M₁ M₂ : CStarMatrix m n A} (h : ∀ i j, M₁ i j = M₂ i j) : M₁ = M₂ := ext_iff.mp h

/-- `M.map f` is the matrix obtained by applying `f` to each entry of the matrix `M`. -/
def map (M : CStarMatrix m n A) (f : A → B) : CStarMatrix m n B :=
  ofMatrix fun i j => f (M i j)

@[simp]
theorem map_apply {M : CStarMatrix m n A} {f : A → B} {i : m} {j : n} : M.map f i j = f (M i j) :=
  rfl

@[simp]
theorem map_id (M : CStarMatrix m n A) : M.map id = M := by
  ext
  rfl

@[simp]
theorem map_id' (M : CStarMatrix m n A) : M.map (·) = M := map_id M

theorem map_map {C : Type*} {M : Matrix m n A} {f : A → B} {g : B → C} :
    (M.map f).map g = M.map (g ∘ f) := by ext; rfl

theorem map_injective {f : A → B} (hf : Function.Injective f) :
    Function.Injective fun M : CStarMatrix m n A => M.map f := fun _ _ h =>
  ext fun i j => hf <| ext_iff.mpr h i j

/-- The transpose of a matrix. -/
def transpose (M : CStarMatrix m n A) : CStarMatrix n m A :=
  ofMatrix fun x y => M y x

@[simp]
theorem transpose_apply (M : CStarMatrix m n A) (i j) : transpose M i j = M j i :=
  rfl

/-- The conjugate transpose of a matrix defined in term of `star`. -/
def conjTranspose [Star A] (M : CStarMatrix m n A) : CStarMatrix n m A :=
  M.transpose.map star

instance instStar [Star A] : Star (CStarMatrix n n A) where
  star M := M.conjTranspose

instance instInvolutiveStar [InvolutiveStar A] : InvolutiveStar (CStarMatrix n n A) where
  star_involutive := star_involutive (R := Matrix n n A)

instance instInhabited [Inhabited A] : Inhabited (CStarMatrix m n A) :=
  inferInstanceAs <| Inhabited <| m → n → A

instance instDecidableEq [DecidableEq A] [Fintype m] [Fintype n] :
    DecidableEq (CStarMatrix m n A) :=
  Fintype.decidablePiFintype

instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (α) [Fintype α] :
    Fintype (CStarMatrix m n α) := inferInstanceAs (Fintype (m → n → α))

instance {n m} [Finite m] [Finite n] (α) [Finite α] :
    Finite (CStarMatrix m n α) := inferInstanceAs (Finite (m → n → α))

instance instAdd [Add A] : Add (CStarMatrix m n A) :=
  Pi.instAdd

instance instAddSemigroup [AddSemigroup A] : AddSemigroup (CStarMatrix m n A) :=
  Pi.addSemigroup

instance instAddCommSemigroup [AddCommSemigroup A] : AddCommSemigroup (CStarMatrix m n A) :=
  Pi.addCommSemigroup

instance instZero [Zero A] : Zero (CStarMatrix m n A) :=
  Pi.instZero

instance instAddZeroClass [AddZeroClass A] : AddZeroClass (CStarMatrix m n A) :=
  Pi.addZeroClass

instance instAddMonoid [AddMonoid A] : AddMonoid (CStarMatrix m n A) :=
  Pi.addMonoid

instance instAddCommMonoid [AddCommMonoid A] : AddCommMonoid (CStarMatrix m n A) :=
  Pi.addCommMonoid

instance instNeg [Neg A] : Neg (CStarMatrix m n A) :=
  Pi.instNeg

instance instSub [Sub A] : Sub (CStarMatrix m n A) :=
  Pi.instSub

instance instAddGroup [AddGroup A] : AddGroup (CStarMatrix m n A) :=
  Pi.addGroup

instance instAddCommGroup [AddCommGroup A] : AddCommGroup (CStarMatrix m n A) :=
  Pi.addCommGroup

instance instUnique [Unique A] : Unique (CStarMatrix m n A) :=
  Pi.unique

instance instSubsingleton [Subsingleton A] : Subsingleton (CStarMatrix m n A) :=
  inferInstanceAs <| Subsingleton <| m → n → A

instance instNonempty [Nonempty m] [Nonempty n] [Nontrivial A] : Nontrivial (CStarMatrix m n A) :=
  Function.nontrivial

instance instSmul [SMul R A] : SMul R (CStarMatrix m n A) :=
  Pi.instSMul

instance instSmulCommClass [SMul R A] [SMul S A] [SMulCommClass R S A] :
    SMulCommClass R S (CStarMatrix m n A) :=
  Pi.smulCommClass

instance instIsScalarTower [SMul R S] [SMul R A] [SMul S A] [IsScalarTower R S A] :
    IsScalarTower R S (CStarMatrix m n A) :=
  Pi.isScalarTower

instance instIsCentralScalar [SMul R A] [SMul Rᵐᵒᵖ A] [IsCentralScalar R A] :
    IsCentralScalar R (CStarMatrix m n A) :=
  Pi.isCentralScalar

instance instMulAction [Monoid R] [MulAction R A] : MulAction R (CStarMatrix m n A) :=
  Pi.mulAction _

instance instDistribMulAction [Monoid R] [AddMonoid A] [DistribMulAction R A] :
    DistribMulAction R (CStarMatrix m n A) :=
  Pi.distribMulAction _

instance instModule [Semiring R] [AddCommMonoid A] [Module R A] : Module R (CStarMatrix m n A) :=
  Pi.module _ _ _

@[simp, nolint simpNF]
theorem zero_apply [Zero A] (i : m) (j : n) : (0 : CStarMatrix m n A) i j = 0 := rfl

@[simp] theorem add_apply [Add A] (M N : CStarMatrix m n A) (i : m) (j : n) :
    (M + N) i j = (M i j) + (N i j) := rfl

@[simp] theorem smul_apply [SMul B A] (r : B) (M : Matrix m n A) (i : m) (j : n) :
    (r • M) i j = r • (M i j) := rfl

@[simp] theorem sub_apply [Sub A] (M N : Matrix m n A) (i : m) (j : n) :
    (M - N) i j = (M i j) - (N i j) := rfl

@[simp] theorem neg_apply [Neg A] (M : Matrix m n A) (i : m) (j : n) :
    (-M) i j = -(M i j) := rfl

/-! simp-normal form pulls `of` to the outside. -/

@[simp] theorem of_zero [Zero A] : ofMatrix (0 : Matrix m n A) = 0 := rfl

@[simp] theorem of_add_of [Add A] (f g : Matrix m n A) :
    ofMatrix f + ofMatrix g = ofMatrix (f + g) := rfl

@[simp]
theorem of_sub_of [Sub A] (f g : Matrix m n A) : ofMatrix f - ofMatrix g = ofMatrix (f - g) :=
  rfl

@[simp] theorem neg_of [Neg A] (f : Matrix m n A) : -ofMatrix f = ofMatrix (-f) := rfl

@[simp] theorem smul_of [SMul R A] (r : R) (f : Matrix m n A) :
    r • ofMatrix f = ofMatrix (r • f) := rfl

instance instStarAddMonoid [AddMonoid A] [StarAddMonoid A] : StarAddMonoid (CStarMatrix n n A) where
  star_add := star_add (R := Matrix n n A)

instance instStarModule [Star R] [Star A] [SMul R A] [StarModule R A] :
    StarModule R (CStarMatrix n n A) where
  star_smul := star_smul (A := Matrix n n A)

/-- The equivalence to matrices, bundled as a linear equivalence. -/
def ofMatrixₗ [AddCommMonoid A] [Semiring R] [Module R A] :
    (Matrix m n A) ≃ₗ[R] CStarMatrix m n A := LinearEquiv.refl _ _

section zero_one

variable [Zero A] [One A] [DecidableEq n]

instance instOne : One (CStarMatrix n n A) := ⟨ofMatrix (1 : Matrix n n A)⟩

theorem one_apply {i j} : (1 : CStarMatrix n n A) i j = if i = j then 1 else 0 := rfl

@[simp]
theorem one_apply_eq (i) : (1 : CStarMatrix n n A) i i = 1 := Matrix.one_apply_eq _

@[simp] theorem one_apply_ne {i j} : i ≠ j → (1 : CStarMatrix n n A) i j = 0 := Matrix.one_apply_ne

theorem one_apply_ne' {i j} : j ≠ i → (1 : CStarMatrix n n A) i j = 0 := Matrix.one_apply_ne'

instance instAddMonoidWithOne [AddMonoidWithOne A] : AddMonoidWithOne (CStarMatrix n n A) where

instance instAddGroupWithOne [AddGroupWithOne A] : AddGroupWithOne (CStarMatrix n n A) where
  __ := instAddGroup
  __ := instAddMonoidWithOne

instance instAddCommMonoidWithOne [AddCommMonoidWithOne A] :
    AddCommMonoidWithOne (CStarMatrix n n A) where
  __ := instAddCommMonoid
  __ := instAddMonoidWithOne

instance instAddCommGroupWithOne [AddCommGroupWithOne A] :
    AddCommGroupWithOne (CStarMatrix n n A) where
  __ := instAddCommGroup
  __ := instAddGroupWithOne

@[default_instance 100]
instance {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] :
    HMul (CStarMatrix l m A) (CStarMatrix m n A) (CStarMatrix l n A) where
  hMul M N := ofMatrix (ofMatrix.symm M * ofMatrix.symm N)

instance [Fintype n] [Mul A] [AddCommMonoid A] : Mul (CStarMatrix n n A) where mul M N := M * N

end zero_one

theorem mul_apply {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
    {N : CStarMatrix m n A} {i k} : (M * N) i k = ∑ j, M i j * N j k := rfl

theorem mul_apply' {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
    {N : CStarMatrix m n A} {i k} : (M * N) i k = (fun j => M i j) ⬝ᵥ fun j => N j k := rfl

@[simp]
theorem smul_mul {l : Type*} [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A] [DistribMulAction R A]
    [IsScalarTower R A A] (a : R) (M : CStarMatrix m n A) (N : CStarMatrix n l A) :
    (a • M) * N = a • (M * N) := Matrix.smul_mul a M N

theorem mul_smul {l : Type*} [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A] [DistribMulAction R A]
    [SMulCommClass R A A] (M : Matrix m n A) (a : R) (N : Matrix n l A) :
    M * (a • N) = a • (M * N) := Matrix.mul_smul M a N

instance instNonUnitalNonAssocSemiring [Fintype n] [NonUnitalNonAssocSemiring A] :
    NonUnitalNonAssocSemiring (CStarMatrix n n A) where
  left_distrib := left_distrib (R := Matrix n n A)
  right_distrib := right_distrib (R := Matrix n n A)
  zero_mul := zero_mul (M₀ := Matrix n n A)
  mul_zero := mul_zero (M₀ := Matrix n n A)

instance instNonUnitalNonAssocRing [Fintype n] [NonUnitalNonAssocRing A] :
    NonUnitalNonAssocRing (CStarMatrix n n A) where
  left_distrib := left_distrib (R := Matrix n n A)
  right_distrib := right_distrib (R := Matrix n n A)
  zero_mul := zero_mul (M₀ := Matrix n n A)
  mul_zero := mul_zero (M₀ := Matrix n n A)

instance instNonUnitalSemiring [Fintype n] [NonUnitalSemiring A] :
    NonUnitalSemiring (CStarMatrix n n A) where
  mul_assoc := mul_assoc (G := Matrix n n A)

instance instNonAssocSemiring [Fintype n] [DecidableEq n] [NonAssocSemiring A] :
    NonAssocSemiring (CStarMatrix n n A) where
  one_mul := one_mul (M := Matrix n n A)
  mul_one := mul_one (M := Matrix n n A)

instance instNonUnitalRing [Fintype n] [NonUnitalRing A] :
    NonUnitalRing (CStarMatrix n n A) where
  mul_assoc := mul_assoc (G := Matrix n n A)

instance instNonAssocRing [Fintype n] [DecidableEq n] [NonAssocRing A] :
    NonAssocRing (CStarMatrix n n A) where
  one_mul := one_mul (M := Matrix n n A)
  mul_one := mul_one (M := Matrix n n A)

instance instSemiring [Fintype n] [DecidableEq n] [Semiring A] :
    Semiring (CStarMatrix n n A) where
  one_mul := one_mul (M := Matrix n n A)
  mul_one := mul_one (M := Matrix n n A)

instance instRing [Fintype n] [DecidableEq n] [Ring A] : Ring (CStarMatrix n n A) :=
  { instSemiring, instAddCommGroupWithOne with }

/-- `ofMatrix` bundled as a ring equivalence. -/
def ofMatrixRingEquiv [Fintype n] [Semiring A] :
    Matrix n n A ≃+* CStarMatrix n n A :=
  { ofMatrix with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

instance instStarRing [Fintype n] [NonUnitalSemiring A] [StarRing A] :
    StarRing (CStarMatrix n n A) where
  star_mul := star_mul (R := Matrix n n A)
  star_add := star_add (R := Matrix n n A)

instance instAlgebra [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] :
    Algebra R (CStarMatrix n n A) where
  toRingHom := ofMatrixRingEquiv.toRingHom.comp <| algebraMap R (Matrix n n A)
  commutes' r M := by
    apply ofMatrixRingEquiv.symm.injective
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      map_mul, RingEquiv.symm_apply_apply]
    exact Algebra.commutes (R := R) (A := Matrix n n A) _ _
  smul_def' r M := by
    apply ofMatrixRingEquiv.symm.injective
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      map_mul, RingEquiv.symm_apply_apply]
    exact Algebra.smul_def (R := R) (A := Matrix n n A) _ _

end basic

variable [Fintype m] [Fintype n] [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℂ A]
  [PartialOrder A] [CStarRing A] [StarOrderedRing A] [SMulCommClass ℂ A A] [StarModule ℂ A]
  [IsScalarTower ℂ A A] [CompleteSpace A]

/-- Interpret a `CStarMatrix m n A` as a continuous linear map acting on
`WithCStarModule (n → A)`. -/
def toCLM : CStarMatrix m n A →ₗ[ℂ] (C⋆ᵐᵒᵈ (n → A)) →L[ℂ] (C⋆ᵐᵒᵈ (m → A)) where
  toFun M := { toFun := (WithCStarModule.equivL ℂ).symm ∘ M.mulVec ∘ WithCStarModule.equivL ℂ
               map_add' := M.mulVec_add
               map_smul' := M.mulVec_smul
               cont := by
                 simp only [LinearMap.coe_mk, AddHom.coe_mk]
                 exact Continuous.comp (by fun_prop) (by fun_prop) }
  map_add' M₁ M₂ := by
    ext
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      WithCStarModule.equivL_apply, WithCStarModule.equivL_symm_apply,
      WithCStarModule.equiv_symm_pi_apply, ContinuousLinearMap.add_apply, WithCStarModule.add_apply]
    rw [Matrix.add_mulVec, Pi.add_apply]
  map_smul' c M := by
    ext x i
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      WithCStarModule.equivL_apply, WithCStarModule.equivL_symm_apply,
      WithCStarModule.equiv_symm_pi_apply, Matrix.mulVec, Matrix.dotProduct,
      WithCStarModule.equiv_pi_apply, RingHom.id_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, WithCStarModule.smul_apply, Finset.smul_sum]
    congr
    ext j
    rw [CStarMatrix.smul_apply, smul_mul_assoc]

lemma toCLM_apply {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ (n → A)} :
    toCLM M v = (WithCStarModule.equiv _).symm (M.mulVec v) := rfl

lemma toCLM_apply_eq_sum {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ (n → A)} :
    toCLM M v = (WithCStarModule.equiv _).symm (fun i => ∑ j, M i j * v j) := by
  ext i
  simp [toCLM_apply, Matrix.mulVec, Matrix.dotProduct]

/-- Interpret a `CStarMatrix m n A` as a continuous linear map acting on `n →C⋆ A`. This
version is specialized to the case `m = n` and is bundled as a non-unital algebra homomorphism. -/
def toCLMNonUnitalAlgHom : CStarMatrix n n A →ₙₐ[ℂ] (C⋆ᵐᵒᵈ (n → A)) →L[ℂ] (C⋆ᵐᵒᵈ (n → A)) :=
  { toCLM (n := n) (m := n) with
    map_zero' := by ext1; simp
    map_mul' := by intros; ext; simp [toCLM] }

lemma toCLMNonUnitalAlgHom_eq_toCLM {M : CStarMatrix n n A} :
    toCLMNonUnitalAlgHom (A := A) M = toCLM M := rfl

open WithCStarModule in
@[simp high]
lemma toCLM_apply_single [DecidableEq n] {M : CStarMatrix m n A} {j : n} (a : A) :
    (toCLM M) (equiv _ |>.symm <| Pi.single j a) = (equiv _).symm (fun i => M i j * a) := by
  simp [toCLM]

open WithCStarModule in
lemma toCLM_apply_single_apply [DecidableEq n] {M : CStarMatrix m n A} {i : m} {j : n} (a : A) :
    (toCLM M) (equiv _ |>.symm <| Pi.single j a) i = M i j * a := by simp

open WithCStarModule in
lemma mul_entry_mul_eq_inner_toCLM [DecidableEq m] [DecidableEq n] {M : CStarMatrix m n A}
    {i : m} {j : n} (a b : A) :
    star a * M i j * b
      = ⟪equiv _ |>.symm (Pi.single i a), toCLM M (equiv _ |>.symm <| Pi.single j b)⟫_A := by
  simp [mul_assoc, inner_def]

lemma toCLM_injective [DecidableEq n] : Function.Injective (toCLM (A := A) (m := m) (n := n)) := by
  rw [injective_iff_map_eq_zero]
  intro M h
  ext i j
  rw [Matrix.zero_apply, ← norm_eq_zero, ← sq_eq_zero_iff, sq, ← CStarRing.norm_self_mul_star,
    ← toCLM_apply_single_apply]
  simp [h]

open WithCStarModule in
lemma toCLM_inner_right_eq_left {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ (m → A)}
    {w : C⋆ᵐᵒᵈ (n → A)} : ⟪v, toCLM M w⟫_A = ⟪toCLM Mᴴ v, w⟫_A := by
  simp only [toCLM_apply_eq_sum, pi_inner, equiv_symm_pi_apply, inner_def, Finset.mul_sum,
    Matrix.conjTranspose_apply, star_sum, star_mul, star_star, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc]

lemma toCLM_inner_conjTranspose_right_eq_left {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ (n → A)}
    {w : C⋆ᵐᵒᵈ (m → A)} : ⟪v, toCLM Mᴴ w⟫_A = ⟪toCLM M v, w⟫_A := by
  simpa using toCLM_inner_right_eq_left (M := Mᴴ) (v := v) (w := w)

/-- The operator norm on `CStarMatrix m n A`. -/
noncomputable instance instNorm : Norm (CStarMatrix m n A) where
  norm M := ‖toCLM M‖

lemma norm_def {M : CStarMatrix m n A} : ‖M‖ = ‖toCLM M‖ := rfl

lemma norm_def' {M : CStarMatrix n n A} : ‖M‖ = ‖toCLMNonUnitalAlgHom (A := A) M‖ := rfl

lemma normedSpaceCore [DecidableEq n]: NormedSpace.Core ℂ (CStarMatrix m n A) where
  norm_nonneg M := (toCLM M).opNorm_nonneg
  norm_smul c M := by rw [norm_def, norm_def, map_smul, norm_smul _ (toCLM M)]
  norm_triangle M₁ M₂ := by simpa [← map_add] using norm_add_le (toCLM M₁) (toCLM M₂)
  norm_eq_zero_iff := by
    simpa only [norm_def, norm_eq_zero, ← injective_iff_map_eq_zero'] using toCLM_injective

open WithCStarModule in
lemma norm_entry_le_norm [DecidableEq n] {M : CStarMatrix m n A} {i : m} {j : n} :
    ‖M i j‖ ≤ ‖M‖ := by
  suffices ‖M i j‖ * ‖M i j‖ ≤ ‖M‖ * ‖M i j‖ by
    obtain (h | h) := eq_zero_or_norm_pos (M i j)
    · simp [h, norm_def]
    · exact le_of_mul_le_mul_right this h
  rw [← CStarRing.norm_self_mul_star, ← toCLM_apply_single_apply]
  apply norm_apply_le_norm _ _ |>.trans
  apply (toCLM M).le_opNorm _ |>.trans
  simp [norm_def]

open CStarModule in
lemma norm_le_of_forall_inner_le {M : CStarMatrix m n A} {C : ℝ≥0}
    (h : ∀ v w, ‖⟪w, toCLM M v⟫_A‖ ≤ C * ‖v‖ * ‖w‖) : ‖M‖ ≤ C := by
  refine (toCLM M).opNorm_le_bound (by simp) fun v ↦ ?_
  obtain (h₀ | h₀) := (norm_nonneg (toCLM M v)).eq_or_lt
  · rw [← h₀]
    positivity
  · refine le_of_mul_le_mul_right ?_ h₀
    simpa [← sq, norm_sq_eq] using h ..

end CStarMatrix

section TopologyAux
/-
## Replacing the uniformity and bornology

Note that while the norm that we have defined on `CStarMatrix m n A` induces the product uniformity,
it is not defeq to `Pi.uniformSpace`. In this section, we show that the norm indeed does induce
the product topology and use this fact to properly set up the
`NormedAddCommGroup (CStarMatrix m n A)` instance such that the uniformity is still
`Pi.uniformSpace` and the bornology is `Pi.instBornology`.

To do this, we locally register a `NormedAddCommGroup` instance on `CStarMatrix` which registers
the "bad" topology, and we also locally use the matrix norm `Matrix.normedAddCommGroup`
(which takes the norm of the biggest entry as the norm of the matrix)
in order to show that the map `ofMatrix` is bilipschitz. We then finally register the
`NormedAddCommGroup (n →C⋆ A)` instance via `NormedAddCommGroup.ofCoreReplaceAll`.
-/

namespace CStarMatrix

variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq n]
  [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [PartialOrder A] [CompleteSpace A]
  [StarOrderedRing A] [NormedSpace ℂ A] [StarModule ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A]

private noncomputable def normedAddCommGroupAux : NormedAddCommGroup (CStarMatrix m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

attribute [local instance] normedAddCommGroupAux

private def normedSpaceAux : NormedSpace ℂ (CStarMatrix m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

/- In this `Aux` section, we locally activate the following instances: a norm on `CStarMatrix`
 which induces a topology that is not defeq with the matrix one, and the elementwise norm on
 matrices, in order to show that the two topologies are in fact equal -/
attribute [local instance] normedSpaceAux Matrix.normedAddCommGroup Matrix.normedSpace

private lemma nnnorm_le_of_forall_inner_le {M : CStarMatrix m n A} {C : ℝ≥0}
    (h : ∀ v w, ‖⟪w, CStarMatrix.toCLM M v⟫_A‖₊ ≤ C * ‖v‖₊ * ‖w‖₊) : ‖M‖₊ ≤ C :=
  CStarMatrix.norm_le_of_forall_inner_le fun v w => h v w

open Finset in
private lemma lipschitzWith_toMatrixAux [DecidableEq m] :
    LipschitzWith 1 (ofMatrixₗ.symm (R := ℂ) : CStarMatrix m n A → Matrix m n A) := by
  refine AddMonoidHomClass.lipschitz_of_bound_nnnorm _ _ fun M => ?_
  rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Matrix.norm_le_iff (norm_nonneg _)]
  exact fun _ _ ↦ CStarMatrix.norm_entry_le_norm

open CStarMatrix WithCStarModule in
private lemma antilipschitzWith_toMatrixAux :
    AntilipschitzWith (Fintype.card m * Fintype.card n)
      (ofMatrixₗ.symm (R := ℂ) : CStarMatrix m n A → Matrix m n A) := by
  refine AddMonoidHomClass.antilipschitz_of_bound _ fun M => ?_
  calc
    ‖M‖ ≤ ∑ i, ∑ j, ‖M i j‖ := by
      rw [norm_def]
      refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
      simp only [toCLM_apply_eq_sum, equiv_symm_pi_apply, Finset.sum_mul]
      apply pi_norm_le_sum_norm _ |>.trans
      gcongr with i _
      apply norm_sum_le _ _ |>.trans
      gcongr with j _
      apply norm_mul_le _ _ |>.trans
      gcongr
      exact norm_apply_le_norm v j
    _ ≤ ∑ _ : m, ∑ _ : n, ‖ofMatrixₗ.symm (R := ℂ) M‖ := by
      gcongr with i _ j _
      exact ofMatrixₗ.symm (R := ℂ) M |>.norm_entry_le_entrywise_sup_norm
    _ = _ := by simp [mul_assoc]

private lemma uniformInducing_toMatrixAux [DecidableEq m] :
    UniformInducing (ofMatrix.symm : CStarMatrix m n A → Matrix m n A) :=
  AntilipschitzWith.uniformInducing antilipschitzWith_toMatrixAux
    lipschitzWith_toMatrixAux.uniformContinuous

private lemma uniformity_eq_aux [DecidableEq m] :
    𝓤 (CStarMatrix m n A) = (𝓤[Pi.uniformSpace _] :
      Filter (CStarMatrix m n A × CStarMatrix m n A)) := by
  have :
    (fun x : CStarMatrix m n A × CStarMatrix m n A => ⟨ofMatrix.symm x.1, ofMatrix.symm x.2⟩)
      = id := by
    ext i <;> rfl
  rw [← uniformInducing_toMatrixAux.comap_uniformity, this, Filter.comap_id]
  rfl

open Bornology in
private lemma cobounded_eq_aux [DecidableEq m] :
    cobounded (CStarMatrix m n A) = @cobounded _ Pi.instBornology := by
  have : cobounded (CStarMatrix m n A) = Filter.comap ofMatrix.symm (cobounded _) := by
    refine le_antisymm ?_ ?_
    · exact antilipschitzWith_toMatrixAux.tendsto_cobounded.le_comap
    · exact lipschitzWith_toMatrixAux.comap_cobounded_le
  exact this.trans Filter.comap_id

end CStarMatrix

end TopologyAux

namespace CStarMatrix

section non_unital

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [PartialOrder A]
  [CompleteSpace A] [StarOrderedRing A] [NormedSpace ℂ A]
  [StarModule ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

instance instTopologicalSpace : TopologicalSpace (CStarMatrix m n A) := Pi.topologicalSpace
instance instUniformSpace : UniformSpace (CStarMatrix m n A) := Pi.uniformSpace _
instance instBornology : Bornology (CStarMatrix m n A) := Pi.instBornology
instance instCompleteSpace : CompleteSpace (CStarMatrix m n A) := Pi.complete _
instance instT2Space : T2Space (CStarMatrix m n A) := Pi.t2Space
instance instT3Space : T3Space (CStarMatrix m n A) := _root_.instT3Space

instance instTopologicalAddGroup : TopologicalAddGroup (CStarMatrix m n A) :=
  Pi.topologicalAddGroup

instance instUniformAddGroup : UniformAddGroup (CStarMatrix m n A) :=
  Pi.instUniformAddGroup

instance instContinuousSMul {R : Type*} [SMul R A] [TopologicalSpace R] [ContinuousSMul R A] :
    ContinuousSMul R (CStarMatrix m n A) := instContinuousSMulForall

noncomputable instance instNormedAddCommGroup [DecidableEq n] :
    NormedAddCommGroup (CStarMatrix m n A) :=
  .ofCoreReplaceAll CStarMatrix.normedSpaceCore
    CStarMatrix.uniformity_eq_aux.symm
      fun _ => Filter.ext_iff.1 CStarMatrix.cobounded_eq_aux.symm _

instance instNormedSpace [DecidableEq n] : NormedSpace ℂ (CStarMatrix m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

noncomputable instance instNonUnitalNormedRing [DecidableEq n] :
    NonUnitalNormedRing (CStarMatrix n n A) where
  dist_eq _ _ := rfl
  norm_mul _ _ := by simpa only [norm_def', map_mul] using norm_mul_le _ _

open ContinuousLinearMap CStarModule in
/-- Matrices with entries in a C⋆-algebra form a C⋆-algebra. -/
instance instCStarRing [DecidableEq n] : CStarRing (CStarMatrix n n A) where
  norm_mul_self_le M := by
    have hmain : ‖M‖ ≤ √‖star M * M‖ := by
      change ‖toCLM M‖ ≤ √‖star M * M‖
      rw [opNorm_le_iff (by positivity)]
      intro v
      rw [norm_eq_sqrt_norm_inner_self, ← toCLM_inner_conjTranspose_right_eq_left]
      have h₁ : ‖⟪v, (toCLM Mᴴ) ((toCLM M) v)⟫_A‖ ≤ ‖star M * M‖ * ‖v‖ ^ 2 := calc
          _ ≤ ‖v‖ * ‖(toCLM Mᴴ) (toCLM M v)‖ := norm_inner_le (C⋆ᵐᵒᵈ (n → A))
          _ ≤ ‖v‖ * ‖(toCLM Mᴴ).comp (toCLM M)‖ * ‖v‖ := by
                    rw [mul_assoc]
                    gcongr
                    rw [← ContinuousLinearMap.comp_apply]
                    exact le_opNorm ((toCLM Mᴴ).comp (toCLM M)) v
          _ = ‖(toCLM Mᴴ).comp (toCLM M)‖ * ‖v‖ ^ 2 := by ring
          _ = ‖star M * M‖ * ‖v‖ ^ 2 := by
                    congr
                    simp only [← toCLMNonUnitalAlgHom_eq_toCLM, Matrix.star_eq_conjTranspose,
                      map_mul]
                    rfl
      have h₂ : ‖v‖ = √(‖v‖ ^ 2) := by simp
      rw [h₂, ← Real.sqrt_mul]
      gcongr
      positivity
    rw [← pow_two, ← Real.sqrt_le_sqrt_iff (by positivity)]
    simp [hmain]

end non_unital

section unital

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [PartialOrder A]
  [CompleteSpace A] [StarOrderedRing A] [NormedAlgebra ℂ A] [StarModule ℂ A]

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable instance instNormedRing : NormedRing (CStarMatrix n n A) where
  dist_eq _ _ := rfl
  norm_mul := norm_mul_le

noncomputable instance instNormedAlgebra : NormedAlgebra ℂ (CStarMatrix n n A) where
  norm_smul_le r M := by simpa only [norm_def, map_smul] using (toCLM M).opNorm_smul_le r

-- TODO: make this non-unital
instance instPartialOrder : PartialOrder (CStarMatrix n n A) := CStarAlgebra.spectralOrder _
instance instStarOrderedRing : StarOrderedRing (CStarMatrix n n A) :=
  CStarAlgebra.spectralOrderedRing _

end unital

section

variable {m n A : Type*}

lemma uniformEmbedding_ofMatrix [NonUnitalNormedRing A] :
    UniformEmbedding (ofMatrix : Matrix m n A → CStarMatrix m n A) where
  comap_uniformity := Filter.comap_id'
  inj := fun ⦃_ _⦄ a ↦ a

/-- `ofMatrix` bundled as a continuous linear map. -/
def ofMatrixL [NonUnitalNormedRing A] [Module ℂ A] : Matrix m n A ≃L[ℂ] CStarMatrix m n A :=
  { ofMatrixₗ with
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }

lemma ofMatrix_eq_ofMatrixL [NonUnitalNormedRing A] [Module ℂ A] :
    (ofMatrix : Matrix m n A → CStarMatrix m n A)
      = (ofMatrixL : Matrix m n A → CStarMatrix m n A) := rfl

/-- `ofMatrix` bundled as a star algebra equivalence. -/
def ofMatrixStarAlgEquiv [Fintype n] [Star A] [Semiring A] [Module ℂ A] :
    Matrix n n A ≃⋆ₐ[ℂ] CStarMatrix n n A :=
  { ofMatrixRingEquiv with
    map_star' := fun _ => rfl
    map_smul' := fun _ _ => rfl }

lemma ofMatrix_eq_ofMatrixStarAlgEquiv [Fintype n] [Star A] [Semiring A] [Module ℂ A] :
    (ofMatrix : Matrix n n A → CStarMatrix n n A)
      = (ofMatrixStarAlgEquiv : Matrix n n A → CStarMatrix n n A) := rfl

end

end CStarMatrix
