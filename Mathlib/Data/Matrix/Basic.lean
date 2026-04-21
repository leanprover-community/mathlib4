/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.RingEquiv
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.GroupTheory.DedekindFinite

/-!
# Matrices

This file contains basic results on matrices including bundled versions of matrix operators.

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `fun i j ↦ _` or even `(fun i j ↦ _ : Matrix m n α)`, as these are not recognized by Lean
as having the right type. Instead, `Matrix.of` should be used.

## TODO

Under various conditions, multiplication of infinite matrices makes sense.
These have not yet been implemented.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

assert_not_exists TrivialStar

universe u u' v w

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}
variable {R S T A α β γ : Type*}

namespace Matrix

instance decidableEq [DecidableEq α] [Fintype m] [Fintype n] : DecidableEq (Matrix m n α) :=
  Fintype.decidablePiFintype

instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (α) [Fintype α] :
    Fintype (Matrix m n α) := inferInstanceAs (Fintype (m → n → α))

instance {n m} [Finite m] [Finite n] (α) [Finite α] :
    Finite (Matrix m n α) := inferInstanceAs (Finite (m → n → α))

instance (priority := low) [Semiring α] [Finite α] : IsStablyFiniteRing α := ⟨inferInstance⟩

section
variable (R)

/-- This is `Matrix.of` bundled as a linear equivalence. -/
def ofLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] : (m → n → α) ≃ₗ[R] Matrix m n α where
  __ := ofAddEquiv
  map_smul' _ _ := rfl

@[simp] lemma coe_ofLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] :
    ⇑(ofLinearEquiv _ : (m → n → α) ≃ₗ[R] Matrix m n α) = of := rfl
@[simp] lemma coe_ofLinearEquiv_symm [Semiring R] [AddCommMonoid α] [Module R α] :
    ⇑((ofLinearEquiv _).symm : Matrix m n α ≃ₗ[R] (m → n → α)) = of.symm := rfl

end

theorem sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finset β) (g : β → Matrix m n α) :
    (∑ c ∈ s, g c) i j = ∑ c ∈ s, g c i j :=
  (congr_fun (s.sum_apply i g) j).trans (s.sum_apply j _)

end Matrix

open Matrix

namespace Matrix

section Diagonal

variable [DecidableEq n]

variable (n α)

/-- `Matrix.diagonal` as an `AddMonoidHom`. -/
@[simps]
def diagonalAddMonoidHom [AddZeroClass α] : (n → α) →+ Matrix n n α where
  toFun := diagonal
  map_zero' := diagonal_zero
  map_add' x y := (diagonal_add x y).symm

variable (R)

/-- `Matrix.diagonal` as a `LinearMap`. -/
@[simps]
def diagonalLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : (n → α) →ₗ[R] Matrix n n α :=
  { diagonalAddMonoidHom n α with map_smul' := diagonal_smul }

variable {n α R}

section One

variable [Zero α] [One α]

lemma zero_le_one_elem [Preorder α] [ZeroLEOneClass α] (i j : n) :
    0 ≤ (1 : Matrix n n α) i j := by
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]

lemma zero_le_one_row [Preorder α] [ZeroLEOneClass α] (i : n) :
    0 ≤ (1 : Matrix n n α) i :=
  zero_le_one_elem i

end One

end Diagonal

section Diag

variable (n α)

/-- `Matrix.diag` as an `AddMonoidHom`. -/
@[simps]
def diagAddMonoidHom [AddZeroClass α] : Matrix n n α →+ n → α where
  toFun := diag
  map_zero' := diag_zero
  map_add' := diag_add

variable (R)

/-- `Matrix.diag` as a `LinearMap`. -/
@[simps]
def diagLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : Matrix n n α →ₗ[R] n → α :=
  { diagAddMonoidHom n α with map_smul' := diag_smul }

variable {n α R}

@[simp]
theorem diag_list_sum [AddMonoid α] (l : List (Matrix n n α)) : diag l.sum = (l.map diag).sum :=
  map_list_sum (diagAddMonoidHom n α) l

@[simp]
theorem diag_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix n n α)) :
    diag s.sum = (s.map diag).sum :=
  map_multiset_sum (diagAddMonoidHom n α) s

@[simp]
theorem diag_sum {ι} [AddCommMonoid α] (s : Finset ι) (f : ι → Matrix n n α) :
    diag (∑ i ∈ s, f i) = ∑ i ∈ s, diag (f i) :=
  map_sum (diagAddMonoidHom n α) f s

end Diag

open Matrix

section NonAssocSemiring

variable [NonAssocSemiring α]

variable (α n)

/-- `Matrix.diagonal` as a `RingHom`. -/
@[simps]
def diagonalRingHom [Fintype n] [DecidableEq n] : (n → α) →+* Matrix n n α :=
  { diagonalAddMonoidHom n α with
    toFun := diagonal
    map_one' := diagonal_one
    map_mul' := fun _ _ => (diagonal_mul_diagonal' _ _).symm }

end NonAssocSemiring

section Semiring

variable [Semiring α]

theorem diagonal_pow [Fintype n] [DecidableEq n] (v : n → α) (k : ℕ) :
    diagonal v ^ k = diagonal (v ^ k) :=
  (map_pow (diagonalRingHom n α) v k).symm

/-- The ring homomorphism `α →+* Matrix n n α`
sending `a` to the diagonal matrix with `a` on the diagonal.
-/
def scalar (n : Type u) [DecidableEq n] [Fintype n] : α →+* Matrix n n α :=
  (diagonalRingHom n α).comp <| Pi.constRingHom n α

section Scalar

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

@[simp]
theorem scalar_apply (a : α) : scalar n a = diagonal fun _ => a :=
  rfl

theorem scalar_inj [Nonempty n] {r s : α} : scalar n r = scalar n s ↔ r = s :=
  (diagonal_injective.comp Function.const_injective).eq_iff

/-- A version of `Matrix.scalar_commute_iff` for rectangular matrices. -/
theorem scalar_comm_iff {r : α} {M : Matrix m n α} :
    scalar m r * M = M * scalar n r ↔ r • M = MulOpposite.op r • M := by
  simp_rw [scalar_apply, ← smul_eq_diagonal_mul, ← op_smul_eq_mul_diagonal]

theorem scalar_commute_iff {r : α} {M : Matrix n n α} :
    Commute (scalar n r) M ↔ r • M = MulOpposite.op r • M :=
  scalar_comm_iff

/-- A version of `Matrix.scalar_commute` for rectangular matrices. -/
theorem scalar_comm (r : α) (hr : ∀ r', Commute r r') (M : Matrix m n α) :
    scalar m r * M = M * scalar n r :=
  scalar_comm_iff.2 <| ext fun _ _ => hr _

theorem scalar_commute (r : α) (hr : ∀ r', Commute r r') (M : Matrix n n α) :
    Commute (scalar n r) M := scalar_comm r hr M

end Scalar

end Semiring

section Algebra

variable [Fintype n] [DecidableEq n]
variable [CommSemiring R] [Semiring α] [Semiring β] [Algebra R α] [Algebra R β]

instance instAlgebra : Algebra R (Matrix n n α) where
  algebraMap := (Matrix.scalar n).comp (algebraMap R α)
  commutes' _ _ := scalar_commute _ (fun _ => Algebra.commutes _ _) _
  smul_def' r x := by ext; simp [Matrix.scalar, Algebra.smul_def r]

theorem algebraMap_matrix_apply {r : R} {i j : n} :
    algebraMap R (Matrix n n α) r i j = if i = j then algebraMap R α r else 0 := rfl

theorem algebraMap_eq_diagonal (r : R) :
    algebraMap R (Matrix n n α) r = diagonal (algebraMap R (n → α) r) := rfl

theorem algebraMap_eq_diagonalRingHom :
    algebraMap R (Matrix n n α) = (diagonalRingHom n α).comp (algebraMap R _) := rfl

@[simp]
theorem map_algebraMap (r : R) (f : α → β) (hf : f 0 = 0)
    (hf₂ : f (algebraMap R α r) = algebraMap R β r) :
    (algebraMap R (Matrix n n α) r).map f = algebraMap R (Matrix n n β) r := by
  rw [algebraMap_eq_diagonal, algebraMap_eq_diagonal, diagonal_map hf]
  simp [hf₂]

variable (R)

/-- `Matrix.diagonal` as an `AlgHom`. -/
@[simps]
def diagonalAlgHom : (n → α) →ₐ[R] Matrix n n α :=
  { diagonalRingHom n α with
    toFun := diagonal
    commutes' := fun r => (algebraMap_eq_diagonal r).symm }

variable (n)

/-- `Matrix.scalar` as an `AlgHom`. -/
def scalarAlgHom : α →ₐ[R] Matrix n n α where
  toRingHom := scalar n
  commutes' _ := rfl

@[simp] theorem scalarAlgHom_apply (a : α) : scalarAlgHom n R a = scalar n a := rfl

end Algebra

section AddHom

variable [Add α]

variable (R α) in
/-- Extracting entries from a matrix as an additive homomorphism. -/
@[simps]
def entryAddHom (i : m) (j : n) : AddHom (Matrix m n α) α where
  toFun M := M i j
  map_add' _ _ := rfl

-- It is necessary to spell out the name of the coercion explicitly on the RHS
-- for unification to succeed
lemma entryAddHom_eq_comp {i : m} {j : n} :
    entryAddHom α i j =
      ((Pi.evalAddHom (fun _ => α) j).comp (Pi.evalAddHom _ i)).comp
        (AddHomClass.toAddHom ofAddEquiv.symm) :=
  rfl

end AddHom

section AddMonoidHom

variable [AddZeroClass α]

variable (R α) in
/--
Extracting entries from a matrix as an additive monoid homomorphism. Note this cannot be upgraded to
a ring homomorphism, as it does not respect multiplication.
-/
@[simps]
def entryAddMonoidHom (i : m) (j : n) : Matrix m n α →+ α where
  toFun M := M i j
  map_add' _ _ := rfl
  map_zero' := rfl

-- It is necessary to spell out the name of the coercion explicitly on the RHS
-- for unification to succeed
lemma entryAddMonoidHom_eq_comp {i : m} {j : n} :
    entryAddMonoidHom α i j =
      ((Pi.evalAddMonoidHom (fun _ => α) j).comp (Pi.evalAddMonoidHom _ i)).comp
        (AddMonoidHomClass.toAddMonoidHom ofAddEquiv.symm) := by
  rfl

@[simp] lemma evalAddMonoidHom_comp_diagAddMonoidHom (i : m) :
    (Pi.evalAddMonoidHom _ i).comp (diagAddMonoidHom m α) = entryAddMonoidHom α i i := by
  simp [AddMonoidHom.ext_iff]

@[simp] lemma entryAddMonoidHom_toAddHom {i : m} {j : n} :
    (entryAddMonoidHom α i j : AddHom _ _) = entryAddHom α i j := rfl

end AddMonoidHom

section LinearMap

variable [Semiring R] [AddCommMonoid α] [Module R α]

variable (R α) in
/--
Extracting entries from a matrix as a linear map. Note this cannot be upgraded to an algebra
homomorphism, as it does not respect multiplication.
-/
@[simps]
def entryLinearMap (i : m) (j : n) :
    Matrix m n α →ₗ[R] α where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- It is necessary to spell out the name of the coercion explicitly on the RHS
-- for unification to succeed
lemma entryLinearMap_eq_comp {i : m} {j : n} :
    entryLinearMap R α i j =
      LinearMap.proj j ∘ₗ LinearMap.proj i ∘ₗ (ofLinearEquiv R).symm.toLinearMap := by
  rfl

@[simp] lemma proj_comp_diagLinearMap (i : m) :
    LinearMap.proj i ∘ₗ diagLinearMap m R α = entryLinearMap R α i i := by
  simp [LinearMap.ext_iff]

@[simp] lemma entryLinearMap_toAddMonoidHom {i : m} {j : n} :
    (entryLinearMap R α i j : _ →+ _) = entryAddMonoidHom α i j := rfl

@[simp] lemma entryLinearMap_toAddHom {i : m} {j : n} :
    (entryLinearMap R α i j : AddHom _ _) = entryAddHom α i j := rfl

end LinearMap

end Matrix

/-!
### Bundled versions of `Matrix.map`
-/


namespace Equiv

/-- The `Equiv` between spaces of matrices induced by an `Equiv` between their
coefficients. This is `Matrix.map` as an `Equiv`. -/
@[simps apply]
def mapMatrix (f : α ≃ β) : Matrix m n α ≃ Matrix m n β where
  toFun M := M.map f
  invFun M := M.map f.symm
  left_inv _ := Matrix.ext fun _ _ => f.symm_apply_apply _
  right_inv _ := Matrix.ext fun _ _ => f.apply_symm_apply _

@[simp]
theorem mapMatrix_refl : (Equiv.refl α).mapMatrix = Equiv.refl (Matrix m n α) :=
  rfl

@[simp]
theorem mapMatrix_symm (f : α ≃ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ _) :=
  rfl

@[simp]
theorem mapMatrix_trans (f : α ≃ β) (g : β ≃ γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ _) :=
  rfl

end Equiv

namespace AddMonoidHom

section AddZeroClass
variable [AddZeroClass α] [AddZeroClass β] [AddZeroClass γ]

/-- The `AddMonoidHom` between spaces of matrices induced by an `AddMonoidHom` between their
coefficients. This is `Matrix.map` as an `AddMonoidHom`. -/
@[simps]
def mapMatrix (f : α →+ β) : Matrix m n α →+ Matrix m n β where
  toFun M := M.map f
  map_zero' := Matrix.map_zero f f.map_zero
  map_add' := Matrix.map_add f f.map_add

@[simp]
theorem mapMatrix_id : (AddMonoidHom.id α).mapMatrix = AddMonoidHom.id (Matrix m n α) :=
  rfl

@[simp]
theorem mapMatrix_comp (f : β →+ γ) (g : α →+ β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α →+ _) :=
  rfl

@[simp] lemma entryAddMonoidHom_comp_mapMatrix (f : α →+ β) (i : m) (j : n) :
    (entryAddMonoidHom β i j).comp f.mapMatrix = f.comp (entryAddMonoidHom α i j) := rfl

@[simp]
theorem mapMatrix_zero : (0 : α →+ β).mapMatrix = (0 : Matrix m n α →+ _) := rfl

end AddZeroClass

@[simp]
theorem mapMatrix_add [AddZeroClass α] [AddCommMonoid β] (f g : α →+ β) :
    (f + g).mapMatrix = (f.mapMatrix + g.mapMatrix : Matrix m n α →+ _) := rfl

@[simp]
theorem mapMatrix_sub [AddZeroClass α] [AddCommGroup β] (f g : α →+ β) :
    (f - g).mapMatrix = (f.mapMatrix - g.mapMatrix : Matrix m n α →+ _) := rfl

@[simp]
theorem mapMatrix_neg [AddZeroClass α] [AddCommGroup β] (f : α →+ β) :
    (-f).mapMatrix = (-f.mapMatrix : Matrix m n α →+ _) := rfl

@[simp]
theorem mapMatrix_smul [Monoid A] [AddZeroClass α] [AddMonoid β] [DistribMulAction A β]
    (a : A) (f : α →+ β) :
    (a • f).mapMatrix = (a • f.mapMatrix : Matrix m n α →+ _) := rfl

end AddMonoidHom

namespace AddEquiv

variable [Add α] [Add β] [Add γ]

/-- The `AddEquiv` between spaces of matrices induced by an `AddEquiv` between their
coefficients. This is `Matrix.map` as an `AddEquiv`. -/
@[simps apply]
def mapMatrix (f : α ≃+ β) : Matrix m n α ≃+ Matrix m n β :=
  { f.toEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm
    map_add' := Matrix.map_add f (map_add f) }

@[simp]
theorem mapMatrix_refl : (AddEquiv.refl α).mapMatrix = AddEquiv.refl (Matrix m n α) :=
  rfl

@[simp]
theorem mapMatrix_symm (f : α ≃+ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃+ _) :=
  rfl

@[simp]
theorem mapMatrix_trans (f : α ≃+ β) (g : β ≃+ γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃+ _) :=
  rfl

@[simp] lemma entryAddHom_comp_mapMatrix (f : α ≃+ β) (i : m) (j : n) :
    (entryAddHom β i j).comp (AddHomClass.toAddHom f.mapMatrix) =
      (f : AddHom α β).comp (entryAddHom _ i j) := rfl

end AddEquiv

namespace LinearMap

variable [Semiring R] [Semiring S] [Semiring T]
variable {σᵣₛ : R →+* S} {σₛₜ : S →+* T} {σᵣₜ : R →+* T} [RingHomCompTriple σᵣₛ σₛₜ σᵣₜ]

section AddCommMonoid
variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
variable [Module R α] [Module S β] [Module T γ]

/-- The `LinearMap` between spaces of matrices induced by a `LinearMap` between their
coefficients. This is `Matrix.map` as a `LinearMap`. -/
@[simps]
def mapMatrix (f : α →ₛₗ[σᵣₛ] β) : Matrix m n α →ₛₗ[σᵣₛ] Matrix m n β where
  toFun M := M.map f
  map_add' := Matrix.map_add f f.map_add
  map_smul' r := Matrix.map_smulₛₗ f _ r (f.map_smulₛₗ r)

@[simp]
theorem mapMatrix_id : LinearMap.id.mapMatrix = (LinearMap.id : Matrix m n α →ₗ[R] _) :=
  rfl

@[simp]
theorem mapMatrix_comp (f : β →ₛₗ[σₛₜ] γ) (g : α →ₛₗ[σᵣₛ] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α →ₛₗ[_] _) :=
  rfl

@[simp] lemma entryLinearMap_comp_mapMatrix (f : α →ₛₗ[σᵣₛ] β) (i : m) (j : n) :
    (entryLinearMap S _ i j).comp f.mapMatrix = f.comp (entryLinearMap R _ i j) := rfl

@[simp]
theorem mapMatrix_zero : (0 : α →ₛₗ[σᵣₛ] β).mapMatrix = (0 : Matrix m n α →ₛₗ[_] _) := rfl

@[simp]
theorem mapMatrix_add (f g : α →ₛₗ[σᵣₛ] β) :
    (f + g).mapMatrix = (f.mapMatrix + g.mapMatrix : Matrix m n α →ₛₗ[_] _) := rfl

@[simp]
theorem mapMatrix_smul [Monoid A] [DistribMulAction A β] [SMulCommClass S A β]
    (a : A) (f : α →ₛₗ[σᵣₛ] β) :
    (a • f).mapMatrix = (a • f.mapMatrix : Matrix m n α →ₛₗ[_] _) := rfl

variable (A) in
/-- `LinearMap.mapMatrix` is itself linear in the map being applied.

Alternative, this is `Matrix.map` as a bilinear map. -/
@[simps]
def mapMatrixLinear [Semiring A] [Module A β] [SMulCommClass S A β] :
    (α →ₛₗ[σᵣₛ] β) →ₗ[A] (Matrix m n α →ₛₗ[σᵣₛ] Matrix m n β) where
  toFun := mapMatrix
  map_add' := mapMatrix_add
  map_smul' := mapMatrix_smul

end AddCommMonoid

section
variable [AddCommMonoid α] [AddCommGroup β]
variable [Module R α] [Module S β]

@[simp]
theorem mapMatrix_sub (f g : α →ₛₗ[σᵣₛ] β) :
    (f - g).mapMatrix = (f.mapMatrix - g.mapMatrix : Matrix m n α →ₛₗ[σᵣₛ] _) := rfl

@[simp]
theorem mapMatrix_neg (f : α →ₛₗ[σᵣₛ] β) :
    (-f).mapMatrix = (-f.mapMatrix : Matrix m n α →ₛₗ[σᵣₛ] _) := rfl

end

end LinearMap

namespace LinearEquiv

variable [Semiring R] [Semiring S] [Semiring T]
variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
variable [Module R α] [Module S β] [Module T γ]
variable {σᵣₛ : R →+* S} {σₛₜ : S →+* T} {σᵣₜ : R →+* T} [RingHomCompTriple σᵣₛ σₛₜ σᵣₜ]
variable {σₛᵣ : S →+* R} {σₜₛ : T →+* S} {σₜᵣ : T →+* R} [RingHomCompTriple σₜₛ σₛᵣ σₜᵣ]
variable [RingHomInvPair σᵣₛ σₛᵣ] [RingHomInvPair σₛᵣ σᵣₛ]
variable [RingHomInvPair σₛₜ σₜₛ] [RingHomInvPair σₜₛ σₛₜ]
variable [RingHomInvPair σᵣₜ σₜᵣ] [RingHomInvPair σₜᵣ σᵣₜ]

/-- The `LinearEquiv` between spaces of matrices induced by a `LinearEquiv` between their
coefficients. This is `Matrix.map` as a `LinearEquiv`. -/
@[simps apply]
def mapMatrix (f : α ≃ₛₗ[σᵣₛ] β) : Matrix m n α ≃ₛₗ[σᵣₛ] Matrix m n β :=
  { f.toEquiv.mapMatrix,
    f.toLinearMap.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]
theorem mapMatrix_refl : (LinearEquiv.refl R α).mapMatrix = LinearEquiv.refl R (Matrix m n α) :=
  rfl

@[simp]
theorem mapMatrix_symm (f : α ≃ₛₗ[σᵣₛ] β) :
    f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ₛₗ[_] _) :=
  rfl

@[simp]
theorem mapMatrix_trans (f : α ≃ₛₗ[σᵣₛ] β) (g : β ≃ₛₗ[σₛₜ] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ₛₗ[_] _) :=
  rfl

@[simp] lemma mapMatrix_toLinearMap (f : α ≃ₛₗ[σᵣₛ] β) :
    (f.mapMatrix : _ ≃ₛₗ[_] Matrix m n β).toLinearMap = f.toLinearMap.mapMatrix := by
  rfl

lemma entryLinearMap_comp_mapMatrix (f : α ≃ₛₗ[σᵣₛ] β) (i : m) (j : n) :
    (entryLinearMap S _ i j).comp f.mapMatrix.toLinearMap =
      f.toLinearMap.comp (entryLinearMap R _ i j) := by
  simp only [mapMatrix_toLinearMap, LinearMap.entryLinearMap_comp_mapMatrix]

end LinearEquiv

namespace RingHom

variable [Fintype m] [DecidableEq m]
variable [NonAssocSemiring α] [NonAssocSemiring β] [NonAssocSemiring γ]

/-- The `RingHom` between spaces of square matrices induced by a `RingHom` between their
coefficients. This is `Matrix.map` as a `RingHom`. -/
@[simps]
def mapMatrix (f : α →+* β) : Matrix m m α →+* Matrix m m β :=
  { f.toAddMonoidHom.mapMatrix with
    toFun := fun M => M.map f
    map_one' := by simp
    map_mul' := fun _ _ => Matrix.map_mul }

@[simp]
theorem mapMatrix_id : (RingHom.id α).mapMatrix = RingHom.id (Matrix m m α) :=
  rfl

@[simp]
theorem mapMatrix_comp (f : β →+* γ) (g : α →+* β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α →+* _) :=
  rfl

protected lemma _root_.Matrix.map_pow {α β : Type*} [Semiring α] [Semiring β]
    (M : Matrix m m α) (f : α →+* β) (a : ℕ) : (M ^ a).map f = (M.map f) ^ a :=
  f.mapMatrix.map_pow M a

end RingHom

namespace RingEquiv

variable [Fintype m] [DecidableEq m]
variable [NonAssocSemiring α] [NonAssocSemiring β] [NonAssocSemiring γ]

/-- The `RingEquiv` between spaces of square matrices induced by a `RingEquiv` between their
coefficients. This is `Matrix.map` as a `RingEquiv`. -/
@[simps apply]
def mapMatrix (f : α ≃+* β) : Matrix m m α ≃+* Matrix m m β :=
  { f.toRingHom.mapMatrix,
    f.toAddEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]
theorem mapMatrix_refl : (RingEquiv.refl α).mapMatrix = RingEquiv.refl (Matrix m m α) :=
  rfl

@[simp]
theorem mapMatrix_symm (f : α ≃+* β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃+* _) :=
  rfl

@[simp]
theorem mapMatrix_trans (f : α ≃+* β) (g : β ≃+* γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m m α ≃+* _) :=
  rfl

open MulOpposite in
/--
For any ring `R`, we have ring isomorphism `Matₙₓₙ(Rᵒᵖ) ≅ (Matₙₓₙ(R))ᵒᵖ` given by transpose.
-/
@[simps apply symm_apply]
def mopMatrix {α} [Mul α] [AddCommMonoid α] : Matrix m m αᵐᵒᵖ ≃+* (Matrix m m α)ᵐᵒᵖ where
  toFun M := op (M.transpose.map unop)
  invFun M := M.unop.transpose.map op
  left_inv _ := by aesop
  right_inv _ := by aesop
  map_mul' _ _ := unop_injective <| by ext; simp [transpose, mul_apply]
  map_add' _ _ := by aesop

end RingEquiv

instance (α) [MulOne α] [AddCommMonoid α] [IsStablyFiniteRing α] : IsStablyFiniteRing αᵐᵒᵖ where
  isDedekindFiniteMonoid n := .of_injective (MonoidHom.mk
    ⟨RingEquiv.mopMatrix, by simp⟩ RingEquiv.mopMatrix.map_mul) (RingEquiv.injective _)

open MulOpposite in
theorem MulOpposite.isStablyFiniteRing_iff (α) [MulOne α] [AddCommMonoid α] :
    IsStablyFiniteRing αᵐᵒᵖ ↔ IsStablyFiniteRing α where
  mp _ :=
  ⟨fun n ↦ let f := MonoidHom.mk ⟨fun M : Matrix (Fin n) (Fin n) α ↦ M.map (op ∘ op), by aesop⟩
               fun _ _ ↦ by ext; simp [mul_apply]
  .of_injective f (map_injective (op_injective.comp op_injective))⟩
  mpr _ := inferInstance

namespace AlgHom

variable [Fintype m] [DecidableEq m]
variable [CommSemiring R] [Semiring α] [Semiring β] [Semiring γ]
variable [Algebra R α] [Algebra R β] [Algebra R γ]

/-- The `AlgHom` between spaces of square matrices induced by an `AlgHom` between their
coefficients. This is `Matrix.map` as an `AlgHom`. -/
@[simps]
def mapMatrix (f : α →ₐ[R] β) : Matrix m m α →ₐ[R] Matrix m m β :=
  { f.toRingHom.mapMatrix with
    toFun := fun M => M.map f
    commutes' := fun r => Matrix.map_algebraMap r f (map_zero _) (f.commutes r) }

@[simp]
theorem mapMatrix_id : (AlgHom.id R α).mapMatrix = AlgHom.id R (Matrix m m α) :=
  rfl

@[simp]
theorem mapMatrix_comp (f : β →ₐ[R] γ) (g : α →ₐ[R] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α →ₐ[R] _) :=
  rfl

end AlgHom

namespace AlgEquiv

variable [Fintype m] [DecidableEq m]
variable [CommSemiring R] [Semiring α] [Semiring β] [Semiring γ]
variable [Algebra R α] [Algebra R β] [Algebra R γ]

/-- The `AlgEquiv` between spaces of square matrices induced by an `AlgEquiv` between their
coefficients. This is `Matrix.map` as an `AlgEquiv`. -/
@[simps apply]
def mapMatrix (f : α ≃ₐ[R] β) : Matrix m m α ≃ₐ[R] Matrix m m β :=
  { f.toAlgHom.mapMatrix,
    f.toRingEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]
theorem mapMatrix_refl : AlgEquiv.refl.mapMatrix = (AlgEquiv.refl : Matrix m m α ≃ₐ[R] _) :=
  rfl

@[simp]
theorem mapMatrix_symm (f : α ≃ₐ[R] β) :
    f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃ₐ[R] _) :=
  rfl

@[simp]
theorem mapMatrix_trans (f : α ≃ₐ[R] β) (g : β ≃ₐ[R] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m m α ≃ₐ[R] _) :=
  rfl

/-- For any algebra `α` over a ring `R`, we have an `R`-algebra isomorphism
`Matₙₓₙ(αᵒᵖ) ≅ (Matₙₓₙ(R))ᵒᵖ` given by transpose. If `α` is commutative,
we can get rid of the `ᵒᵖ` in the left-hand side, see `Matrix.transposeAlgEquiv`. -/
@[simps!] def mopMatrix : Matrix m m αᵐᵒᵖ ≃ₐ[R] (Matrix m m α)ᵐᵒᵖ where
  __ := RingEquiv.mopMatrix
  commutes' _ := MulOpposite.unop_injective <| by
    ext; simp [algebraMap_matrix_apply, eq_comm, apply_ite MulOpposite.unop]

end AlgEquiv

namespace AddSubmonoid

variable {A : Type*} [AddMonoid A]

/-- A version of `Set.matrix` for `AddSubmonoid`s.
Given an `AddSubmonoid` `S`, `S.matrix` is the `AddSubmonoid` of matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps]
def matrix (S : AddSubmonoid A) : AddSubmonoid (Matrix m n A) where
  carrier := Set.matrix S
  add_mem' hm hn i j := add_mem (hm i j) (hn i j)
  zero_mem' _ _ := zero_mem _

end AddSubmonoid

namespace AddSubgroup

variable {A : Type*} [AddGroup A]

/-- A version of `Set.matrix` for `AddSubgroup`s.
Given an `AddSubgroup` `S`, `S.matrix` is the `AddSubgroup` of matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
def matrix (S : AddSubgroup A) : AddSubgroup (Matrix m n A) where
  __ := S.toAddSubmonoid.matrix
  neg_mem' hm i j := AddSubgroup.neg_mem _ (hm i j)

end AddSubgroup

namespace Subsemiring

variable {R : Type*} [NonAssocSemiring R]
variable [Fintype n] [DecidableEq n]

/-- A version of `Set.matrix` for `Subsemiring`s.
Given a `Subsemiring` `S`, `S.matrix` is the `Subsemiring` of square matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
def matrix (S : Subsemiring R) : Subsemiring (Matrix n n R) where
  __ := S.toAddSubmonoid.matrix
  mul_mem' ha hb i j := Subsemiring.sum_mem _ (fun k _ => Subsemiring.mul_mem _ (ha i k) (hb k j))
  one_mem' := (diagonal_mem_matrix_iff (Subsemiring.zero_mem _)).mpr fun _ => Subsemiring.one_mem _

end Subsemiring

namespace Subring

variable {R : Type*} [NonAssocRing R]
variable [Fintype n] [DecidableEq n]

/-- A version of `Set.matrix` for `Subring`s.
Given a `Subring` `S`, `S.matrix` is the `Subring` of square matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
def matrix (S : Subring R) : Subring (Matrix n n R) where
  __ := S.toSubsemiring.matrix
  neg_mem' hm i j := Subring.neg_mem _ (hm i j)

end Subring

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A version of `Set.matrix` for `Submodule`s.
Given a `Submodule` `S`, `S.matrix` is the `Submodule` of matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
def matrix (S : Submodule R M) : Submodule R (Matrix m n M) where
  __ := S.toAddSubmonoid.matrix
  smul_mem' _ _ hm i j := Submodule.smul_mem _ _ (hm i j)

end Submodule

open Matrix

namespace Matrix

section Pi

variable {ι : Type*} {β : ι → Type*}

/-- Matrices over a Pi type are in canonical bijection with tuples of matrices. -/
@[simps] def piEquiv : Matrix m n (Π i, β i) ≃ Π i, Matrix m n (β i) where
  toFun f i := f.map (· i)
  invFun f := .of fun j k i ↦ f i j k
  left_inv _ := rfl
  right_inv _ := rfl

/-- `piEquiv` as an `AddEquiv`. -/
@[simps!] def piAddEquiv [∀ i, Add (β i)] : Matrix m n (Π i, β i) ≃+ Π i, Matrix m n (β i) where
  __ := piEquiv
  map_add' _ _ := rfl

/-- `piEquiv` as a `LinearEquiv`. -/
@[simps] def piLinearEquiv (R) [Semiring R] [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)] :
    Matrix m n (Π i, β i) ≃ₗ[R] Π i, Matrix m n (β i) where
  __ := piAddEquiv
  map_smul' _ _ := rfl

/-- `piEquiv` as a `RingEquiv`. -/
@[simps!] def piRingEquiv [∀ i, AddCommMonoid (β i)] [∀ i, Mul (β i)] [Fintype n] :
    Matrix n n (Π i, β i) ≃+* Π i, Matrix n n (β i) where
  __ := piAddEquiv
  map_mul' _ _ := by ext; simp [Matrix.mul_apply]

/-- `piEquiv` as an `AlgEquiv`. -/
@[simps!] def piAlgEquiv (R) [CommSemiring R] [∀ i, Semiring (β i)] [∀ i, Algebra R (β i)]
    [Fintype n] [DecidableEq n] : Matrix n n (Π i, β i) ≃ₐ[R] Π i, Matrix n n (β i) where
  __ := piRingEquiv
  commutes' := (AlgHom.mk' (piRingEquiv (β := β) (n := n)).toRingHom fun _ _ ↦ rfl).commutes

end Pi

section Transpose

open Matrix

variable (m n α)

/-- `Matrix.transpose` as an `AddEquiv` -/
@[simps apply]
def transposeAddEquiv [Add α] : Matrix m n α ≃+ Matrix n m α where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose
  map_add' := transpose_add

@[simp]
theorem transposeAddEquiv_symm [Add α] : (transposeAddEquiv m n α).symm = transposeAddEquiv n m α :=
  rfl

variable {m n α}

theorem transpose_list_sum [AddMonoid α] (l : List (Matrix m n α)) :
    l.sumᵀ = (l.map transpose).sum :=
  map_list_sum (transposeAddEquiv m n α) l

theorem transpose_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix m n α)) :
    s.sumᵀ = (s.map transpose).sum :=
  (transposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s

theorem transpose_sum [AddCommMonoid α] {ι : Type*} (s : Finset ι) (M : ι → Matrix m n α) :
    (∑ i ∈ s, M i)ᵀ = ∑ i ∈ s, (M i)ᵀ :=
  map_sum (transposeAddEquiv m n α) _ s

variable (m n R α)

/-- `Matrix.transpose` as a `LinearMap` -/
@[simps apply]
def transposeLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] :
    Matrix m n α ≃ₗ[R] Matrix n m α where
  __ := transposeAddEquiv m n α
  map_smul' := transpose_smul

@[simp]
theorem transposeLinearEquiv_symm [Semiring R] [AddCommMonoid α] [Module R α] :
    (transposeLinearEquiv m n R α).symm = transposeLinearEquiv n m R α :=
  rfl

variable {m n R α}
variable (m α)

/-- `Matrix.transpose` as a `RingEquiv` to the opposite ring -/
@[simps!]
def transposeRingEquiv [AddCommMonoid α] [CommMagma α] [Fintype m] :
    Matrix m m α ≃+* (Matrix m m α)ᵐᵒᵖ where
  __ := transposeAddEquiv m m α |>.trans MulOpposite.opAddEquiv
  map_mul' M N := (congrArg MulOpposite.op <| transpose_mul M N).trans <| MulOpposite.op_mul ..

variable {m α}

@[simp]
theorem transpose_pow [CommSemiring α] [Fintype m] [DecidableEq m] (M : Matrix m m α) (k : ℕ) :
    (M ^ k)ᵀ = Mᵀ ^ k :=
  MulOpposite.op_injective <| map_pow (transposeRingEquiv m α) M k

theorem transpose_list_prod [CommSemiring α] [Fintype m] [DecidableEq m] (l : List (Matrix m m α)) :
    l.prodᵀ = (l.map transpose).reverse.prod :=
  (transposeRingEquiv m α).unop_map_list_prod l

variable (R m α)

/-- `Matrix.transpose` as an `AlgEquiv` to the opposite ring -/
@[simps!]
def transposeAlgEquiv [CommSemiring R] [CommSemiring α] [Fintype m] [DecidableEq m] [Algebra R α] :
    Matrix m m α ≃ₐ[R] (Matrix m m α)ᵐᵒᵖ where
  __ := transposeRingEquiv m α
  commutes' r := by simp [algebraMap_eq_diagonal]

end Transpose

section NonUnitalNonAssocSemiring
variable {ι : Type*} [NonUnitalNonAssocSemiring α] [Fintype n]

theorem sum_mulVec (s : Finset ι) (x : ι → Matrix m n α) (y : n → α) :
    (∑ i ∈ s, x i) *ᵥ y = ∑ i ∈ s, x i *ᵥ y := by
  ext
  simp only [mulVec, dotProduct, sum_apply, Finset.sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]

theorem mulVec_sum (x : Matrix m n α) (s : Finset ι) (y : ι → (n → α)) :
    x *ᵥ ∑ i ∈ s, y i = ∑ i ∈ s, x *ᵥ y i := by
  ext
  simp only [mulVec, dotProduct_sum, Finset.sum_apply]

theorem sum_vecMul (s : Finset ι) (x : ι → (n → α)) (y : Matrix n m α) :
    (∑ i ∈ s, x i) ᵥ* y = ∑ i ∈ s, x i ᵥ* y := by
  ext
  simp only [vecMul, sum_dotProduct, Finset.sum_apply]

theorem vecMul_sum (x : n → α) (s : Finset ι) (y : ι → Matrix n m α) :
    x ᵥ* (∑ i ∈ s, y i) = ∑ i ∈ s, x ᵥ* y i := by
  ext
  simp only [vecMul, dotProduct, sum_apply, Finset.mul_sum, Finset.sum_apply]
  rw [Finset.sum_comm]

end NonUnitalNonAssocSemiring

end Matrix
