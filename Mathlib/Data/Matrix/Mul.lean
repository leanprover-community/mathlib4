/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang,
  Matteo Cipollina
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Regular.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Diagonal

/-!
# Matrix multiplication

This file defines vector and matrix multiplication

## Main definitions
* `dotProduct`: the dot product between two vectors
* `Matrix.mul`: multiplication of two matrices
* `Matrix.mulVec`: multiplication of a matrix with a vector
* `Matrix.vecMul`: multiplication of a vector with a matrix
* `Matrix.vecMulVec`: multiplication of a vector with a vector to get a matrix
* `Matrix.instRing`: square matrices form a ring

## Notation

The scope `Matrix` gives the following notation:

* `⬝ᵥ` for `dotProduct`
* `*ᵥ` for `Matrix.mulVec`
* `ᵥ*` for `Matrix.vecMul`

See `Mathlib/Data/Matrix/ConjTranspose.lean` for

* `ᴴ` for `Matrix.conjTranspose`

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `fun i j ↦ _` or even `(fun i j ↦ _ : Matrix m n α)`, as these are not recognized by Lean
as having the right type. Instead, `Matrix.of` should be used.

## TODO

Under various conditions, multiplication of infinite matrices makes sense.
These have not yet been implemented.
-/

assert_not_exists Algebra Field TrivialStar

universe u u' v w

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}
variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

open Matrix

section DotProduct

variable [Fintype m] [Fintype n]

/-- `dotProduct v w` is the sum of the entrywise products `v i * w i`.

See also `dotProductEquiv`. -/
def dotProduct [Mul α] [AddCommMonoid α] (v w : m → α) : α :=
  ∑ i, v i * w i

/- The precedence of 72 comes immediately after ` • ` for `SMul.smul`,
so that `r₁ • a ⬝ᵥ r₂ • b` is parsed as `(r₁ • a) ⬝ᵥ (r₂ • b)` here. -/
@[inherit_doc]
infixl:72 " ⬝ᵥ " => dotProduct

theorem dotProduct_assoc [NonUnitalSemiring α] (u : m → α) (w : n → α) (v : Matrix m n α) :
    (fun j => u ⬝ᵥ fun i => v i j) ⬝ᵥ w = u ⬝ᵥ fun i => v i ⬝ᵥ w := by
  simpa [dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc] using Finset.sum_comm

theorem dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : m → α) : v ⬝ᵥ w = w ⬝ᵥ v := by
  simp_rw [dotProduct, mul_comm]

@[simp]
theorem dotProduct_pUnit [AddCommMonoid α] [Mul α] (v w : PUnit → α) : v ⬝ᵥ w = v ⟨⟩ * w ⟨⟩ := by
  simp [dotProduct]

section MulOneClass

variable [MulOneClass α] [AddCommMonoid α]

theorem dotProduct_one (v : n → α) : v ⬝ᵥ 1 = ∑ i, v i := by simp [(· ⬝ᵥ ·)]

theorem one_dotProduct (v : n → α) : 1 ⬝ᵥ v = ∑ i, v i := by simp [(· ⬝ᵥ ·)]

end MulOneClass

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] (u v w : m → α) (x y : n → α)

@[simp]
theorem dotProduct_zero : v ⬝ᵥ 0 = 0 := by simp [dotProduct]

@[simp]
theorem dotProduct_zero' : (v ⬝ᵥ fun _ => 0) = 0 :=
  dotProduct_zero v

@[simp]
theorem zero_dotProduct : 0 ⬝ᵥ v = 0 := by simp [dotProduct]

@[simp]
theorem zero_dotProduct' : (fun _ => (0 : α)) ⬝ᵥ v = 0 :=
  zero_dotProduct v

@[simp]
theorem add_dotProduct : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w := by
  simp [dotProduct, add_mul, Finset.sum_add_distrib]

@[simp]
theorem dotProduct_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w := by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

@[simp]
theorem sumElim_dotProduct_sumElim : Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct]

/-- Permuting a vector on the left of a dot product can be transferred to the right. -/
@[simp]
theorem comp_equiv_symm_dotProduct (e : m ≃ n) : u ∘ e.symm ⬝ᵥ x = u ⬝ᵥ x ∘ e :=
  (e.sum_comp _).symm.trans <|
    Finset.sum_congr rfl fun _ _ => by simp only [Function.comp, Equiv.symm_apply_apply]

/-- Permuting a vector on the right of a dot product can be transferred to the left. -/
@[simp]
theorem dotProduct_comp_equiv_symm (e : n ≃ m) : u ⬝ᵥ x ∘ e.symm = u ∘ e ⬝ᵥ x := by
  simpa only [Equiv.symm_symm] using (comp_equiv_symm_dotProduct u x e.symm).symm

/-- Permuting vectors on both sides of a dot product is a no-op. -/
@[simp]
theorem comp_equiv_dotProduct_comp_equiv (e : m ≃ n) : x ∘ e ⬝ᵥ y ∘ e = x ⬝ᵥ y := by
  simp [← dotProduct_comp_equiv_symm, Function.comp_def _ e.symm]

theorem dotProduct_sum {ι : Type*} (u : m → α) (s : Finset ι) (v : ι → (m → α)) :
    u ⬝ᵥ ∑ i ∈ s, v i = ∑ i ∈ s, u ⬝ᵥ v i := by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem sum_dotProduct {ι : Type*} (s : Finset ι) (u : ι → (m → α)) (v : m → α) :
    (∑ i ∈ s, u i) ⬝ᵥ v = ∑ i ∈ s, u i ⬝ᵥ v := by
  simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocSemiringDecidable

variable [DecidableEq m] [NonUnitalNonAssocSemiring α] (u v w : m → α)

@[simp]
theorem diagonal_dotProduct (i : m) : diagonal v i ⬝ᵥ w = v i * w i := by
  have : ∀ j ≠ i, diagonal v i j * w j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp


@[simp]
theorem dotProduct_diagonal (i : m) : v ⬝ᵥ diagonal w i = v i * w i := by
  have : ∀ j ≠ i, v j * diagonal w i j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]
theorem dotProduct_diagonal' (i : m) : (v ⬝ᵥ fun j => diagonal w j i) = v i * w i := by
  have : ∀ j ≠ i, v j * diagonal w j i = 0 := fun j hij => by
    simp [diagonal_apply_ne _ hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]
theorem single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ v = x * v i := by
-- Porting note: added `(_ : m → α)`
  have : ∀ j ≠ i, (Pi.single i x : m → α) j * v j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]
theorem dotProduct_single (x : α) (i : m) : v ⬝ᵥ Pi.single i x = v i * x := by
-- Porting note: added `(_ : m → α)`
  have : ∀ j ≠ i, v j * (Pi.single i x : m → α) j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

end NonUnitalNonAssocSemiringDecidable

section NonAssocSemiring

variable [NonAssocSemiring α]

@[simp]
theorem one_dotProduct_one : (1 : n → α) ⬝ᵥ 1 = Fintype.card n := by
  simp [dotProduct]

theorem dotProduct_single_one [DecidableEq n] (v : n → α) (i : n) :
    v ⬝ᵥ Pi.single i 1 = v i := by
  rw [dotProduct_single, mul_one]

theorem single_one_dotProduct [DecidableEq n] (i : n) (v : n → α) :
    Pi.single i 1 ⬝ᵥ v = v i := by
  rw [single_dotProduct, one_mul]

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α] (u v w : m → α)

@[simp]
theorem neg_dotProduct : -v ⬝ᵥ w = -(v ⬝ᵥ w) := by simp [dotProduct]

@[simp]
theorem dotProduct_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w) := by simp [dotProduct]

lemma neg_dotProduct_neg : -v ⬝ᵥ -w = v ⬝ᵥ w := by
  rw [neg_dotProduct, dotProduct_neg, neg_neg]

@[simp]
theorem sub_dotProduct : (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w := by simp [sub_eq_add_neg]

@[simp]
theorem dotProduct_sub : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w := by simp [sub_eq_add_neg]

end NonUnitalNonAssocRing

section DistribMulAction

variable [Mul α] [AddCommMonoid α] [DistribSMul R α]

@[simp]
theorem smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m → α) :
    x • v ⬝ᵥ w = x • (v ⬝ᵥ w) := by simp [dotProduct, Finset.smul_sum, smul_mul_assoc]

@[simp]
theorem dotProduct_smul [SMulCommClass R α α] (x : R) (v w : m → α) :
    v ⬝ᵥ x • w = x • (v ⬝ᵥ w) := by simp [dotProduct, Finset.smul_sum, mul_smul_comm]

end DistribMulAction

section CommRing
variable [CommRing α] [Nontrivial m] [Nontrivial α]

/-- For any vector `a` in a nontrivial commutative ring with nontrivial index,
there exists a non-zero vector `b` such that `b ⬝ᵥ a = 0`. In other words,
there exists a non-zero orthogonal vector. -/
theorem exists_ne_zero_dotProduct_eq_zero (a : m → α) : ∃ b ≠ 0, b ⬝ᵥ a = 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j : m, i ≠ j := nontrivial_iff.mp ‹_›
  classical
  use if a i = 0 then Pi.single i 1 else if a j = 0 then Pi.single j 1 else
    fun k => if k = i then a j else if k = j then - a i else 0
  split_ifs with h h2
  · simp [h]
  · simp [h2]
  · refine ⟨Function.ne_iff.mpr ⟨i, by simp [h2]⟩, ?_⟩
    simp [dotProduct, Finset.sum_ite, Finset.sum_eq_ite i, hij.symm, mul_comm (a i)]

lemma not_injective_dotProduct_left (a : m → α) :
    ¬ Function.Injective (dotProduct a) := by
  intro h
  obtain ⟨b, hb, hba⟩ := exists_ne_zero_dotProduct_eq_zero a
  simpa [dotProduct_comm a b, hba, hb] using @h b 0

lemma not_injective_dotProduct_right (a : m → α) :
    ¬ Function.Injective (dotProduct · a) := by
  intro h
  obtain ⟨b, hb, hba⟩ := exists_ne_zero_dotProduct_eq_zero a
  simpa [hba, hb] using @h b 0

end CommRing

end DotProduct

open Matrix

namespace Matrix

/-- `M * N` is the usual product of matrices `M` and `N`, i.e. we have that
`(M * N) i k` is the dot product of the `i`-th row of `M` by the `k`-th column of `N`.
This is currently only defined when `m` is finite. -/
-- We want to be lower priority than `instHMul`, but without this we can't have operands with
-- implicit dimensions.
@[default_instance 100]
instance [Fintype m] [Mul α] [AddCommMonoid α] :
    HMul (Matrix l m α) (Matrix m n α) (Matrix l n α) where
  hMul M N := fun i k => (fun j => M i j) ⬝ᵥ fun j => N j k

theorem mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
    {i k} : (M * N) i k = ∑ j, M i j * N j k :=
  rfl

instance [Fintype n] [Mul α] [AddCommMonoid α] : Mul (Matrix n n α) where mul M N := M * N

theorem mul_apply' [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
    {i k} : (M * N) i k = (M i) ⬝ᵥ fun j => N j k :=
  rfl

theorem two_mul_expl {R : Type*} [NonUnitalNonAssocSemiring R] (A B : Matrix (Fin 2) (Fin 2) R) :
    (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧
    (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
    (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧
    (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ]
    simp

section AddCommMonoid

variable [AddCommMonoid α] [Mul α]

@[simp]
theorem smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] [IsScalarTower R α α] (a : R)
    (M : Matrix m n α) (N : Matrix n l α) : (a • M) * N = a • (M * N) := by
  ext
  apply smul_dotProduct a

@[simp]
theorem mul_smul [Fintype n] [Monoid R] [DistribMulAction R α] [SMulCommClass R α α]
    (M : Matrix m n α) (a : R) (N : Matrix n l α) : M * (a • N) = a • (M * N) := by
  ext
  apply dotProduct_smul

end AddCommMonoid

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

@[simp]
protected theorem mul_zero [Fintype n] (M : Matrix m n α) : M * (0 : Matrix n o α) = 0 := by
  ext
  apply dotProduct_zero

@[simp]
protected theorem zero_mul [Fintype m] (M : Matrix m n α) : (0 : Matrix l m α) * M = 0 := by
  ext
  apply zero_dotProduct

protected theorem mul_add [Fintype n] (L : Matrix m n α) (M N : Matrix n o α) :
    L * (M + N) = L * M + L * N := by
  ext
  apply dotProduct_add

protected theorem add_mul [Fintype m] (L M : Matrix l m α) (N : Matrix m n α) :
    (L + M) * N = L * N + M * N := by
  ext
  apply add_dotProduct

instance nonUnitalNonAssocSemiring [Fintype n] : NonUnitalNonAssocSemiring (Matrix n n α) :=
  { Matrix.addCommMonoid with
    mul_zero := Matrix.mul_zero
    zero_mul := Matrix.zero_mul
    left_distrib := Matrix.mul_add
    right_distrib := Matrix.add_mul }

@[simp]
theorem diagonal_mul [Fintype m] [DecidableEq m] (d : m → α) (M : Matrix m n α) (i j) :
    (diagonal d * M) i j = d i * M i j :=
  diagonal_dotProduct _ _ _

@[simp]
theorem mul_diagonal [Fintype n] [DecidableEq n] (d : n → α) (M : Matrix m n α) (i j) :
    (M * diagonal d) i j = M i j * d j := by
  rw [← diagonal_transpose]
  apply dotProduct_diagonal

@[simp]
theorem diagonal_mul_diagonal [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
    diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

theorem diagonal_mul_diagonal' [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
    diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i :=
  diagonal_mul_diagonal _ _

theorem commute_diagonal {α : Type*} [NonUnitalNonAssocCommSemiring α]
    [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
    Commute (diagonal d₁) (diagonal d₂) := by
  simp_rw [commute_iff_eq, diagonal_mul_diagonal, mul_comm]

theorem smul_eq_diagonal_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) (a : α) :
    a • M = (diagonal fun _ => a) * M := by
  ext
  simp

theorem op_smul_eq_mul_diagonal [Fintype n] [DecidableEq n] (M : Matrix m n α) (a : α) :
    MulOpposite.op a • M = M * (diagonal fun _ : n => a) := by
  ext
  simp

/-- Left multiplication by a matrix, as an `AddMonoidHom` from matrices to matrices. -/
@[simps]
def addMonoidHomMulLeft [Fintype m] (M : Matrix l m α) : Matrix m n α →+ Matrix l n α where
  toFun x := M * x
  map_zero' := Matrix.mul_zero _
  map_add' := Matrix.mul_add _

/-- Right multiplication by a matrix, as an `AddMonoidHom` from matrices to matrices. -/
@[simps]
def addMonoidHomMulRight [Fintype m] (M : Matrix m n α) : Matrix l m α →+ Matrix l n α where
  toFun x := x * M
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

protected theorem sum_mul [Fintype m] (s : Finset β) (f : β → Matrix l m α) (M : Matrix m n α) :
    (∑ a ∈ s, f a) * M = ∑ a ∈ s, f a * M :=
  map_sum (addMonoidHomMulRight M) f s

protected theorem mul_sum [Fintype m] (s : Finset β) (f : β → Matrix m n α) (M : Matrix l m α) :
    (M * ∑ a ∈ s, f a) = ∑ a ∈ s, M * f a :=
  map_sum (addMonoidHomMulLeft M) f s

/-- This instance enables use with `smul_mul_assoc`. -/
instance Semiring.isScalarTower [Fintype n] [Monoid R] [DistribMulAction R α]
    [IsScalarTower R α α] : IsScalarTower R (Matrix n n α) (Matrix n n α) :=
  ⟨fun r m n => Matrix.smul_mul r m n⟩

/-- This instance enables use with `mul_smul_comm`. -/
instance Semiring.smulCommClass [Fintype n] [Monoid R] [DistribMulAction R α]
    [SMulCommClass R α α] : SMulCommClass R (Matrix n n α) (Matrix n n α) :=
  ⟨fun r m n => (Matrix.mul_smul m r n).symm⟩

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

@[simp]
protected theorem one_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) :
    (1 : Matrix m m α) * M = M := by
  ext
  rw [← diagonal_one, diagonal_mul, one_mul]

@[simp]
protected theorem mul_one [Fintype n] [DecidableEq n] (M : Matrix m n α) :
    M * (1 : Matrix n n α) = M := by
  ext
  rw [← diagonal_one, mul_diagonal, mul_one]

instance nonAssocSemiring [Fintype n] [DecidableEq n] : NonAssocSemiring (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring, Matrix.instAddCommMonoidWithOne with
    one_mul := Matrix.one_mul
    mul_one := Matrix.mul_one }

@[simp]
protected theorem map_mul [Fintype n] {L : Matrix m n α} {M : Matrix n o α} [NonAssocSemiring β]
    {f : α →+* β} : (L * M).map f = L.map f * M.map f := by
  ext
  simp [mul_apply, map_sum]

theorem smul_one_eq_diagonal [DecidableEq m] (a : α) :
    a • (1 : Matrix m m α) = diagonal fun _ => a := by
  simp_rw [← diagonal_one, ← diagonal_smul, Pi.smul_def, smul_eq_mul, mul_one]

theorem op_smul_one_eq_diagonal [DecidableEq m] (a : α) :
    MulOpposite.op a • (1 : Matrix m m α) = diagonal fun _ => a := by
  simp_rw [← diagonal_one, ← diagonal_smul, Pi.smul_def, op_smul_eq_mul, one_mul]

variable (α n)

end NonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring α] [Fintype m] [Fintype n]

protected theorem mul_assoc (L : Matrix l m α) (M : Matrix m n α) (N : Matrix n o α) :
    L * M * N = L * (M * N) := by
  ext
  apply dotProduct_assoc

instance nonUnitalSemiring : NonUnitalSemiring (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring with mul_assoc := Matrix.mul_assoc }

end NonUnitalSemiring

section Semiring

variable [Semiring α]

instance semiring [Fintype n] [DecidableEq n] : Semiring (Matrix n n α) :=
  { Matrix.nonUnitalSemiring, Matrix.nonAssocSemiring with }

end Semiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α] [Fintype n]

@[simp]
protected theorem neg_mul (M : Matrix m n α) (N : Matrix n o α) : (-M) * N = -(M * N) := by
  ext
  apply neg_dotProduct

@[simp]
protected theorem mul_neg (M : Matrix m n α) (N : Matrix n o α) : M * (-N) = -(M * N) := by
  ext
  apply dotProduct_neg

protected theorem sub_mul (M M' : Matrix m n α) (N : Matrix n o α) :
    (M - M') * N = M * N - M' * N := by
  rw [sub_eq_add_neg, Matrix.add_mul, Matrix.neg_mul, sub_eq_add_neg]

protected theorem mul_sub (M : Matrix m n α) (N N' : Matrix n o α) :
    M * (N - N') = M * N - M * N' := by
  rw [sub_eq_add_neg, Matrix.mul_add, Matrix.mul_neg, sub_eq_add_neg]

instance nonUnitalNonAssocRing : NonUnitalNonAssocRing (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring, Matrix.addCommGroup with }

end NonUnitalNonAssocRing

instance instNonUnitalRing [Fintype n] [NonUnitalRing α] : NonUnitalRing (Matrix n n α) :=
  { Matrix.nonUnitalSemiring, Matrix.addCommGroup with }

instance instNonAssocRing [Fintype n] [DecidableEq n] [NonAssocRing α] :
    NonAssocRing (Matrix n n α) :=
  { Matrix.nonAssocSemiring, Matrix.instAddCommGroupWithOne with }

instance instRing [Fintype n] [DecidableEq n] [Ring α] : Ring (Matrix n n α) :=
  { Matrix.semiring, Matrix.instAddCommGroupWithOne with }

section Semiring

variable [Semiring α]

@[simp]
theorem mul_mul_left [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α) :
    (of fun i j => a * M i j) * N = a • (M * N) :=
  smul_mul a M N

lemma pow_apply_nonneg [Fintype n] [DecidableEq n] [PartialOrder α] [IsOrderedRing α]
    {A : Matrix n n α} (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) : ∀ i j, 0 ≤ (A ^ k) i j := by
  induction k with
  | zero => aesop (add simp one_apply)
  | succ m ih =>
    intro i j; rw [pow_succ, mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

end Semiring

section CommSemiring

variable [CommSemiring α]

theorem smul_eq_mul_diagonal [Fintype n] [DecidableEq n] (M : Matrix m n α) (a : α) :
    a • M = M * diagonal fun _ => a := by
  ext
  simp [mul_comm]

@[simp]
theorem mul_mul_right [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α) :
    (M * of fun i j => a * N i j) = a • (M * N) :=
  mul_smul M a N

end CommSemiring

end Matrix

open Matrix

namespace Matrix

/-- For two vectors `w` and `v`, `vecMulVec w v i j` is defined to be `w i * v j`.
Put another way, `vecMulVec w v` is exactly `replicateCol ι w * replicateRow ι v` for
`Unique ι`; see `vecMulVec_eq`. -/
def vecMulVec [Mul α] (w : m → α) (v : n → α) : Matrix m n α :=
  of fun x y => w x * v y

-- TODO: set as an equation lemma for `vecMulVec`, see https://github.com/leanprover-community/mathlib4/pull/3024
theorem vecMulVec_apply [Mul α] (w : m → α) (v : n → α) (i j) : vecMulVec w v i j = w i * v j :=
  rfl

lemma row_vecMulVec [Mul α] (w : m → α) (v : n → α) (i : m) :
    (vecMulVec w v).row i = w i • v := rfl

lemma col_vecMulVec [Mul α] (w : m → α) (v : n → α) (j : n) :
    (vecMulVec w v).col j = MulOpposite.op (v j) • w := rfl

@[simp] theorem zero_vecMulVec [MulZeroClass α] (v : n → α) : vecMulVec (0 : m → α) v = 0 :=
  ext fun _ _ => zero_mul _

@[simp] theorem vecMulVec_zero [MulZeroClass α] (w : m → α) : vecMulVec w (0 : m → α) = 0 :=
  ext fun _ _ => mul_zero _

theorem vecMulVec_ne_zero [Mul α] [Zero α] [NoZeroDivisors α] {a b : n → α}
    (ha : a ≠ 0) (hb : b ≠ 0) : vecMulVec a b ≠ 0 := by
  intro h
  obtain ⟨i, ha⟩ := Function.ne_iff.mp ha
  obtain ⟨j, hb⟩ := Function.ne_iff.mp hb
  exact mul_ne_zero ha hb congr($h i j)

@[simp] theorem vecMulVec_eq_zero [MulZeroClass α] [NoZeroDivisors α] {a b : n → α} :
    vecMulVec a b = 0 ↔ a = 0 ∨ b = 0 := by
  simp only [← ext_iff, vecMulVec_apply, zero_apply, mul_eq_zero, funext_iff, Pi.zero_apply,
    forall_or_left, forall_or_right]

theorem add_vecMulVec [Mul α] [Add α] [RightDistribClass α] (w₁ w₂ : m → α) (v : n → α) :
    vecMulVec (w₁ + w₂) v = vecMulVec w₁ v + vecMulVec w₂ v :=
  ext fun _ _ => add_mul _ _ _

theorem vecMulVec_add [Mul α] [Add α] [LeftDistribClass α] (w : m → α) (v₁ v₂ : n → α) :
    vecMulVec w (v₁ + v₂) = vecMulVec w v₁ + vecMulVec w v₂  :=
  ext fun _ _ => mul_add _ _ _

@[simp]
theorem neg_vecMulVec [Mul α] [HasDistribNeg α] (w : m → α) (v : n → α) :
    vecMulVec (-w) v = -vecMulVec w v :=
  ext fun _ _ => neg_mul _ _

@[simp]
theorem vecMulVec_neg [Mul α] [HasDistribNeg α] (w : m → α) (v : n → α) :
    vecMulVec w (-v) = -vecMulVec w v :=
  ext fun _ _ => mul_neg _ _

@[simp]
theorem smul_vecMulVec [Mul α] [SMul R α] [IsScalarTower R α α] (r : R) (w : m → α) (v : n → α) :
    vecMulVec (r • w) v = r • vecMulVec w v :=
  ext fun _ _ => smul_mul_assoc _ _ _

@[simp]
theorem vecMulVec_smul [Mul α] [SMul R α] [SMulCommClass R α α] (r : R) (w : m → α) (v : n → α) :
    vecMulVec w (r • v) = r • vecMulVec w v :=
  ext fun _ _ => mul_smul_comm _ _ _

theorem vecMulVec_smul' [Semigroup α] (w : m → α) (r : α) (v : n → α) :
    vecMulVec w (r • v) = vecMulVec (MulOpposite.op r • w) v :=
  ext fun _ _ => mul_assoc _ _ _ |>.symm

@[simp]
theorem transpose_vecMulVec [CommMagma α] (w : m → α) (v : n → α) :
    (vecMulVec w v)ᵀ = vecMulVec v w :=
  ext fun _ _ => mul_comm _ _

@[simp]
theorem diag_vecMulVec [Mul α] (u v : n → α) : diag (vecMulVec u v) = u * v := rfl

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

/--
`M *ᵥ v` (notation for `mulVec M v`) is the matrix-vector product of matrix `M` and vector `v`,
where `v` is seen as a column vector.
Put another way, `M *ᵥ v` is the vector whose entries are those of `M * col v` (see `col_mulVec`).

The notation has precedence 73, which comes immediately before ` ⬝ᵥ ` for `dotProduct`,
so that `A *ᵥ v ⬝ᵥ B *ᵥ w` is parsed as `(A *ᵥ v) ⬝ᵥ (B *ᵥ w)`.
-/
def mulVec [Fintype n] (M : Matrix m n α) (v : n → α) : m → α
  | i => (fun j => M i j) ⬝ᵥ v

@[inherit_doc]
scoped infixr:73 " *ᵥ " => Matrix.mulVec

/--
`v ᵥ* M` (notation for `vecMul v M`) is the vector-matrix product of vector `v` and matrix `M`,
where `v` is seen as a row vector.
Put another way, `v ᵥ* M` is the vector whose entries are those of `row v * M` (see `row_vecMul`).

The notation has precedence 73, which comes immediately before ` ⬝ᵥ ` for `dotProduct`,
so that `v ᵥ* A ⬝ᵥ w ᵥ* B` is parsed as `(v ᵥ* A) ⬝ᵥ (w ᵥ* B)`.
-/
def vecMul [Fintype m] (v : m → α) (M : Matrix m n α) : n → α
  | j => v ⬝ᵥ fun i => M i j

@[inherit_doc]
scoped infixl:73 " ᵥ* " => Matrix.vecMul

/-- Left multiplication by a matrix, as an `AddMonoidHom` from vectors to vectors. -/
@[simps]
def mulVec.addMonoidHomLeft [Fintype n] (v : n → α) : Matrix m n α →+ m → α where
  toFun M := M *ᵥ v
  map_zero' := by
    ext
    simp [mulVec]
  map_add' x y := by
    ext m
    apply add_dotProduct

/-- The `i`th row of the multiplication is the same as the `vecMul` with the `i`th row of `A`. -/
theorem mul_apply_eq_vecMul [Fintype n] (A : Matrix m n α) (B : Matrix n o α) (i : m) :
    (A * B) i = A i ᵥ* B :=
  rfl

theorem vecMul_eq_sum [Fintype m] (v : m → α) (M : Matrix m n α) : v ᵥ* M = ∑ i, v i • M i :=
  (Finset.sum_fn ..).symm

theorem mulVec_eq_sum [Fintype n] (v : n → α) (M : Matrix m n α) :
    M *ᵥ v = ∑ i, MulOpposite.op (v i) • Mᵀ i :=
  (Finset.sum_fn ..).symm

theorem mulVec_diagonal [Fintype m] [DecidableEq m] (v w : m → α) (x : m) :
    (diagonal v *ᵥ w) x = v x * w x :=
  diagonal_dotProduct v w x

theorem vecMul_diagonal [Fintype m] [DecidableEq m] (v w : m → α) (x : m) :
    (v ᵥ* diagonal w) x = v x * w x :=
  dotProduct_diagonal' v w x

/-- Associate the dot product of `mulVec` to the left. -/
theorem dotProduct_mulVec [Fintype n] [Fintype m] [NonUnitalSemiring R] (v : m → R)
    (A : Matrix m n R) (w : n → R) : v ⬝ᵥ A *ᵥ w = v ᵥ* A ⬝ᵥ w := by
  simp only [dotProduct, vecMul, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

@[simp]
theorem mulVec_zero [Fintype n] (A : Matrix m n α) : A *ᵥ 0 = 0 := by
  ext
  simp [mulVec]

@[simp]
theorem zero_vecMul [Fintype m] (A : Matrix m n α) : 0 ᵥ* A = 0 := by
  ext
  simp [vecMul]

@[simp]
theorem zero_mulVec [Fintype n] (v : n → α) : (0 : Matrix m n α) *ᵥ v = 0 := by
  ext
  simp [mulVec]

@[simp]
theorem vecMul_zero [Fintype m] (v : m → α) : v ᵥ* (0 : Matrix m n α) = 0 := by
  ext
  simp [vecMul]

theorem mulVec_add [Fintype n] (A : Matrix m n α) (x y : n → α) :
    A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y := by
  ext
  apply dotProduct_add

theorem add_mulVec [Fintype n] (A B : Matrix m n α) (x : n → α) :
    (A + B) *ᵥ x = A *ᵥ x + B *ᵥ x := by
  ext
  apply add_dotProduct

theorem vecMul_add [Fintype m] (A B : Matrix m n α) (x : m → α) :
    x ᵥ* (A + B) = x ᵥ* A + x ᵥ* B := by
  ext
  apply dotProduct_add

theorem add_vecMul [Fintype m] (A : Matrix m n α) (x y : m → α) :
    (x + y) ᵥ* A = x ᵥ* A + y ᵥ* A := by
  ext
  apply add_dotProduct

theorem mulVec_smul [Fintype n] [DistribSMul R α] [SMulCommClass R α α]
    (M : Matrix m n α) (b : R) (v : n → α) :
    M *ᵥ (b • v) = b • M *ᵥ v := by
  ext
  exact dotProduct_smul _ _ _

theorem smul_mulVec [Fintype n] [DistribSMul R α] [IsScalarTower R α α]
    (b : R) (M : Matrix m n α) (v : n → α) :
    (b • M) *ᵥ v = b • M *ᵥ v := by
  ext
  exact smul_dotProduct _ _ _

theorem smul_vecMul [Fintype m] [DistribSMul R α] [IsScalarTower R α α]
    (b : R) (v : m → α) (M : Matrix m n α) :
    (b • v) ᵥ* M = b • v ᵥ* M := by
  ext
  exact smul_dotProduct _ _ _

theorem vecMul_smul [Fintype m] [DistribSMul R α] [SMulCommClass R α α]
    (v : m → α) (b : R) (M : Matrix m n α) :
    v ᵥ* (b • M) = b • v ᵥ* M := by
  ext
  exact dotProduct_smul _ _ _

@[deprecated (since := "2025-08-14")] alias smul_mulVec_assoc := smul_mulVec

@[simp]
theorem mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
    (j : n) (x : R) : M *ᵥ Pi.single j x = MulOpposite.op x • M.col j :=
  funext fun _ => dotProduct_single _ _ _

@[simp]
theorem single_vecMul [Fintype m] [DecidableEq m] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
    (i : m) (x : R) : Pi.single i x ᵥ* M = x • M.row i :=
  funext fun _ => single_dotProduct _ _ _

theorem mulVec_single_one [Fintype n] [DecidableEq n] [NonAssocSemiring R]
    (M : Matrix m n R) (j : n) :
    M *ᵥ Pi.single j 1 = M.col j := by ext; simp

theorem single_one_vecMul [Fintype m] [DecidableEq m] [NonAssocSemiring R]
    (i : m) (M : Matrix m n R) :
    Pi.single i 1 ᵥ* M = M.row i := by ext; simp

theorem diagonal_mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n → R)
    (j : n) (x : R) : diagonal v *ᵥ Pi.single j x = Pi.single j (v j * x) := by
  ext i
  rw [mulVec_diagonal]
  exact Pi.apply_single (fun i x => v i * x) (fun i => mul_zero _) j x i

theorem single_vecMul_diagonal [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n → R)
    (j : n) (x : R) : (Pi.single j x) ᵥ* (diagonal v) = Pi.single j (x * v j) := by
  ext i
  rw [vecMul_diagonal]
  exact Pi.apply_single (fun i x => x * v i) (fun i => zero_mul _) j x i

end NonUnitalNonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring α]

@[simp]
theorem vecMul_vecMul [Fintype n] [Fintype m] (v : m → α) (M : Matrix m n α) (N : Matrix n o α) :
    v ᵥ* M ᵥ* N = v ᵥ* (M * N) := by
  ext
  apply dotProduct_assoc

@[simp]
theorem mulVec_mulVec [Fintype n] [Fintype o] (v : o → α) (M : Matrix m n α) (N : Matrix n o α) :
    M *ᵥ N *ᵥ v = (M * N) *ᵥ v := by
  ext
  symm
  apply dotProduct_assoc

theorem mul_mul_apply [Fintype n] (A B C : Matrix n n α) (i j : n) :
    (A * B * C) i j = A i ⬝ᵥ B *ᵥ (Cᵀ j) := by
  rw [Matrix.mul_assoc]
  simp [mul_apply, dotProduct, mulVec]

theorem vecMul_vecMulVec [Fintype m] (u v : m → α) (w : n → α) :
    u ᵥ* vecMulVec v w = (u ⬝ᵥ v) • w := by
  ext i
  simp [vecMul, dotProduct, vecMulVec, Finset.sum_mul, mul_assoc]

theorem vecMulVec_mulVec [Fintype n] (u : m → α) (v w : n → α) :
    vecMulVec u v *ᵥ w = MulOpposite.op (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_assoc]

theorem mul_vecMulVec [Fintype m] (M : Matrix l m α) (x : m → α) (y : n → α) :
    M * vecMulVec x y = vecMulVec (M *ᵥ x) y := by
  ext
  simp_rw [mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem vecMulVec_mul [Fintype m] (x : l → α) (y : m → α) (M : Matrix m n α) :
    vecMulVec x y * M = vecMulVec x (y ᵥ* M) := by
  ext
  simp_rw [mul_apply, vecMulVec_apply, vecMul, dotProduct, Finset.mul_sum, mul_assoc]

theorem vecMulVec_mul_vecMulVec [Fintype m] (u : l → α) (v w : m → α) (x : n → α) :
    vecMulVec u v * vecMulVec w x = vecMulVec u ((v ⬝ᵥ w) • x) := by
  rw [vecMulVec_mul, vecMul_vecMulVec]

lemma mul_right_injective_iff_mulVec_injective [Fintype m] [Nonempty n] {A : Matrix l m α} :
    Function.Injective (fun B : Matrix m n α => A * B) ↔ Function.Injective A.mulVec := by
  refine ⟨fun ha v w hvw => ?_, fun ha B C hBC => ext_col fun j => ha congr(($hBC).col j)⟩
  inhabit n
  -- `replicateRow` is not available yet
  suffices (of fun i j => v i) = (of fun i j => w i) from
    funext fun i => congrFun₂ this i (default : n)
  exact ha <| ext fun _ _ => congrFun hvw _

lemma mul_left_injective_iff_vecMul_injective [Nonempty l] [Fintype m] {A : Matrix m n α} :
    Function.Injective (fun B : Matrix l m α => B * A) ↔ Function.Injective A.vecMul := by
  refine ⟨fun ha v w hvw => ?_, fun ha B C hBC => ext_row fun i => ha congr(($hBC).row i)⟩
  inhabit l
  --  `replicateCol` is not available yet
  suffices (of fun i j => v j) = (of fun i j => w j) from
    funext fun j => congrFun₂ this (default : l) j
  exact ha <| ext fun _ _ => congrFun hvw _

lemma isLeftRegular_iff_mulVec_injective [Fintype m] {A : Matrix m m α} :
    IsLeftRegular A ↔ Function.Injective A.mulVec := by
  cases isEmpty_or_nonempty m
  · simp [IsLeftRegular, Function.injective_of_subsingleton]
  exact mul_right_injective_iff_mulVec_injective

lemma isRightRegular_iff_vecMul_injective [Fintype m] {A : Matrix m m α} :
    IsRightRegular A ↔ Function.Injective A.vecMul := by
  cases isEmpty_or_nonempty m
  · simp [IsRightRegular, Function.injective_of_subsingleton]
  exact mul_left_injective_iff_vecMul_injective

end NonUnitalSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

theorem mulVec_one [Fintype n] (A : Matrix m n α) : A *ᵥ 1 = ∑ j, Aᵀ j := by
  ext; simp [mulVec, dotProduct]

theorem one_vecMul [Fintype m] (A : Matrix m n α) : 1 ᵥ* A = ∑ i, A i := by
  ext; simp [vecMul, dotProduct]

lemma ext_of_mulVec_single [DecidableEq n] [Fintype n] {M N : Matrix m n α}
    (h : ∀ i, M *ᵥ Pi.single i 1 = N *ᵥ Pi.single i 1) :
    M = N := by
  ext i j
  simp_rw [mulVec_single_one] at h
  exact congrFun (h j) i

lemma ext_of_single_vecMul [DecidableEq m] [Fintype m] {M N : Matrix m n α}
    (h : ∀ i, Pi.single i 1 ᵥ* M = Pi.single i 1 ᵥ* N) :
    M = N := by
  ext i j
  simp_rw [single_one_vecMul] at h
  exact congrFun (h i) j

variable [Fintype m] [Fintype n] [DecidableEq m]

@[simp]
theorem one_mulVec (v : m → α) : 1 *ᵥ v = v := by
  ext
  rw [← diagonal_one, mulVec_diagonal, one_mul]

@[simp]
theorem vecMul_one (v : m → α) : v ᵥ* 1 = v := by
  ext
  rw [← diagonal_one, vecMul_diagonal, mul_one]

@[simp]
theorem diagonal_const_mulVec (x : α) (v : m → α) :
    (diagonal fun _ => x) *ᵥ v = x • v := by
  ext; simp [mulVec_diagonal]

@[simp]
theorem vecMul_diagonal_const (x : α) (v : m → α) :
    v ᵥ* (diagonal fun _ => x) = MulOpposite.op x • v := by
  ext; simp [vecMul_diagonal]

@[simp]
theorem natCast_mulVec (x : ℕ) (v : m → α) : x *ᵥ v = (x : α) • v :=
  diagonal_const_mulVec _ _

@[simp]
theorem vecMul_natCast (x : ℕ) (v : m → α) : v ᵥ* x = MulOpposite.op (x : α) • v :=
  vecMul_diagonal_const _ _


@[simp]
theorem ofNat_mulVec (x : ℕ) [x.AtLeastTwo] (v : m → α) :
    ofNat(x) *ᵥ v = (OfNat.ofNat x : α) • v :=
  natCast_mulVec _ _

@[simp]
theorem vecMul_ofNat (x : ℕ) [x.AtLeastTwo] (v : m → α) :
    v ᵥ* ofNat(x) = MulOpposite.op (OfNat.ofNat x : α) • v :=
  vecMul_natCast _ _

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

theorem neg_vecMul [Fintype m] (v : m → α) (A : Matrix m n α) : (-v) ᵥ* A = -(v ᵥ* A) := by
  ext
  apply neg_dotProduct

theorem vecMul_neg [Fintype m] (v : m → α) (A : Matrix m n α) : v ᵥ* (-A) = -(v ᵥ* A) := by
  ext
  apply dotProduct_neg

lemma neg_vecMul_neg [Fintype m] (v : m → α) (A : Matrix m n α) : (-v) ᵥ* (-A) = v ᵥ* A := by
  rw [vecMul_neg, neg_vecMul, neg_neg]

theorem neg_mulVec [Fintype n] (v : n → α) (A : Matrix m n α) : (-A) *ᵥ v = -(A *ᵥ v) := by
  ext
  apply neg_dotProduct

theorem mulVec_neg [Fintype n] (v : n → α) (A : Matrix m n α) : A *ᵥ (-v) = -(A *ᵥ v) := by
  ext
  apply dotProduct_neg

lemma neg_mulVec_neg [Fintype n] (v : n → α) (A : Matrix m n α) : (-A) *ᵥ (-v) = A *ᵥ v := by
  rw [mulVec_neg, neg_mulVec, neg_neg]

theorem mulVec_sub [Fintype n] (A : Matrix m n α) (x y : n → α) :
    A *ᵥ (x - y) = A *ᵥ x - A *ᵥ y := by
  ext
  apply dotProduct_sub

theorem sub_mulVec [Fintype n] (A B : Matrix m n α) (x : n → α) :
    (A - B) *ᵥ x = A *ᵥ x - B *ᵥ x := by simp [sub_eq_add_neg, add_mulVec, neg_mulVec]

theorem vecMul_sub [Fintype m] (A B : Matrix m n α) (x : m → α) :
    x ᵥ* (A - B) = x ᵥ* A - x ᵥ* B := by simp [sub_eq_add_neg, vecMul_add, vecMul_neg]

theorem sub_vecMul [Fintype m] (A : Matrix m n α) (x y : m → α) :
    (x - y) ᵥ* A = x ᵥ* A - y ᵥ* A := by
  ext
  apply sub_dotProduct

theorem sub_vecMulVec (w₁ w₂ : m → α) (v : n → α) :
    vecMulVec (w₁ - w₂) v = vecMulVec w₁ v - vecMulVec w₂ v :=
  ext fun _ _ => sub_mul _ _ _

theorem vecMulVec_sub (w : m → α) (v₁ v₂ : n → α) :
    vecMulVec w (v₁ - v₂) = vecMulVec w v₁ - vecMulVec w v₂ :=
  ext fun _ _ => mul_sub _ _ _

end NonUnitalNonAssocRing

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α]

theorem mulVec_transpose [Fintype m] (A : Matrix m n α) (x : m → α) : Aᵀ *ᵥ x = x ᵥ* A := by
  ext
  apply dotProduct_comm

theorem vecMul_transpose [Fintype n] (A : Matrix m n α) (x : n → α) : x ᵥ* Aᵀ = A *ᵥ x := by
  ext
  apply dotProduct_comm

theorem mulVec_vecMul [Fintype n] [Fintype o] (A : Matrix m n α) (B : Matrix o n α) (x : o → α) :
    A *ᵥ (x ᵥ* B) = (A * Bᵀ) *ᵥ x := by rw [← mulVec_mulVec, mulVec_transpose]

theorem vecMul_mulVec [Fintype m] [Fintype n] (A : Matrix m n α) (B : Matrix m o α) (x : n → α) :
    (A *ᵥ x) ᵥ* B = x ᵥ* (Aᵀ * B) := by rw [← vecMul_vecMul, vecMul_transpose]

end NonUnitalCommSemiring

section Semiring

variable [Semiring R]

lemma mulVec_injective_of_isUnit [Fintype m] [DecidableEq m] {A : Matrix m m R}
    (ha : IsUnit A) : Function.Injective A.mulVec :=
  isLeftRegular_iff_mulVec_injective.1 ha.isRegular.left

lemma vecMul_injective_of_isUnit [Fintype m] [DecidableEq m] {A : Matrix m m R}
    (ha : IsUnit A) : Function.Injective A.vecMul :=
  isRightRegular_iff_vecMul_injective.1 ha.isRegular.right

lemma pow_row_eq_zero_of_le [Fintype n] [DecidableEq n] {M : Matrix n n R} {k l : ℕ} {i : n}
    (h : (M ^ k).row i = 0) (h' : k ≤ l) :
    (M ^ l).row i = 0 := by
  replace h' : l = k + (l - k) := by omega
  rw [← single_one_vecMul] at h ⊢
  rw [h', pow_add, ← vecMul_vecMul, h, zero_vecMul]

lemma pow_col_eq_zero_of_le [Fintype n] [DecidableEq n] {M : Matrix n n R} {k l : ℕ} {i : n}
    (h : (M ^ k).col i = 0) (h' : k ≤ l) :
    (M ^ l).col i = 0 := by
  replace h' : l = (l - k) + k := by omega
  rw [← mulVec_single_one] at h ⊢
  rw [h', pow_add, ← mulVec_mulVec, h, mulVec_zero]

end Semiring

section CommSemiring

variable [CommSemiring α]

@[deprecated mulVec_smul (since := "2025-08-14")]
theorem mulVec_smul_assoc [Fintype n] (A : Matrix m n α) (b : n → α) (a : α) :
    A *ᵥ (a • b) = a • A *ᵥ b :=
  mulVec_smul _ _ _

end CommSemiring

section NonAssocRing

variable [NonAssocRing α]

variable [Fintype m] [DecidableEq m]

@[simp]
theorem intCast_mulVec (x : ℤ) (v : m → α) : x *ᵥ v = (x : α) • v :=
  diagonal_const_mulVec _ _

@[simp]
theorem vecMul_intCast (x : ℤ) (v : m → α) : v ᵥ* x = MulOpposite.op (x : α) • v :=
  vecMul_diagonal_const _ _

end NonAssocRing

section Transpose

open Matrix

@[simp]
theorem transpose_mul [AddCommMonoid α] [CommMagma α] [Fintype n] (M : Matrix m n α)
    (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ := by
  ext
  apply dotProduct_comm

variable (m n α)

end Transpose

theorem submatrix_mul [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p q : Type*}
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : l → m) (e₂ : o → n) (e₃ : q → p)
    (he₂ : Function.Bijective e₂) :
    (M * N).submatrix e₁ e₃ = M.submatrix e₁ e₂ * N.submatrix e₂ e₃ :=
  ext fun _ _ => (he₂.sum_comp _).symm

/-! `simp` lemmas for `Matrix.submatrix`s interaction with `Matrix.diagonal`, `1`, and `Matrix.mul`
for when the mappings are bundled. -/

@[simp]
theorem submatrix_mul_equiv [Fintype n] [Fintype o] [AddCommMonoid α] [Mul α] {p q : Type*}
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : l → m) (e₂ : o ≃ n) (e₃ : q → p) :
    M.submatrix e₁ e₂ * N.submatrix e₂ e₃ = (M * N).submatrix e₁ e₃ :=
  (submatrix_mul M N e₁ e₂ e₃ e₂.bijective).symm

theorem submatrix_mulVec_equiv [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α]
    (M : Matrix m n α) (v : o → α) (e₁ : l → m) (e₂ : o ≃ n) :
    M.submatrix e₁ e₂ *ᵥ v = (M *ᵥ (v ∘ e₂.symm)) ∘ e₁ :=
  funext fun _ => Eq.symm (dotProduct_comp_equiv_symm _ _ _)

@[simp]
theorem submatrix_id_mul_left [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p : Type*}
    (M : Matrix m n α) (N : Matrix o p α) (e₁ : l → m) (e₂ : n ≃ o) :
    M.submatrix e₁ id * N.submatrix e₂ id = M.submatrix e₁ e₂.symm * N := by
  ext; simp [mul_apply, ← e₂.bijective.sum_comp]

@[simp]
theorem submatrix_id_mul_right [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p : Type*}
    (M : Matrix m n α) (N : Matrix o p α) (e₁ : l → p) (e₂ : o ≃ n) :
    M.submatrix id e₂ * N.submatrix id e₁ = M * N.submatrix e₂.symm e₁ := by
  ext; simp [mul_apply, ← e₂.bijective.sum_comp]

theorem submatrix_vecMul_equiv [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (M : Matrix m n α) (v : l → α) (e₁ : l ≃ m) (e₂ : o → n) :
    v ᵥ* M.submatrix e₁ e₂ = ((v ∘ e₁.symm) ᵥ* M) ∘ e₂ :=
  funext fun _ => Eq.symm (comp_equiv_symm_dotProduct _ _ _)

theorem mul_submatrix_one [Fintype n] [Finite o] [NonAssocSemiring α] [DecidableEq o] (e₁ : n ≃ o)
    (e₂ : l → o) (M : Matrix m n α) :
    M * (1 : Matrix o o α).submatrix e₁ e₂ = submatrix M id (e₁.symm ∘ e₂) := by
  cases nonempty_fintype o
  let A := M.submatrix id e₁.symm
  have : M = A.submatrix id e₁ := by
    simp only [A, submatrix_submatrix, Function.comp_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this, submatrix_mul_equiv]
  simp only [A, Matrix.mul_one, submatrix_submatrix, Function.comp_id, submatrix_id_id,
    Equiv.symm_comp_self]

theorem one_submatrix_mul [Fintype m] [Finite o] [NonAssocSemiring α] [DecidableEq o] (e₁ : l → o)
    (e₂ : m ≃ o) (M : Matrix m n α) :
    ((1 : Matrix o o α).submatrix e₁ e₂) * M = submatrix M (e₂.symm ∘ e₁) id := by
  cases nonempty_fintype o
  let A := M.submatrix e₂.symm id
  have : M = A.submatrix e₂ id := by
    simp only [A, submatrix_submatrix, Function.comp_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this, submatrix_mul_equiv]
  simp only [A, Matrix.one_mul, submatrix_submatrix, Function.comp_id, submatrix_id_id,
    Equiv.symm_comp_self]

theorem submatrix_mul_transpose_submatrix [Fintype m] [Fintype n] [AddCommMonoid α] [Mul α]
    (e : m ≃ n) (M : Matrix m n α) : M.submatrix id e * Mᵀ.submatrix e id = M * Mᵀ := by
  rw [submatrix_mul_equiv, submatrix_id_id]

end Matrix

namespace RingHom

variable [Fintype n] [NonAssocSemiring α] [NonAssocSemiring β]

theorem map_matrix_mul (M : Matrix m n α) (N : Matrix n o α) (i : m) (j : o) (f : α →+* β) :
    f ((M * N) i j) = (M.map f * N.map f) i j := by
  simp [Matrix.mul_apply, map_sum]

theorem map_dotProduct [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (v w : n → R) :
    f (v ⬝ᵥ w) = f ∘ v ⬝ᵥ f ∘ w := by
  simp only [dotProduct, map_sum f, f.map_mul, Function.comp]

theorem map_vecMul [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (M : Matrix n m R)
    (v : n → R) (i : m) : f ((v ᵥ* M) i) = ((f ∘ v) ᵥ* M.map f) i := by
  simp only [Matrix.vecMul, Matrix.map_apply, RingHom.map_dotProduct, Function.comp_def]

theorem map_mulVec [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (M : Matrix m n R)
    (v : n → R) (i : m) : f ((M *ᵥ v) i) = (M.map f *ᵥ (f ∘ v)) i := by
  simp only [Matrix.mulVec, Matrix.map_apply, RingHom.map_dotProduct, Function.comp_def]

end RingHom
