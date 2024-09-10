/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.RingEquiv
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Matrices

This file defines basic properties of matrices.

Matrices with rows indexed by `m`, columns indexed by `n`, and entries of type `α` are represented
with `Matrix m n α`. For the typical approach of counting rows and columns,
`Matrix (Fin m) (Fin n) α` can be used.

## Notation

The locale `Matrix` gives the following notation:

* `⬝ᵥ` for `Matrix.dotProduct`
* `*ᵥ` for `Matrix.mulVec`
* `ᵥ*` for `Matrix.vecMul`
* `ᵀ` for `Matrix.transpose`
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


universe u u' v w

/-- `Matrix m n R` is the type of matrices with entries in `R`, whose rows are indexed by `m`
and whose columns are indexed by `n`. -/
def Matrix (m : Type u) (n : Type u') (α : Type v) : Type max u u' v :=
  m → n → α

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}
variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix

section Ext

variable {M N : Matrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩

@[ext]
theorem ext : (∀ i j, M i j = N i j) → M = N :=
  ext_iff.mp

end Ext

/-- Cast a function into a matrix.

The two sides of the equivalence are definitionally equal types. We want to use an explicit cast
to distinguish the types because `Matrix` has different instances to pi types (such as `Pi.mul`,
which performs elementwise multiplication, vs `Matrix.mul`).

If you are defining a matrix, in terms of its entries, use `of (fun i j ↦ _)`. The
purpose of this approach is to ensure that terms of the form `(fun i j ↦ _) * (fun i j ↦ _)` do not
appear, as the type of `*` can be misleading.

Porting note: In Lean 3, it is also safe to use pattern matching in a definition as `| i j := _`,
which can only be unfolded when fully-applied. leanprover/lean4#2042 means this does not
(currently) work in Lean 4.
-/
def of : (m → n → α) ≃ Matrix m n α :=
  Equiv.refl _

@[simp]
theorem of_apply (f : m → n → α) (i j) : of f i j = f i j :=
  rfl

@[simp]
theorem of_symm_apply (f : Matrix m n α) (i j) : of.symm f i j = f i j :=
  rfl

/-- `M.map f` is the matrix obtained by applying `f` to each entry of the matrix `M`.

This is available in bundled forms as:
* `AddMonoidHom.mapMatrix`
* `LinearMap.mapMatrix`
* `RingHom.mapMatrix`
* `AlgHom.mapMatrix`
* `Equiv.mapMatrix`
* `AddEquiv.mapMatrix`
* `LinearEquiv.mapMatrix`
* `RingEquiv.mapMatrix`
* `AlgEquiv.mapMatrix`
-/
def map (M : Matrix m n α) (f : α → β) : Matrix m n β :=
  of fun i j => f (M i j)

@[simp]
theorem map_apply {M : Matrix m n α} {f : α → β} {i : m} {j : n} : M.map f i j = f (M i j) :=
  rfl

@[simp]
theorem map_id (M : Matrix m n α) : M.map id = M := by
  ext
  rfl

@[simp]
theorem map_id' (M : Matrix m n α) : M.map (·) = M := map_id M

@[simp]
theorem map_map {M : Matrix m n α} {β γ : Type*} {f : α → β} {g : β → γ} :
    (M.map f).map g = M.map (g ∘ f) := by
  ext
  rfl

theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective fun M : Matrix m n α => M.map f := fun _ _ h =>
  ext fun i j => hf <| ext_iff.mpr h i j

/-- The transpose of a matrix. -/
def transpose (M : Matrix m n α) : Matrix n m α :=
  of fun x y => M y x

-- TODO: set as an equation lemma for `transpose`, see mathlib4#3024
@[simp]
theorem transpose_apply (M : Matrix m n α) (i j) : transpose M i j = M j i :=
  rfl

@[inherit_doc]
scoped postfix:1024 "ᵀ" => Matrix.transpose

/-- The conjugate transpose of a matrix defined in term of `star`. -/
def conjTranspose [Star α] (M : Matrix m n α) : Matrix n m α :=
  M.transpose.map star

@[inherit_doc]
scoped postfix:1024 "ᴴ" => Matrix.conjTranspose

instance inhabited [Inhabited α] : Inhabited (Matrix m n α) :=
  inferInstanceAs <| Inhabited <| m → n → α

-- Porting note: new, Lean3 found this automatically
instance decidableEq [DecidableEq α] [Fintype m] [Fintype n] : DecidableEq (Matrix m n α) :=
  Fintype.decidablePiFintype

instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (α) [Fintype α] :
    Fintype (Matrix m n α) := inferInstanceAs (Fintype (m → n → α))

instance {n m} [Finite m] [Finite n] (α) [Finite α] :
    Finite (Matrix m n α) := inferInstanceAs (Finite (m → n → α))

instance add [Add α] : Add (Matrix m n α) :=
  Pi.instAdd

instance addSemigroup [AddSemigroup α] : AddSemigroup (Matrix m n α) :=
  Pi.addSemigroup

instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (Matrix m n α) :=
  Pi.addCommSemigroup

instance zero [Zero α] : Zero (Matrix m n α) :=
  Pi.instZero

instance addZeroClass [AddZeroClass α] : AddZeroClass (Matrix m n α) :=
  Pi.addZeroClass

instance addMonoid [AddMonoid α] : AddMonoid (Matrix m n α) :=
  Pi.addMonoid

instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (Matrix m n α) :=
  Pi.addCommMonoid

instance neg [Neg α] : Neg (Matrix m n α) :=
  Pi.instNeg

instance sub [Sub α] : Sub (Matrix m n α) :=
  Pi.instSub

instance addGroup [AddGroup α] : AddGroup (Matrix m n α) :=
  Pi.addGroup

instance addCommGroup [AddCommGroup α] : AddCommGroup (Matrix m n α) :=
  Pi.addCommGroup

instance unique [Unique α] : Unique (Matrix m n α) :=
  Pi.unique

instance subsingleton [Subsingleton α] : Subsingleton (Matrix m n α) :=
  inferInstanceAs <| Subsingleton <| m → n → α

instance nonempty [Nonempty m] [Nonempty n] [Nontrivial α] : Nontrivial (Matrix m n α) :=
  Function.nontrivial

instance smul [SMul R α] : SMul R (Matrix m n α) :=
  Pi.instSMul

instance smulCommClass [SMul R α] [SMul S α] [SMulCommClass R S α] :
    SMulCommClass R S (Matrix m n α) :=
  Pi.smulCommClass

instance isScalarTower [SMul R S] [SMul R α] [SMul S α] [IsScalarTower R S α] :
    IsScalarTower R S (Matrix m n α) :=
  Pi.isScalarTower

instance isCentralScalar [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α] :
    IsCentralScalar R (Matrix m n α) :=
  Pi.isCentralScalar

instance mulAction [Monoid R] [MulAction R α] : MulAction R (Matrix m n α) :=
  Pi.mulAction _

instance distribMulAction [Monoid R] [AddMonoid α] [DistribMulAction R α] :
    DistribMulAction R (Matrix m n α) :=
  Pi.distribMulAction _

instance module [Semiring R] [AddCommMonoid α] [Module R α] : Module R (Matrix m n α) :=
  Pi.module _ _ _

section

#adaptation_note
/--
After https://github.com/leanprover/lean4/pull/4481
the `simpNF` linter incorrectly claims this lemma can't be applied by `simp`.
-/
@[simp, nolint simpNF]
theorem zero_apply [Zero α] (i : m) (j : n) : (0 : Matrix m n α) i j = 0 := rfl

@[simp]
theorem add_apply [Add α] (A B : Matrix m n α) (i : m) (j : n) :
    (A + B) i j = (A i j) + (B i j) := rfl

@[simp]
theorem smul_apply [SMul β α] (r : β) (A : Matrix m n α) (i : m) (j : n) :
    (r • A) i j = r • (A i j) := rfl

@[simp]
theorem sub_apply [Sub α] (A B : Matrix m n α) (i : m) (j : n) :
    (A - B) i j = (A i j) - (B i j) := rfl

@[simp]
theorem neg_apply [Neg α] (A : Matrix m n α) (i : m) (j : n) :
    (-A) i j = -(A i j) := rfl

end

/-! simp-normal form pulls `of` to the outside. -/

@[simp]
theorem of_zero [Zero α] : of (0 : m → n → α) = 0 :=
  rfl

@[simp]
theorem of_add_of [Add α] (f g : m → n → α) : of f + of g = of (f + g) :=
  rfl

@[simp]
theorem of_sub_of [Sub α] (f g : m → n → α) : of f - of g = of (f - g) :=
  rfl

@[simp]
theorem neg_of [Neg α] (f : m → n → α) : -of f = of (-f) :=
  rfl

@[simp]
theorem smul_of [SMul R α] (r : R) (f : m → n → α) : r • of f = of (r • f) :=
  rfl

@[simp]
protected theorem map_zero [Zero α] [Zero β] (f : α → β) (h : f 0 = 0) :
    (0 : Matrix m n α).map f = 0 := by
  ext
  simp [h]

protected theorem map_add [Add α] [Add β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂)
    (M N : Matrix m n α) : (M + N).map f = M.map f + N.map f :=
  ext fun _ _ => hf _ _

protected theorem map_sub [Sub α] [Sub β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ - a₂) = f a₁ - f a₂)
    (M N : Matrix m n α) : (M - N).map f = M.map f - N.map f :=
  ext fun _ _ => hf _ _

theorem map_smul [SMul R α] [SMul R β] (f : α → β) (r : R) (hf : ∀ a, f (r • a) = r • f a)
    (M : Matrix m n α) : (r • M).map f = r • M.map f :=
  ext fun _ _ => hf _

/-- The scalar action via `Mul.toSMul` is transformed by the same map as the elements
of the matrix, when `f` preserves multiplication. -/
theorem map_smul' [Mul α] [Mul β] (f : α → β) (r : α) (A : Matrix n n α)
    (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) : (r • A).map f = f r • A.map f :=
  ext fun _ _ => hf _ _

/-- The scalar action via `mul.toOppositeSMul` is transformed by the same map as the
elements of the matrix, when `f` preserves multiplication. -/
theorem map_op_smul' [Mul α] [Mul β] (f : α → β) (r : α) (A : Matrix n n α)
    (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) :
    (MulOpposite.op r • A).map f = MulOpposite.op (f r) • A.map f :=
  ext fun _ _ => hf _ _

theorem _root_.IsSMulRegular.matrix [SMul R S] {k : R} (hk : IsSMulRegular S k) :
    IsSMulRegular (Matrix m n S) k :=
  IsSMulRegular.pi fun _ => IsSMulRegular.pi fun _ => hk

theorem _root_.IsLeftRegular.matrix [Mul α] {k : α} (hk : IsLeftRegular k) :
    IsSMulRegular (Matrix m n α) k :=
  hk.isSMulRegular.matrix

instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext i
    exact isEmptyElim i⟩

instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext i j
    exact isEmptyElim j⟩

end Matrix

open Matrix

namespace Matrix

section Diagonal

variable [DecidableEq n]

/-- `diagonal d` is the square matrix such that `(diagonal d) i i = d i` and `(diagonal d) i j = 0`
if `i ≠ j`.

Note that bundled versions exist as:
* `Matrix.diagonalAddMonoidHom`
* `Matrix.diagonalLinearMap`
* `Matrix.diagonalRingHom`
* `Matrix.diagonalAlgHom`
-/
def diagonal [Zero α] (d : n → α) : Matrix n n α :=
  of fun i j => if i = j then d i else 0

-- TODO: set as an equation lemma for `diagonal`, see mathlib4#3024
theorem diagonal_apply [Zero α] (d : n → α) (i j) : diagonal d i j = if i = j then d i else 0 :=
  rfl

@[simp]
theorem diagonal_apply_eq [Zero α] (d : n → α) (i : n) : (diagonal d) i i = d i := by
  simp [diagonal]

@[simp]
theorem diagonal_apply_ne [Zero α] (d : n → α) {i j : n} (h : i ≠ j) : (diagonal d) i j = 0 := by
  simp [diagonal, h]

theorem diagonal_apply_ne' [Zero α] (d : n → α) {i j : n} (h : j ≠ i) : (diagonal d) i j = 0 :=
  diagonal_apply_ne d h.symm

@[simp]
theorem diagonal_eq_diagonal_iff [Zero α] {d₁ d₂ : n → α} :
    diagonal d₁ = diagonal d₂ ↔ ∀ i, d₁ i = d₂ i :=
  ⟨fun h i => by simpa using congr_arg (fun m : Matrix n n α => m i i) h, fun h => by
    rw [show d₁ = d₂ from funext h]⟩

theorem diagonal_injective [Zero α] : Function.Injective (diagonal : (n → α) → Matrix n n α) :=
  fun d₁ d₂ h => funext fun i => by simpa using Matrix.ext_iff.mpr h i i

@[simp]
theorem diagonal_zero [Zero α] : (diagonal fun _ => 0 : Matrix n n α) = 0 := by
  ext
  simp [diagonal]

@[simp]
theorem diagonal_transpose [Zero α] (v : n → α) : (diagonal v)ᵀ = diagonal v := by
  ext i j
  by_cases h : i = j
  · simp [h, transpose]
  · simp [h, transpose, diagonal_apply_ne' _ h]

@[simp]
theorem diagonal_add [AddZeroClass α] (d₁ d₂ : n → α) :
    diagonal d₁ + diagonal d₂ = diagonal fun i => d₁ i + d₂ i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

@[simp]
theorem diagonal_smul [Zero α] [SMulZeroClass R α] (r : R) (d : n → α) :
    diagonal (r • d) = r • diagonal d := by
  ext i j
  by_cases h : i = j <;> simp [h]

@[simp]
theorem diagonal_neg [NegZeroClass α] (d : n → α) :
    -diagonal d = diagonal fun i => -d i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

@[simp]
theorem diagonal_sub [SubNegZeroMonoid α] (d₁ d₂ : n → α) :
    diagonal d₁ - diagonal d₂ = diagonal fun i => d₁ i - d₂ i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

instance [Zero α] [NatCast α] : NatCast (Matrix n n α) where
  natCast m := diagonal fun _ => m

@[norm_cast]
theorem diagonal_natCast [Zero α] [NatCast α] (m : ℕ) : diagonal (fun _ : n => (m : α)) = m := rfl

@[norm_cast]
theorem diagonal_natCast' [Zero α] [NatCast α] (m : ℕ) : diagonal ((m : n → α)) = m := rfl

-- See note [no_index around OfNat.ofNat]
theorem diagonal_ofNat [Zero α] [NatCast α] (m : ℕ) [m.AtLeastTwo] :
    diagonal (fun _ : n => no_index (OfNat.ofNat m : α)) = OfNat.ofNat m := rfl

-- See note [no_index around OfNat.ofNat]
theorem diagonal_ofNat' [Zero α] [NatCast α] (m : ℕ) [m.AtLeastTwo] :
    diagonal (no_index (OfNat.ofNat m : n → α)) = OfNat.ofNat m := rfl

instance [Zero α] [IntCast α] : IntCast (Matrix n n α) where
  intCast m := diagonal fun _ => m

@[norm_cast]
theorem diagonal_intCast [Zero α] [IntCast α] (m : ℤ) : diagonal (fun _ : n => (m : α)) = m := rfl

@[norm_cast]
theorem diagonal_intCast' [Zero α] [IntCast α] (m : ℤ) : diagonal ((m : n → α)) = m := rfl

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

@[simp]
theorem diagonal_map [Zero α] [Zero β] {f : α → β} (h : f 0 = 0) {d : n → α} :
    (diagonal d).map f = diagonal fun m => f (d m) := by
  ext
  simp only [diagonal_apply, map_apply]
  split_ifs <;> simp [h]

protected theorem map_natCast [AddMonoidWithOne α] [AddMonoidWithOne β]
    {f : α → β} (h : f 0 = 0) (d : ℕ) :
    (d : Matrix n n α).map f = diagonal (fun _ => f d) :=
  diagonal_map h

-- See note [no_index around OfNat.ofNat]
protected theorem map_ofNat [AddMonoidWithOne α] [AddMonoidWithOne β]
    {f : α → β} (h : f 0 = 0) (d : ℕ) [d.AtLeastTwo] :
    (no_index (OfNat.ofNat d) : Matrix n n α).map f = diagonal (fun _ => f (OfNat.ofNat d)) :=
  diagonal_map h

protected theorem map_intCast [AddGroupWithOne α] [AddGroupWithOne β]
    {f : α → β} (h : f 0 = 0) (d : ℤ) :
    (d : Matrix n n α).map f = diagonal (fun _ => f d) :=
  diagonal_map h

@[simp]
theorem diagonal_conjTranspose [AddMonoid α] [StarAddMonoid α] (v : n → α) :
    (diagonal v)ᴴ = diagonal (star v) := by
  rw [conjTranspose, diagonal_transpose, diagonal_map (star_zero _)]
  rfl

section One

variable [Zero α] [One α]

instance one : One (Matrix n n α) :=
  ⟨diagonal fun _ => 1⟩

@[simp]
theorem diagonal_one : (diagonal fun _ => 1 : Matrix n n α) = 1 :=
  rfl

theorem one_apply {i j} : (1 : Matrix n n α) i j = if i = j then 1 else 0 :=
  rfl

@[simp]
theorem one_apply_eq (i) : (1 : Matrix n n α) i i = 1 :=
  diagonal_apply_eq _ i

@[simp]
theorem one_apply_ne {i j} : i ≠ j → (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne _

theorem one_apply_ne' {i j} : j ≠ i → (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne' _

@[simp]
theorem map_one [Zero β] [One β] (f : α → β) (h₀ : f 0 = 0) (h₁ : f 1 = 1) :
    (1 : Matrix n n α).map f = (1 : Matrix n n β) := by
  ext
  simp only [one_apply, map_apply]
  split_ifs <;> simp [h₀, h₁]

-- Porting note: added implicit argument `(f := fun_ => α)`, why is that needed?
theorem one_eq_pi_single {i j} : (1 : Matrix n n α) i j = Pi.single (f := fun _ => α) i 1 j := by
  simp only [one_apply, Pi.single_apply, eq_comm]

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

instance instAddMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (Matrix n n α) where
  natCast_zero := show diagonal _ = _ by
    rw [Nat.cast_zero, diagonal_zero]
  natCast_succ n := show diagonal _ = diagonal _ + _ by
    rw [Nat.cast_succ, ← diagonal_add, diagonal_one]

instance instAddGroupWithOne [AddGroupWithOne α] : AddGroupWithOne (Matrix n n α) where
  intCast_ofNat n := show diagonal _ = diagonal _ by
    rw [Int.cast_natCast]
  intCast_negSucc n := show diagonal _ = -(diagonal _) by
    rw [Int.cast_negSucc, diagonal_neg]
  __ := addGroup
  __ := instAddMonoidWithOne

instance instAddCommMonoidWithOne [AddCommMonoidWithOne α] :
    AddCommMonoidWithOne (Matrix n n α) where
  __ := addCommMonoid
  __ := instAddMonoidWithOne

instance instAddCommGroupWithOne [AddCommGroupWithOne α] :
    AddCommGroupWithOne (Matrix n n α) where
  __ := addCommGroup
  __ := instAddGroupWithOne

end Diagonal

section Diag

/-- The diagonal of a square matrix. -/
-- @[simp] -- Porting note: simpNF does not like this.
def diag (A : Matrix n n α) (i : n) : α :=
  A i i

-- Porting note: new, because of removed `simp` above.
-- TODO: set as an equation lemma for `diag`, see mathlib4#3024
@[simp]
theorem diag_apply (A : Matrix n n α) (i) : diag A i = A i i :=
  rfl

@[simp]
theorem diag_diagonal [DecidableEq n] [Zero α] (a : n → α) : diag (diagonal a) = a :=
  funext <| @diagonal_apply_eq _ _ _ _ a

@[simp]
theorem diag_transpose (A : Matrix n n α) : diag Aᵀ = diag A :=
  rfl

@[simp]
theorem diag_zero [Zero α] : diag (0 : Matrix n n α) = 0 :=
  rfl

@[simp]
theorem diag_add [Add α] (A B : Matrix n n α) : diag (A + B) = diag A + diag B :=
  rfl

@[simp]
theorem diag_sub [Sub α] (A B : Matrix n n α) : diag (A - B) = diag A - diag B :=
  rfl

@[simp]
theorem diag_neg [Neg α] (A : Matrix n n α) : diag (-A) = -diag A :=
  rfl

@[simp]
theorem diag_smul [SMul R α] (r : R) (A : Matrix n n α) : diag (r • A) = r • diag A :=
  rfl

@[simp]
theorem diag_one [DecidableEq n] [Zero α] [One α] : diag (1 : Matrix n n α) = 1 :=
  diag_diagonal _

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

theorem diag_map {f : α → β} {A : Matrix n n α} : diag (A.map f) = f ∘ diag A :=
  rfl

@[simp]
theorem diag_conjTranspose [AddMonoid α] [StarAddMonoid α] (A : Matrix n n α) :
    diag Aᴴ = star (diag A) :=
  rfl

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

section DotProduct

variable [Fintype m] [Fintype n]

/-- `dotProduct v w` is the sum of the entrywise products `v i * w i` -/
def dotProduct [Mul α] [AddCommMonoid α] (v w : m → α) : α :=
  ∑ i, v i * w i

/- The precedence of 72 comes immediately after ` • ` for `SMul.smul`,
   so that `r₁ • a ⬝ᵥ r₂ • b` is parsed as `(r₁ • a) ⬝ᵥ (r₂ • b)` here. -/
@[inherit_doc]
scoped infixl:72 " ⬝ᵥ " => Matrix.dotProduct

theorem dotProduct_assoc [NonUnitalSemiring α] (u : m → α) (w : n → α) (v : Matrix m n α) :
    (fun j => u ⬝ᵥ fun i => v i j) ⬝ᵥ w = u ⬝ᵥ fun i => v i ⬝ᵥ w := by
  simpa [dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc] using Finset.sum_comm

theorem dotProduct_comm [AddCommMonoid α] [CommSemigroup α] (v w : m → α) : v ⬝ᵥ w = w ⬝ᵥ v := by
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
theorem sum_elim_dotProduct_sum_elim : Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
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
  -- Porting note: was `simp only` with all three lemmas
  rw [← dotProduct_comp_equiv_symm]; simp only [Function.comp, Equiv.apply_symm_apply]

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
  -- Porting note: (implicit arg) added `(f := fun _ => α)`
  have : ∀ j ≠ i, Pi.single (f := fun _ => α) i x j * v j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]
theorem dotProduct_single (x : α) (i : m) : v ⬝ᵥ Pi.single i x = v i * x := by
  -- Porting note: (implicit arg) added `(f := fun _ => α)`
  have : ∀ j ≠ i, v j * Pi.single (f := fun _ => α) i x j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

end NonUnitalNonAssocSemiringDecidable

section NonAssocSemiring

variable [NonAssocSemiring α]

@[simp]
theorem one_dotProduct_one : (1 : n → α) ⬝ᵥ 1 = Fintype.card n := by
  simp [dotProduct]

theorem dotProduct_single_one [DecidableEq n] (v : n → α) (i : n) :
    dotProduct v (Pi.single i 1) = v i := by
  rw [dotProduct_single, mul_one]

theorem single_one_dotProduct [DecidableEq n] (i : n) (v : n → α) :
    dotProduct (Pi.single i 1) v = v i := by
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

variable [Monoid R] [Mul α] [AddCommMonoid α] [DistribMulAction R α]

@[simp]
theorem smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m → α) :
    x • v ⬝ᵥ w = x • (v ⬝ᵥ w) := by simp [dotProduct, Finset.smul_sum, smul_mul_assoc]

@[simp]
theorem dotProduct_smul [SMulCommClass R α α] (x : R) (v w : m → α) :
    v ⬝ᵥ x • w = x • (v ⬝ᵥ w) := by simp [dotProduct, Finset.smul_sum, mul_smul_comm]

end DistribMulAction

section StarRing

variable [NonUnitalSemiring α] [StarRing α] (v w : m → α)

theorem star_dotProduct_star : star v ⬝ᵥ star w = star (w ⬝ᵥ v) := by simp [dotProduct]

theorem star_dotProduct : star v ⬝ᵥ w = star (star w ⬝ᵥ v) := by simp [dotProduct]

theorem dotProduct_star : v ⬝ᵥ star w = star (w ⬝ᵥ star v) := by simp [dotProduct]

end StarRing

end DotProduct

open Matrix

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
    {i k} : (M * N) i k = (fun j => M i j) ⬝ᵥ fun j => N j k :=
  rfl

theorem sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finset β) (g : β → Matrix m n α) :
    (∑ c ∈ s, g c) i j = ∑ c ∈ s, g c i j :=
  (congr_fun (s.sum_apply i g) j).trans (s.sum_apply j _)

theorem two_mul_expl {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
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
    one := 1
    one_mul := Matrix.one_mul
    mul_one := Matrix.mul_one }

@[simp]
theorem map_mul [Fintype n] {L : Matrix m n α} {M : Matrix n o α} [NonAssocSemiring β]
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

/-- `Matrix.diagonal` as a `RingHom`. -/
@[simps]
def diagonalRingHom [Fintype n] [DecidableEq n] : (n → α) →+* Matrix n n α :=
  { diagonalAddMonoidHom n α with
    toFun := diagonal
    map_one' := diagonal_one
    map_mul' := fun _ _ => (diagonal_mul_diagonal' _ _).symm }

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

theorem diagonal_pow [Fintype n] [DecidableEq n] (v : n → α) (k : ℕ) :
    diagonal v ^ k = diagonal (v ^ k) :=
  (map_pow (diagonalRingHom n α) v k).symm

@[simp]
theorem mul_mul_left [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α) :
    (of fun i j => a * M i j) * N = a • (M * N) :=
  smul_mul a M N

/-- The ring homomorphism `α →+* Matrix n n α`
sending `a` to the diagonal matrix with `a` on the diagonal.
-/
def scalar (n : Type u) [DecidableEq n] [Fintype n] : α →+* Matrix n n α :=
  (diagonalRingHom n α).comp <| Pi.constRingHom n α

section Scalar

variable [DecidableEq n] [Fintype n]

@[simp]
theorem scalar_apply (a : α) : scalar n a = diagonal fun _ => a :=
  rfl

theorem scalar_inj [Nonempty n] {r s : α} : scalar n r = scalar n s ↔ r = s :=
  (diagonal_injective.comp Function.const_injective).eq_iff

theorem scalar_commute_iff {r : α} {M : Matrix n n α} :
    Commute (scalar n r) M ↔ r • M = MulOpposite.op r • M := by
  simp_rw [Commute, SemiconjBy, scalar_apply, ← smul_eq_diagonal_mul, ← op_smul_eq_mul_diagonal]

theorem scalar_commute (r : α) (hr : ∀ r', Commute r r') (M : Matrix n n α) :
    Commute (scalar n r) M := scalar_commute_iff.2 <| ext fun _ _ => hr _

end Scalar

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

section Algebra

variable [Fintype n] [DecidableEq n]
variable [CommSemiring R] [Semiring α] [Semiring β] [Algebra R α] [Algebra R β]

instance instAlgebra : Algebra R (Matrix n n α) where
  toRingHom := (Matrix.scalar n).comp (algebraMap R α)
  commutes' r x := scalar_commute _ (fun r' => Algebra.commutes _ _) _
  smul_def' r x := by ext; simp [Matrix.scalar, Algebra.smul_def r]

theorem algebraMap_matrix_apply {r : R} {i j : n} :
    algebraMap R (Matrix n n α) r i j = if i = j then algebraMap R α r else 0 := by
  dsimp [algebraMap, Algebra.toRingHom, Matrix.scalar]
  split_ifs with h <;> simp [h, Matrix.one_apply_ne]

theorem algebraMap_eq_diagonal (r : R) :
    algebraMap R (Matrix n n α) r = diagonal (algebraMap R (n → α) r) := rfl

theorem algebraMap_eq_diagonalRingHom :
    algebraMap R (Matrix n n α) = (diagonalRingHom n α).comp (algebraMap R _) := rfl

@[simp]
theorem map_algebraMap (r : R) (f : α → β) (hf : f 0 = 0)
    (hf₂ : f (algebraMap R α r) = algebraMap R β r) :
    (algebraMap R (Matrix n n α) r).map f = algebraMap R (Matrix n n β) r := by
  rw [algebraMap_eq_diagonal, algebraMap_eq_diagonal, diagonal_map hf]
  -- Porting note: (congr) the remaining proof was
  -- ```
  -- congr 1
  -- simp only [hf₂, Pi.algebraMap_apply]
  -- ```
  -- But some `congr 1` doesn't quite work.
  simp only [Pi.algebraMap_apply, diagonal_eq_diagonal_iff]
  intro
  rw [hf₂]

variable (R)

/-- `Matrix.diagonal` as an `AlgHom`. -/
@[simps]
def diagonalAlgHom : (n → α) →ₐ[R] Matrix n n α :=
  { diagonalRingHom n α with
    toFun := diagonal
    commutes' := fun r => (algebraMap_eq_diagonal r).symm }

end Algebra

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

end AddEquiv

namespace LinearMap

variable [Semiring R] [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
variable [Module R α] [Module R β] [Module R γ]

/-- The `LinearMap` between spaces of matrices induced by a `LinearMap` between their
coefficients. This is `Matrix.map` as a `LinearMap`. -/
@[simps]
def mapMatrix (f : α →ₗ[R] β) : Matrix m n α →ₗ[R] Matrix m n β where
  toFun M := M.map f
  map_add' := Matrix.map_add f f.map_add
  map_smul' r := Matrix.map_smul f r (f.map_smul r)

@[simp]
theorem mapMatrix_id : LinearMap.id.mapMatrix = (LinearMap.id : Matrix m n α →ₗ[R] _) :=
  rfl

@[simp]
theorem mapMatrix_comp (f : β →ₗ[R] γ) (g : α →ₗ[R] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α →ₗ[R] _) :=
  rfl

end LinearMap

namespace LinearEquiv

variable [Semiring R] [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
variable [Module R α] [Module R β] [Module R γ]

/-- The `LinearEquiv` between spaces of matrices induced by a `LinearEquiv` between their
coefficients. This is `Matrix.map` as a `LinearEquiv`. -/
@[simps apply]
def mapMatrix (f : α ≃ₗ[R] β) : Matrix m n α ≃ₗ[R] Matrix m n β :=
  { f.toEquiv.mapMatrix,
    f.toLinearMap.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }

@[simp]
theorem mapMatrix_refl : (LinearEquiv.refl R α).mapMatrix = LinearEquiv.refl R (Matrix m n α) :=
  rfl

@[simp]
theorem mapMatrix_symm (f : α ≃ₗ[R] β) :
    f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ₗ[R] _) :=
  rfl

@[simp]
theorem mapMatrix_trans (f : α ≃ₗ[R] β) (g : β ≃ₗ[R] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ₗ[R] _) :=
  rfl

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
    map_mul' := fun L M => Matrix.map_mul }

@[simp]
theorem mapMatrix_id : (RingHom.id α).mapMatrix = RingHom.id (Matrix m m α) :=
  rfl

@[simp]
theorem mapMatrix_comp (f : β →+* γ) (g : α →+* β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α →+* _) :=
  rfl

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

end RingEquiv

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

end AlgEquiv

open Matrix

namespace Matrix

/-- For two vectors `w` and `v`, `vecMulVec w v i j` is defined to be `w i * v j`.
    Put another way, `vecMulVec w v` is exactly `col w * row v`. -/
def vecMulVec [Mul α] (w : m → α) (v : n → α) : Matrix m n α :=
  of fun x y => w x * v y

-- TODO: set as an equation lemma for `vecMulVec`, see mathlib4#3024
theorem vecMulVec_apply [Mul α] (w : m → α) (v : n → α) (i j) : vecMulVec w v i j = w i * v j :=
  rfl

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

/--
`M *ᵥ v` (notation for `mulVec M v`) is the matrix-vector product of matrix `M` and vector `v`,
where `v` is seen as a column vector.
Put another way, `M *ᵥ v` is the vector whose entries are those of `M * col v` (see `col_mulVec`).

The notation has precedence 73, which comes immediately before ` ⬝ᵥ ` for `Matrix.dotProduct`,
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

The notation has precedence 73, which comes immediately before ` ⬝ᵥ ` for `Matrix.dotProduct`,
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

theorem smul_mulVec_assoc [Fintype n] [Monoid R] [DistribMulAction R α] [IsScalarTower R α α]
    (a : R) (A : Matrix m n α) (b : n → α) : (a • A) *ᵥ b = a • A *ᵥ b := by
  ext
  apply smul_dotProduct

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

theorem vecMul_smul [Fintype n] [Monoid R] [NonUnitalNonAssocSemiring S] [DistribMulAction R S]
    [IsScalarTower R S S] (M : Matrix n m S) (b : R) (v : n → S) :
    (b • v) ᵥ* M = b • v ᵥ* M := by
  ext i
  simp only [vecMul, dotProduct, Finset.smul_sum, Pi.smul_apply, smul_mul_assoc]

theorem mulVec_smul [Fintype n] [Monoid R] [NonUnitalNonAssocSemiring S] [DistribMulAction R S]
    [SMulCommClass R S S] (M : Matrix m n S) (b : R) (v : n → S) :
    M *ᵥ (b • v) = b • M *ᵥ v := by
  ext i
  simp only [mulVec, dotProduct, Finset.smul_sum, Pi.smul_apply, mul_smul_comm]

@[simp]
theorem mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
    (j : n) (x : R) : M *ᵥ Pi.single j x = fun i => M i j * x :=
  funext fun _ => dotProduct_single _ _ _

@[simp]
theorem single_vecMul [Fintype m] [DecidableEq m] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
    (i : m) (x : R) : Pi.single i x ᵥ* M = fun j => x * M i j :=
  funext fun _ => single_dotProduct _ _ _

theorem mulVec_single_one [Fintype n] [DecidableEq n] [NonAssocSemiring R]
    (M : Matrix m n R) (j : n) :
    M *ᵥ Pi.single j 1 = Mᵀ j := by ext; simp

theorem single_one_vecMul [Fintype m] [DecidableEq m] [NonAssocSemiring R]
    (i : m) (M : Matrix m n R) :
    Pi.single i 1 ᵥ* M = M i := by simp

-- @[simp] -- Porting note: not in simpNF
theorem diagonal_mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n → R)
    (j : n) (x : R) : diagonal v *ᵥ Pi.single j x = Pi.single j (v j * x) := by
  ext i
  rw [mulVec_diagonal]
  exact Pi.apply_single (fun i x => v i * x) (fun i => mul_zero _) j x i

-- @[simp] -- Porting note: not in simpNF
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

theorem star_mulVec [Fintype n] [StarRing α] (M : Matrix m n α) (v : n → α) :
    star (M *ᵥ v) = star v ᵥ* Mᴴ :=
  funext fun _ => (star_dotProduct_star _ _).symm

theorem star_vecMul [Fintype m] [StarRing α] (M : Matrix m n α) (v : m → α) :
    star (v ᵥ* M) = Mᴴ *ᵥ star v :=
  funext fun _ => (star_dotProduct_star _ _).symm

theorem mulVec_conjTranspose [Fintype m] [StarRing α] (A : Matrix m n α) (x : m → α) :
    Aᴴ *ᵥ x = star (star x ᵥ* A) :=
  funext fun _ => star_dotProduct _ _

theorem vecMul_conjTranspose [Fintype n] [StarRing α] (A : Matrix m n α) (x : n → α) :
    x ᵥ* Aᴴ = star (A *ᵥ star x) :=
  funext fun _ => dotProduct_star _ _

theorem mul_mul_apply [Fintype n] (A B C : Matrix n n α) (i j : n) :
    (A * B * C) i j = A i ⬝ᵥ B *ᵥ (Cᵀ j) := by
  rw [Matrix.mul_assoc]
  simp only [mul_apply, dotProduct, mulVec]
  rfl

end NonUnitalSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

theorem mulVec_one [Fintype n] (A : Matrix m n α) : A *ᵥ 1 = fun i => ∑ j, A i j := by
  ext; simp [mulVec, dotProduct]

theorem vec_one_mul [Fintype m] (A : Matrix m n α) : 1 ᵥ* A = fun j => ∑ i, A i j := by
  ext; simp [vecMul, dotProduct]

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


-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_mulVec (x : ℕ) [x.AtLeastTwo] (v : m → α) :
    OfNat.ofNat (no_index x) *ᵥ v = (OfNat.ofNat x : α) • v :=
  natCast_mulVec _ _

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem vecMul_ofNat (x : ℕ) [x.AtLeastTwo] (v : m → α) :
    v ᵥ* OfNat.ofNat (no_index x) = MulOpposite.op (OfNat.ofNat x : α) • v :=
  vecMul_natCast _ _

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

theorem neg_vecMul [Fintype m] (v : m → α) (A : Matrix m n α) : (-v) ᵥ* A = - (v ᵥ* A) := by
  ext
  apply neg_dotProduct

theorem vecMul_neg [Fintype m] (v : m → α) (A : Matrix m n α) : v ᵥ* (-A) = - (v ᵥ* A) := by
  ext
  apply dotProduct_neg

lemma neg_vecMul_neg [Fintype m] (v : m → α) (A : Matrix m n α) : (-v) ᵥ* (-A) = v ᵥ* A := by
  rw [vecMul_neg, neg_vecMul, neg_neg]

theorem neg_mulVec [Fintype n] (v : n → α) (A : Matrix m n α) : (-A) *ᵥ v = - (A *ᵥ v) := by
  ext
  apply neg_dotProduct

theorem mulVec_neg [Fintype n] (v : n → α) (A : Matrix m n α) : A *ᵥ (-v) = - (A *ᵥ v) := by
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

section CommSemiring

variable [CommSemiring α]

theorem mulVec_smul_assoc [Fintype n] (A : Matrix m n α) (b : n → α) (a : α) :
    A *ᵥ (a • b) = a • A *ᵥ b := by
  ext
  apply dotProduct_smul

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
theorem transpose_transpose (M : Matrix m n α) : Mᵀᵀ = M := by
  ext
  rfl

theorem transpose_injective : Function.Injective (transpose : Matrix m n α → Matrix n m α) :=
  fun _ _ h => ext fun i j => ext_iff.2 h j i

@[simp] theorem transpose_inj {A B : Matrix m n α} : Aᵀ = Bᵀ ↔ A = B := transpose_injective.eq_iff

@[simp]
theorem transpose_eq_diagonal [DecidableEq n] [Zero α] {M : Matrix n n α} {v : n → α} :
    Mᵀ = diagonal v ↔ M = diagonal v :=
  (Function.Involutive.eq_iff transpose_transpose).trans <|
    by rw [diagonal_transpose]

@[simp]
theorem transpose_zero [Zero α] : (0 : Matrix m n α)ᵀ = 0 := rfl

@[simp]
theorem transpose_eq_zero [Zero α] {M : Matrix m n α} : Mᵀ = 0 ↔ M = 0 := transpose_inj

@[simp]
theorem transpose_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α)ᵀ = 1 :=
  diagonal_transpose _

@[simp]
theorem transpose_eq_one [DecidableEq n] [Zero α] [One α] {M : Matrix n n α} : Mᵀ = 1 ↔ M = 1 :=
  transpose_eq_diagonal

@[simp]
theorem transpose_natCast [DecidableEq n] [AddMonoidWithOne α] (d : ℕ) :
    (d : Matrix n n α)ᵀ = d :=
  diagonal_transpose _

@[simp]
theorem transpose_eq_natCast [DecidableEq n] [AddMonoidWithOne α] {M : Matrix n n α} {d : ℕ} :
    Mᵀ = d ↔ M = d :=
  transpose_eq_diagonal

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem transpose_ofNat [DecidableEq n] [AddMonoidWithOne α] (d : ℕ) [d.AtLeastTwo] :
    (no_index (OfNat.ofNat d) : Matrix n n α)ᵀ = OfNat.ofNat d :=
  transpose_natCast _

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem transpose_eq_ofNat [DecidableEq n] [AddMonoidWithOne α]
    {M : Matrix n n α} {d : ℕ} [d.AtLeastTwo] :
    Mᵀ = no_index (OfNat.ofNat d) ↔ M = OfNat.ofNat d :=
  transpose_eq_diagonal

@[simp]
theorem transpose_intCast [DecidableEq n] [AddGroupWithOne α] (d : ℤ) :
    (d : Matrix n n α)ᵀ = d :=
  diagonal_transpose _

@[simp]
theorem transpose_eq_intCast [DecidableEq n] [AddGroupWithOne α]
    {M : Matrix n n α} {d : ℤ} :
    Mᵀ = d ↔ M = d :=
  transpose_eq_diagonal

@[simp]
theorem transpose_add [Add α] (M : Matrix m n α) (N : Matrix m n α) : (M + N)ᵀ = Mᵀ + Nᵀ := by
  ext
  simp

@[simp]
theorem transpose_sub [Sub α] (M : Matrix m n α) (N : Matrix m n α) : (M - N)ᵀ = Mᵀ - Nᵀ := by
  ext
  simp

@[simp]
theorem transpose_mul [AddCommMonoid α] [CommSemigroup α] [Fintype n] (M : Matrix m n α)
    (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ := by
  ext
  apply dotProduct_comm

@[simp]
theorem transpose_smul {R : Type*} [SMul R α] (c : R) (M : Matrix m n α) : (c • M)ᵀ = c • Mᵀ := by
  ext
  rfl

@[simp]
theorem transpose_neg [Neg α] (M : Matrix m n α) : (-M)ᵀ = -Mᵀ := by
  ext
  rfl

theorem transpose_map {f : α → β} {M : Matrix m n α} : Mᵀ.map f = (M.map f)ᵀ := by
  ext
  rfl

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
    Matrix m n α ≃ₗ[R] Matrix n m α :=
  { transposeAddEquiv m n α with map_smul' := transpose_smul }

@[simp]
theorem transposeLinearEquiv_symm [Semiring R] [AddCommMonoid α] [Module R α] :
    (transposeLinearEquiv m n R α).symm = transposeLinearEquiv n m R α :=
  rfl

variable {m n R α}
variable (m α)

/-- `Matrix.transpose` as a `RingEquiv` to the opposite ring -/
@[simps]
def transposeRingEquiv [AddCommMonoid α] [CommSemigroup α] [Fintype m] :
    Matrix m m α ≃+* (Matrix m m α)ᵐᵒᵖ :=
  { (transposeAddEquiv m m α).trans MulOpposite.opAddEquiv with
    toFun := fun M => MulOpposite.op Mᵀ
    invFun := fun M => M.unopᵀ
    map_mul' := fun M N =>
      (congr_arg MulOpposite.op (transpose_mul M N)).trans (MulOpposite.op_mul _ _)
    left_inv := fun M => transpose_transpose M
    right_inv := fun M => MulOpposite.unop_injective <| transpose_transpose M.unop }

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
@[simps]
def transposeAlgEquiv [CommSemiring R] [CommSemiring α] [Fintype m] [DecidableEq m] [Algebra R α] :
    Matrix m m α ≃ₐ[R] (Matrix m m α)ᵐᵒᵖ :=
  { (transposeAddEquiv m m α).trans MulOpposite.opAddEquiv,
    transposeRingEquiv m α with
    toFun := fun M => MulOpposite.op Mᵀ
    commutes' := fun r => by
      simp only [algebraMap_eq_diagonal, diagonal_transpose, MulOpposite.algebraMap_apply] }

variable {R m α}

end Transpose

section ConjTranspose

open Matrix

/-- Tell `simp` what the entries are in a conjugate transposed matrix.

  Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-/
@[simp]
theorem conjTranspose_apply [Star α] (M : Matrix m n α) (i j) :
    M.conjTranspose j i = star (M i j) :=
  rfl

@[simp]
theorem conjTranspose_conjTranspose [InvolutiveStar α] (M : Matrix m n α) : Mᴴᴴ = M :=
  Matrix.ext <| by simp

theorem conjTranspose_injective [InvolutiveStar α] :
    Function.Injective (conjTranspose : Matrix m n α → Matrix n m α) :=
  (map_injective star_injective).comp transpose_injective

@[simp] theorem conjTranspose_inj [InvolutiveStar α] {A B : Matrix m n α} : Aᴴ = Bᴴ ↔ A = B :=
  conjTranspose_injective.eq_iff

@[simp]
theorem conjTranspose_eq_diagonal [DecidableEq n] [AddMonoid α] [StarAddMonoid α]
    {M : Matrix n n α} {v : n → α} :
    Mᴴ = diagonal v ↔ M = diagonal (star v) :=
  (Function.Involutive.eq_iff conjTranspose_conjTranspose).trans <|
    by rw [diagonal_conjTranspose]

@[simp]
theorem conjTranspose_zero [AddMonoid α] [StarAddMonoid α] : (0 : Matrix m n α)ᴴ = 0 :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_eq_zero [AddMonoid α] [StarAddMonoid α] {M : Matrix m n α} :
    Mᴴ = 0 ↔ M = 0 := by
  rw [← conjTranspose_inj (A := M), conjTranspose_zero]

@[simp]
theorem conjTranspose_one [DecidableEq n] [Semiring α] [StarRing α] : (1 : Matrix n n α)ᴴ = 1 := by
  simp [conjTranspose]

@[simp]
theorem conjTranspose_eq_one [DecidableEq n] [Semiring α] [StarRing α] {M : Matrix n n α} :
    Mᴴ = 1 ↔ M = 1 :=
  (Function.Involutive.eq_iff conjTranspose_conjTranspose).trans <|
    by rw [conjTranspose_one]

@[simp]
theorem conjTranspose_natCast [DecidableEq n] [Semiring α] [StarRing α] (d : ℕ) :
    (d : Matrix n n α)ᴴ = d := by
  simp [conjTranspose, Matrix.map_natCast, diagonal_natCast]

@[simp]
theorem conjTranspose_eq_natCast [DecidableEq n] [Semiring α] [StarRing α]
    {M : Matrix n n α} {d : ℕ} :
    Mᴴ = d ↔ M = d :=
  (Function.Involutive.eq_iff conjTranspose_conjTranspose).trans <|
    by rw [conjTranspose_natCast]

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem conjTranspose_ofNat [DecidableEq n] [Semiring α] [StarRing α] (d : ℕ) [d.AtLeastTwo] :
    (no_index (OfNat.ofNat d) : Matrix n n α)ᴴ = OfNat.ofNat d :=
  conjTranspose_natCast _

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem conjTranspose_eq_ofNat [DecidableEq n] [Semiring α] [StarRing α]
    {M : Matrix n n α} {d : ℕ} [d.AtLeastTwo] :
    Mᴴ = no_index (OfNat.ofNat d) ↔ M = OfNat.ofNat d :=
  conjTranspose_eq_natCast

@[simp]
theorem conjTranspose_intCast [DecidableEq n] [Ring α] [StarRing α] (d : ℤ) :
    (d : Matrix n n α)ᴴ = d := by
  simp [conjTranspose, Matrix.map_intCast, diagonal_intCast]

@[simp]
theorem conjTranspose_eq_intCast [DecidableEq n] [Ring α] [StarRing α]
    {M : Matrix n n α} {d : ℤ} :
    Mᴴ = d ↔ M = d :=
  (Function.Involutive.eq_iff conjTranspose_conjTranspose).trans <|
    by rw [conjTranspose_intCast]

@[simp]
theorem conjTranspose_add [AddMonoid α] [StarAddMonoid α] (M N : Matrix m n α) :
    (M + N)ᴴ = Mᴴ + Nᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_sub [AddGroup α] [StarAddMonoid α] (M N : Matrix m n α) :
    (M - N)ᴴ = Mᴴ - Nᴴ :=
  Matrix.ext <| by simp

/-- Note that `StarModule` is quite a strong requirement; as such we also provide the following
variants which this lemma would not apply to:
* `Matrix.conjTranspose_smul_non_comm`
* `Matrix.conjTranspose_nsmul`
* `Matrix.conjTranspose_zsmul`
* `Matrix.conjTranspose_natCast_smul`
* `Matrix.conjTranspose_intCast_smul`
* `Matrix.conjTranspose_inv_natCast_smul`
* `Matrix.conjTranspose_inv_intCast_smul`
* `Matrix.conjTranspose_rat_smul`
* `Matrix.conjTranspose_ratCast_smul`
-/
@[simp]
theorem conjTranspose_smul [Star R] [Star α] [SMul R α] [StarModule R α] (c : R)
    (M : Matrix m n α) : (c • M)ᴴ = star c • Mᴴ :=
  Matrix.ext fun _ _ => star_smul _ _

@[simp]
theorem conjTranspose_smul_non_comm [Star R] [Star α] [SMul R α] [SMul Rᵐᵒᵖ α] (c : R)
    (M : Matrix m n α) (h : ∀ (r : R) (a : α), star (r • a) = MulOpposite.op (star r) • star a) :
    (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ :=
  Matrix.ext <| by simp [h]

-- @[simp] -- Porting note (#10618): simp can prove this
theorem conjTranspose_smul_self [Mul α] [StarMul α] (c : α) (M : Matrix m n α) :
    (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ :=
  conjTranspose_smul_non_comm c M star_mul

@[simp]
theorem conjTranspose_nsmul [AddMonoid α] [StarAddMonoid α] (c : ℕ) (M : Matrix m n α) :
    (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_zsmul [AddGroup α] [StarAddMonoid α] (c : ℤ) (M : Matrix m n α) :
    (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_natCast_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
    (c : ℕ) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem conjTranspose_ofNat_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
    (c : ℕ) [c.AtLeastTwo] (M : Matrix m n α) :
    ((no_index (OfNat.ofNat c : R)) • M)ᴴ = (OfNat.ofNat c : R) • Mᴴ :=
  conjTranspose_natCast_smul c M

@[simp]
theorem conjTranspose_intCast_smul [Ring R] [AddCommGroup α] [StarAddMonoid α] [Module R α] (c : ℤ)
    (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] (c : ℕ) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻¹ • Mᴴ :=
  Matrix.ext <| by simp

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem conjTranspose_inv_ofNat_smul [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] (c : ℕ) [c.AtLeastTwo] (M : Matrix m n α) :
    ((no_index (OfNat.ofNat c : R))⁻¹ • M)ᴴ = (OfNat.ofNat c : R)⁻¹ • Mᴴ :=
  conjTranspose_inv_natCast_smul c M

@[simp]
theorem conjTranspose_inv_intCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoid α]
    [Module R α] (c : ℤ) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻¹ • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_ratCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoid α] [Module R α]
    (c : ℚ) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_rat_smul [AddCommGroup α] [StarAddMonoid α] [Module ℚ α] (c : ℚ)
    (M : Matrix m n α) : (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_mul [Fintype n] [NonUnitalSemiring α] [StarRing α] (M : Matrix m n α)
    (N : Matrix n l α) : (M * N)ᴴ = Nᴴ * Mᴴ :=
  Matrix.ext <| by simp [mul_apply]

@[simp]
theorem conjTranspose_neg [AddGroup α] [StarAddMonoid α] (M : Matrix m n α) : (-M)ᴴ = -Mᴴ :=
  Matrix.ext <| by simp

theorem conjTranspose_map [Star α] [Star β] {A : Matrix m n α} (f : α → β)
    (hf : Function.Semiconj f star star) : Aᴴ.map f = (A.map f)ᴴ :=
  Matrix.ext fun _ _ => hf _

/-- When `star x = x` on the coefficients (such as the real numbers) `conjTranspose` and `transpose`
are the same operation. -/
@[simp]
theorem conjTranspose_eq_transpose_of_trivial [Star α] [TrivialStar α] (A : Matrix m n α) :
    Aᴴ = Aᵀ := Matrix.ext fun _ _ => star_trivial _

variable (m n α)

/-- `Matrix.conjTranspose` as an `AddEquiv` -/
@[simps apply]
def conjTransposeAddEquiv [AddMonoid α] [StarAddMonoid α] : Matrix m n α ≃+ Matrix n m α where
  toFun := conjTranspose
  invFun := conjTranspose
  left_inv := conjTranspose_conjTranspose
  right_inv := conjTranspose_conjTranspose
  map_add' := conjTranspose_add

@[simp]
theorem conjTransposeAddEquiv_symm [AddMonoid α] [StarAddMonoid α] :
    (conjTransposeAddEquiv m n α).symm = conjTransposeAddEquiv n m α :=
  rfl

variable {m n α}

theorem conjTranspose_list_sum [AddMonoid α] [StarAddMonoid α] (l : List (Matrix m n α)) :
    l.sumᴴ = (l.map conjTranspose).sum :=
  map_list_sum (conjTransposeAddEquiv m n α) l

theorem conjTranspose_multiset_sum [AddCommMonoid α] [StarAddMonoid α]
    (s : Multiset (Matrix m n α)) : s.sumᴴ = (s.map conjTranspose).sum :=
  (conjTransposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s

theorem conjTranspose_sum [AddCommMonoid α] [StarAddMonoid α] {ι : Type*} (s : Finset ι)
    (M : ι → Matrix m n α) : (∑ i ∈ s, M i)ᴴ = ∑ i ∈ s, (M i)ᴴ :=
  map_sum (conjTransposeAddEquiv m n α) _ s

variable (m n R α)

/-- `Matrix.conjTranspose` as a `LinearMap` -/
@[simps apply]
def conjTransposeLinearEquiv [CommSemiring R] [StarRing R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] [StarModule R α] : Matrix m n α ≃ₗ⋆[R] Matrix n m α :=
  { conjTransposeAddEquiv m n α with map_smul' := conjTranspose_smul }

@[simp]
theorem conjTransposeLinearEquiv_symm [CommSemiring R] [StarRing R] [AddCommMonoid α]
    [StarAddMonoid α] [Module R α] [StarModule R α] :
    (conjTransposeLinearEquiv m n R α).symm = conjTransposeLinearEquiv n m R α :=
  rfl

variable {m n R α}
variable (m α)

/-- `Matrix.conjTranspose` as a `RingEquiv` to the opposite ring -/
@[simps]
def conjTransposeRingEquiv [Semiring α] [StarRing α] [Fintype m] :
    Matrix m m α ≃+* (Matrix m m α)ᵐᵒᵖ :=
  { (conjTransposeAddEquiv m m α).trans MulOpposite.opAddEquiv with
    toFun := fun M => MulOpposite.op Mᴴ
    invFun := fun M => M.unopᴴ
    map_mul' := fun M N =>
      (congr_arg MulOpposite.op (conjTranspose_mul M N)).trans (MulOpposite.op_mul _ _) }

variable {m α}

@[simp]
theorem conjTranspose_pow [Semiring α] [StarRing α] [Fintype m] [DecidableEq m] (M : Matrix m m α)
    (k : ℕ) : (M ^ k)ᴴ = Mᴴ ^ k :=
  MulOpposite.op_injective <| map_pow (conjTransposeRingEquiv m α) M k

theorem conjTranspose_list_prod [Semiring α] [StarRing α] [Fintype m] [DecidableEq m]
    (l : List (Matrix m m α)) : l.prodᴴ = (l.map conjTranspose).reverse.prod :=
  (conjTransposeRingEquiv m α).unop_map_list_prod l

end ConjTranspose

section Star

/-- When `α` has a star operation, square matrices `Matrix n n α` have a star
operation equal to `Matrix.conjTranspose`. -/
instance [Star α] : Star (Matrix n n α) where star := conjTranspose

theorem star_eq_conjTranspose [Star α] (M : Matrix m m α) : star M = Mᴴ :=
  rfl

@[simp]
theorem star_apply [Star α] (M : Matrix n n α) (i j) : (star M) i j = star (M j i) :=
  rfl

instance [InvolutiveStar α] : InvolutiveStar (Matrix n n α) where
  star_involutive := conjTranspose_conjTranspose

/-- When `α` is a `*`-additive monoid, `Matrix.star` is also a `*`-additive monoid. -/
instance [AddMonoid α] [StarAddMonoid α] : StarAddMonoid (Matrix n n α) where
  star_add := conjTranspose_add

instance [Star α] [Star β] [SMul α β] [StarModule α β] : StarModule α (Matrix n n β) where
  star_smul := conjTranspose_smul

/-- When `α` is a `*`-(semi)ring, `Matrix.star` is also a `*`-(semi)ring. -/
instance [Fintype n] [NonUnitalSemiring α] [StarRing α] : StarRing (Matrix n n α) where
  star_add := conjTranspose_add
  star_mul := conjTranspose_mul

/-- A version of `star_mul` for `*` instead of `*`. -/
theorem star_mul [Fintype n] [NonUnitalSemiring α] [StarRing α] (M N : Matrix n n α) :
    star (M * N) = star N * star M :=
  conjTranspose_mul _ _

end Star

/-- Given maps `(r_reindex : l → m)` and `(c_reindex : o → n)` reindexing the rows and columns of
a matrix `M : Matrix m n α`, the matrix `M.submatrix r_reindex c_reindex : Matrix l o α` is defined
by `(M.submatrix r_reindex c_reindex) i j = M (r_reindex i) (c_reindex j)` for `(i,j) : l × o`.
Note that the total number of row and columns does not have to be preserved. -/
def submatrix (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) : Matrix l o α :=
  of fun i j => A (r_reindex i) (c_reindex j)

@[simp]
theorem submatrix_apply (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) (i j) :
    A.submatrix r_reindex c_reindex i j = A (r_reindex i) (c_reindex j) :=
  rfl

@[simp]
theorem submatrix_id_id (A : Matrix m n α) : A.submatrix id id = A :=
  ext fun _ _ => rfl

@[simp]
theorem submatrix_submatrix {l₂ o₂ : Type*} (A : Matrix m n α) (r₁ : l → m) (c₁ : o → n)
    (r₂ : l₂ → l) (c₂ : o₂ → o) :
    (A.submatrix r₁ c₁).submatrix r₂ c₂ = A.submatrix (r₁ ∘ r₂) (c₁ ∘ c₂) :=
  ext fun _ _ => rfl

@[simp]
theorem transpose_submatrix (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) :
    (A.submatrix r_reindex c_reindex)ᵀ = Aᵀ.submatrix c_reindex r_reindex :=
  ext fun _ _ => rfl

@[simp]
theorem conjTranspose_submatrix [Star α] (A : Matrix m n α) (r_reindex : l → m)
    (c_reindex : o → n) : (A.submatrix r_reindex c_reindex)ᴴ = Aᴴ.submatrix c_reindex r_reindex :=
  ext fun _ _ => rfl

theorem submatrix_add [Add α] (A B : Matrix m n α) :
    ((A + B).submatrix : (l → m) → (o → n) → Matrix l o α) = A.submatrix + B.submatrix :=
  rfl

theorem submatrix_neg [Neg α] (A : Matrix m n α) :
    ((-A).submatrix : (l → m) → (o → n) → Matrix l o α) = -A.submatrix :=
  rfl

theorem submatrix_sub [Sub α] (A B : Matrix m n α) :
    ((A - B).submatrix : (l → m) → (o → n) → Matrix l o α) = A.submatrix - B.submatrix :=
  rfl

@[simp]
theorem submatrix_zero [Zero α] :
    ((0 : Matrix m n α).submatrix : (l → m) → (o → n) → Matrix l o α) = 0 :=
  rfl

theorem submatrix_smul {R : Type*} [SMul R α] (r : R) (A : Matrix m n α) :
    ((r • A : Matrix m n α).submatrix : (l → m) → (o → n) → Matrix l o α) = r • A.submatrix :=
  rfl

theorem submatrix_map (f : α → β) (e₁ : l → m) (e₂ : o → n) (A : Matrix m n α) :
    (A.map f).submatrix e₁ e₂ = (A.submatrix e₁ e₂).map f :=
  rfl

/-- Given a `(m × m)` diagonal matrix defined by a map `d : m → α`, if the reindexing map `e` is
  injective, then the resulting matrix is again diagonal. -/
theorem submatrix_diagonal [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l → m)
    (he : Function.Injective e) : (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  ext fun i j => by
    rw [submatrix_apply]
    by_cases h : i = j
    · rw [h, diagonal_apply_eq, diagonal_apply_eq]
      simp only [Function.comp_apply] -- Porting note: (simp) added this
    · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (he.ne h)]

theorem submatrix_one [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l → m)
    (he : Function.Injective e) : (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_diagonal _ e he

theorem submatrix_mul [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p q : Type*}
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : l → m) (e₂ : o → n) (e₃ : q → p)
    (he₂ : Function.Bijective e₂) :
    (M * N).submatrix e₁ e₃ = M.submatrix e₁ e₂ * N.submatrix e₂ e₃ :=
  ext fun _ _ => (he₂.sum_comp _).symm

theorem diag_submatrix (A : Matrix m m α) (e : l → m) : diag (A.submatrix e e) = A.diag ∘ e :=
  rfl

/-! `simp` lemmas for `Matrix.submatrix`s interaction with `Matrix.diagonal`, `1`, and `Matrix.mul`
for when the mappings are bundled. -/


@[simp]
theorem submatrix_diagonal_embedding [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α)
    (e : l ↪ m) : (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  submatrix_diagonal d e e.injective

@[simp]
theorem submatrix_diagonal_equiv [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l ≃ m) :
    (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  submatrix_diagonal d e e.injective

@[simp]
theorem submatrix_one_embedding [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ↪ m) :
    (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_one e e.injective

@[simp]
theorem submatrix_one_equiv [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ≃ m) :
    (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_one e e.injective

@[simp]
theorem submatrix_mul_equiv [Fintype n] [Fintype o] [AddCommMonoid α] [Mul α] {p q : Type*}
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : l → m) (e₂ : o ≃ n) (e₃ : q → p) :
    M.submatrix e₁ e₂ * N.submatrix e₂ e₃ = (M * N).submatrix e₁ e₃ :=
  (submatrix_mul M N e₁ e₂ e₃ e₂.bijective).symm

theorem submatrix_mulVec_equiv [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α]
    (M : Matrix m n α) (v : o → α) (e₁ : l → m) (e₂ : o ≃ n) :
    M.submatrix e₁ e₂ *ᵥ v = (M *ᵥ (v ∘ e₂.symm)) ∘ e₁ :=
  funext fun _ => Eq.symm (dotProduct_comp_equiv_symm _ _ _)

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

/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
def reindex (eₘ : m ≃ l) (eₙ : n ≃ o) : Matrix m n α ≃ Matrix l o α where
  toFun M := M.submatrix eₘ.symm eₙ.symm
  invFun M := M.submatrix eₘ eₙ
  left_inv M := by simp
  right_inv M := by simp

@[simp]
theorem reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    reindex eₘ eₙ M = M.submatrix eₘ.symm eₙ.symm :=
  rfl

-- @[simp] -- Porting note (#10618): simp can prove this
theorem reindex_refl_refl (A : Matrix m n α) : reindex (Equiv.refl _) (Equiv.refl _) A = A :=
  A.submatrix_id_id

@[simp]
theorem reindex_symm (eₘ : m ≃ l) (eₙ : n ≃ o) :
    (reindex eₘ eₙ).symm = (reindex eₘ.symm eₙ.symm : Matrix l o α ≃ _) :=
  rfl

@[simp]
theorem reindex_trans {l₂ o₂ : Type*} (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂) :
    (reindex eₘ eₙ).trans (reindex eₘ₂ eₙ₂) =
      (reindex (eₘ.trans eₘ₂) (eₙ.trans eₙ₂) : Matrix m n α ≃ _) :=
  Equiv.ext fun A => (A.submatrix_submatrix eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm : _)

theorem transpose_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᵀ = reindex eₙ eₘ Mᵀ :=
  rfl

theorem conjTranspose_reindex [Star α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᴴ = reindex eₙ eₘ Mᴴ :=
  rfl

-- @[simp] -- Porting note (#10618): simp can prove this
theorem submatrix_mul_transpose_submatrix [Fintype m] [Fintype n] [AddCommMonoid α] [Mul α]
    (e : m ≃ n) (M : Matrix m n α) : M.submatrix id e * Mᵀ.submatrix e id = M * Mᵀ := by
  rw [submatrix_mul_equiv, submatrix_id_id]

/-- The left `n × l` part of an `n × (l+r)` matrix. -/
abbrev subLeft {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α) : Matrix (Fin m) (Fin l) α :=
  submatrix A id (Fin.castAdd r)

/-- The right `n × r` part of an `n × (l+r)` matrix. -/
abbrev subRight {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α) : Matrix (Fin m) (Fin r) α :=
  submatrix A id (Fin.natAdd l)

/-- The top `u × n` part of a `(u+d) × n` matrix. -/
abbrev subUp {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α) : Matrix (Fin u) (Fin n) α :=
  submatrix A (Fin.castAdd d) id

/-- The bottom `d × n` part of a `(u+d) × n` matrix. -/
abbrev subDown {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α) : Matrix (Fin d) (Fin n) α :=
  submatrix A (Fin.natAdd u) id

/-- The top-right `u × r` part of a `(u+d) × (l+r)` matrix. -/
abbrev subUpRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin u) (Fin r) α :=
  subUp (subRight A)

/-- The bottom-right `d × r` part of a `(u+d) × (l+r)` matrix. -/
abbrev subDownRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin d) (Fin r) α :=
  subDown (subRight A)

/-- The top-left `u × l` part of a `(u+d) × (l+r)` matrix. -/
abbrev subUpLeft {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin u) (Fin l) α :=
  subUp (subLeft A)

/-- The bottom-left `d × l` part of a `(u+d) × (l+r)` matrix. -/
abbrev subDownLeft {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin d) (Fin l) α :=
  subDown (subLeft A)

end Matrix

namespace RingHom

variable [Fintype n] [NonAssocSemiring α] [NonAssocSemiring β]

theorem map_matrix_mul (M : Matrix m n α) (N : Matrix n o α) (i : m) (j : o) (f : α →+* β) :
    f ((M * N) i j) = (M.map f * N.map f) i j := by
  simp [Matrix.mul_apply, map_sum]

theorem map_dotProduct [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (v w : n → R) :
    f (v ⬝ᵥ w) = f ∘ v ⬝ᵥ f ∘ w := by
  simp only [Matrix.dotProduct, map_sum f, f.map_mul, Function.comp]

theorem map_vecMul [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (M : Matrix n m R)
    (v : n → R) (i : m) : f ((v ᵥ* M) i) =  ((f ∘ v) ᵥ* M.map f) i := by
  simp only [Matrix.vecMul, Matrix.map_apply, RingHom.map_dotProduct, Function.comp]

theorem map_mulVec [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (M : Matrix m n R)
    (v : n → R) (i : m) : f ((M *ᵥ v) i) = (M.map f *ᵥ (f ∘ v)) i := by
  simp only [Matrix.mulVec, Matrix.map_apply, RingHom.map_dotProduct, Function.comp]

end RingHom

set_option linter.style.longFile 2700
