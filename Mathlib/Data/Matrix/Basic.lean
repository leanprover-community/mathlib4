/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.RingEquiv
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.Pi
import Mathlib.Data.Fintype.BigOperators

#align_import data.matrix.basic from "leanprover-community/mathlib"@"eba5bb3155cab51d80af00e8d7d69fa271b1302b"

/-!
# Matrices

This file defines basic properties of matrices.

Matrices with rows indexed by `m`, columns indexed by `n`, and entries of type `α` are represented
with `Matrix m n α`. For the typical approach of counting rows and columns,
`Matrix (Fin m) (Fin n) α` can be used.

## Notation

The locale `Matrix` gives the following notation:

* `⬝ᵥ` for `Matrix.dotProduct`
* `ᵀ` for `Matrix.transpose`
* `ᴴ` for `Matrix.conjTranspose`

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `λ i j, _` or even `(λ i j, _ : Matrix m n α)`, as these are not recognized by lean as having
the right type. Instead, `Matrix.of` should be used.

## TODO

Under various conditions, multiplication of infinite matrices makes sense.
These have not yet been implemented.
-/


universe u u' v w

open BigOperators

/-- `Matrix m n R` is the type of matrices with entries in `R`, whose rows are indexed by `m`
and whose columns are indexed by `n`. -/
def Matrix (m : Type u) (n : Type u') (α : Type v) : Type max u u' v :=
  m → n → α
#align matrix Matrix

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix

section Ext

variable {M N : Matrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩
                                                       -- 🎉 no goals
#align matrix.ext_iff Matrix.ext_iff

-- Porting note: `ext` does not like this, see new lemma below.
-- @[ext]
theorem ext : (∀ i j, M i j = N i j) → M = N :=
  ext_iff.mp
#align matrix.ext Matrix.ext

-- Porting note: `ext` does not like if there are two variables introduced at once. E.g.
-- ```
-- example (A B : Matrix m n α) : A = B := by
--   ext i j
--   sorry
-- ```
-- would only introduce the first variable, so that afterwards, the state is
-- ```
-- i : m
-- ⊢ ∀ (j : n), A i j = B i j
-- ```
-- This is probably a bug in `ext`. Once it is fixed, you should delete `Matrix.ext'` below
-- and restore the `@[ext]` attribute on `Matrix.ext` above.
@[ext]
theorem ext' : (∀ i, M i = N i) → M = N :=
  fun h => Matrix.ext <| fun i => by simp[h]
                                     -- 🎉 no goals

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
#align matrix.of Matrix.of

@[simp]
theorem of_apply (f : m → n → α) (i j) : of f i j = f i j :=
  rfl
#align matrix.of_apply Matrix.of_apply

@[simp]
theorem of_symm_apply (f : Matrix m n α) (i j) : of.symm f i j = f i j :=
  rfl
#align matrix.of_symm_apply Matrix.of_symm_apply

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
#align matrix.map Matrix.map

@[simp]
theorem map_apply {M : Matrix m n α} {f : α → β} {i : m} {j : n} : M.map f i j = f (M i j) :=
  rfl
#align matrix.map_apply Matrix.map_apply

@[simp]
theorem map_id (M : Matrix m n α) : M.map id = M := by
  ext
  -- ⊢ map M id i✝ x✝ = M i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.map_id Matrix.map_id

@[simp]
theorem map_map {M : Matrix m n α} {β γ : Type*} {f : α → β} {g : β → γ} :
    (M.map f).map g = M.map (g ∘ f) := by
  ext
  -- ⊢ map (map M f) g i✝ x✝ = map M (g ∘ f) i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.map_map Matrix.map_map

theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective fun M : Matrix m n α => M.map f := fun _ _ h =>
  ext fun i j => hf <| ext_iff.mpr h i j
#align matrix.map_injective Matrix.map_injective

/-- The transpose of a matrix. -/
def transpose (M : Matrix m n α) : Matrix n m α :=
  of fun x y => M y x
#align matrix.transpose Matrix.transpose

-- TODO: set as an equation lemma for `transpose`, see mathlib4#3024
@[simp]
theorem transpose_apply (M : Matrix m n α) (i j) : transpose M i j = M j i :=
  rfl
#align matrix.transpose_apply Matrix.transpose_apply

@[inherit_doc]
scoped postfix:1024 "ᵀ" => Matrix.transpose

/-- The conjugate transpose of a matrix defined in term of `star`. -/
def conjTranspose [Star α] (M : Matrix m n α) : Matrix n m α :=
  M.transpose.map star
#align matrix.conj_transpose Matrix.conjTranspose

@[inherit_doc]
scoped postfix:1024 "ᴴ" => Matrix.conjTranspose

/-- `Matrix.col u` is the column matrix whose entries are given by `u`. -/
def col (w : m → α) : Matrix m Unit α :=
  of fun x _ => w x
#align matrix.col Matrix.col

-- TODO: set as an equation lemma for `col`, see mathlib4#3024
@[simp]
theorem col_apply (w : m → α) (i j) : col w i j = w i :=
  rfl
#align matrix.col_apply Matrix.col_apply

/-- `Matrix.row u` is the row matrix whose entries are given by `u`. -/
def row (v : n → α) : Matrix Unit n α :=
  of fun _ y => v y
#align matrix.row Matrix.row

-- TODO: set as an equation lemma for `row`, see mathlib4#3024
@[simp]
theorem row_apply (v : n → α) (i j) : row v i j = v j :=
  rfl
#align matrix.row_apply Matrix.row_apply

instance inhabited [Inhabited α] : Inhabited (Matrix m n α) :=
  -- Porting note: this instance was called `Pi.inhabited` in lean3-core, which is much
  -- nicer than the name `instInhabitedForAll_1` it got in lean4-core...
  instInhabitedForAll_1 _

-- porting note: new, Lean3 found this automatically
instance decidableEq [DecidableEq α] [Fintype m] [Fintype n] : DecidableEq (Matrix m n α) :=
  Fintype.decidablePiFintype

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
  instSubsingletonForAll
--Porting note: this instance was `Pi.subsingleton` in lean3-core

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

-- Porting note: added the following section with simp lemmas because `simp` fails
-- to apply the corresponding lemmas in the namespace `Pi`.
-- (e.g. `Pi.zero_apply` used on `OfNat.ofNat 0 i j`)
section

@[simp]
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
#align matrix.of_zero Matrix.of_zero

@[simp]
theorem of_add_of [Add α] (f g : m → n → α) : of f + of g = of (f + g) :=
  rfl
#align matrix.of_add_of Matrix.of_add_of

@[simp]
theorem of_sub_of [Sub α] (f g : m → n → α) : of f - of g = of (f - g) :=
  rfl
#align matrix.of_sub_of Matrix.of_sub_of

@[simp]
theorem neg_of [Neg α] (f : m → n → α) : -of f = of (-f) :=
  rfl
#align matrix.neg_of Matrix.neg_of

@[simp]
theorem smul_of [SMul R α] (r : R) (f : m → n → α) : r • of f = of (r • f) :=
  rfl
#align matrix.smul_of Matrix.smul_of

@[simp]
protected theorem map_zero [Zero α] [Zero β] (f : α → β) (h : f 0 = 0) :
    (0 : Matrix m n α).map f = 0 := by
  ext
  -- ⊢ map 0 f i✝ x✝ = OfNat.ofNat 0 i✝ x✝
  simp [h]
  -- 🎉 no goals
#align matrix.map_zero Matrix.map_zero

protected theorem map_add [Add α] [Add β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂)
    (M N : Matrix m n α) : (M + N).map f = M.map f + N.map f :=
  ext fun _ _ => hf _ _
#align matrix.map_add Matrix.map_add

protected theorem map_sub [Sub α] [Sub β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ - a₂) = f a₁ - f a₂)
    (M N : Matrix m n α) : (M - N).map f = M.map f - N.map f :=
  ext fun _ _ => hf _ _
#align matrix.map_sub Matrix.map_sub

theorem map_smul [SMul R α] [SMul R β] (f : α → β) (r : R) (hf : ∀ a, f (r • a) = r • f a)
    (M : Matrix m n α) : (r • M).map f = r • M.map f :=
  ext fun _ _ => hf _
#align matrix.map_smul Matrix.map_smul

/-- The scalar action via `Mul.toSMul` is transformed by the same map as the elements
of the matrix, when `f` preserves multiplication. -/
theorem map_smul' [Mul α] [Mul β] (f : α → β) (r : α) (A : Matrix n n α)
    (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) : (r • A).map f = f r • A.map f :=
  ext fun _ _ => hf _ _
#align matrix.map_smul' Matrix.map_smul'

/-- The scalar action via `mul.toOppositeSMul` is transformed by the same map as the
elements of the matrix, when `f` preserves multiplication. -/
theorem map_op_smul' [Mul α] [Mul β] (f : α → β) (r : α) (A : Matrix n n α)
    (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) :
    (MulOpposite.op r • A).map f = MulOpposite.op (f r) • A.map f :=
  ext fun _ _ => hf _ _
#align matrix.map_op_smul' Matrix.map_op_smul'

theorem _root_.IsSMulRegular.matrix [SMul R S] {k : R} (hk : IsSMulRegular S k) :
    IsSMulRegular (Matrix m n S) k :=
  IsSMulRegular.pi fun _ => IsSMulRegular.pi fun _ => hk
#align is_smul_regular.matrix IsSMulRegular.matrix

theorem _root_.IsLeftRegular.matrix [Mul α] {k : α} (hk : IsLeftRegular k) :
    IsSMulRegular (Matrix m n α) k :=
  hk.isSMulRegular.matrix
#align is_left_regular.matrix IsLeftRegular.matrix

instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext i
    -- ⊢ M i x✝ = N i x✝
    exact isEmptyElim i⟩
    -- 🎉 no goals
#align matrix.subsingleton_of_empty_left Matrix.subsingleton_of_empty_left

instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext i j
    -- ⊢ M i j = N i j
    exact isEmptyElim j⟩
    -- 🎉 no goals
#align matrix.subsingleton_of_empty_right Matrix.subsingleton_of_empty_right

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
#align matrix.diagonal Matrix.diagonal

-- TODO: set as an equation lemma for `diagonal`, see mathlib4#3024
theorem diagonal_apply [Zero α] (d : n → α) (i j) : diagonal d i j = if i = j then d i else 0 :=
  rfl
#align matrix.diagonal_apply Matrix.diagonal_apply

@[simp]
theorem diagonal_apply_eq [Zero α] (d : n → α) (i : n) : (diagonal d) i i = d i := by
  simp [diagonal]
  -- 🎉 no goals
#align matrix.diagonal_apply_eq Matrix.diagonal_apply_eq

@[simp]
theorem diagonal_apply_ne [Zero α] (d : n → α) {i j : n} (h : i ≠ j) : (diagonal d) i j = 0 := by
  simp [diagonal, h]
  -- 🎉 no goals
#align matrix.diagonal_apply_ne Matrix.diagonal_apply_ne

theorem diagonal_apply_ne' [Zero α] (d : n → α) {i j : n} (h : j ≠ i) : (diagonal d) i j = 0 :=
  diagonal_apply_ne d h.symm
#align matrix.diagonal_apply_ne' Matrix.diagonal_apply_ne'

@[simp]
theorem diagonal_eq_diagonal_iff [Zero α] {d₁ d₂ : n → α} :
    diagonal d₁ = diagonal d₂ ↔ ∀ i, d₁ i = d₂ i :=
  ⟨fun h i => by simpa using congr_arg (fun m : Matrix n n α => m i i) h, fun h => by
                 -- 🎉 no goals
    rw [show d₁ = d₂ from funext h]⟩
    -- 🎉 no goals
#align matrix.diagonal_eq_diagonal_iff Matrix.diagonal_eq_diagonal_iff

theorem diagonal_injective [Zero α] : Function.Injective (diagonal : (n → α) → Matrix n n α) :=
  fun d₁ d₂ h => funext fun i => by simpa using Matrix.ext_iff.mpr h i i
                                    -- 🎉 no goals
#align matrix.diagonal_injective Matrix.diagonal_injective

@[simp]
theorem diagonal_zero [Zero α] : (diagonal fun _ => 0 : Matrix n n α) = 0 := by
  ext
  -- ⊢ diagonal (fun x => 0) i✝ x✝ = OfNat.ofNat 0 i✝ x✝
  simp [diagonal]
  -- 🎉 no goals
#align matrix.diagonal_zero Matrix.diagonal_zero

@[simp]
theorem diagonal_transpose [Zero α] (v : n → α) : (diagonal v)ᵀ = diagonal v := by
  ext i j
  -- ⊢ (diagonal v)ᵀ i j = diagonal v i j
  by_cases h : i = j
  -- ⊢ (diagonal v)ᵀ i j = diagonal v i j
  · simp [h, transpose]
    -- 🎉 no goals
  · simp [h, transpose, diagonal_apply_ne' _ h]
    -- 🎉 no goals
#align matrix.diagonal_transpose Matrix.diagonal_transpose

@[simp]
theorem diagonal_add [AddZeroClass α] (d₁ d₂ : n → α) :
    diagonal d₁ + diagonal d₂ = diagonal fun i => d₁ i + d₂ i := by
  ext i j
  -- ⊢ (diagonal d₁ + diagonal d₂) i j = diagonal (fun i => d₁ i + d₂ i) i j
  by_cases h : i = j <;>
  -- ⊢ (diagonal d₁ + diagonal d₂) i j = diagonal (fun i => d₁ i + d₂ i) i j
  simp [h]
  -- 🎉 no goals
  -- 🎉 no goals
#align matrix.diagonal_add Matrix.diagonal_add

@[simp]
theorem diagonal_smul [Monoid R] [AddMonoid α] [DistribMulAction R α] (r : R) (d : n → α) :
    diagonal (r • d) = r • diagonal d := by
  ext i j
  -- ⊢ diagonal (r • d) i j = (r • diagonal d) i j
  by_cases h : i = j <;>
  -- ⊢ diagonal (r • d) i j = (r • diagonal d) i j
  simp [h]
  -- 🎉 no goals
  -- 🎉 no goals
#align matrix.diagonal_smul Matrix.diagonal_smul

variable (n α)

/-- `Matrix.diagonal` as an `AddMonoidHom`. -/
@[simps]
def diagonalAddMonoidHom [AddZeroClass α] : (n → α) →+ Matrix n n α where
  toFun := diagonal
  map_zero' := diagonal_zero
  map_add' x y := (diagonal_add x y).symm
#align matrix.diagonal_add_monoid_hom Matrix.diagonalAddMonoidHom

variable (R)

/-- `Matrix.diagonal` as a `LinearMap`. -/
@[simps]
def diagonalLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : (n → α) →ₗ[R] Matrix n n α :=
  { diagonalAddMonoidHom n α with map_smul' := diagonal_smul }
#align matrix.diagonal_linear_map Matrix.diagonalLinearMap

variable {n α R}

@[simp]
theorem diagonal_map [Zero α] [Zero β] {f : α → β} (h : f 0 = 0) {d : n → α} :
    (diagonal d).map f = diagonal fun m => f (d m) := by
  ext
  -- ⊢ map (diagonal d) f i✝ x✝ = diagonal (fun m => f (d m)) i✝ x✝
  simp only [diagonal_apply, map_apply]
  -- ⊢ f (if i✝ = x✝ then d i✝ else 0) = if i✝ = x✝ then f (d i✝) else 0
  split_ifs <;> simp [h]
  -- ⊢ f (d i✝) = f (d i✝)
                -- 🎉 no goals
                -- 🎉 no goals
#align matrix.diagonal_map Matrix.diagonal_map

@[simp]
theorem diagonal_conjTranspose [AddMonoid α] [StarAddMonoid α] (v : n → α) :
    (diagonal v)ᴴ = diagonal (star v) := by
  rw [conjTranspose, diagonal_transpose, diagonal_map (star_zero _)]
  -- ⊢ (diagonal fun m => star (v m)) = diagonal (star v)
  rfl
  -- 🎉 no goals
#align matrix.diagonal_conj_transpose Matrix.diagonal_conjTranspose

section One

variable [Zero α] [One α]

instance one : One (Matrix n n α) :=
  ⟨diagonal fun _ => 1⟩

@[simp]
theorem diagonal_one : (diagonal fun _ => 1 : Matrix n n α) = 1 :=
  rfl
#align matrix.diagonal_one Matrix.diagonal_one

theorem one_apply {i j} : (1 : Matrix n n α) i j = if i = j then 1 else 0 :=
  rfl
#align matrix.one_apply Matrix.one_apply

@[simp]
theorem one_apply_eq (i) : (1 : Matrix n n α) i i = 1 :=
  diagonal_apply_eq _ i
#align matrix.one_apply_eq Matrix.one_apply_eq

@[simp]
theorem one_apply_ne {i j} : i ≠ j → (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne _
#align matrix.one_apply_ne Matrix.one_apply_ne

theorem one_apply_ne' {i j} : j ≠ i → (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne' _
#align matrix.one_apply_ne' Matrix.one_apply_ne'

@[simp]
theorem map_one [Zero β] [One β] (f : α → β) (h₀ : f 0 = 0) (h₁ : f 1 = 1) :
    (1 : Matrix n n α).map f = (1 : Matrix n n β) := by
  ext
  -- ⊢ map 1 f i✝ x✝ = OfNat.ofNat 1 i✝ x✝
  simp only [one_apply, map_apply]
  -- ⊢ f (if i✝ = x✝ then 1 else 0) = if i✝ = x✝ then 1 else 0
  split_ifs <;> simp [h₀, h₁]
  -- ⊢ f 1 = 1
                -- 🎉 no goals
                -- 🎉 no goals
#align matrix.map_one Matrix.map_one

-- Porting note: added implicit argument `(f := fun_ => α)`, why is that needed?
theorem one_eq_pi_single {i j} : (1 : Matrix n n α) i j = Pi.single (f := fun _ => α) i 1 j := by
  simp only [one_apply, Pi.single_apply, eq_comm]
  -- 🎉 no goals
#align matrix.one_eq_pi_single Matrix.one_eq_pi_single

end One

section Numeral

set_option linter.deprecated false

@[deprecated, simp]
theorem bit0_apply [Add α] (M : Matrix m m α) (i : m) (j : m) : (bit0 M) i j = bit0 (M i j) :=
  rfl
#align matrix.bit0_apply Matrix.bit0_apply

variable [AddZeroClass α] [One α]

@[deprecated]
theorem bit1_apply (M : Matrix n n α) (i : n) (j : n) :
    (bit1 M) i j = if i = j then bit1 (M i j) else bit0 (M i j) := by
  dsimp [bit1]
  -- ⊢ bit0 (M i j) + OfNat.ofNat 1 i j = if i = j then bit0 (M i j) + 1 else bit0  …
  by_cases h : i = j <;>
  -- ⊢ bit0 (M i j) + OfNat.ofNat 1 i j = if i = j then bit0 (M i j) + 1 else bit0  …
  simp [h]
  -- 🎉 no goals
  -- 🎉 no goals
#align matrix.bit1_apply Matrix.bit1_apply

@[deprecated, simp]
theorem bit1_apply_eq (M : Matrix n n α) (i : n) : (bit1 M) i i = bit1 (M i i) := by
  simp [bit1_apply]
  -- 🎉 no goals
#align matrix.bit1_apply_eq Matrix.bit1_apply_eq

@[deprecated, simp]
theorem bit1_apply_ne (M : Matrix n n α) {i j : n} (h : i ≠ j) : (bit1 M) i j = bit0 (M i j) := by
  simp [bit1_apply, h]
  -- 🎉 no goals
#align matrix.bit1_apply_ne Matrix.bit1_apply_ne

end Numeral

end Diagonal

section Diag

/-- The diagonal of a square matrix. -/
-- @[simp] -- Porting note: simpNF does not like this.
def diag (A : Matrix n n α) (i : n) : α :=
  A i i
#align matrix.diag Matrix.diag

-- Porting note: new, because of removed `simp` above.
-- TODO: set as an equation lemma for `diag`, see mathlib4#3024
@[simp]
theorem diag_apply (A : Matrix n n α) (i) : diag A i = A i i :=
  rfl

@[simp]
theorem diag_diagonal [DecidableEq n] [Zero α] (a : n → α) : diag (diagonal a) = a :=
  funext <| @diagonal_apply_eq _ _ _ _ a
#align matrix.diag_diagonal Matrix.diag_diagonal

@[simp]
theorem diag_transpose (A : Matrix n n α) : diag Aᵀ = diag A :=
  rfl
#align matrix.diag_transpose Matrix.diag_transpose

@[simp]
theorem diag_zero [Zero α] : diag (0 : Matrix n n α) = 0 :=
  rfl
#align matrix.diag_zero Matrix.diag_zero

@[simp]
theorem diag_add [Add α] (A B : Matrix n n α) : diag (A + B) = diag A + diag B :=
  rfl
#align matrix.diag_add Matrix.diag_add

@[simp]
theorem diag_sub [Sub α] (A B : Matrix n n α) : diag (A - B) = diag A - diag B :=
  rfl
#align matrix.diag_sub Matrix.diag_sub

@[simp]
theorem diag_neg [Neg α] (A : Matrix n n α) : diag (-A) = -diag A :=
  rfl
#align matrix.diag_neg Matrix.diag_neg

@[simp]
theorem diag_smul [SMul R α] (r : R) (A : Matrix n n α) : diag (r • A) = r • diag A :=
  rfl
#align matrix.diag_smul Matrix.diag_smul

@[simp]
theorem diag_one [DecidableEq n] [Zero α] [One α] : diag (1 : Matrix n n α) = 1 :=
  diag_diagonal _
#align matrix.diag_one Matrix.diag_one

variable (n α)

/-- `Matrix.diag` as an `AddMonoidHom`. -/
@[simps]
def diagAddMonoidHom [AddZeroClass α] : Matrix n n α →+ n → α where
  toFun := diag
  map_zero' := diag_zero
  map_add' := diag_add
#align matrix.diag_add_monoid_hom Matrix.diagAddMonoidHom

variable (R)

/-- `Matrix.diag` as a `LinearMap`. -/
@[simps]
def diagLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : Matrix n n α →ₗ[R] n → α :=
  { diagAddMonoidHom n α with map_smul' := diag_smul }
#align matrix.diag_linear_map Matrix.diagLinearMap

variable {n α R}

theorem diag_map {f : α → β} {A : Matrix n n α} : diag (A.map f) = f ∘ diag A :=
  rfl
#align matrix.diag_map Matrix.diag_map

@[simp]
theorem diag_conjTranspose [AddMonoid α] [StarAddMonoid α] (A : Matrix n n α) :
    diag Aᴴ = star (diag A) :=
  rfl
#align matrix.diag_conj_transpose Matrix.diag_conjTranspose

@[simp]
theorem diag_list_sum [AddMonoid α] (l : List (Matrix n n α)) : diag l.sum = (l.map diag).sum :=
  map_list_sum (diagAddMonoidHom n α) l
#align matrix.diag_list_sum Matrix.diag_list_sum

@[simp]
theorem diag_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix n n α)) :
    diag s.sum = (s.map diag).sum :=
  map_multiset_sum (diagAddMonoidHom n α) s
#align matrix.diag_multiset_sum Matrix.diag_multiset_sum

@[simp]
theorem diag_sum {ι} [AddCommMonoid α] (s : Finset ι) (f : ι → Matrix n n α) :
    diag (∑ i in s, f i) = ∑ i in s, diag (f i) :=
  map_sum (diagAddMonoidHom n α) f s
#align matrix.diag_sum Matrix.diag_sum

end Diag

section DotProduct

variable [Fintype m] [Fintype n]

/-- `dotProduct v w` is the sum of the entrywise products `v i * w i` -/
def dotProduct [Mul α] [AddCommMonoid α] (v w : m → α) : α :=
  ∑ i, v i * w i
#align matrix.dot_product Matrix.dotProduct

/- The precedence of 72 comes immediately after ` • ` for `SMul.smul`,
   so that `r₁ • a ⬝ᵥ r₂ • b` is parsed as `(r₁ • a) ⬝ᵥ (r₂ • b)` here. -/
@[inherit_doc]
scoped infixl:72 " ⬝ᵥ " => Matrix.dotProduct

theorem dotProduct_assoc [NonUnitalSemiring α] (u : m → α) (w : n → α) (v : Matrix m n α) :
    (fun j => u ⬝ᵥ fun i => v i j) ⬝ᵥ w = u ⬝ᵥ fun i => v i ⬝ᵥ w := by
  simpa [dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc] using Finset.sum_comm
  -- 🎉 no goals
#align matrix.dot_product_assoc Matrix.dotProduct_assoc

theorem dotProduct_comm [AddCommMonoid α] [CommSemigroup α] (v w : m → α) : v ⬝ᵥ w = w ⬝ᵥ v := by
  simp_rw [dotProduct, mul_comm]
  -- 🎉 no goals
#align matrix.dot_product_comm Matrix.dotProduct_comm

@[simp]
theorem dotProduct_pUnit [AddCommMonoid α] [Mul α] (v w : PUnit → α) : v ⬝ᵥ w = v ⟨⟩ * w ⟨⟩ := by
  simp [dotProduct]
  -- 🎉 no goals
#align matrix.dot_product_punit Matrix.dotProduct_pUnit

section MulOneClass

variable [MulOneClass α] [AddCommMonoid α]

theorem dotProduct_one (v : n → α) : v ⬝ᵥ 1 = ∑ i, v i := by simp [(· ⬝ᵥ ·)]
                                                             -- 🎉 no goals
#align matrix.dot_product_one Matrix.dotProduct_one

theorem one_dotProduct (v : n → α) : 1 ⬝ᵥ v = ∑ i, v i := by simp [(· ⬝ᵥ ·)]
                                                             -- 🎉 no goals
#align matrix.one_dot_product Matrix.one_dotProduct

end MulOneClass

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] (u v w : m → α) (x y : n → α)

@[simp]
theorem dotProduct_zero : v ⬝ᵥ 0 = 0 := by simp [dotProduct]
                                           -- 🎉 no goals
#align matrix.dot_product_zero Matrix.dotProduct_zero

@[simp]
theorem dotProduct_zero' : (v ⬝ᵥ fun _ => 0) = 0 :=
  dotProduct_zero v
#align matrix.dot_product_zero' Matrix.dotProduct_zero'

@[simp]
theorem zero_dotProduct : 0 ⬝ᵥ v = 0 := by simp [dotProduct]
                                           -- 🎉 no goals
#align matrix.zero_dot_product Matrix.zero_dotProduct

@[simp]
theorem zero_dotProduct' : (fun _ => (0 : α)) ⬝ᵥ v = 0 :=
  zero_dotProduct v
#align matrix.zero_dot_product' Matrix.zero_dotProduct'

@[simp]
theorem add_dotProduct : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w := by
  simp [dotProduct, add_mul, Finset.sum_add_distrib]
  -- 🎉 no goals
#align matrix.add_dot_product Matrix.add_dotProduct

@[simp]
theorem dotProduct_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w := by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]
  -- 🎉 no goals
#align matrix.dot_product_add Matrix.dotProduct_add

@[simp]
theorem sum_elim_dotProduct_sum_elim : Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct]
  -- 🎉 no goals
#align matrix.sum_elim_dot_product_sum_elim Matrix.sum_elim_dotProduct_sum_elim

/-- Permuting a vector on the left of a dot product can be transferred to the right. -/
@[simp]
theorem comp_equiv_symm_dotProduct (e : m ≃ n) : u ∘ e.symm ⬝ᵥ x = u ⬝ᵥ x ∘ e :=
  (e.sum_comp _).symm.trans <|
    Finset.sum_congr rfl fun _ _ => by simp only [Function.comp, Equiv.symm_apply_apply]
                                       -- 🎉 no goals
#align matrix.comp_equiv_symm_dot_product Matrix.comp_equiv_symm_dotProduct

/-- Permuting a vector on the right of a dot product can be transferred to the left. -/
@[simp]
theorem dotProduct_comp_equiv_symm (e : n ≃ m) : u ⬝ᵥ x ∘ e.symm = u ∘ e ⬝ᵥ x := by
  simpa only [Equiv.symm_symm] using (comp_equiv_symm_dotProduct u x e.symm).symm
  -- 🎉 no goals
#align matrix.dot_product_comp_equiv_symm Matrix.dotProduct_comp_equiv_symm

/-- Permuting vectors on both sides of a dot product is a no-op. -/
@[simp]
theorem comp_equiv_dotProduct_comp_equiv (e : m ≃ n) : x ∘ e ⬝ᵥ y ∘ e = x ⬝ᵥ y := by
  -- Porting note: was `simp only` with all three lemmas
  rw [← dotProduct_comp_equiv_symm]; simp only [Function.comp, Equiv.apply_symm_apply]
  -- ⊢ x ⬝ᵥ (y ∘ ↑e) ∘ ↑e.symm = x ⬝ᵥ y
                                     -- 🎉 no goals
#align matrix.comp_equiv_dot_product_comp_equiv Matrix.comp_equiv_dotProduct_comp_equiv

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocSemiringDecidable

variable [DecidableEq m] [NonUnitalNonAssocSemiring α] (u v w : m → α)

@[simp]
theorem diagonal_dotProduct (i : m) : diagonal v i ⬝ᵥ w = v i * w i := by
  have : ∀ (j) (_ : j ≠ i), diagonal v i j * w j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp
  -- ⊢ v i * w i = diagonal v i i * w i
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align matrix.diagonal_dot_product Matrix.diagonal_dotProduct

@[simp]
theorem dotProduct_diagonal (i : m) : v ⬝ᵥ diagonal w i = v i * w i := by
  have : ∀ (j) (_ : j ≠ i), v j * diagonal w i j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp
  -- ⊢ v i * w i = v i * diagonal w i i
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align matrix.dot_product_diagonal Matrix.dotProduct_diagonal

@[simp]
theorem dotProduct_diagonal' (i : m) : (v ⬝ᵥ fun j => diagonal w j i) = v i * w i := by
  have : ∀ (j) (_ : j ≠ i), v j * diagonal w j i = 0 := fun j hij => by
    simp [diagonal_apply_ne _ hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp
  -- ⊢ v i * w i = v i * diagonal w i i
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align matrix.dot_product_diagonal' Matrix.dotProduct_diagonal'

@[simp]
theorem single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ v = x * v i := by
  -- Porting note: (implicit arg) added `(f := fun _ => α)`
  have : ∀ (j) (_ : j ≠ i), Pi.single (f := fun _ => α) i x j * v j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp
  -- ⊢ x * v i = Pi.single i x i * v i
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align matrix.single_dot_product Matrix.single_dotProduct

@[simp]
theorem dotProduct_single (x : α) (i : m) : v ⬝ᵥ Pi.single i x = v i * x := by
  -- Porting note: (implicit arg) added `(f := fun _ => α)`
  have : ∀ (j) (_ : j ≠ i), v j * Pi.single (f := fun _ => α) i x j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp
  -- ⊢ v i * x = v i * Pi.single i x i
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align matrix.dot_product_single Matrix.dotProduct_single

end NonUnitalNonAssocSemiringDecidable

section NonAssocSemiring

variable [NonAssocSemiring α]

@[simp]
theorem one_dotProduct_one : (1 : n → α) ⬝ᵥ 1 = Fintype.card n := by
  simp [dotProduct, Fintype.card]
  -- 🎉 no goals
#align matrix.one_dot_product_one Matrix.one_dotProduct_one

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α] (u v w : m → α)

@[simp]
theorem neg_dotProduct : -v ⬝ᵥ w = -(v ⬝ᵥ w) := by simp [dotProduct]
                                                   -- 🎉 no goals
#align matrix.neg_dot_product Matrix.neg_dotProduct

@[simp]
theorem dotProduct_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w) := by simp [dotProduct]
                                                   -- 🎉 no goals
#align matrix.dot_product_neg Matrix.dotProduct_neg

@[simp]
theorem sub_dotProduct : (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w := by simp [sub_eq_add_neg]
                                                              -- 🎉 no goals
#align matrix.sub_dot_product Matrix.sub_dotProduct

@[simp]
theorem dotProduct_sub : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w := by simp [sub_eq_add_neg]
                                                              -- 🎉 no goals
#align matrix.dot_product_sub Matrix.dotProduct_sub

end NonUnitalNonAssocRing

section DistribMulAction

variable [Monoid R] [Mul α] [AddCommMonoid α] [DistribMulAction R α]

@[simp]
theorem smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m → α) : x • v ⬝ᵥ w = x • (v ⬝ᵥ w) :=
  by simp [dotProduct, Finset.smul_sum, smul_mul_assoc]
     -- 🎉 no goals
#align matrix.smul_dot_product Matrix.smul_dotProduct

@[simp]
theorem dotProduct_smul [SMulCommClass R α α] (x : R) (v w : m → α) : v ⬝ᵥ x • w = x • (v ⬝ᵥ w) :=
  by simp [dotProduct, Finset.smul_sum, mul_smul_comm]
     -- 🎉 no goals
#align matrix.dot_product_smul Matrix.dotProduct_smul

end DistribMulAction

section StarRing

variable [NonUnitalSemiring α] [StarRing α] (v w : m → α)

theorem star_dotProduct_star : star v ⬝ᵥ star w = star (w ⬝ᵥ v) := by simp [dotProduct]
                                                                      -- 🎉 no goals
#align matrix.star_dot_product_star Matrix.star_dotProduct_star

theorem star_dotProduct : star v ⬝ᵥ w = star (star w ⬝ᵥ v) := by simp [dotProduct]
                                                                 -- 🎉 no goals
#align matrix.star_dot_product Matrix.star_dotProduct

theorem dotProduct_star : v ⬝ᵥ star w = star (w ⬝ᵥ star v) := by simp [dotProduct]
                                                                 -- 🎉 no goals
#align matrix.dot_product_star Matrix.dotProduct_star

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
#align matrix.mul HMul.hMul

theorem mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
    {i k} : (M * N) i k = ∑ j, M i j * N j k :=
  rfl
#align matrix.mul_apply Matrix.mul_apply

instance [Fintype n] [Mul α] [AddCommMonoid α] : Mul (Matrix n n α) where mul M N := M * N

#noalign matrix.mul_eq_mul

theorem mul_apply' [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
    {i k} : (M * N) i k = (fun j => M i j) ⬝ᵥ fun j => N j k :=
  rfl
#align matrix.mul_apply' Matrix.mul_apply'

@[simp]
theorem diagonal_neg [DecidableEq n] [AddGroup α] (d : n → α) :
    -diagonal d = diagonal fun i => -d i :=
  ((diagonalAddMonoidHom n α).map_neg d).symm
#align matrix.diagonal_neg Matrix.diagonal_neg

theorem sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finset β) (g : β → Matrix m n α) :
    (∑ c in s, g c) i j = ∑ c in s, g c i j :=
  (congr_fun (s.sum_apply i g) j).trans (s.sum_apply j _)
#align matrix.sum_apply Matrix.sum_apply

theorem two_mul_expl {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
    (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧
    (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
    (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧
    (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ]
    -- ⊢ (((∑ x in Finset.range 0, if h : x < 2 then A 0 { val := x, isLt := h } * B  …
    -- ⊢ (((∑ x in Finset.range 0, if h : x < 2 then A 0 { val := x, isLt := h } * B  …
    -- 🎉 no goals
    -- ⊢ (((∑ x in Finset.range 0, if h : x < 2 then A 1 { val := x, isLt := h } * B  …
    -- 🎉 no goals
    -- ⊢ (((∑ x in Finset.range 0, if h : x < 2 then A 1 { val := x, isLt := h } * B  …
    -- 🎉 no goals
    simp
    -- 🎉 no goals
#align matrix.two_mul_expl Matrix.two_mul_expl

section AddCommMonoid

variable [AddCommMonoid α] [Mul α]

@[simp]
theorem smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] [IsScalarTower R α α] (a : R)
    (M : Matrix m n α) (N : Matrix n l α) : (a • M) * N = a • (M * N) := by
  ext
  -- ⊢ (a • M * N) i✝ x✝ = (a • (M * N)) i✝ x✝
  apply smul_dotProduct a
  -- 🎉 no goals
#align matrix.smul_mul Matrix.smul_mul

@[simp]
theorem mul_smul [Fintype n] [Monoid R] [DistribMulAction R α] [SMulCommClass R α α]
    (M : Matrix m n α) (a : R) (N : Matrix n l α) : M * (a • N) = a • (M * N) := by
  ext
  -- ⊢ (M * a • N) i✝ x✝ = (a • (M * N)) i✝ x✝
  apply dotProduct_smul
  -- 🎉 no goals
#align matrix.mul_smul Matrix.mul_smul

end AddCommMonoid

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

@[simp]
protected theorem mul_zero [Fintype n] (M : Matrix m n α) : M * (0 : Matrix n o α) = 0 := by
  ext
  -- ⊢ (M * 0) i✝ x✝ = OfNat.ofNat 0 i✝ x✝
  apply dotProduct_zero
  -- 🎉 no goals
#align matrix.mul_zero Matrix.mul_zero

@[simp]
protected theorem zero_mul [Fintype m] (M : Matrix m n α) : (0 : Matrix l m α) * M = 0 := by
  ext
  -- ⊢ (0 * M) i✝ x✝ = OfNat.ofNat 0 i✝ x✝
  apply zero_dotProduct
  -- 🎉 no goals
#align matrix.zero_mul Matrix.zero_mul

protected theorem mul_add [Fintype n] (L : Matrix m n α) (M N : Matrix n o α) :
    L * (M + N) = L * M + L * N := by
  ext
  -- ⊢ (L * (M + N)) i✝ x✝ = (L * M + L * N) i✝ x✝
  apply dotProduct_add
  -- 🎉 no goals
#align matrix.mul_add Matrix.mul_add

protected theorem add_mul [Fintype m] (L M : Matrix l m α) (N : Matrix m n α) :
    (L + M) * N = L * N + M * N := by
  ext
  -- ⊢ ((L + M) * N) i✝ x✝ = (L * N + M * N) i✝ x✝
  apply add_dotProduct
  -- 🎉 no goals
#align matrix.add_mul Matrix.add_mul

instance nonUnitalNonAssocSemiring [Fintype n] : NonUnitalNonAssocSemiring (Matrix n n α) :=
  { Matrix.addCommMonoid with
    mul := (· * ·)
    add := (· + ·)
    zero := 0
    mul_zero := Matrix.mul_zero
    zero_mul := Matrix.zero_mul
    left_distrib := Matrix.mul_add
    right_distrib := Matrix.add_mul }

@[simp]
theorem diagonal_mul [Fintype m] [DecidableEq m] (d : m → α) (M : Matrix m n α) (i j) :
    (diagonal d * M) i j = d i * M i j :=
  diagonal_dotProduct _ _ _
#align matrix.diagonal_mul Matrix.diagonal_mul

@[simp]
theorem mul_diagonal [Fintype n] [DecidableEq n] (d : n → α) (M : Matrix m n α) (i j) :
    (M * diagonal d) i j = M i j * d j := by
  rw [← diagonal_transpose]
  -- ⊢ (M * (diagonal d)ᵀ) i j = M i j * d j
  apply dotProduct_diagonal
  -- 🎉 no goals
#align matrix.mul_diagonal Matrix.mul_diagonal

@[simp]
theorem diagonal_mul_diagonal [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
    diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i := by
  ext i j
  -- ⊢ (diagonal d₁ * diagonal d₂) i j = diagonal (fun i => d₁ i * d₂ i) i j
  by_cases i = j <;>
  -- ⊢ (diagonal d₁ * diagonal d₂) i j = diagonal (fun i => d₁ i * d₂ i) i j
  -- ⊢ (diagonal d₁ * diagonal d₂) i j = diagonal (fun i => d₁ i * d₂ i) i j
  simp [h]
  -- 🎉 no goals
  -- 🎉 no goals
#align matrix.diagonal_mul_diagonal Matrix.diagonal_mul_diagonal

theorem diagonal_mul_diagonal' [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
    diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i :=
  diagonal_mul_diagonal _ _
#align matrix.diagonal_mul_diagonal' Matrix.diagonal_mul_diagonal'

theorem smul_eq_diagonal_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) (a : α) :
    a • M = (diagonal fun _ => a) * M := by
  ext
  -- ⊢ (a • M) i✝ x✝ = ((diagonal fun x => a) * M) i✝ x✝
  simp
  -- 🎉 no goals
#align matrix.smul_eq_diagonal_mul Matrix.smul_eq_diagonal_mul

@[simp]
theorem diag_col_mul_row (a b : n → α) : diag (col a * row b) = a * b := by
  ext
  -- ⊢ diag (col a * row b) x✝ = (a * b) x✝
  simp [Matrix.mul_apply, col, row]
  -- 🎉 no goals
#align matrix.diag_col_mul_row Matrix.diag_col_mul_row

/-- Left multiplication by a matrix, as an `AddMonoidHom` from matrices to matrices. -/
@[simps]
def addMonoidHomMulLeft [Fintype m] (M : Matrix l m α) : Matrix m n α →+ Matrix l n α where
  toFun x := M * x
  map_zero' := Matrix.mul_zero _
  map_add' := Matrix.mul_add _
#align matrix.add_monoid_hom_mul_left Matrix.addMonoidHomMulLeft

/-- Right multiplication by a matrix, as an `AddMonoidHom` from matrices to matrices. -/
@[simps]
def addMonoidHomMulRight [Fintype m] (M : Matrix m n α) : Matrix l m α →+ Matrix l n α where
  toFun x := x * M
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _
#align matrix.add_monoid_hom_mul_right Matrix.addMonoidHomMulRight

protected theorem sum_mul [Fintype m] (s : Finset β) (f : β → Matrix l m α) (M : Matrix m n α) :
    (∑ a in s, f a) * M = ∑ a in s, f a * M :=
  (addMonoidHomMulRight M : Matrix l m α →+ _).map_sum f s
#align matrix.sum_mul Matrix.sum_mul

protected theorem mul_sum [Fintype m] (s : Finset β) (f : β → Matrix m n α) (M : Matrix l m α) :
    (M * ∑ a in s, f a) = ∑ a in s, M * f a :=
  (addMonoidHomMulLeft M : Matrix m n α →+ _).map_sum f s
#align matrix.mul_sum Matrix.mul_sum

/-- This instance enables use with `smul_mul_assoc`. -/
instance Semiring.isScalarTower [Fintype n] [Monoid R] [DistribMulAction R α]
    [IsScalarTower R α α] : IsScalarTower R (Matrix n n α) (Matrix n n α) :=
  ⟨fun r m n => Matrix.smul_mul r m n⟩
#align matrix.semiring.is_scalar_tower Matrix.Semiring.isScalarTower

/-- This instance enables use with `mul_smul_comm`. -/
instance Semiring.smulCommClass [Fintype n] [Monoid R] [DistribMulAction R α]
    [SMulCommClass R α α] : SMulCommClass R (Matrix n n α) (Matrix n n α) :=
  ⟨fun r m n => (Matrix.mul_smul m r n).symm⟩
#align matrix.semiring.smul_comm_class Matrix.Semiring.smulCommClass

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

@[simp]
protected theorem one_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) :
    (1 : Matrix m m α) * M = M := by
  ext
  -- ⊢ (1 * M) i✝ x✝ = M i✝ x✝
  rw [← diagonal_one, diagonal_mul, one_mul]
  -- 🎉 no goals
#align matrix.one_mul Matrix.one_mul

@[simp]
protected theorem mul_one [Fintype n] [DecidableEq n] (M : Matrix m n α) :
    M * (1 : Matrix n n α) = M := by
  ext
  -- ⊢ (M * 1) i✝ x✝ = M i✝ x✝
  rw [← diagonal_one, mul_diagonal, mul_one]
  -- 🎉 no goals
#align matrix.mul_one Matrix.mul_one

instance nonAssocSemiring [Fintype n] [DecidableEq n] : NonAssocSemiring (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring with
    one := 1
    one_mul := Matrix.one_mul
    mul_one := Matrix.mul_one
    natCast := fun n => diagonal fun _ => n
    natCast_zero := by
      ext
      -- ⊢ NatCast.natCast 0 i✝ x✝ = OfNat.ofNat 0 i✝ x✝
      simp [Nat.cast]
      -- 🎉 no goals
    natCast_succ := fun n => by
      ext i j
      -- ⊢ NatCast.natCast (n + 1) i j = (NatCast.natCast n + 1) i j
      by_cases i = j <;>
      -- ⊢ NatCast.natCast (n + 1) i j = (NatCast.natCast n + 1) i j
      -- ⊢ NatCast.natCast (n + 1) i j = (NatCast.natCast n + 1) i j
      simp [Nat.cast, *]}
      -- 🎉 no goals
      -- 🎉 no goals

@[simp]
theorem map_mul [Fintype n] {L : Matrix m n α} {M : Matrix n o α} [NonAssocSemiring β]
    {f : α →+* β} : (L * M).map f = L.map f * M.map f := by
  ext
  -- ⊢ map (L * M) (↑f) i✝ x✝ = (map L ↑f * map M ↑f) i✝ x✝
  simp [mul_apply, map_sum]
  -- 🎉 no goals
#align matrix.map_mul Matrix.map_mul

variable (α n)

/-- `Matrix.diagonal` as a `RingHom`. -/
@[simps]
def diagonalRingHom [Fintype n] [DecidableEq n] : (n → α) →+* Matrix n n α :=
  { diagonalAddMonoidHom n α with
    toFun := diagonal
    map_one' := diagonal_one
    map_mul' := fun _ _ => (diagonal_mul_diagonal' _ _).symm }
#align matrix.diagonal_ring_hom Matrix.diagonalRingHom

end NonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring α] [Fintype m] [Fintype n]

protected theorem mul_assoc (L : Matrix l m α) (M : Matrix m n α) (N : Matrix n o α) :
    L * M * N = L * (M * N) := by
  ext
  -- ⊢ (L * M * N) i✝ x✝ = (L * (M * N)) i✝ x✝
  apply dotProduct_assoc
  -- 🎉 no goals
#align matrix.mul_assoc Matrix.mul_assoc

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
  -- ⊢ (-M * N) i✝ x✝ = (-(M * N)) i✝ x✝
  apply neg_dotProduct
  -- 🎉 no goals
#align matrix.neg_mul Matrix.neg_mul

@[simp]
protected theorem mul_neg (M : Matrix m n α) (N : Matrix n o α) : M * (-N) = -(M * N) := by
  ext
  -- ⊢ (M * -N) i✝ x✝ = (-(M * N)) i✝ x✝
  apply dotProduct_neg
  -- 🎉 no goals
#align matrix.mul_neg Matrix.mul_neg

protected theorem sub_mul (M M' : Matrix m n α) (N : Matrix n o α) :
    (M - M') * N = M * N - M' * N := by
  rw [sub_eq_add_neg, Matrix.add_mul, Matrix.neg_mul, sub_eq_add_neg]
  -- 🎉 no goals
#align matrix.sub_mul Matrix.sub_mul

protected theorem mul_sub (M : Matrix m n α) (N N' : Matrix n o α) :
    M * (N - N') = M * N - M * N' := by
  rw [sub_eq_add_neg, Matrix.mul_add, Matrix.mul_neg, sub_eq_add_neg]
  -- 🎉 no goals
#align matrix.mul_sub Matrix.mul_sub

instance nonUnitalNonAssocRing : NonUnitalNonAssocRing (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring, Matrix.addCommGroup with }

end NonUnitalNonAssocRing

instance instNonUnitalRing [Fintype n] [NonUnitalRing α] : NonUnitalRing (Matrix n n α) :=
  { Matrix.nonUnitalSemiring, Matrix.addCommGroup with }
#align matrix.non_unital_ring Matrix.instNonUnitalRing

instance instNonAssocRing [Fintype n] [DecidableEq n] [NonAssocRing α] :
    NonAssocRing (Matrix n n α) :=
  { Matrix.nonAssocSemiring, Matrix.addCommGroup with }
#align matrix.non_assoc_ring Matrix.instNonAssocRing

instance instRing [Fintype n] [DecidableEq n] [Ring α] : Ring (Matrix n n α) :=
  { Matrix.semiring, Matrix.addCommGroup with }
#align matrix.ring Matrix.instRing

section Semiring

variable [Semiring α]

theorem diagonal_pow [Fintype n] [DecidableEq n] (v : n → α) (k : ℕ) :
    diagonal v ^ k = diagonal (v ^ k) :=
  (map_pow (diagonalRingHom n α) v k).symm
#align matrix.diagonal_pow Matrix.diagonal_pow

@[simp]
theorem mul_mul_left [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α) :
    (of fun i j => a * M i j) * N = a • (M * N) :=
  smul_mul a M N
#align matrix.mul_mul_left Matrix.mul_mul_left

/-- The ring homomorphism `α →+* Matrix n n α`
sending `a` to the diagonal matrix with `a` on the diagonal.
-/
def scalar (n : Type u) [DecidableEq n] [Fintype n] : α →+* Matrix n n α :=
  { (smulAddHom α _).flip (1 : Matrix n n α) with
    toFun := fun a => a • (1 : Matrix n n α)
    map_one' := by simp
                   -- 🎉 no goals
    map_mul' := by
      intros
      -- ⊢ OneHom.toFun { toFun := fun a => a • 1, map_one' := (_ : 1 • 1 = 1) } (x✝ *  …
      ext
      -- ⊢ OneHom.toFun { toFun := fun a => a • 1, map_one' := (_ : 1 • 1 = 1) } (x✝¹ * …
      simp [mul_assoc] }
      -- 🎉 no goals
#align matrix.scalar Matrix.scalar

section Scalar

variable [DecidableEq n] [Fintype n]

@[simp]
theorem coe_scalar : (scalar n : α → Matrix n n α) = fun a => a • (1 : Matrix n n α) :=
  rfl
#align matrix.coe_scalar Matrix.coe_scalar

theorem scalar_apply_eq (a : α) (i : n) : scalar n a i i = a := by
  -- Porting note: replaced `Pi.smul_apply` with the new `Matrix.smul_apply`
  simp only [coe_scalar, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
  -- 🎉 no goals
#align matrix.scalar_apply_eq Matrix.scalar_apply_eq

theorem scalar_apply_ne (a : α) (i j : n) (h : i ≠ j) : scalar n a i j = 0 := by
  -- Porting note: replaced `Pi.smul_apply` with the new `Matrix.smul_apply`
  simp only [h, coe_scalar, one_apply_ne, Ne.def, not_false_iff, Matrix.smul_apply, smul_zero]
  -- 🎉 no goals
#align matrix.scalar_apply_ne Matrix.scalar_apply_ne

theorem scalar_inj [Nonempty n] {r s : α} : scalar n r = scalar n s ↔ r = s := by
  constructor
  -- ⊢ ↑(scalar n) r = ↑(scalar n) s → r = s
  · intro h
    -- ⊢ r = s
    inhabit n
    -- ⊢ r = s
    rw [← scalar_apply_eq r (Inhabited.default (α := n)),
        ← scalar_apply_eq s (Inhabited.default (α := n)), h]
  · rintro rfl
    -- ⊢ ↑(scalar n) r = ↑(scalar n) r
    rfl
    -- 🎉 no goals
#align matrix.scalar_inj Matrix.scalar_inj

end Scalar

end Semiring

section CommSemiring

variable [CommSemiring α] [Fintype n]

theorem smul_eq_mul_diagonal [DecidableEq n] (M : Matrix m n α) (a : α) :
    a • M = M * diagonal fun _ => a := by
  ext
  -- ⊢ (a • M) i✝ x✝ = (M * diagonal fun x => a) i✝ x✝
  simp [mul_comm]
  -- 🎉 no goals
#align matrix.smul_eq_mul_diagonal Matrix.smul_eq_mul_diagonal

@[simp]
theorem mul_mul_right (M : Matrix m n α) (N : Matrix n o α) (a : α) :
    (M * of fun i j => a * N i j) = a • (M * N) :=
  mul_smul M a N
#align matrix.mul_mul_right Matrix.mul_mul_right

theorem scalar.commute [DecidableEq n] (r : α) (M : Matrix n n α) : Commute (scalar n r) M := by
  simp [Commute, SemiconjBy]
  -- 🎉 no goals
#align matrix.scalar.commute Matrix.scalar.commute

end CommSemiring

section Algebra

variable [Fintype n] [DecidableEq n]

variable [CommSemiring R] [Semiring α] [Semiring β] [Algebra R α] [Algebra R β]

instance instAlgebra : Algebra R (Matrix n n α) :=
  { (Matrix.scalar n).comp (algebraMap R α) with
    commutes' := fun r x => by
      ext
      -- ⊢ (↑{ toMonoidHom := ↑src✝, map_zero' := (_ : OneHom.toFun (↑↑src✝) 0 = 0), ma …
      simp [Matrix.scalar, Matrix.mul_apply, Matrix.one_apply, Algebra.commutes, smul_ite]
      -- 🎉 no goals
    smul_def' := fun r x => by ext; simp [Matrix.scalar, Algebra.smul_def r] }
                               -- ⊢ (r • x) i✝ x✝ = (↑{ toMonoidHom := ↑src✝, map_zero' := (_ : OneHom.toFun (↑↑ …
                                    -- 🎉 no goals
#align matrix.algebra Matrix.instAlgebra

theorem algebraMap_matrix_apply {r : R} {i j : n} :
    algebraMap R (Matrix n n α) r i j = if i = j then algebraMap R α r else 0 := by
  dsimp [algebraMap, Algebra.toRingHom, Matrix.scalar]
  -- ⊢ ↑Algebra.toRingHom r * OfNat.ofNat 1 i j = if i = j then ↑Algebra.toRingHom  …
  split_ifs with h <;> simp [h, Matrix.one_apply_ne]
  -- ⊢ ↑Algebra.toRingHom r * OfNat.ofNat 1 i j = ↑Algebra.toRingHom r
                       -- 🎉 no goals
                       -- 🎉 no goals
#align matrix.algebra_map_matrix_apply Matrix.algebraMap_matrix_apply

theorem algebraMap_eq_diagonal (r : R) :
    algebraMap R (Matrix n n α) r = diagonal (algebraMap R (n → α) r) :=
  Matrix.ext fun _ _ => algebraMap_matrix_apply
#align matrix.algebra_map_eq_diagonal Matrix.algebraMap_eq_diagonal

@[simp]
theorem algebraMap_eq_smul (r : R) : algebraMap R (Matrix n n R) r = r • (1 : Matrix n n R) :=
  rfl
#align matrix.algebra_map_eq_smul Matrix.algebraMap_eq_smul

theorem algebraMap_eq_diagonalRingHom :
    algebraMap R (Matrix n n α) = (diagonalRingHom n α).comp (algebraMap R _) :=
  RingHom.ext algebraMap_eq_diagonal
#align matrix.algebra_map_eq_diagonal_ring_hom Matrix.algebraMap_eq_diagonalRingHom

@[simp]
theorem map_algebraMap (r : R) (f : α → β) (hf : f 0 = 0)
    (hf₂ : f (algebraMap R α r) = algebraMap R β r) :
    (algebraMap R (Matrix n n α) r).map f = algebraMap R (Matrix n n β) r := by
  rw [algebraMap_eq_diagonal, algebraMap_eq_diagonal, diagonal_map hf]
  -- ⊢ (diagonal fun m => f (↑(algebraMap R (n → α)) r m)) = diagonal (↑(algebraMap …
  -- Porting note: (congr) the remaining proof was
  -- ```
  -- congr 1
  -- simp only [hf₂, Pi.algebraMap_apply]
  -- ```
  -- But some `congr 1` doesn't quite work.
  simp only [Pi.algebraMap_apply, diagonal_eq_diagonal_iff]
  -- ⊢ n → f (↑(algebraMap R α) r) = ↑(algebraMap R β) r
  intro
  -- ⊢ f (↑(algebraMap R α) r) = ↑(algebraMap R β) r
  rw [hf₂]
  -- 🎉 no goals
#align matrix.map_algebra_map Matrix.map_algebraMap

variable (R)

/-- `Matrix.diagonal` as an `AlgHom`. -/
@[simps]
def diagonalAlgHom : (n → α) →ₐ[R] Matrix n n α :=
  { diagonalRingHom n α with
    toFun := diagonal
    commutes' := fun r => (algebraMap_eq_diagonal r).symm }
#align matrix.diagonal_alg_hom Matrix.diagonalAlgHom

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
#align equiv.map_matrix Equiv.mapMatrix

@[simp]
theorem mapMatrix_refl : (Equiv.refl α).mapMatrix = Equiv.refl (Matrix m n α) :=
  rfl
#align equiv.map_matrix_refl Equiv.mapMatrix_refl

@[simp]
theorem mapMatrix_symm (f : α ≃ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ _) :=
  rfl
#align equiv.map_matrix_symm Equiv.mapMatrix_symm

@[simp]
theorem mapMatrix_trans (f : α ≃ β) (g : β ≃ γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ _) :=
  rfl
#align equiv.map_matrix_trans Equiv.mapMatrix_trans

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
#align add_monoid_hom.map_matrix AddMonoidHom.mapMatrix

@[simp]
theorem mapMatrix_id : (AddMonoidHom.id α).mapMatrix = AddMonoidHom.id (Matrix m n α) :=
  rfl
#align add_monoid_hom.map_matrix_id AddMonoidHom.mapMatrix_id

@[simp]
theorem mapMatrix_comp (f : β →+ γ) (g : α →+ β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α →+ _) :=
  rfl
#align add_monoid_hom.map_matrix_comp AddMonoidHom.mapMatrix_comp

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
    map_add' := Matrix.map_add f f.map_add }
#align add_equiv.map_matrix AddEquiv.mapMatrix

@[simp]
theorem mapMatrix_refl : (AddEquiv.refl α).mapMatrix = AddEquiv.refl (Matrix m n α) :=
  rfl
#align add_equiv.map_matrix_refl AddEquiv.mapMatrix_refl

@[simp]
theorem mapMatrix_symm (f : α ≃+ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃+ _) :=
  rfl
#align add_equiv.map_matrix_symm AddEquiv.mapMatrix_symm

@[simp]
theorem mapMatrix_trans (f : α ≃+ β) (g : β ≃+ γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃+ _) :=
  rfl
#align add_equiv.map_matrix_trans AddEquiv.mapMatrix_trans

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
#align linear_map.map_matrix LinearMap.mapMatrix

@[simp]
theorem mapMatrix_id : LinearMap.id.mapMatrix = (LinearMap.id : Matrix m n α →ₗ[R] _) :=
  rfl
#align linear_map.map_matrix_id LinearMap.mapMatrix_id

@[simp]
theorem mapMatrix_comp (f : β →ₗ[R] γ) (g : α →ₗ[R] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α →ₗ[R] _) :=
  rfl
#align linear_map.map_matrix_comp LinearMap.mapMatrix_comp

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
#align linear_equiv.map_matrix LinearEquiv.mapMatrix

@[simp]
theorem mapMatrix_refl : (LinearEquiv.refl R α).mapMatrix = LinearEquiv.refl R (Matrix m n α) :=
  rfl
#align linear_equiv.map_matrix_refl LinearEquiv.mapMatrix_refl

@[simp]
theorem mapMatrix_symm (f : α ≃ₗ[R] β) :
    f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ₗ[R] _) :=
  rfl
#align linear_equiv.map_matrix_symm LinearEquiv.mapMatrix_symm

@[simp]
theorem mapMatrix_trans (f : α ≃ₗ[R] β) (g : β ≃ₗ[R] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ₗ[R] _) :=
  rfl
#align linear_equiv.map_matrix_trans LinearEquiv.mapMatrix_trans

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
                   -- 🎉 no goals
    map_mul' := fun L M => Matrix.map_mul }
#align ring_hom.map_matrix RingHom.mapMatrix

@[simp]
theorem mapMatrix_id : (RingHom.id α).mapMatrix = RingHom.id (Matrix m m α) :=
  rfl
#align ring_hom.map_matrix_id RingHom.mapMatrix_id

@[simp]
theorem mapMatrix_comp (f : β →+* γ) (g : α →+* β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α →+* _) :=
  rfl
#align ring_hom.map_matrix_comp RingHom.mapMatrix_comp

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
#align ring_equiv.map_matrix RingEquiv.mapMatrix

@[simp]
theorem mapMatrix_refl : (RingEquiv.refl α).mapMatrix = RingEquiv.refl (Matrix m m α) :=
  rfl
#align ring_equiv.map_matrix_refl RingEquiv.mapMatrix_refl

@[simp]
theorem mapMatrix_symm (f : α ≃+* β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃+* _) :=
  rfl
#align ring_equiv.map_matrix_symm RingEquiv.mapMatrix_symm

@[simp]
theorem mapMatrix_trans (f : α ≃+* β) (g : β ≃+* γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m m α ≃+* _) :=
  rfl
#align ring_equiv.map_matrix_trans RingEquiv.mapMatrix_trans

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
    commutes' := fun r => Matrix.map_algebraMap r f f.map_zero (f.commutes r) }
#align alg_hom.map_matrix AlgHom.mapMatrix

@[simp]
theorem mapMatrix_id : (AlgHom.id R α).mapMatrix = AlgHom.id R (Matrix m m α) :=
  rfl
#align alg_hom.map_matrix_id AlgHom.mapMatrix_id

@[simp]
theorem mapMatrix_comp (f : β →ₐ[R] γ) (g : α →ₐ[R] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α →ₐ[R] _) :=
  rfl
#align alg_hom.map_matrix_comp AlgHom.mapMatrix_comp

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
#align alg_equiv.map_matrix AlgEquiv.mapMatrix

@[simp]
theorem mapMatrix_refl : AlgEquiv.refl.mapMatrix = (AlgEquiv.refl : Matrix m m α ≃ₐ[R] _) :=
  rfl
#align alg_equiv.map_matrix_refl AlgEquiv.mapMatrix_refl

@[simp]
theorem mapMatrix_symm (f : α ≃ₐ[R] β) :
    f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃ₐ[R] _) :=
  rfl
#align alg_equiv.map_matrix_symm AlgEquiv.mapMatrix_symm

@[simp]
theorem mapMatrix_trans (f : α ≃ₐ[R] β) (g : β ≃ₐ[R] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m m α ≃ₐ[R] _) :=
  rfl
#align alg_equiv.map_matrix_trans AlgEquiv.mapMatrix_trans

end AlgEquiv

open Matrix

namespace Matrix

/-- For two vectors `w` and `v`, `vecMulVec w v i j` is defined to be `w i * v j`.
    Put another way, `vecMulVec w v` is exactly `col w * row v`. -/
def vecMulVec [Mul α] (w : m → α) (v : n → α) : Matrix m n α :=
  of fun x y => w x * v y
#align matrix.vec_mul_vec Matrix.vecMulVec

-- TODO: set as an equation lemma for `vecMulVec`, see mathlib4#3024
theorem vecMulVec_apply [Mul α] (w : m → α) (v : n → α) (i j) : vecMulVec w v i j = w i * v j :=
  rfl
#align matrix.vec_mul_vec_apply Matrix.vecMulVec_apply

theorem vecMulVec_eq [Mul α] [AddCommMonoid α] (w : m → α) (v : n → α) :
    vecMulVec w v = col w * row v := by
  ext
  -- ⊢ vecMulVec w v i✝ x✝ = (col w * row v) i✝ x✝
  simp only [vecMulVec, mul_apply, Fintype.univ_punit, Finset.sum_singleton]
  -- ⊢ ↑of (fun x y => w x * v y) i✝ x✝ = col w i✝ PUnit.unit * row v PUnit.unit x✝
  rfl
  -- 🎉 no goals
#align matrix.vec_mul_vec_eq Matrix.vecMulVec_eq

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

/-- `mulVec M v` is the matrix-vector product of `M` and `v`, where `v` is seen as a column matrix.
    Put another way, `mulVec M v` is the vector whose entries
    are those of `M * col v` (see `col_mulVec`). -/
def mulVec [Fintype n] (M : Matrix m n α) (v : n → α) : m → α
  | i => (fun j => M i j) ⬝ᵥ v
#align matrix.mul_vec Matrix.mulVec

/-- `vecMul v M` is the vector-matrix product of `v` and `M`, where `v` is seen as a row matrix.
    Put another way, `vecMul v M` is the vector whose entries
    are those of `row v * M` (see `row_vecMul`). -/
def vecMul [Fintype m] (v : m → α) (M : Matrix m n α) : n → α
  | j => v ⬝ᵥ fun i => M i j
#align matrix.vec_mul Matrix.vecMul

/-- Left multiplication by a matrix, as an `AddMonoidHom` from vectors to vectors. -/
@[simps]
def mulVec.addMonoidHomLeft [Fintype n] (v : n → α) : Matrix m n α →+ m → α where
  toFun M := mulVec M v
  map_zero' := by
    ext
    -- ⊢ (fun M => mulVec M v) 0 x✝ = OfNat.ofNat 0 x✝
    simp [mulVec]
    -- 🎉 no goals
  map_add' x y := by
    ext m
    -- ⊢ ZeroHom.toFun { toFun := fun M => mulVec M v, map_zero' := (_ : (fun M => mu …
    apply add_dotProduct
    -- 🎉 no goals
#align matrix.mul_vec.add_monoid_hom_left Matrix.mulVec.addMonoidHomLeft

theorem mulVec_diagonal [Fintype m] [DecidableEq m] (v w : m → α) (x : m) :
    mulVec (diagonal v) w x = v x * w x :=
  diagonal_dotProduct v w x
#align matrix.mul_vec_diagonal Matrix.mulVec_diagonal

theorem vecMul_diagonal [Fintype m] [DecidableEq m] (v w : m → α) (x : m) :
    vecMul v (diagonal w) x = v x * w x :=
  dotProduct_diagonal' v w x
#align matrix.vec_mul_diagonal Matrix.vecMul_diagonal

/-- Associate the dot product of `mulVec` to the left. -/
theorem dotProduct_mulVec [Fintype n] [Fintype m] [NonUnitalSemiring R] (v : m → R)
    (A : Matrix m n R) (w : n → R) : v ⬝ᵥ mulVec A w = vecMul v A ⬝ᵥ w := by
  simp only [dotProduct, vecMul, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  -- ⊢ ∑ x : m, ∑ x_1 : n, v x * (A x x_1 * w x_1) = ∑ x : n, ∑ x_1 : m, v x_1 * (A …
  exact Finset.sum_comm
  -- 🎉 no goals
#align matrix.dot_product_mul_vec Matrix.dotProduct_mulVec

@[simp]
theorem mulVec_zero [Fintype n] (A : Matrix m n α) : mulVec A 0 = 0 := by
  ext
  -- ⊢ mulVec A 0 x✝ = OfNat.ofNat 0 x✝
  simp [mulVec]
  -- 🎉 no goals
#align matrix.mul_vec_zero Matrix.mulVec_zero

@[simp]
theorem zero_vecMul [Fintype m] (A : Matrix m n α) : vecMul 0 A = 0 := by
  ext
  -- ⊢ vecMul 0 A x✝ = OfNat.ofNat 0 x✝
  simp [vecMul]
  -- 🎉 no goals
#align matrix.zero_vec_mul Matrix.zero_vecMul

@[simp]
theorem zero_mulVec [Fintype n] (v : n → α) : mulVec (0 : Matrix m n α) v = 0 := by
  ext
  -- ⊢ mulVec 0 v x✝ = OfNat.ofNat 0 x✝
  simp [mulVec]
  -- 🎉 no goals
#align matrix.zero_mul_vec Matrix.zero_mulVec

@[simp]
theorem vecMul_zero [Fintype m] (v : m → α) : vecMul v (0 : Matrix m n α) = 0 := by
  ext
  -- ⊢ vecMul v 0 x✝ = OfNat.ofNat 0 x✝
  simp [vecMul]
  -- 🎉 no goals
#align matrix.vec_mul_zero Matrix.vecMul_zero

theorem smul_mulVec_assoc [Fintype n] [Monoid R] [DistribMulAction R α] [IsScalarTower R α α]
    (a : R) (A : Matrix m n α) (b : n → α) : (a • A).mulVec b = a • A.mulVec b := by
  ext
  -- ⊢ mulVec (a • A) b x✝ = (a • mulVec A b) x✝
  apply smul_dotProduct
  -- 🎉 no goals
#align matrix.smul_mul_vec_assoc Matrix.smul_mulVec_assoc

theorem mulVec_add [Fintype n] (A : Matrix m n α) (x y : n → α) :
    A.mulVec (x + y) = A.mulVec x + A.mulVec y := by
  ext
  -- ⊢ mulVec A (x + y) x✝ = (mulVec A x + mulVec A y) x✝
  apply dotProduct_add
  -- 🎉 no goals
#align matrix.mul_vec_add Matrix.mulVec_add

theorem add_mulVec [Fintype n] (A B : Matrix m n α) (x : n → α) :
    (A + B).mulVec x = A.mulVec x + B.mulVec x := by
  ext
  -- ⊢ mulVec (A + B) x x✝ = (mulVec A x + mulVec B x) x✝
  apply add_dotProduct
  -- 🎉 no goals
#align matrix.add_mul_vec Matrix.add_mulVec

theorem vecMul_add [Fintype m] (A B : Matrix m n α) (x : m → α) :
    vecMul x (A + B) = vecMul x A + vecMul x B := by
  ext
  -- ⊢ vecMul x (A + B) x✝ = (vecMul x A + vecMul x B) x✝
  apply dotProduct_add
  -- 🎉 no goals
#align matrix.vec_mul_add Matrix.vecMul_add

theorem add_vecMul [Fintype m] (A : Matrix m n α) (x y : m → α) :
    vecMul (x + y) A = vecMul x A + vecMul y A := by
  ext
  -- ⊢ vecMul (x + y) A x✝ = (vecMul x A + vecMul y A) x✝
  apply add_dotProduct
  -- 🎉 no goals
#align matrix.add_vec_mul Matrix.add_vecMul

theorem vecMul_smul [Fintype n] [Monoid R] [NonUnitalNonAssocSemiring S] [DistribMulAction R S]
    [IsScalarTower R S S] (M : Matrix n m S) (b : R) (v : n → S) :
    M.vecMul (b • v) = b • M.vecMul v := by
  ext i
  -- ⊢ vecMul (b • v) M i = (b • vecMul v M) i
  simp only [vecMul, dotProduct, Finset.smul_sum, Pi.smul_apply, smul_mul_assoc]
  -- 🎉 no goals
#align matrix.vec_mul_smul Matrix.vecMul_smul

theorem mulVec_smul [Fintype n] [Monoid R] [NonUnitalNonAssocSemiring S] [DistribMulAction R S]
    [SMulCommClass R S S] (M : Matrix m n S) (b : R) (v : n → S) :
    M.mulVec (b • v) = b • M.mulVec v := by
  ext i
  -- ⊢ mulVec M (b • v) i = (b • mulVec M v) i
  simp only [mulVec, dotProduct, Finset.smul_sum, Pi.smul_apply, mul_smul_comm]
  -- 🎉 no goals
#align matrix.mul_vec_smul Matrix.mulVec_smul

@[simp]
theorem mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
    (j : n) (x : R) : M.mulVec (Pi.single j x) = fun i => M i j * x :=
  funext fun _ => dotProduct_single _ _ _
#align matrix.mul_vec_single Matrix.mulVec_single

@[simp]
theorem single_vecMul [Fintype m] [DecidableEq m] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
    (i : m) (x : R) : vecMul (Pi.single i x) M = fun j => x * M i j :=
  funext fun _ => single_dotProduct _ _ _
#align matrix.single_vec_mul Matrix.single_vecMul

-- @[simp] -- Porting note: not in simpNF
theorem diagonal_mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n → R)
    (j : n) (x : R) : (diagonal v).mulVec (Pi.single j x) = Pi.single j (v j * x) := by
  ext i
  -- ⊢ mulVec (diagonal v) (Pi.single j x) i = Pi.single j (v j * x) i
  rw [mulVec_diagonal]
  -- ⊢ v i * Pi.single j x i = Pi.single j (v j * x) i
  exact Pi.apply_single (fun i x => v i * x) (fun i => mul_zero _) j x i
  -- 🎉 no goals
#align matrix.diagonal_mul_vec_single Matrix.diagonal_mulVec_single

-- @[simp] -- Porting note: not in simpNF
theorem single_vecMul_diagonal [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n → R)
    (j : n) (x : R) : vecMul (Pi.single j x) (diagonal v) = Pi.single j (x * v j) := by
  ext i
  -- ⊢ vecMul (Pi.single j x) (diagonal v) i = Pi.single j (x * v j) i
  rw [vecMul_diagonal]
  -- ⊢ Pi.single j x i * v i = Pi.single j (x * v j) i
  exact Pi.apply_single (fun i x => x * v i) (fun i => zero_mul _) j x i
  -- 🎉 no goals
#align matrix.single_vec_mul_diagonal Matrix.single_vecMul_diagonal

end NonUnitalNonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring α]

@[simp]
theorem vecMul_vecMul [Fintype n] [Fintype m] (v : m → α) (M : Matrix m n α) (N : Matrix n o α) :
    vecMul (vecMul v M) N = vecMul v (M * N) := by
  ext
  -- ⊢ vecMul (vecMul v M) N x✝ = vecMul v (M * N) x✝
  apply dotProduct_assoc
  -- 🎉 no goals
#align matrix.vec_mul_vec_mul Matrix.vecMul_vecMul

@[simp]
theorem mulVec_mulVec [Fintype n] [Fintype o] (v : o → α) (M : Matrix m n α) (N : Matrix n o α) :
    mulVec M (mulVec N v) = mulVec (M * N) v := by
  ext
  -- ⊢ mulVec M (mulVec N v) x✝ = mulVec (M * N) v x✝
  symm
  -- ⊢ mulVec (M * N) v x✝ = mulVec M (mulVec N v) x✝
  apply dotProduct_assoc
  -- 🎉 no goals
#align matrix.mul_vec_mul_vec Matrix.mulVec_mulVec

theorem star_mulVec [Fintype n] [StarRing α] (M : Matrix m n α) (v : n → α) :
    star (M.mulVec v) = vecMul (star v) Mᴴ :=
  funext fun _ => (star_dotProduct_star _ _).symm
#align matrix.star_mul_vec Matrix.star_mulVec

theorem star_vecMul [Fintype m] [StarRing α] (M : Matrix m n α) (v : m → α) :
    star (M.vecMul v) = Mᴴ.mulVec (star v) :=
  funext fun _ => (star_dotProduct_star _ _).symm
#align matrix.star_vec_mul Matrix.star_vecMul

theorem mulVec_conjTranspose [Fintype m] [StarRing α] (A : Matrix m n α) (x : m → α) :
    mulVec Aᴴ x = star (vecMul (star x) A) :=
  funext fun _ => star_dotProduct _ _
#align matrix.mul_vec_conj_transpose Matrix.mulVec_conjTranspose

theorem vecMul_conjTranspose [Fintype n] [StarRing α] (A : Matrix m n α) (x : n → α) :
    vecMul x Aᴴ = star (mulVec A (star x)) :=
  funext fun _ => dotProduct_star _ _
#align matrix.vec_mul_conj_transpose Matrix.vecMul_conjTranspose

theorem mul_mul_apply [Fintype n] (A B C : Matrix n n α) (i j : n) :
    (A * B * C) i j = A i ⬝ᵥ B.mulVec (Cᵀ j) := by
  rw [Matrix.mul_assoc]
  -- ⊢ (A * (B * C)) i j = A i ⬝ᵥ mulVec B (Cᵀ j)
  simp only [mul_apply, dotProduct, mulVec]
  -- ⊢ ∑ x : n, A i x * ∑ j_1 : n, B x j_1 * C j_1 j = ∑ x : n, A i x * ∑ x_1 : n,  …
  rfl
  -- 🎉 no goals
#align matrix.mul_mul_apply Matrix.mul_mul_apply

end NonUnitalSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

theorem mulVec_one [Fintype n] (A : Matrix m n α) : mulVec A 1 = fun i => ∑ j, A i j := by
  ext; simp [mulVec, dotProduct]
  -- ⊢ mulVec A 1 x✝ = ∑ j : n, A x✝ j
       -- 🎉 no goals
#align matrix.mul_vec_one Matrix.mulVec_one

theorem vec_one_mul [Fintype m] (A : Matrix m n α) : vecMul 1 A = fun j => ∑ i, A i j := by
  ext; simp [vecMul, dotProduct]
  -- ⊢ vecMul 1 A x✝ = ∑ i : m, A i x✝
       -- 🎉 no goals
#align matrix.vec_one_mul Matrix.vec_one_mul

variable [Fintype m] [Fintype n] [DecidableEq m]

@[simp]
theorem one_mulVec (v : m → α) : mulVec 1 v = v := by
  ext
  -- ⊢ mulVec 1 v x✝ = v x✝
  rw [← diagonal_one, mulVec_diagonal, one_mul]
  -- 🎉 no goals
#align matrix.one_mul_vec Matrix.one_mulVec

@[simp]
theorem vecMul_one (v : m → α) : vecMul v 1 = v := by
  ext
  -- ⊢ vecMul v 1 x✝ = v x✝
  rw [← diagonal_one, vecMul_diagonal, mul_one]
  -- 🎉 no goals
#align matrix.vec_mul_one Matrix.vecMul_one

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

theorem neg_vecMul [Fintype m] (v : m → α) (A : Matrix m n α) : vecMul (-v) A = -vecMul v A := by
  ext
  -- ⊢ vecMul (-v) A x✝ = (-vecMul v A) x✝
  apply neg_dotProduct
  -- 🎉 no goals
#align matrix.neg_vec_mul Matrix.neg_vecMul

theorem vecMul_neg [Fintype m] (v : m → α) (A : Matrix m n α) : vecMul v (-A) = -vecMul v A := by
  ext
  -- ⊢ vecMul v (-A) x✝ = (-vecMul v A) x✝
  apply dotProduct_neg
  -- 🎉 no goals
#align matrix.vec_mul_neg Matrix.vecMul_neg

theorem neg_mulVec [Fintype n] (v : n → α) (A : Matrix m n α) : mulVec (-A) v = -mulVec A v := by
  ext
  -- ⊢ mulVec (-A) v x✝ = (-mulVec A v) x✝
  apply neg_dotProduct
  -- 🎉 no goals
#align matrix.neg_mul_vec Matrix.neg_mulVec

theorem mulVec_neg [Fintype n] (v : n → α) (A : Matrix m n α) : mulVec A (-v) = -mulVec A v := by
  ext
  -- ⊢ mulVec A (-v) x✝ = (-mulVec A v) x✝
  apply dotProduct_neg
  -- 🎉 no goals
#align matrix.mul_vec_neg Matrix.mulVec_neg

theorem sub_mulVec [Fintype n] (A B : Matrix m n α) (x : n → α) :
    mulVec (A - B) x = mulVec A x - mulVec B x := by simp [sub_eq_add_neg, add_mulVec, neg_mulVec]
                                                     -- 🎉 no goals
#align matrix.sub_mul_vec Matrix.sub_mulVec

theorem vecMul_sub [Fintype m] (A B : Matrix m n α) (x : m → α) :
    vecMul x (A - B) = vecMul x A - vecMul x B := by simp [sub_eq_add_neg, vecMul_add, vecMul_neg]
                                                     -- 🎉 no goals
#align matrix.vec_mul_sub Matrix.vecMul_sub

end NonUnitalNonAssocRing

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α]

theorem mulVec_transpose [Fintype m] (A : Matrix m n α) (x : m → α) : mulVec Aᵀ x = vecMul x A := by
  ext
  -- ⊢ mulVec Aᵀ x x✝ = vecMul x A x✝
  apply dotProduct_comm
  -- 🎉 no goals
#align matrix.mul_vec_transpose Matrix.mulVec_transpose

theorem vecMul_transpose [Fintype n] (A : Matrix m n α) (x : n → α) : vecMul x Aᵀ = mulVec A x := by
  ext
  -- ⊢ vecMul x Aᵀ x✝ = mulVec A x x✝
  apply dotProduct_comm
  -- 🎉 no goals
#align matrix.vec_mul_transpose Matrix.vecMul_transpose

theorem mulVec_vecMul [Fintype n] [Fintype o] (A : Matrix m n α) (B : Matrix o n α) (x : o → α) :
    mulVec A (vecMul x B) = mulVec (A * Bᵀ) x := by rw [← mulVec_mulVec, mulVec_transpose]
                                                    -- 🎉 no goals
#align matrix.mul_vec_vec_mul Matrix.mulVec_vecMul

theorem vecMul_mulVec [Fintype m] [Fintype n] (A : Matrix m n α) (B : Matrix m o α) (x : n → α) :
    vecMul (mulVec A x) B = vecMul x (Aᵀ * B) := by rw [← vecMul_vecMul, vecMul_transpose]
                                                    -- 🎉 no goals
#align matrix.vec_mul_mul_vec Matrix.vecMul_mulVec

end NonUnitalCommSemiring

section CommSemiring

variable [CommSemiring α]

theorem mulVec_smul_assoc [Fintype n] (A : Matrix m n α) (b : n → α) (a : α) :
    A.mulVec (a • b) = a • A.mulVec b := by
  ext
  -- ⊢ mulVec A (a • b) x✝ = (a • mulVec A b) x✝
  apply dotProduct_smul
  -- 🎉 no goals
#align matrix.mul_vec_smul_assoc Matrix.mulVec_smul_assoc

end CommSemiring

section Transpose

open Matrix

@[simp]
theorem transpose_transpose (M : Matrix m n α) : Mᵀᵀ = M := by
  ext
  -- ⊢ Mᵀᵀ i✝ x✝ = M i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.transpose_transpose Matrix.transpose_transpose

theorem transpose_injective : Function.Injective (transpose : Matrix m n α → Matrix n m α) :=
  fun _ _ h => ext fun i j => ext_iff.2 h j i

@[simp] theorem transpose_inj {A B : Matrix m n α} : Aᵀ = Bᵀ ↔ A = B := transpose_injective.eq_iff

@[simp]
theorem transpose_zero [Zero α] : (0 : Matrix m n α)ᵀ = 0 := by
  ext
  -- ⊢ 0ᵀ i✝ x✝ = OfNat.ofNat 0 i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.transpose_zero Matrix.transpose_zero

@[simp]
theorem transpose_eq_zero [Zero α] {M : Matrix m n α} : Mᵀ = 0 ↔ M = 0 := transpose_inj

@[simp]
theorem transpose_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α)ᵀ = 1 := by
  ext i j
  -- ⊢ 1ᵀ i j = OfNat.ofNat 1 i j
  rw [transpose_apply, ← diagonal_one]
  -- ⊢ diagonal (fun x => 1) j i = diagonal (fun x => 1) i j
  by_cases i = j
  -- ⊢ diagonal (fun x => 1) j i = diagonal (fun x => 1) i j
  -- ⊢ diagonal (fun x => 1) j i = diagonal (fun x => 1) i j
  · simp only [h, diagonal_apply_eq]
    -- 🎉 no goals
  · simp only [diagonal_apply_ne _ h, diagonal_apply_ne' _ h]
    -- 🎉 no goals
#align matrix.transpose_one Matrix.transpose_one

@[simp]
theorem transpose_eq_one [DecidableEq n] [Zero α] [One α] {M : Matrix n n α} : Mᵀ = 1 ↔ M = 1 :=
  (Function.Involutive.eq_iff transpose_transpose).trans <| by rw [transpose_one]
                                                               -- 🎉 no goals

@[simp]
theorem transpose_add [Add α] (M : Matrix m n α) (N : Matrix m n α) : (M + N)ᵀ = Mᵀ + Nᵀ := by
  ext
  -- ⊢ (M + N)ᵀ i✝ x✝ = (Mᵀ + Nᵀ) i✝ x✝
  simp
  -- 🎉 no goals
#align matrix.transpose_add Matrix.transpose_add

@[simp]
theorem transpose_sub [Sub α] (M : Matrix m n α) (N : Matrix m n α) : (M - N)ᵀ = Mᵀ - Nᵀ := by
  ext
  -- ⊢ (M - N)ᵀ i✝ x✝ = (Mᵀ - Nᵀ) i✝ x✝
  simp
  -- 🎉 no goals
#align matrix.transpose_sub Matrix.transpose_sub

@[simp]
theorem transpose_mul [AddCommMonoid α] [CommSemigroup α] [Fintype n] (M : Matrix m n α)
    (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ := by
  ext
  -- ⊢ (M * N)ᵀ i✝ x✝ = (Nᵀ * Mᵀ) i✝ x✝
  apply dotProduct_comm
  -- 🎉 no goals
#align matrix.transpose_mul Matrix.transpose_mul

@[simp]
theorem transpose_smul {R : Type*} [SMul R α] (c : R) (M : Matrix m n α) : (c • M)ᵀ = c • Mᵀ := by
  ext
  -- ⊢ (c • M)ᵀ i✝ x✝ = (c • Mᵀ) i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.transpose_smul Matrix.transpose_smul

@[simp]
theorem transpose_neg [Neg α] (M : Matrix m n α) : (-M)ᵀ = -Mᵀ := by
  ext
  -- ⊢ (-M)ᵀ i✝ x✝ = (-Mᵀ) i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.transpose_neg Matrix.transpose_neg

theorem transpose_map {f : α → β} {M : Matrix m n α} : Mᵀ.map f = (M.map f)ᵀ := by
  ext
  -- ⊢ map Mᵀ f i✝ x✝ = (map M f)ᵀ i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.transpose_map Matrix.transpose_map

variable (m n α)

/-- `Matrix.transpose` as an `AddEquiv` -/
@[simps apply]
def transposeAddEquiv [Add α] : Matrix m n α ≃+ Matrix n m α where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose
  map_add' := transpose_add
#align matrix.transpose_add_equiv Matrix.transposeAddEquiv

@[simp]
theorem transposeAddEquiv_symm [Add α] : (transposeAddEquiv m n α).symm = transposeAddEquiv n m α :=
  rfl
#align matrix.transpose_add_equiv_symm Matrix.transposeAddEquiv_symm

variable {m n α}

theorem transpose_list_sum [AddMonoid α] (l : List (Matrix m n α)) :
    l.sumᵀ = (l.map transpose).sum :=
  (transposeAddEquiv m n α).toAddMonoidHom.map_list_sum l
#align matrix.transpose_list_sum Matrix.transpose_list_sum

theorem transpose_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix m n α)) :
    s.sumᵀ = (s.map transpose).sum :=
  (transposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s
#align matrix.transpose_multiset_sum Matrix.transpose_multiset_sum

theorem transpose_sum [AddCommMonoid α] {ι : Type*} (s : Finset ι) (M : ι → Matrix m n α) :
    (∑ i in s, M i)ᵀ = ∑ i in s, (M i)ᵀ :=
  (transposeAddEquiv m n α).toAddMonoidHom.map_sum _ s
#align matrix.transpose_sum Matrix.transpose_sum

variable (m n R α)

/-- `Matrix.transpose` as a `LinearMap` -/
@[simps apply]
def transposeLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] :
    Matrix m n α ≃ₗ[R] Matrix n m α :=
  { transposeAddEquiv m n α with map_smul' := transpose_smul }
#align matrix.transpose_linear_equiv Matrix.transposeLinearEquiv

@[simp]
theorem transposeLinearEquiv_symm [Semiring R] [AddCommMonoid α] [Module R α] :
    (transposeLinearEquiv m n R α).symm = transposeLinearEquiv n m R α :=
  rfl
#align matrix.transpose_linear_equiv_symm Matrix.transposeLinearEquiv_symm

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
#align matrix.transpose_ring_equiv Matrix.transposeRingEquiv

variable {m α}

@[simp]
theorem transpose_pow [CommSemiring α] [Fintype m] [DecidableEq m] (M : Matrix m m α) (k : ℕ) :
    (M ^ k)ᵀ = Mᵀ ^ k :=
  MulOpposite.op_injective <| map_pow (transposeRingEquiv m α) M k
#align matrix.transpose_pow Matrix.transpose_pow

theorem transpose_list_prod [CommSemiring α] [Fintype m] [DecidableEq m] (l : List (Matrix m m α)) :
    l.prodᵀ = (l.map transpose).reverse.prod :=
  (transposeRingEquiv m α).unop_map_list_prod l
#align matrix.transpose_list_prod Matrix.transpose_list_prod

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
      -- 🎉 no goals
#align matrix.transpose_alg_equiv Matrix.transposeAlgEquiv

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
#align matrix.conj_transpose_apply Matrix.conjTranspose_apply

@[simp]
theorem conjTranspose_conjTranspose [InvolutiveStar α] (M : Matrix m n α) : Mᴴᴴ = M :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_conj_transpose Matrix.conjTranspose_conjTranspose

theorem conjTranspose_injective [InvolutiveStar α] :
    Function.Injective (conjTranspose : Matrix m n α → Matrix n m α) :=
  (map_injective star_injective).comp transpose_injective

@[simp] theorem conjTranspose_inj [InvolutiveStar α] {A B : Matrix m n α} : Aᴴ = Bᴴ ↔ A = B :=
  conjTranspose_injective.eq_iff

@[simp]
theorem conjTranspose_zero [AddMonoid α] [StarAddMonoid α] : (0 : Matrix m n α)ᴴ = 0 :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_zero Matrix.conjTranspose_zero

@[simp]
theorem conjTranspose_eq_zero [AddMonoid α] [StarAddMonoid α] {M : Matrix m n α} :
    Mᴴ = 0 ↔ M = 0 :=
  by rw [←conjTranspose_inj (A := M), conjTranspose_zero]
     -- 🎉 no goals

@[simp]
theorem conjTranspose_one [DecidableEq n] [Semiring α] [StarRing α] : (1 : Matrix n n α)ᴴ = 1 := by
  simp [conjTranspose]
  -- 🎉 no goals
#align matrix.conj_transpose_one Matrix.conjTranspose_one

@[simp]
theorem conjTranspose_eq_one [DecidableEq n] [Semiring α] [StarRing α] {M : Matrix n n α} :
    Mᴴ = 1 ↔ M = 1 :=
  (Function.Involutive.eq_iff conjTranspose_conjTranspose).trans <|
    by rw [conjTranspose_one]
       -- 🎉 no goals

@[simp]
theorem conjTranspose_add [AddMonoid α] [StarAddMonoid α] (M N : Matrix m n α) :
    (M + N)ᴴ = Mᴴ + Nᴴ :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_add Matrix.conjTranspose_add

@[simp]
theorem conjTranspose_sub [AddGroup α] [StarAddMonoid α] (M N : Matrix m n α) :
    (M - N)ᴴ = Mᴴ - Nᴴ :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_sub Matrix.conjTranspose_sub

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
#align matrix.conj_transpose_smul Matrix.conjTranspose_smul

@[simp]
theorem conjTranspose_smul_non_comm [Star R] [Star α] [SMul R α] [SMul Rᵐᵒᵖ α] (c : R)
    (M : Matrix m n α) (h : ∀ (r : R) (a : α), star (r • a) = MulOpposite.op (star r) • star a) :
    (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ :=
  Matrix.ext <| by simp [h]
                   -- 🎉 no goals
#align matrix.conj_transpose_smul_non_comm Matrix.conjTranspose_smul_non_comm

-- @[simp] -- Porting note: simp can prove this
theorem conjTranspose_smul_self [Semigroup α] [StarSemigroup α] (c : α) (M : Matrix m n α) :
    (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ :=
  conjTranspose_smul_non_comm c M star_mul
#align matrix.conj_transpose_smul_self Matrix.conjTranspose_smul_self

@[simp]
theorem conjTranspose_nsmul [AddMonoid α] [StarAddMonoid α] (c : ℕ) (M : Matrix m n α) :
    (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_nsmul Matrix.conjTranspose_nsmul

@[simp]
theorem conjTranspose_zsmul [AddGroup α] [StarAddMonoid α] (c : ℤ) (M : Matrix m n α) :
    (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_zsmul Matrix.conjTranspose_zsmul

@[simp]
theorem conjTranspose_natCast_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
    (c : ℕ) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_nat_cast_smul Matrix.conjTranspose_natCast_smul

@[simp]
theorem conjTranspose_intCast_smul [Ring R] [AddCommGroup α] [StarAddMonoid α] [Module R α] (c : ℤ)
    (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_int_cast_smul Matrix.conjTranspose_intCast_smul

@[simp]
theorem conjTranspose_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] (c : ℕ) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻¹ • Mᴴ :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_inv_nat_cast_smul Matrix.conjTranspose_inv_natCast_smul

@[simp]
theorem conjTranspose_inv_intCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoid α]
    [Module R α] (c : ℤ) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻¹ • Mᴴ :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_inv_int_cast_smul Matrix.conjTranspose_inv_intCast_smul

@[simp]
theorem conjTranspose_ratCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoid α] [Module R α]
    (c : ℚ) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_rat_cast_smul Matrix.conjTranspose_ratCast_smul

@[simp]
theorem conjTranspose_rat_smul [AddCommGroup α] [StarAddMonoid α] [Module ℚ α] (c : ℚ)
    (M : Matrix m n α) : (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_rat_smul Matrix.conjTranspose_rat_smul

@[simp]
theorem conjTranspose_mul [Fintype n] [NonUnitalSemiring α] [StarRing α] (M : Matrix m n α)
    (N : Matrix n l α) : (M * N)ᴴ = Nᴴ * Mᴴ :=
  Matrix.ext <| by simp [mul_apply]
                   -- 🎉 no goals
#align matrix.conj_transpose_mul Matrix.conjTranspose_mul

@[simp]
theorem conjTranspose_neg [AddGroup α] [StarAddMonoid α] (M : Matrix m n α) : (-M)ᴴ = -Mᴴ :=
  Matrix.ext <| by simp
                   -- 🎉 no goals
#align matrix.conj_transpose_neg Matrix.conjTranspose_neg

theorem conjTranspose_map [Star α] [Star β] {A : Matrix m n α} (f : α → β)
    (hf : Function.Semiconj f star star) : Aᴴ.map f = (A.map f)ᴴ :=
  Matrix.ext fun _ _ => hf _
#align matrix.conj_transpose_map Matrix.conjTranspose_map

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
#align matrix.conj_transpose_add_equiv Matrix.conjTransposeAddEquiv

@[simp]
theorem conjTransposeAddEquiv_symm [AddMonoid α] [StarAddMonoid α] :
    (conjTransposeAddEquiv m n α).symm = conjTransposeAddEquiv n m α :=
  rfl
#align matrix.conj_transpose_add_equiv_symm Matrix.conjTransposeAddEquiv_symm

variable {m n α}

theorem conjTranspose_list_sum [AddMonoid α] [StarAddMonoid α] (l : List (Matrix m n α)) :
    l.sumᴴ = (l.map conjTranspose).sum :=
  (conjTransposeAddEquiv m n α).toAddMonoidHom.map_list_sum l
#align matrix.conj_transpose_list_sum Matrix.conjTranspose_list_sum

theorem conjTranspose_multiset_sum [AddCommMonoid α] [StarAddMonoid α]
    (s : Multiset (Matrix m n α)) : s.sumᴴ = (s.map conjTranspose).sum :=
  (conjTransposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s
#align matrix.conj_transpose_multiset_sum Matrix.conjTranspose_multiset_sum

theorem conjTranspose_sum [AddCommMonoid α] [StarAddMonoid α] {ι : Type*} (s : Finset ι)
    (M : ι → Matrix m n α) : (∑ i in s, M i)ᴴ = ∑ i in s, (M i)ᴴ :=
  (conjTransposeAddEquiv m n α).toAddMonoidHom.map_sum _ s
#align matrix.conj_transpose_sum Matrix.conjTranspose_sum

variable (m n R α)

/-- `Matrix.conjTranspose` as a `LinearMap` -/
@[simps apply]
def conjTransposeLinearEquiv [CommSemiring R] [StarRing R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] [StarModule R α] : Matrix m n α ≃ₗ⋆[R] Matrix n m α :=
  { conjTransposeAddEquiv m n α with map_smul' := conjTranspose_smul }
#align matrix.conj_transpose_linear_equiv Matrix.conjTransposeLinearEquiv

@[simp]
theorem conjTransposeLinearEquiv_symm [CommSemiring R] [StarRing R] [AddCommMonoid α]
    [StarAddMonoid α] [Module R α] [StarModule R α] :
    (conjTransposeLinearEquiv m n R α).symm = conjTransposeLinearEquiv n m R α :=
  rfl
#align matrix.conj_transpose_linear_equiv_symm Matrix.conjTransposeLinearEquiv_symm

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
#align matrix.conj_transpose_ring_equiv Matrix.conjTransposeRingEquiv

variable {m α}

@[simp]
theorem conjTranspose_pow [Semiring α] [StarRing α] [Fintype m] [DecidableEq m] (M : Matrix m m α)
    (k : ℕ) : (M ^ k)ᴴ = Mᴴ ^ k :=
  MulOpposite.op_injective <| map_pow (conjTransposeRingEquiv m α) M k
#align matrix.conj_transpose_pow Matrix.conjTranspose_pow

theorem conjTranspose_list_prod [Semiring α] [StarRing α] [Fintype m] [DecidableEq m]
    (l : List (Matrix m m α)) : l.prodᴴ = (l.map conjTranspose).reverse.prod :=
  (conjTransposeRingEquiv m α).unop_map_list_prod l
#align matrix.conj_transpose_list_prod Matrix.conjTranspose_list_prod

end ConjTranspose

section Star

/-- When `α` has a star operation, square matrices `Matrix n n α` have a star
operation equal to `Matrix.conjTranspose`. -/
instance [Star α] : Star (Matrix n n α) where star := conjTranspose

theorem star_eq_conjTranspose [Star α] (M : Matrix m m α) : star M = Mᴴ :=
  rfl
#align matrix.star_eq_conj_transpose Matrix.star_eq_conjTranspose

@[simp]
theorem star_apply [Star α] (M : Matrix n n α) (i j) : (star M) i j = star (M j i) :=
  rfl
#align matrix.star_apply Matrix.star_apply

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
#align matrix.star_mul Matrix.star_mul

end Star

/-- Given maps `(r_reindex : l → m)` and `(c_reindex : o → n)` reindexing the rows and columns of
a matrix `M : Matrix m n α`, the matrix `M.submatrix r_reindex c_reindex : Matrix l o α` is defined
by `(M.submatrix r_reindex c_reindex) i j = M (r_reindex i) (c_reindex j)` for `(i,j) : l × o`.
Note that the total number of row and columns does not have to be preserved. -/
def submatrix (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) : Matrix l o α :=
  of fun i j => A (r_reindex i) (c_reindex j)
#align matrix.submatrix Matrix.submatrix

@[simp]
theorem submatrix_apply (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) (i j) :
    A.submatrix r_reindex c_reindex i j = A (r_reindex i) (c_reindex j) :=
  rfl
#align matrix.submatrix_apply Matrix.submatrix_apply

@[simp]
theorem submatrix_id_id (A : Matrix m n α) : A.submatrix id id = A :=
  ext fun _ _ => rfl
#align matrix.submatrix_id_id Matrix.submatrix_id_id

@[simp]
theorem submatrix_submatrix {l₂ o₂ : Type*} (A : Matrix m n α) (r₁ : l → m) (c₁ : o → n)
    (r₂ : l₂ → l) (c₂ : o₂ → o) :
    (A.submatrix r₁ c₁).submatrix r₂ c₂ = A.submatrix (r₁ ∘ r₂) (c₁ ∘ c₂) :=
  ext fun _ _ => rfl
#align matrix.submatrix_submatrix Matrix.submatrix_submatrix

@[simp]
theorem transpose_submatrix (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) :
    (A.submatrix r_reindex c_reindex)ᵀ = Aᵀ.submatrix c_reindex r_reindex :=
  ext fun _ _ => rfl
#align matrix.transpose_submatrix Matrix.transpose_submatrix

@[simp]
theorem conjTranspose_submatrix [Star α] (A : Matrix m n α) (r_reindex : l → m)
    (c_reindex : o → n) : (A.submatrix r_reindex c_reindex)ᴴ = Aᴴ.submatrix c_reindex r_reindex :=
  ext fun _ _ => rfl
#align matrix.conj_transpose_submatrix Matrix.conjTranspose_submatrix

theorem submatrix_add [Add α] (A B : Matrix m n α) :
    ((A + B).submatrix : (l → m) → (o → n) → Matrix l o α) = A.submatrix + B.submatrix :=
  rfl
#align matrix.submatrix_add Matrix.submatrix_add

theorem submatrix_neg [Neg α] (A : Matrix m n α) :
    ((-A).submatrix : (l → m) → (o → n) → Matrix l o α) = -A.submatrix :=
  rfl
#align matrix.submatrix_neg Matrix.submatrix_neg

theorem submatrix_sub [Sub α] (A B : Matrix m n α) :
    ((A - B).submatrix : (l → m) → (o → n) → Matrix l o α) = A.submatrix - B.submatrix :=
  rfl
#align matrix.submatrix_sub Matrix.submatrix_sub

@[simp]
theorem submatrix_zero [Zero α] :
    ((0 : Matrix m n α).submatrix : (l → m) → (o → n) → Matrix l o α) = 0 :=
  rfl
#align matrix.submatrix_zero Matrix.submatrix_zero

theorem submatrix_smul {R : Type*} [SMul R α] (r : R) (A : Matrix m n α) :
    ((r • A : Matrix m n α).submatrix : (l → m) → (o → n) → Matrix l o α) = r • A.submatrix :=
  rfl
#align matrix.submatrix_smul Matrix.submatrix_smul

theorem submatrix_map (f : α → β) (e₁ : l → m) (e₂ : o → n) (A : Matrix m n α) :
    (A.map f).submatrix e₁ e₂ = (A.submatrix e₁ e₂).map f :=
  rfl
#align matrix.submatrix_map Matrix.submatrix_map

/-- Given a `(m × m)` diagonal matrix defined by a map `d : m → α`, if the reindexing map `e` is
  injective, then the resulting matrix is again diagonal. -/
theorem submatrix_diagonal [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l → m)
    (he : Function.Injective e) : (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  ext fun i j => by
    rw [submatrix_apply]
    -- ⊢ diagonal d (e i) (e j) = diagonal (d ∘ e) i j
    by_cases h : i = j
    -- ⊢ diagonal d (e i) (e j) = diagonal (d ∘ e) i j
    · rw [h, diagonal_apply_eq, diagonal_apply_eq]
      -- ⊢ d (e j) = (d ∘ e) j
      simp only [Function.comp_apply] -- Porting note: (simp) added this
      -- 🎉 no goals
    · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (he.ne h)]
      -- 🎉 no goals
#align matrix.submatrix_diagonal Matrix.submatrix_diagonal

theorem submatrix_one [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l → m)
    (he : Function.Injective e) : (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_diagonal _ e he
#align matrix.submatrix_one Matrix.submatrix_one

theorem submatrix_mul [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p q : Type*}
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : l → m) (e₂ : o → n) (e₃ : q → p)
    (he₂ : Function.Bijective e₂) :
    (M * N).submatrix e₁ e₃ = M.submatrix e₁ e₂ * N.submatrix e₂ e₃ :=
  ext fun _ _ => (he₂.sum_comp _).symm
#align matrix.submatrix_mul Matrix.submatrix_mul

theorem diag_submatrix (A : Matrix m m α) (e : l → m) : diag (A.submatrix e e) = A.diag ∘ e :=
  rfl
#align matrix.diag_submatrix Matrix.diag_submatrix

/-! `simp` lemmas for `Matrix.submatrix`s interaction with `Matrix.diagonal`, `1`, and `Matrix.mul`
for when the mappings are bundled. -/


@[simp]
theorem submatrix_diagonal_embedding [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α)
    (e : l ↪ m) : (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  submatrix_diagonal d e e.injective
#align matrix.submatrix_diagonal_embedding Matrix.submatrix_diagonal_embedding

@[simp]
theorem submatrix_diagonal_equiv [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l ≃ m) :
    (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  submatrix_diagonal d e e.injective
#align matrix.submatrix_diagonal_equiv Matrix.submatrix_diagonal_equiv

@[simp]
theorem submatrix_one_embedding [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ↪ m) :
    (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_one e e.injective
#align matrix.submatrix_one_embedding Matrix.submatrix_one_embedding

@[simp]
theorem submatrix_one_equiv [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ≃ m) :
    (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_one e e.injective
#align matrix.submatrix_one_equiv Matrix.submatrix_one_equiv

@[simp]
theorem submatrix_mul_equiv [Fintype n] [Fintype o] [AddCommMonoid α] [Mul α] {p q : Type*}
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : l → m) (e₂ : o ≃ n) (e₃ : q → p) :
    M.submatrix e₁ e₂ * N.submatrix e₂ e₃ = (M * N).submatrix e₁ e₃ :=
  (submatrix_mul M N e₁ e₂ e₃ e₂.bijective).symm
#align matrix.submatrix_mul_equiv Matrix.submatrix_mul_equiv

theorem submatrix_mulVec_equiv [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α]
    (M : Matrix m n α) (v : o → α) (e₁ : l → m) (e₂ : o ≃ n) :
    (M.submatrix e₁ e₂).mulVec v = M.mulVec (v ∘ e₂.symm) ∘ e₁ :=
  funext fun _ => Eq.symm (dotProduct_comp_equiv_symm _ _ _)
#align matrix.submatrix_mul_vec_equiv Matrix.submatrix_mulVec_equiv

theorem submatrix_vecMul_equiv [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (M : Matrix m n α) (v : l → α) (e₁ : l ≃ m) (e₂ : o → n) :
    vecMul v (M.submatrix e₁ e₂) = vecMul (v ∘ e₁.symm) M ∘ e₂ :=
  funext fun _ => Eq.symm (comp_equiv_symm_dotProduct _ _ _)
#align matrix.submatrix_vec_mul_equiv Matrix.submatrix_vecMul_equiv

theorem mul_submatrix_one [Fintype n] [Finite o] [NonAssocSemiring α] [DecidableEq o] (e₁ : n ≃ o)
    (e₂ : l → o) (M : Matrix m n α) :
    M * (1 : Matrix o o α).submatrix e₁ e₂ = submatrix M id (e₁.symm ∘ e₂) := by
  cases nonempty_fintype o
  -- ⊢ M * submatrix 1 (↑e₁) e₂ = submatrix M id (↑e₁.symm ∘ e₂)
  let A := M.submatrix id e₁.symm
  -- ⊢ M * submatrix 1 (↑e₁) e₂ = submatrix M id (↑e₁.symm ∘ e₂)
  have : M = A.submatrix id e₁ := by
    simp only [submatrix_submatrix, Function.comp.right_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this, submatrix_mul_equiv]
  -- ⊢ submatrix (A * 1) id e₂ = submatrix (submatrix A id ↑e₁) id (↑e₁.symm ∘ e₂)
  simp only [Matrix.mul_one, submatrix_submatrix, Function.comp.right_id, submatrix_id_id,
    Equiv.symm_comp_self]
#align matrix.mul_submatrix_one Matrix.mul_submatrix_one

theorem one_submatrix_mul [Fintype m] [Finite o] [NonAssocSemiring α] [DecidableEq o] (e₁ : l → o)
    (e₂ : m ≃ o) (M : Matrix m n α) :
    ((1 : Matrix o o α).submatrix e₁ e₂) * M = submatrix M (e₂.symm ∘ e₁) id := by
  cases nonempty_fintype o
  -- ⊢ submatrix 1 e₁ ↑e₂ * M = submatrix M (↑e₂.symm ∘ e₁) id
  let A := M.submatrix e₂.symm id
  -- ⊢ submatrix 1 e₁ ↑e₂ * M = submatrix M (↑e₂.symm ∘ e₁) id
  have : M = A.submatrix e₂ id := by
    simp only [submatrix_submatrix, Function.comp.right_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this, submatrix_mul_equiv]
  -- ⊢ submatrix (1 * A) e₁ id = submatrix (submatrix A (↑e₂) id) (↑e₂.symm ∘ e₁) id
  simp only [Matrix.one_mul, submatrix_submatrix, Function.comp.right_id, submatrix_id_id,
    Equiv.symm_comp_self]
#align matrix.one_submatrix_mul Matrix.one_submatrix_mul

/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
def reindex (eₘ : m ≃ l) (eₙ : n ≃ o) : Matrix m n α ≃ Matrix l o α where
  toFun M := M.submatrix eₘ.symm eₙ.symm
  invFun M := M.submatrix eₘ eₙ
  left_inv M := by simp
                   -- 🎉 no goals
  right_inv M := by simp
                    -- 🎉 no goals
#align matrix.reindex Matrix.reindex

@[simp]
theorem reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    reindex eₘ eₙ M = M.submatrix eₘ.symm eₙ.symm :=
  rfl
#align matrix.reindex_apply Matrix.reindex_apply

-- @[simp] -- Porting note: simp can prove this
theorem reindex_refl_refl (A : Matrix m n α) : reindex (Equiv.refl _) (Equiv.refl _) A = A :=
  A.submatrix_id_id
#align matrix.reindex_refl_refl Matrix.reindex_refl_refl

@[simp]
theorem reindex_symm (eₘ : m ≃ l) (eₙ : n ≃ o) :
    (reindex eₘ eₙ).symm = (reindex eₘ.symm eₙ.symm : Matrix l o α ≃ _) :=
  rfl
#align matrix.reindex_symm Matrix.reindex_symm

@[simp]
theorem reindex_trans {l₂ o₂ : Type*} (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂) :
    (reindex eₘ eₙ).trans (reindex eₘ₂ eₙ₂) =
      (reindex (eₘ.trans eₘ₂) (eₙ.trans eₙ₂) : Matrix m n α ≃ _) :=
  Equiv.ext fun A => (A.submatrix_submatrix eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm : _)
#align matrix.reindex_trans Matrix.reindex_trans

theorem transpose_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᵀ = reindex eₙ eₘ Mᵀ :=
  rfl
#align matrix.transpose_reindex Matrix.transpose_reindex

theorem conjTranspose_reindex [Star α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᴴ = reindex eₙ eₘ Mᴴ :=
  rfl
#align matrix.conj_transpose_reindex Matrix.conjTranspose_reindex

-- @[simp] -- Porting note: simp can prove this
theorem submatrix_mul_transpose_submatrix [Fintype m] [Fintype n] [AddCommMonoid α] [Mul α]
    (e : m ≃ n) (M : Matrix m n α) : M.submatrix id e * Mᵀ.submatrix e id = M * Mᵀ := by
  rw [submatrix_mul_equiv, submatrix_id_id]
  -- 🎉 no goals
#align matrix.submatrix_mul_transpose_submatrix Matrix.submatrix_mul_transpose_submatrix

/-- The left `n × l` part of an `n × (l+r)` matrix. -/
@[reducible]
def subLeft {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α) : Matrix (Fin m) (Fin l) α :=
  submatrix A id (Fin.castAdd r)
#align matrix.sub_left Matrix.subLeft

/-- The right `n × r` part of an `n × (l+r)` matrix. -/
@[reducible]
def subRight {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α) : Matrix (Fin m) (Fin r) α :=
  submatrix A id (Fin.natAdd l)
#align matrix.sub_right Matrix.subRight

/-- The top `u × n` part of a `(u+d) × n` matrix. -/
@[reducible]
def subUp {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α) : Matrix (Fin u) (Fin n) α :=
  submatrix A (Fin.castAdd d) id
#align matrix.sub_up Matrix.subUp

/-- The bottom `d × n` part of a `(u+d) × n` matrix. -/
@[reducible]
def subDown {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α) : Matrix (Fin d) (Fin n) α :=
  submatrix A (Fin.natAdd u) id
#align matrix.sub_down Matrix.subDown

/-- The top-right `u × r` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def subUpRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin u) (Fin r) α :=
  subUp (subRight A)
#align matrix.sub_up_right Matrix.subUpRight

/-- The bottom-right `d × r` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def subDownRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin d) (Fin r) α :=
  subDown (subRight A)
#align matrix.sub_down_right Matrix.subDownRight

/-- The top-left `u × l` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def subUpLeft {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin u) (Fin l) α :=
  subUp (subLeft A)
#align matrix.sub_up_left Matrix.subUpLeft

/-- The bottom-left `d × l` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def subDownLeft {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin d) (Fin l) α :=
  subDown (subLeft A)
#align matrix.sub_down_left Matrix.subDownLeft

section RowCol

/-!
### `row_col` section

Simplification lemmas for `Matrix.row` and `Matrix.col`.
-/


open Matrix

theorem col_injective : Function.Injective (col : (m → α) → _) :=
  fun _x _y h => funext fun i => congr_fun₂ h i ()

@[simp] theorem col_inj {v w : m → α} : col v = col w ↔ v = w := col_injective.eq_iff

@[simp] theorem col_zero [Zero α] : col (0 : m → α) = 0 := rfl

@[simp] theorem col_eq_zero [Zero α] (v : m → α) : col v = 0 ↔ v = 0 := col_inj

@[simp]
theorem col_add [Add α] (v w : m → α) : col (v + w) = col v + col w := by
  ext
  -- ⊢ col (v + w) i✝ x✝ = (col v + col w) i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.col_add Matrix.col_add

@[simp]
theorem col_smul [SMul R α] (x : R) (v : m → α) : col (x • v) = x • col v := by
  ext
  -- ⊢ col (x • v) i✝ x✝ = (x • col v) i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.col_smul Matrix.col_smul

theorem row_injective : Function.Injective (row : (n → α) → _) :=
  fun _x _y h => funext fun j => congr_fun₂ h () j

@[simp] theorem row_inj {v w : n → α} : row v = row w ↔ v = w := row_injective.eq_iff

@[simp] theorem row_zero [Zero α] : row (0 : n → α) = 0 := rfl

@[simp] theorem row_eq_zero [Zero α] (v : n → α) : row v = 0 ↔ v = 0 := row_inj

@[simp]
theorem row_add [Add α] (v w : m → α) : row (v + w) = row v + row w := by
  ext
  -- ⊢ row (v + w) i✝ x✝ = (row v + row w) i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.row_add Matrix.row_add

@[simp]
theorem row_smul [SMul R α] (x : R) (v : m → α) : row (x • v) = x • row v := by
  ext
  -- ⊢ row (x • v) i✝ x✝ = (x • row v) i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.row_smul Matrix.row_smul

@[simp]
theorem transpose_col (v : m → α) : (Matrix.col v)ᵀ = Matrix.row v := by
  ext
  -- ⊢ (col v)ᵀ i✝ x✝ = row v i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.transpose_col Matrix.transpose_col

@[simp]
theorem transpose_row (v : m → α) : (Matrix.row v)ᵀ = Matrix.col v := by
  ext
  -- ⊢ (row v)ᵀ i✝ x✝ = col v i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.transpose_row Matrix.transpose_row

@[simp]
theorem conjTranspose_col [Star α] (v : m → α) : (col v)ᴴ = row (star v) := by
  ext
  -- ⊢ (col v)ᴴ i✝ x✝ = row (star v) i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.conj_transpose_col Matrix.conjTranspose_col

@[simp]
theorem conjTranspose_row [Star α] (v : m → α) : (row v)ᴴ = col (star v) := by
  ext
  -- ⊢ (row v)ᴴ i✝ x✝ = col (star v) i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.conj_transpose_row Matrix.conjTranspose_row

theorem row_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : m → α) :
    Matrix.row (Matrix.vecMul v M) = Matrix.row v * M := by
  ext
  -- ⊢ row (vecMul v M) i✝ x✝ = (row v * M) i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.row_vec_mul Matrix.row_vecMul

theorem col_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : m → α) :
    Matrix.col (Matrix.vecMul v M) = (Matrix.row v * M)ᵀ := by
  ext
  -- ⊢ col (vecMul v M) i✝ x✝ = (row v * M)ᵀ i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.col_vec_mul Matrix.col_vecMul

theorem col_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : n → α) :
    Matrix.col (Matrix.mulVec M v) = M * Matrix.col v := by
  ext
  -- ⊢ col (mulVec M v) i✝ x✝ = (M * col v) i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.col_mul_vec Matrix.col_mulVec

theorem row_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : n → α) :
    Matrix.row (Matrix.mulVec M v) = (M * Matrix.col v)ᵀ := by
  ext
  -- ⊢ row (mulVec M v) i✝ x✝ = (M * col v)ᵀ i✝ x✝
  rfl
  -- 🎉 no goals
#align matrix.row_mul_vec Matrix.row_mulVec

@[simp]
theorem row_mul_col_apply [Fintype m] [Mul α] [AddCommMonoid α] (v w : m → α) (i j) :
    (row v * col w) i j = v ⬝ᵥ w :=
  rfl
#align matrix.row_mul_col_apply Matrix.row_mul_col_apply

end RowCol

section Update

/-- Update, i.e. replace the `i`th row of matrix `A` with the values in `b`. -/
def updateRow [DecidableEq m] (M : Matrix m n α) (i : m) (b : n → α) : Matrix m n α :=
  of <| Function.update M i b
#align matrix.update_row Matrix.updateRow

/-- Update, i.e. replace the `j`th column of matrix `A` with the values in `b`. -/
def updateColumn [DecidableEq n] (M : Matrix m n α) (j : n) (b : m → α) : Matrix m n α :=
  of fun i => Function.update (M i) j (b i)
#align matrix.update_column Matrix.updateColumn

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

@[simp]
theorem updateRow_self [DecidableEq m] : updateRow M i b i = b :=
  -- Porting note: (implicit arg) added `(β := _)`
  Function.update_same (β := fun _ => (n → α)) i b M
#align matrix.update_row_self Matrix.updateRow_self

@[simp]
theorem updateColumn_self [DecidableEq n] : updateColumn M j c i j = c i :=
  -- Porting note: (implicit arg) added `(β := _)`
  Function.update_same (β := fun _ => α) j (c i) (M i)
#align matrix.update_column_self Matrix.updateColumn_self

@[simp]
theorem updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' ≠ i) : updateRow M i b i' = M i' :=
  -- Porting note: (implicit arg) added `(β := _)`
  Function.update_noteq (β := fun _ => (n → α)) i_ne b M
#align matrix.update_row_ne Matrix.updateRow_ne

@[simp]
theorem updateColumn_ne [DecidableEq n] {j' : n} (j_ne : j' ≠ j) :
    updateColumn M j c i j' = M i j' :=
  -- Porting note: (implicit arg) added `(β := _)`
  Function.update_noteq (β := fun _ => α) j_ne (c i) (M i)
#align matrix.update_column_ne Matrix.updateColumn_ne

theorem updateRow_apply [DecidableEq m] {i' : m} :
    updateRow M i b i' j = if i' = i then b j else M i' j := by
  by_cases i' = i
  -- ⊢ updateRow M i b i' j = if i' = i then b j else M i' j
  -- ⊢ updateRow M i b i' j = if i' = i then b j else M i' j
  · rw [h, updateRow_self, if_pos rfl]
    -- 🎉 no goals
  · rw [updateRow_ne h, if_neg h]
    -- 🎉 no goals
#align matrix.update_row_apply Matrix.updateRow_apply

theorem updateColumn_apply [DecidableEq n] {j' : n} :
    updateColumn M j c i j' = if j' = j then c i else M i j' := by
  by_cases j' = j
  -- ⊢ updateColumn M j c i j' = if j' = j then c i else M i j'
  -- ⊢ updateColumn M j c i j' = if j' = j then c i else M i j'
  · rw [h, updateColumn_self, if_pos rfl]
    -- 🎉 no goals
  · rw [updateColumn_ne h, if_neg h]
    -- 🎉 no goals
#align matrix.update_column_apply Matrix.updateColumn_apply

@[simp]
theorem updateColumn_subsingleton [Subsingleton n] (A : Matrix m n R) (i : n) (b : m → R) :
    A.updateColumn i b = (col b).submatrix id (Function.const n ()) := by
  ext x y
  -- ⊢ updateColumn A i b x y = submatrix (col b) id (Function.const n ()) x y
  simp [updateColumn_apply, Subsingleton.elim i y]
  -- 🎉 no goals
#align matrix.update_column_subsingleton Matrix.updateColumn_subsingleton

@[simp]
theorem updateRow_subsingleton [Subsingleton m] (A : Matrix m n R) (i : m) (b : n → R) :
    A.updateRow i b = (row b).submatrix (Function.const m ()) id := by
  ext x y
  -- ⊢ updateRow A i b x y = submatrix (row b) (Function.const m ()) id x y
  simp [updateColumn_apply, Subsingleton.elim i x]
  -- 🎉 no goals
#align matrix.update_row_subsingleton Matrix.updateRow_subsingleton

theorem map_updateRow [DecidableEq m] (f : α → β) :
    map (updateRow M i b) f = updateRow (M.map f) i (f ∘ b) := by
  ext
  -- ⊢ map (updateRow M i b) f i✝ x✝ = updateRow (map M f) i (f ∘ b) i✝ x✝
  rw [updateRow_apply, map_apply, map_apply, updateRow_apply]
  -- ⊢ f (if i✝ = i then b x✝ else M i✝ x✝) = if i✝ = i then (f ∘ b) x✝ else f (M i …
  exact apply_ite f _ _ _
  -- 🎉 no goals
#align matrix.map_update_row Matrix.map_updateRow

theorem map_updateColumn [DecidableEq n] (f : α → β) :
    map (updateColumn M j c) f = updateColumn (M.map f) j (f ∘ c) := by
  ext
  -- ⊢ map (updateColumn M j c) f i✝ x✝ = updateColumn (map M f) j (f ∘ c) i✝ x✝
  rw [updateColumn_apply, map_apply, map_apply, updateColumn_apply]
  -- ⊢ f (if x✝ = j then c i✝ else M i✝ x✝) = if x✝ = j then (f ∘ c) i✝ else f (M i …
  exact apply_ite f _ _ _
  -- 🎉 no goals
#align matrix.map_update_column Matrix.map_updateColumn

theorem updateRow_transpose [DecidableEq n] : updateRow Mᵀ j c = (updateColumn M j c)ᵀ := by
  ext
  -- ⊢ updateRow Mᵀ j c i✝ x✝ = (updateColumn M j c)ᵀ i✝ x✝
  rw [transpose_apply, updateRow_apply, updateColumn_apply]
  -- ⊢ (if i✝ = j then c x✝ else Mᵀ i✝ x✝) = if i✝ = j then c x✝ else M x✝ i✝
  rfl
  -- 🎉 no goals
#align matrix.update_row_transpose Matrix.updateRow_transpose

theorem updateColumn_transpose [DecidableEq m] : updateColumn Mᵀ i b = (updateRow M i b)ᵀ := by
  ext
  -- ⊢ updateColumn Mᵀ i b i✝ x✝ = (updateRow M i b)ᵀ i✝ x✝
  rw [transpose_apply, updateRow_apply, updateColumn_apply]
  -- ⊢ (if x✝ = i then b i✝ else Mᵀ i✝ x✝) = if x✝ = i then b i✝ else M x✝ i✝
  rfl
  -- 🎉 no goals
#align matrix.update_column_transpose Matrix.updateColumn_transpose

theorem updateRow_conjTranspose [DecidableEq n] [Star α] :
    updateRow Mᴴ j (star c) = (updateColumn M j c)ᴴ := by
  rw [conjTranspose, conjTranspose, transpose_map, transpose_map, updateRow_transpose,
    map_updateColumn]
  rfl
  -- 🎉 no goals
#align matrix.update_row_conj_transpose Matrix.updateRow_conjTranspose

theorem updateColumn_conjTranspose [DecidableEq m] [Star α] :
    updateColumn Mᴴ i (star b) = (updateRow M i b)ᴴ := by
  rw [conjTranspose, conjTranspose, transpose_map, transpose_map, updateColumn_transpose,
    map_updateRow]
  rfl
  -- 🎉 no goals
#align matrix.update_column_conj_transpose Matrix.updateColumn_conjTranspose

@[simp]
theorem updateRow_eq_self [DecidableEq m] (A : Matrix m n α) (i : m) : A.updateRow i (A i) = A :=
  Function.update_eq_self i A
#align matrix.update_row_eq_self Matrix.updateRow_eq_self

@[simp]
theorem updateColumn_eq_self [DecidableEq n] (A : Matrix m n α) (i : n) :
    (A.updateColumn i fun j => A j i) = A :=
  funext fun j => Function.update_eq_self i (A j)
#align matrix.update_column_eq_self Matrix.updateColumn_eq_self

theorem diagonal_updateColumn_single [DecidableEq n] [Zero α] (v : n → α) (i : n) (x : α) :
    (diagonal v).updateColumn i (Pi.single i x) = diagonal (Function.update v i x) := by
  ext j k
  -- ⊢ updateColumn (diagonal v) i (Pi.single i x) j k = diagonal (Function.update  …
  obtain rfl | hjk := eq_or_ne j k
  -- ⊢ updateColumn (diagonal v) i (Pi.single i x) j j = diagonal (Function.update  …
  · rw [diagonal_apply_eq]
    -- ⊢ updateColumn (diagonal v) i (Pi.single i x) j j = Function.update v i x j
    obtain rfl | hji := eq_or_ne j i
    -- ⊢ updateColumn (diagonal v) j (Pi.single j x) j j = Function.update v j x j
    · rw [updateColumn_self, Pi.single_eq_same, Function.update_same]
      -- 🎉 no goals
    · rw [updateColumn_ne hji, diagonal_apply_eq, Function.update_noteq hji]
      -- 🎉 no goals
  · rw [diagonal_apply_ne _ hjk]
    -- ⊢ updateColumn (diagonal v) i (Pi.single i x) j k = 0
    obtain rfl | hki := eq_or_ne k i
    -- ⊢ updateColumn (diagonal v) k (Pi.single k x) j k = 0
    · rw [updateColumn_self, Pi.single_eq_of_ne hjk]
      -- 🎉 no goals
    · rw [updateColumn_ne hki, diagonal_apply_ne _ hjk]
      -- 🎉 no goals
#align matrix.diagonal_update_column_single Matrix.diagonal_updateColumn_single

theorem diagonal_updateRow_single [DecidableEq n] [Zero α] (v : n → α) (i : n) (x : α) :
    (diagonal v).updateRow i (Pi.single i x) = diagonal (Function.update v i x) := by
  rw [← diagonal_transpose, updateRow_transpose, diagonal_updateColumn_single, diagonal_transpose]
  -- 🎉 no goals
#align matrix.diagonal_update_row_single Matrix.diagonal_updateRow_single

/-! Updating rows and columns commutes in the obvious way with reindexing the matrix. -/


theorem updateRow_submatrix_equiv [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l)
    (r : o → α) (e : l ≃ m) (f : o ≃ n) :
    updateRow (A.submatrix e f) i r = (A.updateRow (e i) fun j => r (f.symm j)).submatrix e f := by
  ext i' j
  -- ⊢ updateRow (submatrix A ↑e ↑f) i r i' j = submatrix (updateRow A (↑e i) fun j …
  simp only [submatrix_apply, updateRow_apply, Equiv.apply_eq_iff_eq, Equiv.symm_apply_apply]
  -- 🎉 no goals
#align matrix.update_row_submatrix_equiv Matrix.updateRow_submatrix_equiv

theorem submatrix_updateRow_equiv [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : m)
    (r : n → α) (e : l ≃ m) (f : o ≃ n) :
    (A.updateRow i r).submatrix e f = updateRow (A.submatrix e f) (e.symm i) fun i => r (f i) :=
  Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateRow_submatrix_equiv A _ _ e f).symm
               -- 🎉 no goals
#align matrix.submatrix_update_row_equiv Matrix.submatrix_updateRow_equiv

theorem updateColumn_submatrix_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : o)
    (c : l → α) (e : l ≃ m) (f : o ≃ n) : updateColumn (A.submatrix e f) j c =
    (A.updateColumn (f j) fun i => c (e.symm i)).submatrix e f := by
  simpa only [← transpose_submatrix, updateRow_transpose] using
    congr_arg transpose (updateRow_submatrix_equiv Aᵀ j c f e)
#align matrix.update_column_submatrix_equiv Matrix.updateColumn_submatrix_equiv

theorem submatrix_updateColumn_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n)
    (c : m → α) (e : l ≃ m) (f : o ≃ n) : (A.updateColumn j c).submatrix e f =
    updateColumn (A.submatrix e f) (f.symm j) fun i => c (e i) :=
  Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateColumn_submatrix_equiv A _ _ e f).symm
               -- 🎉 no goals
#align matrix.submatrix_update_column_equiv Matrix.submatrix_updateColumn_equiv

/-! `reindex` versions of the above `submatrix` lemmas for convenience. -/


theorem updateRow_reindex [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l) (r : o → α)
    (e : m ≃ l) (f : n ≃ o) :
    updateRow (reindex e f A) i r = reindex e f (A.updateRow (e.symm i) fun j => r (f j)) :=
  updateRow_submatrix_equiv _ _ _ _ _
#align matrix.update_row_reindex Matrix.updateRow_reindex

theorem reindex_updateRow [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : m) (r : n → α)
    (e : m ≃ l) (f : n ≃ o) :
    reindex e f (A.updateRow i r) = updateRow (reindex e f A) (e i) fun i => r (f.symm i) :=
  submatrix_updateRow_equiv _ _ _ _ _
#align matrix.reindex_update_row Matrix.reindex_updateRow

theorem updateColumn_reindex [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : o) (c : l → α)
    (e : m ≃ l) (f : n ≃ o) :
    updateColumn (reindex e f A) j c = reindex e f (A.updateColumn (f.symm j) fun i => c (e i)) :=
  updateColumn_submatrix_equiv _ _ _ _ _
#align matrix.update_column_reindex Matrix.updateColumn_reindex

theorem reindex_updateColumn [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n) (c : m → α)
    (e : m ≃ l) (f : n ≃ o) :
    reindex e f (A.updateColumn j c) = updateColumn (reindex e f A) (f j) fun i => c (e.symm i) :=
  submatrix_updateColumn_equiv _ _ _ _ _
#align matrix.reindex_update_column Matrix.reindex_updateColumn

end Update

end Matrix

namespace RingHom

variable [Fintype n] [NonAssocSemiring α] [NonAssocSemiring β]

theorem map_matrix_mul (M : Matrix m n α) (N : Matrix n o α) (i : m) (j : o) (f : α →+* β) :
    f ((M * N) i j) = (M.map f * N.map f) i j := by
  simp [Matrix.mul_apply, map_sum]
  -- 🎉 no goals
#align ring_hom.map_matrix_mul RingHom.map_matrix_mul

theorem map_dotProduct [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (v w : n → R) :
    f (v ⬝ᵥ w) = f ∘ v ⬝ᵥ f ∘ w := by
  simp only [Matrix.dotProduct, f.map_sum, f.map_mul, Function.comp]
  -- 🎉 no goals
#align ring_hom.map_dot_product RingHom.map_dotProduct

theorem map_vecMul [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (M : Matrix n m R)
    (v : n → R) (i : m) : f (M.vecMul v i) = (M.map f).vecMul (f ∘ v) i := by
  simp only [Matrix.vecMul, Matrix.map_apply, RingHom.map_dotProduct, Function.comp]
  -- 🎉 no goals
#align ring_hom.map_vec_mul RingHom.map_vecMul

theorem map_mulVec [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (M : Matrix m n R)
    (v : n → R) (i : m) : f (M.mulVec v i) = (M.map f).mulVec (f ∘ v) i := by
  simp only [Matrix.mulVec, Matrix.map_apply, RingHom.map_dotProduct, Function.comp]
  -- 🎉 no goals
#align ring_hom.map_mul_vec RingHom.map_mulVec

end RingHom
