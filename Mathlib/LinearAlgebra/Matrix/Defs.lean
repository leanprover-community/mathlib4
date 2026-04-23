/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Data.Set.Operations
import Mathlib.Algebra.Module.Pi
import Mathlib.Init
import Mathlib.Logic.Nontrivial.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Matrices

This file defines basic properties of matrices up to the module structure.

Matrices with rows indexed by `m`, columns indexed by `n`, and entries of type `α` are represented
with `Matrix m n α`. For the typical approach of counting rows and columns,
`Matrix (Fin m) (Fin n) α` can be used.

## Main definitions

* `Matrix.transpose`: transpose of a matrix, turning rows into columns and vice versa
* `Matrix.submatrix`: take a submatrix by reindexing rows and columns
* `Matrix.module`: matrices are a module over the ring of entries
* `Set.matrix`: set of matrices with entries in a given set

## Notation

The scope `Matrix` gives the following notation:

* `ᵀ` for `Matrix.transpose`

See `Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean` for

* `ᴴ` for `Matrix.conjTranspose`

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `fun i j ↦ _` or even `(fun i j ↦ _ : Matrix m n α)`, as these are not recognized by Lean
as having the right type. Instead, `Matrix.of` should be used.
-/

@[expose] public section

assert_not_exists Algebra TrivialStar

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

theorem map_involutive {f : α → α} (hf : Function.Involutive f) :
    Function.Involutive fun M : Matrix m n α ↦ M.map f := by intro; simp [hf]

/-- The transpose of a matrix. -/
def transpose (M : Matrix m n α) : Matrix n m α :=
  of fun x y => M y x

-- TODO: set as an equation lemma for `transpose`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
theorem transpose_apply (M : Matrix m n α) (i j) : transpose M i j = M j i :=
  rfl

@[inherit_doc]
scoped postfix:1024 "ᵀ" => Matrix.transpose

instance inhabited [Inhabited α] : Inhabited (Matrix m n α) :=
  inferInstanceAs <| Inhabited (m → n → α)

instance add [Add α] : Add (Matrix m n α) :=
  inferInstanceAs <| Add (m → n → α)

instance addSemigroup [AddSemigroup α] : AddSemigroup (Matrix m n α) :=
  inferInstanceAs <| AddSemigroup (m → n → α)

instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (Matrix m n α) :=
  inferInstanceAs <| AddCommSemigroup (m → n → α)

instance zero [Zero α] : Zero (Matrix m n α) :=
  inferInstanceAs <| Zero (m → n → α)

instance addZeroClass [AddZeroClass α] : AddZeroClass (Matrix m n α) :=
  inferInstanceAs <| AddZeroClass (m → n → α)

instance addMonoid [AddMonoid α] : AddMonoid (Matrix m n α) where
  __ : AddMonoid (Matrix m n α) := inferInstanceAs <| AddMonoid (m → n → α)
  nsmul a b := fun i ↦ a • b i

instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (Matrix m n α) :=
  inferInstanceAs <| AddCommMonoid (m → n → α)

instance neg [Neg α] : Neg (Matrix m n α) :=
  inferInstanceAs <| Neg (m → n → α)

instance involutiveNeg [InvolutiveNeg α] : InvolutiveNeg (Matrix m n α) :=
  inferInstanceAs <| InvolutiveNeg (m → n → α)

instance sub [Sub α] : Sub (Matrix m n α) :=
  inferInstanceAs <| Sub (m → n → α)

instance addGroup [AddGroup α] : AddGroup (Matrix m n α) where
  __ : AddGroup (Matrix m n α) := inferInstanceAs <| AddGroup (m → n → α)
  zsmul a b := fun i ↦ a • b i

instance addCommGroup [AddCommGroup α] : AddCommGroup (Matrix m n α) :=
  inferInstanceAs <| AddCommGroup (m → n → α)

instance unique [Unique α] : Unique (Matrix m n α) :=
  inferInstanceAs <| Unique (m → n → α)

instance subsingleton [Subsingleton α] : Subsingleton (Matrix m n α) :=
  inferInstanceAs <| Subsingleton <| m → n → α

instance nonempty [Nonempty m] [Nonempty n] [Nontrivial α] : Nontrivial (Matrix m n α) :=
  Function.nontrivial

instance smul [SMul R α] : SMul R (Matrix m n α) where
  smul a b := fun i ↦ a • b i

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
  inferInstanceAs <| MulAction R (m → n → α)

instance distribMulAction [Monoid R] [AddMonoid α] [DistribMulAction R α] :
    DistribMulAction R (Matrix m n α) :=
  inferInstanceAs <| DistribMulAction R (m → n → α)

instance module [Semiring R] [AddCommMonoid α] [Module R α] : Module R (Matrix m n α) :=
  inferInstanceAs <| Module R (m → n → α)

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

protected theorem dite_apply (P : Prop) [Decidable P]
    (A : P → Matrix m n α) (B : ¬P → Matrix m n α) (i : m) (j : n) :
    dite P A B i j = dite P (A · i j) (B · i j) := by
  by_cases h : P <;> simp [h]

protected theorem ite_apply (P : Prop) [Decidable P]
    (A : Matrix m n α) (B : Matrix m n α) (i : m) (j : n) :
    (if P then A else B) i j = if P then A i j else B i j :=
  Matrix.dite_apply _ _ _ _ _

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

protected theorem map_neg [Neg α] [Neg β] (f : α → β) (hf : ∀ a, f (-a) = -f a)
    (M : Matrix m n α) : (-M).map f = -(M.map f) :=
  ext fun _ _ => hf _

protected theorem map_sub [Sub α] [Sub β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ - a₂) = f a₁ - f a₂)
    (M N : Matrix m n α) : (M - N).map f = M.map f - N.map f :=
  ext fun _ _ => hf _ _

protected theorem map_smul [SMul R α] [SMul R β] (f : α → β) (r : R) (hf : ∀ a, f (r • a) = r • f a)
    (M : Matrix m n α) : (r • M).map f = r • M.map f :=
  ext fun _ _ => hf _

protected theorem map_smulₛₗ [SMul R α] [SMul S β] (f : α → β) (σ : R → S) (r : R)
    (hf : ∀ a, f (r • a) = σ r • f a)
    (M : Matrix m n α) : (r • M).map f = σ r • M.map f :=
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

/-- This is `Matrix.of` bundled as an additive equivalence. -/
def ofAddEquiv [Add α] : (m → n → α) ≃+ Matrix m n α where
  __ := of
  map_add' _ _ := rfl

@[simp] lemma coe_ofAddEquiv [Add α] :
    ⇑(ofAddEquiv : (m → n → α) ≃+ Matrix m n α) = of := rfl
@[simp] lemma coe_ofAddEquiv_symm [Add α] :
    ⇑(ofAddEquiv.symm : Matrix m n α ≃+ (m → n → α)) = of.symm := rfl

@[simp] lemma isAddUnit_iff [AddMonoid α] {A : Matrix m n α} :
    IsAddUnit A ↔ ∀ i j, IsAddUnit (A i j) := by
  simp_rw [isAddUnit_iff_exists, Classical.skolem, forall_and,
    ← Matrix.ext_iff, add_apply, zero_apply]
  rfl

end Matrix

open Matrix

namespace Matrix

section Transpose

@[simp]
theorem transpose_transpose (M : Matrix m n α) : Mᵀᵀ = M := by
  ext
  rfl

variable (n α) in
theorem transpose_involutive : (transpose : Matrix n n α → Matrix n n α).Involutive :=
  transpose_transpose

theorem transpose_injective : Function.Injective (transpose : Matrix m n α → Matrix n m α) :=
  fun _ _ h => ext fun i j => ext_iff.2 h j i

@[simp] theorem transpose_inj {A B : Matrix m n α} : Aᵀ = Bᵀ ↔ A = B := transpose_injective.eq_iff

@[simp]
theorem transpose_zero [Zero α] : (0 : Matrix m n α)ᵀ = 0 := rfl

@[simp]
theorem transpose_eq_zero [Zero α] {M : Matrix m n α} : Mᵀ = 0 ↔ M = 0 := transpose_inj

@[simp]
theorem transpose_add [Add α] (M : Matrix m n α) (N : Matrix m n α) : (M + N)ᵀ = Mᵀ + Nᵀ := by
  ext
  simp

@[simp]
theorem transpose_sub [Sub α] (M : Matrix m n α) (N : Matrix m n α) : (M - N)ᵀ = Mᵀ - Nᵀ := by
  ext
  simp

@[simp]
theorem transpose_smul {R : Type*} [SMul R α] (c : R) (M : Matrix m n α) : (c • M)ᵀ = c • Mᵀ :=
  rfl

@[simp]
theorem transpose_neg [Neg α] (M : Matrix m n α) : (-M)ᵀ = -Mᵀ :=
  rfl

theorem transpose_map {f : α → β} {M : Matrix m n α} : Mᵀ.map f = (M.map f)ᵀ :=
  rfl

end Transpose

/-- Given maps `(r : l → m)` and `(c : o → n)` reindexing the rows and columns of
a matrix `M : Matrix m n α`, the matrix `M.submatrix r c : Matrix l o α` is defined
by `(M.submatrix r c) i j = M (r i) (c j)` for `(i,j) : l × o`.
Note that the total number of row and columns does not have to be preserved. -/
def submatrix (A : Matrix m n α) (r : l → m) (c : o → n) : Matrix l o α :=
  of fun i j => A (r i) (c j)

@[simp]
theorem submatrix_apply (A : Matrix m n α) (r : l → m) (c : o → n) (i j) :
    A.submatrix r c i j = A (r i) (c j) :=
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
theorem transpose_submatrix (A : Matrix m n α) (r : l → m) (c : o → n) :
    (A.submatrix r c)ᵀ = Aᵀ.submatrix c r :=
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
  Equiv.ext fun A => (A.submatrix_submatrix eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm :)

theorem transpose_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᵀ = reindex eₙ eₘ Mᵀ :=
  rfl

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

section RowCol

/-- For an `m × n` `α`-matrix `A`, `A.row i` is the `i`th row of `A` as a vector in `n → α`.
`A.row` is defeq to `A`, but explicitly refers to the 'row function' of `A`
while avoiding defeq abuse and noisy eta-expansions,
such as in expressions like `Set.Injective A.row` and `Set.range A.row`.
(Note 2025-04-07 : the identifier `Matrix.row` used to refer to a matrix with all rows equal;
this is now called `Matrix.replicateRow`) -/
def row (A : Matrix m n α) : m → n → α := A

/-- For an `m × n` `α`-matrix `A`, `A.col j` is the `j`th column of `A` as a vector in `m → α`.
`A.col` is defeq to `Aᵀ`, but refers to the 'column function' of `A`
while avoiding defeq abuse and noisy eta-expansions
(and without the simplifier unfolding transposes) in expressions like `Set.Injective A.col`
and `Set.range A.col`.
(Note 2025-04-07 : the identifier `Matrix.col` used to refer to a matrix with all columns equal;
this is now called `Matrix.replicateCol`) -/
def col (A : Matrix m n α) : n → m → α := Aᵀ

lemma row_eq_self (A : Matrix m n α) : A.row = of.symm A := rfl

lemma col_eq_transpose (A : Matrix m n α) : A.col = of.symm Aᵀ := rfl

@[simp]
lemma of_row (f : m → n → α) : (Matrix.of f).row = f := rfl

@[simp]
lemma of_col (f : m → n → α) : (Matrix.of f)ᵀ.col = f := rfl

lemma row_def (A : Matrix m n α) : A.row = fun i ↦ A i := rfl

lemma col_def (A : Matrix m n α) : A.col = fun j ↦ Aᵀ j := rfl

@[simp]
lemma row_apply (A : Matrix m n α) (i : m) (j : n) : A.row i j = A i j := rfl

/-- A partially applied version of `Matrix.row_apply` -/
lemma row_apply' (A : Matrix m n α) (i : m) : A.row i = A i := rfl

@[simp]
lemma col_apply (A : Matrix m n α) (i : n) (j : m) : A.col i j = A j i := rfl

/-- A partially applied version of `Matrix.col_apply` -/
lemma col_apply' (A : Matrix m n α) (i : n) : A.col i = fun j ↦ A j i := rfl

section

/-- Two matrices agree if their rows agree. -/
@[local ext]
lemma ext_row {A B : Matrix m n α} (h : ∀ i, A.row i = B.row i) : A = B :=
  ext fun i j => congr_fun (h i) j

/-- Two matrices agree if their columns agree. -/
@[local ext]
lemma ext_col {A B : Matrix m n α} (h : ∀ j, A.col j = B.col j) : A = B :=
  ext fun i j => congr_fun (h j) i

end

lemma row_submatrix {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ → m) (c : n₀ → n) (i : m₀) :
    (A.submatrix r c).row i = (A.submatrix id c).row (r i) := rfl

lemma row_submatrix_eq_comp {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ → m) (c : n₀ → n) (i : m₀) :
    (A.submatrix r c).row i = A.row (r i) ∘ c := rfl

lemma col_submatrix {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ → m) (c : n₀ → n) (j : n₀) :
    (A.submatrix r c).col j = (A.submatrix r id).col (c j) := rfl

lemma col_submatrix_eq_comp {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ → m) (c : n₀ → n) (j : n₀) :
    (A.submatrix r c).col j = A.col (c j) ∘ r := rfl

lemma row_map (A : Matrix m n α) (f : α → β) (i : m) : (A.map f).row i = f ∘ A.row i := rfl

lemma col_map (A : Matrix m n α) (f : α → β) (j : n) : (A.map f).col j = f ∘ A.col j := rfl

@[simp]
lemma row_transpose (A : Matrix m n α) : Aᵀ.row = A.col := rfl

@[simp]
lemma col_transpose (A : Matrix m n α) : Aᵀ.col = A.row := rfl

end RowCol

end Matrix

namespace Set

/-- Given a set `S`, `S.matrix` is the set of matrices `M`
all of whose entries `M i j` belong to `S`. -/
def matrix (S : Set α) : Set (Matrix m n α) := {M | ∀ i j, M i j ∈ S}

theorem mem_matrix {S : Set α} {M : Matrix m n α} :
    M ∈ S.matrix ↔ ∀ i j, M i j ∈ S := .rfl

theorem matrix_eq_pi {S : Set α} :
    S.matrix = of.symm ⁻¹' Set.univ.pi fun (_ : m) ↦ Set.univ.pi fun (_ : n) ↦ S := by
  ext
  simp [Set.mem_matrix]

end Set

namespace Matrix

variable {S : Set α}

@[simp]
theorem transpose_mem_matrix_iff {M : Matrix m n α} :
    Mᵀ ∈ S.matrix ↔ M ∈ S.matrix := forall_comm

theorem submatrix_mem_matrix {M : Matrix m n α} {r : l → m} {c : o → n} (hM : M ∈ S.matrix) :
    M.submatrix r c ∈ S.matrix := by simp_all [Set.mem_matrix]

theorem submatrix_mem_matrix_iff {M : Matrix m n α} {r : l → m} {c : o → n}
    (hr : Function.Surjective r) (hc : Function.Surjective c) :
    M.submatrix r c ∈ S.matrix ↔ M ∈ S.matrix :=
  ⟨(hr.forall.mpr fun _ => hc.forall.mpr fun _ => · _ _), submatrix_mem_matrix⟩

end Matrix
