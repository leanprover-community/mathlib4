/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
import Mathlib.Algebra.Module.Pi

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

## Notation

The locale `Matrix` gives the following notation:

* `ᵀ` for `Matrix.transpose`

See `Mathlib/Data/Matrix/ConjTranspose.lean` for

* `ᴴ` for `Matrix.conjTranspose`

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `fun i j ↦ _` or even `(fun i j ↦ _ : Matrix m n α)`, as these are not recognized by Lean
as having the right type. Instead, `Matrix.of` should be used.
-/

assert_not_exists Algebra
assert_not_exists Star

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
which can only be unfolded when fully-applied. https://github.com/leanprover/lean4/issues/2042 means this does not
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

-- TODO: set as an equation lemma for `transpose`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
theorem transpose_apply (M : Matrix m n α) (i j) : transpose M i j = M j i :=
  rfl

@[inherit_doc]
scoped postfix:1024 "ᵀ" => Matrix.transpose

instance inhabited [Inhabited α] : Inhabited (Matrix m n α) :=
  inferInstanceAs <| Inhabited <| m → n → α

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

open Matrix

@[simp]
theorem transpose_transpose (M : Matrix m n α) : Mᵀᵀ = M := by
  ext
  rfl

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

end Transpose

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
  Equiv.ext fun A => (A.submatrix_submatrix eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm : _)

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

end Matrix
