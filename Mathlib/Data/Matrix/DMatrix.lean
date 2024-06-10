/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.Hom.Defs

#align_import data.matrix.dmatrix from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Dependent-typed matrices
-/


universe u u' v w z

/-- `DMatrix m n` is the type of dependently typed matrices
whose rows are indexed by the type `m` and
whose columns are indexed by the type `n`.

In most applications `m` and `n` are finite types. -/
def DMatrix (m : Type u) (n : Type u') (α : m → n → Type v) : Type max u u' v :=
  ∀ i j, α i j
#align dmatrix DMatrix

variable {l m n o : Type*}
variable {α : m → n → Type v}

namespace DMatrix

section Ext

variable {M N : DMatrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩
#align dmatrix.ext_iff DMatrix.ext_iff

@[ext]
theorem ext : (∀ i j, M i j = N i j) → M = N :=
  ext_iff.mp
#align dmatrix.ext DMatrix.ext

end Ext

/-- `M.map f` is the DMatrix obtained by applying `f` to each entry of the matrix `M`. -/
def map (M : DMatrix m n α) {β : m → n → Type w} (f : ∀ ⦃i j⦄, α i j → β i j) : DMatrix m n β :=
  fun i j => f (M i j)
#align dmatrix.map DMatrix.map

@[simp]
theorem map_apply {M : DMatrix m n α} {β : m → n → Type w} {f : ∀ ⦃i j⦄, α i j → β i j} {i : m}
    {j : n} : M.map f i j = f (M i j) := rfl
#align dmatrix.map_apply DMatrix.map_apply

@[simp]
theorem map_map {M : DMatrix m n α} {β : m → n → Type w} {γ : m → n → Type z}
    {f : ∀ ⦃i j⦄, α i j → β i j} {g : ∀ ⦃i j⦄, β i j → γ i j} :
    (M.map f).map g = M.map fun i j x => g (f x) := by ext; simp
#align dmatrix.map_map DMatrix.map_map

/-- The transpose of a dmatrix. -/
def transpose (M : DMatrix m n α) : DMatrix n m fun j i => α i j
  | x, y => M y x
#align dmatrix.transpose DMatrix.transpose

@[inherit_doc]
scoped postfix:1024 "ᵀ" => DMatrix.transpose

/-- `DMatrix.col u` is the column matrix whose entries are given by `u`. -/
def col {α : m → Type v} (w : ∀ i, α i) : DMatrix m Unit fun i _j => α i
  | x, _y => w x
#align dmatrix.col DMatrix.col

/-- `DMatrix.row u` is the row matrix whose entries are given by `u`. -/
def row {α : n → Type v} (v : ∀ j, α j) : DMatrix Unit n fun _i j => α j
  | _x, y => v y
#align dmatrix.row DMatrix.row

instance [∀ i j, Inhabited (α i j)] : Inhabited (DMatrix m n α) :=
  inferInstanceAs <| Inhabited <| ∀ i j, α i j

instance [∀ i j, Add (α i j)] : Add (DMatrix m n α) :=
  inferInstanceAs <| Add <| ∀ i j, α i j

instance [∀ i j, AddSemigroup (α i j)] : AddSemigroup (DMatrix m n α) :=
  inferInstanceAs <| AddSemigroup <| ∀ i j, α i j

instance [∀ i j, AddCommSemigroup (α i j)] : AddCommSemigroup (DMatrix m n α) :=
  inferInstanceAs <| AddCommSemigroup <| ∀ i j, α i j

instance [∀ i j, Zero (α i j)] : Zero (DMatrix m n α) :=
  inferInstanceAs <| Zero <| ∀ i j, α i j

instance [∀ i j, AddMonoid (α i j)] : AddMonoid (DMatrix m n α) :=
  inferInstanceAs <| AddMonoid <| ∀ i j, α i j

instance [∀ i j, AddCommMonoid (α i j)] : AddCommMonoid (DMatrix m n α) :=
  inferInstanceAs <| AddCommMonoid <| ∀ i j, α i j

instance [∀ i j, Neg (α i j)] : Neg (DMatrix m n α) :=
  inferInstanceAs <| Neg <| ∀ i j, α i j

instance [∀ i j, Sub (α i j)] : Sub (DMatrix m n α) :=
  inferInstanceAs <| Sub <| ∀ i j, α i j

instance [∀ i j, AddGroup (α i j)] : AddGroup (DMatrix m n α) :=
  inferInstanceAs <| AddGroup <| ∀ i j, α i j

instance [∀ i j, AddCommGroup (α i j)] : AddCommGroup (DMatrix m n α) :=
  inferInstanceAs <| AddCommGroup <| ∀ i j, α i j

instance [∀ i j, Unique (α i j)] : Unique (DMatrix m n α) :=
  inferInstanceAs <| Unique <| ∀ i j, α i j

instance [∀ i j, Subsingleton (α i j)] : Subsingleton (DMatrix m n α) :=
  inferInstanceAs <| Subsingleton <| ∀ i j, α i j

@[simp]
theorem zero_apply [∀ i j, Zero (α i j)] (i j) : (0 : DMatrix m n α) i j = 0 := rfl
#align dmatrix.zero_apply DMatrix.zero_apply

@[simp]
theorem neg_apply [∀ i j, Neg (α i j)] (M : DMatrix m n α) (i j) : (-M) i j = -M i j := rfl
#align dmatrix.neg_apply DMatrix.neg_apply

@[simp]
theorem add_apply [∀ i j, Add (α i j)] (M N : DMatrix m n α) (i j) : (M + N) i j = M i j + N i j :=
  rfl
#align dmatrix.add_apply DMatrix.add_apply

@[simp]
theorem sub_apply [∀ i j, Sub (α i j)] (M N : DMatrix m n α) (i j) : (M - N) i j = M i j - N i j :=
  rfl
#align dmatrix.sub_apply DMatrix.sub_apply

@[simp]
theorem map_zero [∀ i j, Zero (α i j)] {β : m → n → Type w} [∀ i j, Zero (β i j)]
    {f : ∀ ⦃i j⦄, α i j → β i j} (h : ∀ i j, f (0 : α i j) = 0) :
    (0 : DMatrix m n α).map f = 0 := by ext; simp [h]
#align dmatrix.map_zero DMatrix.map_zero

theorem map_add [∀ i j, AddMonoid (α i j)] {β : m → n → Type w} [∀ i j, AddMonoid (β i j)]
    (f : ∀ ⦃i j⦄, α i j →+ β i j) (M N : DMatrix m n α) :
    ((M + N).map fun i j => @f i j) = (M.map fun i j => @f i j) + N.map fun i j => @f i j := by
  ext; simp
#align dmatrix.map_add DMatrix.map_add

theorem map_sub [∀ i j, AddGroup (α i j)] {β : m → n → Type w} [∀ i j, AddGroup (β i j)]
    (f : ∀ ⦃i j⦄, α i j →+ β i j) (M N : DMatrix m n α) :
    ((M - N).map fun i j => @f i j) = (M.map fun i j => @f i j) - N.map fun i j => @f i j := by
  ext; simp
#align dmatrix.map_sub DMatrix.map_sub

instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (DMatrix m n α) :=
  ⟨fun M N => by
    ext i
    exact isEmptyElim i⟩
#align dmatrix.subsingleton_of_empty_left DMatrix.subsingleton_of_empty_left

instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (DMatrix m n α) :=
  ⟨fun M N => by ext i j; exact isEmptyElim j⟩
#align dmatrix.subsingleton_of_empty_right DMatrix.subsingleton_of_empty_right

end DMatrix

/-- The `AddMonoidHom` between spaces of dependently typed matrices
induced by an `AddMonoidHom` between their coefficients. -/
def AddMonoidHom.mapDMatrix [∀ i j, AddMonoid (α i j)] {β : m → n → Type w}
    [∀ i j, AddMonoid (β i j)] (f : ∀ ⦃i j⦄, α i j →+ β i j) : DMatrix m n α →+ DMatrix m n β where
  toFun M := M.map fun i j => @f i j
  map_zero' := by simp
  map_add' := DMatrix.map_add f
#align add_monoid_hom.map_dmatrix AddMonoidHom.mapDMatrix

@[simp]
theorem AddMonoidHom.mapDMatrix_apply [∀ i j, AddMonoid (α i j)] {β : m → n → Type w}
    [∀ i j, AddMonoid (β i j)] (f : ∀ ⦃i j⦄, α i j →+ β i j) (M : DMatrix m n α) :
    AddMonoidHom.mapDMatrix f M = M.map fun i j => @f i j := rfl
#align add_monoid_hom.map_dmatrix_apply AddMonoidHom.mapDMatrix_apply
