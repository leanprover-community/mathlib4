/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module data.matrix.dmatrix
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.Data.Fintype.Basic

/-!
# Matrices
-/


universe u u' v w z

/-- `dmatrix m n` is the type of dependently typed matrices
whose rows are indexed by the fintype `m` and
whose columns are indexed by the fintype `n`. -/
@[nolint unused_arguments]
def Dmatrix (m : Type u) (n : Type u') [Fintype m] [Fintype n] (α : m → n → Type v) :
    Type max u u' v :=
  ∀ i j, α i j
#align dmatrix Dmatrix

variable {l m n o : Type _} [Fintype l] [Fintype m] [Fintype n] [Fintype o]

variable {α : m → n → Type v}

namespace Dmatrix

section Ext

variable {M N : Dmatrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩
#align dmatrix.ext_iff Dmatrix.ext_iff

@[ext]
theorem ext : (∀ i j, M i j = N i j) → M = N :=
  ext_iff.mp
#align dmatrix.ext Dmatrix.ext

end Ext

/-- `M.map f` is the dmatrix obtained by applying `f` to each entry of the matrix `M`. -/
def map (M : Dmatrix m n α) {β : m → n → Type w} (f : ∀ ⦃i j⦄, α i j → β i j) : Dmatrix m n β :=
  fun i j => f (M i j)
#align dmatrix.map Dmatrix.map

@[simp]
theorem map_apply {M : Dmatrix m n α} {β : m → n → Type w} {f : ∀ ⦃i j⦄, α i j → β i j} {i : m}
    {j : n} : M.map f i j = f (M i j) :=
  rfl
#align dmatrix.map_apply Dmatrix.map_apply

@[simp]
theorem map_map {M : Dmatrix m n α} {β : m → n → Type w} {γ : m → n → Type z}
    {f : ∀ ⦃i j⦄, α i j → β i j} {g : ∀ ⦃i j⦄, β i j → γ i j} :
    (M.map f).map g = M.map fun i j x => g (f x) :=
  by
  ext
  simp
#align dmatrix.map_map Dmatrix.map_map

/- warning: dmatrix.transpose -> Dmatrix.transpose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u3} n] {α : m -> n -> Type.{u1}}, (Dmatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) -> (Dmatrix.{u3, u2, u1} n m _inst_3 _inst_2 (fun (j : n) (i : m) => α i j))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} [_inst_2 : Fintype.{u1} m] [_inst_3 : Fintype.{u2} n] {α : m -> n -> Type.{u3}}, (Dmatrix.{u1, u2, u3} m n _inst_2 _inst_3 α) -> (Dmatrix.{u2, u1, u3} n m _inst_3 _inst_2 (fun (j : n) (i : m) => α i j))
Case conversion may be inaccurate. Consider using '#align dmatrix.transpose Dmatrix.transposeₓ'. -/
/-- The transpose of a dmatrix. -/
def transpose (M : Dmatrix m n α) : Dmatrix n m fun j i => α i j
  | x, y => M y x
#align dmatrix.transpose Dmatrix.transpose

-- mathport name: dmatrix.transpose
scoped postfix:1024 "ᵀ" => Dmatrix.transpose

/- warning: dmatrix.col -> Dmatrix.col is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} [_inst_2 : Fintype.{u2} m] {α : m -> Type.{u1}}, (forall (i : m), α i) -> (Dmatrix.{u2, 0, u1} m Unit _inst_2 PUnit.fintype.{0} (fun (i : m) (j : Unit) => α i))
but is expected to have type
  forall {m : Type.{u1}} [_inst_2 : Fintype.{u1} m] {α : m -> Type.{u2}}, (forall (i : m), α i) -> (Dmatrix.{u1, 0, u2} m Unit _inst_2 PUnit.fintype.{0} (fun (i : m) (j : Unit) => α i))
Case conversion may be inaccurate. Consider using '#align dmatrix.col Dmatrix.colₓ'. -/
/-- `dmatrix.col u` is the column matrix whose entries are given by `u`. -/
def col {α : m → Type v} (w : ∀ i, α i) : Dmatrix m Unit fun i j => α i
  | x, y => w x
#align dmatrix.col Dmatrix.col

/- warning: dmatrix.row -> Dmatrix.row is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} [_inst_3 : Fintype.{u2} n] {α : n -> Type.{u1}}, (forall (j : n), α j) -> (Dmatrix.{0, u2, u1} Unit n PUnit.fintype.{0} _inst_3 (fun (i : Unit) (j : n) => α j))
but is expected to have type
  forall {n : Type.{u1}} [_inst_3 : Fintype.{u1} n] {α : n -> Type.{u2}}, (forall (j : n), α j) -> (Dmatrix.{0, u1, u2} Unit n PUnit.fintype.{0} _inst_3 (fun (i : Unit) (j : n) => α j))
Case conversion may be inaccurate. Consider using '#align dmatrix.row Dmatrix.rowₓ'. -/
/-- `dmatrix.row u` is the row matrix whose entries are given by `u`. -/
def row {α : n → Type v} (v : ∀ j, α j) : Dmatrix Unit n fun i j => α j
  | x, y => v y
#align dmatrix.row Dmatrix.row

instance [∀ i j, Inhabited (α i j)] : Inhabited (Dmatrix m n α) :=
  Pi.inhabited _

instance [∀ i j, Add (α i j)] : Add (Dmatrix m n α) :=
  Pi.instAdd

instance [∀ i j, AddSemigroup (α i j)] : AddSemigroup (Dmatrix m n α) :=
  Pi.addSemigroup

instance [∀ i j, AddCommSemigroup (α i j)] : AddCommSemigroup (Dmatrix m n α) :=
  Pi.addCommSemigroup

instance [∀ i j, Zero (α i j)] : Zero (Dmatrix m n α) :=
  Pi.instZero

instance [∀ i j, AddMonoid (α i j)] : AddMonoid (Dmatrix m n α) :=
  Pi.addMonoid

instance [∀ i j, AddCommMonoid (α i j)] : AddCommMonoid (Dmatrix m n α) :=
  Pi.addCommMonoid

instance [∀ i j, Neg (α i j)] : Neg (Dmatrix m n α) :=
  Pi.instNeg

instance [∀ i j, Sub (α i j)] : Sub (Dmatrix m n α) :=
  Pi.instSub

instance [∀ i j, AddGroup (α i j)] : AddGroup (Dmatrix m n α) :=
  Pi.addGroup

instance [∀ i j, AddCommGroup (α i j)] : AddCommGroup (Dmatrix m n α) :=
  Pi.addCommGroup

instance [∀ i j, Unique (α i j)] : Unique (Dmatrix m n α) :=
  Pi.unique

instance [∀ i j, Subsingleton (α i j)] : Subsingleton (Dmatrix m n α) :=
  Pi.subsingleton

@[simp]
theorem zero_apply [∀ i j, Zero (α i j)] (i j) : (0 : Dmatrix m n α) i j = 0 :=
  rfl
#align dmatrix.zero_apply Dmatrix.zero_apply

@[simp]
theorem neg_apply [∀ i j, Neg (α i j)] (M : Dmatrix m n α) (i j) : (-M) i j = -M i j :=
  rfl
#align dmatrix.neg_apply Dmatrix.neg_apply

@[simp]
theorem add_apply [∀ i j, Add (α i j)] (M N : Dmatrix m n α) (i j) : (M + N) i j = M i j + N i j :=
  rfl
#align dmatrix.add_apply Dmatrix.add_apply

@[simp]
theorem sub_apply [∀ i j, Sub (α i j)] (M N : Dmatrix m n α) (i j) : (M - N) i j = M i j - N i j :=
  rfl
#align dmatrix.sub_apply Dmatrix.sub_apply

@[simp]
theorem map_zero [∀ i j, Zero (α i j)] {β : m → n → Type w} [∀ i j, Zero (β i j)]
    {f : ∀ ⦃i j⦄, α i j → β i j} (h : ∀ i j, f (0 : α i j) = 0) : (0 : Dmatrix m n α).map f = 0 :=
  by
  ext
  simp [h]
#align dmatrix.map_zero Dmatrix.map_zero

theorem map_add [∀ i j, AddMonoid (α i j)] {β : m → n → Type w} [∀ i j, AddMonoid (β i j)]
    (f : ∀ ⦃i j⦄, α i j →+ β i j) (M N : Dmatrix m n α) :
    ((M + N).map fun i j => @f i j) = (M.map fun i j => @f i j) + N.map fun i j => @f i j :=
  by
  ext
  simp
#align dmatrix.map_add Dmatrix.map_add

theorem map_sub [∀ i j, AddGroup (α i j)] {β : m → n → Type w} [∀ i j, AddGroup (β i j)]
    (f : ∀ ⦃i j⦄, α i j →+ β i j) (M N : Dmatrix m n α) :
    ((M - N).map fun i j => @f i j) = (M.map fun i j => @f i j) - N.map fun i j => @f i j :=
  by
  ext
  simp
#align dmatrix.map_sub Dmatrix.map_sub

instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (Dmatrix m n α) :=
  ⟨fun M N => by
    ext
    exact isEmptyElim i⟩
#align dmatrix.subsingleton_of_empty_left Dmatrix.subsingleton_of_empty_left

instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (Dmatrix m n α) :=
  ⟨fun M N => by
    ext
    exact isEmptyElim j⟩
#align dmatrix.subsingleton_of_empty_right Dmatrix.subsingleton_of_empty_right

end Dmatrix

/-- The `add_monoid_hom` between spaces of dependently typed matrices
induced by an `add_monoid_hom` between their coefficients. -/
def AddMonoidHom.mapDmatrix [∀ i j, AddMonoid (α i j)] {β : m → n → Type w}
    [∀ i j, AddMonoid (β i j)] (f : ∀ ⦃i j⦄, α i j →+ β i j) : Dmatrix m n α →+ Dmatrix m n β
    where
  toFun M := M.map fun i j => @f i j
  map_zero' := by simp
  map_add' := Dmatrix.map_add f
#align add_monoid_hom.map_dmatrix AddMonoidHom.mapDmatrix

@[simp]
theorem AddMonoidHom.map_dmatrix_apply [∀ i j, AddMonoid (α i j)] {β : m → n → Type w}
    [∀ i j, AddMonoid (β i j)] (f : ∀ ⦃i j⦄, α i j →+ β i j) (M : Dmatrix m n α) :
    AddMonoidHom.mapDmatrix f M = M.map fun i j => @f i j :=
  rfl
#align add_monoid_hom.map_dmatrix_apply AddMonoidHom.map_dmatrix_apply

