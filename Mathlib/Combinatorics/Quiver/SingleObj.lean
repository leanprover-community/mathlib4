/-
Copyright (c) 2023 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle

! This file was ported from Lean 3 source module combinatorics.quiver.single_obj
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.Quiver.Cast
import Mathbin.Combinatorics.Quiver.Symmetric

/-!
# Single-object quiver

Single object quiver with a given arrows type.

## Main definitions

Given a type `α`, `single_obj α` is the `unit` type, whose single object is called `star α`, with
`quiver` structure such that `star α ⟶ star α` is the type `α`.
An element `x : α` can be reinterpreted as an element of `star α ⟶ star α` using
`to_hom`.
More generally, a list of elements of `a` can be reinterpreted as a path from `star α` to
itself using `path_equiv_list`.
-/


namespace Quiver

/-- Type tag on `unit` used to define single-object quivers. -/
@[nolint unused_arguments]
def SingleObj (α : Type _) : Type :=
  Unit deriving Unique
#align quiver.single_obj Quiver.SingleObj

namespace SingleObj

variable (α β γ : Type _)

instance : Quiver (SingleObj α) :=
  ⟨fun _ _ => α⟩

/-- The single object in `single_obj α`. -/
def star : SingleObj α :=
  Unit.unit
#align quiver.single_obj.star Quiver.SingleObj.star

instance : Inhabited (SingleObj α) :=
  ⟨star α⟩

variable {α β γ}

-- See note [reducible non-instances]
/-- Equip `single_obj α` with a reverse operation. -/
@[reducible]
def hasReverse (rev : α → α) : HasReverse (SingleObj α) :=
  ⟨fun _ _ => rev⟩
#align quiver.single_obj.has_reverse Quiver.SingleObj.hasReverse

-- See note [reducible non-instances]
/-- Equip `single_obj α` with an involutive reverse operation. -/
@[reducible]
def hasInvolutiveReverse (rev : α → α) (h : Function.Involutive rev) :
    HasInvolutiveReverse (SingleObj α)
    where
  toHasReverse := hasReverse rev
  inv' _ _ := h
#align quiver.single_obj.has_involutive_reverse Quiver.SingleObj.hasInvolutiveReverse

/-- The type of arrows from `star α` to itself is equivalent to the original type `α`. -/
@[simps]
def toHom : α ≃ (star α ⟶ star α) :=
  Equiv.refl _
#align quiver.single_obj.to_hom Quiver.SingleObj.toHom

/-- Prefunctors between two `single_obj` quivers correspond to functions between the corresponding
arrows types.
-/
@[simps]
def toPrefunctor : (α → β) ≃ SingleObj α ⥤q SingleObj β
    where
  toFun f := ⟨id, fun _ _ => f⟩
  invFun f a := f.map (toHom a)
  left_inv _ := rfl
  right_inv f := by cases f <;> obviously
#align quiver.single_obj.to_prefunctor Quiver.SingleObj.toPrefunctor

theorem to_prefunctor_id : toPrefunctor id = 𝟭q (SingleObj α) :=
  rfl
#align quiver.single_obj.to_prefunctor_id Quiver.SingleObj.to_prefunctor_id

@[simp]
theorem to_prefunctor_symm_id : toPrefunctor.symm (𝟭q (SingleObj α)) = id :=
  rfl
#align quiver.single_obj.to_prefunctor_symm_id Quiver.SingleObj.to_prefunctor_symm_id

theorem to_prefunctor_comp (f : α → β) (g : β → γ) :
    toPrefunctor (g ∘ f) = toPrefunctor f ⋙q toPrefunctor g :=
  rfl
#align quiver.single_obj.to_prefunctor_comp Quiver.SingleObj.to_prefunctor_comp

@[simp]
theorem to_prefunctor_symm_comp (f : SingleObj α ⥤q SingleObj β) (g : SingleObj β ⥤q SingleObj γ) :
    toPrefunctor.symm (f ⋙q g) = toPrefunctor.symm g ∘ toPrefunctor.symm f := by
  simp only [Equiv.symm_apply_eq, to_prefunctor_comp, Equiv.apply_symm_apply]
#align quiver.single_obj.to_prefunctor_symm_comp Quiver.SingleObj.to_prefunctor_symm_comp

/-- Auxiliary definition for `quiver.single_obj.path_equiv_list`.
Converts a path in the quiver `single_obj α` into a list of elements of type `a`.
-/
@[simp]
def pathToList : ∀ {x : SingleObj α}, Path (star α) x → List α
  | _, path.nil => []
  | _, path.cons p a => a :: path_to_list p
#align quiver.single_obj.path_to_list Quiver.SingleObj.pathToList

/-- Auxiliary definition for `quiver.single_obj.path_equiv_list`.
Converts a list of elements of type `α` into a path in the quiver `single_obj α`.
-/
@[simp]
def listToPath : List α → Path (star α) (star α)
  | [] => Path.nil
  | a :: l => (list_to_path l).cons a
#align quiver.single_obj.list_to_path Quiver.SingleObj.listToPath

theorem path_to_list_to_path {x : SingleObj α} (p : Path (star α) x) :
    listToPath (pathToList p) = p.cast rfl Unit.ext :=
  by
  induction' p with y z p a ih
  rfl
  tidy
#align quiver.single_obj.path_to_list_to_path Quiver.SingleObj.path_to_list_to_path

theorem list_to_path_to_list (l : List α) : pathToList (listToPath l) = l :=
  by
  induction' l with a l ih
  rfl
  simp [ih]
#align quiver.single_obj.list_to_path_to_list Quiver.SingleObj.list_to_path_to_list

/-- Paths in `single_obj α` quiver correspond to lists of elements of type `α`. -/
def pathEquivList : Path (star α) (star α) ≃ List α :=
  ⟨pathToList, listToPath, fun p => path_to_list_to_path p, list_to_path_to_list⟩
#align quiver.single_obj.path_equiv_list Quiver.SingleObj.pathEquivList

@[simp]
theorem path_equiv_list_nil : pathEquivList Path.nil = ([] : List α) :=
  rfl
#align quiver.single_obj.path_equiv_list_nil Quiver.SingleObj.path_equiv_list_nil

@[simp]
theorem path_equiv_list_cons (p : Path (star α) (star α)) (a : star α ⟶ star α) :
    pathEquivList (Path.cons p a) = a :: pathToList p :=
  rfl
#align quiver.single_obj.path_equiv_list_cons Quiver.SingleObj.path_equiv_list_cons

@[simp]
theorem path_equiv_list_symm_nil : pathEquivList.symm ([] : List α) = path.nil :=
  rfl
#align quiver.single_obj.path_equiv_list_symm_nil Quiver.SingleObj.path_equiv_list_symm_nil

@[simp]
theorem path_equiv_list_symm_cons (l : List α) (a : α) :
    pathEquivList.symm (a :: l) = Path.cons (pathEquivList.symm l) a :=
  rfl
#align quiver.single_obj.path_equiv_list_symm_cons Quiver.SingleObj.path_equiv_list_symm_cons

end SingleObj

end Quiver

