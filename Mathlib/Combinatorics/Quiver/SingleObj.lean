/-
Copyright (c) 2023 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.Combinatorics.Quiver.Cast
import Mathlib.Combinatorics.Quiver.Symmetric

#align_import combinatorics.quiver.single_obj from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# Single-object quiver

Single object quiver with a given arrows type.

## Main definitions

Given a type `α`, `SingleObj α` is the `Unit` type, whose single object is called `star α`, with
`Quiver` structure such that `star α ⟶ star α` is the type `α`.
An element `x : α` can be reinterpreted as an element of `star α ⟶ star α` using
`toHom`.
More generally, a list of elements of `a` can be reinterpreted as a path from `star α` to
itself using `pathEquivList`.
-/

namespace Quiver

/-- Type tag on `Unit` used to define single-object quivers. -/
-- Porting note: Removed `deriving Unique`.
@[nolint unusedArguments]
def SingleObj (_ : Type*) : Type :=
  Unit
#align quiver.single_obj Quiver.SingleObj

-- Porting note: `deriving` from above has been moved to below.
instance {α : Type*} : Unique (SingleObj α) where
  default := ⟨⟩
  uniq := fun _ => rfl

namespace SingleObj

variable (α β γ : Type*)

instance : Quiver (SingleObj α) :=
  ⟨fun _ _ => α⟩

/-- The single object in `SingleObj α`. -/
def star : SingleObj α :=
  Unit.unit
#align quiver.single_obj.star Quiver.SingleObj.star

instance : Inhabited (SingleObj α) :=
  ⟨star α⟩

variable {α β γ}

lemma ext {x y : SingleObj α} : x = y := Unit.ext x y

-- See note [reducible non-instances]
/-- Equip `SingleObj α` with a reverse operation. -/
abbrev hasReverse (rev : α → α) : HasReverse (SingleObj α) := ⟨rev⟩
#align quiver.single_obj.has_reverse Quiver.SingleObj.hasReverse

-- See note [reducible non-instances]
/-- Equip `SingleObj α` with an involutive reverse operation. -/
abbrev hasInvolutiveReverse (rev : α → α) (h : Function.Involutive rev) :
    HasInvolutiveReverse (SingleObj α) where
  toHasReverse := hasReverse rev
  inv' := h
#align quiver.single_obj.has_involutive_reverse Quiver.SingleObj.hasInvolutiveReverse

/-- The type of arrows from `star α` to itself is equivalent to the original type `α`. -/
@[simps!]
def toHom : α ≃ (star α ⟶ star α) :=
  Equiv.refl _
#align quiver.single_obj.to_hom Quiver.SingleObj.toHom
#align quiver.single_obj.to_hom_apply Quiver.SingleObj.toHom_apply
#align quiver.single_obj.to_hom_symm_apply Quiver.SingleObj.toHom_symm_apply

/-- Prefunctors between two `SingleObj` quivers correspond to functions between the corresponding
arrows types.
-/
@[simps]
def toPrefunctor : (α → β) ≃ SingleObj α ⥤q SingleObj β where
  toFun f := ⟨id, f⟩
  invFun f a := f.map (toHom a)
  left_inv _ := rfl
  right_inv _ := rfl
#align quiver.single_obj.to_prefunctor_symm_apply Quiver.SingleObj.toPrefunctor_symm_apply
#align quiver.single_obj.to_prefunctor_apply_map Quiver.SingleObj.toPrefunctor_apply_map
#align quiver.single_obj.to_prefunctor_apply_obj Quiver.SingleObj.toPrefunctor_apply_obj

#align quiver.single_obj.to_prefunctor Quiver.SingleObj.toPrefunctor

theorem toPrefunctor_id : toPrefunctor id = 𝟭q (SingleObj α) :=
  rfl
#align quiver.single_obj.to_prefunctor_id Quiver.SingleObj.toPrefunctor_id

@[simp]
theorem toPrefunctor_symm_id : toPrefunctor.symm (𝟭q (SingleObj α)) = id :=
  rfl
#align quiver.single_obj.to_prefunctor_symm_id Quiver.SingleObj.toPrefunctor_symm_id

theorem toPrefunctor_comp (f : α → β) (g : β → γ) :
    toPrefunctor (g ∘ f) = toPrefunctor f ⋙q toPrefunctor g :=
  rfl
#align quiver.single_obj.to_prefunctor_comp Quiver.SingleObj.toPrefunctor_comp

@[simp]
theorem toPrefunctor_symm_comp (f : SingleObj α ⥤q SingleObj β) (g : SingleObj β ⥤q SingleObj γ) :
    toPrefunctor.symm (f ⋙q g) = toPrefunctor.symm g ∘ toPrefunctor.symm f := by
  simp only [Equiv.symm_apply_eq, toPrefunctor_comp, Equiv.apply_symm_apply]
#align quiver.single_obj.to_prefunctor_symm_comp Quiver.SingleObj.toPrefunctor_symm_comp

/-- Auxiliary definition for `quiver.SingleObj.pathEquivList`.
Converts a path in the quiver `single_obj α` into a list of elements of type `a`.
-/
def pathToList : ∀ {x : SingleObj α}, Path (star α) x → List α
  | _, Path.nil => []
  | _, Path.cons p a => a :: pathToList p
#align quiver.single_obj.path_to_list Quiver.SingleObj.pathToList

/-- Auxiliary definition for `quiver.SingleObj.pathEquivList`.
Converts a list of elements of type `α` into a path in the quiver `SingleObj α`.
-/
@[simp]
def listToPath : List α → Path (star α) (star α)
  | [] => Path.nil
  | a :: l => (listToPath l).cons a
#align quiver.single_obj.list_to_path Quiver.SingleObj.listToPath

theorem listToPath_pathToList {x : SingleObj α} (p : Path (star α) x) :
    listToPath (pathToList p) = p.cast rfl ext := by
  induction' p with y z p a ih
  · rfl
  · dsimp at *; rw [ih]
#align quiver.single_obj.path_to_list_to_path Quiver.SingleObj.listToPath_pathToList

theorem pathToList_listToPath (l : List α) : pathToList (listToPath l) = l := by
  induction' l with a l ih
  · rfl
  · change a :: pathToList (listToPath l) = a :: l; rw [ih]
#align quiver.single_obj.list_to_path_to_list Quiver.SingleObj.pathToList_listToPath

/-- Paths in `SingleObj α` quiver correspond to lists of elements of type `α`. -/
def pathEquivList : Path (star α) (star α) ≃ List α :=
  ⟨pathToList, listToPath, fun p => listToPath_pathToList p, pathToList_listToPath⟩
#align quiver.single_obj.path_equiv_list Quiver.SingleObj.pathEquivList

@[simp]
theorem pathEquivList_nil : pathEquivList Path.nil = ([] : List α) :=
  rfl
#align quiver.single_obj.path_equiv_list_nil Quiver.SingleObj.pathEquivList_nil

@[simp]
theorem pathEquivList_cons (p : Path (star α) (star α)) (a : star α ⟶ star α) :
    pathEquivList (Path.cons p a) = a :: pathToList p :=
  rfl
#align quiver.single_obj.path_equiv_list_cons Quiver.SingleObj.pathEquivList_cons

@[simp]
theorem pathEquivList_symm_nil : pathEquivList.symm ([] : List α) = Path.nil :=
  rfl
#align quiver.single_obj.path_equiv_list_symm_nil Quiver.SingleObj.pathEquivList_symm_nil

@[simp]
theorem pathEquivList_symm_cons (l : List α) (a : α) :
    pathEquivList.symm (a :: l) = Path.cons (pathEquivList.symm l) a :=
  rfl
#align quiver.single_obj.path_equiv_list_symm_cons Quiver.SingleObj.pathEquivList_symm_cons

end SingleObj

end Quiver
