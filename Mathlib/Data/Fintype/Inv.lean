/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Defs

/-!
# Computable inverses for injective/surjective functions on finite types

## Main results

* `Function.Injective.invOfMemRange`, `Embedding.invOfMemRange`, `Fintype.bijInv`:
  computable versions of `Function.invFun`.
* `Fintype.choose`: computably obtain a witness for `ExistsUnique`.
-/

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

section Inv

namespace Function

variable [Fintype α] [DecidableEq β]

namespace Injective

variable {f : α → β} (hf : Function.Injective f)

/-- The inverse of an `hf : injective` function `f : α → β`, of the type `↥(Set.range f) → α`.
This is the computable version of `Function.invFun` that requires `Fintype α` and `DecidableEq β`,
or the function version of applying `(Equiv.ofInjective f hf).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = Fintype.card α`.
-/
def invOfMemRange : Set.range f → α := fun b =>
  Finset.choose (fun a => f a = b) Finset.univ
    ((existsUnique_congr (by simp)).mp (hf.existsUnique_of_mem_range b.property))

theorem left_inv_of_invOfMemRange (b : Set.range f) : f (hf.invOfMemRange b) = b :=
  (Finset.choose_spec (fun a => f a = b) _ _).right

@[simp]
theorem right_inv_of_invOfMemRange (a : α) : hf.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  hf (Finset.choose_spec (fun a' => f a' = f a) _ _).right

theorem invFun_restrict [Nonempty α] : (Set.range f).restrict (invFun f) = hf.invOfMemRange := by
  ext ⟨b, h⟩
  apply hf
  simp [hf.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]

theorem invOfMemRange_surjective : Function.Surjective hf.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩

end Injective

namespace Embedding

variable (f : α ↪ β) (b : Set.range f)

/-- The inverse of an embedding `f : α ↪ β`, of the type `↥(Set.range f) → α`.
This is the computable version of `Function.invFun` that requires `Fintype α` and `DecidableEq β`,
or the function version of applying `(Equiv.ofInjective f f.injective).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = Fintype.card α`.
-/
def invOfMemRange : α :=
  f.injective.invOfMemRange b

@[simp]
theorem left_inv_of_invOfMemRange : f (f.invOfMemRange b) = b :=
  f.injective.left_inv_of_invOfMemRange b

@[simp]
theorem right_inv_of_invOfMemRange (a : α) : f.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  f.injective.right_inv_of_invOfMemRange a

theorem invFun_restrict [Nonempty α] : (Set.range f).restrict (invFun f) = f.invOfMemRange := by
  ext ⟨b, h⟩
  apply f.injective
  simp [f.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]

theorem invOfMemRange_surjective : Function.Surjective f.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩

end Embedding

end Function

end Inv

open Finset

namespace Fintype

section Choose

open Fintype Equiv

variable [Fintype α] (p : α → Prop) [DecidablePred p]

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def chooseX (hp : ∃! a : α, p a) : { a // p a } :=
  ⟨Finset.choose p univ (by simpa), Finset.choose_property _ _ _⟩

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of `α`. -/
def choose (hp : ∃! a, p a) : α :=
  chooseX p hp

theorem choose_spec (hp : ∃! a, p a) : p (choose p hp) :=
  (chooseX p hp).property

theorem choose_subtype_eq {α : Type*} (p : α → Prop) [Fintype { a : α // p a }] [DecidableEq α]
    (x : { a : α // p a })
    (h : ∃! a : { a // p a }, (a : α) = x :=
      ⟨x, rfl, fun y hy => by simpa [Subtype.ext_iff] using hy⟩) :
    Fintype.choose (fun y : { a : α // p a } => (y : α) = x) h = x := by
  rw [Subtype.ext_iff, Fintype.choose_spec (fun y : { a : α // p a } => (y : α) = x) _]

end Choose

section BijectionInverse

variable [Fintype α] [DecidableEq β] {f : α → β}

/-- `bijInv f` is the unique inverse to a bijection `f`. This acts
  as a computable alternative to `Function.invFun`. -/
def bijInv (f_bij : Bijective f) (b : β) : α :=
  Fintype.choose (fun a => f a = b) (f_bij.existsUnique b)

theorem leftInverse_bijInv (f_bij : Bijective f) : LeftInverse (bijInv f_bij) f := fun a =>
  f_bij.left (choose_spec (fun a' => f a' = f a) _)

theorem rightInverse_bijInv (f_bij : Bijective f) : RightInverse (bijInv f_bij) f := fun b =>
  choose_spec (fun a' => f a' = b) _

theorem bijective_bijInv (f_bij : Bijective f) : Bijective (bijInv f_bij) :=
  ⟨(rightInverse_bijInv _).injective, (leftInverse_bijInv _).surjective⟩

end BijectionInverse

end Fintype
