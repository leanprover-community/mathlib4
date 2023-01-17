/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.set.Union_lift
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Directed

/-!
# Union lift
This file defines `Set.unionᵢLift` to glue together functions defined on each of a collection of
sets to make a function on the Union of those sets.

## Main definitions

* `Set.unionᵢLift` -  Given a Union of sets `unionᵢ S`, define a function on any subset of the Union
  by defining it on each component, and proving that it agrees on the intersections.
* `Set.liftCover` - Version of `Set.unionᵢLift` for the special case that the sets cover the
  entire type.

## Main statements

There are proofs of the obvious properties of `unionᵢLift`, i.e. what it does to elements of
each of the sets in the `unionᵢ`, stated in different ways.

There are also three lemmas about `unionᵢLift` intended to aid with proving that `unionᵢLift` is a
homomorphism when defined on a Union of substructures. There is one lemma each to show that
constants, unary functions, or binary functions are preserved. These lemmas are:

*`Set.unionᵢLift_const`
*`Set.unionᵢLift_unary`
*`Set.unionᵢLift_binary`

## Tags

directed union, directed supremum, glue, gluing
-/

variable {α ι β : Type _}

namespace Set

section UnionLift

/- The unused argument is left in the definition so that the `simp` lemmas
`unionᵢLift_inclusion` will work without the user having to provide it explicitly to
simplify terms involving `unionᵢLift`. -/
/-- Given a union of sets `unionᵢ S`, define a function on the Union by defining
it on each component, and proving that it agrees on the intersections. -/
@[nolint unusedArguments]
noncomputable def unionᵢLift (S : ι → Set α) (f : ∀ (i) (_ : S i), β)
    (_ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩) (T : Set α)
    (hT : T ⊆ unionᵢ S) (x : T) : β :=
  let i := Classical.indefiniteDescription _ (mem_unionᵢ.1 (hT x.prop))
  f i ⟨x, i.prop⟩
#align set.Union_lift Set.unionᵢLift

variable {S : ι → Set α} {f : ∀ (i) (_ : S i), β}
  {hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩} {T : Set α}
  {hT : T ⊆ unionᵢ S} (hT' : T = unionᵢ S)

@[simp]
theorem unionᵢLift_mk {i : ι} (x : S i) (hx : (x : α) ∈ T) :
    unionᵢLift S f hf T hT ⟨x, hx⟩ = f i x := hf _ i x _ _
#align set.Union_lift_mk Set.unionᵢLift_mk

@[simp]
theorem unionᵢLift_inclusion {i : ι} (x : S i) (h : S i ⊆ T) :
    unionᵢLift S f hf T hT (Set.inclusion h x) = f i x :=
  unionᵢLift_mk x _
#align set.Union_lift_inclusion Set.unionᵢLift_inclusion

theorem unionᵢLift_of_mem (x : T) {i : ι} (hx : (x : α) ∈ S i) :
    unionᵢLift S f hf T hT x = f i ⟨x, hx⟩ := by cases' x with x hx; exact hf _ _ _ _ _
#align set.Union_lift_of_mem Set.unionᵢLift_of_mem

/-- `unionᵢLift_const` is useful for proving that `unionᵢLift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of group homomorphisms on a union of subgroups preserves `1`. -/
theorem unionᵢLift_const (c : T) (ci : ∀ i, S i) (hci : ∀ i, (ci i : α) = c) (cβ : β)
    (h : ∀ i, f i (ci i) = cβ) : unionᵢLift S f hf T hT c = cβ := by
  let ⟨i, hi⟩ := Set.mem_unionᵢ.1 (hT c.prop)
  have : ci i = ⟨c, hi⟩ := Subtype.ext (hci i)
  rw [unionᵢLift_of_mem _ hi, ← this, h]
#align set.Union_lift_const Set.unionᵢLift_const

/-- `unionᵢLift_unary` is useful for proving that `unionᵢLift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of linear_maps on a union of submodules preserves scalar multiplication. -/
theorem unionᵢLift_unary (u : T → T) (ui : ∀ i, S i → S i)
    (hui :
      ∀ (i) (x : S i),
        u (Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_unionᵢ S i) x) =
          Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_unionᵢ S i) (ui i x))
    (uβ : β → β) (h : ∀ (i) (x : S i), f i (ui i x) = uβ (f i x)) (x : T) :
    unionᵢLift S f hf T (le_of_eq hT') (u x) = uβ (unionᵢLift S f hf T (le_of_eq hT') x) := by
  subst hT'
  cases' Set.mem_unionᵢ.1 x.prop with i hi
  rw [unionᵢLift_of_mem x hi, ← h i]
  have : x = Set.inclusion (Set.subset_unionᵢ S i) ⟨x, hi⟩ := by
    cases x
    rfl
  conv_lhs => rw [this, hui, unionᵢLift_inclusion]
#align set.Union_lift_unary Set.unionᵢLift_unary

/-- `unionᵢLift_binary` is useful for proving that `unionᵢLift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of group homomorphisms on a union of subgroups preserves `*`. -/
theorem unionᵢLift_binary (dir : Directed (· ≤ ·) S) (op : T → T → T) (opi : ∀ i, S i → S i → S i)
    (hopi :
      ∀ i x y,
        Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_unionᵢ S i) (opi i x y) =
          op (Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_unionᵢ S i) x)
            (Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_unionᵢ S i) y))
    (opβ : β → β → β) (h : ∀ (i) (x y : S i), f i (opi i x y) = opβ (f i x) (f i y)) (x y : T) :
    unionᵢLift S f hf T (le_of_eq hT') (op x y) =
      opβ (unionᵢLift S f hf T (le_of_eq hT') x) (unionᵢLift S f hf T (le_of_eq hT') y) := by
  subst hT'
  cases' Set.mem_unionᵢ.1 x.prop with i hi
  cases' Set.mem_unionᵢ.1 y.prop with j hj
  rcases dir i j with ⟨k, hik, hjk⟩
  rw [unionᵢLift_of_mem x (hik hi), unionᵢLift_of_mem y (hjk hj), ← h k]
  have hx : x = Set.inclusion (Set.subset_unionᵢ S k) ⟨x, hik hi⟩ := by
    cases x
    rfl
  have hy : y = Set.inclusion (Set.subset_unionᵢ S k) ⟨y, hjk hj⟩ := by
    cases y
    rfl
  have hxy : (Set.inclusion (Set.subset_unionᵢ S k) (opi k ⟨x, hik hi⟩ ⟨y, hjk hj⟩) : α) ∈ S k :=
    (opi k ⟨x, hik hi⟩ ⟨y, hjk hj⟩).prop
  conv_lhs => rw [hx, hy, ← hopi, unionᵢLift_of_mem _ hxy]
#align set.Union_lift_binary Set.unionᵢLift_binary

end UnionLift

variable {S : ι → Set α} {f : ∀ (i) (_ : S i), β}
  {hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
  {hS : unionᵢ S = univ}

/-- Glue together functions defined on each of a collection `S` of sets that cover a type. See
  also `Set.unionᵢLift`.   -/
noncomputable def liftCover (S : ι → Set α) (f : ∀ (i) (_ : S i), β)
    (hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    (hS : unionᵢ S = univ) (a : α) : β :=
  unionᵢLift S f hf univ (hS ▸ Set.Subset.refl _) ⟨a, trivial⟩
#align set.lift_cover Set.liftCover

@[simp]
theorem liftCover_coe {i : ι} (x : S i) : liftCover S f hf hS x = f i x :=
  unionᵢLift_mk x _
#align set.lift_cover_coe Set.liftCover_coe

theorem liftCover_of_mem {i : ι} {x : α} (hx : (x : α) ∈ S i) :
    liftCover S f hf hS x = f i ⟨x, hx⟩ :=
  unionᵢLift_of_mem (⟨x, trivial⟩ : {_z // True}) hx
#align set.lift_cover_of_mem Set.liftCover_of_mem

end Set
