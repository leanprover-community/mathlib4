/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module deprecated.subring
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Deprecated.Subgroup
import Mathbin.Deprecated.Group
import Mathbin.RingTheory.Subring.Basic

/-!
# Unbundled subrings (deprecated)

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines predicates for unbundled subrings. Instead of using this file, please use
`subring`, defined in `ring_theory.subring.basic`, for subrings of rings.

## Main definitions

`is_subring (S : set R) : Prop` : the predicate that `S` is the underlying set of a subring
of the ring `R`. The bundled variant `subring R` should be used in preference to this.

## Tags

is_subring
-/


universe u v

open Group

variable {R : Type u} [Ring R]

/-- `S` is a subring: a set containing 1 and closed under multiplication, addition and additive
inverse. -/
structure IsSubring (S : Set R) extends IsAddSubgroup S, IsSubmonoid S : Prop
#align is_subring IsSubring

/-- Construct a `subring` from a set satisfying `is_subring`. -/
def IsSubring.subring {S : Set R} (hs : IsSubring S) : Subring R
    where
  carrier := S
  one_mem' := hs.one_mem
  mul_mem' _ _ := hs.mul_mem
  zero_mem' := hs.zero_mem
  add_mem' _ _ := hs.add_mem
  neg_mem' _ := hs.neg_mem
#align is_subring.subring IsSubring.subring

namespace RingHom

theorem isSubring_preimage {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) {s : Set S}
    (hs : IsSubring s) : IsSubring (f ⁻¹' s) :=
  { IsAddGroupHom.preimage f.to_isAddGroupHom hs.to_isAddSubgroup,
    IsSubmonoid.preimage f.to_isMonoidHom hs.to_isSubmonoid with }
#align ring_hom.is_subring_preimage RingHom.isSubring_preimage

theorem isSubring_image {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) {s : Set R}
    (hs : IsSubring s) : IsSubring (f '' s) :=
  { IsAddGroupHom.image_addSubgroup f.to_isAddGroupHom hs.to_isAddSubgroup,
    IsSubmonoid.image f.to_isMonoidHom hs.to_isSubmonoid with }
#align ring_hom.is_subring_image RingHom.isSubring_image

theorem isSubring_set_range {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) :
    IsSubring (Set.range f) :=
  { IsAddGroupHom.range_addSubgroup f.to_isAddGroupHom, Range.isSubmonoid f.to_isMonoidHom with }
#align ring_hom.is_subring_set_range RingHom.isSubring_set_range

end RingHom

variable {cR : Type u} [CommRing cR]

theorem IsSubring.inter {S₁ S₂ : Set R} (hS₁ : IsSubring S₁) (hS₂ : IsSubring S₂) :
    IsSubring (S₁ ∩ S₂) :=
  { IsAddSubgroup.inter hS₁.to_isAddSubgroup hS₂.to_isAddSubgroup,
    IsSubmonoid.inter hS₁.to_isSubmonoid hS₂.to_isSubmonoid with }
#align is_subring.inter IsSubring.inter

theorem IsSubring.interᵢ {ι : Sort _} {S : ι → Set R} (h : ∀ y : ι, IsSubring (S y)) :
    IsSubring (Set.interᵢ S) :=
  { IsAddSubgroup.interᵢ fun i => (h i).to_isAddSubgroup,
    IsSubmonoid.interᵢ fun i => (h i).to_isSubmonoid with }
#align is_subring.Inter IsSubring.interᵢ

theorem isSubring_unionᵢ_of_directed {ι : Type _} [hι : Nonempty ι] {s : ι → Set R}
    (h : ∀ i, IsSubring (s i)) (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
    IsSubring (⋃ i, s i) :=
  { to_isAddSubgroup := isAddSubgroup_unionᵢ_of_directed (fun i => (h i).to_isAddSubgroup) Directed
    to_isSubmonoid := isSubmonoid_unionᵢ_of_directed (fun i => (h i).to_isSubmonoid) Directed }
#align is_subring_Union_of_directed isSubring_unionᵢ_of_directed

namespace Ring

/-- The smallest subring containing a given subset of a ring, considered as a set. This function
is deprecated; use `subring.closure`. -/
def closure (s : Set R) :=
  AddGroup.closure (Monoid.Closure s)
#align ring.closure Ring.closure

variable {s : Set R}

attribute [local reducible] closure

theorem exists_list_of_mem_closure {a : R} (h : a ∈ closure s) :
    ∃ L : List (List R), (∀ l ∈ L, ∀ x ∈ l, x ∈ s ∨ x = (-1 : R)) ∧ (L.map List.prod).Sum = a :=
  AddGroup.InClosure.rec_on h
    (fun x hx =>
      match x, Monoid.exists_list_of_mem_closure hx with
      | _, ⟨L, h1, rfl⟩ =>
        ⟨[L], List.forall_mem_singleton.2 fun r hr => Or.inl (h1 r hr), zero_add _⟩)
    ⟨[], List.forall_mem_nil _, rfl⟩
    (fun b _ ih =>
      match b, ih with
      | _, ⟨L1, h1, rfl⟩ =>
        ⟨L1.map (List.cons (-1)), fun L2 h2 =>
          match L2, List.mem_map'.1 h2 with
          | _, ⟨L3, h3, rfl⟩ => List.forall_mem_cons.2 ⟨Or.inr rfl, h1 L3 h3⟩,
          by
          simp only [List.map_map, (· ∘ ·), List.prod_cons, neg_one_mul] <;>
            exact
              List.recOn L1 neg_zero.symm fun hd tl ih => by
                rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, neg_add]⟩)
    fun r1 r2 hr1 hr2 ih1 ih2 =>
    match r1, r2, ih1, ih2 with
    | _, _, ⟨L1, h1, rfl⟩, ⟨L2, h2, rfl⟩ =>
      ⟨L1 ++ L2, List.forall_mem_append.2 ⟨h1, h2⟩, by rw [List.map_append, List.sum_append]⟩
#align ring.exists_list_of_mem_closure Ring.exists_list_of_mem_closure

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[elab_as_elim]
protected theorem InClosure.rec_on {C : R → Prop} {x : R} (hx : x ∈ closure s) (h1 : C 1)
    (hneg1 : C (-1)) (hs : ∀ z ∈ s, ∀ n, C n → C (z * n)) (ha : ∀ {x y}, C x → C y → C (x + y)) :
    C x := by
  have h0 : C 0 := add_neg_self (1 : R) ▸ ha h1 hneg1
  rcases exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩
  clear hx
  induction' L with hd tl ih
  · exact h0
  rw [List.forall_mem_cons] at HL
  suffices C (List.prod hd) by
    rw [List.map_cons, List.sum_cons]
    exact ha this (ih HL.2)
  replace HL := HL.1
  clear ih tl
  rsuffices ⟨L, HL', HP | HP⟩ :
    ∃ L : List R, (∀ x ∈ L, x ∈ s) ∧ (List.prod hd = List.prod L ∨ List.prod hd = -List.prod L)
  · rw [HP]
    clear HP HL hd
    induction' L with hd tl ih
    · exact h1
    rw [List.forall_mem_cons] at HL'
    rw [List.prod_cons]
    exact hs _ HL'.1 _ (ih HL'.2)
  · rw [HP]
    clear HP HL hd
    induction' L with hd tl ih
    · exact hneg1
    rw [List.prod_cons, neg_mul_eq_mul_neg]
    rw [List.forall_mem_cons] at HL'
    exact hs _ HL'.1 _ (ih HL'.2)
  induction' hd with hd tl ih
  · exact ⟨[], List.forall_mem_nil _, Or.inl rfl⟩
  rw [List.forall_mem_cons] at HL
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩ <;> cases' HL.1 with hhd hhd
  ·
    exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inl <| by rw [List.prod_cons, List.prod_cons, HP]⟩
  · exact ⟨L, HL', Or.inr <| by rw [List.prod_cons, hhd, neg_one_mul, HP]⟩
  ·
    exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inr <| by rw [List.prod_cons, List.prod_cons, HP, neg_mul_eq_mul_neg]⟩
  · exact ⟨L, HL', Or.inl <| by rw [List.prod_cons, hhd, HP, neg_one_mul, neg_neg]⟩
#align ring.in_closure.rec_on Ring.InClosure.rec_on

theorem closure.isSubring : IsSubring (closure s) :=
  {
    AddGroup.closure.isAddSubgroup
      _ with
    one_mem := AddGroup.mem_closure <| IsSubmonoid.one_mem <| Monoid.closure.isSubmonoid _
    mul_mem := fun a b ha hb =>
      AddGroup.InClosure.rec_on hb
        (fun c hc =>
          AddGroup.InClosure.rec_on ha
            (fun d hd => AddGroup.subset_closure ((Monoid.closure.isSubmonoid _).mul_mem hd hc))
            ((zero_mul c).symm ▸ (AddGroup.closure.isAddSubgroup _).zero_mem)
            (fun d hd hdc =>
              neg_mul_eq_neg_mul d c ▸ (AddGroup.closure.isAddSubgroup _).neg_mem hdc)
            fun d e hd he hdc hec =>
            (add_mul d e c).symm ▸ (AddGroup.closure.isAddSubgroup _).add_mem hdc hec)
        ((mul_zero a).symm ▸ (AddGroup.closure.isAddSubgroup _).zero_mem)
        (fun c hc hac => neg_mul_eq_mul_neg a c ▸ (AddGroup.closure.isAddSubgroup _).neg_mem hac)
        fun c d hc hd hac had =>
        (mul_add a c d).symm ▸ (AddGroup.closure.isAddSubgroup _).add_mem hac had }
#align ring.closure.is_subring Ring.closure.isSubring

theorem mem_closure {a : R} : a ∈ s → a ∈ closure s :=
  AddGroup.mem_closure ∘ @Monoid.subset_closure _ _ _ _
#align ring.mem_closure Ring.mem_closure

theorem subset_closure : s ⊆ closure s := fun _ => mem_closure
#align ring.subset_closure Ring.subset_closure

theorem closure_subset {t : Set R} (ht : IsSubring t) : s ⊆ t → closure s ⊆ t :=
  AddGroup.closure_subset ht.to_isAddSubgroup ∘ Monoid.closure_subset ht.to_isSubmonoid
#align ring.closure_subset Ring.closure_subset

theorem closure_subset_iff {s t : Set R} (ht : IsSubring t) : closure s ⊆ t ↔ s ⊆ t :=
  (AddGroup.closure_subset_iff ht.to_isAddSubgroup).trans
    ⟨Set.Subset.trans Monoid.subset_closure, Monoid.closure_subset ht.to_isSubmonoid⟩
#align ring.closure_subset_iff Ring.closure_subset_iff

theorem closure_mono {s t : Set R} (H : s ⊆ t) : closure s ⊆ closure t :=
  closure_subset closure.isSubring <| Set.Subset.trans H subset_closure
#align ring.closure_mono Ring.closure_mono

theorem image_closure {S : Type _} [Ring S] (f : R →+* S) (s : Set R) :
    f '' closure s = closure (f '' s) :=
  le_antisymm
    (by
      rintro _ ⟨x, hx, rfl⟩
      apply in_closure.rec_on hx <;> intros
      · rw [f.map_one]
        apply closure.is_subring.to_is_submonoid.one_mem
      · rw [f.map_neg, f.map_one]
        apply closure.is_subring.to_is_add_subgroup.neg_mem
        apply closure.is_subring.to_is_submonoid.one_mem
      · rw [f.map_mul]
        apply closure.is_subring.to_is_submonoid.mul_mem <;>
          solve_by_elim [subset_closure, Set.mem_image_of_mem]
      · rw [f.map_add]
        apply closure.is_subring.to_is_add_submonoid.add_mem
        assumption')
    (closure_subset (RingHom.isSubring_image _ closure.isSubring) <|
      Set.image_subset _ subset_closure)
#align ring.image_closure Ring.image_closure

end Ring

