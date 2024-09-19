/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Deprecated.Subgroup
import Mathlib.Deprecated.Group
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Unbundled subrings (deprecated)

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines predicates for unbundled subrings. Instead of using this file, please use
`Subring`, defined in `Mathlib.Algebra.Ring.Subring.Basic`, for subrings of rings.

## Main definitions

`IsSubring (S : Set R) : Prop` : the predicate that `S` is the underlying set of a subring
of the ring `R`. The bundled variant `Subring R` should be used in preference to this.

## Tags

IsSubring
-/


universe u v

open Group

variable {R : Type u} [Ring R]

/-- `S` is a subring: a set containing 1 and closed under multiplication, addition and additive
inverse. -/
structure IsSubring (S : Set R) extends IsAddSubgroup S, IsSubmonoid S : Prop

/-- Construct a `Subring` from a set satisfying `IsSubring`. -/
def IsSubring.subring {S : Set R} (hs : IsSubring S) : Subring R where
  carrier := S
  one_mem' := hs.one_mem
  mul_mem' := hs.mul_mem
  zero_mem' := hs.zero_mem
  add_mem' := hs.add_mem
  neg_mem' := hs.neg_mem

namespace RingHom

theorem isSubring_preimage {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) {s : Set S}
    (hs : IsSubring s) : IsSubring (f ⁻¹' s) :=
  { IsAddGroupHom.preimage f.to_isAddGroupHom hs.toIsAddSubgroup,
    IsSubmonoid.preimage f.to_isMonoidHom hs.toIsSubmonoid with }

theorem isSubring_image {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) {s : Set R}
    (hs : IsSubring s) : IsSubring (f '' s) :=
  { IsAddGroupHom.image_addSubgroup f.to_isAddGroupHom hs.toIsAddSubgroup,
    IsSubmonoid.image f.to_isMonoidHom hs.toIsSubmonoid with }

theorem isSubring_set_range {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) :
    IsSubring (Set.range f) :=
  { IsAddGroupHom.range_addSubgroup f.to_isAddGroupHom, Range.isSubmonoid f.to_isMonoidHom with }

end RingHom

variable {cR : Type u} [CommRing cR]

theorem IsSubring.inter {S₁ S₂ : Set R} (hS₁ : IsSubring S₁) (hS₂ : IsSubring S₂) :
    IsSubring (S₁ ∩ S₂) :=
  { IsAddSubgroup.inter hS₁.toIsAddSubgroup hS₂.toIsAddSubgroup,
    IsSubmonoid.inter hS₁.toIsSubmonoid hS₂.toIsSubmonoid with }

theorem IsSubring.iInter {ι : Sort*} {S : ι → Set R} (h : ∀ y : ι, IsSubring (S y)) :
    IsSubring (Set.iInter S) :=
  { IsAddSubgroup.iInter fun i ↦ (h i).toIsAddSubgroup,
    IsSubmonoid.iInter fun i ↦ (h i).toIsSubmonoid with }

theorem isSubring_iUnion_of_directed {ι : Type*} [Nonempty ι] {s : ι → Set R}
    (h : ∀ i, IsSubring (s i)) (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
    IsSubring (⋃ i, s i) :=
  { toIsAddSubgroup := isAddSubgroup_iUnion_of_directed (fun i ↦ (h i).toIsAddSubgroup) directed
    toIsSubmonoid := isSubmonoid_iUnion_of_directed (fun i ↦ (h i).toIsSubmonoid) directed }

namespace Ring

/-- The smallest subring containing a given subset of a ring, considered as a set. This function
is deprecated; use `Subring.closure`. -/
def closure (s : Set R) :=
  AddGroup.closure (Monoid.Closure s)

variable {s : Set R}

-- attribute [local reducible] closure -- Porting note: not available in Lean4

theorem exists_list_of_mem_closure {a : R} (h : a ∈ closure s) :
    ∃ L : List (List R), (∀ l ∈ L, ∀ x ∈ l, x ∈ s ∨ x = (-1 : R)) ∧ (L.map List.prod).sum = a :=
  AddGroup.InClosure.recOn h
    fun {x} hx ↦ match x, Monoid.exists_list_of_mem_closure hx with
    | _, ⟨L, h1, rfl⟩ => ⟨[L], List.forall_mem_singleton.2 fun r hr ↦ Or.inl (h1 r hr), zero_add _⟩
    ⟨[], List.forall_mem_nil _, rfl⟩
    fun {b} _ ih ↦ match b, ih with
    | _, ⟨L1, h1, rfl⟩ =>
      ⟨L1.map (List.cons (-1)),
        fun L2 h2 ↦ match L2, List.mem_map.1 h2 with
        | _, ⟨L3, h3, rfl⟩ => List.forall_mem_cons.2 ⟨Or.inr rfl, h1 L3 h3⟩, by
        simp only [List.map_map, Function.comp_def, List.prod_cons, neg_one_mul]
        refine List.recOn L1 neg_zero.symm fun hd tl ih ↦ ?_
        rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, neg_add]⟩
    fun {r1 r2} _ _ ih1 ih2 ↦ match r1, r2, ih1, ih2 with
    | _, _, ⟨L1, h1, rfl⟩, ⟨L2, h2, rfl⟩ =>
      ⟨L1 ++ L2, List.forall_mem_append.2 ⟨h1, h2⟩, by rw [List.map_append, List.sum_append]⟩

@[elab_as_elim]
protected theorem InClosure.recOn {C : R → Prop} {x : R} (hx : x ∈ closure s) (h1 : C 1)
    (hneg1 : C (-1)) (hs : ∀ z ∈ s, ∀ n, C n → C (z * n)) (ha : ∀ {x y}, C x → C y → C (x + y)) :
    C x := by
  have h0 : C 0 := add_neg_cancel (1 : R) ▸ ha h1 hneg1
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
  -- Porting note: Expanded `rsuffices`
  suffices ∃ L, (∀ x ∈ L, x ∈ s) ∧ (List.prod hd = List.prod L ∨ List.prod hd = -List.prod L) by
    rcases this with ⟨L, HL', HP | HP⟩ <;> rw [HP] <;> clear HP HL
    · induction' L with hd tl ih
      · exact h1
      rw [List.forall_mem_cons] at HL'
      rw [List.prod_cons]
      exact hs _ HL'.1 _ (ih HL'.2)
    · induction' L with hd tl ih
      · exact hneg1
      rw [List.prod_cons, neg_mul_eq_mul_neg]
      rw [List.forall_mem_cons] at HL'
      exact hs _ HL'.1 _ (ih HL'.2)
  induction' hd with hd tl ih
  · exact ⟨[], List.forall_mem_nil _, Or.inl rfl⟩
  rw [List.forall_mem_cons] at HL
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩ <;> cases' HL.1 with hhd hhd
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inl <| by rw [List.prod_cons, List.prod_cons, HP]⟩
  · exact ⟨L, HL', Or.inr <| by rw [List.prod_cons, hhd, neg_one_mul, HP]⟩
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inr <| by rw [List.prod_cons, List.prod_cons, HP, neg_mul_eq_mul_neg]⟩
  · exact ⟨L, HL', Or.inl <| by rw [List.prod_cons, hhd, HP, neg_one_mul, neg_neg]⟩

theorem closure.isSubring : IsSubring (closure s) :=
  { AddGroup.closure.isAddSubgroup _ with
    one_mem := AddGroup.mem_closure <| IsSubmonoid.one_mem <| Monoid.closure.isSubmonoid _
    mul_mem := fun {a _} ha hb ↦ AddGroup.InClosure.recOn hb
      (fun {c} hc ↦ AddGroup.InClosure.recOn ha
        (fun hd ↦ AddGroup.subset_closure ((Monoid.closure.isSubmonoid _).mul_mem hd hc))
        ((zero_mul c).symm ▸ (AddGroup.closure.isAddSubgroup _).zero_mem)
        (fun {d} _ hdc ↦ neg_mul_eq_neg_mul d c ▸ (AddGroup.closure.isAddSubgroup _).neg_mem hdc)
        fun {d e} _ _ hdc hec ↦
          (add_mul d e c).symm ▸ (AddGroup.closure.isAddSubgroup _).add_mem hdc hec)
      ((mul_zero a).symm ▸ (AddGroup.closure.isAddSubgroup _).zero_mem)
      (fun {c} _ hac ↦ neg_mul_eq_mul_neg a c ▸ (AddGroup.closure.isAddSubgroup _).neg_mem hac)
      fun {c d} _ _ hac had ↦
        (mul_add a c d).symm ▸ (AddGroup.closure.isAddSubgroup _).add_mem hac had }

theorem mem_closure {a : R} : a ∈ s → a ∈ closure s :=
  AddGroup.mem_closure ∘ @Monoid.subset_closure _ _ _ _

theorem subset_closure : s ⊆ closure s :=
  fun _ ↦ mem_closure

theorem closure_subset {t : Set R} (ht : IsSubring t) : s ⊆ t → closure s ⊆ t :=
  AddGroup.closure_subset ht.toIsAddSubgroup ∘ Monoid.closure_subset ht.toIsSubmonoid

theorem closure_subset_iff {s t : Set R} (ht : IsSubring t) : closure s ⊆ t ↔ s ⊆ t :=
  (AddGroup.closure_subset_iff ht.toIsAddSubgroup).trans
    ⟨Set.Subset.trans Monoid.subset_closure, Monoid.closure_subset ht.toIsSubmonoid⟩

theorem closure_mono {s t : Set R} (H : s ⊆ t) : closure s ⊆ closure t :=
  closure_subset closure.isSubring <| Set.Subset.trans H subset_closure

theorem image_closure {S : Type*} [Ring S] (f : R →+* S) (s : Set R) :
    f '' closure s = closure (f '' s) := by
  refine le_antisymm ?_ (closure_subset (RingHom.isSubring_image _ closure.isSubring) <|
    Set.image_subset _ subset_closure)
  rintro _ ⟨x, hx, rfl⟩
  apply AddGroup.InClosure.recOn (motive := fun {x} _ ↦ f x ∈ closure (f '' s)) hx _ <;> intros
  · rw [f.map_zero]
    apply closure.isSubring.zero_mem
  · rw [f.map_neg]
    apply closure.isSubring.neg_mem
    assumption
  · rw [f.map_add]
    apply closure.isSubring.add_mem
    assumption'
  · apply AddGroup.mem_closure
    rw [← Monoid.image_closure f.to_isMonoidHom]
    apply Set.mem_image_of_mem
    assumption

end Ring
