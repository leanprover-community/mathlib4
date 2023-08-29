/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard
-/
import Mathlib.GroupTheory.Submonoid.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Deprecated.Group

#align_import deprecated.submonoid from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# Unbundled submonoids (deprecated)

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines unbundled multiplicative and additive submonoids. Instead of using this file,
please use `Submonoid G` and `AddSubmonoid A`, defined in `GroupTheory.Submonoid.Basic`.

## Main definitions

`IsAddSubmonoid (S : Set M)` : the predicate that `S` is the underlying subset of an additive
submonoid of `M`. The bundled variant `AddSubmonoid M` should be used in preference to this.

`IsSubmonoid (S : Set M)` : the predicate that `S` is the underlying subset of a submonoid
of `M`. The bundled variant `Submonoid M` should be used in preference to this.

## Tags
Submonoid, Submonoids, IsSubmonoid
-/


open BigOperators

variable {M : Type*} [Monoid M] {s : Set M}

variable {A : Type*} [AddMonoid A] {t : Set A}

/-- `s` is an additive submonoid: a set containing 0 and closed under addition.
Note that this structure is deprecated, and the bundled variant `AddSubmonoid A` should be
preferred. -/
structure IsAddSubmonoid (s : Set A) : Prop where
  /-- The proposition that s contains 0. -/
  zero_mem : (0 : A) ∈ s
  /-- The proposition that s is closed under addition. -/
  add_mem {a b} : a ∈ s → b ∈ s → a + b ∈ s
#align is_add_submonoid IsAddSubmonoid

/-- `s` is a submonoid: a set containing 1 and closed under multiplication.
Note that this structure is deprecated, and the bundled variant `Submonoid M` should be
preferred. -/
@[to_additive]
structure IsSubmonoid (s : Set M) : Prop where
  /-- The proposition that s contains 1. -/
  one_mem : (1 : M) ∈ s
  /-- The proposition that s is closed under multiplication. -/
  mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s
#align is_submonoid IsSubmonoid

theorem Additive.isAddSubmonoid {s : Set M} :
    ∀ _ : IsSubmonoid s, @IsAddSubmonoid (Additive M) _ s
  | ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩
#align additive.is_add_submonoid Additive.isAddSubmonoid

theorem Additive.isAddSubmonoid_iff {s : Set M} :
    @IsAddSubmonoid (Additive M) _ s ↔ IsSubmonoid s :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩, Additive.isAddSubmonoid⟩
#align additive.is_add_submonoid_iff Additive.isAddSubmonoid_iff

theorem Multiplicative.isSubmonoid {s : Set A} :
    ∀ _ : IsAddSubmonoid s, @IsSubmonoid (Multiplicative A) _ s
  | ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩
#align multiplicative.is_submonoid Multiplicative.isSubmonoid

theorem Multiplicative.isSubmonoid_iff {s : Set A} :
    @IsSubmonoid (Multiplicative A) _ s ↔ IsAddSubmonoid s :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩, Multiplicative.isSubmonoid⟩
#align multiplicative.is_submonoid_iff Multiplicative.isSubmonoid_iff

/-- The intersection of two submonoids of a monoid `M` is a submonoid of `M`. -/
@[to_additive
      "The intersection of two `AddSubmonoid`s of an `AddMonoid` `M` is an `AddSubmonoid` of M."]
theorem IsSubmonoid.inter {s₁ s₂ : Set M} (is₁ : IsSubmonoid s₁) (is₂ : IsSubmonoid s₂) :
    IsSubmonoid (s₁ ∩ s₂) :=
  { one_mem := ⟨is₁.one_mem, is₂.one_mem⟩
    mul_mem := @fun _ _ hx hy => ⟨is₁.mul_mem hx.1 hy.1, is₂.mul_mem hx.2 hy.2⟩ }
#align is_submonoid.inter IsSubmonoid.inter
#align is_add_submonoid.inter IsAddSubmonoid.inter

/-- The intersection of an indexed set of submonoids of a monoid `M` is a submonoid of `M`. -/
@[to_additive
      "The intersection of an indexed set of `AddSubmonoid`s of an `AddMonoid` `M` is
      an `AddSubmonoid` of `M`."]
theorem IsSubmonoid.iInter {ι : Sort*} {s : ι → Set M} (h : ∀ y : ι, IsSubmonoid (s y)) :
    IsSubmonoid (Set.iInter s) :=
  { one_mem := Set.mem_iInter.2 fun y => (h y).one_mem
    mul_mem := fun h₁ h₂ =>
      Set.mem_iInter.2 fun y => (h y).mul_mem (Set.mem_iInter.1 h₁ y) (Set.mem_iInter.1 h₂ y) }
#align is_submonoid.Inter IsSubmonoid.iInter
#align is_add_submonoid.Inter IsAddSubmonoid.iInter

/-- The union of an indexed, directed, nonempty set of submonoids of a monoid `M` is a submonoid
    of `M`. -/
@[to_additive
      "The union of an indexed, directed, nonempty set of `AddSubmonoid`s of an `AddMonoid` `M`
      is an `AddSubmonoid` of `M`. "]
theorem isSubmonoid_iUnion_of_directed {ι : Type*} [hι : Nonempty ι] {s : ι → Set M}
    (hs : ∀ i, IsSubmonoid (s i)) (Directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
    IsSubmonoid (⋃ i, s i) :=
  { one_mem :=
      let ⟨i⟩ := hι
      Set.mem_iUnion.2 ⟨i, (hs i).one_mem⟩
    mul_mem := fun ha hb =>
      let ⟨i, hi⟩ := Set.mem_iUnion.1 ha
      let ⟨j, hj⟩ := Set.mem_iUnion.1 hb
      let ⟨k, hk⟩ := Directed i j
      Set.mem_iUnion.2 ⟨k, (hs k).mul_mem (hk.1 hi) (hk.2 hj)⟩ }
#align is_submonoid_Union_of_directed isSubmonoid_iUnion_of_directed
#align is_add_submonoid_Union_of_directed isAddSubmonoid_iUnion_of_directed

section powers

/-- The set of natural number powers `1, x, x², ...` of an element `x` of a monoid. -/
@[to_additive multiples
      "The set of natural number multiples `0, x, 2x, ...` of an element `x` of an `AddMonoid`."]
def powers (x : M) : Set M :=
  { y | ∃ n : ℕ, x ^ n = y }
#align powers powers
#align multiples multiples

/-- 1 is in the set of natural number powers of an element of a monoid. -/
@[to_additive "0 is in the set of natural number multiples of an element of an `AddMonoid`."]
theorem powers.one_mem {x : M} : (1 : M) ∈ powers x :=
  ⟨0, pow_zero _⟩
#align powers.one_mem powers.one_mem
#align multiples.zero_mem multiples.zero_mem

/-- An element of a monoid is in the set of that element's natural number powers. -/
@[to_additive
      "An element of an `AddMonoid` is in the set of that element's natural number multiples."]
theorem powers.self_mem {x : M} : x ∈ powers x :=
  ⟨1, pow_one _⟩
#align powers.self_mem powers.self_mem
#align multiples.self_mem multiples.self_mem

/-- The set of natural number powers of an element of a monoid is closed under multiplication. -/
@[to_additive
      "The set of natural number multiples of an element of an `AddMonoid` is closed under
      addition."]
theorem powers.mul_mem {x y z : M} : y ∈ powers x → z ∈ powers x → y * z ∈ powers x :=
  fun ⟨n₁, h₁⟩ ⟨n₂, h₂⟩ => ⟨n₁ + n₂, by simp only [pow_add, *]⟩
                                        -- 🎉 no goals
#align powers.mul_mem powers.mul_mem
#align multiples.add_mem multiples.add_mem

/-- The set of natural number powers of an element of a monoid `M` is a submonoid of `M`. -/
@[to_additive
      "The set of natural number multiples of an element of an `AddMonoid` `M` is
      an `AddSubmonoid` of `M`."]
theorem powers.isSubmonoid (x : M) : IsSubmonoid (powers x) :=
  { one_mem := powers.one_mem
    mul_mem := powers.mul_mem }
#align powers.is_submonoid powers.isSubmonoid
#align multiples.is_add_submonoid multiples.isAddSubmonoid

/-- A monoid is a submonoid of itself. -/
@[to_additive "An `AddMonoid` is an `AddSubmonoid` of itself."]
theorem Univ.isSubmonoid : IsSubmonoid (@Set.univ M) := by constructor <;> simp
                                                           -- ⊢ 1 ∈ Set.univ
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
#align univ.is_submonoid Univ.isSubmonoid
#align univ.is_add_submonoid Univ.isAddSubmonoid

/-- The preimage of a submonoid under a monoid hom is a submonoid of the domain. -/
@[to_additive
      "The preimage of an `AddSubmonoid` under an `AddMonoid` hom is
      an `AddSubmonoid` of the domain."]
theorem IsSubmonoid.preimage {N : Type*} [Monoid N] {f : M → N} (hf : IsMonoidHom f) {s : Set N}
    (hs : IsSubmonoid s) : IsSubmonoid (f ⁻¹' s) :=
  { one_mem := show f 1 ∈ s by (rw [IsMonoidHom.map_one hf]; exact hs.one_mem)
                                -- ⊢ 1 ∈ s
                                                             -- 🎉 no goals
    mul_mem := fun {a b} (ha : f a ∈ s) (hb : f b ∈ s) =>
      show f (a * b) ∈ s by (rw [IsMonoidHom.map_mul' hf]; exact hs.mul_mem ha hb) }
                             -- ⊢ f a * f b ∈ s
                                                           -- 🎉 no goals
#align is_submonoid.preimage IsSubmonoid.preimage
#align is_add_submonoid.preimage IsAddSubmonoid.preimage

/-- The image of a submonoid under a monoid hom is a submonoid of the codomain. -/
@[to_additive
      "The image of an `AddSubmonoid` under an `AddMonoid` hom is an `AddSubmonoid` of the
      codomain."]
theorem IsSubmonoid.image {γ : Type*} [Monoid γ] {f : M → γ} (hf : IsMonoidHom f) {s : Set M}
    (hs : IsSubmonoid s) : IsSubmonoid (f '' s) :=
  { one_mem := ⟨1, hs.one_mem, hf.map_one⟩
    mul_mem := @fun a b ⟨x, hx⟩ ⟨y, hy⟩ =>
      ⟨x * y, hs.mul_mem hx.1 hy.1, by rw [hf.map_mul, hx.2, hy.2]⟩ }
                                       -- 🎉 no goals
#align is_submonoid.image IsSubmonoid.image
#align is_add_submonoid.image IsAddSubmonoid.image

/-- The image of a monoid hom is a submonoid of the codomain. -/
@[to_additive "The image of an `AddMonoid` hom is an `AddSubmonoid` of the codomain."]
theorem Range.isSubmonoid {γ : Type*} [Monoid γ] {f : M → γ} (hf : IsMonoidHom f) :
    IsSubmonoid (Set.range f) := by
  rw [← Set.image_univ]
  -- ⊢ IsSubmonoid (f '' Set.univ)
  exact Univ.isSubmonoid.image hf
  -- 🎉 no goals
#align range.is_submonoid Range.isSubmonoid
#align range.is_add_submonoid Range.isAddSubmonoid

/-- Submonoids are closed under natural powers. -/
@[to_additive
      "An `AddSubmonoid` is closed under multiplication by naturals."]
theorem IsSubmonoid.pow_mem {a : M} (hs : IsSubmonoid s) (h : a ∈ s) : ∀ {n : ℕ}, a ^ n ∈ s
  | 0 => by
    rw [pow_zero]
    -- ⊢ 1 ∈ s
    exact hs.one_mem
    -- 🎉 no goals
  | n + 1 => by
    rw [pow_succ]
    -- ⊢ a * a ^ n ∈ s
    exact hs.mul_mem h (IsSubmonoid.pow_mem hs h)
    -- 🎉 no goals
#align is_submonoid.pow_mem IsSubmonoid.pow_mem

/-- The set of natural number powers of an element of a submonoid is a subset of the submonoid. -/
@[to_additive IsAddSubmonoid.multiples_subset
      "The set of natural number multiples of an element of an `AddSubmonoid` is a subset of
      the `AddSubmonoid`."]
theorem IsSubmonoid.power_subset {a : M} (hs : IsSubmonoid s) (h : a ∈ s) : powers a ⊆ s :=
  fun _ ⟨_, hx⟩ => hx ▸ hs.pow_mem h
#align is_submonoid.power_subset IsSubmonoid.power_subset
#align is_add_submonoid.multiples_subset IsAddSubmonoid.multiples_subset

end powers

namespace IsSubmonoid

/-- The product of a list of elements of a submonoid is an element of the submonoid. -/
@[to_additive
      "The sum of a list of elements of an `AddSubmonoid` is an element of the `AddSubmonoid`."]
theorem list_prod_mem (hs : IsSubmonoid s) : ∀ {l : List M}, (∀ x ∈ l, x ∈ s) → l.prod ∈ s
  | [], _ => hs.one_mem
  | a :: l, h =>
    suffices a * l.prod ∈ s by simpa
                               -- 🎉 no goals
                                        -- 🎉 no goals
    have : a ∈ s ∧ ∀ x ∈ l, x ∈ s := by simpa using h
    hs.mul_mem this.1 (list_prod_mem hs this.2)
#align is_submonoid.list_prod_mem IsSubmonoid.list_prod_mem
#align is_add_submonoid.list_sum_mem IsAddSubmonoid.list_sum_mem

/-- The product of a multiset of elements of a submonoid of a `CommMonoid` is an element of
the submonoid. -/
@[to_additive
      "The sum of a multiset of elements of an `AddSubmonoid` of an `AddCommMonoid`
      is an element of the `AddSubmonoid`. "]
theorem multiset_prod_mem {M} [CommMonoid M] {s : Set M} (hs : IsSubmonoid s) (m : Multiset M) :
    (∀ a ∈ m, a ∈ s) → m.prod ∈ s := by
  refine' Quotient.inductionOn m fun l hl => _
  -- ⊢ Multiset.prod (Quotient.mk (List.isSetoid M) l) ∈ s
  rw [Multiset.quot_mk_to_coe, Multiset.coe_prod]
  -- ⊢ List.prod l ∈ s
  exact list_prod_mem hs hl
  -- 🎉 no goals
#align is_submonoid.multiset_prod_mem IsSubmonoid.multiset_prod_mem
#align is_add_submonoid.multiset_sum_mem IsAddSubmonoid.multiset_sum_mem

/-- The product of elements of a submonoid of a `CommMonoid` indexed by a `Finset` is an element
of the submonoid. -/
@[to_additive
      "The sum of elements of an `AddSubmonoid` of an `AddCommMonoid` indexed by
      a `Finset` is an element of the `AddSubmonoid`."]
theorem finset_prod_mem {M A} [CommMonoid M] {s : Set M} (hs : IsSubmonoid s) (f : A → M) :
    ∀ t : Finset A, (∀ b ∈ t, f b ∈ s) → (∏ b in t, f b) ∈ s
  | ⟨m, hm⟩, _ => multiset_prod_mem hs _ (by simpa)
                                             -- 🎉 no goals
#align is_submonoid.finset_prod_mem IsSubmonoid.finset_prod_mem
#align is_add_submonoid.finset_sum_mem IsAddSubmonoid.finset_sum_mem

end IsSubmonoid

namespace AddMonoid

/-- The inductively defined membership predicate for the submonoid generated by a subset of a
    monoid.-/
inductive InClosure (s : Set A) : A → Prop
  | basic {a : A} : a ∈ s → InClosure _ a
  | zero : InClosure _ 0
  | add {a b : A} : InClosure _ a → InClosure _ b → InClosure _ (a + b)
#align add_monoid.in_closure AddMonoid.InClosure

end AddMonoid

namespace Monoid

/-- The inductively defined membership predicate for the `Submonoid` generated by a subset of an
    monoid. -/
@[to_additive]
inductive InClosure (s : Set M) : M → Prop
  | basic {a : M} : a ∈ s → InClosure _ a
  | one : InClosure _ 1
  | mul {a b : M} : InClosure _ a → InClosure _ b → InClosure _ (a * b)
#align monoid.in_closure Monoid.InClosure

/-- The inductively defined submonoid generated by a subset of a monoid. -/
@[to_additive
      "The inductively defined `AddSubmonoid` generated by a subset of an `AddMonoid`."]
def Closure (s : Set M) : Set M :=
  { a | InClosure s a }
#align monoid.closure Monoid.Closure
#align add_monoid.closure AddMonoid.Closure

@[to_additive]
theorem closure.isSubmonoid (s : Set M) : IsSubmonoid (Closure s) :=
  { one_mem := InClosure.one
    mul_mem := InClosure.mul }
#align monoid.closure.is_submonoid Monoid.closure.isSubmonoid
#align add_monoid.closure.is_add_submonoid AddMonoid.closure.isAddSubmonoid

/-- A subset of a monoid is contained in the submonoid it generates. -/
@[to_additive
    "A subset of an `AddMonoid` is contained in the `AddSubmonoid` it generates."]
theorem subset_closure {s : Set M} : s ⊆ Closure s := fun _ => InClosure.basic
#align monoid.subset_closure Monoid.subset_closure
#align add_monoid.subset_closure AddMonoid.subset_closure

/-- The submonoid generated by a set is contained in any submonoid that contains the set. -/
@[to_additive
      "The `AddSubmonoid` generated by a set is contained in any `AddSubmonoid` that
      contains the set."]
theorem closure_subset {s t : Set M} (ht : IsSubmonoid t) (h : s ⊆ t) : Closure s ⊆ t := fun a ha =>
  by induction ha <;> simp [h _, *, IsSubmonoid.one_mem, IsSubmonoid.mul_mem]
                      -- 🎉 no goals
                      -- 🎉 no goals
                      -- 🎉 no goals
#align monoid.closure_subset Monoid.closure_subset
#align add_monoid.closure_subset AddMonoid.closure_subset

/-- Given subsets `t` and `s` of a monoid `M`, if `s ⊆ t`, the submonoid of `M` generated by `s` is
    contained in the submonoid generated by `t`. -/
@[to_additive
      "Given subsets `t` and `s` of an `AddMonoid M`, if `s ⊆ t`, the `AddSubmonoid`
      of `M` generated by `s` is contained in the `AddSubmonoid` generated by `t`."]
theorem closure_mono {s t : Set M} (h : s ⊆ t) : Closure s ⊆ Closure t :=
  closure_subset (closure.isSubmonoid t) <| Set.Subset.trans h subset_closure
#align monoid.closure_mono Monoid.closure_mono
#align add_monoid.closure_mono AddMonoid.closure_mono

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
@[to_additive
      "The `AddSubmonoid` generated by an element of an `AddMonoid` equals the set of
      natural number multiples of the element."]
theorem closure_singleton {x : M} : Closure ({x} : Set M) = powers x :=
  Set.eq_of_subset_of_subset
      (closure_subset (powers.isSubmonoid x) <| Set.singleton_subset_iff.2 <| powers.self_mem) <|
    IsSubmonoid.power_subset (closure.isSubmonoid _) <|
      Set.singleton_subset_iff.1 <| subset_closure
#align monoid.closure_singleton Monoid.closure_singleton
#align add_monoid.closure_singleton AddMonoid.closure_singleton

/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set under the monoid hom. -/
@[to_additive
      "The image under an `AddMonoid` hom of the `AddSubmonoid` generated by a set equals
      the `AddSubmonoid` generated by the image of the set under the `AddMonoid` hom."]
theorem image_closure {A : Type*} [Monoid A] {f : M → A} (hf : IsMonoidHom f) (s : Set M) :
    f '' Closure s = Closure (f '' s) :=
  le_antisymm
    (by
      rintro _ ⟨x, hx, rfl⟩
      -- ⊢ f x ∈ Closure (f '' s)
      induction' hx with z hz
      · solve_by_elim [subset_closure, Set.mem_image_of_mem]
        -- 🎉 no goals
      · rw [hf.map_one]
        -- ⊢ 1 ∈ Closure (f '' s)
        apply IsSubmonoid.one_mem (closure.isSubmonoid (f '' s))
        -- 🎉 no goals
      · rw [hf.map_mul]
        -- ⊢ f a✝² * f b✝ ∈ Closure (f '' s)
        solve_by_elim [(closure.isSubmonoid _).mul_mem] )
        -- 🎉 no goals
    (closure_subset (IsSubmonoid.image hf (closure.isSubmonoid _)) <|
      Set.image_subset _ subset_closure)
#align monoid.image_closure Monoid.image_closure
#align add_monoid.image_closure AddMonoid.image_closure

/-- Given an element `a` of the submonoid of a monoid `M` generated by a set `s`, there exists
a list of elements of `s` whose product is `a`. -/
@[to_additive
      "Given an element `a` of the `AddSubmonoid` of an `AddMonoid M` generated by
      a set `s`, there exists a list of elements of `s` whose sum is `a`."]
theorem exists_list_of_mem_closure {s : Set M} {a : M} (h : a ∈ Closure s) :
    ∃ l : List M, (∀ x ∈ l, x ∈ s) ∧ l.prod = a := by
  induction h
  case basic a ha => exists [a]; simp [ha]
  -- ⊢ ∃ l, (∀ (x : M), x ∈ l → x ∈ s) ∧ List.prod l = 1
  -- 🎉 no goals
  case one => exists []; simp
  -- ⊢ ∃ l, (∀ (x : M), x ∈ l → x ∈ s) ∧ List.prod l = a✝² * b✝
  -- 🎉 no goals
  case mul a b _ _ ha hb =>
    rcases ha with ⟨la, ha, eqa⟩
    rcases hb with ⟨lb, hb, eqb⟩
    exists la ++ lb
    simp [eqa.symm, eqb.symm, or_imp]
    exact fun a => ⟨ha a, hb a⟩
#align monoid.exists_list_of_mem_closure Monoid.exists_list_of_mem_closure
#align add_monoid.exists_list_of_mem_closure AddMonoid.exists_list_of_mem_closure

/-- Given sets `s, t` of a commutative monoid `M`, `x ∈ M` is in the submonoid of `M` generated by
    `s ∪ t` iff there exists an element of the submonoid generated by `s` and an element of the
    submonoid generated by `t` whose product is `x`. -/
@[to_additive
      "Given sets `s, t` of a commutative `AddMonoid M`, `x ∈ M` is in the `AddSubmonoid`
      of `M` generated by `s ∪ t` iff there exists an element of the `AddSubmonoid` generated by `s`
      and an element of the `AddSubmonoid` generated by `t` whose sum is `x`."]
theorem mem_closure_union_iff {M : Type*} [CommMonoid M] {s t : Set M} {x : M} :
    x ∈ Closure (s ∪ t) ↔ ∃ y ∈ Closure s, ∃ z ∈ Closure t, y * z = x :=
  ⟨fun hx =>
    let ⟨L, HL1, HL2⟩ := exists_list_of_mem_closure hx
    HL2 ▸
      List.recOn L
        (fun _ =>
          ⟨1, (closure.isSubmonoid _).one_mem, 1, (closure.isSubmonoid _).one_mem, mul_one _⟩)
        (fun hd tl ih HL1 =>
          let ⟨y, hy, z, hz, hyzx⟩ := ih (List.forall_mem_of_forall_mem_cons HL1)
          Or.casesOn (HL1 hd <| List.mem_cons_self _ _)
            (fun hs =>
              ⟨hd * y, (closure.isSubmonoid _).mul_mem (subset_closure hs) hy, z, hz, by
                rw [mul_assoc, List.prod_cons, ← hyzx]⟩)
                -- 🎉 no goals
            fun ht =>
            ⟨y, hy, z * hd, (closure.isSubmonoid _).mul_mem hz (subset_closure ht), by
              rw [← mul_assoc, List.prod_cons, ← hyzx, mul_comm hd]⟩)
              -- 🎉 no goals
        HL1,
    fun ⟨y, hy, z, hz, hyzx⟩ =>
    hyzx ▸
      (closure.isSubmonoid _).mul_mem (closure_mono (Set.subset_union_left _ _) hy)
        (closure_mono (Set.subset_union_right _ _) hz)⟩
#align monoid.mem_closure_union_iff Monoid.mem_closure_union_iff
#align add_monoid.mem_closure_union_iff AddMonoid.mem_closure_union_iff

end Monoid

/-- Create a bundled submonoid from a set `s` and `[IsSubmonoid s]`. -/
@[to_additive "Create a bundled additive submonoid from a set `s` and `[IsAddSubmonoid s]`."]
def Submonoid.of {s : Set M} (h : IsSubmonoid s) : Submonoid M :=
  ⟨⟨s, @fun _ _ => h.2⟩, h.1⟩
#align submonoid.of Submonoid.of
#align add_submonoid.of AddSubmonoid.of

@[to_additive]
theorem Submonoid.isSubmonoid (S : Submonoid M) : IsSubmonoid (S : Set M) := by
  refine' ⟨S.2, S.1.2⟩
  -- 🎉 no goals
#align submonoid.is_submonoid Submonoid.isSubmonoid
#align add_submonoid.is_add_submonoid AddSubmonoid.isAddSubmonoid
