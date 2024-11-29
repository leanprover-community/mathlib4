/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Deprecated.Group

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

/-- `s` is a submonoid: a set containing 1 and closed under multiplication.
Note that this structure is deprecated, and the bundled variant `Submonoid M` should be
preferred. -/
@[to_additive]
structure IsSubmonoid (s : Set M) : Prop where
  /-- The proposition that s contains 1. -/
  one_mem : (1 : M) ∈ s
  /-- The proposition that s is closed under multiplication. -/
  mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s

theorem Additive.isAddSubmonoid {s : Set M} :
    IsSubmonoid s → @IsAddSubmonoid (Additive M) _ s
  | ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩

theorem Additive.isAddSubmonoid_iff {s : Set M} :
    @IsAddSubmonoid (Additive M) _ s ↔ IsSubmonoid s :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩, Additive.isAddSubmonoid⟩

theorem Multiplicative.isSubmonoid {s : Set A} :
    IsAddSubmonoid s → @IsSubmonoid (Multiplicative A) _ s
  | ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩

theorem Multiplicative.isSubmonoid_iff {s : Set A} :
    @IsSubmonoid (Multiplicative A) _ s ↔ IsAddSubmonoid s :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩, Multiplicative.isSubmonoid⟩

/-- The intersection of two submonoids of a monoid `M` is a submonoid of `M`. -/
@[to_additive
      "The intersection of two `AddSubmonoid`s of an `AddMonoid` `M` is an `AddSubmonoid` of M."]
theorem IsSubmonoid.inter {s₁ s₂ : Set M} (is₁ : IsSubmonoid s₁) (is₂ : IsSubmonoid s₂) :
    IsSubmonoid (s₁ ∩ s₂) :=
  { one_mem := ⟨is₁.one_mem, is₂.one_mem⟩
    mul_mem := @fun _ _ hx hy => ⟨is₁.mul_mem hx.1 hy.1, is₂.mul_mem hx.2 hy.2⟩ }

/-- The intersection of an indexed set of submonoids of a monoid `M` is a submonoid of `M`. -/
@[to_additive
      "The intersection of an indexed set of `AddSubmonoid`s of an `AddMonoid` `M` is
      an `AddSubmonoid` of `M`."]
theorem IsSubmonoid.iInter {ι : Sort*} {s : ι → Set M} (h : ∀ y : ι, IsSubmonoid (s y)) :
    IsSubmonoid (Set.iInter s) :=
  { one_mem := Set.mem_iInter.2 fun y => (h y).one_mem
    mul_mem := fun h₁ h₂ =>
      Set.mem_iInter.2 fun y => (h y).mul_mem (Set.mem_iInter.1 h₁ y) (Set.mem_iInter.1 h₂ y) }

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

section powers

/-- The set of natural number powers `1, x, x², ...` of an element `x` of a monoid. -/
@[to_additive
      "The set of natural number multiples `0, x, 2x, ...` of an element `x` of an `AddMonoid`."]
def powers (x : M) : Set M :=
  { y | ∃ n : ℕ, x ^ n = y }

/-- 1 is in the set of natural number powers of an element of a monoid. -/
@[to_additive "0 is in the set of natural number multiples of an element of an `AddMonoid`."]
theorem powers.one_mem {x : M} : (1 : M) ∈ powers x :=
  ⟨0, pow_zero _⟩

/-- An element of a monoid is in the set of that element's natural number powers. -/
@[to_additive
      "An element of an `AddMonoid` is in the set of that element's natural number multiples."]
theorem powers.self_mem {x : M} : x ∈ powers x :=
  ⟨1, pow_one _⟩

/-- The set of natural number powers of an element of a monoid is closed under multiplication. -/
@[to_additive
      "The set of natural number multiples of an element of an `AddMonoid` is closed under
      addition."]
theorem powers.mul_mem {x y z : M} : y ∈ powers x → z ∈ powers x → y * z ∈ powers x :=
  fun ⟨n₁, h₁⟩ ⟨n₂, h₂⟩ => ⟨n₁ + n₂, by simp only [pow_add, *]⟩

/-- The set of natural number powers of an element of a monoid `M` is a submonoid of `M`. -/
@[to_additive
      "The set of natural number multiples of an element of an `AddMonoid` `M` is
      an `AddSubmonoid` of `M`."]
theorem powers.isSubmonoid (x : M) : IsSubmonoid (powers x) :=
  { one_mem := powers.one_mem
    mul_mem := powers.mul_mem }

/-- A monoid is a submonoid of itself. -/
@[to_additive "An `AddMonoid` is an `AddSubmonoid` of itself."]
theorem Univ.isSubmonoid : IsSubmonoid (@Set.univ M) := by constructor <;> simp

/-- The preimage of a submonoid under a monoid hom is a submonoid of the domain. -/
@[to_additive
      "The preimage of an `AddSubmonoid` under an `AddMonoid` hom is
      an `AddSubmonoid` of the domain."]
theorem IsSubmonoid.preimage {N : Type*} [Monoid N] {f : M → N} (hf : IsMonoidHom f) {s : Set N}
    (hs : IsSubmonoid s) : IsSubmonoid (f ⁻¹' s) :=
  { one_mem := show f 1 ∈ s by (rw [IsMonoidHom.map_one hf]; exact hs.one_mem)
    mul_mem := fun {a b} (ha : f a ∈ s) (hb : f b ∈ s) =>
      show f (a * b) ∈ s by (rw [IsMonoidHom.map_mul' hf]; exact hs.mul_mem ha hb) }

/-- The image of a submonoid under a monoid hom is a submonoid of the codomain. -/
@[to_additive
      "The image of an `AddSubmonoid` under an `AddMonoid` hom is an `AddSubmonoid` of the
      codomain."]
theorem IsSubmonoid.image {γ : Type*} [Monoid γ] {f : M → γ} (hf : IsMonoidHom f) {s : Set M}
    (hs : IsSubmonoid s) : IsSubmonoid (f '' s) :=
  { one_mem := ⟨1, hs.one_mem, hf.map_one⟩
    mul_mem := @fun a b ⟨x, hx⟩ ⟨y, hy⟩ =>
      ⟨x * y, hs.mul_mem hx.1 hy.1, by rw [hf.map_mul, hx.2, hy.2]⟩ }

/-- The image of a monoid hom is a submonoid of the codomain. -/
@[to_additive "The image of an `AddMonoid` hom is an `AddSubmonoid` of the codomain."]
theorem Range.isSubmonoid {γ : Type*} [Monoid γ] {f : M → γ} (hf : IsMonoidHom f) :
    IsSubmonoid (Set.range f) := by
  rw [← Set.image_univ]
  exact Univ.isSubmonoid.image hf

/-- Submonoids are closed under natural powers. -/
@[to_additive
      "An `AddSubmonoid` is closed under multiplication by naturals."]
theorem IsSubmonoid.pow_mem {a : M} (hs : IsSubmonoid s) (h : a ∈ s) : ∀ {n : ℕ}, a ^ n ∈ s
  | 0 => by
    rw [pow_zero]
    exact hs.one_mem
  | n + 1 => by
    rw [pow_succ]
    exact hs.mul_mem (IsSubmonoid.pow_mem hs h) h

/-- The set of natural number powers of an element of a `Submonoid` is a subset of the
`Submonoid`. -/
@[to_additive
      "The set of natural number multiples of an element of an `AddSubmonoid` is a subset of
      the `AddSubmonoid`."]
theorem IsSubmonoid.powers_subset {a : M} (hs : IsSubmonoid s) (h : a ∈ s) : powers a ⊆ s :=
  fun _ ⟨_, hx⟩ => hx ▸ hs.pow_mem h
@[deprecated (since := "2024-02-21")] alias IsSubmonoid.power_subset := IsSubmonoid.powers_subset

end powers

namespace IsSubmonoid

/-- The product of a list of elements of a submonoid is an element of the submonoid. -/
@[to_additive
      "The sum of a list of elements of an `AddSubmonoid` is an element of the `AddSubmonoid`."]
theorem list_prod_mem (hs : IsSubmonoid s) : ∀ {l : List M}, (∀ x ∈ l, x ∈ s) → l.prod ∈ s
  | [], _ => hs.one_mem
  | a :: l, h =>
    suffices a * l.prod ∈ s by simpa
    have : a ∈ s ∧ ∀ x ∈ l, x ∈ s := by simpa using h
    hs.mul_mem this.1 (list_prod_mem hs this.2)

/-- The product of a multiset of elements of a submonoid of a `CommMonoid` is an element of
the submonoid. -/
@[to_additive
      "The sum of a multiset of elements of an `AddSubmonoid` of an `AddCommMonoid`
      is an element of the `AddSubmonoid`. "]
theorem multiset_prod_mem {M} [CommMonoid M] {s : Set M} (hs : IsSubmonoid s) (m : Multiset M) :
    (∀ a ∈ m, a ∈ s) → m.prod ∈ s := by
  refine Quotient.inductionOn m fun l hl => ?_
  rw [Multiset.quot_mk_to_coe, Multiset.prod_coe]
  exact list_prod_mem hs hl

/-- The product of elements of a submonoid of a `CommMonoid` indexed by a `Finset` is an element
of the submonoid. -/
@[to_additive
      "The sum of elements of an `AddSubmonoid` of an `AddCommMonoid` indexed by
      a `Finset` is an element of the `AddSubmonoid`."]
theorem finset_prod_mem {M A} [CommMonoid M] {s : Set M} (hs : IsSubmonoid s) (f : A → M) :
    ∀ t : Finset A, (∀ b ∈ t, f b ∈ s) → (∏ b ∈ t, f b) ∈ s
  | ⟨m, hm⟩, _ => multiset_prod_mem hs _ (by simpa)

end IsSubmonoid

namespace AddMonoid

/-- The inductively defined membership predicate for the submonoid generated by a subset of a
    monoid. -/
inductive InClosure (s : Set A) : A → Prop
  | basic {a : A} : a ∈ s → InClosure _ a
  | zero : InClosure _ 0
  | add {a b : A} : InClosure _ a → InClosure _ b → InClosure _ (a + b)

end AddMonoid

namespace Monoid

/-- The inductively defined membership predicate for the `Submonoid` generated by a subset of an
    monoid. -/
@[to_additive]
inductive InClosure (s : Set M) : M → Prop
  | basic {a : M} : a ∈ s → InClosure _ a
  | one : InClosure _ 1
  | mul {a b : M} : InClosure _ a → InClosure _ b → InClosure _ (a * b)

/-- The inductively defined submonoid generated by a subset of a monoid. -/
@[to_additive
      "The inductively defined `AddSubmonoid` generated by a subset of an `AddMonoid`."]
def Closure (s : Set M) : Set M :=
  { a | InClosure s a }

@[to_additive]
theorem closure.isSubmonoid (s : Set M) : IsSubmonoid (Closure s) :=
  { one_mem := InClosure.one
    mul_mem := InClosure.mul }

/-- A subset of a monoid is contained in the submonoid it generates. -/
@[to_additive
    "A subset of an `AddMonoid` is contained in the `AddSubmonoid` it generates."]
theorem subset_closure {s : Set M} : s ⊆ Closure s := fun _ => InClosure.basic

/-- The submonoid generated by a set is contained in any submonoid that contains the set. -/
@[to_additive
      "The `AddSubmonoid` generated by a set is contained in any `AddSubmonoid` that
      contains the set."]
theorem closure_subset {s t : Set M} (ht : IsSubmonoid t) (h : s ⊆ t) : Closure s ⊆ t := fun a ha =>
  by induction ha <;> simp [h _, *, IsSubmonoid.one_mem, IsSubmonoid.mul_mem]

/-- Given subsets `t` and `s` of a monoid `M`, if `s ⊆ t`, the submonoid of `M` generated by `s` is
    contained in the submonoid generated by `t`. -/
@[to_additive
      "Given subsets `t` and `s` of an `AddMonoid M`, if `s ⊆ t`, the `AddSubmonoid`
      of `M` generated by `s` is contained in the `AddSubmonoid` generated by `t`."]
theorem closure_mono {s t : Set M} (h : s ⊆ t) : Closure s ⊆ Closure t :=
  closure_subset (closure.isSubmonoid t) <| Set.Subset.trans h subset_closure

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
@[to_additive
      "The `AddSubmonoid` generated by an element of an `AddMonoid` equals the set of
      natural number multiples of the element."]
theorem closure_singleton {x : M} : Closure ({x} : Set M) = powers x :=
  Set.eq_of_subset_of_subset
      (closure_subset (powers.isSubmonoid x) <| Set.singleton_subset_iff.2 <| powers.self_mem) <|
    IsSubmonoid.powers_subset (closure.isSubmonoid _) <|
      Set.singleton_subset_iff.1 <| subset_closure

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
      induction' hx with z hz
      · solve_by_elim [subset_closure, Set.mem_image_of_mem]
      · rw [hf.map_one]
        apply IsSubmonoid.one_mem (closure.isSubmonoid (f '' s))
      · rw [hf.map_mul]
        solve_by_elim [(closure.isSubmonoid _).mul_mem] )
    (closure_subset (IsSubmonoid.image hf (closure.isSubmonoid _)) <|
      Set.image_subset _ subset_closure)

/-- Given an element `a` of the submonoid of a monoid `M` generated by a set `s`, there exists
a list of elements of `s` whose product is `a`. -/
@[to_additive
      "Given an element `a` of the `AddSubmonoid` of an `AddMonoid M` generated by
      a set `s`, there exists a list of elements of `s` whose sum is `a`."]
theorem exists_list_of_mem_closure {s : Set M} {a : M} (h : a ∈ Closure s) :
    ∃ l : List M, (∀ x ∈ l, x ∈ s) ∧ l.prod = a := by
  induction h with
  | @basic a ha => exists [a]; simp [ha]
  | one => exists []; simp
  | mul _ _ ha hb =>
    rcases ha with ⟨la, ha, eqa⟩
    rcases hb with ⟨lb, hb, eqb⟩
    exists la ++ lb
    simp only [List.mem_append, or_imp, List.prod_append, eqa.symm, eqb.symm, and_true]
    exact fun a => ⟨ha a, hb a⟩

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
            fun ht =>
            ⟨y, hy, z * hd, (closure.isSubmonoid _).mul_mem hz (subset_closure ht), by
              rw [← mul_assoc, List.prod_cons, ← hyzx, mul_comm hd]⟩)
        HL1,
    fun ⟨_, hy, _, hz, hyzx⟩ =>
    hyzx ▸
      (closure.isSubmonoid _).mul_mem (closure_mono Set.subset_union_left hy)
        (closure_mono Set.subset_union_right hz)⟩

end Monoid

/-- Create a bundled submonoid from a set `s` and `[IsSubmonoid s]`. -/
@[to_additive "Create a bundled additive submonoid from a set `s` and `[IsAddSubmonoid s]`."]
def Submonoid.of {s : Set M} (h : IsSubmonoid s) : Submonoid M :=
  ⟨⟨s, @fun _ _ => h.2⟩, h.1⟩

@[to_additive]
theorem Submonoid.isSubmonoid (S : Submonoid M) : IsSubmonoid (S : Set M) := by
  exact ⟨S.2, S.1.2⟩
