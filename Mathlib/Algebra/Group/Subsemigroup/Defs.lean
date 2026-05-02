/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Tactic.FastInstance

/-!
# Subsemigroups: definition

This file defines bundled multiplicative and additive subsemigroups.

## Main definitions

* `Subsemigroup M`: the type of bundled subsemigroup of a magma `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : Set M)`.
* `AddSubsemigroup M` : the type of bundled subsemigroups of an additive magma `M`.

For each of the following definitions in the `Subsemigroup` namespace, there is a corresponding
definition in the `AddSubsemigroup` namespace.

* `Subsemigroup.copy` : copy of a subsemigroup with `carrier` replaced by a set that is equal but
  possibly not definitionally equal to the carrier of the original `Subsemigroup`.

Similarly, for each of these definitions in the `MulHom` namespace, there is a corresponding
definition in the `AddHom` namespace.

* `MulHom.eqLocus f g`: the subsemigroup of those `x` such that `f x = g x`

## Implementation notes

Subsemigroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subsemigroup's underlying set.

Note that `Subsemigroup M` does not actually require `Semigroup M`,
instead requiring only the weaker `Mul M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers.

## Tags
subsemigroup, subsemigroups
-/

@[expose] public section

assert_not_exists RelIso CompleteLattice MonoidWithZero

variable {M : Type*} {N : Type*}

section NonAssoc

variable [Mul M] {s : Set M}

/-- `MulMemClass S M` says `S` is a type of sets `s : Set M` that are closed under `(*)` -/
class MulMemClass (S : Type*) (M : outParam Type*) [Mul M] [SetLike S M] : Prop where
  /-- A substructure satisfying `MulMemClass` is closed under multiplication. -/
  mul_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a * b ∈ s

export MulMemClass (mul_mem)

/-- `AddMemClass S M` says `S` is a type of sets `s : Set M` that are closed under `(+)` -/
class AddMemClass (S : Type*) (M : outParam Type*) [Add M] [SetLike S M] : Prop where
  /-- A substructure satisfying `AddMemClass` is closed under addition. -/
  add_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a + b ∈ s

export AddMemClass (add_mem)

attribute [to_additive] MulMemClass

attribute [aesop 90% (rule_sets := [SetLike])] mul_mem add_mem

/-- A subsemigroup of a magma `M` is a subset closed under multiplication. -/
structure Subsemigroup (M : Type*) [Mul M] where
  /-- The carrier of a subsemigroup. -/
  carrier : Set M
  /-- The product of two elements of a subsemigroup belongs to the subsemigroup. -/
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier

/-- An additive subsemigroup of an additive magma `M` is a subset closed under addition. -/
structure AddSubsemigroup (M : Type*) [Add M] where
  /-- The carrier of an additive subsemigroup. -/
  carrier : Set M
  /-- The sum of two elements of an additive subsemigroup belongs to the subsemigroup. -/
  add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier

attribute [to_additive AddSubsemigroup] Subsemigroup

namespace Subsemigroup

@[to_additive]
instance : SetLike (Subsemigroup M) M :=
  ⟨Subsemigroup.carrier, fun p q h => by cases p; cases q; congr⟩

@[to_additive] instance : PartialOrder (Subsemigroup M) := .ofSetLike (Subsemigroup M) M

initialize_simps_projections Subsemigroup (carrier → coe, as_prefix coe)
initialize_simps_projections AddSubsemigroup (carrier → coe, as_prefix coe)

/-- The actual `Subsemigroup` obtained from an element of a `MulMemClass`. -/
@[to_additive (attr := simps) /-- The actual `AddSubsemigroup` obtained from an element of a
`AddMemClass` -/]
def ofClass {S M : Type*} [Mul M] [SetLike S M] [MulMemClass S M] (s : S) : Subsemigroup M :=
  ⟨s, MulMemClass.mul_mem⟩

@[to_additive]
instance (priority := 100) : CanLift (Set M) (Subsemigroup M) (↑)
    (fun s ↦ ∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) where
  prf s h := ⟨{ carrier := s, mul_mem' := h }, rfl⟩

@[to_additive]
instance : MulMemClass (Subsemigroup M) M where mul_mem := fun {_ _ _} => Subsemigroup.mul_mem' _

@[to_additive (attr := simp)]
theorem mem_carrier {s : Subsemigroup M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[to_additive (attr := simp)]
theorem mem_mk {s : Set M} {x : M} (h_mul) : x ∈ mk s h_mul ↔ x ∈ s :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_set_mk (s : Set M) (h_mul) : (mk s h_mul : Set M) = s :=
  rfl

@[to_additive (attr := simp)]
theorem mk_le_mk {s t : Set M} (h_mul) (h_mul') : mk s h_mul ≤ mk t h_mul' ↔ s ⊆ t :=
  Iff.rfl

/-- Two subsemigroups are equal if they have the same elements. -/
@[to_additive (attr := ext) /-- Two `AddSubsemigroup`s are equal if they have the same elements. -/]
theorem ext {S T : Subsemigroup M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy a subsemigroup replacing `carrier` with a set that is equal to it. -/
@[to_additive
/-- Copy an additive subsemigroup replacing `carrier` with a set that is equal to it. -/]
protected def copy (S : Subsemigroup M) (s : Set M) (hs : s = S) :
    Subsemigroup M where
  carrier := s
  mul_mem' := hs.symm ▸ S.mul_mem'

variable {S : Subsemigroup M}

@[to_additive (attr := simp, norm_cast)]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl

@[to_additive]
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S)

/-- A subsemigroup is closed under multiplication. -/
@[to_additive /-- An `AddSubsemigroup` is closed under addition. -/]
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  Subsemigroup.mul_mem' S

/-- The subsemigroup `M` of the magma `M`. -/
@[to_additive /-- The additive subsemigroup `M` of the magma `M`. -/]
instance : Top (Subsemigroup M) :=
  ⟨{  carrier := Set.univ
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

/-- The trivial subsemigroup `∅` of a magma `M`. -/
@[to_additive /-- The trivial `AddSubsemigroup` `∅` of an additive magma `M`. -/]
instance : Bot (Subsemigroup M) :=
  ⟨{  carrier := ∅
      mul_mem' := False.elim }⟩

@[to_additive]
instance : Inhabited (Subsemigroup M) :=
  ⟨⊥⟩

@[to_additive]
theorem notMem_bot {x : M} : x ∉ (⊥ : Subsemigroup M) :=
  Set.notMem_empty x

@[to_additive (attr := simp)]
theorem mem_top (x : M) : x ∈ (⊤ : Subsemigroup M) :=
  Set.mem_univ x

@[to_additive (attr := simp, norm_cast)]
theorem coe_top : ((⊤ : Subsemigroup M) : Set M) = Set.univ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_bot : ((⊥ : Subsemigroup M) : Set M) = ∅ :=
  rfl

@[to_additive (attr := simp)]
lemma mk_eq_top (carrier : Set M) (mul_mem') : mk carrier mul_mem' = ⊤ ↔ carrier = .univ := by
  simp [← SetLike.coe_set_eq]

@[to_additive (attr := simp)]
lemma mk_eq_bot (carrier : Set M) (mul_mem') : mk carrier mul_mem' = ⊥ ↔ carrier = ∅ := by
  simp [← SetLike.coe_set_eq]

/-- The inf of two subsemigroups is their intersection. -/
@[to_additive /-- The inf of two `AddSubsemigroup`s is their intersection. -/]
instance : Min (Subsemigroup M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ ∩ S₂
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_inf (p p' : Subsemigroup M) : ((p ⊓ p' : Subsemigroup M) : Set M) = (p : Set M) ∩ p' :=
  rfl

@[to_additive (attr := simp)]
theorem mem_inf {p p' : Subsemigroup M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

@[to_additive]
theorem subsingleton_of_subsingleton [Subsingleton (Subsemigroup M)] : Subsingleton M := by
  constructor; intro x y
  have : ∀ a : M, a ∈ (⊥ : Subsemigroup M) := by simp [Subsingleton.elim (⊥ : Subsemigroup M) ⊤]
  exact absurd (this x) notMem_bot

@[to_additive]
instance [hn : Nonempty M] : Nontrivial (Subsemigroup M) :=
  ⟨⟨⊥, ⊤, fun h => by
      obtain ⟨x⟩ := id hn
      refine absurd (?_ : x ∈ ⊥) notMem_bot
      simp [h]⟩⟩

end Subsemigroup

namespace MulHom

variable [Mul N]

open Subsemigroup

/-- The subsemigroup of elements `x : M` such that `f x = g x` -/
@[to_additive /-- The additive subsemigroup of elements `x : M` such that `f x = g x` -/]
def eqLocus (f g : M →ₙ* N) : Subsemigroup M where
  carrier := { x | f x = g x }
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]

@[to_additive (attr := simp)]
theorem mem_eqLocus {f g : M →ₙ* N} {x : M} : x ∈ f.eqLocus g ↔ f x = g x := Iff.rfl

@[to_additive]
theorem eq_of_eqOn_top {f g : M →ₙ* N} (h : Set.EqOn f g (⊤ : Subsemigroup M)) : f = g :=
  ext fun _ => h trivial

end MulHom

end NonAssoc

namespace MulMemClass

variable {A : Type*} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

-- lower priority so other instances are found first
/-- A submagma of a magma inherits a multiplication. -/
@[to_additive /-- An additive submagma of an additive magma inherits an addition. -/]
instance (priority := 900) mul : Mul S' :=
  ⟨fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩⟩

-- lower priority so later simp lemmas are used first; to appease simp_nf
@[to_additive (attr := simp low, norm_cast)]
theorem coe_mul (x y : S') : (↑(x * y) : M) = ↑x * ↑y :=
  rfl

-- lower priority so later simp lemmas are used first; to appease simp_nf
@[to_additive (attr := simp low)]
theorem mk_mul_mk (x y : M) (hx : x ∈ S') (hy : y ∈ S') :
    (⟨x, hx⟩ : S') * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ :=
  rfl

@[to_additive]
theorem mul_def (x y : S') : x * y = ⟨x * y, mul_mem x.2 y.2⟩ :=
  rfl

/-- A subsemigroup of a semigroup inherits a semigroup structure. -/
@[to_additive
/-- An `AddSubsemigroup` of an `AddSemigroup` inherits an `AddSemigroup` structure. -/]
instance toSemigroup {M : Type*} [Semigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
    (S : A) : Semigroup S := fast_instance%
  Subtype.coe_injective.semigroup Subtype.val fun _ _ => rfl

/-- A subsemigroup of a `CommSemigroup` is a `CommSemigroup`. -/
@[to_additive /-- An `AddSubsemigroup` of an `AddCommSemigroup` is an `AddCommSemigroup`. -/]
instance toCommSemigroup {M} [CommSemigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
    (S : A) : CommSemigroup S := fast_instance%
  Subtype.coe_injective.commSemigroup Subtype.val fun _ _ => rfl

/-- A submagma of a left cancellative magma inherits left cancellation. -/
@[to_additive
/-- An additive submagma of a left cancellative additive magma inherits left cancellation. -/]
instance isLeftCancelMul [IsLeftCancelMul M] (S : A) : IsLeftCancelMul S :=
  Subtype.coe_injective.isLeftCancelMul Subtype.val fun _ _ => rfl

/-- A submagma of a right cancellative magma inherits right cancellation. -/
@[to_additive
/-- An additive submagma of a right cancellative additive magma inherits right cancellation. -/]
instance isRightCancelMul [IsRightCancelMul M] (S : A) : IsRightCancelMul S :=
  Subtype.coe_injective.isRightCancelMul Subtype.val fun _ _ => rfl

/-- A submagma of a cancellative magma inherits cancellation. -/
@[to_additive /-- An additive submagma of a cancellative additive magma inherits cancellation. -/]
instance isCancelMul [IsCancelMul M] (S : A) : IsCancelMul S where

/-- The natural semigroup hom from a subsemigroup of semigroup `M` to `M`. -/
@[to_additive /-- The natural semigroup hom from an `AddSubsemigroup` of
`AddSubsemigroup` `M` to `M`. -/]
def subtype : S' →ₙ* M where
  toFun := Subtype.val; map_mul' := fun _ _ => rfl

variable {S'} in
@[to_additive (attr := simp)]
lemma subtype_apply (x : S') :
    MulMemClass.subtype S' x = x := rfl

@[to_additive]
lemma subtype_injective :
    Function.Injective (MulMemClass.subtype S') :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
theorem coe_subtype : (MulMemClass.subtype S' : S' → M) = Subtype.val :=
  rfl

end MulMemClass

@[to_additive]
lemma isMulCommutative_iff_of_setLike {S M : Type*} [SetLike S M] [Mul M] [MulMemClass S M]
    {s : S} : IsMulCommutative s ↔ ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
  simp [isMulCommutative_iff]

@[to_additive]
alias ⟨_, IsMulCommutative.of_setLike_mul_comm⟩ := isMulCommutative_iff_of_setLike

/-- Commutativity of multiplication in commutative subobjects. -/
@[to_additive /-- Commutativity of addition in commutative subobjects. -/ ]
lemma setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [MulMemClass S M]
    {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a ∈ s) (hb : b ∈ s) :
    a * b = b * a :=
  isMulCommutative_iff_of_setLike.mp ‹_› a ha b hb
