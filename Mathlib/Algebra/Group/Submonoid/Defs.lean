/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Tactic.FastInstance
public import Mathlib.Data.Set.Insert

/-!
# Submonoids: definition

This file defines bundled multiplicative and additive submonoids. We also define
a `CompleteLattice` structure on `Submonoid`s, define the closure of a set as the minimal submonoid
that includes this set, and prove a few results about extending properties from a dense set (i.e.
a set with `closure s = ⊤`) to the whole monoid, see `Submonoid.dense_induction` and
`MonoidHom.ofClosureEqTopLeft`/`MonoidHom.ofClosureEqTopRight`.

## Main definitions

* `Submonoid M`: the type of bundled submonoids of a monoid `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : Set M)`.
* `AddSubmonoid M` : the type of bundled submonoids of an additive monoid `M`.

For each of the following definitions in the `Submonoid` namespace, there is a corresponding
definition in the `AddSubmonoid` namespace.

* `Submonoid.copy` : copy of a submonoid with `carrier` replaced by a set that is equal but possibly
  not definitionally equal to the carrier of the original `Submonoid`.
* `MonoidHom.eqLocusM`: the submonoid of elements `x : M` such that `f x = g x`;

## Implementation notes

Submonoid inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a submonoid's underlying set.

Note that `Submonoid M` does not actually require `Monoid M`, instead requiring only the weaker
`MulOneClass M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers. `Submonoid` is implemented by extending `Subsemigroup` requiring `one_mem'`.

## Tags
submonoid, submonoids
-/

@[expose] public section

assert_not_exists RelIso CompleteLattice MonoidWithZero

variable {M : Type*} {N : Type*}

section NonAssoc

variable [MulOneClass M] {s : Set M}

/-- `OneMemClass S M` says `S` is a type of subsets `s ≤ M`, such that `1 ∈ s` for all `s`. -/
class OneMemClass (S : Type*) (M : outParam Type*) [One M] [SetLike S M] : Prop where
  /-- By definition, if we have `OneMemClass S M`, we have `1 ∈ s` for all `s : S`. -/
  one_mem : ∀ s : S, (1 : M) ∈ s

export OneMemClass (one_mem)

/-- `ZeroMemClass S M` says `S` is a type of subsets `s ≤ M`, such that `0 ∈ s` for all `s`. -/
class ZeroMemClass (S : Type*) (M : outParam Type*) [Zero M] [SetLike S M] : Prop where
  /-- By definition, if we have `ZeroMemClass S M`, we have `0 ∈ s` for all `s : S`. -/
  zero_mem : ∀ s : S, (0 : M) ∈ s

export ZeroMemClass (zero_mem)

attribute [to_additive] OneMemClass

attribute [simp, aesop safe (rule_sets := [SetLike])] one_mem zero_mem

section

/-- A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication. -/
structure Submonoid (M : Type*) [MulOneClass M] extends Subsemigroup M where
  /-- A submonoid contains `1`. -/
  one_mem' : (1 : M) ∈ carrier

end

/-- A submonoid of a monoid `M` can be considered as a subsemigroup of that monoid. -/
add_decl_doc Submonoid.toSubsemigroup

/-- `SubmonoidClass S M` says `S` is a type of subsets `s ≤ M` that contain `1`
and are closed under `(*)` -/
class SubmonoidClass (S : Type*) (M : outParam Type*) [MulOneClass M] [SetLike S M] : Prop
    extends MulMemClass S M, OneMemClass S M

section

/-- An additive submonoid of an additive monoid `M` is a subset containing 0 and
  closed under addition. -/
structure AddSubmonoid (M : Type*) [AddZeroClass M] extends AddSubsemigroup M where
  /-- An additive submonoid contains `0`. -/
  zero_mem' : (0 : M) ∈ carrier

end

/-- An additive submonoid of an additive monoid `M` can be considered as an
additive subsemigroup of that additive monoid. -/
add_decl_doc AddSubmonoid.toAddSubsemigroup

/-- `AddSubmonoidClass S M` says `S` is a type of subsets `s ≤ M` that contain `0`
and are closed under `(+)` -/
class AddSubmonoidClass (S : Type*) (M : outParam Type*) [AddZeroClass M] [SetLike S M] : Prop
  extends AddMemClass S M, ZeroMemClass S M

attribute [to_additive] Submonoid SubmonoidClass

@[to_additive (attr := aesop 90% (rule_sets := [SetLike]))]
theorem pow_mem {M A} [Monoid M] [SetLike A M] [SubmonoidClass A M] {S : A} {x : M}
    (hx : x ∈ S) : ∀ n : ℕ, x ^ n ∈ S
  | 0 => by
    rw [pow_zero]
    exact OneMemClass.one_mem S
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem (pow_mem hx n) hx

namespace Submonoid

@[to_additive]
lemma toSubsemigroup_injective : (toSubsemigroup : Submonoid M → Subsemigroup M).Injective :=
  fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ by congr!

@[to_additive (attr := simp)]
lemma toSubsemigroup_inj {s t : Submonoid M} : s.toSubsemigroup = t.toSubsemigroup ↔ s = t :=
  toSubsemigroup_injective.eq_iff

@[to_additive]
instance : SetLike (Submonoid M) M where
  coe s := s.carrier
  coe_injective' := SetLike.coe_injective.comp toSubsemigroup_injective

@[to_additive] instance : PartialOrder (Submonoid M) := .ofSetLike (Submonoid M) M

initialize_simps_projections Submonoid (carrier → coe, as_prefix coe)
initialize_simps_projections AddSubmonoid (carrier → coe, as_prefix coe)

/-- The actual `Submonoid` obtained from an element of a `SubmonoidClass` -/
@[to_additive (attr := simps) /-- The actual `AddSubmonoid` obtained from an element of a
`AddSubmonoidClass` -/]
def ofClass {S M : Type*} [Monoid M] [SetLike S M] [SubmonoidClass S M] (s : S) : Submonoid M :=
  ⟨⟨s, MulMemClass.mul_mem⟩, OneMemClass.one_mem s⟩

@[to_additive]
instance (priority := 100) : CanLift (Set M) (Submonoid M) (↑)
    (fun s ↦ 1 ∈ s ∧ ∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) where
  prf s h := ⟨{ carrier := s, one_mem' := h.1, mul_mem' := h.2 }, rfl⟩

@[to_additive]
instance : SubmonoidClass (Submonoid M) M where
  one_mem := Submonoid.one_mem'
  mul_mem {s} := s.mul_mem'

@[to_additive (attr := simp)]
theorem mem_toSubsemigroup {s : Submonoid M} {x : M} : x ∈ s.toSubsemigroup ↔ x ∈ s :=
  Iff.rfl

@[to_additive]
theorem mem_carrier {s : Submonoid M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[to_additive (attr := simp)]
theorem mem_mk {s : Subsemigroup M} {x : M} (h_one) : x ∈ mk s h_one ↔ x ∈ s :=
  Iff.rfl

@[to_additive (attr := simp)]
theorem coe_set_mk {s : Subsemigroup M} (h_one) : (mk s h_one : Set M) = s :=
  rfl

@[to_additive (attr := simp)]
theorem mk_le_mk {s t : Subsemigroup M} (h_one) (h_one') : mk s h_one ≤ mk t h_one' ↔ s ≤ t :=
  Iff.rfl

/-- Two submonoids are equal if they have the same elements. -/
@[to_additive (attr := ext) /-- Two `AddSubmonoid`s are equal if they have the same elements. -/]
theorem ext {S T : Submonoid M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy a submonoid replacing `carrier` with a set that is equal to it. -/
@[to_additive /-- Copy an additive submonoid replacing `carrier` with a set that is equal to it. -/]
protected def copy (S : Submonoid M) (s : Set M) (hs : s = S) : Submonoid M where
  carrier := s
  one_mem' := show 1 ∈ s from hs.symm ▸ S.one_mem'
  mul_mem' := hs.symm ▸ S.mul_mem'

variable {S : Submonoid M}

@[to_additive (attr := simp, norm_cast)]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl

@[to_additive]
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S)

/-- A submonoid contains the monoid's 1. -/
@[to_additive /-- An `AddSubmonoid` contains the monoid's 0. -/]
protected theorem one_mem : (1 : M) ∈ S :=
  one_mem S

/-- A submonoid is closed under multiplication. -/
@[to_additive /-- An `AddSubmonoid` is closed under addition. -/]
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  mul_mem

/-- The submonoid `M` of the monoid `M`. -/
@[to_additive /-- The additive submonoid `M` of the `AddMonoid M`. -/]
instance : Top (Submonoid M) :=
  ⟨{  carrier := Set.univ
      one_mem' := Set.mem_univ 1
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

/-- The trivial submonoid `{1}` of a monoid `M`. -/
@[to_additive /-- The trivial `AddSubmonoid` `{0}` of an `AddMonoid` `M`. -/]
instance : Bot (Submonoid M) :=
  ⟨{  carrier := {1}
      one_mem' := Set.mem_singleton 1
      mul_mem' := fun ha hb => by
        push _ ∈ _ at *
        rw [ha, hb, mul_one] }⟩

@[to_additive]
instance : Inhabited (Submonoid M) :=
  ⟨⊥⟩

@[to_additive (attr := simp)]
theorem mem_bot {x : M} : x ∈ (⊥ : Submonoid M) ↔ x = 1 :=
  Set.mem_singleton_iff

@[to_additive (attr := simp)]
theorem mem_top (x : M) : x ∈ (⊤ : Submonoid M) :=
  Set.mem_univ x

@[to_additive (attr := simp, norm_cast)]
theorem coe_top : ((⊤ : Submonoid M) : Set M) = Set.univ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_bot : ((⊥ : Submonoid M) : Set M) = {1} :=
  rfl

@[to_additive (attr := simp)]
lemma mk_eq_top (toSubsemigroup : Subsemigroup M) (one_mem') :
    mk toSubsemigroup one_mem' = ⊤ ↔ toSubsemigroup = ⊤ := by simp [← SetLike.coe_set_eq]

@[to_additive (attr := simp)]
lemma mk_eq_bot (toSubsemigroup : Subsemigroup M) (one_mem') :
    mk toSubsemigroup one_mem' = ⊥ ↔ (toSubsemigroup : Set M) = {1} := by
  simp [← SetLike.coe_set_eq]

/-- The inf of two submonoids is their intersection. -/
@[to_additive /-- The inf of two `AddSubmonoid`s is their intersection. -/]
instance : Min (Submonoid M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ ∩ S₂
      one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_inf (p p' : Submonoid M) : ((p ⊓ p' : Submonoid M) : Set M) = (p : Set M) ∩ p' :=
  rfl

@[to_additive (attr := simp, grind =)]
theorem mem_inf {p p' : Submonoid M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

@[to_additive (attr := simp)]
theorem subsingleton_iff : Subsingleton (Submonoid M) ↔ Subsingleton M :=
  ⟨fun _ =>
    ⟨fun x y =>
      have : ∀ i : M, i = 1 := fun i =>
        mem_bot.mp <| Subsingleton.elim (⊤ : Submonoid M) ⊥ ▸ mem_top i
      (this x).trans (this y).symm⟩,
    fun _ ↦ ⟨fun x y ↦ Submonoid.ext fun i ↦ by simp [← Subsingleton.elim 1 i]⟩⟩

@[to_additive (attr := simp)]
theorem nontrivial_iff : Nontrivial (Submonoid M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans subsingleton_iff).trans
      not_nontrivial_iff_subsingleton.symm)

@[to_additive]
instance [Subsingleton M] : Unique (Submonoid M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ (subsingleton_iff.mpr ‹_›) a _⟩

@[to_additive]
instance [Nontrivial M] : Nontrivial (Submonoid M) :=
  nontrivial_iff.mpr ‹_›

end Submonoid

namespace MonoidHom

variable [MulOneClass N]

open Submonoid

/-- The submonoid of elements `x : M` such that `f x = g x` -/
@[to_additive /-- The additive submonoid of elements `x : M` such that `f x = g x` -/]
def eqLocusM (f g : M →* N) : Submonoid M where
  carrier := { x | f x = g x }
  one_mem' := by rw [Set.mem_setOf_eq, f.map_one, g.map_one]
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]

@[to_additive (attr := simp)]
theorem mem_eqLocusM {f g : M →* N} {x : M} : x ∈ f.eqLocusM g ↔ f x = g x := Iff.rfl

@[to_additive (attr := simp)]
theorem eqLocusM_same (f : M →* N) : f.eqLocusM f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

@[to_additive]
theorem eq_of_eqOn_topM {f g : M →* N} (h : Set.EqOn f g (⊤ : Submonoid M)) : f = g :=
  ext fun _ => h trivial

end MonoidHom

end NonAssoc

namespace OneMemClass

variable {A M₁ : Type*} [SetLike A M₁] [One M₁] [hA : OneMemClass A M₁] (S' : A)

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits a zero. -/]
instance one : One S' :=
  ⟨⟨1, OneMemClass.one_mem S'⟩⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_one : ((1 : S') : M₁) = 1 :=
  rfl

variable {S'}

@[to_additive (attr := simp, norm_cast)]
theorem coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1 :=
  (Subtype.ext_iff.symm : (x : M₁) = (1 : S') ↔ x = 1)

variable (S')

@[to_additive]
theorem one_def : (1 : S') = ⟨1, OneMemClass.one_mem S'⟩ :=
  rfl

end OneMemClass

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

namespace SubmonoidClass

/-- A submonoid of a monoid inherits a power operator. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits a scalar multiplication. -/]
instance instPow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] (S : A) : Pow S ℕ :=
  ⟨fun a n => ⟨a.1 ^ n, pow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_pow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : A} (x : S)
    (n : ℕ) : ↑(x ^ n) = (x : M) ^ n :=
  rfl

@[to_additive (attr := simp)]
theorem mk_pow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : A} (x : M)
    (hx : x ∈ S) (n : ℕ) : (⟨x, hx⟩ : S) ^ n = ⟨x ^ n, pow_mem hx n⟩ :=
  rfl

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
  /-- An `AddSubmonoid` of a unital additive magma inherits a unital additive magma structure. -/]
instance (priority := 75) toMulOneClass {M : Type*} [MulOneClass M] {A : Type*} [SetLike A M]
    [SubmonoidClass A M] (S : A) : MulOneClass S := fast_instance%
  Subtype.coe_injective.mulOneClass Subtype.val rfl (fun _ _ => rfl)

instance (S : A) [IsDedekindFiniteMonoid M] : IsDedekindFiniteMonoid S where
  mul_eq_one_symm eq := Subtype.ext (mul_eq_one_symm <| congr_arg (·.1) eq)

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits an `AddMonoid` structure. -/]
instance (priority := 75) toMonoid {M : Type*} [Monoid M] {A : Type*} [SetLike A M]
    [SubmonoidClass A M] (S : A) : Monoid S := fast_instance%
  Subtype.coe_injective.monoid Subtype.val rfl (fun _ _ => rfl) (fun _ _ => rfl)

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a `CommMonoid` is a `CommMonoid`. -/
@[to_additive /-- An `AddSubmonoid` of an `AddCommMonoid` is an `AddCommMonoid`. -/]
instance (priority := 75) toCommMonoid {M} [CommMonoid M] {A : Type*} [SetLike A M]
    [SubmonoidClass A M] (S : A) : CommMonoid S := fast_instance%
  Subtype.coe_injective.commMonoid Subtype.val rfl (fun _ _ => rfl) fun _ _ => rfl

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive /-- The natural monoid hom from an `AddSubmonoid` of `AddMonoid` `M` to `M`. -/]
def subtype : S' →* M where
  toFun := Subtype.val; map_one' := rfl; map_mul' _ _ := by simp

variable {S'} in
@[to_additive (attr := simp)]
lemma subtype_apply (x : S') :
    SubmonoidClass.subtype S' x = x := rfl

@[to_additive]
lemma subtype_injective :
    Function.Injective (SubmonoidClass.subtype S') :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
theorem coe_subtype : (SubmonoidClass.subtype S' : S' → M) = Subtype.val :=
  rfl

end SubmonoidClass

namespace Submonoid

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

/-- A submonoid of a monoid inherits a multiplication. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits an addition. -/]
instance mul : Mul S :=
  ⟨fun a b => ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits a zero. -/]
instance one : One S :=
  ⟨⟨_, S.one_mem⟩⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_one : ((1 : S) : M) = 1 :=
  rfl

@[to_additive (attr := simp)]
lemma mk_eq_one {a : M} {ha} : (⟨a, ha⟩ : S) = 1 ↔ a = 1 := by simp [← SetLike.coe_eq_coe]

@[to_additive (attr := simp)]
theorem mk_mul_mk (x y : M) (hx : x ∈ S) (hy : y ∈ S) :
    (⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, S.mul_mem hx hy⟩ :=
  rfl

@[to_additive]
theorem mul_def (x y : S) : x * y = ⟨x * y, S.mul_mem x.2 y.2⟩ :=
  rfl

@[to_additive]
theorem one_def : (1 : S) = ⟨1, S.one_mem⟩ :=
  rfl

/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
  /-- An `AddSubmonoid` of a unital additive magma inherits a unital additive magma structure. -/]
instance toMulOneClass {M : Type*} [MulOneClass M] (S : Submonoid M) : MulOneClass S :=
  SubmonoidClass.toMulOneClass S

@[to_additive]
protected theorem pow_mem {M : Type*} [Monoid M] (S : Submonoid M) {x : M} (hx : x ∈ S) (n : ℕ) :
    x ^ n ∈ S :=
  pow_mem hx n

/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits an `AddMonoid` structure. -/]
instance toMonoid {M : Type*} [Monoid M] (S : Submonoid M) : Monoid S :=
  SubmonoidClass.toMonoid S

/-- A submonoid of a `CommMonoid` is a `CommMonoid`. -/
@[to_additive /-- An `AddSubmonoid` of an `AddCommMonoid` is an `AddCommMonoid`. -/]
instance toCommMonoid {M} [CommMonoid M] (S : Submonoid M) : CommMonoid S :=
  SubmonoidClass.toCommMonoid S

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive /-- The natural monoid hom from an `AddSubmonoid` of `AddMonoid` `M` to `M`. -/]
def subtype : S →* M where
  toFun := Subtype.val; map_one' := rfl; map_mul' _ _ := by simp

@[to_additive (attr := simp)]
lemma subtype_apply {s : Submonoid M} (x : s) :
    s.subtype x = x := rfl

@[to_additive]
lemma subtype_injective (s : Submonoid M) :
    Function.Injective s.subtype :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
theorem coe_subtype : ⇑S.subtype = Subtype.val :=
  rfl

end Submonoid
