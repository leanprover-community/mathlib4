/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Set.Lattice
import Mathlib.Data.SetLike.Basic

#align_import group_theory.subsemigroup.basic from "leanprover-community/mathlib"@"feb99064803fd3108e37c18b0f77d0a8344677a3"

/-!
# Subsemigroups: definition and `CompleteLattice` structure

This file defines bundled multiplicative and additive subsemigroups. We also define
a `CompleteLattice` structure on `Subsemigroup`s,
and define the closure of a set as the minimal subsemigroup that includes this set.

## Main definitions

* `Subsemigroup M`: the type of bundled subsemigroup of a magma `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : Set M)`.
* `AddSubsemigroup M` : the type of bundled subsemigroups of an additive magma `M`.

For each of the following definitions in the `Subsemigroup` namespace, there is a corresponding
definition in the `AddSubsemigroup` namespace.

* `Subsemigroup.copy` : copy of a subsemigroup with `carrier` replaced by a set that is equal but
  possibly not definitionally equal to the carrier of the original `Subsemigroup`.
* `Subsemigroup.closure` :  semigroup closure of a set, i.e.,
  the least subsemigroup that includes the set.
* `Subsemigroup.gi` : `closure : Set M → Subsemigroup M` and coercion `coe : Subsemigroup M → Set M`
  form a `GaloisInsertion`;

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

assert_not_exists MonoidWithZero

-- Only needed for notation
variable {M : Type*} {N : Type*} {A : Type*}

section NonAssoc

variable [Mul M] {s : Set M}
variable [Add A] {t : Set A}

/-- `MulMemClass S M` says `S` is a type of sets `s : Set M` that are closed under `(*)` -/
class MulMemClass (S : Type*) (M : Type*) [Mul M] [SetLike S M] : Prop where
  /-- A substructure satisfying `MulMemClass` is closed under multiplication. -/
  mul_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
#align mul_mem_class MulMemClass

export MulMemClass (mul_mem)

/-- `AddMemClass S M` says `S` is a type of sets `s : Set M` that are closed under `(+)` -/
class AddMemClass (S : Type*) (M : Type*) [Add M] [SetLike S M] : Prop where
  /-- A substructure satisfying `AddMemClass` is closed under addition. -/
  add_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a + b ∈ s
#align add_mem_class AddMemClass

export AddMemClass (add_mem)

attribute [to_additive] MulMemClass

attribute [aesop safe apply (rule_sets := [SetLike])] mul_mem add_mem

/-- A subsemigroup of a magma `M` is a subset closed under multiplication. -/
structure Subsemigroup (M : Type*) [Mul M] where
  /-- The carrier of a subsemigroup. -/
  carrier : Set M
  /-- The product of two elements of a subsemigroup belongs to the subsemigroup. -/
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
#align subsemigroup Subsemigroup

/-- An additive subsemigroup of an additive magma `M` is a subset closed under addition. -/
structure AddSubsemigroup (M : Type*) [Add M] where
  /-- The carrier of an additive subsemigroup. -/
  carrier : Set M
  /-- The sum of two elements of an additive subsemigroup belongs to the subsemigroup. -/
  add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier
#align add_subsemigroup AddSubsemigroup

attribute [to_additive AddSubsemigroup] Subsemigroup

namespace Subsemigroup

@[to_additive]
instance : SetLike (Subsemigroup M) M :=
  ⟨Subsemigroup.carrier, fun p q h => by cases p; cases q; congr⟩

@[to_additive]
instance : MulMemClass (Subsemigroup M) M where mul_mem := fun {_ _ _} => Subsemigroup.mul_mem' _

initialize_simps_projections Subsemigroup (carrier → coe)
initialize_simps_projections AddSubsemigroup (carrier → coe)

@[to_additive (attr := simp)]
theorem mem_carrier {s : Subsemigroup M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align subsemigroup.mem_carrier Subsemigroup.mem_carrier
#align add_subsemigroup.mem_carrier AddSubsemigroup.mem_carrier

@[to_additive (attr := simp)]
theorem mem_mk {s : Set M} {x : M} (h_mul) : x ∈ mk s h_mul ↔ x ∈ s :=
  Iff.rfl
#align subsemigroup.mem_mk Subsemigroup.mem_mk
#align add_subsemigroup.mem_mk AddSubsemigroup.mem_mk

@[to_additive (attr := simp, norm_cast)]
theorem coe_set_mk {s : Set M} (h_mul) : (mk s h_mul : Set M) = s :=
  rfl
#align subsemigroup.coe_set_mk Subsemigroup.coe_set_mk
#align add_subsemigroup.coe_set_mk AddSubsemigroup.coe_set_mk

@[to_additive (attr := simp)]
theorem mk_le_mk {s t : Set M} (h_mul) (h_mul') : mk s h_mul ≤ mk t h_mul' ↔ s ⊆ t :=
  Iff.rfl
#align subsemigroup.mk_le_mk Subsemigroup.mk_le_mk
#align add_subsemigroup.mk_le_mk AddSubsemigroup.mk_le_mk

/-- Two subsemigroups are equal if they have the same elements. -/
@[to_additive (attr := ext) "Two `AddSubsemigroup`s are equal if they have the same elements."]
theorem ext {S T : Subsemigroup M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align subsemigroup.ext Subsemigroup.ext
#align add_subsemigroup.ext AddSubsemigroup.ext

/-- Copy a subsemigroup replacing `carrier` with a set that is equal to it. -/
@[to_additive "Copy an additive subsemigroup replacing `carrier` with a set that is equal to it."]
protected def copy (S : Subsemigroup M) (s : Set M) (hs : s = S) :
    Subsemigroup M where
  carrier := s
  mul_mem' := hs.symm ▸ S.mul_mem'
#align subsemigroup.copy Subsemigroup.copy
#align add_subsemigroup.copy AddSubsemigroup.copy

variable {S : Subsemigroup M}

@[to_additive (attr := simp)]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl
#align subsemigroup.coe_copy Subsemigroup.coe_copy
#align add_subsemigroup.coe_copy AddSubsemigroup.coe_copy

@[to_additive]
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align subsemigroup.copy_eq Subsemigroup.copy_eq
#align add_subsemigroup.copy_eq AddSubsemigroup.copy_eq

variable (S)

/-- A subsemigroup is closed under multiplication. -/
@[to_additive "An `AddSubsemigroup` is closed under addition."]
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  Subsemigroup.mul_mem' S
#align subsemigroup.mul_mem Subsemigroup.mul_mem
#align add_subsemigroup.add_mem AddSubsemigroup.add_mem

/-- The subsemigroup `M` of the magma `M`. -/
@[to_additive "The additive subsemigroup `M` of the magma `M`."]
instance : Top (Subsemigroup M) :=
  ⟨{  carrier := Set.univ
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

/-- The trivial subsemigroup `∅` of a magma `M`. -/
@[to_additive "The trivial `AddSubsemigroup` `∅` of an additive magma `M`."]
instance : Bot (Subsemigroup M) :=
  ⟨{  carrier := ∅
      mul_mem' := False.elim }⟩

@[to_additive]
instance : Inhabited (Subsemigroup M) :=
  ⟨⊥⟩

@[to_additive]
theorem not_mem_bot {x : M} : x ∉ (⊥ : Subsemigroup M) :=
  Set.not_mem_empty x
#align subsemigroup.not_mem_bot Subsemigroup.not_mem_bot
#align add_subsemigroup.not_mem_bot AddSubsemigroup.not_mem_bot

@[to_additive (attr := simp)]
theorem mem_top (x : M) : x ∈ (⊤ : Subsemigroup M) :=
  Set.mem_univ x
#align subsemigroup.mem_top Subsemigroup.mem_top
#align add_subsemigroup.mem_top AddSubsemigroup.mem_top

@[to_additive (attr := simp)]
theorem coe_top : ((⊤ : Subsemigroup M) : Set M) = Set.univ :=
  rfl
#align subsemigroup.coe_top Subsemigroup.coe_top
#align add_subsemigroup.coe_top AddSubsemigroup.coe_top

@[to_additive (attr := simp)]
theorem coe_bot : ((⊥ : Subsemigroup M) : Set M) = ∅ :=
  rfl
#align subsemigroup.coe_bot Subsemigroup.coe_bot
#align add_subsemigroup.coe_bot AddSubsemigroup.coe_bot

/-- The inf of two subsemigroups is their intersection. -/
@[to_additive "The inf of two `AddSubsemigroup`s is their intersection."]
instance : Inf (Subsemigroup M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ ∩ S₂
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[to_additive (attr := simp)]
theorem coe_inf (p p' : Subsemigroup M) : ((p ⊓ p' : Subsemigroup M) : Set M) = (p : Set M) ∩ p' :=
  rfl
#align subsemigroup.coe_inf Subsemigroup.coe_inf
#align add_subsemigroup.coe_inf AddSubsemigroup.coe_inf

@[to_additive (attr := simp)]
theorem mem_inf {p p' : Subsemigroup M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
#align subsemigroup.mem_inf Subsemigroup.mem_inf
#align add_subsemigroup.mem_inf AddSubsemigroup.mem_inf

@[to_additive]
instance : InfSet (Subsemigroup M) :=
  ⟨fun s =>
    { carrier := ⋂ t ∈ s, ↑t
      mul_mem' := fun hx hy =>
        Set.mem_biInter fun i h =>
          i.mul_mem (by apply Set.mem_iInter₂.1 hx i h) (by apply Set.mem_iInter₂.1 hy i h) }⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_sInf (S : Set (Subsemigroup M)) : ((sInf S : Subsemigroup M) : Set M) = ⋂ s ∈ S, ↑s :=
  rfl
#align subsemigroup.coe_Inf Subsemigroup.coe_sInf
#align add_subsemigroup.coe_Inf AddSubsemigroup.coe_sInf

@[to_additive]
theorem mem_sInf {S : Set (Subsemigroup M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂
#align subsemigroup.mem_Inf Subsemigroup.mem_sInf
#align add_subsemigroup.mem_Inf AddSubsemigroup.mem_sInf

@[to_additive]
theorem mem_iInf {ι : Sort*} {S : ι → Subsemigroup M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]
#align subsemigroup.mem_infi Subsemigroup.mem_iInf
#align add_subsemigroup.mem_infi AddSubsemigroup.mem_iInf

@[to_additive (attr := simp, norm_cast)]
theorem coe_iInf {ι : Sort*} {S : ι → Subsemigroup M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]
#align subsemigroup.coe_infi Subsemigroup.coe_iInf
#align add_subsemigroup.coe_infi AddSubsemigroup.coe_iInf

/-- subsemigroups of a monoid form a complete lattice. -/
@[to_additive "The `AddSubsemigroup`s of an `AddMonoid` form a complete lattice."]
instance : CompleteLattice (Subsemigroup M) :=
  { completeLatticeOfInf (Subsemigroup M) fun _ =>
      IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun _ _ hx => (not_mem_bot hx).elim
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _ _ _ ha hb _ hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

@[to_additive]
theorem subsingleton_of_subsingleton [Subsingleton (Subsemigroup M)] : Subsingleton M := by
  constructor; intro x y
  have : ∀ a : M, a ∈ (⊥ : Subsemigroup M) := by simp [Subsingleton.elim (⊥ : Subsemigroup M) ⊤]
  exact absurd (this x) not_mem_bot
#align subsemigroup.subsingleton_of_subsingleton Subsemigroup.subsingleton_of_subsingleton
#align add_subsemigroup.subsingleton_of_subsingleton AddSubsemigroup.subsingleton_of_subsingleton

@[to_additive]
instance [hn : Nonempty M] : Nontrivial (Subsemigroup M) :=
  ⟨⟨⊥, ⊤, fun h => by
      obtain ⟨x⟩ := id hn
      refine absurd (?_ : x ∈ ⊥) not_mem_bot
      simp [h]⟩⟩

/-- The `Subsemigroup` generated by a set. -/
@[to_additive "The `AddSubsemigroup` generated by a set"]
def closure (s : Set M) : Subsemigroup M :=
  sInf { S | s ⊆ S }
#align subsemigroup.closure Subsemigroup.closure
#align add_subsemigroup.closure AddSubsemigroup.closure

@[to_additive]
theorem mem_closure {x : M} : x ∈ closure s ↔ ∀ S : Subsemigroup M, s ⊆ S → x ∈ S :=
  mem_sInf
#align subsemigroup.mem_closure Subsemigroup.mem_closure
#align add_subsemigroup.mem_closure AddSubsemigroup.mem_closure

/-- The subsemigroup generated by a set includes the set. -/
@[to_additive (attr := simp, aesop safe 20 apply (rule_sets := [SetLike]))
  "The `AddSubsemigroup` generated by a set includes the set."]
theorem subset_closure : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx
#align subsemigroup.subset_closure Subsemigroup.subset_closure
#align add_subsemigroup.subset_closure AddSubsemigroup.subset_closure

@[to_additive]
theorem not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align subsemigroup.not_mem_of_not_mem_closure Subsemigroup.not_mem_of_not_mem_closure
#align add_subsemigroup.not_mem_of_not_mem_closure AddSubsemigroup.not_mem_of_not_mem_closure

variable {S}

open Set

/-- A subsemigroup `S` includes `closure s` if and only if it includes `s`. -/
@[to_additive (attr := simp)
  "An additive subsemigroup `S` includes `closure s` if and only if it includes `s`"]
theorem closure_le : closure s ≤ S ↔ s ⊆ S :=
  ⟨Subset.trans subset_closure, fun h => sInf_le h⟩
#align subsemigroup.closure_le Subsemigroup.closure_le
#align add_subsemigroup.closure_le AddSubsemigroup.closure_le

/-- subsemigroup closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive "Additive subsemigroup closure of a set is monotone in its argument: if `s ⊆ t`,
  then `closure s ≤ closure t`"]
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Subset.trans h subset_closure
#align subsemigroup.closure_mono Subsemigroup.closure_mono
#align add_subsemigroup.closure_mono AddSubsemigroup.closure_mono

@[to_additive]
theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
  le_antisymm (closure_le.2 h₁) h₂
#align subsemigroup.closure_eq_of_le Subsemigroup.closure_eq_of_le
#align add_subsemigroup.closure_eq_of_le AddSubsemigroup.closure_eq_of_le

variable (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[to_additive (attr := elab_as_elim) "An induction principle for additive closure membership. If `p`
  holds for all elements of `s`, and is preserved under addition, then `p` holds for all
  elements of the additive closure of `s`."]
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure s) (mem : ∀ x ∈ s, p x)
    (mul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨p, mul _ _⟩).2 mem h
#align subsemigroup.closure_induction Subsemigroup.closure_induction
#align add_subsemigroup.closure_induction AddSubsemigroup.closure_induction

/-- A dependent version of `Subsemigroup.closure_induction`.  -/
@[to_additive (attr := elab_as_elim) "A dependent version of `AddSubsemigroup.closure_induction`. "]
theorem closure_induction' (s : Set M) {p : ∀ x, x ∈ closure s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_closure h))
    (mul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem hx hy)) {x} (hx : x ∈ closure s) :
    p x hx := by
  refine Exists.elim ?_ fun (hx : x ∈ closure s) (hc : p x hx) => hc
  exact
    closure_induction hx (fun x hx => ⟨_, mem x hx⟩) fun x y ⟨hx', hx⟩ ⟨hy', hy⟩ =>
      ⟨_, mul _ _ _ _ hx hy⟩
#align subsemigroup.closure_induction' Subsemigroup.closure_induction'
#align add_subsemigroup.closure_induction' AddSubsemigroup.closure_induction'

/-- An induction principle for closure membership for predicates with two arguments.  -/
@[to_additive (attr := elab_as_elim) "An induction principle for additive closure membership for
  predicates with two arguments."]
theorem closure_induction₂ {p : M → M → Prop} {x} {y : M} (hx : x ∈ closure s) (hy : y ∈ closure s)
    (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (Hmul_left : ∀ x y z, p x z → p y z → p (x * y) z)
    (Hmul_right : ∀ x y z, p z x → p z y → p z (x * y)) : p x y :=
  closure_induction hx
    (fun x xs => closure_induction hy (Hs x xs) fun z _ h₁ h₂ => Hmul_right z _ _ h₁ h₂)
    fun _ _ h₁ h₂ => Hmul_left _ _ _ h₁ h₂
#align subsemigroup.closure_induction₂ Subsemigroup.closure_induction₂
#align add_subsemigroup.closure_induction₂ AddSubsemigroup.closure_induction₂

/-- If `s` is a dense set in a magma `M`, `Subsemigroup.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[to_additive (attr := elab_as_elim) "If `s` is a dense set in an additive monoid `M`,
  `AddSubsemigroup.closure s = ⊤`, then in order to prove that some predicate `p` holds
  for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify that `p x` and `p y` imply
  `p (x + y)`."]
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure s = ⊤)
    (mem : ∀ x ∈ s, p x)
    (mul : ∀ x y, p x → p y → p (x * y)) : p x := by
  have : ∀ x ∈ closure s, p x := fun x hx => closure_induction hx mem mul
  simpa [hs] using this x
#align subsemigroup.dense_induction Subsemigroup.dense_induction
#align add_subsemigroup.dense_induction AddSubsemigroup.dense_induction

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive "`closure` forms a Galois insertion with the coercion to set."]
protected def gi : GaloisInsertion (@closure M _) SetLike.coe :=
  GaloisConnection.toGaloisInsertion (fun _ _ => closure_le) fun _ => subset_closure
#align subsemigroup.gi Subsemigroup.gi
#align add_subsemigroup.gi AddSubsemigroup.gi

variable {M}

/-- Closure of a subsemigroup `S` equals `S`. -/
@[to_additive (attr := simp) "Additive closure of an additive subsemigroup `S` equals `S`"]
theorem closure_eq : closure (S : Set M) = S :=
  (Subsemigroup.gi M).l_u_eq S
#align subsemigroup.closure_eq Subsemigroup.closure_eq
#align add_subsemigroup.closure_eq AddSubsemigroup.closure_eq

@[to_additive (attr := simp)]
theorem closure_empty : closure (∅ : Set M) = ⊥ :=
  (Subsemigroup.gi M).gc.l_bot
#align subsemigroup.closure_empty Subsemigroup.closure_empty
#align add_subsemigroup.closure_empty AddSubsemigroup.closure_empty

@[to_additive (attr := simp)]
theorem closure_univ : closure (univ : Set M) = ⊤ :=
  @coe_top M _ ▸ closure_eq ⊤
#align subsemigroup.closure_univ Subsemigroup.closure_univ
#align add_subsemigroup.closure_univ AddSubsemigroup.closure_univ

@[to_additive]
theorem closure_union (s t : Set M) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subsemigroup.gi M).gc.l_sup
#align subsemigroup.closure_union Subsemigroup.closure_union
#align add_subsemigroup.closure_union AddSubsemigroup.closure_union

@[to_additive]
theorem closure_iUnion {ι} (s : ι → Set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subsemigroup.gi M).gc.l_iSup
#align subsemigroup.closure_Union Subsemigroup.closure_iUnion
#align add_subsemigroup.closure_Union AddSubsemigroup.closure_iUnion

@[to_additive]
theorem closure_singleton_le_iff_mem (m : M) (p : Subsemigroup M) : closure {m} ≤ p ↔ m ∈ p := by
  rw [closure_le, singleton_subset_iff, SetLike.mem_coe]
#align subsemigroup.closure_singleton_le_iff_mem Subsemigroup.closure_singleton_le_iff_mem
#align add_subsemigroup.closure_singleton_le_iff_mem AddSubsemigroup.closure_singleton_le_iff_mem

@[to_additive]
theorem mem_iSup {ι : Sort*} (p : ι → Subsemigroup M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← closure_singleton_le_iff_mem, le_iSup_iff]
  simp only [closure_singleton_le_iff_mem]
#align subsemigroup.mem_supr Subsemigroup.mem_iSup
#align add_subsemigroup.mem_supr AddSubsemigroup.mem_iSup

@[to_additive]
theorem iSup_eq_closure {ι : Sort*} (p : ι → Subsemigroup M) :
    ⨆ i, p i = Subsemigroup.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Subsemigroup.closure_iUnion, Subsemigroup.closure_eq]
#align subsemigroup.supr_eq_closure Subsemigroup.iSup_eq_closure
#align add_subsemigroup.supr_eq_closure AddSubsemigroup.iSup_eq_closure

end Subsemigroup

namespace MulHom

variable [Mul N]

open Subsemigroup

/-- The subsemigroup of elements `x : M` such that `f x = g x` -/
@[to_additive "The additive subsemigroup of elements `x : M` such that `f x = g x`"]
def eqLocus (f g : M →ₙ* N) : Subsemigroup M where
  carrier := { x | f x = g x }
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]
#align mul_hom.eq_mlocus MulHom.eqLocus
#align add_hom.eq_mlocus AddHom.eqLocus

/-- If two mul homomorphisms are equal on a set, then they are equal on its subsemigroup closure. -/
@[to_additive "If two add homomorphisms are equal on a set,
  then they are equal on its additive subsemigroup closure."]
theorem eqOn_closure {f g : M →ₙ* N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from closure_le.2 h
#align mul_hom.eq_on_mclosure MulHom.eqOn_closure
#align add_hom.eq_on_mclosure AddHom.eqOn_closure

@[to_additive]
theorem eq_of_eqOn_top {f g : M →ₙ* N} (h : Set.EqOn f g (⊤ : Subsemigroup M)) : f = g :=
  ext fun _ => h trivial
#align mul_hom.eq_of_eq_on_mtop MulHom.eq_of_eqOn_top
#align add_hom.eq_of_eq_on_mtop AddHom.eq_of_eqOn_top

@[to_additive]
theorem eq_of_eqOn_dense {s : Set M} (hs : closure s = ⊤) {f g : M →ₙ* N} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_top <| hs ▸ eqOn_closure h
#align mul_hom.eq_of_eq_on_mdense MulHom.eq_of_eqOn_dense
#align add_hom.eq_of_eq_on_mdense AddHom.eq_of_eqOn_dense

end MulHom

end NonAssoc

section Assoc

namespace MulHom

open Subsemigroup

/-- Let `s` be a subset of a semigroup `M` such that the closure of `s` is the whole semigroup.
Then `MulHom.ofDense` defines a mul homomorphism from `M` asking for a proof
of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive]
def ofDense {M N} [Semigroup M] [Semigroup N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (hmul : ∀ (x), ∀ y ∈ s, f (x * y) = f x * f y) :
    M →ₙ* N where
  toFun := f
  map_mul' x y :=
    dense_induction y hs (fun y hy x => hmul x y hy)
      (fun y₁ y₂ h₁ h₂ x => by simp only [← mul_assoc, h₁, h₂]) x
#align mul_hom.of_mdense MulHom.ofDense
#align add_hom.of_mdense AddHom.ofDense

/-- Let `s` be a subset of an additive semigroup `M` such that the closure of `s` is the whole
semigroup.  Then `AddHom.ofDense` defines an additive homomorphism from `M` asking for a proof
of `f (x + y) = f x + f y` only for `y ∈ s`. -/
add_decl_doc AddHom.ofDense

@[to_additive (attr := simp, norm_cast)]
theorem coe_ofDense [Semigroup M] [Semigroup N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (hmul) : (ofDense f hs hmul : M → N) = f :=
  rfl
#align mul_hom.coe_of_mdense MulHom.coe_ofDense
#align add_hom.coe_of_mdense AddHom.coe_ofDense

end MulHom

end Assoc
