/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import Mathlib.Algebra.Hom.Group
import Mathlib.Algebra.Group.Units
import Mathlib.GroupTheory.Subsemigroup.Basic

#align_import group_theory.submonoid.basic from "leanprover-community/mathlib"@"feb99064803fd3108e37c18b0f77d0a8344677a3"

/-!
# Submonoids: definition and `CompleteLattice` structure

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
* `Submonoid.closure` :  monoid closure of a set, i.e., the least submonoid that includes the set.
* `Submonoid.gi` : `closure : Set M → Submonoid M` and coercion `coe : Submonoid M → Set M`
  form a `GaloisInsertion`;
* `MonoidHom.eqLocus`: the submonoid of elements `x : M` such that `f x = g x`;
* `MonoidHom.ofClosureEqTopRight`:  if a map `f : M → N` between two monoids satisfies
  `f 1 = 1` and `f (x * y) = f x * f y` for `y` from some dense set `s`, then `f` is a monoid
  homomorphism. E.g., if `f : ℕ → M` satisfies `f 0 = 0` and `f (x + 1) = f x + f 1`, then `f` is
  an additive monoid homomorphism.

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


-- Only needed for notation
-- Only needed for notation
variable {M : Type*} {N : Type*}

variable {A : Type*}

section NonAssoc

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

/-- `OneMemClass S M` says `S` is a type of subsets `s ≤ M`, such that `1 ∈ s` for all `s`. -/
class OneMemClass (S : Type*) (M : Type*) [One M] [SetLike S M] : Prop where
  /-- By definition, if we have `OneMemClass S M`, we have `1 ∈ s` for all `s : S`. -/
  one_mem : ∀ s : S, (1 : M) ∈ s
#align one_mem_class OneMemClass

export OneMemClass (one_mem)

/-- `ZeroMemClass S M` says `S` is a type of subsets `s ≤ M`, such that `0 ∈ s` for all `s`. -/
class ZeroMemClass (S : Type*) (M : Type*) [Zero M] [SetLike S M] : Prop where
  /-- By definition, if we have `ZeroMemClass S M`, we have `0 ∈ s` for all `s : S`. -/
  zero_mem : ∀ s : S, (0 : M) ∈ s
#align zero_mem_class ZeroMemClass

export ZeroMemClass (zero_mem)

attribute [to_additive] OneMemClass

section

/-- A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication. -/
structure Submonoid (M : Type*) [MulOneClass M] extends Subsemigroup M where
  /-- A submonoid contains `1`. -/
  one_mem' : (1 : M) ∈ carrier
#align submonoid Submonoid

end

/-- A submonoid of a monoid `M` can be considered as a subsemigroup of that monoid. -/
add_decl_doc Submonoid.toSubsemigroup
#align submonoid.to_subsemigroup Submonoid.toSubsemigroup

/-- `SubmonoidClass S M` says `S` is a type of subsets `s ≤ M` that contain `1`
and are closed under `(*)` -/
class SubmonoidClass (S : Type*) (M : Type*) [MulOneClass M] [SetLike S M] extends
  MulMemClass S M, OneMemClass S M : Prop
#align submonoid_class SubmonoidClass

section

/-- An additive submonoid of an additive monoid `M` is a subset containing 0 and
  closed under addition. -/
structure AddSubmonoid (M : Type*) [AddZeroClass M] extends AddSubsemigroup M where
  /-- An additive submonoid contains `0`. -/
  zero_mem' : (0 : M) ∈ carrier
#align add_submonoid AddSubmonoid

end

/-- An additive submonoid of an additive monoid `M` can be considered as an
additive subsemigroup of that additive monoid. -/
add_decl_doc AddSubmonoid.toAddSubsemigroup
#align add_submonoid.to_add_subsemigroup AddSubmonoid.toAddSubsemigroup

/-- `AddSubmonoidClass S M` says `S` is a type of subsets `s ≤ M` that contain `0`
and are closed under `(+)` -/
class AddSubmonoidClass (S : Type*) (M : Type*) [AddZeroClass M] [SetLike S M] extends
  AddMemClass S M, ZeroMemClass S M : Prop
#align add_submonoid_class AddSubmonoidClass

attribute [to_additive] Submonoid SubmonoidClass

@[to_additive]
theorem pow_mem {M A} [Monoid M] [SetLike A M] [SubmonoidClass A M] {S : A} {x : M}
    (hx : x ∈ S) : ∀ n : ℕ, x ^ n ∈ S
  | 0 => by
    rw [pow_zero]
    -- ⊢ 1 ∈ S
    exact OneMemClass.one_mem S
    -- 🎉 no goals
  | n + 1 => by
    rw [pow_succ]
    -- ⊢ x * x ^ n ∈ S
    exact mul_mem hx (pow_mem hx n)
    -- 🎉 no goals
#align pow_mem pow_mem
#align nsmul_mem nsmul_mem

namespace Submonoid

@[to_additive]
instance : SetLike (Submonoid M) M where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h
                             -- ⊢ { toSubsemigroup := toSubsemigroup✝, one_mem' := one_mem'✝ } = q
                                      -- ⊢ { toSubsemigroup := toSubsemigroup✝¹, one_mem' := one_mem'✝¹ } = { toSubsemi …
                                               -- ⊢ toSubsemigroup✝¹ = toSubsemigroup✝
                                                      -- 🎉 no goals

@[to_additive]
instance : SubmonoidClass (Submonoid M) M where
  one_mem := Submonoid.one_mem'
  mul_mem {s} := s.mul_mem'

initialize_simps_projections Submonoid (carrier → coe)

initialize_simps_projections AddSubmonoid (carrier → coe)

@[to_additive (attr := simp)]
theorem mem_toSubsemigroup {s : Submonoid M} {x : M} : x ∈ s.toSubsemigroup ↔ x ∈ s :=
  Iff.rfl

-- Porting note: `x ∈ s.carrier` is now syntactically `x ∈ s.toSubsemigroup.carrier`,
-- which `simp` already simplifies to `x ∈ s.toSubsemigroup`. So we remove the `@[simp]` attribute
-- here, and instead add the simp lemma `mem_toSubsemigroup` to allow `simp` to do this exact
-- simplification transitively.
@[to_additive]
theorem mem_carrier {s : Submonoid M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align submonoid.mem_carrier Submonoid.mem_carrier
#align add_submonoid.mem_carrier AddSubmonoid.mem_carrier

@[to_additive (attr := simp)]
theorem mem_mk {s : Subsemigroup M} {x : M} (h_one) : x ∈ mk s h_one ↔ x ∈ s :=
  Iff.rfl
#align submonoid.mem_mk Submonoid.mem_mk
#align add_submonoid.mem_mk AddSubmonoid.mem_mk

@[to_additive (attr := simp)]
theorem coe_set_mk {s : Subsemigroup M} (h_one) : (mk s h_one : Set M) = s :=
  rfl
#align submonoid.coe_set_mk Submonoid.coe_set_mk
#align add_submonoid.coe_set_mk AddSubmonoid.coe_set_mk

@[to_additive (attr := simp)]
theorem mk_le_mk {s t : Subsemigroup M} (h_one) (h_one') : mk s h_one ≤ mk t h_one' ↔ s ≤ t :=
  Iff.rfl
#align submonoid.mk_le_mk Submonoid.mk_le_mk
#align add_submonoid.mk_le_mk AddSubmonoid.mk_le_mk

/-- Two submonoids are equal if they have the same elements. -/
@[to_additive (attr := ext) "Two `AddSubmonoid`s are equal if they have the same elements."]
theorem ext {S T : Submonoid M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align submonoid.ext Submonoid.ext
#align add_submonoid.ext AddSubmonoid.ext

/-- Copy a submonoid replacing `carrier` with a set that is equal to it. -/
@[to_additive "Copy an additive submonoid replacing `carrier` with a set that is equal to it."]
protected def copy (S : Submonoid M) (s : Set M) (hs : s = S) : Submonoid M where
  carrier := s
  one_mem' := show 1 ∈ s from hs.symm ▸ S.one_mem'
  mul_mem' := hs.symm ▸ S.mul_mem'
#align submonoid.copy Submonoid.copy
#align add_submonoid.copy AddSubmonoid.copy

variable {S : Submonoid M}

@[to_additive (attr := simp)]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl
#align submonoid.coe_copy Submonoid.coe_copy
#align add_submonoid.coe_copy AddSubmonoid.coe_copy

@[to_additive]
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align submonoid.copy_eq Submonoid.copy_eq
#align add_submonoid.copy_eq AddSubmonoid.copy_eq

variable (S)

/-- A submonoid contains the monoid's 1. -/
@[to_additive "An `AddSubmonoid` contains the monoid's 0."]
protected theorem one_mem : (1 : M) ∈ S :=
  one_mem S
#align submonoid.one_mem Submonoid.one_mem
#align add_submonoid.zero_mem AddSubmonoid.zero_mem

/-- A submonoid is closed under multiplication. -/
@[to_additive "An `AddSubmonoid` is closed under addition."]
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  mul_mem
#align submonoid.mul_mem Submonoid.mul_mem
#align add_submonoid.add_mem AddSubmonoid.add_mem

/-- The submonoid `M` of the monoid `M`. -/
@[to_additive "The additive submonoid `M` of the `AddMonoid M`."]
instance : Top (Submonoid M) :=
  ⟨{  carrier := Set.univ
      one_mem' := Set.mem_univ 1
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

/-- The trivial submonoid `{1}` of a monoid `M`. -/
@[to_additive "The trivial `AddSubmonoid` `{0}` of an `AddMonoid` `M`."]
instance : Bot (Submonoid M) :=
  ⟨{  carrier := {1}
      one_mem' := Set.mem_singleton 1
      mul_mem' := fun ha hb => by
        simp only [Set.mem_singleton_iff] at *
        -- ⊢ a✝ * b✝ = 1
        rw [ha, hb, mul_one] }⟩
        -- 🎉 no goals

@[to_additive]
instance : Inhabited (Submonoid M) :=
  ⟨⊥⟩

@[to_additive (attr := simp)]
theorem mem_bot {x : M} : x ∈ (⊥ : Submonoid M) ↔ x = 1 :=
  Set.mem_singleton_iff
#align submonoid.mem_bot Submonoid.mem_bot
#align add_submonoid.mem_bot AddSubmonoid.mem_bot

@[to_additive (attr := simp)]
theorem mem_top (x : M) : x ∈ (⊤ : Submonoid M) :=
  Set.mem_univ x
#align submonoid.mem_top Submonoid.mem_top
#align add_submonoid.mem_top AddSubmonoid.mem_top

@[to_additive (attr := simp)]
theorem coe_top : ((⊤ : Submonoid M) : Set M) = Set.univ :=
  rfl
#align submonoid.coe_top Submonoid.coe_top
#align add_submonoid.coe_top AddSubmonoid.coe_top

@[to_additive (attr := simp)]
theorem coe_bot : ((⊥ : Submonoid M) : Set M) = {1} :=
  rfl
#align submonoid.coe_bot Submonoid.coe_bot
#align add_submonoid.coe_bot AddSubmonoid.coe_bot

/-- The inf of two submonoids is their intersection. -/
@[to_additive "The inf of two `AddSubmonoid`s is their intersection."]
instance : Inf (Submonoid M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ ∩ S₂
      one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[to_additive (attr := simp)]
theorem coe_inf (p p' : Submonoid M) : ((p ⊓ p' : Submonoid M) : Set M) = (p : Set M) ∩ p' :=
  rfl
#align submonoid.coe_inf Submonoid.coe_inf
#align add_submonoid.coe_inf AddSubmonoid.coe_inf

@[to_additive (attr := simp)]
theorem mem_inf {p p' : Submonoid M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
#align submonoid.mem_inf Submonoid.mem_inf
#align add_submonoid.mem_inf AddSubmonoid.mem_inf

@[to_additive]
instance : InfSet (Submonoid M) :=
  ⟨fun s =>
    { carrier := ⋂ t ∈ s, ↑t
      one_mem' := Set.mem_biInter fun i _ => i.one_mem
      mul_mem' := fun hx hy =>
        Set.mem_biInter fun i h =>
          i.mul_mem (by apply Set.mem_iInter₂.1 hx i h) (by apply Set.mem_iInter₂.1 hy i h) }⟩
                        -- 🎉 no goals
                                                            -- 🎉 no goals

@[to_additive (attr := simp, norm_cast)]
theorem coe_sInf (S : Set (Submonoid M)) : ((sInf S : Submonoid M) : Set M) = ⋂ s ∈ S, ↑s :=
  rfl
#align submonoid.coe_Inf Submonoid.coe_sInf
#align add_submonoid.coe_Inf AddSubmonoid.coe_sInf

@[to_additive]
theorem mem_sInf {S : Set (Submonoid M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂
#align submonoid.mem_Inf Submonoid.mem_sInf
#align add_submonoid.mem_Inf AddSubmonoid.mem_sInf

@[to_additive]
theorem mem_iInf {ι : Sort*} {S : ι → Submonoid M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_range_iff]
  -- 🎉 no goals
#align submonoid.mem_infi Submonoid.mem_iInf
#align add_submonoid.mem_infi AddSubmonoid.mem_iInf

@[to_additive (attr := simp, norm_cast)]
theorem coe_iInf {ι : Sort*} {S : ι → Submonoid M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]
  -- 🎉 no goals
#align submonoid.coe_infi Submonoid.coe_iInf
#align add_submonoid.coe_infi AddSubmonoid.coe_iInf

/-- Submonoids of a monoid form a complete lattice. -/
@[to_additive "The `AddSubmonoid`s of an `AddMonoid` form a complete lattice."]
instance : CompleteLattice (Submonoid M) :=
  { (completeLatticeOfInf (Submonoid M)) fun _ =>
      IsGLB.of_image (f := (SetLike.coe : Submonoid M → Set M))
        (@fun S T => show (S : Set M) ≤ T ↔ S ≤ T from SetLike.coe_subset_coe)
        isGLB_biInf with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun S _ hx => (mem_bot.1 hx).symm ▸ S.one_mem
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _ _ _ ha hb _ hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

@[to_additive (attr := simp)]
theorem subsingleton_iff : Subsingleton (Submonoid M) ↔ Subsingleton M :=
  ⟨fun h =>
    ⟨fun x y =>
      have : ∀ i : M, i = 1 := fun i =>
        mem_bot.mp <| Subsingleton.elim (⊤ : Submonoid M) ⊥ ▸ mem_top i
      (this x).trans (this y).symm⟩,
    fun h =>
    ⟨fun x y => Submonoid.ext fun i => Subsingleton.elim 1 i ▸ by simp [Submonoid.one_mem]⟩⟩
                                                                  -- 🎉 no goals
#align submonoid.subsingleton_iff Submonoid.subsingleton_iff
#align add_submonoid.subsingleton_iff AddSubmonoid.subsingleton_iff

@[to_additive (attr := simp)]
theorem nontrivial_iff : Nontrivial (Submonoid M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans subsingleton_iff).trans
      not_nontrivial_iff_subsingleton.symm)
#align submonoid.nontrivial_iff Submonoid.nontrivial_iff
#align add_submonoid.nontrivial_iff AddSubmonoid.nontrivial_iff

@[to_additive]
instance [Subsingleton M] : Unique (Submonoid M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ (subsingleton_iff.mpr ‹_›) a _⟩

@[to_additive]
instance [Nontrivial M] : Nontrivial (Submonoid M) :=
  nontrivial_iff.mpr ‹_›

/-- The `Submonoid` generated by a set. -/
@[to_additive "The `add_submonoid` generated by a set"]
def closure (s : Set M) : Submonoid M :=
  sInf { S | s ⊆ S }
#align submonoid.closure Submonoid.closure
#align add_submonoid.closure AddSubmonoid.closure

@[to_additive]
theorem mem_closure {x : M} : x ∈ closure s ↔ ∀ S : Submonoid M, s ⊆ S → x ∈ S :=
  mem_sInf
#align submonoid.mem_closure Submonoid.mem_closure
#align add_submonoid.mem_closure AddSubmonoid.mem_closure

/-- The submonoid generated by a set includes the set. -/
@[to_additive (attr := simp) "The `AddSubmonoid` generated by a set includes the set."]
theorem subset_closure : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx
#align submonoid.subset_closure Submonoid.subset_closure
#align add_submonoid.subset_closure AddSubmonoid.subset_closure

@[to_additive]
theorem not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align submonoid.not_mem_of_not_mem_closure Submonoid.not_mem_of_not_mem_closure
#align add_submonoid.not_mem_of_not_mem_closure AddSubmonoid.not_mem_of_not_mem_closure

variable {S}

open Set

/-- A submonoid `S` includes `closure s` if and only if it includes `s`. -/
@[to_additive (attr := simp)
"An additive submonoid `S` includes `closure s` if and only if it includes `s`"]
theorem closure_le : closure s ≤ S ↔ s ⊆ S :=
  ⟨Subset.trans subset_closure, fun h => sInf_le h⟩
#align submonoid.closure_le Submonoid.closure_le
#align add_submonoid.closure_le AddSubmonoid.closure_le

/-- Submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive
      "Additive submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
      then `closure s ≤ closure t`"]
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Subset.trans h subset_closure
#align submonoid.closure_mono Submonoid.closure_mono
#align add_submonoid.closure_mono AddSubmonoid.closure_mono

@[to_additive]
theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
  le_antisymm (closure_le.2 h₁) h₂
#align submonoid.closure_eq_of_le Submonoid.closure_eq_of_le
#align add_submonoid.closure_eq_of_le AddSubmonoid.closure_eq_of_le

variable (S)

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[to_additive (attr := elab_as_elim)
      "An induction principle for additive closure membership. If `p` holds for `0` and all
      elements of `s`, and is preserved under addition, then `p` holds for all elements of the
      additive closure of `s`."]
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure s) (Hs : ∀ x ∈ s, p x) (H1 : p 1)
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨⟨p, Hmul _ _⟩, H1⟩).2 Hs h
#align submonoid.closure_induction Submonoid.closure_induction
#align add_submonoid.closure_induction AddSubmonoid.closure_induction

/-- A dependent version of `Submonoid.closure_induction`.  -/
@[to_additive (attr := elab_as_elim) "A dependent version of `AddSubmonoid.closure_induction`. "]
theorem closure_induction' (s : Set M) {p : ∀ x, x ∈ closure s → Prop}
    (Hs : ∀ (x) (h : x ∈ s), p x (subset_closure h)) (H1 : p 1 (one_mem _))
    (Hmul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem hx hy)) {x} (hx : x ∈ closure s) :
    p x hx := by
  refine' Exists.elim _ fun (hx : x ∈ closure s) (hc : p x hx) => hc
  -- ⊢ ∃ x_1, p x x_1
  exact
    closure_induction hx (fun x hx => ⟨_, Hs x hx⟩) ⟨_, H1⟩ fun x y ⟨hx', hx⟩ ⟨hy', hy⟩ =>
      ⟨_, Hmul _ _ _ _ hx hy⟩
#align submonoid.closure_induction' Submonoid.closure_induction'
#align add_submonoid.closure_induction' AddSubmonoid.closure_induction'

/-- An induction principle for closure membership for predicates with two arguments.  -/
@[to_additive (attr := elab_as_elim)
      "An induction principle for additive closure membership for predicates with two arguments."]
theorem closure_induction₂ {p : M → M → Prop} {x} {y : M} (hx : x ∈ closure s) (hy : y ∈ closure s)
    (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (H1_left : ∀ x, p 1 x) (H1_right : ∀ x, p x 1)
    (Hmul_left : ∀ x y z, p x z → p y z → p (x * y) z)
    (Hmul_right : ∀ x y z, p z x → p z y → p z (x * y)) : p x y :=
  closure_induction hx
    (fun x xs =>
      closure_induction hy (Hs x xs) (H1_right x) fun z _ h₁ h₂ => Hmul_right z _ _ h₁ h₂)
    (H1_left y) fun _ _ h₁ h₂ => Hmul_left _ _ _ h₁ h₂
#align submonoid.closure_induction₂ Submonoid.closure_induction₂
#align add_submonoid.closure_induction₂ AddSubmonoid.closure_induction₂

/-- If `s` is a dense set in a monoid `M`, `Submonoid.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, verify `p 1`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[to_additive (attr := elab_as_elim)
      "If `s` is a dense set in an additive monoid `M`, `AddSubmonoid.closure s = ⊤`, then in
      order to prove that some predicate `p` holds for all `x : M` it suffices to verify `p x` for
      `x ∈ s`, verify `p 0`, and verify that `p x` and `p y` imply `p (x + y)`."]
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure s = ⊤) (Hs : ∀ x ∈ s, p x)
    (H1 : p 1) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x := by
  have : ∀ x ∈ closure s, p x := fun x hx => closure_induction hx Hs H1 Hmul
  -- ⊢ p x
  simpa [hs] using this x
  -- 🎉 no goals
#align submonoid.dense_induction Submonoid.dense_induction
#align add_submonoid.dense_induction AddSubmonoid.dense_induction

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive "`closure` forms a Galois insertion with the coercion to set."]
protected def gi : GaloisInsertion (@closure M _) SetLike.coe where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl
#align submonoid.gi Submonoid.gi
#align add_submonoid.gi AddSubmonoid.gi

variable {M}

/-- Closure of a submonoid `S` equals `S`. -/
@[to_additive (attr := simp) "Additive closure of an additive submonoid `S` equals `S`"]
theorem closure_eq : closure (S : Set M) = S :=
  (Submonoid.gi M).l_u_eq S
#align submonoid.closure_eq Submonoid.closure_eq
#align add_submonoid.closure_eq AddSubmonoid.closure_eq

@[to_additive (attr := simp)]
theorem closure_empty : closure (∅ : Set M) = ⊥ :=
  (Submonoid.gi M).gc.l_bot
#align submonoid.closure_empty Submonoid.closure_empty
#align add_submonoid.closure_empty AddSubmonoid.closure_empty

@[to_additive (attr := simp)]
theorem closure_univ : closure (univ : Set M) = ⊤ :=
  @coe_top M _ ▸ closure_eq ⊤
#align submonoid.closure_univ Submonoid.closure_univ
#align add_submonoid.closure_univ AddSubmonoid.closure_univ

@[to_additive]
theorem closure_union (s t : Set M) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Submonoid.gi M).gc.l_sup
#align submonoid.closure_union Submonoid.closure_union
#align add_submonoid.closure_union AddSubmonoid.closure_union

@[to_additive]
theorem closure_iUnion {ι} (s : ι → Set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Submonoid.gi M).gc.l_iSup
#align submonoid.closure_Union Submonoid.closure_iUnion
#align add_submonoid.closure_Union AddSubmonoid.closure_iUnion

-- Porting note: `simp` can now prove this, so we remove the `@[simp]` attribute
@[to_additive]
theorem closure_singleton_le_iff_mem (m : M) (p : Submonoid M) : closure {m} ≤ p ↔ m ∈ p := by
  rw [closure_le, singleton_subset_iff, SetLike.mem_coe]
  -- 🎉 no goals
#align submonoid.closure_singleton_le_iff_mem Submonoid.closure_singleton_le_iff_mem
#align add_submonoid.closure_singleton_le_iff_mem AddSubmonoid.closure_singleton_le_iff_mem

@[to_additive]
theorem mem_iSup {ι : Sort*} (p : ι → Submonoid M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← closure_singleton_le_iff_mem, le_iSup_iff]
  -- ⊢ (∀ (b : Submonoid M), (∀ (i : ι), p i ≤ b) → closure {m} ≤ b) ↔ ∀ (N : Submo …
  simp only [closure_singleton_le_iff_mem]
  -- 🎉 no goals
#align submonoid.mem_supr Submonoid.mem_iSup
#align add_submonoid.mem_supr AddSubmonoid.mem_iSup

@[to_additive]
theorem iSup_eq_closure {ι : Sort*} (p : ι → Submonoid M) :
    ⨆ i, p i = Submonoid.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Submonoid.closure_iUnion, Submonoid.closure_eq]
  -- 🎉 no goals
#align submonoid.supr_eq_closure Submonoid.iSup_eq_closure
#align add_submonoid.supr_eq_closure AddSubmonoid.iSup_eq_closure

@[to_additive]
theorem disjoint_def {p₁ p₂ : Submonoid M} : Disjoint p₁ p₂ ↔ ∀ {x : M}, x ∈ p₁ → x ∈ p₂ → x = 1 :=
  by simp_rw [disjoint_iff_inf_le, SetLike.le_def, mem_inf, and_imp, mem_bot]
     -- 🎉 no goals
#align submonoid.disjoint_def Submonoid.disjoint_def
#align add_submonoid.disjoint_def AddSubmonoid.disjoint_def

@[to_additive]
theorem disjoint_def' {p₁ p₂ : Submonoid M} :
    Disjoint p₁ p₂ ↔ ∀ {x y : M}, x ∈ p₁ → y ∈ p₂ → x = y → x = 1 :=
  disjoint_def.trans ⟨fun h _ _ hx hy hxy => h hx <| hxy.symm ▸ hy, fun h _ hx hx' => h hx hx' rfl⟩
#align submonoid.disjoint_def' Submonoid.disjoint_def'
#align add_submonoid.disjoint_def' AddSubmonoid.disjoint_def'

end Submonoid

namespace MonoidHom

variable [MulOneClass N]

open Submonoid

/-- The submonoid of elements `x : M` such that `f x = g x` -/
@[to_additive "The additive submonoid of elements `x : M` such that `f x = g x`"]
def eqLocusM (f g : M →* N) : Submonoid M where
  carrier := { x | f x = g x }
  one_mem' := by rw [Set.mem_setOf_eq, f.map_one, g.map_one]
                 -- 🎉 no goals
                                           -- 🎉 no goals
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]
#align monoid_hom.eq_mlocus MonoidHom.eqLocusM
#align add_monoid_hom.eq_mlocus AddMonoidHom.eqLocusM

@[to_additive (attr := simp)]
theorem eqLocusM_same (f : M →* N) : f.eqLocusM f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _
#align monoid_hom.eq_mlocus_same MonoidHom.eqLocusM_same
#align add_monoid_hom.eq_mlocus_same AddMonoidHom.eqLocusM_same

/-- If two monoid homomorphisms are equal on a set, then they are equal on its submonoid closure. -/
@[to_additive
      "If two monoid homomorphisms are equal on a set, then they are equal on its submonoid
      closure."]
theorem eqOn_closureM {f g : M →* N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocusM g from closure_le.2 h
#align monoid_hom.eq_on_mclosure MonoidHom.eqOn_closureM
#align add_monoid_hom.eq_on_mclosure AddMonoidHom.eqOn_closureM

@[to_additive]
theorem eq_of_eqOn_topM {f g : M →* N} (h : Set.EqOn f g (⊤ : Submonoid M)) : f = g :=
  ext fun _ => h trivial
#align monoid_hom.eq_of_eq_on_mtop MonoidHom.eq_of_eqOn_topM
#align add_monoid_hom.eq_of_eq_on_mtop AddMonoidHom.eq_of_eqOn_topM

@[to_additive]
theorem eq_of_eqOn_denseM {s : Set M} (hs : closure s = ⊤) {f g : M →* N} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_topM <| hs ▸ eqOn_closureM h
#align monoid_hom.eq_of_eq_on_mdense MonoidHom.eq_of_eqOn_denseM
#align add_monoid_hom.eq_of_eq_on_mdense AddMonoidHom.eq_of_eqOn_denseM

end MonoidHom

end NonAssoc

section Assoc

variable [Monoid M] [Monoid N] {s : Set M}

section IsUnit

/-- The submonoid consisting of the units of a monoid -/
@[to_additive "The additive submonoid consisting of the additive units of an additive monoid"]
def IsUnit.submonoid (M : Type*) [Monoid M] : Submonoid M where
  carrier := setOf IsUnit
  one_mem' := by simp only [isUnit_one, Set.mem_setOf_eq]
                 -- 🎉 no goals
  mul_mem' := by
    -- ⊢ a * b ∈ setOf IsUnit
    intro a b ha hb
    -- ⊢ IsUnit (a * b)
    rw [Set.mem_setOf_eq] at *
    -- 🎉 no goals
    exact IsUnit.mul ha hb
#align is_unit.submonoid IsUnit.submonoid
#align is_add_unit.add_submonoid IsAddUnit.addSubmonoid

@[to_additive]
theorem IsUnit.mem_submonoid_iff {M : Type*} [Monoid M] (a : M) :
    a ∈ IsUnit.submonoid M ↔ IsUnit a := by
  change a ∈ setOf IsUnit ↔ IsUnit a
  -- ⊢ a ∈ setOf IsUnit ↔ IsUnit a
  rw [Set.mem_setOf_eq]
  -- 🎉 no goals
#align is_unit.mem_submonoid_iff IsUnit.mem_submonoid_iff
#align is_add_unit.mem_add_submonoid_iff IsAddUnit.mem_addSubmonoid_iff

end IsUnit

namespace MonoidHom

open Submonoid

/-- Let `s` be a subset of a monoid `M` such that the closure of `s` is the whole monoid.
Then `MonoidHom.ofClosureEqTopLeft` defines a monoid homomorphism from `M` asking for
a proof of `f (x * y) = f x * f y` only for `x ∈ s`. -/
@[to_additive
      "Let `s` be a subset of an additive monoid `M` such that the closure of `s` is
      the whole monoid. Then `AddMonoidHom.ofClosureEqTopLeft` defines an additive monoid
      homomorphism from `M` asking for a proof of `f (x + y) = f x + f y` only for `x ∈ s`. "]
def ofClosureMEqTopLeft {M N} [Monoid M] [Monoid N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (h1 : f 1 = 1) (hmul : ∀ x ∈ s, ∀ (y), f (x * y) = f x * f y) :
    M →* N where
  toFun := f
  map_one' := h1
  map_mul' x :=
    (dense_induction (p := _) x hs hmul fun y => by rw [one_mul, h1, one_mul]) fun a b ha hb y => by
                                                    -- 🎉 no goals
      rw [mul_assoc, ha, ha, hb, mul_assoc]
      -- 🎉 no goals
#align monoid_hom.of_mclosure_eq_top_left MonoidHom.ofClosureMEqTopLeft
#align add_monoid_hom.of_mclosure_eq_top_left AddMonoidHom.ofClosureMEqTopLeft

@[to_additive (attr := simp, norm_cast)]
theorem coe_ofClosureMEqTopLeft (f : M → N) (hs : closure s = ⊤) (h1 hmul) :
    ⇑(ofClosureMEqTopLeft f hs h1 hmul) = f :=
  rfl
#align monoid_hom.coe_of_mclosure_eq_top_left MonoidHom.coe_ofClosureMEqTopLeft
#align add_monoid_hom.coe_of_mclosure_eq_top_left AddMonoidHom.coe_ofClosureMEqTopLeft

/-- Let `s` be a subset of a monoid `M` such that the closure of `s` is the whole monoid.
Then `MonoidHom.ofClosureEqTopRight` defines a monoid homomorphism from `M` asking for
a proof of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive
      "Let `s` be a subset of an additive monoid `M` such that the closure of `s` is
      the whole monoid. Then `AddMonoidHom.ofClosureEqTopRight` defines an additive monoid
      homomorphism from `M` asking for a proof of `f (x + y) = f x + f y` only for `y ∈ s`. "]
def ofClosureMEqTopRight {M N} [Monoid M] [Monoid N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (h1 : f 1 = 1) (hmul : ∀ (x), ∀ y ∈ s, f (x * y) = f x * f y) :
    M →* N where
  toFun := f
  map_one' := h1
  map_mul' x y :=
    dense_induction y hs (fun y hy x => hmul x y hy) (by simp [h1])
                                                         -- 🎉 no goals
      (fun y₁ y₂ (h₁ : ∀ x, f _ = f _ * f _) (h₂ : ∀ x, f _ = f _ * f _) x => by
        simp [← mul_assoc, h₁, h₂]) x
        -- 🎉 no goals
#align monoid_hom.of_mclosure_eq_top_right MonoidHom.ofClosureMEqTopRight
#align add_monoid_hom.of_mclosure_eq_top_right AddMonoidHom.ofClosureMEqTopRight

@[to_additive (attr := simp, norm_cast)]
theorem coe_ofClosureMEqTopRight (f : M → N) (hs : closure s = ⊤) (h1 hmul) :
    ⇑(ofClosureMEqTopRight f hs h1 hmul) = f :=
  rfl
#align monoid_hom.coe_of_mclosure_eq_top_right MonoidHom.coe_ofClosureMEqTopRight
#align add_monoid_hom.coe_of_mclosure_eq_top_right AddMonoidHom.coe_ofClosureMEqTopRight

end MonoidHom

end Assoc
