/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
Ported by: Anatole Dedecjer

! This file was ported from Lean 3 source module group_theory.submonoid.basic
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Hom.Group
import Mathlib.Algebra.Group.Units
import Mathlib.GroupTheory.Subsemigroup.Basic

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
variable {M : Type _} {N : Type _}

variable {A : Type _}

section NonAssoc

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

/-- `one_mem_class S M` says `S` is a type of subsets `s ≤ M`, such that `1 ∈ s` for all `s`. -/
class OneMemClass (S : Type _) (M : outParam <| Type _) [One M] [SetLike S M] where
  one_mem : ∀ s : S, (1 : M) ∈ s
#align one_mem_class OneMemClass

export OneMemClass (one_mem)

/-- `zero_mem_class S M` says `S` is a type of subsets `s ≤ M`, such that `0 ∈ s` for all `s`. -/
class ZeroMemClass (S : Type _) (M : outParam <| Type _) [Zero M] [SetLike S M] where
  zero_mem : ∀ s : S, (0 : M) ∈ s
#align zero_mem_class ZeroMemClass

export ZeroMemClass (zero_mem)

attribute [to_additive] OneMemClass

section

/-- A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication. -/
structure Submonoid (M : Type _) [MulOneClass M] extends Subsemigroup M where
  one_mem' : (1 : M) ∈ carrier
#align submonoid Submonoid

end

/-- A submonoid of a monoid `M` can be considered as a subsemigroup of that monoid. -/
add_decl_doc Submonoid.toSubsemigroup

/-- `SubmonoidClass S M` says `S` is a type of subsets `s ≤ M` that contain `1`
and are closed under `(*)` -/
class SubmonoidClass (S : Type _) (M : outParam <| Type _) [MulOneClass M] [SetLike S M] extends
  MulMemClass S M where
  one_mem : ∀ s : S, (1 : M) ∈ s
#align submonoid_class SubmonoidClass

section

/-- An additive submonoid of an additive monoid `M` is a subset containing 0 and
  closed under addition. -/
structure AddSubmonoid (M : Type _) [AddZeroClass M] extends AddSubsemigroup M where
  zero_mem' : (0 : M) ∈ carrier
#align add_submonoid AddSubmonoid

end

/-- An additive submonoid of an additive monoid `M` can be considered as an
additive subsemigroup of that additive monoid. -/
add_decl_doc AddSubmonoid.toAddSubsemigroup

/-- `AddSubmonoidClass S M` says `S` is a type of subsets `s ≤ M` that contain `0`
and are closed under `(+)` -/
class AddSubmonoidClass (S : Type _) (M : outParam <| Type _) [AddZeroClass M] [SetLike S M] extends
  AddMemClass S M where
  zero_mem : ∀ s : S, (0 : M) ∈ s
#align add_submonoid_class AddSubmonoidClass

attribute [to_additive] Submonoid SubmonoidClass

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SubmonoidClass.toOneMemClass (S : Type _) (M : outParam <| Type _)
    [MulOneClass M] [SetLike S M] [h : SubmonoidClass S M] : OneMemClass S M :=
  { h with }
#align submonoid_class.to_one_mem_class SubmonoidClass.toOneMemClass

@[to_additive]
theorem pow_mem {M} [Monoid M] {A : Type _} [SetLike A M] [SubmonoidClass A M] {S : A} {x : M}
    (hx : x ∈ S) : ∀ n : ℕ, x ^ n ∈ S
  | 0 => by
    rw [pow_zero]
    -- Porting note: for some reason, `exact OneMemClass.one_mem S` is super slow...
    exact @OneMemClass.one_mem A M _ _ (SubmonoidClass.toOneMemClass _ _) S
  | n + 1 => by
    rw [pow_succ]
    exact MulMemClass.mul_mem hx (pow_mem hx n)
#align pow_mem pow_mem

namespace Submonoid

@[to_additive]
instance : SetLike (Submonoid M)
      M where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h

@[to_additive]
instance : SubmonoidClass (Submonoid M)
      M where
  one_mem := Submonoid.one_mem'
  mul_mem {s} := s.mul_mem'

/-- See Note [custom simps projection] -/
@[to_additive]
def Simps.coe (S : Submonoid M) : Set M :=
  S
#align submonoid.simps.coe Submonoid.Simps.coe

/-- See Note [custom simps projection] -/
add_decl_doc AddSubmonoid.Simps.coe

initialize_simps_projections Submonoid (toSubsemigroup_carrier → coe)

initialize_simps_projections AddSubmonoid (toAddSubsemigroup_carrier → coe)

@[simp, to_additive]
theorem mem_carrier {s : Submonoid M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align submonoid.mem_carrier Submonoid.mem_carrier

@[simp, to_additive]
theorem mem_mk {s : Set M} {x : M} (h_one) (h_mul) : x ∈ mk ⟨s, h_mul⟩ h_one ↔ x ∈ s :=
  Iff.rfl
#align submonoid.mem_mk Submonoid.mem_mk

@[simp, to_additive]
theorem coe_set_mk {s : Set M} (h_one) (h_mul) : (mk ⟨s, h_mul⟩ h_one : Set M) = s :=
  rfl
#align submonoid.coe_set_mk Submonoid.coe_set_mk

@[simp, to_additive]
theorem mk_le_mk {s t : Set M} (h_one) (h_mul) (h_one') (h_mul') :
    mk ⟨s, h_mul⟩ h_one ≤ mk ⟨t, h_mul'⟩ h_one' ↔ s ⊆ t :=
  Iff.rfl
#align submonoid.mk_le_mk Submonoid.mk_le_mk

/-- Two submonoids are equal if they have the same elements. -/
@[ext, to_additive "Two `add_submonoid`s are equal if they have the same elements."]
theorem ext {S T : Submonoid M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align submonoid.ext Submonoid.ext

/-- Copy a submonoid replacing `carrier` with a set that is equal to it. -/
@[to_additive "Copy an additive submonoid replacing `carrier` with a set that is equal to it."]
protected def copy (S : Submonoid M) (s : Set M) (hs : s = S) :
    Submonoid M where
  carrier := s
  one_mem' := show 1 ∈ s from hs.symm ▸ S.one_mem'
  mul_mem' := hs.symm ▸ S.mul_mem'
#align submonoid.copy Submonoid.copy

variable {S : Submonoid M}

@[simp, to_additive]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl
#align submonoid.coe_copy Submonoid.coe_copy

@[to_additive]
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align submonoid.copy_eq Submonoid.copy_eq

variable (S)

/-- A submonoid contains the monoid's 1. -/
@[to_additive "An `add_submonoid` contains the monoid's 0."]
protected theorem one_mem : (1 : M) ∈ S :=
  one_mem S
#align submonoid.one_mem Submonoid.one_mem

/-- A submonoid is closed under multiplication. -/
@[to_additive "An `add_submonoid` is closed under addition."]
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  mul_mem
#align submonoid.mul_mem Submonoid.mul_mem

/-- The submonoid `M` of the monoid `M`. -/
@[to_additive "The additive submonoid `M` of the `add_monoid M`."]
instance : Top (Submonoid M) :=
  ⟨{  carrier := Set.univ
      one_mem' := Set.mem_univ 1
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

/-- The trivial submonoid `{1}` of an monoid `M`. -/
@[to_additive "The trivial `add_submonoid` `{0}` of an `add_monoid` `M`."]
instance : Bot (Submonoid M) :=
  ⟨{  carrier := {1}
      one_mem' := Set.mem_singleton 1
      mul_mem' := fun ha hb => by
        simp only [Set.mem_singleton_iff] at *
        rw [ha, hb, mul_one] }⟩

@[to_additive]
instance : Inhabited (Submonoid M) :=
  ⟨⊥⟩

@[simp, to_additive]
theorem mem_bot {x : M} : x ∈ (⊥ : Submonoid M) ↔ x = 1 :=
  Set.mem_singleton_iff
#align submonoid.mem_bot Submonoid.mem_bot

@[simp, to_additive]
theorem mem_top (x : M) : x ∈ (⊤ : Submonoid M) :=
  Set.mem_univ x
#align submonoid.mem_top Submonoid.mem_top

@[simp, to_additive]
theorem coe_top : ((⊤ : Submonoid M) : Set M) = Set.univ :=
  rfl
#align submonoid.coe_top Submonoid.coe_top

@[simp, to_additive]
theorem coe_bot : ((⊥ : Submonoid M) : Set M) = {1} :=
  rfl
#align submonoid.coe_bot Submonoid.coe_bot

/-- The inf of two submonoids is their intersection. -/
@[to_additive "The inf of two `add_submonoid`s is their intersection."]
instance : HasInf (Submonoid M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ ∩ S₂
      one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[simp, to_additive]
theorem coe_inf (p p' : Submonoid M) : ((p ⊓ p' : Submonoid M) : Set M) = (p : Set M) ∩ p' :=
  rfl
#align submonoid.coe_inf Submonoid.coe_inf

@[simp, to_additive]
theorem mem_inf {p p' : Submonoid M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
#align submonoid.mem_inf Submonoid.mem_inf

@[to_additive]
instance : InfSet (Submonoid M) :=
  ⟨fun s =>
    { carrier := ⋂ t ∈ s, ↑t
      one_mem' := Set.mem_binterᵢ fun i _ => i.one_mem
      mul_mem' := fun hx hy =>
        Set.mem_binterᵢ fun i h =>
          i.mul_mem (by apply Set.mem_interᵢ₂.1 hx i h) (by apply Set.mem_interᵢ₂.1 hy i h) }⟩

@[simp, norm_cast, to_additive]
theorem coe_infₛ (S : Set (Submonoid M)) : ((infₛ S : Submonoid M) : Set M) = ⋂ s ∈ S, ↑s :=
  rfl
#align submonoid.coe_Inf Submonoid.coe_infₛ

@[to_additive]
theorem mem_infₛ {S : Set (Submonoid M)} {x : M} : x ∈ infₛ S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_interᵢ₂
#align submonoid.mem_Inf Submonoid.mem_infₛ

@[to_additive]
theorem mem_infᵢ {ι : Sort _} {S : ι → Submonoid M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [infᵢ, mem_infₛ, Set.forall_range_iff]
#align submonoid.mem_infi Submonoid.mem_infᵢ

@[simp, norm_cast, to_additive]
theorem coe_infᵢ {ι : Sort _} {S : ι → Submonoid M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [infᵢ, coe_infₛ, Set.binterᵢ_range]
#align submonoid.coe_infi Submonoid.coe_infᵢ

/-- Submonoids of a monoid form a complete lattice. -/
@[to_additive "The `add_submonoid`s of an `add_monoid` form a complete lattice."]
instance : CompleteLattice (Submonoid M) :=
  { (completeLatticeOfInf (Submonoid M)) fun _ =>
      IsGLB.of_image (f := (SetLike.coe : Submonoid M → Set M))
        (@fun S T => show (S : Set M) ≤ T ↔ S ≤ T from SetLike.coe_subset_coe)
        isGLB_binfᵢ with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun S _ hx => (mem_bot.1 hx).symm ▸ S.one_mem
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    infₛ := InfSet.infₛ
    le_inf := fun _ _ _ ha hb _ hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

@[simp, to_additive]
theorem subsingleton_iff : Subsingleton (Submonoid M) ↔ Subsingleton M :=
  ⟨fun h =>
    ⟨fun x y =>
      have : ∀ i : M, i = 1 := fun i =>
        mem_bot.mp <| Subsingleton.elim (⊤ : Submonoid M) ⊥ ▸ mem_top i
      (this x).trans (this y).symm⟩,
    fun h =>
    ⟨fun x y => Submonoid.ext fun i => Subsingleton.elim 1 i ▸ by simp [Submonoid.one_mem]⟩⟩
#align submonoid.subsingleton_iff Submonoid.subsingleton_iff

@[simp, to_additive]
theorem nontrivial_iff : Nontrivial (Submonoid M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans subsingleton_iff).trans
      not_nontrivial_iff_subsingleton.symm)
#align submonoid.nontrivial_iff Submonoid.nontrivial_iff

@[to_additive]
instance [Subsingleton M] : Unique (Submonoid M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ (subsingleton_iff.mpr ‹_›) a _⟩

@[to_additive]
instance [Nontrivial M] : Nontrivial (Submonoid M) :=
  nontrivial_iff.mpr ‹_›

/-- The `Submonoid` generated by a set. -/
@[to_additive "The `add_submonoid` generated by a set"]
def closure (s : Set M) : Submonoid M :=
  infₛ { S | s ⊆ S }
#align submonoid.closure Submonoid.closure

@[to_additive]
theorem mem_closure {x : M} : x ∈ closure s ↔ ∀ S : Submonoid M, s ⊆ S → x ∈ S :=
  mem_infₛ
#align submonoid.mem_closure Submonoid.mem_closure

/-- The submonoid generated by a set includes the set. -/
@[simp, to_additive "The `add_submonoid` generated by a set includes the set."]
theorem subset_closure : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx
#align submonoid.subset_closure Submonoid.subset_closure

@[to_additive]
theorem not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align submonoid.not_mem_of_not_mem_closure Submonoid.not_mem_of_not_mem_closure

variable {S}

open Set

/-- A submonoid `S` includes `closure s` if and only if it includes `s`. -/
@[simp, to_additive "An additive submonoid `S` includes `closure s` if and only if it includes `s`"]
theorem closure_le : closure s ≤ S ↔ s ⊆ S :=
  ⟨Subset.trans subset_closure, fun h => infₛ_le h⟩
#align submonoid.closure_le Submonoid.closure_le

/-- Submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive
      "Additive submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
      then `closure s ≤ closure t`"]
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Subset.trans h subset_closure
#align submonoid.closure_mono Submonoid.closure_mono

@[to_additive]
theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
  le_antisymm (closure_le.2 h₁) h₂
#align submonoid.closure_eq_of_le Submonoid.closure_eq_of_le

variable (S)

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_elim,
  to_additive
      "An induction principle for additive closure membership. If `p` holds for `0` and all
      elements of `s`, and is preserved under addition, then `p` holds for all elements of the
      additive closure of `s`."]
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure s) (Hs : ∀ x ∈ s, p x) (H1 : p 1)
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨⟨p, Hmul _ _⟩, H1⟩).2 Hs h
#align submonoid.closure_induction Submonoid.closure_induction

/-- A dependent version of `Submonoid.closure_induction`.  -/
@[elab_as_elim, to_additive "A dependent version of `AddSubmonoid.closure_induction`. "]
theorem closure_induction' (s : Set M) {p : ∀ x, x ∈ closure s → Prop}
    (Hs : ∀ (x) (h : x ∈ s), p x (subset_closure h)) (H1 : p 1 (one_mem _))
    (Hmul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem hx hy)) {x} (hx : x ∈ closure s) :
    p x hx := by
  refine' Exists.elim _ fun (hx : x ∈ closure s) (hc : p x hx) => hc
  exact
    closure_induction hx (fun x hx => ⟨_, Hs x hx⟩) ⟨_, H1⟩ fun x y ⟨hx', hx⟩ ⟨hy', hy⟩ =>
      ⟨_, Hmul _ _ _ _ hx hy⟩
#align submonoid.closure_induction' Submonoid.closure_induction'

/-- An induction principle for closure membership for predicates with two arguments.  -/
@[elab_as_elim,
  to_additive
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

/-- If `s` is a dense set in a monoid `M`, `Submonoid.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, verify `p 1`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[elab_as_elim,
  to_additive
      "If `s` is a dense set in an additive monoid `M`, `AddSubmonoid.closure s = ⊤`, then in
      order to prove that some predicate `p` holds for all `x : M` it suffices to verify `p x` for
      `x ∈ s`, verify `p 0`, and verify that `p x` and `p y` imply `p (x + y)`."]
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure s = ⊤) (Hs : ∀ x ∈ s, p x)
    (H1 : p 1) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x := by
  have : ∀ x ∈ closure s, p x := fun x hx => closure_induction hx Hs H1 Hmul
  simpa [hs] using this x
#align submonoid.dense_induction Submonoid.dense_induction

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive "`closure` forms a Galois insertion with the coercion to set."]
protected def gi : GaloisInsertion (@closure M _) SetLike.coe where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl
#align submonoid.gi Submonoid.gi

variable {M}

/-- Closure of a submonoid `S` equals `S`. -/
@[simp, to_additive "Additive closure of an additive submonoid `S` equals `S`"]
theorem closure_eq : closure (S : Set M) = S :=
  (Submonoid.gi M).l_u_eq S
#align submonoid.closure_eq Submonoid.closure_eq

@[simp, to_additive]
theorem closure_empty : closure (∅ : Set M) = ⊥ :=
  (Submonoid.gi M).gc.l_bot
#align submonoid.closure_empty Submonoid.closure_empty

@[simp, to_additive]
theorem closure_univ : closure (univ : Set M) = ⊤ :=
  @coe_top M _ ▸ closure_eq ⊤
#align submonoid.closure_univ Submonoid.closure_univ

@[to_additive]
theorem closure_union (s t : Set M) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Submonoid.gi M).gc.l_sup
#align submonoid.closure_union Submonoid.closure_union

@[to_additive]
theorem closure_unionᵢ {ι} (s : ι → Set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Submonoid.gi M).gc.l_supᵢ
#align submonoid.closure_Union Submonoid.closure_unionᵢ

@[simp, to_additive]
theorem closure_singleton_le_iff_mem (m : M) (p : Submonoid M) : closure {m} ≤ p ↔ m ∈ p := by
  rw [closure_le, singleton_subset_iff, SetLike.mem_coe]
#align submonoid.closure_singleton_le_iff_mem Submonoid.closure_singleton_le_iff_mem

@[to_additive]
theorem mem_supᵢ {ι : Sort _} (p : ι → Submonoid M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← closure_singleton_le_iff_mem, le_supᵢ_iff]
  simp only [closure_singleton_le_iff_mem]
#align submonoid.mem_supr Submonoid.mem_supᵢ

@[to_additive]
theorem supᵢ_eq_closure {ι : Sort _} (p : ι → Submonoid M) :
    (⨆ i, p i) = Submonoid.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Submonoid.closure_unionᵢ, Submonoid.closure_eq]
#align submonoid.supr_eq_closure Submonoid.supᵢ_eq_closure

@[to_additive]
theorem disjoint_def {p₁ p₂ : Submonoid M} : Disjoint p₁ p₂ ↔ ∀ {x : M}, x ∈ p₁ → x ∈ p₂ → x = 1 :=
  by simp_rw [disjoint_iff_inf_le, SetLike.le_def, mem_inf, and_imp, mem_bot]
#align submonoid.disjoint_def Submonoid.disjoint_def

@[to_additive]
theorem disjoint_def' {p₁ p₂ : Submonoid M} :
    Disjoint p₁ p₂ ↔ ∀ {x y : M}, x ∈ p₁ → y ∈ p₂ → x = y → x = 1 :=
  disjoint_def.trans ⟨fun h _ _ hx hy hxy => h hx <| hxy.symm ▸ hy, fun h _ hx hx' => h hx hx' rfl⟩
#align submonoid.disjoint_def' Submonoid.disjoint_def'

end Submonoid

namespace MonoidHom

variable [MulOneClass N]

open Submonoid

/-- The submonoid of elements `x : M` such that `f x = g x` -/
@[to_additive "The additive submonoid of elements `x : M` such that `f x = g x`"]
def eqLocus (f g : M →* N) :
    Submonoid M where
  carrier := { x | f x = g x }
  one_mem' := by rw [Set.mem_setOf_eq, f.map_one, g.map_one]
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]
#align monoid_hom.eq_mlocus MonoidHom.eqLocus

@[simp, to_additive]
theorem eqLocus_same (f : M →* N) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _
#align monoid_hom.eq_mlocus_same MonoidHom.eqLocus_same

/-- If two monoid homomorphisms are equal on a set, then they are equal on its submonoid closure. -/
@[to_additive
      "If two monoid homomorphisms are equal on a set, then they are equal on its submonoid
      closure."]
theorem eqOn_closure {f g : M →* N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from closure_le.2 h
#align monoid_hom.eq_on_mclosure MonoidHom.eqOn_closure

@[to_additive]
theorem eq_of_eqOn_top {f g : M →* N} (h : Set.EqOn f g (⊤ : Submonoid M)) : f = g :=
  ext fun _ => h trivial
#align monoid_hom.eq_of_eq_on_mtop MonoidHom.eq_of_eqOn_top

@[to_additive]
theorem eq_of_eqOn_dense {s : Set M} (hs : closure s = ⊤) {f g : M →* N} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_top <| hs ▸ eqOn_closure h
#align monoid_hom.eq_of_eq_on_mdense MonoidHom.eq_of_eqOn_dense

end MonoidHom

end NonAssoc

section Assoc

variable [Monoid M] [Monoid N] {s : Set M}

section IsUnit

/-- The submonoid consisting of the units of a monoid -/
@[to_additive "The additive submonoid consisting of the additive units of an additive monoid"]
def IsUnit.submonoid (M : Type _) [Monoid M] :
    Submonoid M where
  carrier := setOf IsUnit
  one_mem' := by simp only [isUnit_one, Set.mem_setOf_eq]
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at *
    exact IsUnit.mul ha hb
#align is_unit.submonoid IsUnit.submonoid

@[to_additive]
theorem IsUnit.mem_submonoid_iff {M : Type _} [Monoid M] (a : M) :
    a ∈ IsUnit.submonoid M ↔ IsUnit a := by
  change a ∈ setOf IsUnit ↔ IsUnit a
  rw [Set.mem_setOf_eq]
#align is_unit.mem_submonoid_iff IsUnit.mem_submonoid_iff

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
def ofClosureEqTopLeft {M N} [Monoid M] [Monoid N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (h1 : f 1 = 1) (hmul : ∀ x ∈ s, ∀ (y), f (x * y) = f x * f y) :
    M →* N where
  toFun := f
  map_one' := h1
  map_mul' x :=
    (dense_induction (p := _) x hs hmul fun y => by rw [one_mul, h1, one_mul]) fun a b ha hb y => by
      rw [mul_assoc, ha, ha, hb, mul_assoc]
#align monoid_hom.of_mclosure_eq_top_left MonoidHom.ofClosureEqTopLeft

@[simp, norm_cast, to_additive]
theorem coe_ofClosureEqTopLeft (f : M → N) (hs : closure s = ⊤) (h1 hmul) :
    ⇑(ofClosureEqTopLeft f hs h1 hmul) = f :=
  rfl
#align monoid_hom.coe_of_mclosure_eq_top_left MonoidHom.coe_ofClosureEqTopLeft

/-- Let `s` be a subset of a monoid `M` such that the closure of `s` is the whole monoid.
Then `MonoidHom.ofClosureEqTopRight` defines a monoid homomorphism from `M` asking for
a proof of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive
      "Let `s` be a subset of an additive monoid `M` such that the closure of `s` is
      the whole monoid. Then `AddMonoidHom.ofClosureEqTopRight` defines an additive monoid
      homomorphism from `M` asking for a proof of `f (x + y) = f x + f y` only for `y ∈ s`. "]
def ofClosureEqTopRight {M N} [Monoid M] [Monoid N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (h1 : f 1 = 1) (hmul : ∀ (x), ∀ y ∈ s, f (x * y) = f x * f y) :
    M →* N where
  toFun := f
  map_one' := h1
  map_mul' x y :=
    dense_induction y hs (fun y hy x => hmul x y hy) (by simp [h1])
      (fun y₁ y₂ (h₁ : ∀ x, f _ = f _ * f _) (h₂ : ∀ x, f _ = f _ * f _) x => by
        simp [← mul_assoc, h₁, h₂]) x
#align monoid_hom.of_mclosure_eq_top_right MonoidHom.ofClosureEqTopRight

@[simp, norm_cast, to_additive]
theorem coe_ofClosureEqTopRight (f : M → N) (hs : closure s = ⊤) (h1 hmul) :
    ⇑(ofClosureEqTopRight f hs h1 hmul) = f :=
  rfl
#align monoid_hom.coe_of_mclosure_eq_top_right MonoidHom.coe_ofClosureEqTopRight

end MonoidHom

end Assoc
