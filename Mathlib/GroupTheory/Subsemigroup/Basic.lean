/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky

! This file was ported from Lean 3 source module group_theory.subsemigroup.basic
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Data.Set.Lattice
import Mathbin.Data.SetLike.Basic

/-!
# Subsemigroups: definition and `complete_lattice` structure

This file defines bundled multiplicative and additive subsemigroups. We also define
a `complete_lattice` structure on `subsemigroup`s,
and define the closure of a set as the minimal subsemigroup that includes this set.

## Main definitions

* `subsemigroup M`: the type of bundled subsemigroup of a magma `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : set M)`.
* `add_subsemigroup M` : the type of bundled subsemigroups of an additive magma `M`.

For each of the following definitions in the `subsemigroup` namespace, there is a corresponding
definition in the `add_subsemigroup` namespace.

* `subsemigroup.copy` : copy of a subsemigroup with `carrier` replaced by a set that is equal but
  possibly not definitionally equal to the carrier of the original `subsemigroup`.
* `subsemigroup.closure` :  semigroup closure of a set, i.e.,
  the least subsemigroup that includes the set.
* `subsemigroup.gi` : `closure : set M → subsemigroup M` and coercion `coe : subsemigroup M → set M`
  form a `galois_insertion`;

## Implementation notes

Subsemigroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subsemigroup's underlying set.

Note that `subsemigroup M` does not actually require `semigroup M`,
instead requiring only the weaker `has_mul M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers.

## Tags
subsemigroup, subsemigroups
-/


-- Only needed for notation
-- Only needed for notation
variable {M : Type _} {N : Type _}

variable {A : Type _}

section NonAssoc

variable [Mul M] {s : Set M}

variable [Add A] {t : Set A}

/-- `mul_mem_class S M` says `S` is a type of subsets `s ≤ M` that are closed under `(*)` -/
class MulMemClass (S : Type _) (M : outParam <| Type _) [Mul M] [SetLike S M] where
  mul_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
#align mul_mem_class MulMemClass

export MulMemClass (mul_mem)

/-- `add_mem_class S M` says `S` is a type of subsets `s ≤ M` that are closed under `(+)` -/
class AddMemClass (S : Type _) (M : outParam <| Type _) [Add M] [SetLike S M] where
  add_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a + b ∈ s
#align add_mem_class AddMemClass

export AddMemClass (add_mem)

attribute [to_additive] MulMemClass

/-- A subsemigroup of a magma `M` is a subset closed under multiplication. -/
structure Subsemigroup (M : Type _) [Mul M] where
  carrier : Set M
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
#align subsemigroup Subsemigroup

/-- An additive subsemigroup of an additive magma `M` is a subset closed under addition. -/
structure AddSubsemigroup (M : Type _) [Add M] where
  carrier : Set M
  add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier
#align add_subsemigroup AddSubsemigroup

attribute [to_additive AddSubsemigroup] Subsemigroup

namespace Subsemigroup

@[to_additive]
instance : SetLike (Subsemigroup M) M :=
  ⟨Subsemigroup.carrier, fun p q h => by cases p <;> cases q <;> congr ⟩

@[to_additive]
instance : MulMemClass (Subsemigroup M) M where mul_mem := Subsemigroup.mul_mem'

/-- See Note [custom simps projection] -/
@[to_additive " See Note [custom simps projection]"]
def Simps.coe (S : Subsemigroup M) : Set M :=
  S
#align subsemigroup.simps.coe Subsemigroup.Simps.coe

initialize_simps_projections Subsemigroup (carrier → coe)

initialize_simps_projections AddSubsemigroup (carrier → coe)

@[simp, to_additive]
theorem mem_carrier {s : Subsemigroup M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align subsemigroup.mem_carrier Subsemigroup.mem_carrier

@[simp, to_additive]
theorem mem_mk {s : Set M} {x : M} (h_mul) : x ∈ mk s h_mul ↔ x ∈ s :=
  Iff.rfl
#align subsemigroup.mem_mk Subsemigroup.mem_mk

@[simp, to_additive]
theorem coe_set_mk {s : Set M} (h_mul) : (mk s h_mul : Set M) = s :=
  rfl
#align subsemigroup.coe_set_mk Subsemigroup.coe_set_mk

@[simp, to_additive]
theorem mk_le_mk {s t : Set M} (h_mul) (h_mul') : mk s h_mul ≤ mk t h_mul' ↔ s ⊆ t :=
  Iff.rfl
#align subsemigroup.mk_le_mk Subsemigroup.mk_le_mk

/-- Two subsemigroups are equal if they have the same elements. -/
@[ext, to_additive "Two `add_subsemigroup`s are equal if they have the same elements."]
theorem ext {S T : Subsemigroup M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align subsemigroup.ext Subsemigroup.ext

/-- Copy a subsemigroup replacing `carrier` with a set that is equal to it. -/
@[to_additive "Copy an additive subsemigroup replacing `carrier` with a set that is equal to\nit."]
protected def copy (S : Subsemigroup M) (s : Set M) (hs : s = S) :
    Subsemigroup M where 
  carrier := s
  mul_mem' _ _ := hs.symm ▸ S.mul_mem'
#align subsemigroup.copy Subsemigroup.copy

variable {S : Subsemigroup M}

@[simp, to_additive]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl
#align subsemigroup.coe_copy Subsemigroup.coe_copy

@[to_additive]
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align subsemigroup.copy_eq Subsemigroup.copy_eq

variable (S)

/-- A subsemigroup is closed under multiplication. -/
@[to_additive "An `add_subsemigroup` is closed under addition."]
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  Subsemigroup.mul_mem' S
#align subsemigroup.mul_mem Subsemigroup.mul_mem

/-- The subsemigroup `M` of the magma `M`. -/
@[to_additive "The additive subsemigroup `M` of the magma `M`."]
instance : Top (Subsemigroup M) :=
  ⟨{  carrier := Set.univ
      mul_mem' := fun _ _ _ _ => Set.mem_univ _ }⟩

/-- The trivial subsemigroup `∅` of a magma `M`. -/
@[to_additive "The trivial `add_subsemigroup` `∅` of an additive magma `M`."]
instance : Bot (Subsemigroup M) :=
  ⟨{  carrier := ∅
      mul_mem' := fun a b => by simp }⟩

@[to_additive]
instance : Inhabited (Subsemigroup M) :=
  ⟨⊥⟩

@[to_additive]
theorem not_mem_bot {x : M} : x ∉ (⊥ : Subsemigroup M) :=
  Set.not_mem_empty x
#align subsemigroup.not_mem_bot Subsemigroup.not_mem_bot

@[simp, to_additive]
theorem mem_top (x : M) : x ∈ (⊤ : Subsemigroup M) :=
  Set.mem_univ x
#align subsemigroup.mem_top Subsemigroup.mem_top

@[simp, to_additive]
theorem coe_top : ((⊤ : Subsemigroup M) : Set M) = Set.univ :=
  rfl
#align subsemigroup.coe_top Subsemigroup.coe_top

@[simp, to_additive]
theorem coe_bot : ((⊥ : Subsemigroup M) : Set M) = ∅ :=
  rfl
#align subsemigroup.coe_bot Subsemigroup.coe_bot

/-- The inf of two subsemigroups is their intersection. -/
@[to_additive "The inf of two `add_subsemigroup`s is their intersection."]
instance : HasInf (Subsemigroup M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ ∩ S₂
      mul_mem' := fun _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[simp, to_additive]
theorem coe_inf (p p' : Subsemigroup M) : ((p ⊓ p' : Subsemigroup M) : Set M) = p ∩ p' :=
  rfl
#align subsemigroup.coe_inf Subsemigroup.coe_inf

@[simp, to_additive]
theorem mem_inf {p p' : Subsemigroup M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
#align subsemigroup.mem_inf Subsemigroup.mem_inf

@[to_additive]
instance : InfSet (Subsemigroup M) :=
  ⟨fun s =>
    { carrier := ⋂ t ∈ s, ↑t
      mul_mem' := fun x y hx hy =>
        Set.mem_bInter fun i h =>
          i.mul_mem (by apply Set.mem_Inter₂.1 hx i h) (by apply Set.mem_Inter₂.1 hy i h) }⟩

@[simp, norm_cast, to_additive]
theorem coe_Inf (S : Set (Subsemigroup M)) : ((infₛ S : Subsemigroup M) : Set M) = ⋂ s ∈ S, ↑s :=
  rfl
#align subsemigroup.coe_Inf Subsemigroup.coe_Inf

@[to_additive]
theorem mem_Inf {S : Set (Subsemigroup M)} {x : M} : x ∈ infₛ S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_Inter₂
#align subsemigroup.mem_Inf Subsemigroup.mem_Inf

@[to_additive]
theorem mem_infi {ι : Sort _} {S : ι → Subsemigroup M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [infi, mem_Inf, Set.forall_range_iff]
#align subsemigroup.mem_infi Subsemigroup.mem_infi

@[simp, norm_cast, to_additive]
theorem coe_infi {ι : Sort _} {S : ι → Subsemigroup M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [infi, coe_Inf, Set.bInter_range]
#align subsemigroup.coe_infi Subsemigroup.coe_infi

/-- subsemigroups of a monoid form a complete lattice. -/
@[to_additive "The `add_subsemigroup`s of an `add_monoid` form a complete lattice."]
instance : CompleteLattice (Subsemigroup M) :=
  { (completeLatticeOfInf (Subsemigroup M)) fun s =>
      IsGLB.of_image (fun S T => show (S : Set M) ≤ T ↔ S ≤ T from SetLike.coe_subset_coe)
        is_glb_binfi with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun S x hx => (not_mem_bot hx).elim
    top := ⊤
    le_top := fun S x hx => mem_top x
    inf := (· ⊓ ·)
    inf := InfSet.infₛ
    le_inf := fun a b c ha hb x hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun a b x => And.left
    inf_le_right := fun a b x => And.right }

@[simp, to_additive]
theorem subsingleton_of_subsingleton [Subsingleton (Subsemigroup M)] : Subsingleton M := by
  constructor <;> intro x y
  have : ∀ a : M, a ∈ (⊥ : Subsemigroup M) := by simp [Subsingleton.elim (⊥ : Subsemigroup M) ⊤]
  exact absurd (this x) not_mem_bot
#align subsemigroup.subsingleton_of_subsingleton Subsemigroup.subsingleton_of_subsingleton

@[to_additive]
instance [hn : Nonempty M] : Nontrivial (Subsemigroup M) :=
  ⟨⟨⊥, ⊤, fun h => by 
      obtain ⟨x⟩ := id hn
      refine' absurd (_ : x ∈ ⊥) not_mem_bot
      simp [h]⟩⟩

/-- The `subsemigroup` generated by a set. -/
@[to_additive "The `add_subsemigroup` generated by a set"]
def closure (s : Set M) : Subsemigroup M :=
  infₛ { S | s ⊆ S }
#align subsemigroup.closure Subsemigroup.closure

@[to_additive]
theorem mem_closure {x : M} : x ∈ closure s ↔ ∀ S : Subsemigroup M, s ⊆ S → x ∈ S :=
  mem_Inf
#align subsemigroup.mem_closure Subsemigroup.mem_closure

/-- The subsemigroup generated by a set includes the set. -/
@[simp, to_additive "The `add_subsemigroup` generated by a set includes the set."]
theorem subset_closure : s ⊆ closure s := fun x hx => mem_closure.2 fun S hS => hS hx
#align subsemigroup.subset_closure Subsemigroup.subset_closure

@[to_additive]
theorem not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align subsemigroup.not_mem_of_not_mem_closure Subsemigroup.not_mem_of_not_mem_closure

variable {S}

open Set

/-- A subsemigroup `S` includes `closure s` if and only if it includes `s`. -/
@[simp,
  to_additive "An additive subsemigroup `S` includes `closure s`\nif and only if it includes `s`"]
theorem closure_le : closure s ≤ S ↔ s ⊆ S :=
  ⟨Subset.trans subset_closure, fun h => infₛ_le h⟩
#align subsemigroup.closure_le Subsemigroup.closure_le

/-- subsemigroup closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive
      "Additive subsemigroup closure of a set is monotone in its argument: if `s ⊆ t`,\nthen `closure s ≤ closure t`"]
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Subset.trans h subset_closure
#align subsemigroup.closure_mono Subsemigroup.closure_mono

@[to_additive]
theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
  le_antisymm (closure_le.2 h₁) h₂
#align subsemigroup.closure_eq_of_le Subsemigroup.closure_eq_of_le

variable (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_elim,
  to_additive
      "An induction principle for additive closure membership. If `p`\nholds for all elements of `s`, and is preserved under addition, then `p` holds for all\nelements of the additive closure of `s`."]
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure s) (Hs : ∀ x ∈ s, p x)
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨p, Hmul⟩).2 Hs h
#align subsemigroup.closure_induction Subsemigroup.closure_induction

/-- A dependent version of `subsemigroup.closure_induction`.  -/
@[elab_as_elim, to_additive "A dependent version of `add_subsemigroup.closure_induction`. "]
theorem closure_induction' (s : Set M) {p : ∀ x, x ∈ closure s → Prop}
    (Hs : ∀ (x) (h : x ∈ s), p x (subset_closure h))
    (Hmul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem hx hy)) {x} (hx : x ∈ closure s) :
    p x hx := by 
  refine' Exists.elim _ fun (hx : x ∈ closure s) (hc : p x hx) => hc
  exact
    closure_induction hx (fun x hx => ⟨_, Hs x hx⟩) fun x y ⟨hx', hx⟩ ⟨hy', hy⟩ =>
      ⟨_, Hmul _ _ _ _ hx hy⟩
#align subsemigroup.closure_induction' Subsemigroup.closure_induction'

/-- An induction principle for closure membership for predicates with two arguments.  -/
@[elab_as_elim,
  to_additive
      "An induction principle for additive closure membership for\npredicates with two arguments."]
theorem closure_induction₂ {p : M → M → Prop} {x} {y : M} (hx : x ∈ closure s) (hy : y ∈ closure s)
    (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (Hmul_left : ∀ x y z, p x z → p y z → p (x * y) z)
    (Hmul_right : ∀ x y z, p z x → p z y → p z (x * y)) : p x y :=
  closure_induction hx
    (fun x xs => closure_induction hy (Hs x xs) fun z y h₁ h₂ => Hmul_right z _ _ h₁ h₂)
    fun x z h₁ h₂ => Hmul_left _ _ _ h₁ h₂
#align subsemigroup.closure_induction₂ Subsemigroup.closure_induction₂

/-- If `s` is a dense set in a magma `M`, `subsemigroup.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[elab_as_elim,
  to_additive
      "If `s` is a dense set in an additive monoid `M`,\n`add_subsemigroup.closure s = ⊤`, then in order to prove that some predicate `p` holds\nfor all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify that `p x` and `p y` imply\n`p (x + y)`."]
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure s = ⊤) (Hs : ∀ x ∈ s, p x)
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x := by
  have : ∀ x ∈ closure s, p x := fun x hx => closure_induction hx Hs Hmul
  simpa [hs] using this x
#align subsemigroup.dense_induction Subsemigroup.dense_induction

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive "`closure` forms a Galois insertion with the coercion to set."]
protected def gi :
    GaloisInsertion (@closure M _)
      coe where 
  choice s _ := closure s
  gc s t := closure_le
  le_l_u s := subset_closure
  choice_eq s h := rfl
#align subsemigroup.gi Subsemigroup.gi

variable {M}

/-- Closure of a subsemigroup `S` equals `S`. -/
@[simp, to_additive "Additive closure of an additive subsemigroup `S` equals `S`"]
theorem closure_eq : closure (S : Set M) = S :=
  (Subsemigroup.gi M).l_u_eq S
#align subsemigroup.closure_eq Subsemigroup.closure_eq

@[simp, to_additive]
theorem closure_empty : closure (∅ : Set M) = ⊥ :=
  (Subsemigroup.gi M).gc.l_bot
#align subsemigroup.closure_empty Subsemigroup.closure_empty

@[simp, to_additive]
theorem closure_univ : closure (univ : Set M) = ⊤ :=
  @coe_top M _ ▸ closure_eq ⊤
#align subsemigroup.closure_univ Subsemigroup.closure_univ

@[to_additive]
theorem closure_union (s t : Set M) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subsemigroup.gi M).gc.l_sup
#align subsemigroup.closure_union Subsemigroup.closure_union

@[to_additive]
theorem closure_Union {ι} (s : ι → Set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subsemigroup.gi M).gc.l_supr
#align subsemigroup.closure_Union Subsemigroup.closure_Union

@[simp, to_additive]
theorem closure_singleton_le_iff_mem (m : M) (p : Subsemigroup M) : closure {m} ≤ p ↔ m ∈ p := by
  rw [closure_le, singleton_subset_iff, SetLike.mem_coe]
#align subsemigroup.closure_singleton_le_iff_mem Subsemigroup.closure_singleton_le_iff_mem

@[to_additive]
theorem mem_supr {ι : Sort _} (p : ι → Subsemigroup M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← closure_singleton_le_iff_mem, le_supᵢ_iff]
  simp only [closure_singleton_le_iff_mem]
#align subsemigroup.mem_supr Subsemigroup.mem_supr

@[to_additive]
theorem supr_eq_closure {ι : Sort _} (p : ι → Subsemigroup M) :
    (⨆ i, p i) = Subsemigroup.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Subsemigroup.closure_Union, Subsemigroup.closure_eq]
#align subsemigroup.supr_eq_closure Subsemigroup.supr_eq_closure

end Subsemigroup

namespace MulHom

variable [Mul N]

open Subsemigroup

/-- The subsemigroup of elements `x : M` such that `f x = g x` -/
@[to_additive "The additive subsemigroup of elements `x : M` such that `f x = g x`"]
def eqMlocus (f g : M →ₙ* N) :
    Subsemigroup M where 
  carrier := { x | f x = g x }
  mul_mem' x y (hx : _ = _) (hy : _ = _) := by simp [*]
#align mul_hom.eq_mlocus MulHom.eqMlocus

/-- If two mul homomorphisms are equal on a set, then they are equal on its subsemigroup closure. -/
@[to_additive
      "If two add homomorphisms are equal on a set,\nthen they are equal on its additive subsemigroup closure."]
theorem eq_on_mclosure {f g : M →ₙ* N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqMlocus g from closure_le.2 h
#align mul_hom.eq_on_mclosure MulHom.eq_on_mclosure

@[to_additive]
theorem eq_of_eq_on_mtop {f g : M →ₙ* N} (h : Set.EqOn f g (⊤ : Subsemigroup M)) : f = g :=
  ext fun x => h trivial
#align mul_hom.eq_of_eq_on_mtop MulHom.eq_of_eq_on_mtop

@[to_additive]
theorem eq_of_eq_on_mdense {s : Set M} (hs : closure s = ⊤) {f g : M →ₙ* N} (h : s.EqOn f g) :
    f = g :=
  eq_of_eq_on_mtop <| hs ▸ eq_on_mclosure h
#align mul_hom.eq_of_eq_on_mdense MulHom.eq_of_eq_on_mdense

end MulHom

end NonAssoc

section Assoc

namespace MulHom

open Subsemigroup

/-- Let `s` be a subset of a semigroup `M` such that the closure of `s` is the whole semigroup.
Then `mul_hom.of_mdense` defines a mul homomorphism from `M` asking for a proof
of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive]
def ofMdense {M N} [Semigroup M] [Semigroup N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (hmul : ∀ (x), ∀ y ∈ s, f (x * y) = f x * f y) :
    M →ₙ* N where 
  toFun := f
  map_mul' x y :=
    dense_induction y hs (fun y hy x => hmul x y hy)
      (fun y₁ y₂ h₁ h₂ x => by simp only [← mul_assoc, h₁, h₂]) x
#align mul_hom.of_mdense MulHom.ofMdense

/-- Let `s` be a subset of an additive semigroup `M` such that the closure of `s` is the whole
semigroup.  Then `add_hom.of_mdense` defines an additive homomorphism from `M` asking for a proof
of `f (x + y) = f x + f y` only for `y ∈ s`. -/
add_decl_doc AddHom.ofMdense

@[simp, norm_cast, to_additive]
theorem coe_of_mdense [Semigroup M] [Semigroup N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (hmul) : (ofMdense f hs hmul : M → N) = f :=
  rfl
#align mul_hom.coe_of_mdense MulHom.coe_of_mdense

end MulHom

end Assoc

