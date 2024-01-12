/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.BundledSet.Weaken
import Mathlib.Data.BundledSet.CompleteLattice.Basic

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


-- Only needed for notation
variable {M : Type*} {N : Type*} {A : Type*}

section NonAssoc

variable [Mul M] {s : Set M}

variable [Add A] {t : Set A}

structure IsAddSubsemigroup (s : Set A) : Prop where
  add_mem {a b : A} : a ∈ s → b ∈ s → a + b ∈ s

@[to_additive (attr := mk_eq)]
structure IsSubsemigroup (s : Set M) : Prop where
  mul_mem {a b : M} : a ∈ s → b ∈ s → a * b ∈ s

attribute [to_additive existing] isSubsemigroup_eq

/-- A subsemigroup is closed under multiplication. -/
@[to_additive "An additive subsemigroup is closed under addition."]
theorem BundledSet.mul_mem {p : Set M → Prop} [Implies p IsSubsemigroup] {s : BundledSet M p} {a b}
    (ha : a ∈ s) (hb : b ∈ s) : a * b ∈ s :=
  IsSubsemigroup.mul_mem (BundledSet.Implies.implies s s.2) ha hb

attribute [aesop safe apply (rule_sets [SetLike])] BundledSet.mul_mem BundledSet.add_mem

/-- A subsemigroup of a magma `M` is a subset closed under multiplication. -/
@[to_additive (attr := reducible)
  "An additive subsemigroup of an additive magma `M` is a subset closed under addition."]
def Subsemigroup (M : Type*) [Mul M] := BundledSet M IsSubsemigroup
#align subsemigroup Subsemigroup
#align add_subsemigroup AddSubsemigroup


#align subsemigroup.mem_carrier BundledSet.mem_carrier
#align add_subsemigroup.mem_carrier BundledSet.mem_carrier
#align subsemigroup.mem_mk BundledSet.mem_mk
#align add_subsemigroup.mem_mk BundledSet.mem_mk
#align subsemigroup.coe_set_mk BundledSet.carrier_mk
#align add_subsemigroup.coe_set_mk BundledSet.carrier_mk
#align subsemigroup.mk_le_mk BundledSet.mk_le_mk
#align add_subsemigroup.mk_le_mk BundledSet.mk_le_mk
#align subsemigroup.ext BundledSet.ext
#align add_subsemigroup.ext BundledSet.ext
#align subsemigroup.copy BundledSet.copy
#align add_subsemigroup.copy BundledSet.copy
#align subsemigroup.coe_copy BundledSet.copy_carrier
#align add_subsemigroup.coe_copy BundledSet.copy_carrier
#align subsemigroup.copy_eq BundledSet.copy_eq
#align add_subsemigroup.copy_eq BundledSet.copy_eq
#align subsemigroup.mul_mem BundledSet.mul_mem
#align add_subsemigroup.add_mem BundledSet.add_mem

namespace Subsemigroup

open BundledSet

@[to_additive]
instance : SetInterPred M IsSubsemigroup := by simp only [isSubsemigroup_eq]; infer_instance

#align subsemigroup.mem_top BundledSet.mem_top
#align add_subsemigroup.mem_top BundledSet.mem_top
#align subsemigroup.coe_top BundledSet.top_carrier
#align add_subsemigroup.coe_top BundledSet.top_carrier
#align subsemigroup.coe_inf BundledSet.inf_carrier
#align add_subsemigroup.coe_inf BundledSet.inf_carrier
#align subsemigroup.mem_inf BundledSet.mem_inf
#align add_subsemigroup.mem_inf BundledSet.mem_inf
#align subsemigroup.coe_Inf BundledSet.sInf_carrier
#align add_subsemigroup.coe_Inf BundledSet.sInf_carrier
#align subsemigroup.mem_Inf BundledSet.mem_sInf
#align add_subsemigroup.mem_Inf BundledSet.mem_sInf
#align subsemigroup.mem_infi BundledSet.mem_iInf
#align add_subsemigroup.mem_infi BundledSet.mem_iInf
#align subsemigroup.coe_infi BundledSet.iInf_carrier
#align add_subsemigroup.coe_infi BundledSet.iInf_carrier

@[to_additive] instance : BotPred M IsSubsemigroup ∅ := .mk_empty ⟨False.elim⟩

@[to_additive] instance : SupPred M IsSubsemigroup (supOfSetInter M IsSubsemigroup) :=
  .of_setInterPred _ _

@[to_additive] instance : CompleteLattice (BundledSet M IsSubsemigroup) :=
  completeLatticeOfBotSupSetInter _ _

#align subsemigroup.not_mem_bot BundledSet.not_mem_bot
#align add_subsemigroup.not_mem_bot BundledSet.not_mem_bot
#align subsemigroup.coe_bot BundledSet.bot_carrier
#align add_subsemigroup.coe_bot BundledSet.bot_carrier

@[to_additive]
instance : Inhabited (Subsemigroup M) :=
  ⟨⊥⟩

@[to_additive (attr := simp)]
theorem subsingleton_iff_isEmpty : Subsingleton (Subsemigroup M) ↔ IsEmpty M := by
  simp [BundledSet.subsingleton_iff, @eq_comm _ ∅]

@[to_additive (attr := simp)]
theorem nontrivial_iff_nonempty : Nontrivial (Subsemigroup M) ↔ Nonempty M := by
  simp [BundledSet.nontrivial_iff, @eq_comm _ ∅]

@[to_additive]
instance [Nonempty M] : Nontrivial (Subsemigroup M) := nontrivial_iff_nonempty.2 ‹_›

@[to_additive]
instance [IsEmpty M] : Subsingleton (Subsemigroup M) := by simpa

-- Use `subsingleton_iff_isEmpty` instead
#noalign subsemigroup.subsingleton_of_subsingleton
#noalign add_subsemigroup.subsingleton_of_subsingleton

/-- The `Subsemigroup` generated by a set. -/
@[to_additive (attr := reducible) "The `AddSubsemigroup` generated by a set"]
def closure : Set M → Subsemigroup M := BundledSet.closure IsSubsemigroup
#align subsemigroup.closure Subsemigroup.closure
#align add_subsemigroup.closure AddSubsemigroup.closure

#align subsemigroup.mem_closure BundledSet.mem_closure
#align add_subsemigroup.mem_closure BundledSet.mem_closure
#align subsemigroup.subset_closure BundledSet.subset_closure
#align add_subsemigroup.subset_closure BundledSet.subset_closure
#align subsemigroup.not_mem_of_not_mem_closure BundledSet.not_mem_of_not_mem_closure
#align add_subsemigroup.not_mem_of_not_mem_closure BundledSet.not_mem_of_not_mem_closure
#align subsemigroup.closure_le BundledSet.closure_le
#align add_subsemigroup.closure_le BundledSet.closure_le
#align subsemigroup.closure_mono BundledSet.closure_mono
#align add_subsemigroup.closure_mono BundledSet.closure_mono
#align subsemigroup.closure_eq_of_le BundledSet.closure_eq_of_le
#align add_subsemigroup.closure_eq_of_le BundledSet.closure_eq_of_le

variable (S : Subsemigroup M)

open Set

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[to_additive (attr := elab_as_elim) "An induction principle for additive closure membership. If `p`
  holds for all elements of `s`, and is preserved under addition, then `p` holds for all
  elements of the additive closure of `s`."]
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure s) (Hs : ∀ x ∈ s, p x)
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (closure_le (t := ⟨p, ⟨Hmul _ _⟩⟩)).2 Hs h
#align subsemigroup.closure_induction Subsemigroup.closure_induction
#align add_subsemigroup.closure_induction AddSubsemigroup.closure_induction

/-- A dependent version of `Subsemigroup.closure_induction`.  -/
@[to_additive (attr := elab_as_elim) "A dependent version of `AddSubsemigroup.closure_induction`. "]
theorem closure_induction' (s : Set M) {p : ∀ x, x ∈ closure s → Prop}
    (Hs : ∀ (x) (h : x ∈ s), p x (subset_closure h))
    (Hmul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem hx hy)) {x} (hx : x ∈ closure s) :
    p x hx := by
  refine' Exists.elim _ fun (hx : x ∈ closure s) (hc : p x hx) => hc
  exact
    closure_induction hx (fun x hx => ⟨_, Hs x hx⟩) fun x y ⟨hx', hx⟩ ⟨hy', hy⟩ =>
      ⟨_, Hmul _ _ _ _ hx hy⟩
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
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure s = ⊤) (Hs : ∀ x ∈ s, p x)
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x := by
  have : ∀ x ∈ closure s, p x := fun x hx => closure_induction hx Hs Hmul
  simpa [hs] using this x
#align subsemigroup.dense_induction Subsemigroup.dense_induction
#align add_subsemigroup.dense_induction AddSubsemigroup.dense_induction

#align subsemigroup.gi BundledSet.gi
#align add_subsemigroup.gi BundledSet.gi
#align subsemigroup.closure_eq BundledSet.closure_eq
#align add_subsemigroup.closure_eq BundledSet.closure_eq
#align subsemigroup.closure_empty BundledSet.closure_empty
#align add_subsemigroup.closure_empty BundledSet.closure_empty
#align subsemigroup.closure_univ BundledSet.closure_univ
#align add_subsemigroup.closure_univ BundledSet.closure_univ
#align subsemigroup.closure_union BundledSet.closure_union
#align add_subsemigroup.closure_union BundledSet.closure_union
#align subsemigroup.closure_Union BundledSet.closure_iUnion
#align add_subsemigroup.closure_Union BundledSet.closure_iUnion
#align subsemigroup.closure_singleton_le_iff_mem BundledSet.closure_singleton_le
#align add_subsemigroup.closure_singleton_le_iff_mem BundledSet.closure_singleton_le
#align subsemigroup.mem_supr BundledSet.mem_iSup
#align add_subsemigroup.mem_supr BundledSet.mem_iSup
#align subsemigroup.supr_eq_closure BundledSet.iSup_eq_closure
#align add_subsemigroup.supr_eq_closure BundledSet.iSup_eq_closure

end Subsemigroup

namespace MulHom

variable [Mul N]

open Subsemigroup

/-- The subsemigroup of elements `x : M` such that `f x = g x` -/
@[to_additive "The additive subsemigroup of elements `x : M` such that `f x = g x`"]
def eqLocus (f g : M →ₙ* N) : Subsemigroup M where
  carrier := { x | f x = g x }
  prop := ⟨fun (hx : _ = _) (hy : _ = _) => by simp [*]⟩
#align mul_hom.eq_mlocus MulHom.eqLocus
#align add_hom.eq_mlocus AddHom.eqLocus

/-- If two mul homomorphisms are equal on a set, then they are equal on its subsemigroup closure. -/
@[to_additive "If two add homomorphisms are equal on a set,
  then they are equal on its additive subsemigroup closure."]
theorem eqOn_closure {f g : M →ₙ* N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from BundledSet.closure_le.2 h
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
