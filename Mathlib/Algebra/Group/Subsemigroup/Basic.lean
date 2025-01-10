/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky
-/
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Data.Set.Lattice

/-!
# Subsemigroups: `CompleteLattice` structure

This file defines a `CompleteLattice` structure on `Subsemigroup`s,
and define the closure of a set as the minimal subsemigroup that includes this set.

## Main definitions

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

class SetLikeCompleteLattice (L α : Type*) extends CompleteLattice L, SetLike L α where
  le_def' : le =
    @LE.le L (@Preorder.toLE L (@PartialOrder.toPreorder L SetLike.instPartialOrder))
  lt_def' : lt =
    @LT.lt L (@Preorder.toLT L (@PartialOrder.toPreorder L SetLike.instPartialOrder))
  coe_sInf' (s : Set L) : sInf s = InfSet.sInf (SetLike.coe '' s)

namespace SetLike

variable {α L : Type*} [SetLikeCompleteLattice L α]

@[simp, norm_cast]
protected theorem coe_sInf (s : Set L) : ((sInf s : L) : Set α) = ⋂ a ∈ s, ↑a := by
  simpa using SetLikeCompleteLattice.coe_sInf' s

protected theorem mem_sInf {s : Set L} {x : α} : x ∈ sInf s ↔ ∀ a ∈ s, x ∈ a := by
  rw [← SetLike.mem_coe]; simp

variable (L) in
def closure (s : Set α) : L := sInf { l | s ⊆ l }

theorem mem_closure {s : Set α} {x : α} : x ∈ closure L s ↔ ∀ l : L, s ⊆ l → x ∈ l :=
  SetLike.mem_sInf

variable (L) in
open SetLikeCompleteLattice in
def gi_closure : GaloisInsertion (closure L) SetLike.coe :=
  GaloisConnection.toGaloisInsertion
    (fun _ _ =>
      ⟨by rw [le_def']; exact Set.Subset.trans <| fun _ hx => mem_closure.2 fun _ hs => hs hx,
      fun h => sInf_le h⟩)
    fun _ => by rw [le_def']; exact fun _ hx => mem_closure.2 fun _ hs => hs hx

@[simp, aesop safe 20 apply (rule_sets := [SetLike])]
theorem subset_closure {s : Set α} : s ⊆ closure L s := (gi_closure L).gc.le_u_l s

@[aesop unsafe 50% apply (rule_sets := [SetLike])]
theorem mem_closure_of_mem {s : Set α} {x : α} (hx : x ∈ s) : x ∈ closure L s := subset_closure hx

theorem not_mem_of_not_mem_closure {s : Set α} {x : α} (hx : x ∉ closure L s) : x ∉ s :=
  (hx <| subset_closure ·)

@[simp]
theorem closure_le {s : Set α} {l : L} : closure L s ≤ l ↔ s ⊆ l := (gi_closure L).gc.le_iff_le

theorem closure_monotone : Monotone (closure L : Set α → L) := (gi_closure L).gc.monotone_l

@[gcongr]
theorem closure_mono ⦃s t : Set α⦄ (h : s ⊆ t) : closure L s ≤ closure L t := closure_monotone h

theorem closure_eq_of_le {s : Set α} {l : L} (h₁ : s ⊆ l) (h₂ : l ≤ closure L s) :
    closure L s = l := le_antisymm (closure_le.2 h₁) h₂

@[simp] theorem closure_eq (l : L) : closure L (l : Set α) = l := (gi_closure L).l_u_eq l

@[simp] theorem closure_empty : closure L (∅ : Set α) = ⊥ := (gi_closure L).gc.l_bot

@[simp] theorem closure_univ : closure L (Set.univ : Set α) = ⊤ := (gi_closure L).l_top

theorem closure_union (s t : Set α) : closure L (s ∪ t) = closure L s ⊔ closure L t :=
  (gi_closure L).gc.l_sup

theorem closure_iUnion {ι} (s : ι → Set α) : closure L (⋃ i, s i) = ⨆ i, closure L (s i) :=
  (gi_closure L).gc.l_iSup

theorem closure_singleton_le_iff_mem (x : α) (l : L) : closure L {x} ≤ l ↔ x ∈ l := by
  rw [closure_le, Set.singleton_subset_iff, SetLike.mem_coe]

theorem mem_iSup {ι : Sort*} (l : ι → L) {x : α} :
    (x ∈ ⨆ i, l i) ↔ ∀ m, (∀ i, l i ≤ m) → x ∈ m := by
  rw [← closure_singleton_le_iff_mem, le_iSup_iff]
  simp only [closure_singleton_le_iff_mem]

theorem iSup_eq_closure {ι : Sort*} (l : ι → L) :
    ⨆ i, l i = closure L (⋃ i, (l i : Set α)) := by
  simp_rw [closure_iUnion, closure_eq]

end SetLike

-- Only needed for notation
variable {M : Type*} {N : Type*}

section NonAssoc

variable [Mul M] {s : Set M}

namespace Subsemigroup

variable (S : Subsemigroup M)

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

@[to_additive]
theorem mem_sInf {S : Set (Subsemigroup M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[to_additive]
theorem mem_iInf {ι : Sort*} {S : ι → Subsemigroup M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[to_additive (attr := simp, norm_cast)]
theorem coe_iInf {ι : Sort*} {S : ι → Subsemigroup M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

/-- subsemigroups of a monoid form a complete lattice. -/
@[to_additive "The `AddSubsemigroup`s of an `AddMonoid` form a complete lattice."]
instance : CompleteLattice (Subsemigroup M) :=
  { completeLatticeOfInf (Subsemigroup M) fun _ =>
      IsGLB.of_image OrderedSetLike.coe_subset_coe isGLB_biInf with
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
instance : SetLikeCompleteLattice (Subsemigroup M) M where
  le_def' := rfl
  lt_def' := rfl
  coe_sInf' := by simp

@[to_additive]
abbrev closure : Set M → Subsemigroup M := SetLike.closure <| Subsemigroup M

@[to_additive]
theorem mem_closure {x : M} : x ∈ closure s ↔ ∀ S : Subsemigroup M, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The subsemigroup generated by a set includes the set. -/
@[to_additive (attr := simp, aesop safe 20 apply (rule_sets := [SetLike]))
  "The `AddSubsemigroup` generated by a set includes the set."]
theorem subset_closure : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

@[to_additive]
theorem not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

variable {S}

open Set SetLike

@[to_additive]
theorem closure_induction {p : (x : M) → x ∈ closure s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_closure h))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy)) {x} (hx : x ∈ closure s) :
    p x hx :=
  let S : Subsemigroup M :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩ }
  Exists.elim (closure_le (s := s) (l := S) |>.mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx)
    fun _ ↦ id

@[deprecated closure_induction (since := "2024-10-09")]
alias closure_induction' := closure_induction

/-- An induction principle for closure membership for predicates with two arguments. -/
@[to_additive (attr := elab_as_elim) "An induction principle for additive closure membership for
  predicates with two arguments."]
theorem closure_induction₂ {p : (x y : M) → x ∈ closure s → y ∈ closure s → Prop}
    (mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (subset_closure hx) (subset_closure hy))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p z x hz hx → p z y hz hy → p z (x * y) hz (mul_mem hx hy))
    {x y : M} (hx : x ∈ closure s) (hy : y ∈ closure s) : p x y hx hy := by
  induction hx using closure_induction with
  | mem z hz => induction hy using closure_induction with
    | mem _ h => exact mem _ _ hz h
    | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ hy h₁ h₂

/-- If `s` is a dense set in a magma `M`, `Subsemigroup.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[to_additive (attr := elab_as_elim) "If `s` is a dense set in an additive monoid `M`,
  `AddSubsemigroup.closure s = ⊤`, then in order to prove that some predicate `p` holds
  for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify that `p x` and `p y` imply
  `p (x + y)`."]
theorem dense_induction {p : M → Prop} (s : Set M) (closure : closure s = ⊤)
    (mem : ∀ x ∈ s, p x) (mul : ∀ x y, p x → p y → p (x * y)) (x : M) :
    p x := by
  induction closure.symm ▸ mem_top x using closure_induction with
  | mem _ h => exact mem _ h
  | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂

/- The argument `s : Set M` is explicit in `Subsemigroup.dense_induction` because the type of the
induction variable, namely `x : M`, does not reference `x`. Making `s` explicit allows the user
to apply the induction principle while deferring the proof of `closure s = ⊤` without creating
metavariables, as in the following example. -/
example {p : M → Prop} (s : Set M) (closure : closure s = ⊤)
    (mem : ∀ x ∈ s, p x) (mul : ∀ x y, p x → p y → p (x * y)) (x : M) :
    p x := by
  induction x using dense_induction s with
  | closure => exact closure
  | mem x hx => exact mem x hx
  | mul _ _ h₁ h₂ => exact mul _ _ h₁ h₂

end Subsemigroup

namespace MulHom

variable [Mul N]

open Subsemigroup

/-- If two mul homomorphisms are equal on a set, then they are equal on its subsemigroup closure. -/
@[to_additive "If two add homomorphisms are equal on a set,
  then they are equal on its additive subsemigroup closure."]
theorem eqOn_closure {f g : M →ₙ* N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from SetLike.closure_le.2 h

@[to_additive]
theorem eq_of_eqOn_dense {s : Set M} (hs : closure s = ⊤) {f g : M →ₙ* N} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_top <| hs ▸ eqOn_closure h

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
    dense_induction _ hs (fun y hy x => hmul x y hy)
      (fun y₁ y₂ h₁ h₂ x => by simp only [← mul_assoc, h₁, h₂]) y x

/-- Let `s` be a subset of an additive semigroup `M` such that the closure of `s` is the whole
semigroup.  Then `AddHom.ofDense` defines an additive homomorphism from `M` asking for a proof
of `f (x + y) = f x + f y` only for `y ∈ s`. -/
add_decl_doc AddHom.ofDense

@[to_additive (attr := simp, norm_cast)]
theorem coe_ofDense [Semigroup M] [Semigroup N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (hmul) : (ofDense f hs hmul : M → N) = f :=
  rfl

end MulHom

end Assoc
