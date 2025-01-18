/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky
-/
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Data.SetLike.Closure

/-!
# Subsemigroups: `CompleteLattice` structure

This file defines a `CompleteLattice` structure on `Subsemigroup`s and closure induction principles
for `Subsemigroup`s.

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

@[to_additive]
instance : IsConcreteSInf (Subsemigroup M) M where
  coe_sInf' := rfl

/-- Subsemigroups of a monoid form a complete lattice. -/
@[to_additive "The `AddSubsemigroup`s of an `AddMonoid` form a complete lattice."]
instance : CompleteLattice (Subsemigroup M) where
  __ := SetLike.toCompleteLattice (Subsemigroup M) M
  bot := ⊥
  bot_le := fun _ _ hx => (Set.not_mem_empty _ hx).elim
  top := ⊤
  le_top := fun _ _ _ => trivial
  inf := (· ⊓ ·)
  le_inf := fun _ _ _ ha hb _ hx => ⟨ha hx, hb hx⟩
  inf_le_left := fun _ _ _ => And.left
  inf_le_right := fun _ _ _ => And.right

@[to_additive]
instance : HasClosure (Subsemigroup M) M := SetLike.toHasClosure (Subsemigroup M) M

/-- Alias for the subsemiring closure of a set. -/
@[to_additive]
abbrev closure : Set M → Subsemigroup M := HasClosure.closure (A := (Subsemigroup M))

@[to_additive]
theorem not_mem_bot {x : M} : x ∉ (⊥ : Subsemigroup M) :=
  Set.not_mem_empty x

@[to_additive (attr := simp)]
theorem coe_bot : ((⊥ : Subsemigroup M) : Set M) = ∅ :=
  rfl

@[to_additive]
theorem subsingleton_of_subsingleton [Subsingleton (Subsemigroup M)] : Subsingleton M := by
  constructor; intro x y
  have : ∀ a : M, a ∈ (⊥ : Subsemigroup M) := by simp [Subsingleton.elim (⊥ : Subsemigroup M) ⊤]
  exact absurd (this x) not_mem_bot

@[to_additive]
instance [hn : Nonempty M] : Nontrivial (Subsemigroup M) :=
  ⟨⟨⊥, ⊤, fun h => by
      obtain ⟨x⟩ := id hn
      refine absurd (?_ : x ∈ ⊥) not_mem_bot
      simp [h]⟩⟩

variable {S}

open Set SetLike

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[to_additive (attr := elab_as_elim) "An induction principle for additive closure membership. If `p`
  holds for all elements of `s`, and is preserved under addition, then `p` holds for all
  elements of the additive closure of `s`."]
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
