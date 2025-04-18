/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Indexed products of submonoids

FIXME.
-/

namespace Submonoid

variable {η : Type*} {f : η → Type*}

-- defined here and not in Algebra.Group.Submonoid.Operations to have access to Algebra.Group.Pi
/-- A version of `Set.pi` for submonoids. Given an index set `I` and a family of submodules
`s : Π i, Submonoid f i`, `pi I s` is the submonoid of dependent functions `f : Π i, f i` such that
`f i` belongs to `Pi I s` whenever `i ∈ I`. -/
@[to_additive "A version of `Set.pi` for `AddSubmonoid`s. Given an index set `I` and a family
  of submodules `s : Π i, AddSubmonoid f i`, `pi I s` is the `AddSubmonoid` of dependent functions
  `f : Π i, f i` such that `f i` belongs to `pi I s` whenever `i ∈ I`."]
def pi [∀ i, MulOneClass (f i)] (I : Set η) (s : ∀ i, Submonoid (f i)) :
    Submonoid (∀ i, f i) where
  carrier := I.pi fun i => (s i).carrier
  one_mem' i _ := (s i).one_mem
  mul_mem' hp hq i hI := (s i).mul_mem (hp i hI) (hq i hI)

@[to_additive]
theorem coe_pi [∀ i, Monoid (f i)] (I : Set η) (H : ∀ i, Submonoid (f i)) :
    (pi I H : Set (∀ i, f i)) = Set.pi I fun i => (H i : Set (f i)) := rfl

@[to_additive]
theorem mem_pi [∀ i, Monoid (f i)] (I : Set η) {H : ∀ i, Submonoid (f i)} {p : ∀ i, f i} :
    p ∈ pi I H ↔ ∀ i : η, i ∈ I → p i ∈ H i :=
  Iff.rfl

@[to_additive]
theorem pi_top [∀ i, Monoid (f i)] (I : Set η) : (pi I fun i => (⊤ : Submonoid (f i))) = ⊤ := by
  ext; simp [mem_pi]

@[to_additive]
theorem pi_empty [∀ i, Monoid (f i)] (H : ∀ i, Submonoid (f i)) : pi ∅ H = ⊤ := by
  ext; simp [mem_pi]

@[to_additive]
theorem pi_bot [∀ i, Monoid (f i)] : (pi Set.univ fun i => (⊥ : Submonoid (f i))) = ⊥ := by
  simp only [Submonoid.eq_bot_iff_forall, mem_pi, Set.mem_univ, Submonoid.mem_bot, forall_const]
  intro x hx
  ext j
  exact hx j

@[to_additive]
theorem le_pi_iff [∀ i, Monoid (f i)] {I : Set η}
    {H : ∀ i, Submonoid (f i)} {J : Submonoid (∀ i, f i)} :
    J ≤ pi I H ↔ ∀ i : η, i ∈ I → Submonoid.map (Pi.evalMonoidHom f i) J ≤ H i := by
  constructor
  · intro h i hi
    rintro _ ⟨x, hx, rfl⟩
    exact (h hx) _ hi
  · intro h x hx i hi
    exact h i hi ⟨_, hx, rfl⟩

end Submonoid
