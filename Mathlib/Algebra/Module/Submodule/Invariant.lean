/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Order.Sublattice

/-!
# The lattice of invariant submodules

In this file we defined the type `Module.End.invtSubmodule`, associated to a linear endomorphism of
a module. Its utilty stems primarily from those occasions on which we wish to take advantage of the
lattice structure of invariant submodules.

See also `Module.AEval`.

-/

namespace Module.End

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f : End R M)

/-- Given an endomorphism, `f` of some module, this is the sublattice of all `f`-invariant
submodules. -/
def invtSubmodule : Sublattice (Submodule R M) where
  carrier := {p : Submodule R M | p ≤ p.comap f}
  supClosed' p hp q hq := sup_le_iff.mpr
    ⟨le_trans hp <| Submodule.comap_mono le_sup_left,
    le_trans hq <| Submodule.comap_mono le_sup_right⟩
  infClosed' p hp q hq := by
    simp only [Set.mem_setOf_eq, Submodule.comap_inf, le_inf_iff]
    exact ⟨inf_le_of_left_le hp, inf_le_of_right_le hq⟩

lemma mem_invtSubmodule {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ p ≤ p.comap f :=
  Iff.rfl

namespace invtSubmodule

variable {f}

lemma inf_mem {p q : Submodule R M} (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    p ⊓ q ∈ f.invtSubmodule :=
  ((⟨p, hp⟩ : f.invtSubmodule) ⊓ (⟨q, hq⟩ : f.invtSubmodule)).property

lemma sup_mem {p q : Submodule R M} (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    p ⊔ q ∈ f.invtSubmodule :=
  ((⟨p, hp⟩ : f.invtSubmodule) ⊔ (⟨q, hq⟩ : f.invtSubmodule)).property

variable (f)

@[simp]
protected lemma top_mem : ⊤ ∈ f.invtSubmodule := by simp [invtSubmodule]

@[simp]
protected lemma bot_mem : ⊥ ∈ f.invtSubmodule := by simp [invtSubmodule]

instance : BoundedOrder (f.invtSubmodule) where
  top := ⟨⊤, invtSubmodule.top_mem f⟩
  bot := ⟨⊥, invtSubmodule.bot_mem f⟩
  le_top := fun ⟨p, hp⟩ ↦ by simp
  bot_le := fun ⟨p, hp⟩ ↦ by simp

@[simp]
protected lemma zero :
    (0 : End R M).invtSubmodule = ⊤ :=
  eq_top_iff.mpr fun x ↦ by simp [invtSubmodule]

@[simp]
protected lemma id :
    invtSubmodule (LinearMap.id : End R M) = ⊤ :=
  eq_top_iff.mpr fun x ↦ by simp [invtSubmodule]

protected lemma mk_eq_bot_iff {p : Submodule R M} (hp : p ∈ f.invtSubmodule) :
    (⟨p, hp⟩ : f.invtSubmodule) = ⊥ ↔ p = ⊥ :=
  Subtype.mk_eq_bot_iff (by simp [invtSubmodule]) _

protected lemma mk_eq_top_iff {p : Submodule R M} (hp : p ∈ f.invtSubmodule) :
    (⟨p, hp⟩ : f.invtSubmodule) = ⊤ ↔ p = ⊤ :=
  Subtype.mk_eq_top_iff (by simp [invtSubmodule]) _

@[simp]
protected lemma disjoint_mk_iff {p q : Submodule R M}
    (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    Disjoint (α := f.invtSubmodule) ⟨p, hp⟩ ⟨q, hq⟩ ↔ Disjoint p q := by
  rw [disjoint_iff, disjoint_iff, Sublattice.mk_inf_mk,
    Subtype.mk_eq_bot_iff (⊥ : f.invtSubmodule).property]

protected lemma disjoint_iff {p q : f.invtSubmodule} :
    Disjoint p q ↔ Disjoint (p : Submodule R M) (q : Submodule R M) := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

@[simp]
protected lemma codisjoint_mk_iff {p q : Submodule R M}
    (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    Codisjoint (α := f.invtSubmodule) ⟨p, hp⟩ ⟨q, hq⟩ ↔ Codisjoint p q := by
  rw [codisjoint_iff, codisjoint_iff, Sublattice.mk_sup_mk,
    Subtype.mk_eq_top_iff (⊤ : f.invtSubmodule).property]

protected lemma codisjoint_iff {p q : f.invtSubmodule} :
    Codisjoint p q ↔ Codisjoint (p : Submodule R M) (q : Submodule R M) := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

@[simp]
protected lemma isCompl_mk_iff {p q : Submodule R M}
    (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    IsCompl (α := f.invtSubmodule) ⟨p, hp⟩ ⟨q, hq⟩ ↔ IsCompl p q := by
  simp [isCompl_iff]

protected lemma isCompl_iff {p q : f.invtSubmodule} :
    IsCompl p q ↔ IsCompl (p : Submodule R M) (q : Submodule R M) := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

lemma map_subtype_mem_of_mem_invtSubmodule {p : Submodule R M} (hp : p ∈ f.invtSubmodule)
    {q : Submodule R p} (hq : q ∈ invtSubmodule (LinearMap.restrict f hp)) :
    Submodule.map p.subtype q ∈ f.invtSubmodule := by
  rintro - ⟨⟨x, hx⟩, hx', rfl⟩
  specialize hq hx'
  rw [Submodule.mem_comap, LinearMap.restrict_apply] at hq
  simpa [hq] using hp hx

end invtSubmodule

end Module.End
