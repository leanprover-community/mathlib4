/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.Sublattice

/-!
# The lattice of invariant submodules

In this file we defined the type `Module.End.invtSubmodule`, associated to a linear endomorphism of
a module. Its utility stems primarily from those occasions on which we wish to take advantage of the
lattice structure of invariant submodules.

See also `Mathlib/Algebra/Polynomial/Module/AEval.lean`.

-/

open Submodule (span)

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

/-- `p` is `f` invariant if and only if `p.map f ≤ p`. -/
theorem mem_invtSubmodule_iff_map_le {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ p.map f ≤ p := Submodule.map_le_iff_le_comap.symm

/-- `p` is `f` invariant if and only if `Set.MapsTo f p p`. -/
theorem mem_invtSubmodule_iff_mapsTo {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ Set.MapsTo f p p := Iff.rfl

alias ⟨_, _root_.Set.Mapsto.mem_invtSubmodule⟩ := mem_invtSubmodule_iff_mapsTo

theorem mem_invtSubmodule_iff_forall_mem_of_mem {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ ∀ x ∈ p, f x ∈ p :=
  Iff.rfl

/-- `p` is `f.symm` invariant if and only if `p ≤ p.map f`. -/
lemma mem_invtSubmodule_symm_iff_le_map {f : M ≃ₗ[R] M} {p : Submodule R M} :
    p ∈ invtSubmodule f.symm ↔ p ≤ p.map f :=
  (mem_invtSubmodule_iff_map_le _).trans (f.toEquiv.symm.subset_symm_image _ _).symm

namespace invtSubmodule

variable {f}

lemma inf_mem {p q : Submodule R M} (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    p ⊓ q ∈ f.invtSubmodule :=
  Sublattice.inf_mem hp hq

lemma sup_mem {p q : Submodule R M} (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    p ⊔ q ∈ f.invtSubmodule :=
  Sublattice.sup_mem hp hq

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

@[simp]
protected lemma one :
    invtSubmodule (1 : End R M) = ⊤ :=
  invtSubmodule.id

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

protected lemma comp {p : Submodule R M} {g : End R M}
    (hf : p ∈ f.invtSubmodule) (hg : p ∈ g.invtSubmodule) :
    p ∈ invtSubmodule (f ∘ₗ g) :=
  fun _ hx ↦ hf (hg hx)

@[simp] lemma _root_.LinearEquiv.map_mem_invtSubmodule_conj_iff {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {f : End R M}
    {e : M ≃ₗ[R] N} {p : Submodule R M} :
    p.map e ∈ (e.conj f).invtSubmodule ↔ p ∈ f.invtSubmodule := by
  change p.map e.toLinearMap ∈ _ ↔ _
  have : e.symm.toLinearMap ∘ₗ ((e ∘ₗ f) ∘ₗ e.symm.toLinearMap) ∘ₗ e = f := by ext; simp
  rw [LinearEquiv.conj_apply, mem_invtSubmodule, mem_invtSubmodule, Submodule.map_le_iff_le_comap,
    Submodule.map_equiv_eq_comap_symm, ← Submodule.comap_comp, ← Submodule.comap_comp, this]

lemma _root_.LinearEquiv.map_mem_invtSubmodule_iff {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {f : End R N}
    {e : M ≃ₗ[R] N} {p : Submodule R M} :
    p.map e ∈ f.invtSubmodule ↔ p ∈ (e.symm.conj f).invtSubmodule := by
  simp [← e.map_mem_invtSubmodule_conj_iff]

end invtSubmodule

variable (R) in
lemma span_orbit_mem_invtSubmodule {G : Type*}
    [Monoid G] [DistribMulAction G M] [SMulCommClass G R M] (x : M) (g : G) :
    span R (MulAction.orbit G x) ∈ invtSubmodule (DistribMulAction.toLinearMap R M g) := by
  rw [mem_invtSubmodule, Submodule.span_le, Submodule.comap_coe]
  intro y hy
  simp only [Set.mem_preimage, DistribMulAction.toLinearMap_apply, SetLike.mem_coe]
  exact Submodule.subset_span <| MulAction.mem_orbit_of_mem_orbit g hy

end Module.End
