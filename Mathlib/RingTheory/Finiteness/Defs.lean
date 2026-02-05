/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic.Algebraize

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `Submodule.FG`, `Ideal.FG`
  These express that some object is finitely generated as *submodule* over some base ring.

- `Module.Finite`, `RingHom.Finite`, `AlgHom.Finite`
  all of these express that some object is finitely generated *as module* over some base ring.

-/

@[expose] public section

assert_not_exists Module.Basis Ideal.radical Matrix Subalgebra

open Function (Surjective)

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

/-- A submodule of `M` is finitely generated if it is the span of a finite subset of `M`. -/
def FG (N : Submodule R M) : Prop :=
  ∃ S : Finset M, span R ↑S = N

theorem fg_def {N : Submodule R M} : N.FG ↔ ∃ S : Set M, S.Finite ∧ span R S = N := by
  refine ⟨fun ⟨t, h⟩ => ⟨_, t.finite_toSet, h⟩, ?_⟩
  rintro ⟨t', h, rfl⟩
  have := h.exists_finset_coe
  tauto

theorem fg_iff_addSubmonoid_fg (P : Submodule ℕ M) : P.FG ↔ P.toAddSubmonoid.FG :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoidClosure]⟩,
    fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoidClosure] using hS⟩⟩

theorem fg_iff_addSubgroup_fg {G : Type*} [AddCommGroup G] (P : Submodule ℤ G) :
    P.FG ↔ P.toAddSubgroup.FG :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroupClosure]⟩,
    fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroupClosure] using hS⟩⟩

@[deprecated (since := "2025-08-20")] alias fg_iff_add_subgroup_fg := fg_iff_addSubgroup_fg

theorem fg_iff_exists_fin_generating_family {N : Submodule R M} :
    N.FG ↔ ∃ (n : ℕ) (s : Fin n → M), span R (range s) = N := by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  · rintro ⟨n, s, hs⟩
    exact ⟨range s, finite_range s, hs⟩

universe w v u in
lemma fg_iff_exists_finite_generating_family {A : Type u} [Semiring A] {M : Type v}
    [AddCommMonoid M] [Module A M] {N : Submodule A M} :
    N.FG ↔ ∃ (G : Type w) (_ : Finite G) (g : G → M), span A (range g) = N := by
  constructor
  · intro hN
    obtain ⟨n, f, h⟩ := fg_iff_exists_fin_generating_family.mp hN
    refine ⟨ULift (Fin n), inferInstance, f ∘ ULift.down, ?_⟩
    convert h
    ext
    simp
  · rintro ⟨G, _, g, hg⟩
    have := Fintype.ofFinite (range g)
    exact ⟨(range g).toFinset, by simpa⟩

theorem fg_span_iff_fg_span_finset_subset (s : Set M) :
    (span R s).FG ↔ ∃ s' : Finset M, ↑s' ⊆ s ∧ span R s = span R s' := by
  constructor
  · intro ⟨s'', hs''⟩
    obtain ⟨s', hs's, hss'⟩ := subset_span_finite_of_subset_span <| hs'' ▸ subset_span
    refine ⟨s', hs's, ?_⟩
    apply le_antisymm
    · rwa [← hs'', span_le]
    · rw [span_le]
      exact le_trans hs's subset_span
  · intro ⟨s', _, h⟩
    exact ⟨s', h.symm⟩

end Submodule

namespace Ideal

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- An ideal of `R` is finitely generated if it is the span of a finite subset of `R`.

This is defeq to `Submodule.FG`, but unfolds more nicely. -/
def FG (I : Ideal R) : Prop :=
  ∃ S : Finset R, span ↑S = I

end Ideal

section ModuleAndAlgebra

variable (R A B M N : Type*)

/-- A module over a semiring is `Module.Finite` if it is finitely generated as a module. -/
protected class Module.Finite [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  of_fg_top ::
    fg_top : (⊤ : Submodule R M).FG

attribute [inherit_doc Module.Finite] Module.Finite.fg_top

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- See also `Module.Finite.iff_fg` for a version when `M` is itself a submodule. -/
theorem finite_def {R M} [Semiring R] [AddCommMonoid M] [Module R M] :
    Module.Finite R M ↔ (⊤ : Submodule R M).FG :=
  ⟨(·.fg_top), .of_fg_top⟩

namespace Finite

open Submodule Set

theorem iff_addMonoid_fg {M : Type*} [AddCommMonoid M] : Module.Finite ℕ M ↔ AddMonoid.FG M :=
  ⟨fun h => AddMonoid.fg_def.mpr <| (fg_iff_addSubmonoid_fg ⊤).mp h.fg_top,
    fun h => of_fg_top <| (fg_iff_addSubmonoid_fg ⊤).mpr (AddMonoid.fg_def.mp h)⟩

theorem iff_addGroup_fg {G : Type*} [AddCommGroup G] : Module.Finite ℤ G ↔ AddGroup.FG G :=
  ⟨fun h => AddGroup.fg_def.mpr <| (fg_iff_addSubgroup_fg ⊤).mp h.fg_top,
    fun h => of_fg_top <| (fg_iff_addSubgroup_fg ⊤).mpr (AddGroup.fg_def.mp h)⟩

variable {R M N}

/-- See also `Module.Finite.exists_fin'`. -/
lemma exists_fin [Module.Finite R M] : ∃ (n : ℕ) (s : Fin n → M), span R (range s) = ⊤ :=
  fg_iff_exists_fin_generating_family.mp fg_top

end Finite

end Module

instance AddMonoid.FG.to_moduleFinite_nat {M : Type*} [AddCommMonoid M] [FG M] :
    Module.Finite ℕ M :=
  Module.Finite.iff_addMonoid_fg.mpr ‹_›

instance AddMonoid.FG.to_moduleFinite_int {G : Type*} [AddCommGroup G] [FG G] :
    Module.Finite ℤ G :=
  Module.Finite.iff_addGroup_fg.mpr <| AddGroup.fg_iff_addMonoid_fg.mpr ‹_›

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is `RingHom.Finite` if `B` is finitely generated as `A`-module. -/
@[algebraize Module.Finite, stacks 0563]
def Finite (f : A →+* B) : Prop :=
  letI : Algebra A B := f.toAlgebra
  Module.Finite A B

@[simp]
lemma finite_algebraMap [Algebra A B] :
    (algebraMap A B).Finite ↔ Module.Finite A B := by
  rw [Finite, toAlgebra_algebraMap]

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommRing R]
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
def Finite (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.Finite

end AlgHom
