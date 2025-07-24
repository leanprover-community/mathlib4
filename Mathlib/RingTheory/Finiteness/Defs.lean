/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Finsupp.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Algebraize

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `Submodule.FG`, `Ideal.FG`
  These express that some object is finitely generated as *submodule* over some base ring.

- `Module.Finite`, `RingHom.Finite`, `AlgHom.Finite`
  all of these express that some object is finitely generated *as module* over some base ring.

-/

assert_not_exists Module.Basis Ideal.radical Matrix Subalgebra

open Function (Surjective)
open Finsupp

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

/-- A submodule of `M` is finitely generated if it is the span of a finite subset of `M`. -/
def FG (N : Submodule R M) : Prop :=
  ∃ S : Finset M, Submodule.span R ↑S = N

theorem fg_def {N : Submodule R M} : N.FG ↔ ∃ S : Set M, S.Finite ∧ span R S = N :=
  ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_toSet t, h⟩, by
    rintro ⟨t', h, rfl⟩
    rcases Finite.exists_finset_coe h with ⟨t, rfl⟩
    exact ⟨t, rfl⟩⟩

theorem fg_iff_addSubmonoid_fg (P : Submodule ℕ M) : P.FG ↔ P.toAddSubmonoid.FG :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoid_closure] using hS⟩, fun ⟨S, hS⟩ =>
    ⟨S, by simpa [← span_nat_eq_addSubmonoid_closure] using hS⟩⟩

theorem fg_iff_add_subgroup_fg {G : Type*} [AddCommGroup G] (P : Submodule ℤ G) :
    P.FG ↔ P.toAddSubgroup.FG :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroup_closure] using hS⟩, fun ⟨S, hS⟩ =>
    ⟨S, by simpa [← span_int_eq_addSubgroup_closure] using hS⟩⟩

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
    N.FG ↔ ∃ (G : Type w) (_ : Finite G) (g : G → M), Submodule.span A (Set.range g) = N := by
  constructor
  · intro hN
    obtain ⟨n, f, h⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hN
    refine ⟨ULift (Fin n), inferInstance, f ∘ ULift.down, ?_⟩
    convert h
    ext x
    simp only [Set.mem_range, Function.comp_apply, ULift.exists]
  · rintro ⟨G, _, g, hg⟩
    have := Fintype.ofFinite (range g)
    exact ⟨(range g).toFinset, by simpa using hg⟩

end Submodule

namespace Ideal

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- An ideal of `R` is finitely generated if it is the span of a finite subset of `R`.

This is defeq to `Submodule.FG`, but unfolds more nicely. -/
def FG (I : Ideal R) : Prop :=
  ∃ S : Finset R, Ideal.span ↑S = I

end Ideal

section ModuleAndAlgebra

variable (R A B M N : Type*)

/-- A module over a semiring is `Module.Finite` if it is finitely generated as a module. -/
protected class Module.Finite [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  fg_top : (⊤ : Submodule R M).FG

attribute [inherit_doc Module.Finite] Module.Finite.fg_top

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

theorem finite_def {R M} [Semiring R] [AddCommMonoid M] [Module R M] :
    Module.Finite R M ↔ (⊤ : Submodule R M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

namespace Finite

open Submodule Set

theorem iff_addMonoid_fg {M : Type*} [AddCommMonoid M] : Module.Finite ℕ M ↔ AddMonoid.FG M :=
  ⟨fun h => AddMonoid.fg_def.2 <| (Submodule.fg_iff_addSubmonoid_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 <| (Submodule.fg_iff_addSubmonoid_fg ⊤).2 (AddMonoid.fg_def.1 h)⟩

theorem iff_addGroup_fg {G : Type*} [AddCommGroup G] : Module.Finite ℤ G ↔ AddGroup.FG G :=
  ⟨fun h => AddGroup.fg_def.2 <| (Submodule.fg_iff_add_subgroup_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 <| (Submodule.fg_iff_add_subgroup_fg ⊤).2 (AddGroup.fg_def.1 h)⟩

variable {R M N}

/-- See also `Module.Finite.exists_fin'`. -/
lemma exists_fin [Module.Finite R M] : ∃ (n : ℕ) (s : Fin n → M), Submodule.span R (range s) = ⊤ :=
  Submodule.fg_iff_exists_fin_generating_family.mp fg_top

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
