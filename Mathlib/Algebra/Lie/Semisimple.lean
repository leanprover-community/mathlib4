/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Order.Atoms
import Mathlib.Order.Minimal

#align_import algebra.lie.semisimple from "leanprover-community/mathlib"@"356447fe00e75e54777321045cdff7c9ea212e60"

/-!
# Semisimple Lie algebras

The famous Cartan-Dynkin-Killing classification of semisimple Lie algebras renders them one of the
most important classes of Lie algebras. In this file we define simple and semisimple Lie algebras
and prove some basic related results.

## Main definitions

  * `LieModule.IsIrreducible`
  * `LieAlgebra.IsSimple`
  * `LieAlgebra.HasTrivialRadical`
  * `LieAlgebra.IsSemisimple`
  * `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`
  * `LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals`
  * `LieAlgebra.abelian_radical_iff_solvable_is_abelian`

## Tags

lie algebra, radical, simple, semisimple
-/


universe u v w w₁ w₂

/-- A Lie module is irreducible if it is zero or its only non-trivial Lie submodule is itself. -/
class LieModule.IsIrreducible (R : Type u) (L : Type v) (M : Type w) [CommRing R] [LieRing L]
    [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M] :
    Prop where
  irreducible : ∀ N : LieSubmodule R L M, N ≠ ⊥ → N = ⊤
#align lie_module.is_irreducible LieModule.IsIrreducible

namespace LieAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
class IsSimple extends LieModule.IsIrreducible R L L : Prop where
  non_abelian : ¬IsLieAbelian L
#align lie_algebra.is_simple LieAlgebra.IsSimple

/--
A Lie algebra *has trivial radical* if its radical is trivial.
This is equivalent to having no non-trivial solvable ideals,
and further equivalent to having no non-trivial abelian ideals.

In characteristic zero, it is also equivalent to `LieAlgebra.IsSemisimple`.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.HasTrivialRadical`,
whereas we reserve it for Lie algebras that are a direct sum of simple Lie algebras.
-/
class HasTrivialRadical : Prop where
  trivial_radical : radical R L = ⊥
#align lie_algebra.is_semisimple LieAlgebra.HasTrivialRadical

/--
A *semisimple* Lie algebra is one that is a direct sum of simple Lie algebras.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.HasTrivialRadical`,
the weakest of the various properties which are all equivalent over a field of characteristic zero.
-/
class IsSemisimple : Prop where
  spanning : sSup {I : LieIdeal R L | IsAtom I} = ⊤
  independent : CompleteLattice.SetIndependent {I : LieIdeal R L | IsAtom I}
  non_abelian_of_isAtom : ∀ I : LieIdeal R L, IsAtom I → ¬ IsLieAbelian I

-- TODO: show that the atomic ideals of a semisimple Lie algebra are simple

theorem hasTrivialRadical_iff_no_solvable_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsSolvable R I → I = ⊥ :=
  ⟨fun h => sSup_eq_bot.mp h.trivial_radical, fun h => ⟨sSup_eq_bot.mpr h⟩⟩
#align lie_algebra.is_semisimple_iff_no_solvable_ideals LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals

theorem hasTrivialRadical_iff_no_abelian_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsLieAbelian I → I = ⊥ := by
  rw [hasTrivialRadical_iff_no_solvable_ideals]
  constructor <;> intro h₁ I h₂
  · haveI : IsLieAbelian I := h₂; apply h₁; exact LieAlgebra.ofAbelianIsSolvable R I
  · haveI : IsSolvable R I := h₂; rw [← abelian_of_solvable_ideal_eq_bot_iff]; apply h₁
    exact abelian_derivedAbelianOfIdeal I
#align lie_algebra.is_semisimple_iff_no_abelian_ideals LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals

@[simp]
theorem center_eq_bot_of_hasTrivialRadical [h : HasTrivialRadical R L] : center R L = ⊥ := by
  rw [hasTrivialRadical_iff_no_abelian_ideals] at h; apply h; infer_instance
#align lie_algebra.center_eq_bot_of_semisimple LieAlgebra.center_eq_bot_of_hasTrivialRadical

variable {R L} in
lemma eq_top_of_isAtom [IsSimple R L] (I : LieIdeal R L) (hI : IsAtom I) : I = ⊤ :=
  LieModule.IsIrreducible.irreducible I hI.1

lemma isAtom_top [IsSimple R L] : IsAtom (⊤ : LieIdeal R L) := by
  constructor
  · intro h
    apply IsSimple.non_abelian R (L := L)
    constructor
    intro x y
    rw [← LieSubmodule.mem_bot (R := R) (L := L), ← h]
    trivial
  · intro I hI
    have := LieModule.IsIrreducible.irreducible I
    contrapose! this
    exact ⟨this, hI.ne⟩

variable {R L} in
lemma isAtom_iff_eq_top [IsSimple R L] (I : LieIdeal R L) : IsAtom I ↔ I = ⊤ :=
  ⟨eq_top_of_isAtom I, fun h ↦ h ▸ isAtom_top R L⟩

-- move this to `Mathlib.Order.SupIndep`
lemma _root_.CompleteLattice.setIndependent_singleton {α : Type w} [CompleteLattice α] (a : α) :
    CompleteLattice.SetIndependent ({a} : Set α) := by
  intro i hi
  simp_all

/-- A simple Lie algebra is semisimple. -/
instance (priority := 100) isSemisimple_of_isSimple [h : IsSimple R L] :
    IsSemisimple R L := by
  have aux : {I : LieIdeal R L | IsAtom I} = {⊤} := by
    ext I
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, isAtom_iff_eq_top]
  constructor
  · simp [aux]
  · simpa [aux] using _root_.CompleteLattice.setIndependent_singleton _
  · intro I hI₁ hI₂
    rw [isAtom_iff_eq_top] at hI₁
    subst I
    obtain @⟨⟨h₁⟩, h₂⟩ := id h
    rw [lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv] at hI₂
    contradiction

/-- A semisimple Lie algebra has trivial radical. -/
instance (priority := 100) hasTrivialRadical_of_isSemisimple [h : IsSemisimple R L] :
    HasTrivialRadical R L := by
  sorry

/-- A simple Lie algebra has trivial radical. -/
instance (priority := 100) hasTrivialRadical_of_isSimple [IsSimple R L] :
    HasTrivialRadical R L := inferInstance
#align lie_algebra.is_semisimple_of_is_simple LieAlgebra.hasTrivialRadical_of_isSimple

/-- An abelian Lie algebra with trivial radical is trivial. -/
theorem subsingleton_of_hasTrivialRadical_lie_abelian [HasTrivialRadical R L] [h : IsLieAbelian L] :
    Subsingleton L := by
  rw [isLieAbelian_iff_center_eq_top R L, center_eq_bot_of_hasTrivialRadical] at h
  exact (LieSubmodule.subsingleton_iff R L L).mp (subsingleton_of_bot_eq_top h)
#align lie_algebra.subsingleton_of_semisimple_lie_abelian LieAlgebra.subsingleton_of_hasTrivialRadical_lie_abelian

theorem abelian_radical_of_hasTrivialRadical [HasTrivialRadical R L] :
    IsLieAbelian (radical R L) := by
  rw [HasTrivialRadical.trivial_radical]; infer_instance
#align lie_algebra.abelian_radical_of_semisimple LieAlgebra.abelian_radical_of_hasTrivialRadical

/-- The two properties shown to be equivalent here are possible definitions for a Lie algebra
to be reductive.

Note that there is absolutely [no agreement](https://mathoverflow.net/questions/284713/) on what
the label 'reductive' should mean when the coefficients are not a field of characteristic zero. -/
theorem abelian_radical_iff_solvable_is_abelian [IsNoetherian R L] :
    IsLieAbelian (radical R L) ↔ ∀ I : LieIdeal R L, IsSolvable R I → IsLieAbelian I := by
  constructor
  · rintro h₁ I h₂
    rw [LieIdeal.solvable_iff_le_radical] at h₂
    exact (LieIdeal.inclusion_injective h₂).isLieAbelian h₁
  · intro h; apply h; infer_instance
#align lie_algebra.abelian_radical_iff_solvable_is_abelian LieAlgebra.abelian_radical_iff_solvable_is_abelian

theorem ad_ker_eq_bot_of_hasTrivialRadical [HasTrivialRadical R L] : (ad R L).ker = ⊥ := by simp
#align lie_algebra.ad_ker_eq_bot_of_semisimple LieAlgebra.ad_ker_eq_bot_of_hasTrivialRadical

end LieAlgebra
