/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Order.Atoms.Finite
import Mathlib.RingTheory.Artinian

/-!
# Modules of finite length

We define modules of finite length (`IsFiniteLength`) to be finite iterated extensions of
simple modules, and show that a module is of finite length iff it is both Noetherian and Artinian.
We do not make `IsFiniteLength` a class, instead we use `[IsNoetherian R M] [IsArtinian R M]`.

## Tag

Finite length
-/

universe u

variable (R : Type*) [Ring R]

/-- A module of finite length is either trivial or a simple extension of a module known
to be of finite length. -/
inductive IsFiniteLength : ∀ (M : Type u) [AddCommGroup M] [Module R M], Prop
  | of_subsingleton {M} [AddCommGroup M] [Module R M] [Subsingleton M] : IsFiniteLength M
  | of_simple_quotient {M} [AddCommGroup M] [Module R M] {N : Submodule R M}
      [IsSimpleModule R (M ⧸ N)] : IsFiniteLength N → IsFiniteLength M

variable {R} {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem LinearEquiv.isFiniteLength (e : M ≃ₗ[R] N)
    (h : IsFiniteLength R M) : IsFiniteLength R N := by
  induction' h with M _ _ _ M _ _ S _ _ ih generalizing N
  · have := e.symm.toEquiv.subsingleton; exact .of_subsingleton
  · have := IsSimpleModule.congr (Submodule.Quotient.equiv S _ e rfl).symm
    exact .of_simple_quotient (ih <| e.submoduleMap S)

theorem isFiniteLength_iff_isNoetherian_isArtinian :
    IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M :=
  ⟨fun h ↦ h.rec (fun {M} _ _ _ ↦ ⟨inferInstance, inferInstance⟩) fun M _ _ {N} _ _ ⟨_, _⟩ ↦
    ⟨(isNoetherian_iff_submodule_quotient N).mpr ⟨‹_›, isNoetherian_iff'.mpr inferInstance⟩,
      (isArtinian_iff_submodule_quotient N).mpr ⟨‹_›, inferInstance⟩⟩,
    fun ⟨_, _⟩ ↦ Submodule.topEquiv.isFiniteLength <| by
      obtain ⟨f, f0, n, hn⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (Submodule R M)
      rw [← hn.1.eq_top]
      suffices ∀ i ≤ n, IsFiniteLength R (f i) from this n le_rfl
      intro i hi
      induction' i with i ih
      · rw [f0.eq_bot]; exact .of_subsingleton
      let cov := hn.2 i hi
      have := (covBy_iff_quot_is_simple cov.le).mp cov
      have := ((f i).comap (f i.succ).subtype).equivMapOfInjective _ (Submodule.injective_subtype _)
      rw [Submodule.map_comap_subtype, inf_of_le_right cov.le] at this
      exact .of_simple_quotient (this.symm.isFiniteLength <| ih <| le_of_lt hi)⟩

theorem isFiniteLength_iff_exists_compositionSeries :
    IsFiniteLength R M ↔ ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ := by
  _
