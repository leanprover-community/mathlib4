/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.RingTheory.Artinian.Module

/-!
# Modules of finite length

We define modules of finite length (`IsFiniteLength`) to be finite iterated extensions of
simple modules, and show that a module is of finite length iff it is both Noetherian and Artinian,
iff it admits a composition series.

We do not make `IsFiniteLength` a class, instead we use `[IsNoetherian R M] [IsArtinian R M]`.

## Tags

Finite length, Composition series
-/

variable (R : Type*) [Ring R]

/-- A module of finite length is either trivial or a simple extension of a module known
to be of finite length. -/
inductive IsFiniteLength : ∀ (M : Type*) [AddCommGroup M] [Module R M], Prop
  | of_subsingleton {M} [AddCommGroup M] [Module R M] [Subsingleton M] : IsFiniteLength M
  | of_simple_quotient {M} [AddCommGroup M] [Module R M] {N : Submodule R M}
      [IsSimpleModule R (M ⧸ N)] : IsFiniteLength N → IsFiniteLength M

attribute [nontriviality] IsFiniteLength.of_subsingleton

variable {R} {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem LinearEquiv.isFiniteLength (e : M ≃ₗ[R] N)
    (h : IsFiniteLength R M) : IsFiniteLength R N := by
  induction h generalizing N with
  | of_subsingleton =>
    have := e.symm.toEquiv.subsingleton; exact .of_subsingleton
  | @of_simple_quotient M _ _ S _ _ ih =>
    have : IsSimpleModule R (N ⧸ Submodule.map (e : M →ₗ[R] N) S) :=
      IsSimpleModule.congr (Submodule.Quotient.equiv S _ e rfl).symm
    exact .of_simple_quotient (ih <| e.submoduleMap S)

variable (R M) in
theorem exists_compositionSeries_of_isNoetherian_isArtinian [IsNoetherian R M] [IsArtinian R M] :
    ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ := by
  obtain ⟨f, f0, n, hn⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (Submodule R M)
  exact ⟨⟨n, fun i ↦ f i, fun i ↦ hn.2 i i.2⟩, f0.eq_bot, hn.1.eq_top⟩

theorem isFiniteLength_of_exists_compositionSeries
    (h : ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤) :
    IsFiniteLength R M :=
  Submodule.topEquiv.isFiniteLength <| by
    obtain ⟨s, s_head, s_last⟩ := h
    rw [← s_last]
    suffices ∀ i, IsFiniteLength R (s i) from this (Fin.last _)
    intro i
    induction' i using Fin.induction with i ih
    · change IsFiniteLength R s.head; rw [s_head]; exact .of_subsingleton
    let cov := s.step i
    have := (covBy_iff_quot_is_simple cov.le).mp cov
    have := ((s i.castSucc).comap (s i.succ).subtype).equivMapOfInjective
      _ (Submodule.injective_subtype _)
    rw [Submodule.map_comap_subtype, inf_of_le_right cov.le] at this
    exact .of_simple_quotient (this.symm.isFiniteLength ih)

theorem isFiniteLength_iff_isNoetherian_isArtinian :
    IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M :=
  ⟨fun h ↦ h.rec (fun {M} _ _ _ ↦ ⟨inferInstance, inferInstance⟩) fun M _ _ {N} _ _ ⟨_, _⟩ ↦
    ⟨(isNoetherian_iff_submodule_quotient N).mpr ⟨‹_›, isNoetherian_iff'.mpr inferInstance⟩,
      (isArtinian_iff_submodule_quotient N).mpr ⟨‹_›, inferInstance⟩⟩,
    fun ⟨_, _⟩ ↦ isFiniteLength_of_exists_compositionSeries
      (exists_compositionSeries_of_isNoetherian_isArtinian R M)⟩

theorem isFiniteLength_iff_exists_compositionSeries :
    IsFiniteLength R M ↔ ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ :=
  ⟨fun h ↦ have ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
    exists_compositionSeries_of_isNoetherian_isArtinian R M,
    isFiniteLength_of_exists_compositionSeries⟩

theorem IsSemisimpleModule.finite_tfae [IsSemisimpleModule R M] :
    List.TFAE [Module.Finite R M, IsNoetherian R M, IsArtinian R M, IsFiniteLength R M,
      ∃ s : Set (Submodule R M), s.Finite ∧ sSupIndep s ∧
        sSup s = ⊤ ∧ ∀ m ∈ s, IsSimpleModule R m] := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  obtain ⟨s, hs⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top R M
  tfae_have 1 ↔ 2 := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩
  tfae_have 2 → 5 := fun _ ↦ ⟨s, WellFoundedGT.finite_of_sSupIndep hs.1, hs⟩
  tfae_have 3 → 5 := fun _ ↦ ⟨s, WellFoundedLT.finite_of_sSupIndep hs.1, hs⟩
  tfae_have 5 → 4 := fun ⟨s, fin, _, sSup_eq_top, simple⟩ ↦ by
    rw [← isNoetherian_top_iff, ← Submodule.topEquiv.isArtinian_iff,
      ← sSup_eq_top, sSup_eq_iSup, ← iSup_subtype'']
    rw [SetCoe.forall'] at simple
    have := fin.to_subtype
    exact ⟨isNoetherian_iSup, isArtinian_iSup⟩
  tfae_have 4 → 2 := And.left
  tfae_have 4 → 3 := And.right
  tfae_finish

instance [IsSemisimpleModule R M] [Module.Finite R M] : IsArtinian R M :=
  (IsSemisimpleModule.finite_tfae.out 0 2).mp ‹_›

variable {f : M →ₗ[R] N}

lemma IsFiniteLength.of_injective (H : IsFiniteLength R N) (hf : Function.Injective f) :
    IsFiniteLength R M := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at H ⊢
  cases H
  exact ⟨isNoetherian_of_injective f hf, isArtinian_of_injective f hf⟩

lemma IsFiniteLength.of_surjective (H : IsFiniteLength R M) (hf : Function.Surjective f) :
    IsFiniteLength R N := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at H ⊢
  cases H
  exact ⟨isNoetherian_of_surjective _ f (LinearMap.range_eq_top.mpr hf),
    isArtinian_of_surjective _ f hf⟩

/- The following instances are now automatic:
example [IsSemisimpleRing R] : IsNoetherianRing R := inferInstance
example [IsSemisimpleRing R] : IsArtinianRing R := inferInstance
-/
