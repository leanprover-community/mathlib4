/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.Ideal.Colon

/-!
# Modules of finite length

We define modules of finite length (`IsFiniteLength`) to be finite iterated extensions of
simple modules, and show that a module is of finite length iff it is both Noetherian and Artinian,
iff it admits a composition series.

We do not make `IsFiniteLength` a class, instead we use `[IsNoetherian R M] [IsArtinian R M]`.

## Main result

* `IsSemiprimaryRing.isNoetherian_iff_isArtinian`: the Hopkins–Levitzki theorem, which states
that for a module over a semiprimary ring (in particular, an Artinian ring),
`IsNoetherian` is equivalent to `IsArtinian` (and therefore also to `IsFiniteLength`).

* In particular, for a module over an Artinian ring, `Module.Finite`, `IsNoetherian`, `IsArtinian`,
and `IsFiniteLength` are all equivalent (`IsArtinianRing.tfae`),
and a (left) Artinian ring is also (left) Noetherian.

## Tag

Finite length, Composition series
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
  · have : IsSimpleModule R (N ⧸ Submodule.map (e : M →ₗ[R] N) S) :=
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
      ∃ s : Set (Submodule R M), s.Finite ∧ CompleteLattice.SetIndependent s ∧
        sSup s = ⊤ ∧ ∀ m ∈ s, IsSimpleModule R m] := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  obtain ⟨s, hs⟩ := IsSemisimpleModule.exists_setIndependent_sSup_simples_eq_top R M
  tfae_have 1 ↔ 2 := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩
  tfae_have 2 → 5 := fun _ ↦ ⟨s, CompleteLattice.WellFoundedGT.finite_of_setIndependent hs.1, hs⟩
  tfae_have 3 → 5 := fun _ ↦ ⟨s, CompleteLattice.WellFoundedLT.finite_of_setIndependent hs.1, hs⟩
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

example [IsSemisimpleRing R] : IsNoetherianRing R := inferInstance
example [IsSemisimpleRing R] : IsArtinianRing R := inferInstance

open Ideal in
theorem IsSemiprimaryRing.isNoetherian_iff_isArtinian [IsSemiprimaryRing R] :
    IsNoetherian R M ↔ IsArtinian R M := by
  have ⟨ss, n, hn⟩ := (isSemiprimaryRing_iff R).mp ‹_›
  set Jac := Ring.jacobson R
  replace hn : Jac ^ n ≤ Module.annihilator R M := hn ▸ bot_le
  induction' n with n ih generalizing M
  · rw [Submodule.pow_zero, one_eq_top, top_le_iff, Module.annihilator_eq_top_iff] at hn
    constructor <;> infer_instance
  obtain _ | n := n
  · rw [Submodule.pow_one, ← SetLike.coe_subset_coe,
      ← Module.isTorsionBySet_iff_subset_annihilator] at hn
    let _ := hn.module
    have := hn.isSemisimpleModule_iff.mp inferInstance
    exact IsSemisimpleModule.finite_tfae.out 1 2
  let N := Jac ^ (n + 1) • (⊤ : Submodule R M)
  simp_rw [iff_iff_eq] at ih -- otherwise `rw [ih]` below fails!
  rw [isNoetherian_iff_submodule_quotient N, isArtinian_iff_submodule_quotient N, ih, ih]
  · rw [← SetLike.coe_subset_coe, ← Module.isTorsionBySet_iff_subset_annihilator,
      Module.isTorsionBySet_quotient_iff]
    intro m i hi; exact Submodule.smul_mem_smul hi trivial
  · rw [← Submodule.annihilator_top, Submodule.le_annihilator_iff, Ideal.IsTwoSided.pow_succ,
      Submodule.mul_smul, ← Submodule.le_annihilator_iff] at hn
    exact (Ideal.pow_le_self n.succ_ne_zero).trans hn

variable (R M)

theorem IsArtinianRing.tfae [IsArtinianRing R] :
    List.TFAE [Module.Finite R M, IsNoetherian R M, IsArtinian R M, IsFiniteLength R M] := by
  tfae_have 2 ↔ 3 := IsSemiprimaryRing.isNoetherian_iff_isArtinian
  tfae_have 2 → 1 := fun _ ↦ inferInstance
  tfae_have 1 → 3 := fun _ ↦ inferInstance
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  tfae_have 4 → 2 := And.left
  tfae_have 2 → 4 := fun h ↦ ⟨h, tfae_2_iff_3.mp h⟩
  tfae_finish

instance [IsArtinianRing R] : IsNoetherianRing R := ((IsArtinianRing.tfae R R).out 2 1).mp ‹_›

/-- A finitely generated Artinian module over a commutative ring is Noetherian. This is not
necessarily the case over a noncommutative ring, see https://mathoverflow.net/a/61700/3332. -/
theorem isNoetherian_of_finite_isArtinian {R} [CommRing R] [Module R M]
    [Module.Finite R M] [IsArtinian R M] : IsNoetherian R M := by
  obtain ⟨s, fin, span⟩ := Submodule.fg_def.mp (Module.finite_def.mp ‹_›)
  rw [← s.iUnion_of_singleton_coe, Submodule.span_iUnion] at span
  rw [← Set.finite_coe_iff] at fin
  rw [← isNoetherian_top_iff, ← span]
  have _ (i : M) : IsNoetherian R (Submodule.span R {i}) := by
    rw [LinearMap.span_singleton_eq_range, ← (LinearMap.quotKerEquivRange _).isNoetherian_iff]
    let e (I : Ideal R) : R ⧸ I →ₛₗ[Ideal.Quotient.mk I] R ⧸ I := ⟨.id _, fun _ _ ↦ rfl⟩
    rw [(e _).isNoetherian_iff_of_bijective Function.bijective_id]
    refine @instIsNoetherianRingOfIsArtinianRing _ _ ?_
    rw [IsArtinianRing, ← (e _).isArtinian_iff_of_bijective Function.bijective_id,
      (LinearMap.quotKerEquivRange _).isArtinian_iff]
    infer_instance
  infer_instance
