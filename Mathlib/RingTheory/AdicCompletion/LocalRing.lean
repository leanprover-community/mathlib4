/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Basic Properties of Complete Local Ring

In this file we prove that for `I` an finitely generated ideal of `R`,
`AdicCompletion I M` is adic complete with respect to `I`. Then we use this to deduce for
Noetherian local ring `R`, `AdicCompletion (maximalIdeal R) R` is always a complete local ring.

-/

public section

variable {R : Type*} [CommRing R]

open Ideal Quotient

theorem isLocalRing_of_isAdicComplete_maximal (m : Ideal R) [m.IsMaximal] [IsAdicComplete m R] :
    IsLocalRing R :=
  IsLocalRing.of_unique_max_ideal ⟨m, ‹m.IsMaximal›, fun _ hJ ↦
    (‹m.IsMaximal›.eq_of_le hJ.ne_top <|
      (IsAdicComplete.le_jacobson_bot m).trans <| sInf_le ⟨bot_le, hJ⟩).symm⟩

open IsLocalRing

variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

lemma AdicCompletion.isAdicComplete_self (fg : I.FG) :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
  (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete fg)

lemma AdicCompletion.isMaximal_map_of_le (m : Ideal R) [m.IsMaximal] (le : I ≤ m) (fg : I.FG) :
    (m.map (algebraMap R (AdicCompletion I R))).IsMaximal := by
  have compeq : (AdicCompletion.evalOneₐ I).toRingHom.comp (algebraMap R (AdicCompletion I R)) =
    (Ideal.Quotient.mk I) := rfl
  have kerle : RingHom.ker (evalOneₐ I).toRingHom ≤ m.map (algebraMap R (AdicCompletion I R)) := by
    intro x hx
    have : x ∈ (AdicCompletion.eval I R 1).ker := by
      have eq : I ^ 1 * ⊤ = I := by simp
      simp only [AlgHom.toRingHom_eq_coe, RingHom.mem_ker, RingHom.coe_coe, ← factorₐ_evalₐ_one,
        pow_one, smul_eq_mul, mul_top, le_refl, ← factor_eval_eq_evalₐ, Submodule.mapQ_eq_factor,
        Submodule.factor_eq_factor, factor_comp_apply] at hx
      have : (factor (le_of_eq eq.symm)) ((factor (le_of_eq eq)) ((eval I R 1) x)) = 0 := by
        simp [hx]
      simpa using this
    simp only [smul_eq_mul, ← pow_smul_top_eq_ker_eval fg, pow_one, smul_top_eq_map,
      Submodule.restrictScalars_mem] at this
    exact Ideal.map_mono le this
  have : m.map (algebraMap R (AdicCompletion I R)) = (m.map (Ideal.Quotient.mk I)).comap
    (AdicCompletion.evalOneₐ I).toRingHom := by
    rw [← compeq, ← Ideal.map_map,
      Ideal.comap_map_of_surjective' (evalOneₐ I).toRingHom (evalOneₐ_surjective I),
      eq_comm, sup_eq_left]
    exact kerle
  rw [this]
  have : (Ideal.map (Ideal.Quotient.mk I) m).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using le)
  exact Ideal.comap_isMaximal_of_surjective _ (evalOneₐ_surjective I)

lemma AdicCompletion.isLocalRing_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
  @isLocalRing_of_isAdicComplete_maximal _ _
    ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)))
    (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _) fg)
    (AdicCompletion.isAdicComplete_self _ fg)

instance [IsNoetherianRing R] [IsLocalRing R] : IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
  AdicCompletion.isLocalRing_of_fg (fg_of_isNoetherianRing (maximalIdeal R))

lemma AdicCompletion.maximalIdeal_eq_map_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    letI := AdicCompletion.isLocalRing_of_fg fg
    maximalIdeal (AdicCompletion (maximalIdeal R) R) =
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  letI := AdicCompletion.isLocalRing_of_fg fg
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _) fg)).symm

lemma AdicCompletion.maximalIdeal_eq_map [IsNoetherianRing R] [IsLocalRing R] :
    maximalIdeal (AdicCompletion (maximalIdeal R) R) =
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _)
    (maximalIdeal R).fg_of_isNoetherianRing)).symm

lemma AdicCompletion.mem_maximalIdeal_iff_eval_one_eq_zero [IsNoetherianRing R] [IsLocalRing R]
    (x : AdicCompletion (maximalIdeal R) R) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ↔ x.1 1 = 0 := by
  have : (AdicCompletion.eval (maximalIdeal R) R 1).ker =
    (maximalIdeal R) • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    simp [← pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing]
  rw [maximalIdeal_eq_map, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
  simp [← this, eval]

lemma AdicCompletion.algebraMap_isLocalHom_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  let _ := AdicCompletion.isLocalRing_of_fg fg
  apply ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
  simp [AdicCompletion.maximalIdeal_eq_map_of_fg fg]

instance [IsNoetherianRing R] [IsLocalRing R] :
    IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  AdicCompletion.algebraMap_isLocalHom_of_fg (maximalIdeal R).fg_of_isNoetherianRing

lemma AdicCompletion.isAdicComplete_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    letI := AdicCompletion.isLocalRing_of_fg fg
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (AdicCompletion (maximalIdeal R) R) := by
  rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
  exact AdicCompletion.isAdicComplete_self _ fg

instance [IsNoetherianRing R] [IsLocalRing R] : IsAdicComplete
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)) (AdicCompletion (maximalIdeal R) R) :=
  AdicCompletion.isAdicComplete_of_fg (maximalIdeal R).fg_of_isNoetherianRing

lemma AdicCompletion.residueField_map_bijective_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    haveI := AdicCompletion.isLocalRing_of_fg fg
    haveI := AdicCompletion.algebraMap_isLocalHom_of_fg fg
    Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  have := AdicCompletion.isLocalRing_of_fg fg
  refine ⟨RingHom.injective _, fun x ↦ ?_⟩
  rcases residue_surjective x with ⟨y, hy⟩
  rcases Ideal.Quotient.mk_surjective (y.1 1) with ⟨z, hz⟩
  use residue R z
  rw [IsLocalRing.ResidueField.map_residue, ← hy]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [maximalIdeal_eq_map_of_fg fg, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
  have : (algebraMap R (AdicCompletion (maximalIdeal R) R)) z - y ∈
    (maximalIdeal R) ^ 1 • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    rw [AdicCompletion.algebraMap_apply, pow_smul_top_eq_ker_eval fg]
    simpa [eval, sub_eq_zero] using hz
  simpa

variable (R) in
lemma AdicCompletion.residueField_map_bijective [IsNoetherianRing R] [IsLocalRing R] :
    Function.Bijective (IsLocalRing.ResidueField.map
      (algebraMap R (AdicCompletion (maximalIdeal R) R))) :=
    AdicCompletion.residueField_map_bijective_of_fg (maximalIdeal R).fg_of_isNoetherianRing

lemma AdicCompletion.spanFinrank_maximalIdeal_eq [IsNoetherianRing R] [IsLocalRing R] :
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank =
    (maximalIdeal R).spanFinrank := by
  have fg : (maximalIdeal R).FG := fg_of_isNoetherianRing (maximalIdeal R)
  have comapeq := IsLocalRing.maximalIdeal_comap (algebraMap R (AdicCompletion (maximalIdeal R) R))
  let f := Ideal.mapCotangent _ _ (Algebra.ofId R (AdicCompletion (maximalIdeal R) R))
    (le_of_eq comapeq.symm)
  have inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
    simp only [← hm', mapCotangent_toCotangent, Algebra.ofId_apply, toCotangent_eq_zero,
      maximalIdeal_eq_map, ← Ideal.map_pow, f] at hm
    rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
      pow_smul_top_eq_ker_eval fg] at hm
    have : (algebraMap R (AdicCompletion (maximalIdeal R) R)) m'.1 = of _ R m'.1 := rfl
    simp only [smul_eq_mul, eval, this, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk,
      of_apply, Submodule.mkQ_apply, mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hm
    simpa [← hm', toCotangent_eq_zero] using hm
  have surj : Function.Surjective f := by
    intro m
    rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
    rcases Submodule.Quotient.mk_surjective _ (m'.1.1 2) with ⟨l, hl⟩
    have lmem : (transitionMap _ R (Nat.le_succ 1)) (m'.1.1 2) = m'.1.1 1 := m'.1.2 (Nat.le_succ 1)
    simp only [smul_eq_mul, Nat.succ_eq_add_one, Nat.reduceAdd, transitionMap, Submodule.factorPow,
      Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, ← hl, mk_eq_mk, factor_mk, pow_one,
      (mem_maximalIdeal_iff_eval_one_eq_zero m'.1).mp m'.2, eq_zero_iff_mem, mul_top] at lmem
    use (maximalIdeal R).toCotangent ⟨l, lmem⟩
    simp only [mapCotangent_toCotangent, Algebra.ofId_apply, ← hm', toCotangent_eq, f]
    change (of (maximalIdeal R) R l) - m' ∈ _
    simp only [maximalIdeal_eq_map, ← Ideal.map_pow]
    rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
    simpa [pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing, eval, sub_eq_zero]
      using hl
  have rkeq := rank_eq_of_equiv_equiv _
    (LinearEquiv.ofBijective f ⟨inj, surj⟩).toAddEquiv
    (residueField_map_bijective R) (fun r m ↦ by
      rcases IsLocalRing.residue_surjective r with ⟨s, rfl⟩
      exact map_smul f s m )
  have fg' : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).FG := by
    simpa [AdicCompletion.maximalIdeal_eq_map] using fg.map _
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg fg,
    IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg fg', eq_comm]
  simp [Module.finrank, CotangentSpace, rkeq]
