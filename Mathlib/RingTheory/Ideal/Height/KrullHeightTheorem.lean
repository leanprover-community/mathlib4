/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Jingting Wang, Andrew Yang, Shouxin Zhang
-/
import Mathlib.RingTheory.Artinian.Noetherian
import Mathlib.RingTheory.Ideal.Height.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Nakayama
/-!
# Krull Height Theorem
-/

#check IsLocalization.isNoetherianRing

variable {R : Type*} [CommRing R] (I : Ideal R)

lemma IsLocalization.isNoetherianRing (I : Ideal R) [I.IsPrime] (A : Type*) [CommRing A]
    [Algebra R A] [IsLocalization.AtPrime A I] [hR : IsNoetherianRing R] : IsNoetherianRing A := by
  infer_instance
  -- sorry
  -- rw [isNoetherianRing_iff, isNoetherian_iff] at hR ⊢
  -- exact OrderEmbedding.wellFounded (IsLocalization.orderEmbedding I.primeCompl A).dual hR

#find_home! IsLocalization.isNoetherianRing

instance (I : Ideal R) [I.IsPrime] [IsNoetherianRing R] :
    IsNoetherianRing (Localization.AtPrime I) := IsLocalization.isNoetherianRing I _

namespace Submodule

open Ideal

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- *Nakayama's Lemma** - A slightly more general version of (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_sup_eq_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`. -/
lemma smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson' {I J : Ideal R}
  {N N' : Submodule R M} (hN' : N'.FG) (hIJ : I ≤ jacobson J)
  (hNN : N' ≤ N ⊔ I • N') : N ⊔ N' = N ⊔ J • N' := by
  replace hNN : N ⊔ N' ≤ N ⊔ I • N' := sup_le le_sup_left hNN
  have hNN' : N ⊔ N' = N ⊔ I • N' :=
    le_antisymm hNN (sup_le_sup_left (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _) _)
  have h_comap := Submodule.comap_injective_of_surjective (LinearMap.range_eq_top.1 (N.range_mkQ))
  have : (I • N').map N.mkQ = N'.map N.mkQ := by
    simp_rw [←h_comap.eq_iff, comap_map_eq]
    rwa [ker_mkQ, eq_comm, sup_comm (I • N'), sup_comm N']
  have := @Submodule.eq_smul_of_le_smul_of_le_jacobson _ _ _ _ _ I J
    (N'.map N.mkQ) (hN'.map _) (by rw [← map_smul'', this]) hIJ
  rw [← map_smul'', ←h_comap.eq_iff, comap_map_eq, comap_map_eq, Submodule.ker_mkQ,
    sup_comm] at this
  rw [this, sup_comm]

/-- *Nakayama's Lemma** - Statement (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
lemma smul_sup_le_of_le_smul_of_le_jacobson_bot' {I : Ideal R}
  {N N' : Submodule R M} (hN' : N'.FG) (hIJ : I ≤ jacobson ⊥)
  (hNN : N' ≤ N ⊔ I • N') : N' ≤ N := by
  rw [← sup_eq_left, smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson' hN' hIJ hNN,
    bot_smul, sup_bot_eq]

end Submodule

variable {R : Type*} [CommRing R]

lemma Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing [IsNoetherianRing R]
    [IsLocalRing R] (I : Ideal R) (hI : I.IsPrincipal)
    (hp : (IsLocalRing.maximalIdeal R) ∈ I.minimalPrimes) :
    (IsLocalRing.maximalIdeal R).height ≤ 1 := by
  sorry
  -- rw [← WithTop.coe_one, Ideal.height_le_iff]
  -- intro q h₁ h₂
  -- suffices q.primeHeight = 0 by rw [Ideal.height_eq_primeHeight, this]; exact zero_lt_one
  -- rw [← Ideal.height_eq_primeHeight,
  --   ← IsLocalization.AtPrime.krullDim_eq_height q (Localization.atPrime q),
  --   ← IsArtinianRing_iff_krullDim_eq_zero,
  --   IsArtinianRing_iff_isNilpotent_maximalIdeal,
  --   ← Localization.AtPrime.map_eq_maximalIdeal]
  -- have hI : I ≠ ⊤ := (hp.1.2.trans_lt
  --   (lt_top_iff_ne_top.mpr (LocalRing.maximalIdeal.isMaximal _).ne_top)).ne
  -- haveI := Ideal.Quotient.nontrivial hI
  -- haveI := LocalRing.ofSurjective' I^.quotient.mk Ideal.Quotient.mk_surjective
  -- have : IsArtinianRing (R ⧸ I) := by
  --   rw [IsArtinianRing_iff_isNilpotent_maximalIdeal,
  --     Ideal.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
  --   refine (Ideal.comap_le_comap_iff_of_surjective I^.quotient.mk Ideal.Quotient.mk_surjective _ _).mp ?_
  --   rw [nilradical, Ideal.comap_radical, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot,
  --     Ideal.mk_ker, LocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective
  --     I^.quotient.mk Ideal.Quotient.mk_surjective), Ideal.radical_eq_inf, le_inf_iff]
  --   -- any_goals apply_instance
  --   exact fun J ⟨hJ₁, hJ₂⟩ => hp.2 ⟨hJ₂, hJ₁⟩ (LocalRing.le_maximalIdeal hJ₂.ne_top)
  -- let f := algebraMap R (Localization.atPrime q)
  -- let qs : ℕ →o (Ideal (R ⧸ I))ᵒᵈ :=
  --   { toFun := fun n => ((q.map f ^ n).comap f).map I^.quotient.mk
  --     monotone' := fun i j e => Ideal.map_mono (Ideal.comap_mono (Ideal.pow_le_pow e)) }
  -- obtain ⟨n, hn⟩ := (@WellFounded.monotone_chain_condition (OrderDual _) _).mp this.1 qs
  -- refine ⟨n, ?_⟩
  -- apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (q.map f) _ (IsNoetherian.noetherian _)
  -- rotate_left
  -- · rw [LocalRing.jacobson_eq_maximalIdeal, Localization.AtPrime.map_eq_maximalIdeal]
  --   exacts [le_rfl, bot_ne_top]
  -- · apply_instance
  -- rw [smul_eq_mul, ← pow_succ,
  --   ← IsLocalization.map_comap q.primeCompl (Localization.atPrime q) (q.map f ^ n),
  --   ← IsLocalization.map_comap q.primeCompl (Localization.atPrime q) (q.map f ^ (n + 1))]
  -- apply Ideal.map_mono
  -- refine Submodule.smul_sup_le_of_le_smul_of_le_jacobson_bot' (IsNoetherian.noetherian _)
  --   (_ : I ≤ _) ?_
  -- · rw [LocalRing.jacobson_eq_maximalIdeal]
  --   exacts [hp.1.2, bot_ne_top]
  -- specialize hn _ n.le_succ
  -- apply_fun Ideal.comap I^.quotient.mk at hn
  -- simp only [qs, OrderHom.coe_fun_mk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
  --   Ideal.comap_map_of_surjective I^.quotient.mk Ideal.Quotient.mk_surjective] at hn
  -- intro x hx
  -- obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ((hn.le : _) (Ideal.mem_sup_left hx))
  -- refine Submodule.add_mem_sup hy ?_
  -- obtain ⟨z, rfl⟩ := I^.isPrincipal.mem_iff_eq_smul_generator.mp hz
  -- rw [smul_eq_mul, smul_eq_mul, mul_comm]
  -- refine Ideal.mul_mem_mul (Submodule.IsPrincipal.generator_mem _) ?_
  -- rwa [Ideal.mem_comap, f.map_add, smul_eq_mul, map_mul, Ideal.add_mem_iff_right _
  --   (Ideal.pow_le_pow n.le_succ hy), mul_comm, Ideal.unit_mul_mem_iff_mem] at hx
  -- refine IsLocalization.map_units _ ⟨_, show I^.isPrincipal.generator ∈ q.primeCompl from ?_⟩
  -- change I^.isPrincipal.generator ∉ (↑q : Set R)
  -- rw [← Set.singleton_subset_iff, ← Ideal.span_le, Ideal.span_singleton_generator]
  -- exact fun e => h₂.not_le (hp.2 ⟨h₁, e⟩ h₂.le)

/-- Krull's Hauptidealsatz -/
lemma Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes [IsNoetherianRing R]
    (I : Ideal R) (hI : I.IsPrincipal) (p : Ideal R) (hp : p ∈ I.minimalPrimes) : p.height ≤ 1 :=
  sorry

/-- Krull height theorem -/
lemma Ideal.height_le_spanRank_toENat_of_mem_minimal_primes [IsNoetherianRing R]
    (I : Ideal R) (p : Ideal R) (hp : p ∈ I.minimalPrimes) :
    p.height ≤ Cardinal.toENat I.spanRank := by
  rw [I.spanRank_toENat_eq_iInf_finset_card]
  apply le_iInf; rintro ⟨s, hs, hspan⟩
  induction' hn : hs.toFinset.card using Nat.strong_induction_on with n H generalizing R
  cases n
  · rw [CharP.cast_eq_zero, nonpos_iff_eq_zero, @Ideal.height_eq_primeHeight _ _ p hp.1.1,
      @Ideal.primeHeight_eq_zero_iff, minimalPrimes]
    simp_all
  · rename ℕ => n
    sorry

lemma Ideal.height_le_spanRank_toENat [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    I.height ≤ Cardinal.toENat I.spanRank := by
  obtain ⟨J, hJ⟩ := Ideal.nonempty_minimalPrimes hI
  refine (iInf₂_le J hJ).trans ?_
  convert (I.height_le_spanRank_toENat_of_mem_minimal_primes J hJ)
  exact Eq.symm (@height_eq_primeHeight _ _ J hJ.1.1)

lemma Ideal.height_le_spanRank [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    I.height ≤ I.spanRank := by
  apply le_trans (b := ((Cardinal.toENat I.spanRank) : Cardinal))
  · norm_cast; exact I.height_le_spanRank_toENat hI
  · exact Cardinal.ofENat_toENat_le (Submodule.spanRank I)

instance Ideal.finite_height_of_is_noetherian_ring [IsNoetherianRing R] (I : Ideal R) :
    I.FiniteHeight := by
  rw [Ideal.finiteHeight_iff_lt, Classical.or_iff_not_imp_left]
  intro h; have := Ideal.height_le_spanRank_toENat I h
  exact lt_of_le_of_lt this (by simpa using (IsNoetherian.noetherian I))

lemma exists_spanRank_eq_and_height_eq [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ J ≤ I, J.spanRank = I.height ∧ J.height = I.height := by
  obtain ⟨J, hJ₁, hJ₂, hJ₃⟩ := exists_spanRank_le_and_le_height_of_le_height I _
    (ENat.coe_toNat_le_self I.height)
  rw [ENat.coe_toNat_eq_self.mpr (Ideal.height_ne_top hI)] at hJ₃
  refine ⟨J, hJ₁, le_antisymm ?_ (le_trans ?_ (J.height_le_spanRank ?_)),
    le_antisymm (Ideal.height_mono hJ₁) hJ₃⟩
  · convert hJ₂; exact Cardinal.ofENat_eq_nat.mpr (ENat.coe_toNat (I.height_ne_top hI)).symm
  · exact Cardinal.ofENat_le_ofENat_of_le hJ₃
  · rintro rfl; exact hI (top_le_iff.mp hJ₁)

lemma Ideal.height_le_iff_exists_minimal_primes [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (n : ℕ∞) : p.height ≤ n ↔ ∃ I : Ideal R, p ∈ I.minimalPrimes ∧ I.spanRank ≤ n := by
  constructor
  · intro h;
    obtain ⟨I, hI, e₁, e₂⟩ := exists_spanRank_eq_and_height_eq p (IsPrime.ne_top ‹_›)
    refine ⟨I, Ideal.mem_minimalPrimes_of_height_eq hI e₂.ge, e₁.symm ▸ ?_⟩
    norm_cast
  · rintro ⟨I, hp, hI⟩; exact le_trans
      (Ideal.height_le_spanRank_toENat_of_mem_minimal_primes I p hp)
      (by simpa using (Cardinal.toENat.monotone' hI))
