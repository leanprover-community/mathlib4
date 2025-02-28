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

variable {R : Type*} [CommRing R]

lemma Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing [IsNoetherianRing R]
    [IsLocalRing R] (I : Ideal R) (hI : I.IsPrincipal)
    (hp : (IsLocalRing.maximalIdeal R) ∈ I.minimalPrimes) :
    (IsLocalRing.maximalIdeal R).height ≤ 1 := by
  apply (Ideal.height_le_iff (p := (IsLocalRing.maximalIdeal R)) (n := 1)).mpr; intro q h₁ h₂
  suffices q.primeHeight = 0 by rw [Ideal.height_eq_primeHeight, this]; exact zero_lt_one
  rw [← Ideal.height_eq_primeHeight, ← WithBot.coe_inj,
    ← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
    WithBot.coe_zero, ← isArtinianRing_iff_ringKrullDim_eq_zero,
    isArtinianRing_iff_isNilpotent_maximalIdeal,
    ← Localization.AtPrime.map_eq_maximalIdeal]
  have hI : I ≠ ⊤ := (hp.1.2.trans_lt
    (lt_top_iff_ne_top.mpr (IsLocalRing.maximalIdeal.isMaximal _).ne_top)).ne
  haveI := Ideal.Quotient.nontrivial hI
  haveI := IsLocalRing.of_surjective' _ (Ideal.Quotient.mk_surjective (I := I))
  have : IsArtinianRing (R ⧸ I) := by
    rw [isArtinianRing_iff_isNilpotent_maximalIdeal,
      Ideal.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    refine (Ideal.comap_le_comap_iff_of_surjective _ Ideal.Quotient.mk_surjective _ _).mp ?_
    rw [nilradical, Ideal.comap_radical, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective
      _ (Ideal.Quotient.mk_surjective (I := I))), Ideal.radical_eq_sInf, le_sInf_iff]
    exact fun J ⟨hJ₁, hJ₂⟩ => hp.2 ⟨hJ₂, hJ₁⟩ (IsLocalRing.le_maximalIdeal hJ₂.ne_top)
  let f := algebraMap R (Localization.AtPrime q)
  let qs : ℕ →o (Ideal (R ⧸ I))ᵒᵈ :=
    { toFun := fun n => ((q.map f ^ n).comap f).map (Ideal.Quotient.mk (I := I))
      monotone' := fun i j e => Ideal.map_mono (Ideal.comap_mono (Ideal.pow_le_pow_right e)) }
  obtain ⟨n, hn⟩ := (@wellFoundedGT_iff_monotone_chain_condition (OrderDual _) _).mp (by
    rw [wellFoundedGT_dual_iff]; exact this) qs
  refine ⟨n, (?_ : q.map f ^ n = 0)⟩
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (q.map f) _ (IsNoetherian.noetherian _)
  rotate_left
  · rw [IsLocalRing.jacobson_eq_maximalIdeal, Localization.AtPrime.map_eq_maximalIdeal]
    exact bot_ne_top
  rw [smul_eq_mul, ← pow_succ',
    ← IsLocalization.map_comap q.primeCompl (Localization.AtPrime q) (q.map f ^ n),
    ← IsLocalization.map_comap q.primeCompl (Localization.AtPrime q) (q.map f ^ (n + 1))]
  apply Ideal.map_mono
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) (_ : I ≤ _)
  swap
  · rw [IsLocalRing.jacobson_eq_maximalIdeal]
    exacts [hp.1.2, bot_ne_top]
  · specialize hn _ n.le_succ
    apply_fun Ideal.comap (Ideal.Quotient.mk (I := I)) at hn
    simp only [qs, OrderHom.coe_mk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      Ideal.comap_map_of_surjective (Ideal.Quotient.mk (I := I)) Ideal.Quotient.mk_surjective] at hn
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ((hn.le : _) (Ideal.mem_sup_left hx))
    refine Submodule.add_mem_sup hy ?_
    obtain ⟨z, rfl⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hz
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
    refine Ideal.mul_mem_mul ?_ (Submodule.IsPrincipal.generator_mem _)
    rwa [Ideal.mem_comap, f.map_add, smul_eq_mul, f.map_mul, Ideal.add_mem_iff_right _
      (Ideal.pow_le_pow_right n.le_succ hy), mul_comm, Ideal.unit_mul_mem_iff_mem] at hx
    refine IsLocalization.map_units _ ⟨_,
      show Submodule.IsPrincipal.generator I ∈ q.primeCompl from ?_⟩
    show Submodule.IsPrincipal.generator I ∉ (↑q : Set R)
    rw [← Set.singleton_subset_iff, ← Ideal.span_le, Ideal.span_singleton_generator]
    exact fun e => h₂.not_le (hp.2 ⟨h₁, e⟩ h₂.le)

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
