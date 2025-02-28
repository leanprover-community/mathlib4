import Mathlib.RingTheory.Artinian.Noetherian
import Mathlib.RingTheory.Ideal.Height.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Nakayama

variable {R : Type*} [CommRing R] (I : Ideal R)

lemma Ideal.isMaximal_iff_forall_isPrime {I : Ideal R} :
  I.IsMaximal ↔ I ≠ ⊤ ∧ ∀ J, Ideal.IsPrime J → I ≤ J → I = J := by
  constructor
  · intro H
    exact ⟨H.ne_top, fun J hJ e => H.eq_of_le hJ.ne_top e⟩
  · intro H
    obtain ⟨m, hm, hm'⟩ := Ideal.exists_le_maximal _ H.1
    rwa [H.2 m hm.isPrime hm']

lemma IsLocalization.isNoetherianRing (I : Ideal R) [I.IsPrime] (A : Type*) [CommRing A]
  [Algebra R A] [IsLocalization.AtPrime A I] [hR : IsNoetherianRing R] :
  IsNoetherianRing A := by
  rw [isNoetherianRing_iff, isNoetherian_iff] at hR ⊢
  exact OrderEmbedding.wellFounded (IsLocalization.orderEmbedding I.primeCompl A).dual hR

instance (I : Ideal R) [I.IsPrime] [IsNoetherianRing R] :
  IsNoetherianRing (Localization.AtPrime I) :=
  IsLocalization.isNoetherianRing I _

lemma IsArtinianRing.eq_maximalIdeal_of_isPrime [IsArtinianRing R] [IsLocalRing R]
  (I : Ideal R) [I.IsPrime] : I = IsLocalRing.maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal <|
    ((isArtinianRing_iff_isNoetherianRing_and_primes_maximal).mp ‹_›).2 _ ‹_›

lemma IsArtinianRing.radical_eq_maximalIdeal [IsArtinianRing R] [IsLocalRing R]
  (I : Ideal R) (hI : I ≠ ⊤) : I.radical = IsLocalRing.maximalIdeal R := by
  rw [Ideal.radical_eq_sInf]
  refine (sInf_le ?_).antisymm (le_sInf ?_)
  · exact ⟨IsLocalRing.le_maximalIdeal hI, inferInstance⟩
  · rintro J ⟨h₁, h₂⟩
    exact (IsArtinianRing.eq_maximalIdeal_of_isPrime J).ge

lemma isArtinianRing_iff_isNilpotent_maximalIdeal [IsNoetherianRing R] [IsLocalRing R] :
  IsArtinianRing R ↔ IsNilpotent (IsLocalRing.maximalIdeal R) := by
  constructor
  · intro h
    rw [← IsArtinianRing.radical_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
    exact IsArtinianRing.isNilpotent_nilradical
  · rintro ⟨n, hn⟩
    rcases eq_or_ne n 0 with (rfl|hn')
    · rw [pow_zero] at hn
      exact (one_ne_zero hn).elim
    · rw [isArtinianRing_iff_isNoetherianRing_and_primes_maximal]
      refine ⟨inferInstance, fun I hI => ?_⟩
      suffices IsLocalRing.maximalIdeal R ≤ I by
        rw [← (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hI.ne_top this]
        infer_instance
      rw [← hI.pow_le_iff hn', hn]
      exact bot_le

lemma Ideal.exists_pow_le_of_fg {R : Type*} [CommSemiring R] (I J : Ideal R) (h : I.FG)
  (h' : I ≤ J.radical) :
  ∃ n : ℕ, I ^ n ≤ J := by
  revert h'
  refine Submodule.fg_induction _ _ (fun I => I ≤ J.radical → ∃ n : ℕ, I ^ n ≤ J) ?_ ?_ _ h
  · intro x hx
    obtain ⟨n, hn⟩ := hx (Ideal.subset_span (Set.mem_singleton x))
    exact ⟨n, by rwa [← Ideal.span, Ideal.span_singleton_pow, Ideal.span_le,
      Set.singleton_subset_iff]⟩
  · intros J K hJ hK hJK
    obtain ⟨n, hn⟩ := hJ (fun x hx => hJK <| Ideal.mem_sup_left hx)
    obtain ⟨m, hm⟩ := hK (fun x hx => hJK <| Ideal.mem_sup_right hx)
    use n + m
    rw [← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup, Finset.sup_le_iff]
    refine fun i hi => Ideal.mul_le_right.trans ?_
    obtain h | h := le_or_lt n i
    · exact Ideal.mul_le_right.trans ((Ideal.pow_le_pow_right h).trans hn)
    · refine Ideal.mul_le_left.trans ((Ideal.pow_le_pow_right ?_).trans hm)
      rw [add_comm, Nat.add_sub_assoc h.le]
      apply Nat.le_add_right

lemma Ideal.isNilpotent_iff_le_nilradical {I : Ideal R} (hI : I.FG) :
  IsNilpotent I ↔ I ≤ nilradical R :=
⟨fun ⟨n, hn⟩ _ hx => ⟨n, hn ▸ Ideal.pow_mem_pow hx n⟩,
  fun h => let ⟨n, hn⟩ := Ideal.exists_pow_le_of_fg I ⊥ hI h; ⟨n, le_bot_iff.mp hn⟩⟩

namespace Submodule

open Ideal

variables {M : Type*} [AddCommGroup M] [Module R M]

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
