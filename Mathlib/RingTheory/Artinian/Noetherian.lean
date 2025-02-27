/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jingting Wang, Andrew Yang, Shouxin Zhang
-/
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Relation between Artinian and Noetherian

In this file, we establish several results linking Artinian property and Noetherian property.

-/
open Set Submodule

section Ideal

lemma isNoetherian_iff_isArtinian_of_mul {R : Type*} [CommRing R] (I J : Ideal R) [I.IsMaximal]
  (H : IsNoetherian R (I * J : Submodule R R) ↔ IsArtinian R (I * J : Submodule R R)) :
  IsNoetherian R J ↔ IsArtinian R J := by
  let IJ := Submodule.comap J.subtype (I * J)
  have : Module.IsTorsionBySet R (J ⧸ IJ) I := by
    intro x ⟨y, hy⟩
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective IJ x
    rw [Subtype.coe_mk, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show _ ∈ I * J
    simp [Ideal.mul_mem_mul hy hx]
  letI : Module (R ⧸ I) (J ⧸ IJ) := this.module
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have tfae_out := (IsArtinianRing.tfae (R ⧸ I) (J ⧸ IJ)).out 1 2
  have : IsNoetherian R (J ⧸ IJ) ↔ IsArtinian R (J ⧸ IJ) := by
    rw [isNoetherian_iff_tower_of_surjective (J ⧸ IJ) this, tfae_out,
        ← isArtinian_iff_tower_of_surjective (J ⧸ IJ) this]
  constructor
  · intro hNoetherianJ
    haveI := this.mp inferInstance
    haveI : IsArtinian R (I * J : Submodule R R) := H.mp (isNoetherian_of_le Ideal.mul_le_left)
    apply isArtinian_of_range_eq_ker
      (Submodule.inclusion Ideal.mul_le_left : (I * J : Submodule R R) →ₗ[R] J) IJ.mkQ
    simp [Submodule.range_inclusion]
    rfl
  · intro hArtinianJ
    haveI := this.mpr inferInstance
    haveI : IsNoetherian R (I * J : Submodule R R) := H.mpr (isArtinian_of_le Ideal.mul_le_left)
    apply isNoetherian_of_range_eq_ker
      (Submodule.inclusion Ideal.mul_le_left : (I * J : Submodule R R) →ₗ[R] J) IJ.mkQ
    simp [Submodule.range_inclusion]
    rfl

end Ideal

section Noetherian

variable {R : Type*} [CommRing R]

lemma isNoetherian_iff_isArtinian_of_prod_eq_bot (s : Multiset (Ideal R))
    (hs : ∀ I ∈ s, Ideal.IsMaximal I) (h' : Multiset.prod s = ⊥) :
    IsNoetherianRing R ↔ IsArtinianRing R := by
  rw [isNoetherianRing_iff, ← isNoetherian_top_iff, isArtinianRing_iff, ← isArtinian_top_iff]
  by_contra h
  suffices ¬(IsNoetherian R (⊥ : Ideal R) ↔ IsArtinian R (⊥ : Ideal R)) by
    apply this
    exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩
  rw [← h']
  clear h'
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.prod_zero, Ideal.one_eq_top]
    exact h
  | cons a s hs' =>
    rw [Multiset.prod_cons]
    intro hs''
    apply hs' (fun I hMem => hs I (Multiset.mem_cons_of_mem hMem))
    haveI := hs a (Multiset.mem_cons_self a s)
    exact isNoetherian_iff_isArtinian_of_mul _ _ hs''

lemma isArtinianRing_iff_isNoetherianRing_and_primes_maximal :
    IsArtinianRing R ↔ IsNoetherianRing R ∧ ∀ I : Ideal R, I.IsPrime → I.IsMaximal := by
  cases' subsingleton_or_nontrivial R with h h
  · exact ⟨fun _ => ⟨inferInstance, by
      exact fun I a ↦ (fun p ↦ (IsArtinianRing.isPrime_iff_isMaximal p).mp) I a⟩,
        fun _ => inferInstance⟩
  · constructor
    · intro H
      obtain ⟨s, hs, hs'⟩ :=
        IsArtinianRing.exists_multiset_ideal_is_maximal_and_prod_eq_bot (R := R)
      have := isNoetherian_iff_isArtinian_of_prod_eq_bot s hs hs'
      simp_rw [IsArtinianRing.isPrime_iff_isMaximal, this]
      exact ⟨H, fun _ h => h⟩
    · rintro ⟨h₁, h₂⟩
      obtain ⟨n, e⟩ := IsNoetherianRing.isNilpotent_nilradical R
      rwa [← isNoetherian_iff_isArtinian_of_prod_eq_bot
        (n • (minimalPrimes.finite_of_isNoetherianRing R).toFinset.1) _ _]
      · simp_rw [Multiset.mem_nsmul, ← Finset.mem_def, Set.Finite.mem_toFinset]
        exact fun I ↦ fun hI ↦  h₂ _ hI.2.1.1
      · rw [Multiset.prod_nsmul, eq_bot_iff, ← Ideal.zero_eq_bot, ← e, nilradical,
          ← Ideal.sInf_minimalPrimes, Finset.prod_val]
        apply Ideal.pow_right_mono
        refine Ideal.prod_le_inf.trans (le_sInf fun I hI => Finset.inf_le ?_)
        rwa [Set.Finite.mem_toFinset]

end Noetherian
