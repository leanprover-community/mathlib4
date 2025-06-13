/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.GroupTheory.Transfer

/-!
# The Schur-Zassenhaus Theorem

In this file we prove the Schur-Zassenhaus theorem.

## Main results

- `Subgroup.exists_right_complement'_of_coprime`: The **Schur-Zassenhaus** theorem:
  If `H : Subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (right) complement of `H`.
- `Subgroup.exists_left_complement'_of_coprime`: The **Schur-Zassenhaus** theorem:
  If `H : Subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (left) complement of `H`.
-/


namespace Subgroup

section SchurZassenhausAbelian

open MulOpposite MulAction Subgroup.leftTransversals MemLeftTransversals

variable {G : Type*} [Group G] (H : Subgroup G) [IsMulCommutative H] [FiniteIndex H]
  (α β : H.LeftTransversal)

/-- The quotient of the transversals of an abelian normal `N` by the `diff` relation. -/
def QuotientDiff :=
  Quotient
    (Setoid.mk (fun α β => diff (MonoidHom.id H) α β = 1)
      ⟨fun α => diff_self (MonoidHom.id H) α, fun h => by rw [← diff_inv, h, inv_one],
        fun h h' => by rw [← diff_mul_diff, h, h', one_mul]⟩)

instance : Inhabited H.QuotientDiff :=
  inferInstanceAs (Inhabited <| Quotient _)

theorem smul_diff_smul' [hH : Normal H] (g : Gᵐᵒᵖ) :
    diff (MonoidHom.id H) (g • α) (g • β) =
      ⟨g.unop⁻¹ * (diff (MonoidHom.id H) α β : H) * g.unop,
        hH.mem_comm ((congr_arg (· ∈ H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩ := by
  letI := H.fintypeQuotientOfFiniteIndex
  let ϕ : H →* H :=
    { toFun := fun h =>
        ⟨g.unop⁻¹ * h * g.unop,
          hH.mem_comm ((congr_arg (· ∈ H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩
      map_one' := by rw [Subtype.ext_iff, coe_mk, coe_one, mul_one, inv_mul_cancel]
      map_mul' := fun h₁ h₂ => by
        simp only [Subtype.ext_iff, coe_mk, coe_mul, mul_assoc, mul_inv_cancel_left] }
  refine (Fintype.prod_equiv (MulAction.toPerm g).symm _ _ fun x ↦ ?_).trans (map_prod ϕ _ _).symm
  simp only [ϕ, smul_apply_eq_smul_apply_inv_smul, smul_eq_mul_unop, mul_inv_rev, mul_assoc,
    MonoidHom.id_apply, toPerm_symm_apply, MonoidHom.coe_mk, OneHom.coe_mk]

variable {H}
variable [Normal H]

noncomputable instance : MulAction G H.QuotientDiff where
  smul g :=
    Quotient.map' (fun α => op g⁻¹ • α) fun α β h =>
      Subtype.ext
        (by
          rwa [smul_diff_smul', coe_mk, coe_one, mul_eq_one_iff_eq_inv, mul_eq_left, ←
            coe_one, ← Subtype.ext_iff])
  mul_smul g₁ g₂ q :=
    Quotient.inductionOn' q fun T =>
      congr_arg Quotient.mk'' (by rw [mul_inv_rev]; exact mul_smul (op g₁⁻¹) (op g₂⁻¹) T)
  one_smul q :=
    Quotient.inductionOn' q fun T =>
      congr_arg Quotient.mk'' (by rw [inv_one]; apply one_smul Gᵐᵒᵖ T)

theorem smul_diff' (h : H) :
    diff (MonoidHom.id H) α (op (h : G) • β) = diff (MonoidHom.id H) α β * h ^ H.index := by
  letI := H.fintypeQuotientOfFiniteIndex
  rw [diff, diff, index_eq_card, Nat.card_eq_fintype_card,
      ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  simp_rw [Subtype.ext_iff, MonoidHom.id_apply, coe_mul, mul_assoc, mul_right_inj]
  rw [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul_unop, MulOpposite.unop_op, mul_left_inj,
    ← Subtype.ext_iff, Equiv.apply_eq_iff_eq, inv_smul_eq_iff]
  exact left_eq_mul.mpr ((QuotientGroup.eq_one_iff _).mpr h.2)

theorem eq_one_of_smul_eq_one (hH : Nat.Coprime (Nat.card H) H.index) (α : H.QuotientDiff)
    (h : H) : h • α = α → h = 1 :=
  Quotient.inductionOn' α fun α hα =>
    (powCoprime hH).injective <|
      calc
        h ^ H.index = diff (MonoidHom.id H) (op ((h⁻¹ : H) : G) • α) α := by
          rw [← diff_inv, smul_diff', diff_self, one_mul, inv_pow, inv_inv]
        _ = 1 ^ H.index := (Quotient.exact' hα).trans (one_pow H.index).symm

theorem exists_smul_eq (hH : Nat.Coprime (Nat.card H) H.index) (α β : H.QuotientDiff) :
    ∃ h : H, h • α = β :=
  Quotient.inductionOn' α
    (Quotient.inductionOn' β fun β α =>
      Exists.imp (fun _ => Quotient.sound')
        ⟨(powCoprime hH).symm (diff (MonoidHom.id H) β α),
          (diff_inv _ _ _).symm.trans
            (inv_eq_one.mpr
              ((smul_diff' β α ((powCoprime hH).symm (diff (MonoidHom.id H) β α))⁻¹).trans
                (by rw [inv_pow, ← powCoprime_apply hH, Equiv.apply_symm_apply, mul_inv_cancel])))⟩)

theorem isComplement'_stabilizer_of_coprime {α : H.QuotientDiff}
    (hH : Nat.Coprime (Nat.card H) H.index) : IsComplement' H (stabilizer G α) :=
  isComplement'_stabilizer α (eq_one_of_smul_eq_one hH α) fun g => exists_smul_eq hH (g • α) α

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem exists_right_complement'_of_coprime_aux (hH : Nat.Coprime (Nat.card H) H.index) :
    ∃ K : Subgroup G, IsComplement' H K :=
  have ne : Nonempty (QuotientDiff H) := inferInstance
  ne.elim fun α => ⟨stabilizer G α, isComplement'_stabilizer_of_coprime hH⟩

end SchurZassenhausAbelian

universe u

namespace SchurZassenhausInduction

/-! ## Proof of the Schur-Zassenhaus theorem

In this section, we prove the Schur-Zassenhaus theorem.
The proof is by contradiction. We assume that `G` is a minimal counterexample to the theorem.
-/


variable {G : Type u} [Group G] {N : Subgroup G} [Normal N]
  (h1 : Nat.Coprime (Nat.card N) N.index)
  (h2 : ∀ (G' : Type u) [Group G'] [Finite G'],
    Nat.card G' < Nat.card G → ∀ {N' : Subgroup G'} [N'.Normal],
      Nat.Coprime (Nat.card N') N'.index → ∃ H' : Subgroup G', IsComplement' N' H')
  (h3 : ∀ H : Subgroup G, ¬IsComplement' N H)
include h1 h3

/-! We will arrive at a contradiction via the following steps:
* step 0: `N` (the normal Hall subgroup) is nontrivial.
* step 1: If `K` is a subgroup of `G` with `K ⊔ N = ⊤`, then `K = ⊤`.
* step 2: `N` is a minimal normal subgroup, phrased in terms of subgroups of `G`.
* step 3: `N` is a minimal normal subgroup, phrased in terms of subgroups of `N`.
* step 4: `p` (`min_fact (Fintype.card N)`) is prime (follows from step0).
* step 5: `P` (a Sylow `p`-subgroup of `N`) is nontrivial.
* step 6: `N` is a `p`-group (applies step 1 to the normalizer of `P` in `G`).
* step 7: `N` is abelian (applies step 3 to the center of `N`).
-/


/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step0 : N ≠ ⊥ := by
  rintro rfl
  exact h3 ⊤ isComplement'_bot_top

variable [Finite G]

include h2 in
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step1 (K : Subgroup G) (hK : K ⊔ N = ⊤) : K = ⊤ := by
  contrapose! h3
  have h4 : (N.comap K.subtype).index = N.index := by
    rw [← N.relindex_top_right, ← hK]
    exact (relindex_sup_right K N).symm
  have h5 : Nat.card K < Nat.card G := by
    rw [← K.index_mul_card]
    exact lt_mul_of_one_lt_left Nat.card_pos (one_lt_index_of_ne_top h3)
  have h6 : Nat.Coprime (Nat.card (N.comap K.subtype)) (N.comap K.subtype).index := by
    rw [h4]
    exact h1.coprime_dvd_left (card_comap_dvd_of_injective N K.subtype Subtype.coe_injective)
  obtain ⟨H, hH⟩ := h2 K h5 h6
  replace hH : Nat.card (H.map K.subtype) = N.index := by
    rw [← relindex_bot_left, ← relindex_comap, MonoidHom.comap_bot, Subgroup.ker_subtype,
      relindex_bot_left, ← IsComplement'.index_eq_card (IsComplement'.symm hH), index_comap,
      range_subtype, ← relindex_sup_right, hK, relindex_top_right]
  have h7 : Nat.card N * Nat.card (H.map K.subtype) = Nat.card G := by
    rw [hH, ← N.index_mul_card, mul_comm]
  have h8 : (Nat.card N).Coprime (Nat.card (H.map K.subtype)) := by
    rwa [hH]
  exact ⟨H.map K.subtype, isComplement'_of_coprime h7 h8⟩

include h2 in
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step2 (K : Subgroup G) [K.Normal] (hK : K ≤ N) : K = ⊥ ∨ K = N := by
  have : Function.Surjective (QuotientGroup.mk' K) := Quotient.mk''_surjective
  have h4 := step1 h1 h2 h3
  contrapose! h4
  have h5 : Nat.card (G ⧸ K) < Nat.card G := by
    rw [← index_eq_card, ← K.index_mul_card]
    refine
      lt_mul_of_one_lt_right (Nat.pos_of_ne_zero index_ne_zero_of_finite)
        (K.one_lt_card_iff_ne_bot.mpr h4.1)
  have h6 :
    (Nat.card (N.map (QuotientGroup.mk' K))).Coprime (N.map (QuotientGroup.mk' K)).index := by
    have index_map := N.index_map_eq this (by rwa [QuotientGroup.ker_mk'])
    have index_pos : 0 < N.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
    rw [index_map]
    refine h1.coprime_dvd_left ?_
    rw [← Nat.mul_dvd_mul_iff_left index_pos, index_mul_card, ← index_map, index_mul_card]
    exact K.card_quotient_dvd_card
  obtain ⟨H, hH⟩ := h2 (G ⧸ K) h5 h6
  refine ⟨H.comap (QuotientGroup.mk' K), ?_, ?_⟩
  · have key : (N.map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) = N := by
      refine comap_map_eq_self ?_
      rwa [QuotientGroup.ker_mk']
    rwa [← key, comap_sup_eq, hH.symm.sup_eq_top, comap_top]
  · rw [← comap_top (QuotientGroup.mk' K)]
    intro hH'
    rw [comap_injective this hH', isComplement'_top_right, map_eq_bot_iff,
      QuotientGroup.ker_mk'] at hH
    exact h4.2 (le_antisymm hK hH)

include h2 in
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step3 (K : Subgroup N) [(K.map N.subtype).Normal] : K = ⊥ ∨ K = ⊤ := by
  have key := step2 h1 h2 h3 (K.map N.subtype) (map_subtype_le K)
  rw [← map_bot N.subtype] at key
  conv at key =>
    rhs
    rhs
    rw [← N.range_subtype, N.subtype.range_eq_map]
  have inj := map_injective N.subtype_injective
  rwa [inj.eq_iff, inj.eq_iff] at key

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step4 : (Nat.card N).minFac.Prime :=
  Nat.minFac_prime (N.one_lt_card_iff_ne_bot.mpr (step0 h1 h3)).ne'

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step5 {P : Sylow (Nat.card N).minFac N} : P.1 ≠ ⊥ := by
  haveI : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  apply P.ne_bot_of_dvd_card
  exact (Nat.card N).minFac_dvd

include h2 in
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step6 : IsPGroup (Nat.card N).minFac N := by
  haveI : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  refine Sylow.nonempty.elim fun P => P.2.of_surjective P.1.subtype ?_
  rw [← MonoidHom.range_eq_top, range_subtype]
  haveI : (P.1.map N.subtype).Normal :=
    normalizer_eq_top_iff.mp (step1 h1 h2 h3 (P.map N.subtype).normalizer P.normalizer_sup_eq_top)
  exact (step3 h1 h2 h3 P.1).resolve_left (step5 h1 h3)

include h2 in
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
theorem step7 : IsMulCommutative N := by
  haveI := N.bot_or_nontrivial.resolve_left (step0 h1 h3)
  haveI : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  exact
    ⟨⟨fun g h => ((eq_top_iff.mp ((step3 h1 h2 h3 (center N)).resolve_left
      (step6 h1 h2 h3).bot_lt_center.ne') (mem_top h)).comm g).symm⟩⟩

end SchurZassenhausInduction

variable {n : ℕ} {G : Type u} [Group G]

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem exists_right_complement'_of_coprime_aux' [Finite G] (hG : Nat.card G = n)
    {N : Subgroup G} [N.Normal] (hN : Nat.Coprime (Nat.card N) N.index) :
    ∃ H : Subgroup G, IsComplement' N H := by
  revert G
  induction n using Nat.strongRecOn with | ind n ih => ?_
  rintro G _ _ rfl N _ hN
  refine not_forall_not.mp fun h3 => ?_
  haveI := SchurZassenhausInduction.step7 hN (fun G' _ _ hG' => by apply ih _ hG'; rfl) h3
  exact not_exists_of_forall_not h3 (exists_right_complement'_of_coprime_aux hN)

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : Subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index) : ∃ H : Subgroup G, IsComplement' N H := by
  by_cases hN1 : Nat.card N = 0
  · rw [hN1, Nat.coprime_zero_left, index_eq_one] at hN
    rw [hN]
    exact ⟨⊥, isComplement'_top_bot⟩
  by_cases hN2 : N.index = 0
  · rw [hN2, Nat.coprime_zero_right] at hN
    haveI := (Cardinal.toNat_eq_one_iff_unique.mp hN).1
    rw [N.eq_bot_of_subsingleton]
    exact ⟨⊤, isComplement'_bot_top⟩
  have hN3 : Nat.card G ≠ 0 := by
    rw [← N.card_mul_index]
    exact mul_ne_zero hN1 hN2
  haveI := (Cardinal.lt_aleph0_iff_fintype.mp
    (lt_of_not_ge (mt Cardinal.toNat_apply_of_aleph0_le hN3))).some
  exact exists_right_complement'_of_coprime_aux' rfl hN

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : Subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index) : ∃ H : Subgroup G, IsComplement' H N :=
  Exists.imp (fun _ => IsComplement'.symm) (exists_right_complement'_of_coprime hN)

end Subgroup
