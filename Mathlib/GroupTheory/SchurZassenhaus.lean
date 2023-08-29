/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer

#align_import group_theory.schur_zassenhaus from "leanprover-community/mathlib"@"d57133e49cf06508700ef69030cd099917e0f0de"

/-!
# The Schur-Zassenhaus Theorem

In this file we prove the Schur-Zassenhaus theorem.

## Main results

- `exists_right_complement'_of_coprime` : The **Schur-Zassenhaus** theorem:
  If `H : Subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (right) complement of `H`.
- `exists_left_complement'_of_coprime` : The **Schur-Zassenhaus** theorem:
  If `H : Subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (left) complement of `H`.
-/


open scoped BigOperators

namespace Subgroup

section SchurZassenhausAbelian

open MulOpposite MulAction Subgroup.leftTransversals MemLeftTransversals

variable {G : Type*} [Group G] (H : Subgroup G) [IsCommutative H] [FiniteIndex H]
  (α β : leftTransversals (H : Set G))

/-- The quotient of the transversals of an abelian normal `N` by the `diff` relation. -/
def QuotientDiff :=
  Quotient
    (Setoid.mk (fun α β => diff (MonoidHom.id H) α β = 1)
      ⟨fun α => diff_self (MonoidHom.id H) α, fun h => by rw [← diff_inv, h, inv_one],
                                                          -- 🎉 no goals
        fun h h' => by rw [← diff_mul_diff, h, h', one_mul]⟩)
                       -- 🎉 no goals
#align subgroup.quotient_diff Subgroup.QuotientDiff

instance : Inhabited H.QuotientDiff := by
  dsimp [QuotientDiff] -- porting note: Added `dsimp`
  -- ⊢ Inhabited (Quotient { r := fun α β => diff (MonoidHom.id { x // x ∈ H }) α β …
  infer_instance
  -- 🎉 no goals

theorem smul_diff_smul' [hH : Normal H] (g : Gᵐᵒᵖ) :
    diff (MonoidHom.id H) (g • α) (g • β) =
      ⟨g.unop⁻¹ * (diff (MonoidHom.id H) α β : H) * g.unop,
        hH.mem_comm ((congr_arg (· ∈ H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩ := by
  letI := H.fintypeQuotientOfFiniteIndex
  -- ⊢ diff (MonoidHom.id { x // x ∈ H }) (g • α) (g • β) = { val := (unop g)⁻¹ * ↑ …
  let ϕ : H →* H :=
    { toFun := fun h =>
        ⟨g.unop⁻¹ * h * g.unop,
          hH.mem_comm ((congr_arg (· ∈ H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩
      map_one' := by rw [Subtype.ext_iff, coe_mk, coe_one, mul_one, inv_mul_self]
      map_mul' := fun h₁ h₂ => by
        simp only [Subtype.ext_iff, coe_mk, coe_mul, mul_assoc, mul_inv_cancel_left] }
  refine'
    Eq.trans
      (Finset.prod_bij' (fun q _ => g⁻¹ • q) (fun q _ => Finset.mem_univ _)
        (fun q _ => Subtype.ext _) (fun q _ => g • q) (fun q _ => Finset.mem_univ _)
        (fun q _ => smul_inv_smul g q) fun q _ => inv_smul_smul g q)
      (map_prod ϕ _ _).symm
  simp only [MonoidHom.id_apply, MonoidHom.coe_mk, OneHom.coe_mk,
    smul_apply_eq_smul_apply_inv_smul, smul_eq_mul_unop, mul_inv_rev, mul_assoc]
#align subgroup.smul_diff_smul' Subgroup.smul_diff_smul'

variable {H} [Normal H]

noncomputable instance : MulAction G H.QuotientDiff where
  smul g :=
    Quotient.map' (fun α => op g⁻¹ • α) fun α β h =>
      Subtype.ext
        (by
          rwa [smul_diff_smul', coe_mk, coe_one, mul_eq_one_iff_eq_inv, mul_right_eq_self, ←
            coe_one, ← Subtype.ext_iff])
  mul_smul g₁ g₂ q :=
    Quotient.inductionOn' q fun T =>
      congr_arg Quotient.mk'' (by rw [mul_inv_rev]; exact mul_smul (op g₁⁻¹) (op g₂⁻¹) T)
                                  -- ⊢ (fun α => op (g₂⁻¹ * g₁⁻¹) • α) T = (fun α => op g₁⁻¹ • α) ((fun α => op g₂⁻ …
                                                    -- 🎉 no goals
  one_smul q :=
                                  -- ⊢ (fun α => op 1 • α) T = T
                                                -- 🎉 no goals
    Quotient.inductionOn' q fun T =>
      congr_arg Quotient.mk'' (by rw [inv_one]; apply one_smul Gᵐᵒᵖ T)

theorem smul_diff' (h : H) :
    diff (MonoidHom.id H) α (op (h : G) • β) = diff (MonoidHom.id H) α β * h ^ H.index := by
  letI := H.fintypeQuotientOfFiniteIndex
  -- ⊢ diff (MonoidHom.id { x // x ∈ H }) α (op ↑h • β) = diff (MonoidHom.id { x // …
  rw [diff, diff, index_eq_card, ←Finset.card_univ, ←Finset.prod_const, ←Finset.prod_mul_distrib]
  -- ⊢ (let α_1 := toEquiv (_ : ↑α ∈ leftTransversals ↑H);
  refine' Finset.prod_congr rfl fun q _ => _
  -- ⊢ ↑(MonoidHom.id { x // x ∈ H }) { val := (↑(↑(toEquiv (_ : ↑α ∈ leftTransvers …
  simp_rw [Subtype.ext_iff, MonoidHom.id_apply, coe_mul, mul_assoc, mul_right_inj]
  -- ⊢ ↑(↑(toEquiv (_ : ↑(op ↑h • β) ∈ leftTransversals ↑H)) q) = ↑(↑(toEquiv (_ :  …
  rw [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul_unop, unop_op, mul_left_inj, ←Subtype.ext_iff,
    Equiv.apply_eq_iff_eq, inv_smul_eq_iff]
  exact self_eq_mul_right.mpr ((QuotientGroup.eq_one_iff _).mpr h.2)
  -- 🎉 no goals
#align subgroup.smul_diff' Subgroup.smul_diff'

theorem eq_one_of_smul_eq_one (hH : Nat.coprime (Nat.card H) H.index) (α : H.QuotientDiff)
  (h : H) : h • α = α → h = 1 :=
  Quotient.inductionOn' α fun α hα =>
    (powCoprime hH).injective <|
      calc
        h ^ H.index = diff (MonoidHom.id H) (op ((h⁻¹ : H) : G) • α) α := by
          rw [← diff_inv, smul_diff', diff_self, one_mul, inv_pow, inv_inv]
          -- 🎉 no goals
        _ = 1 ^ H.index := (Quotient.exact' hα).trans (one_pow H.index).symm

#align subgroup.eq_one_of_smul_eq_one Subgroup.eq_one_of_smul_eq_one

theorem exists_smul_eq (hH : Nat.coprime (Nat.card H) H.index) (α β : H.QuotientDiff) :
    ∃ h : H, h • α = β :=
  Quotient.inductionOn' α
    (Quotient.inductionOn' β fun β α =>
      Exists.imp (fun n => Quotient.sound')
        ⟨(powCoprime hH).symm (diff (MonoidHom.id H) β α),
          (diff_inv _ _ _).symm.trans
            (inv_eq_one.mpr
              ((smul_diff' β α ((powCoprime hH).symm (diff (MonoidHom.id H) β α))⁻¹).trans
                (by rw [inv_pow, ← powCoprime_apply hH, Equiv.apply_symm_apply, mul_inv_self])))⟩)
                    -- 🎉 no goals
#align subgroup.exists_smul_eq Subgroup.exists_smul_eq

theorem isComplement'_stabilizer_of_coprime {α : H.QuotientDiff}
    (hH : Nat.coprime (Nat.card H) H.index) : IsComplement' H (stabilizer G α) :=
  isComplement'_stabilizer α (eq_one_of_smul_eq_one hH α) fun g => exists_smul_eq hH (g • α) α
#align subgroup.is_complement'_stabilizer_of_coprime Subgroup.isComplement'_stabilizer_of_coprime

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem exists_right_complement'_of_coprime_aux (hH : Nat.coprime (Nat.card H) H.index) :
    ∃ K : Subgroup G, IsComplement' H K :=
  instNonempty.elim fun α => ⟨stabilizer G α, isComplement'_stabilizer_of_coprime hH⟩

end SchurZassenhausAbelian

open scoped Classical

universe u

namespace SchurZassenhausInduction

/-! ## Proof of the Schur-Zassenhaus theorem

In this section, we prove the Schur-Zassenhaus theorem.
The proof is by contradiction. We assume that `G` is a minimal counterexample to the theorem.
-/


variable {G : Type u} [Group G] [Fintype G] {N : Subgroup G} [Normal N]
  (h1 : Nat.coprime (Fintype.card N) N.index)
  (h2 :
    ∀ (G' : Type u) [Group G'] [Fintype G'],
      ∀ (_ : Fintype.card G' < Fintype.card G) {N' : Subgroup G'} [N'.Normal]
        (_ : Nat.coprime (Fintype.card N') N'.index), ∃ H' : Subgroup G', IsComplement' N' H')
  (h3 : ∀ H : Subgroup G, ¬IsComplement' N H)

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
  -- ⊢ False
  exact h3 ⊤ isComplement'_bot_top
  -- 🎉 no goals

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step1 (K : Subgroup G) (hK : K ⊔ N = ⊤) : K = ⊤ := by
  contrapose! h3
  -- ⊢ ∃ H, IsComplement' N H
  have h4 : (N.comap K.subtype).index = N.index := by
    rw [← N.relindex_top_right, ← hK]
    exact (relindex_sup_right K N).symm
  have h5 : Fintype.card K < Fintype.card G := by
    rw [← K.index_mul_card]
    exact lt_mul_of_one_lt_left Fintype.card_pos (one_lt_index_of_ne_top h3)
  have h6 : Nat.coprime (Fintype.card (N.comap K.subtype)) (N.comap K.subtype).index := by
    rw [h4]
    exact h1.coprime_dvd_left (card_comap_dvd_of_injective N K.subtype Subtype.coe_injective)
  obtain ⟨H, hH⟩ := h2 K h5 h6
  -- ⊢ ∃ H, IsComplement' N H
  replace hH : Fintype.card (H.map K.subtype) = N.index := by
    rw [←relindex_bot_left_eq_card, ←relindex_comap, MonoidHom.comap_bot, Subgroup.ker_subtype,
      relindex_bot_left, ←IsComplement'.index_eq_card (IsComplement'.symm hH), index_comap,
      subtype_range, ←relindex_sup_right, hK, relindex_top_right]
  have h7 : Fintype.card N * Fintype.card (H.map K.subtype) = Fintype.card G := by
    rw [hH, ← N.index_mul_card, mul_comm]
  have h8 : (Fintype.card N).coprime (Fintype.card (H.map K.subtype)) := by
    rwa [hH]
  exact ⟨H.map K.subtype, isComplement'_of_coprime h7 h8⟩
  -- 🎉 no goals

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step2 (K : Subgroup G) [K.Normal] (hK : K ≤ N) : K = ⊥ ∨ K = N := by
  have : Function.Surjective (QuotientGroup.mk' K) := Quotient.surjective_Quotient_mk''
  -- ⊢ K = ⊥ ∨ K = N
  have h4 := step1 h1 h2 h3
  -- ⊢ K = ⊥ ∨ K = N
  contrapose! h4
  -- ⊢ ∃ K, K ⊔ N = ⊤ ∧ K ≠ ⊤
  have h5 : Fintype.card (G ⧸ K) < Fintype.card G := by
    rw [← index_eq_card, ← K.index_mul_card]
    refine'
      lt_mul_of_one_lt_right (Nat.pos_of_ne_zero index_ne_zero_of_finite)
        (K.one_lt_card_iff_ne_bot.mpr h4.1)
  have h6 :
    (Fintype.card (N.map (QuotientGroup.mk' K))).coprime (N.map (QuotientGroup.mk' K)).index := by
    have index_map := N.index_map_eq this (by rwa [QuotientGroup.ker_mk'])
    have index_pos : 0 < N.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
    rw [index_map]
    refine' h1.coprime_dvd_left _
    rw [← Nat.mul_dvd_mul_iff_left index_pos, index_mul_card, ← index_map, index_mul_card]
    exact K.card_quotient_dvd_card
  obtain ⟨H, hH⟩ := h2 (G ⧸ K) h5 h6
  -- ⊢ ∃ K, K ⊔ N = ⊤ ∧ K ≠ ⊤
  refine' ⟨H.comap (QuotientGroup.mk' K), _, _⟩
  -- ⊢ comap (QuotientGroup.mk' K) H ⊔ N = ⊤
  · have key : (N.map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) = N := by
      refine' comap_map_eq_self _
      rwa [QuotientGroup.ker_mk']
    rwa [← key, comap_sup_eq, hH.symm.sup_eq_top, comap_top]
    -- 🎉 no goals
  · rw [← comap_top (QuotientGroup.mk' K)]
    -- ⊢ comap (QuotientGroup.mk' K) H ≠ comap (QuotientGroup.mk' K) ⊤
    intro hH'
    -- ⊢ False
    rw [comap_injective this hH', isComplement'_top_right, map_eq_bot_iff,
      QuotientGroup.ker_mk'] at hH
    · exact h4.2 (le_antisymm hK hH)
      -- 🎉 no goals

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step3 (K : Subgroup N) [(K.map N.subtype).Normal] : K = ⊥ ∨ K = ⊤ := by
  have key := step2 h1 h2 h3 (K.map N.subtype) (map_subtype_le K)
  -- ⊢ K = ⊥ ∨ K = ⊤
  rw [← map_bot N.subtype] at key
  -- ⊢ K = ⊥ ∨ K = ⊤
  conv at key =>
    rhs
    rhs
    rw [← N.subtype_range, N.subtype.range_eq_map]
  have inj := map_injective N.subtype_injective
  -- ⊢ K = ⊥ ∨ K = ⊤
  rwa [inj.eq_iff, inj.eq_iff] at key
  -- 🎉 no goals

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step4 : (Fintype.card N).minFac.Prime :=
  Nat.minFac_prime (N.one_lt_card_iff_ne_bot.mpr (step0 h1 h3)).ne'

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step5 {P : Sylow (Fintype.card N).minFac N} : P.1 ≠ ⊥ :=
  haveI : Fact (Fintype.card N).minFac.Prime := ⟨step4 h1 h3⟩
  P.ne_bot_of_dvd_card (Fintype.card N).minFac_dvd

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step6 : IsPGroup (Fintype.card N).minFac N := by
  haveI : Fact (Fintype.card N).minFac.Prime := ⟨step4 h1 h3⟩
  -- ⊢ IsPGroup (Nat.minFac (Fintype.card { x // x ∈ N })) { x // x ∈ N }
  refine' Sylow.nonempty.elim fun P => P.2.of_surjective P.1.subtype _
  -- ⊢ Function.Surjective ↑(Subgroup.subtype ↑P)
  rw [← MonoidHom.range_top_iff_surjective, subtype_range]
  -- ⊢ ↑P = ⊤
  haveI : (P.1.map N.subtype).Normal :=
    normalizer_eq_top.mp (step1 h1 h2 h3 (P.1.map N.subtype).normalizer P.normalizer_sup_eq_top)
  exact (step3 h1 h2 h3 P.1).resolve_left (step5 h1 h3)
  -- 🎉 no goals

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
theorem step7 : IsCommutative N := by
  haveI := N.bot_or_nontrivial.resolve_left (step0 h1 h3)
  -- ⊢ IsCommutative N
  haveI : Fact (Fintype.card N).minFac.Prime := ⟨step4 h1 h3⟩
  -- ⊢ IsCommutative N
  exact
    ⟨⟨fun g h =>
        eq_top_iff.mp ((step3 h1 h2 h3 (center N)).resolve_left (step6 h1 h2 h3).bot_lt_center.ne')
          (mem_top h) g⟩⟩
#align subgroup.schur_zassenhaus_induction.step7 Subgroup.SchurZassenhausInduction.step7

end SchurZassenhausInduction

variable {n : ℕ} {G : Type u} [Group G]

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem exists_right_complement'_of_coprime_aux' [Fintype G] (hG : Fintype.card G = n)
    {N : Subgroup G} [N.Normal] (hN : Nat.coprime (Fintype.card N) N.index) :
    ∃ H : Subgroup G, IsComplement' N H := by
  revert G
  -- ⊢ ∀ {G : Type u} [inst : Group G] [inst_1 : Fintype G], Fintype.card G = n → ∀ …
  apply Nat.strongInductionOn n
  -- ⊢ ∀ (n : ℕ), (∀ (m : ℕ), m < n → ∀ {G : Type u} [inst : Group G] [inst_1 : Fin …
  rintro n ih G _ _ rfl N _ hN
  -- ⊢ ∃ H, IsComplement' N H
  refine' not_forall_not.mp fun h3 => _
  -- ⊢ False
  haveI := SchurZassenhausInduction.step7 hN (fun G' _ _ hG' => by apply ih _ hG'; rfl) h3
  -- ⊢ False
  rw [← Nat.card_eq_fintype_card] at hN
  -- ⊢ False
  exact not_exists_of_forall_not h3 (exists_right_complement'_of_coprime_aux hN)
  -- 🎉 no goals

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : Subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime_of_fintype [Fintype G] {N : Subgroup G} [N.Normal]
    (hN : Nat.coprime (Fintype.card N) N.index) : ∃ H : Subgroup G, IsComplement' N H :=
  exists_right_complement'_of_coprime_aux' rfl hN
#align subgroup.exists_right_complement'_of_coprime_of_fintype Subgroup.exists_right_complement'_of_coprime_of_fintype

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : Subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime {N : Subgroup G} [N.Normal]
    (hN : Nat.coprime (Nat.card N) N.index) : ∃ H : Subgroup G, IsComplement' N H := by
  by_cases hN1 : Nat.card N = 0
  -- ⊢ ∃ H, IsComplement' N H
  · rw [hN1, Nat.coprime_zero_left, index_eq_one] at hN
    -- ⊢ ∃ H, IsComplement' N H
    rw [hN]
    -- ⊢ ∃ H, IsComplement' ⊤ H
    exact ⟨⊥, isComplement'_top_bot⟩
    -- 🎉 no goals
  by_cases hN2 : N.index = 0
  -- ⊢ ∃ H, IsComplement' N H
  · rw [hN2, Nat.coprime_zero_right] at hN
    -- ⊢ ∃ H, IsComplement' N H
    haveI := (Cardinal.toNat_eq_one_iff_unique.mp hN).1
    -- ⊢ ∃ H, IsComplement' N H
    rw [N.eq_bot_of_subsingleton]
    -- ⊢ ∃ H, IsComplement' ⊥ H
    exact ⟨⊤, isComplement'_bot_top⟩
    -- 🎉 no goals
  have hN3 : Nat.card G ≠ 0 := by
    rw [← N.card_mul_index]
    exact mul_ne_zero hN1 hN2
  haveI := (Cardinal.lt_aleph0_iff_fintype.mp
    (lt_of_not_ge (mt Cardinal.toNat_apply_of_aleph0_le hN3))).some
  apply exists_right_complement'_of_coprime_of_fintype
  -- ⊢ Nat.coprime (Fintype.card { x // x ∈ N }) (index N)
  rwa [←Nat.card_eq_fintype_card]
  -- 🎉 no goals
#align subgroup.exists_right_complement'_of_coprime Subgroup.exists_right_complement'_of_coprime

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : Subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime_of_fintype [Fintype G] {N : Subgroup G} [N.Normal]
    (hN : Nat.coprime (Fintype.card N) N.index) : ∃ H : Subgroup G, IsComplement' H N :=
  Exists.imp (fun _ => IsComplement'.symm) (exists_right_complement'_of_coprime_of_fintype hN)
#align subgroup.exists_left_complement'_of_coprime_of_fintype Subgroup.exists_left_complement'_of_coprime_of_fintype

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : Subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime {N : Subgroup G} [N.Normal]
    (hN : Nat.coprime (Nat.card N) N.index) : ∃ H : Subgroup G, IsComplement' H N :=
  Exists.imp (fun _ => IsComplement'.symm) (exists_right_complement'_of_coprime hN)
#align subgroup.exists_left_complement'_of_coprime Subgroup.exists_left_complement'_of_coprime

end Subgroup
