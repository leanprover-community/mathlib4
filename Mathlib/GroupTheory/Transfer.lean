/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Sylow

#align_import group_theory.transfer from "leanprover-community/mathlib"@"4be589053caf347b899a494da75410deb55fb3ef"

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `diff ϕ S T` : The difference of two left transversals `S` and `T` under the homomorphism `ϕ`.
- `transfer ϕ` : The transfer homomorphism induced by `ϕ`.
- `transferCenterPow`: The transfer homomorphism `G →* center G`.

## Main results
- `transferCenterPow_apply`:
  The transfer homomorphism `G →* center G` is given by `g ↦ g ^ (center G).index`.
- `ker_transferSylow_isComplement'`: Burnside's transfer (or normal `p`-complement) theorem:
  If `hP : N(P) ≤ C(P)`, then `(transfer P hP).ker` is a normal `p`-complement.
-/


open scoped BigOperators

variable {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A] (ϕ : H →* A)

namespace Subgroup

namespace leftTransversals

open Finset MulAction

open scoped Pointwise

variable (R S T : leftTransversals (H : Set G)) [FiniteIndex H]

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
  let α := MemLeftTransversals.toEquiv S.2
  let β := MemLeftTransversals.toEquiv T.2
  (@Finset.univ (G ⧸ H) H.fintypeQuotientOfFiniteIndex).prod fun q =>
    ϕ
      ⟨(α q : G)⁻¹ * β q,
        QuotientGroup.leftRel_apply.mp <|
          Quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩
#align subgroup.left_transversals.diff Subgroup.leftTransversals.diff
#align add_subgroup.left_transversals.diff AddSubgroup.leftTransversals.diff

@[to_additive]
theorem diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
  prod_mul_distrib.symm.trans
    (prod_congr rfl fun q _ =>
      (ϕ.map_mul _ _).symm.trans
        (congr_arg ϕ
          (by simp_rw [Subtype.ext_iff, coe_mul, mul_assoc, mul_inv_cancel_left])))
              -- 🎉 no goals
#align subgroup.left_transversals.diff_mul_diff Subgroup.leftTransversals.diff_mul_diff
#align add_subgroup.left_transversals.diff_add_diff AddSubgroup.leftTransversals.diff_add_diff

@[to_additive]
theorem diff_self : diff ϕ T T = 1 :=
  mul_right_eq_self.mp (diff_mul_diff ϕ T T T)
#align subgroup.left_transversals.diff_self Subgroup.leftTransversals.diff_self
#align add_subgroup.left_transversals.diff_self AddSubgroup.leftTransversals.diff_self

@[to_additive]
theorem diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
  inv_eq_of_mul_eq_one_right <| (diff_mul_diff ϕ S T S).trans <| diff_self ϕ S
#align subgroup.left_transversals.diff_inv Subgroup.leftTransversals.diff_inv
#align add_subgroup.left_transversals.diff_neg AddSubgroup.leftTransversals.diff_neg

@[to_additive]
theorem smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
  let _ := H.fintypeQuotientOfFiniteIndex
  prod_bij' (fun q _ => g⁻¹ • q) (fun _ _ => mem_univ _)
    (fun _ _ =>
      congr_arg ϕ
        (by
          simp_rw [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc,
            inv_mul_cancel_left]))
    (fun q _ => g • q) (fun _ _ => mem_univ _) (fun q _ => smul_inv_smul g q) fun q _ =>
    inv_smul_smul g q
#align subgroup.left_transversals.smul_diff_smul Subgroup.leftTransversals.smul_diff_smul
#align add_subgroup.left_transversals.vadd_diff_vadd AddSubgroup.leftTransversals.vadd_diff_vadd

end leftTransversals

end Subgroup

namespace MonoidHom

open MulAction Subgroup Subgroup.leftTransversals

/-- Given `ϕ : H →* A` from `H : Subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →* A`. -/
@[to_additive "Given `ϕ : H →+ A` from `H : AddSubgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →+ A`."]
noncomputable def transfer [FiniteIndex H] : G →* A :=
  let T : leftTransversals (H : Set G) := Inhabited.default
  { toFun := fun g => diff ϕ T (g • T)
    map_one' := by simp only; rw [one_smul, diff_self] -- porting note: added `simp only`
                   -- ⊢ diff ϕ default (1 • default) = 1
                              -- 🎉 no goals
    map_mul' := fun g h => by simp only; rw [mul_smul, ← diff_mul_diff, smul_diff_smul] }
                              -- ⊢ diff ϕ default ((g * h) • default) = diff ϕ default (g • default) * diff ϕ d …
                                         -- 🎉 no goals
#align monoid_hom.transfer MonoidHom.transfer
#align add_monoid_hom.transfer AddMonoidHom.transfer

variable (T : leftTransversals (H : Set G))

@[to_additive]
theorem transfer_def [FiniteIndex H] (g : G) : transfer ϕ g = diff ϕ T (g • T) := by
  rw [transfer, ← diff_mul_diff, ← smul_diff_smul, mul_comm, diff_mul_diff] <;> rfl
  -- ⊢ ↑(let T := default;
                                                                                -- 🎉 no goals
#align monoid_hom.transfer_def MonoidHom.transfer_def
#align add_monoid_hom.transfer_def AddMonoidHom.transfer_def

/-- Explicit computation of the transfer homomorphism. -/
theorem transfer_eq_prod_quotient_orbitRel_zpowers_quot [FiniteIndex H] (g : G)
    [Fintype (Quotient (orbitRel (zpowers g) (G ⧸ H)))] :
    transfer ϕ g =
      ∏ q : Quotient (orbitRel (zpowers g) (G ⧸ H)),
        ϕ
          ⟨q.out'.out'⁻¹ * g ^ Function.minimalPeriod ((· • ·) g) q.out' * q.out'.out',
            QuotientGroup.out'_conj_pow_minimalPeriod_mem H g q.out'⟩ := by
  classical
    letI := H.fintypeQuotientOfFiniteIndex
    calc
      transfer ϕ g = ∏ q : G ⧸ H, _ := transfer_def ϕ (transferTransversal H g) g
      _ = _ := ((quotientEquivSigmaZMod H g).symm.prod_comp _).symm
      _ = _ := (Finset.prod_sigma _ _ _)
      _ = _ := by
        refine' Fintype.prod_congr _ _ (fun q => _)
        simp only [quotientEquivSigmaZMod_symm_apply, transferTransversal_apply',
          transferTransversal_apply'']
        rw [Fintype.prod_eq_single (0 : ZMod (Function.minimalPeriod ((· • ·) g) q.out')) _]
        · simp only [if_pos, ZMod.cast_zero, zpow_zero, one_mul, mul_assoc]
        · intro k hk
          simp only [if_neg hk, inv_mul_self]
          exact map_one ϕ
#align monoid_hom.transfer_eq_prod_quotient_orbit_rel_zpowers_quot MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot

/-- Auxiliary lemma in order to state `transfer_eq_pow`. -/
theorem transfer_eq_pow_aux (g : G)
    (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
    g ^ H.index ∈ H := by
  by_cases hH : H.index = 0
  -- ⊢ g ^ index H ∈ H
  · rw [hH, pow_zero]
    -- ⊢ 1 ∈ H
    exact H.one_mem
    -- 🎉 no goals
  letI := fintypeOfIndexNeZero hH
  -- ⊢ g ^ index H ∈ H
  classical
    replace key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g ^ k ∈ H := fun k g₀ hk =>
      (_root_.congr_arg (· ∈ H) (key k g₀ hk)).mp hk
    replace key : ∀ q : G ⧸ H, g ^ Function.minimalPeriod ((· • ·) g) q ∈ H := fun q =>
      key (Function.minimalPeriod ((· • ·) g) q) q.out'
        (QuotientGroup.out'_conj_pow_minimalPeriod_mem H g q)
    let f : Quotient (orbitRel (zpowers g) (G ⧸ H)) → zpowers g := fun q =>
      (⟨g, mem_zpowers g⟩ : zpowers g) ^ Function.minimalPeriod ((· • ·) g) q.out'
    have hf : ∀ q, f q ∈ H.subgroupOf (zpowers g) := fun q => key q.out'
    replace key :=
      Subgroup.prod_mem (H.subgroupOf (zpowers g)) fun q (_ : q ∈ Finset.univ) => hf q
    simpa only [minimalPeriod_eq_card, Finset.prod_pow_eq_pow_sum, Fintype.card_sigma,
      Fintype.card_congr (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)), index_eq_card] using key
#align monoid_hom.transfer_eq_pow_aux MonoidHom.transfer_eq_pow_aux

theorem transfer_eq_pow [FiniteIndex H] (g : G)
    (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
    transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow_aux g key⟩ := by
  classical
    letI := H.fintypeQuotientOfFiniteIndex
    change ∀ (k g₀) (hk : g₀⁻¹ * g ^ k * g₀ ∈ H), ↑(⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = g ^ k at key
    rw [transfer_eq_prod_quotient_orbitRel_zpowers_quot, ← Finset.prod_to_list]
    refine' (List.prod_map_hom _ _ _).trans _ -- porting note: this used to be in the `rw`
    refine' congrArg ϕ (Subtype.coe_injective _)
    simp only -- porting note: added `simp only`
    rw [H.coe_mk, ← (zpowers g).coe_mk g (mem_zpowers g), ← (zpowers g).coe_pow,
      index_eq_card, Fintype.card_congr (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)),
      Fintype.card_sigma, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_to_list]
    simp only [Subgroup.val_list_prod, List.map_map, ← minimalPeriod_eq_card]
    congr
    funext
    apply key
#align monoid_hom.transfer_eq_pow MonoidHom.transfer_eq_pow

theorem transfer_center_eq_pow [FiniteIndex (center G)] (g : G) :
    transfer (MonoidHom.id (center G)) g = ⟨g ^ (center G).index, (center G).pow_index_mem g⟩ :=
  transfer_eq_pow (id (center G)) g fun k _ hk => by rw [← mul_right_inj, hk, mul_inv_cancel_right]
                                                     -- 🎉 no goals
#align monoid_hom.transfer_center_eq_pow MonoidHom.transfer_center_eq_pow

variable (G)

/-- The transfer homomorphism `G →* center G`. -/
noncomputable def transferCenterPow [FiniteIndex (center G)] : G →* center G where
  toFun g := ⟨g ^ (center G).index, (center G).pow_index_mem g⟩
  map_one' := Subtype.ext (one_pow (center G).index)
  map_mul' a b := by simp_rw [← show ∀ _, (_ : center G) = _ from transfer_center_eq_pow, map_mul]
                     -- 🎉 no goals
#align monoid_hom.transfer_center_pow MonoidHom.transferCenterPow

variable {G}

@[simp]
theorem transferCenterPow_apply [FiniteIndex (center G)] (g : G) :
    ↑(transferCenterPow G g) = g ^ (center G).index :=
  rfl
#align monoid_hom.transfer_center_pow_apply MonoidHom.transferCenterPow_apply

section BurnsideTransfer

variable {p : ℕ} (P : Sylow p G) (hP : (P : Subgroup G).normalizer ≤ centralizer (P : Set G))

/-- The homomorphism `G →* P` in Burnside's transfer theorem. -/
noncomputable def transferSylow [FiniteIndex (P : Subgroup G)] : G →* (P : Subgroup G) :=
  @transfer G _ P P
    (@Subgroup.IsCommutative.commGroup G _ P
      ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩)
    (MonoidHom.id P) _
#align monoid_hom.transfer_sylow MonoidHom.transferSylow

variable [Fact p.Prime] [Finite (Sylow p G)]

/-- Auxiliary lemma in order to state `transferSylow_eq_pow`. -/
theorem transferSylow_eq_pow_aux (g : G) (hg : g ∈ P) (k : ℕ) (g₀ : G)
    (h : g₀⁻¹ * g ^ k * g₀ ∈ P) : g₀⁻¹ * g ^ k * g₀ = g ^ k := by
  haveI : (P : Subgroup G).IsCommutative :=
    ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
  replace hg := (P : Subgroup G).pow_mem hg k
  -- ⊢ g₀⁻¹ * g ^ k * g₀ = g ^ k
  obtain ⟨n, hn, h⟩ := P.conj_eq_normalizer_conj_of_mem (g ^ k) g₀ hg h
  -- ⊢ g₀⁻¹ * g ^ k * g₀ = g ^ k
  exact h.trans (Commute.inv_mul_cancel (hP hn (g ^ k) hg).symm)
  -- 🎉 no goals
#align monoid_hom.transfer_sylow_eq_pow_aux MonoidHom.transferSylow_eq_pow_aux

variable [FiniteIndex (P : Subgroup G)]

theorem transferSylow_eq_pow (g : G) (hg : g ∈ P) :
    transferSylow P hP g =
      ⟨g ^ (P : Subgroup G).index, transfer_eq_pow_aux g (transferSylow_eq_pow_aux P hP g hg)⟩ :=
  @transfer_eq_pow G _ P P (@Subgroup.IsCommutative.commGroup G _ P
    ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩) _ _ g
      (transferSylow_eq_pow_aux P hP g hg) -- porting note: apply used to do this automatically
#align monoid_hom.transfer_sylow_eq_pow MonoidHom.transferSylow_eq_pow

theorem transferSylow_restrict_eq_pow : ⇑((transferSylow P hP).restrict (P : Subgroup G)) =
  (fun x : P => x ^ (P : Subgroup G).index) :=
  funext fun g => transferSylow_eq_pow P hP g g.2
#align monoid_hom.transfer_sylow_restrict_eq_pow MonoidHom.transferSylow_restrict_eq_pow

/-- Burnside's normal p-complement theorem: If `N(P) ≤ C(P)`, then `P` has a normal complement. -/
theorem ker_transferSylow_isComplement' : IsComplement' (transferSylow P hP).ker P := by
  have hf : Function.Bijective ((transferSylow P hP).restrict (P : Subgroup G)) :=
    (transferSylow_restrict_eq_pow P hP).symm ▸
      (P.2.powEquiv'
          (not_dvd_index_sylow P
            (mt index_eq_zero_of_relindex_eq_zero index_ne_zero_of_finite))).bijective
  rw [Function.Bijective, ← range_top_iff_surjective, restrict_range] at hf
  -- ⊢ IsComplement' (ker (transferSylow P hP)) ↑P
  have := range_top_iff_surjective.mp (top_le_iff.mp (hf.2.ge.trans
    (map_le_range (transferSylow P hP) P)))
  rw [← (comap_injective this).eq_iff, comap_top, comap_map_eq, sup_comm, SetLike.ext'_iff,
    normal_mul, ← ker_eq_bot_iff, ← (map_injective (P : Subgroup G).subtype_injective).eq_iff,
    ker_restrict, subgroupOf_map_subtype, Subgroup.map_bot, coe_top] at hf
  exact isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hf.1) hf.2
  -- 🎉 no goals
#align monoid_hom.ker_transfer_sylow_is_complement' MonoidHom.ker_transferSylow_isComplement'

theorem not_dvd_card_ker_transferSylow : ¬p ∣ Nat.card (transferSylow P hP).ker :=
  (ker_transferSylow_isComplement' P hP).index_eq_card ▸ not_dvd_index_sylow P <|
    mt index_eq_zero_of_relindex_eq_zero index_ne_zero_of_finite
#align monoid_hom.not_dvd_card_ker_transfer_sylow MonoidHom.not_dvd_card_ker_transferSylow

theorem ker_transferSylow_disjoint (Q : Subgroup G) (hQ : IsPGroup p Q) :
    Disjoint (transferSylow P hP).ker Q :=
  disjoint_iff.mpr <|
    card_eq_one.mp <|
      (hQ.to_le inf_le_right).card_eq_or_dvd.resolve_right fun h =>
        not_dvd_card_ker_transferSylow P hP <| h.trans <| nat_card_dvd_of_le _ _ inf_le_left
#align monoid_hom.ker_transfer_sylow_disjoint MonoidHom.ker_transferSylow_disjoint

end BurnsideTransfer

end MonoidHom
