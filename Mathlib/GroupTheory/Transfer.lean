/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Sylow

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


variable {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A] (ϕ : H →* A)

namespace Subgroup

namespace leftTransversals

open Finset MulAction

open scoped Pointwise

variable (R S T : H.LeftTransversal) [FiniteIndex H]

/-- The difference of two left transversals -/
@[to_additive /-- The difference of two left transversals -/]
noncomputable def diff : A :=
  let α := S.2.leftQuotientEquiv
  let β := T.2.leftQuotientEquiv
  let _ := H.fintypeQuotientOfFiniteIndex
  ∏ q : G ⧸ H, ϕ
      ⟨(α q : G)⁻¹ * β q,
        QuotientGroup.leftRel_apply.mp <|
          Quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive]
theorem diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
  prod_mul_distrib.symm.trans
    (prod_congr rfl fun q _ =>
      (ϕ.map_mul _ _).symm.trans
        (congr_arg ϕ
          (by simp_rw [Subtype.ext_iff, coe_mul, mul_assoc, mul_inv_cancel_left])))

@[to_additive]
theorem diff_self : diff ϕ T T = 1 :=
  mul_eq_left.mp (diff_mul_diff ϕ T T T)

@[to_additive]
theorem diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
  inv_eq_of_mul_eq_one_right <| (diff_mul_diff ϕ S T S).trans <| diff_self ϕ S

@[to_additive]
theorem smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
  let _ := H.fintypeQuotientOfFiniteIndex
  Fintype.prod_equiv (MulAction.toPerm g).symm _ _ fun _ ↦ by
    simp only [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left, toPerm_symm_apply]

end leftTransversals

open Equiv Function MulAction ZMod

variable (g : G)

variable (H) in
/-- The transfer transversal as a function. Given a `⟨g⟩`-orbit `q₀, g • q₀, ..., g ^ (m - 1) • q₀`
  in `G ⧸ H`, an element `g ^ k • q₀` is mapped to `g ^ k • g₀` for a fixed choice of
  representative `g₀` of `q₀`. -/
noncomputable def transferFunction : G ⧸ H → G := fun q =>
  g ^ (cast (quotientEquivSigmaZMod H g q).2 : ℤ) * (quotientEquivSigmaZMod H g q).1.out.out

lemma transferFunction_apply (q : G ⧸ H) :
    transferFunction H g q =
      g ^ (cast (quotientEquivSigmaZMod H g q).2 : ℤ) *
        (quotientEquivSigmaZMod H g q).1.out.out := rfl

lemma coe_transferFunction (q : G ⧸ H) : ↑(transferFunction H g q) = q := by
  rw [transferFunction_apply, ← smul_eq_mul, Quotient.coe_smul_out,
    ← quotientEquivSigmaZMod_symm_apply, Sigma.eta, symm_apply_apply]

variable (H) in
/-- The transfer transversal as a set. Contains elements of the form `g ^ k • g₀` for fixed choices
of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits in `G ⧸ H`. -/
def transferSet : Set G := Set.range (transferFunction H g)

lemma mem_transferSet (q : G ⧸ H) : transferFunction H g q ∈ transferSet H g := ⟨q, rfl⟩

variable (H) in
/-- The transfer transversal. Contains elements of the form `g ^ k • g₀` for fixed choices
  of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits in `G ⧸ H`. -/
def transferTransversal : H.LeftTransversal :=
  ⟨transferSet H g, isComplement_range_left (coe_transferFunction g)⟩

lemma transferTransversal_apply (q : G ⧸ H) :
    ↑((transferTransversal H g).2.leftQuotientEquiv q) = transferFunction H g q :=
  IsComplement.leftQuotientEquiv_apply (coe_transferFunction g) q

lemma transferTransversal_apply' (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod (g • ·) q.out)) :
    ↑((transferTransversal H g).2.leftQuotientEquiv (g ^ (cast k : ℤ) • q.out)) =
      g ^ (cast k : ℤ) * q.out.out := by
  rw [transferTransversal_apply, transferFunction_apply, ← quotientEquivSigmaZMod_symm_apply,
    apply_symm_apply]

lemma transferTransversal_apply'' (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod (g • ·) q.out)) :
    ↑((g • transferTransversal H g).2.leftQuotientEquiv (g ^ (cast k : ℤ) • q.out)) =
      if k = 0 then g ^ minimalPeriod (g • ·) q.out * q.out.out
      else g ^ (cast k : ℤ) * q.out.out := by
  rw [smul_apply_eq_smul_apply_inv_smul, transferTransversal_apply, transferFunction_apply, ←
    mul_smul, ← zpow_neg_one, ← zpow_add, quotientEquivSigmaZMod_apply, smul_eq_mul, ← mul_assoc,
    ← zpow_one_add, Int.cast_add, Int.cast_neg, Int.cast_one, intCast_cast, cast_id', id, ←
    sub_eq_neg_add, cast_sub_one, add_sub_cancel]
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk, zpow_natCast]
  · rw [if_neg hk, if_neg hk]

end Subgroup

namespace MonoidHom

open MulAction Subgroup Subgroup.leftTransversals

/-- Given `ϕ : H →* A` from `H : Subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →* A`. -/
@[to_additive /-- Given `ϕ : H →+ A` from `H : AddSubgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →+ A`. -/]
noncomputable def transfer [FiniteIndex H] : G →* A :=
  let T : H.LeftTransversal := default
  { toFun := fun g => diff ϕ T (g • T)
    map_one' := by rw [one_smul, diff_self]
    map_mul' := fun g h => by rw [mul_smul, ← diff_mul_diff, smul_diff_smul] }

variable (T : H.LeftTransversal)

@[to_additive]
theorem transfer_def [FiniteIndex H] (g : G) : transfer ϕ g = diff ϕ T (g • T) := by
  rw [transfer, ← diff_mul_diff, ← smul_diff_smul, mul_comm, diff_mul_diff] <;> rfl

/-- Explicit computation of the transfer homomorphism. -/
theorem transfer_eq_prod_quotient_orbitRel_zpowers_quot [FiniteIndex H] (g : G)
    [Fintype (Quotient (orbitRel (zpowers g) (G ⧸ H)))] :
    transfer ϕ g =
      ∏ q : Quotient (orbitRel (zpowers g) (G ⧸ H)),
        ϕ
          ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem H g q.out⟩ := by
  classical
    letI := H.fintypeQuotientOfFiniteIndex
    calc
      transfer ϕ g = ∏ q : G ⧸ H, _ := transfer_def ϕ (transferTransversal H g) g
      _ = _ := ((quotientEquivSigmaZMod H g).symm.prod_comp _).symm
      _ = _ := Finset.prod_sigma _ _ _
      _ = _ := by
        refine Fintype.prod_congr _ _ (fun q => ?_)
        simp only [quotientEquivSigmaZMod_symm_apply, transferTransversal_apply',
          transferTransversal_apply'']
        rw [Fintype.prod_eq_single (0 : ZMod (Function.minimalPeriod (g • ·) q.out)) _]
        · simp only [if_pos, ZMod.cast_zero, zpow_zero, one_mul, mul_assoc]
        · intro k hk
          simp only [if_neg hk, inv_mul_cancel]
          exact map_one ϕ

/-- Auxiliary lemma in order to state `transfer_eq_pow`. -/
theorem transfer_eq_pow_aux (g : G)
    (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
    g ^ H.index ∈ H := by
  by_cases hH : H.index = 0
  · rw [hH, pow_zero]
    exact H.one_mem
  letI := fintypeOfIndexNeZero hH
  classical
    replace key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g ^ k ∈ H := fun k g₀ hk =>
      (congr_arg (· ∈ H) (key k g₀ hk)).mp hk
    replace key : ∀ q : G ⧸ H, g ^ Function.minimalPeriod (g • ·) q ∈ H := fun q =>
      key (Function.minimalPeriod (g • ·) q) q.out
        (QuotientGroup.out_conj_pow_minimalPeriod_mem H g q)
    let f : Quotient (orbitRel (zpowers g) (G ⧸ H)) → zpowers g := fun q =>
      (⟨g, mem_zpowers g⟩ : zpowers g) ^ Function.minimalPeriod (g • ·) q.out
    have hf : ∀ q, f q ∈ H.subgroupOf (zpowers g) := fun q => key q.out
    replace key :=
      Subgroup.prod_mem (H.subgroupOf (zpowers g)) fun q (_ : q ∈ Finset.univ) => hf q
    simpa only [f, minimalPeriod_eq_card, Finset.prod_pow_eq_pow_sum, Fintype.card_sigma,
      Fintype.card_congr (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)), index_eq_card,
      Nat.card_eq_fintype_card] using key

theorem transfer_eq_pow [FiniteIndex H] (g : G)
    (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
    transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow_aux g key⟩ := by
  classical
    letI := H.fintypeQuotientOfFiniteIndex
    change ∀ (k g₀) (hk : g₀⁻¹ * g ^ k * g₀ ∈ H), ↑(⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = g ^ k at key
    rw [transfer_eq_prod_quotient_orbitRel_zpowers_quot, ← Finset.prod_map_toList,
      ← Function.comp_def ϕ, List.prod_map_hom]
    refine congrArg ϕ (Subtype.coe_injective ?_)
    dsimp only
    rw [H.coe_mk, ← (zpowers g).coe_mk g (mem_zpowers g), ← (zpowers g).coe_pow, index_eq_card,
      Nat.card_eq_fintype_card, Fintype.card_congr (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)),
      Fintype.card_sigma, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_map_toList]
    simp only [Subgroup.val_list_prod, List.map_map, ← minimalPeriod_eq_card]
    congr 2
    funext
    apply key

theorem transfer_center_eq_pow [FiniteIndex (center G)] (g : G) :
    transfer (MonoidHom.id (center G)) g = ⟨g ^ (center G).index, (center G).pow_index_mem g⟩ :=
  transfer_eq_pow (id (center G)) g fun k _ hk => by rw [← mul_right_inj, ← hk.comm,
    mul_inv_cancel_right]

variable (G) in
/-- The transfer homomorphism `G →* center G`. -/
noncomputable def transferCenterPow [FiniteIndex (center G)] : G →* center G where
  toFun g := ⟨g ^ (center G).index, (center G).pow_index_mem g⟩
  map_one' := Subtype.ext (one_pow (center G).index)
  map_mul' a b := by simp_rw [← show ∀ _, (_ : center G) = _ from transfer_center_eq_pow, map_mul]

@[simp]
theorem transferCenterPow_apply [FiniteIndex (center G)] (g : G) :
    ↑(transferCenterPow G g) = g ^ (center G).index :=
  rfl

section BurnsideTransfer

variable {p : ℕ} (P : Sylow p G) (hP : (P : Subgroup G).normalizer ≤ centralizer (P : Set G))
include hP

/-- The homomorphism `G →* P` in Burnside's transfer theorem. -/
noncomputable def transferSylow [FiniteIndex (P : Subgroup G)] : G →* (P : Subgroup G) :=
  @transfer G _ P P
    (@CommGroup.ofIsMulCommutative P _ ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩)
      (MonoidHom.id P) _

variable [Fact p.Prime] [Finite (Sylow p G)]

/-- Auxiliary lemma in order to state `transferSylow_eq_pow`. -/
theorem transferSylow_eq_pow_aux (g : G) (hg : g ∈ P) (k : ℕ) (g₀ : G)
    (h : g₀⁻¹ * g ^ k * g₀ ∈ P) : g₀⁻¹ * g ^ k * g₀ = g ^ k := by
  haveI : IsMulCommutative (P : Subgroup G) :=
    ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
  replace hg := (P : Subgroup G).pow_mem hg k
  obtain ⟨n, hn, h⟩ := P.conj_eq_normalizer_conj_of_mem (g ^ k) g₀ hg h
  exact h.trans (Commute.inv_mul_cancel (hP hn (g ^ k) hg).symm)

variable [FiniteIndex (P : Subgroup G)]

theorem transferSylow_eq_pow (g : G) (hg : g ∈ P) :
    transferSylow P hP g =
      ⟨g ^ (P : Subgroup G).index, transfer_eq_pow_aux g (transferSylow_eq_pow_aux P hP g hg)⟩ :=
  haveI : IsMulCommutative P := ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
  transfer_eq_pow _ _ <| transferSylow_eq_pow_aux P hP g hg

theorem transferSylow_restrict_eq_pow : ⇑((transferSylow P hP).restrict (P : Subgroup G)) =
    (fun x : P => x ^ (P : Subgroup G).index) :=
  funext fun g => transferSylow_eq_pow P hP g g.2

/-- **Burnside's normal p-complement theorem**: If `N(P) ≤ C(P)`, then `P` has a normal
complement. -/
theorem ker_transferSylow_isComplement' : IsComplement' (transferSylow P hP).ker P := by
  have hf : Function.Bijective ((transferSylow P hP).restrict (P : Subgroup G)) :=
    (transferSylow_restrict_eq_pow P hP).symm ▸ (P.2.powEquiv' P.not_dvd_index).bijective
  rw [Function.Bijective, ← range_eq_top, restrict_range] at hf
  have := range_eq_top.mp (top_le_iff.mp (hf.2.ge.trans
    (map_le_range (transferSylow P hP) P)))
  rw [← (comap_injective this).eq_iff, comap_top, comap_map_eq, sup_comm, SetLike.ext'_iff,
    normal_mul, ← ker_eq_bot_iff, ← (map_injective (P : Subgroup G).subtype_injective).eq_iff,
    ker_restrict, subgroupOf_map_subtype, Subgroup.map_bot, coe_top] at hf
  exact isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hf.1) hf.2

theorem not_dvd_card_ker_transferSylow : ¬p ∣ Nat.card (transferSylow P hP).ker :=
  (ker_transferSylow_isComplement' P hP).index_eq_card ▸ P.not_dvd_index

theorem ker_transferSylow_disjoint (Q : Subgroup G) (hQ : IsPGroup p Q) :
    Disjoint (transferSylow P hP).ker Q :=
  disjoint_iff.mpr <|
    card_eq_one.mp <|
      (hQ.to_le inf_le_right).card_eq_or_dvd.resolve_right fun h =>
        not_dvd_card_ker_transferSylow P hP <| h.trans <| card_dvd_of_le inf_le_left

end BurnsideTransfer

end MonoidHom

namespace IsCyclic

open Subgroup

-- we could suppress the variable `p`, but that might introduce `motive not type correct` issues.
variable {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : (Nat.card G).minFac = p) {P : Sylow p G}

include hp in
theorem normalizer_le_centralizer (hP : IsCyclic P) : P.normalizer ≤ centralizer (P : Set G) := by
  subst hp
  by_cases hn : Nat.card G = 1
  · have := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [Subsingleton.elim P.normalizer (centralizer P)]
  have := Fact.mk (Nat.minFac_prime hn)
  have key := card_dvd_of_injective _ (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker, ← index, ← relIndex] at key
  refine relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes ?_ dvd_rfl key)
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  rcases eq_zero_or_pos k with h0 | h0
  · rw [hP.card_mulAut, hk, h0, pow_zero, Nat.totient_one]
    apply Nat.coprime_one_right
  rw [hP.card_mulAut, hk, Nat.totient_prime_pow Fact.out h0]
  refine (Nat.Coprime.pow_right _ ?_).mul_right ?_
  · apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_of_le_left P.normalizer P.le_centralizer)
    apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_index_of_le P.le_normalizer)
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact P.not_dvd_index
  · apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_card (centralizer P) P.normalizer)
    apply Nat.Coprime.coprime_dvd_left (card_subgroup_dvd_card P.normalizer)
    have h1 := Nat.gcd_dvd_left (Nat.card G) ((Nat.card G).minFac - 1)
    have h2 := Nat.gcd_le_right (n := (Nat.card G).minFac - 1) (Nat.card G)
      (tsub_pos_iff_lt.mpr (Nat.minFac_prime hn).one_lt)
    contrapose! h2
    refine Nat.sub_one_lt_of_le (Nat.card G).minFac_pos (Nat.minFac_le_of_dvd ?_ h1)
    exact (Nat.two_le_iff _).mpr ⟨ne_zero_of_dvd_ne_zero Nat.card_pos.ne' h1, h2⟩

include hp in
/-- A cyclic Sylow subgroup for the smallest prime has a normal complement. -/
theorem isComplement' (hP : IsCyclic P) :
    (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hp)).ker.IsComplement' P := by
  subst hp
  by_cases hn : Nat.card G = 1
  · have := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [Subsingleton.elim (MonoidHom.transferSylow P (hP.normalizer_le_centralizer rfl)).ker ⊥,
      Subsingleton.elim P.1 ⊤]
    exact isComplement'_bot_top
  have := Fact.mk (Nat.minFac_prime hn)
  exact MonoidHom.ker_transferSylow_isComplement' P (hP.normalizer_le_centralizer rfl)

end IsCyclic
