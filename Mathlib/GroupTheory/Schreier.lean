/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.GroupTheory.Abelianization
import Mathlib.GroupTheory.Commutator.Finite
import Mathlib.GroupTheory.Transfer
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Schreier's Lemma

In this file we prove Schreier's lemma.

## Main results

- `closure_mul_image_eq` : **Schreier's Lemma**: If `R : Set G` is a right_transversal
  of `H : Subgroup G` with `1 ∈ R`, and if `G` is generated by `S : Set G`,
  then `H` is generated by the `Set` `(R * S).image (fun g ↦ g * (hR.toRightFun g)⁻¹)`.
- `fg_of_index_ne_zero` : **Schreier's Lemma**: A finite index subgroup of a finitely generated
  group is finitely generated.
- `card_commutator_le_of_finite_commutatorSet`: A theorem of Schur: The size of the commutator
  subgroup is bounded in terms of the number of commutators.
-/


open scoped Finset Pointwise

section CommGroup

open Subgroup

variable (G : Type*) [CommGroup G] [Group.FG G]

@[to_additive]
theorem card_dvd_exponent_pow_rank : Nat.card G ∣ Monoid.exponent G ^ Group.rank G := by
  classical
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  rw [← hS1, ← Fintype.card_coe, ← Finset.card_univ, ← Finset.prod_const]
  let f : (∀ g : S, zpowers (g : G)) →* G := noncommPiCoprod fun s t _ x y _ _ => mul_comm x _
  have hf : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hS2, closure_le]
    exact fun g hg => ⟨Pi.mulSingle ⟨g, hg⟩ ⟨g, mem_zpowers g⟩, noncommPiCoprod_mulSingle _ _⟩
  replace hf := card_dvd_of_surjective f hf
  rw [Nat.card_pi] at hf
  refine hf.trans (Finset.prod_dvd_prod_of_dvd _ _ fun g _ => ?_)
  rw [Nat.card_zpowers]
  exact Monoid.order_dvd_exponent (g : G)

@[to_additive]
theorem card_dvd_exponent_pow_rank' {n : ℕ} (hG : ∀ g : G, g ^ n = 1) :
    Nat.card G ∣ n ^ Group.rank G :=
  (card_dvd_exponent_pow_rank G).trans
    (pow_dvd_pow_of_dvd (Monoid.exponent_dvd_of_forall_pow_eq_one hG) (Group.rank G))

end CommGroup

namespace Subgroup

open MemRightTransversals

variable {G : Type*} [Group G] {H : Subgroup G} {R S : Set G}

theorem closure_mul_image_mul_eq_top
    (hR : IsComplement H R) (hR1 : (1 : G) ∈ R) (hS : closure S = ⊤) :
    (closure ((R * S).image fun g => g * (hR.toRightFun g : G)⁻¹)) * R = ⊤ := by
  let f : G → R := hR.toRightFun
  let U : Set G := (R * S).image fun g => g * (f g : G)⁻¹
  change (closure U : Set G) * R = ⊤
  refine top_le_iff.mp fun g _ => ?_
  refine closure_induction_right ?_ ?_ ?_ (eq_top_iff.mp hS (mem_top g))
  · exact ⟨1, (closure U).one_mem, 1, hR1, one_mul 1⟩
  · rintro - - s hs ⟨u, hu, r, hr, rfl⟩
    rw [show u * r * s = u * (r * s * (f (r * s) : G)⁻¹) * f (r * s) by group]
    refine Set.mul_mem_mul ((closure U).mul_mem hu ?_) (f (r * s)).coe_prop
    exact subset_closure ⟨r * s, Set.mul_mem_mul hr hs, rfl⟩
  · rintro - - s hs ⟨u, hu, r, hr, rfl⟩
    rw [show u * r * s⁻¹ = u * (f (r * s⁻¹) * s * r⁻¹)⁻¹ * f (r * s⁻¹) by group]
    refine Set.mul_mem_mul ((closure U).mul_mem hu ((closure U).inv_mem ?_)) (f (r * s⁻¹)).2
    refine subset_closure ⟨f (r * s⁻¹) * s, Set.mul_mem_mul (f (r * s⁻¹)).2 hs, ?_⟩
    rw [mul_right_inj, inv_inj, ← Subtype.coe_mk r hr, ← Subtype.ext_iff, Subtype.coe_mk]
    apply (isComplement_iff_existsUnique_mul_inv_mem.mp hR (f (r * s⁻¹) * s)).unique
      (hR.mul_inv_toRightFun_mem (f (r * s⁻¹) * s))
    rw [mul_assoc, ← inv_inv s, ← mul_inv_rev, inv_inv]
    exact hR.toRightFun_mul_inv_mem (r * s⁻¹)

/-- **Schreier's Lemma**: If `R : Set G` is a `rightTransversal` of `H : Subgroup G`
  with `1 ∈ R`, and if `G` is generated by `S : Set G`, then `H` is generated by the `Set`
  `(R * S).image (fun g ↦ g * (hR.toRightFun g)⁻¹)`. -/
theorem closure_mul_image_eq (hR : IsComplement H R) (hR1 : (1 : G) ∈ R)
    (hS : closure S = ⊤) : closure ((R * S).image fun g => g * (hR.toRightFun g : G)⁻¹) = H := by
  have hU : closure ((R * S).image fun g => g * (hR.toRightFun g : G)⁻¹) ≤ H := by
    rw [closure_le]
    rintro - ⟨g, -, rfl⟩
    exact hR.mul_inv_toRightFun_mem g
  refine le_antisymm hU fun h hh => ?_
  obtain ⟨g, hg, r, hr, rfl⟩ :=
    show h ∈ _ from eq_top_iff.mp (closure_mul_image_mul_eq_top hR hR1 hS) (mem_top h)
  suffices (⟨r, hr⟩ : R) = (⟨1, hR1⟩ : R) by
    simpa only [show r = 1 from Subtype.ext_iff.mp this, mul_one]
  apply (isComplement_iff_existsUnique_mul_inv_mem.mp hR r).unique
  · rw [Subtype.coe_mk, mul_inv_cancel]
    exact H.one_mem
  · rw [Subtype.coe_mk, inv_one, mul_one]
    exact (H.mul_mem_cancel_left (hU hg)).mp hh

/-- **Schreier's Lemma**: If `R : Set G` is a `rightTransversal` of `H : Subgroup G`
  with `1 ∈ R`, and if `G` is generated by `S : Set G`, then `H` is generated by the `Set`
  `(R * S).image (fun g ↦ g * (hR.toRightFun g)⁻¹)`. -/
theorem closure_mul_image_eq_top (hR : IsComplement H R) (hR1 : (1 : G) ∈ R)
    (hS : closure S = ⊤) : closure ((R * S).image fun g =>
      ⟨g * (hR.toRightFun g : G)⁻¹, hR.mul_inv_toRightFun_mem g⟩ : Set H) = ⊤ := by
  rw [eq_top_iff, ← map_subtype_le_map_subtype, MonoidHom.map_closure, Set.image_image]
  exact (map_subtype_le ⊤).trans (ge_of_eq (closure_mul_image_eq hR hR1 hS))

/-- **Schreier's Lemma**: If `R : Finset G` is a `rightTransversal` of `H : Subgroup G`
  with `1 ∈ R`, and if `G` is generated by `S : Finset G`, then `H` is generated by the `Finset`
  `(R * S).image (fun g ↦ g * (hR.toRightFun g)⁻¹)`. -/
theorem closure_mul_image_eq_top' [DecidableEq G] {R S : Finset G}
    (hR : IsComplement (H : Set G) R) (hR1 : (1 : G) ∈ R)
    (hS : closure (S : Set G) = ⊤) :
    closure (((R * S).image fun g => ⟨_, hR.mul_inv_toRightFun_mem g⟩ : Finset H) : Set H) = ⊤ := by
  rw [Finset.coe_image, Finset.coe_mul]
  exact closure_mul_image_eq_top hR hR1 hS

variable (H)

theorem exists_finset_card_le_mul [FiniteIndex H] {S : Finset G} (hS : closure (S : Set G) = ⊤) :
    ∃ T : Finset H, #T ≤ H.index * #S ∧ closure (T : Set H) = ⊤ := by
  letI := H.fintypeQuotientOfFiniteIndex
  haveI : DecidableEq G := Classical.decEq G
  obtain ⟨R₀, hR, hR1⟩ := H.exists_isComplement_right 1
  haveI : Fintype R₀ := Fintype.ofEquiv _ hR.rightQuotientEquiv
  let R : Finset G := Set.toFinset R₀
  replace hR : IsComplement (H : Set G) R := by rwa [Set.coe_toFinset]
  replace hR1 : (1 : G) ∈ R := by rwa [Set.mem_toFinset]
  refine ⟨_, ?_, closure_mul_image_eq_top' hR hR1 hS⟩
  calc
    _ ≤ #(R * S) := Finset.card_image_le
    _ ≤ #R * #S := Finset.card_mul_le
    _ = H.index * S.card := congr_arg (· * S.card) ?_
  calc
    #R = Fintype.card R := (Fintype.card_coe R).symm
    _ = _ := (Fintype.card_congr hR.rightQuotientEquiv).symm
    _ = Fintype.card (G ⧸ H) := QuotientGroup.card_quotient_rightRel H
    _ = H.index := by rw [index_eq_card, Nat.card_eq_fintype_card]

/-- **Schreier's Lemma**: A finite index subgroup of a finitely generated
  group is finitely generated. -/
instance fg_of_index_ne_zero [hG : Group.FG G] [FiniteIndex H] : Group.FG H := by
  obtain ⟨S, hS⟩ := hG.1
  obtain ⟨T, -, hT⟩ := exists_finset_card_le_mul H hS
  exact ⟨⟨T, hT⟩⟩

theorem rank_le_index_mul_rank [hG : Group.FG G] [FiniteIndex H] :
    Group.rank H ≤ H.index * Group.rank G := by
  haveI := H.fg_of_index_ne_zero
  obtain ⟨S, hS₀, hS⟩ := Group.rank_spec G
  obtain ⟨T, hT₀, hT⟩ := exists_finset_card_le_mul H hS
  calc
    Group.rank H ≤ #T := Group.rank_le H hT
    _ ≤ H.index * #S := hT₀
    _ = H.index * Group.rank G := congr_arg (H.index * ·) hS₀

variable (G)

/-- If `G` has `n` commutators `[g₁, g₂]`, then `|G'| ∣ [G : Z(G)] ^ ([G : Z(G)] * n + 1)`,
where `G'` denotes the commutator of `G`. -/
theorem card_commutator_dvd_index_center_pow [Finite (commutatorSet G)] :
    Nat.card (_root_.commutator G) ∣
      (center G).index ^ ((center G).index * Nat.card (commutatorSet G) + 1) := by
  -- First handle the case when `Z(G)` has infinite index and `[G : Z(G)]` is defined to be `0`
  by_cases hG : (center G).index = 0
  · simp_rw [hG, zero_mul, zero_add, pow_one, dvd_zero]
  haveI : FiniteIndex (center G) := ⟨hG⟩
  -- Rewrite as `|Z(G) ∩ G'| * [G' : Z(G) ∩ G'] ∣ [G : Z(G)] ^ ([G : Z(G)] * n) * [G : Z(G)]`
  rw [← ((center G).subgroupOf (_root_.commutator G)).card_mul_index, pow_succ]
  -- We have `h1 : [G' : Z(G) ∩ G'] ∣ [G : Z(G)]`
  have h1 := relindex_dvd_index_of_normal (center G) (_root_.commutator G)
  -- So we can reduce to proving `|Z(G) ∩ G'| ∣ [G : Z(G)] ^ ([G : Z(G)] * n)`
  refine mul_dvd_mul ?_ h1
  -- We know that `[G' : Z(G) ∩ G'] < ∞` by `h1` and `hG`
  haveI : FiniteIndex ((center G).subgroupOf (_root_.commutator G)) :=
    ⟨ne_zero_of_dvd_ne_zero hG h1⟩
  -- We have `h2 : rank (Z(G) ∩ G') ≤ [G' : Z(G) ∩ G'] * rank G'` by Schreier's lemma
  have h2 := rank_le_index_mul_rank ((center G).subgroupOf (_root_.commutator G))
  -- We have `h3 : [G' : Z(G) ∩ G'] * rank G' ≤ [G : Z(G)] * n` by `h1` and `rank G' ≤ n`
  have h3 := Nat.mul_le_mul (Nat.le_of_dvd (Nat.pos_of_ne_zero hG) h1) (rank_commutator_le_card G)
  -- So we can reduce to proving `|Z(G) ∩ G'| ∣ [G : Z(G)] ^ rank (Z(G) ∩ G')`
  refine dvd_trans ?_ (pow_dvd_pow (center G).index (h2.trans h3))
  -- `Z(G) ∩ G'` is abelian, so it enough to prove that `g ^ [G : Z(G)] = 1` for `g ∈ Z(G) ∩ G'`
  apply card_dvd_exponent_pow_rank'
  intro g
  -- `Z(G)` is abelian, so `g ∈ Z(G) ∩ G' ≤ G' ≤ ker (transfer : G → Z(G))`
  have := Abelianization.commutator_subset_ker (MonoidHom.transferCenterPow G) g.1.2
  -- `transfer g` is defeq to `g ^ [G : Z(G)]`, so we are done
  simpa only [MonoidHom.mem_ker, Subtype.ext_iff] using this

/-- A bound for the size of the commutator subgroup in terms of the number of commutators. -/
def cardCommutatorBound (n : ℕ) :=
  (n ^ (2 * n)) ^ (n ^ (2 * n + 1) + 1)

/-- A theorem of Schur: The size of the commutator subgroup is bounded in terms of the number of
  commutators. -/
theorem card_commutator_le_of_finite_commutatorSet [Finite (commutatorSet G)] :
    Nat.card (_root_.commutator G) ≤ cardCommutatorBound (Nat.card (commutatorSet G)) := by
  have h1 := index_center_le_pow (closureCommutatorRepresentatives G)
  have h2 := card_commutator_dvd_index_center_pow (closureCommutatorRepresentatives G)
  rw [card_commutatorSet_closureCommutatorRepresentatives] at h1 h2
  rw [card_commutator_closureCommutatorRepresentatives] at h2
  replace h1 :=
    h1.trans
      (Nat.pow_le_pow_right Finite.card_pos (rank_closureCommutatorRepresentatives_le G))
  replace h2 := h2.trans (pow_dvd_pow _ (add_le_add_right (mul_le_mul_right' h1 _) 1))
  rw [← pow_succ] at h2
  refine (Nat.le_of_dvd ?_ h2).trans (Nat.pow_le_pow_left h1 _)
  exact pow_pos (Nat.pos_of_ne_zero FiniteIndex.finiteIndex) _

/-- A theorem of Schur: A group with finitely many commutators has finite commutator subgroup. -/
instance [Finite (commutatorSet G)] : Finite (_root_.commutator G) := by
  have h2 := card_commutator_dvd_index_center_pow (closureCommutatorRepresentatives G)
  refine Nat.finite_of_card_ne_zero fun h => ?_
  rw [card_commutator_closureCommutatorRepresentatives, h, zero_dvd_iff] at h2
  exact FiniteIndex.finiteIndex (pow_eq_zero h2)

end Subgroup
