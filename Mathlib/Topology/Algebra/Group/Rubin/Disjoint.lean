/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.Data.Int.Lemmas
import Mathlib.Topology.Separation
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.LocallyDense
import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Topology.Algebra.Group.InjectiveAction

/-!
# Group-theoretical condition for the disjointness of `(fixedBy α g)ᶜ` sets

This module describes a somewhat mysterious condition for two group elements to have disjoint
`(fixedBy α g)ᶜ` sets, assuming the group action is locally dense.

TODO: link to locally dense

This is a key construction in the proof of Rubin's theorem, as the `(fixedBy α g)ᶜ` sets can be used
to describe a topological basis of the acted-upon topological space.
-/

namespace Rubin

open Pointwise
open MulAction

variable {G : Type*} [Group G] {g h : G}
variable {α : Type*} [TopologicalSpace α] [MulAction G α]

section Witness

/--
A bundled pair `(fst, snd)` such that `fst`, `snd` and `⁅fst, ⁅snd, h⁆⁆` are elements
of the centralizer of `g` and `⁅fst, ⁅snd, h⁆⁆` is nontrivial.
-/
structure AlgDisjointWitness (g h : G) :=
  /-- The first element of the pair -/
  fst : G
  /-- The second element of the pair -/
  snd : G
  /-- `fst` must be an element of the centralizer of `g` -/
  fst_comm : Commute fst g
  /-- `snd` must be an element of the centralizer of `g` -/
  snd_comm : Commute snd g
  /-- `comm_elem` must be an element of the centralizer of `g` -/
  comm_elem_commute' : Commute ⁅fst, ⁅snd, h⁆⁆ g
  /-- `comm_elem` must not be trivial -/
  comm_elem_nontrivial' : ⁅fst, ⁅snd, h⁆⁆ ≠ 1

/--
A shorthand for `⁅elem.fst, ⁅elem.snd, h⁆⁆`
-/
def AlgDisjointWitness.comm_elem (elem : AlgDisjointWitness g h) : G :=
  ⁅elem.fst, ⁅elem.snd, h⁆⁆

theorem AlgDisjointWitness.comm_elem_commute (elem : AlgDisjointWitness g h) :
    Commute elem.comm_elem g := elem.comm_elem_commute'

theorem AlgDisjointWitness.comm_elem_nontrivial (elem : AlgDisjointWitness g h) :
    elem.comm_elem ≠ 1 := elem.comm_elem_nontrivial'

/--
The witness for the conjugation of `AlgDisjointElem g h` with `i`.
-/
def AlgDisjointWitness.conj (elem : AlgDisjointWitness g h) (i : G) :
    AlgDisjointWitness (i * g * i⁻¹) (i * h * i⁻¹) where
  fst := i * elem.fst * i⁻¹
  snd := i * elem.snd * i⁻¹
  fst_comm := by
    rw [Commute.conj_iff]
    exact elem.fst_comm
  snd_comm := by
    rw [Commute.conj_iff]
    exact elem.snd_comm
  comm_elem_commute' := by
    rw [← conjugate_commutatorElement, ← conjugate_commutatorElement, Commute.conj_iff]
    exact elem.comm_elem_commute'
  comm_elem_nontrivial' := by
    rw [← conjugate_commutatorElement, ← conjugate_commutatorElement, ne_eq, conj_eq_one_iff]
    exact elem.comm_elem_nontrivial'

theorem AlgDisjointWitness.comm_elem_subset_iUnion (elem : AlgDisjointWitness g h) {s : Set α}
    (movedBy_subset : (fixedBy α h)ᶜ ⊆ s) :
    (fixedBy α elem.comm_elem)ᶜ ⊆ ⋃ (i : Fin 2 × Fin 2),
      (elem.fst ^ i.1.val * elem.snd ^ i.2.val) • s := by
  rw [Set.compl_subset_comm] at movedBy_subset

  -- Split into two cases: one with and one without `f₁` as a factor
  rw [Set.compl_subset_comm, Set.compl_iUnion]
  simp_rw [← Set.smul_set_compl]
  apply subset_trans _ (fixedBy_commutatorElement _ _ _)
  apply Set.subset_inter

  -- Further split both cases into four cases, making sure all of them are of the form
  -- `g • fixedBy α h`
  apply subset_trans _ (fixedBy_commutatorElement _ _ _)
  any_goals (
    apply subset_trans _ (Set.smul_set_mono (fixedBy_commutatorElement _ _ _));
    rw [Set.smul_set_inter]
  )
  all_goals apply Set.subset_inter
  any_goals rw [← mul_smul]
  rw [← one_smul G (fixedBy α h)]

  all_goals apply subset_trans _ (Set.smul_set_mono movedBy_subset)
  · apply Set.iInter_subset_of_subset ⟨0, 0⟩
    simp only [Fin.val_zero, pow_zero, mul_one, one_smul, subset_refl]
  · apply Set.iInter_subset_of_subset ⟨0, 1⟩
    simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one, one_mul, subset_refl]
  · apply Set.iInter_subset_of_subset ⟨1, 0⟩
    simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one, mul_one, subset_refl]
  · apply Set.iInter_subset_of_subset ⟨1, 1⟩
    simp only [Fin.val_one, pow_one, subset_refl]

end Witness

/--
`f` is said to be algebraically disjoint with `g` if for all element `h` that doesn't commute with
`f`, one can construct a witness `AlgDisjointWitness g h`.

That witness consists of two group elements `f₁` and `f₂`,
such that `f₁`, `f₂` and `⁅f₁, ⁅f₂, h⁆⁆` commute with `g`, and the latter is non-trivial.
-/
def IsAlgDisjoint (f g : G) := ∀ h : G, ¬Commute f h → Nonempty (AlgDisjointWitness g h)

theorem isAlgDisjoint_iff_nonempty (f g : G) : IsAlgDisjoint f g ↔
    Nonempty (∀ h : G, ¬Commute f h → AlgDisjointWitness g h) :=
  ⟨fun disj => ⟨fun h nc => (disj h nc).some⟩,
    fun ⟨disj⟩ => fun h nc => ⟨disj h nc⟩⟩

theorem IsAlgDisjoint.conj {f g : G} (disj : IsAlgDisjoint f g) (h : G) :
    IsAlgDisjoint (h * f * h⁻¹) (h * g * h⁻¹) := by
  intro i nc
  rw [← Commute.conj_iff h⁻¹] at nc
  group at nc
  refine (disj _ nc).elim (fun elem => ⟨?elem⟩)
  have res := elem.conj h
  group at res
  rwa [zpow_neg_one] at res

section Disjoint

variable [T2Space α] [ContinuousConstSMul G α]

/--
If two points have disjoint `(fixedBy α g)ᶜ` sets, then they are algebraically disjoint.
-/
theorem IsAlgDisjoint.of_disjoint_movedBy [LocallyDenseSMul G α] [FaithfulSMul G α]
    [NoIsolatedPoints α] {f g : G} (disj_fg : Disjoint (fixedBy α f)ᶜ (fixedBy α g)ᶜ) :
    IsAlgDisjoint f g := by
  intro i nc

  -- Since f and i do not commute, there must exist a point `x ∈ (fixedBy α f)ᶜ ∩ (fixedBy α i)ᶜ`
  have fi_not_disj := mt (commute_of_disjoint_movedBy (α := α)) nc
  have ⟨x, ⟨x_in_movedBy_f, x_in_movedBy_i⟩⟩ := Set.not_disjoint_iff.mp fi_not_disj

  -- We get from the Hausdorff property that `∃ s ∋ x, s ∩ i • s = ∅`
  have ⟨s, s_open, x_in_s, s_ss_movedBy, disj_s_is⟩ := t2_separation_smul_subset
    (isClosed_fixedBy α f).isOpen_compl x_in_movedBy_f x_in_movedBy_i
  clear x_in_movedBy_i fi_not_disj

  -- Since the action is locally dense, we can extract `f₂` such that `f₂` only moves within `s`
  -- and `f₂ • x ≠ x`
  have ⟨f₂, f₂_in_fixing, f₂_moving⟩ := LocallyDenseSMul.moving_elem_in_fixingSubgroup_compl
    G s_open x_in_s
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at f₂_in_fixing

  -- Use the Hausdorff property again to get `∃ t ∋ x, t ∩ f₂ • t = ∅`
  have ⟨t, t_open, x_in_t, t_ss_s, disj_t_f₂t⟩ := t2_separation_smul_subset
    s_open x_in_s f₂_moving

  -- Use the local denseness again, to extract `f₁` such that `f₁` only moves within `t` and
  -- `f₁ • x ≠ x`
  have ⟨f₁, f₁_in_fixing, f₁_moving⟩ := LocallyDenseSMul.moving_elem_in_fixingSubgroup_compl
    G t_open x_in_t
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at f₁_in_fixing

  -- Since `Disjoint s (i • s)` and `t ⊆ s`, while a point `x` is multiplied by `i`, the action of
  -- `f₂` does not affect it, so `(i * f₂ * i⁻¹) • t = t`
  have f₂i_smul_t_eq : ⁅f₂, i⁆ • t = f₂ • t := by
    apply commutatorElement_smul_eq_of_subset_fixedBy_conj
    apply subset_trans t_ss_s
    exact subset_fixedBy_conj_of_movedBy_subset_of_disj f₂_in_fixing disj_s_is

  refine ⟨⟨f₁, f₂, ?nc_f₁, ?nc_f₂, ?nc_comm_elem, ?comm_elem_ne_one⟩⟩
  case nc_f₁ =>
    apply commute_of_disjoint_movedBy (α := α)
    apply Set.disjoint_of_subset_left _ disj_fg
    exact subset_trans f₁_in_fixing (subset_trans t_ss_s s_ss_movedBy)
  case nc_f₂ =>
    apply commute_of_disjoint_movedBy (α := α)
    apply Set.disjoint_of_subset_left _ disj_fg
    exact subset_trans f₂_in_fixing s_ss_movedBy
  case nc_comm_elem =>
    apply commute_of_disjoint_movedBy (α := α)
    apply Set.disjoint_of_subset_left _ disj_fg
    -- `⁅f₁, ⁅f₂, i⁆⁆` does not move any point outside of `s`, although showing this is the case
    -- requires a few intermediate steps:
    calc
      (fixedBy α ⁅f₁, ⁅f₂, i⁆⁆)ᶜ = (fixedBy α ⁅⁅f₂, i⁆, f₁⁆)ᶜ := by
        rw [← fixedBy_inv_eq_fixedBy, commutatorElement_inv]
      _ ⊆ (fixedBy α f₁)ᶜ ∪ ⁅f₂, i⁆ • (fixedBy α f₁)ᶜ := by
        rw [Set.smul_set_compl, ← Set.compl_inter, Set.compl_subset_compl,
          commutatorElement_def _ f₁]
        apply subset_trans _ (fixedBy_commutatorElement α _ _)
        exact subset_of_eq rfl
      _ ⊆ t ∪ ⁅f₂, i⁆ • t := by
        apply Set.union_subset_union
        · assumption
        · apply Set.smul_set_mono
          assumption
      _ = t ∪ f₂ • t := by rw [f₂i_smul_t_eq]
      _ ⊆ s ∪ f₂ • t := Set.union_subset_union_left _ t_ss_s
      _ ⊆ s ∪ s := by
        apply Set.union_subset_union_right
        apply smul_subset_of_set_mem_fixedBy t_ss_s
        exact set_mem_fixedBy_of_movedBy_subset f₂_in_fixing
      _ = s := Set.union_self s
      _ ⊆ (fixedBy α f)ᶜ := s_ss_movedBy
  case comm_elem_ne_one =>
    intro eq_one
    apply f₁_moving
    -- Show that `⁅f₁, ⁅f₂, i⁆⁆ • x = f₁ • x`
    nth_rw 2 [← one_smul (M := G) x]
    rw [← eq_one, ← Set.singleton_eq_singleton_iff, ← Set.smul_set_singleton,
      ← Set.smul_set_singleton, eq_comm]
    apply commutatorElement_smul_eq_of_subset_fixedBy_conj
    apply subset_trans (Set.singleton_subset_iff.mpr x_in_t)
    apply subset_fixedBy_conj_of_movedBy_subset_of_disj f₁_in_fixing
    rw [f₂i_smul_t_eq]
    exact disj_t_f₂t

variable {G α : Type*} [Group G] [MulAction G α]

variable [TopologicalSpace α] [T2Space α] [ContinuousConstSMul G α]

lemma dvd_twelve_of_lt_5_of_pos {i : ℕ} (i_pos : 0 < i) (i_lt_5 : i < 5) : i ∣ 12 := by
  suffices ∀ i : Fin 5, 0 < (i : ℕ) → (i : ℕ) ∣ 12 by
    exact this ⟨i, i_lt_5⟩ i_pos
  intro i
  fin_cases i
  {
    intro ff
    exfalso
    rwa [lt_self_iff_false] at ff
  }
  all_goals (intro; norm_num)

variable [LocallyDenseSMul G α] [FaithfulSMul G α] [NoIsolatedPoints α]

/--
If one can construct a set `s` such that `g ^ i • s` is pairwise disjoint for `i < 5`,
and an element `h` that exclusively moves points within `s` and that doesn't commute with `f`,
then `f` and `g` cannot be algebraically disjoint.

Assuming that `f` and `g` are algebraically disjoint,
then let `f₁` and `f₂` be the witnesses for their disjointness using `¬Commute f h`.

We can then get an element `y` moved by the commutator `⁅f₁, ⁅f₂, h⁆⁆`, and
each `g ^ i • y` will be contained in one of `s`, `f₁ • s`, `f₂ • s` or `(f₁ * f₂) • s`,
so by the pigeonhole principle two such powers of `g` will share one of those sets.

Since both `f₁` and `f₂` commute with `g`, we can get to a contradiction,
since `(f₁^j₁ * f₂^j₂)⁻¹ • y` will be in `g ^ -i₁ • s` and `g ^ -i₂ • s`, which should be disjoint.
-/
theorem not_isAlgDisjoint_of_pairwise_disjoint {f g h: G} {s : Set α}
    (g_orderOf : 5 ≤ orderOf g ∨ orderOf g = 0)
    (pairwise_disj : { g ^ i | i < 5 }.Pairwise (Disjoint on (· • s)))
    (movedBy_subset : (fixedBy α h)ᶜ ⊆ s) (h_nc : ¬Commute f h) : ¬IsAlgDisjoint f g := by
  intro disj
  -- We now have the prerequisites to use the algebraic disjointness hypothesis
  let ⟨disj_elem⟩ := disj h h_nc
  let f₁ := disj_elem.fst
  let f₂ := disj_elem.snd
  let c := ⁅f₁, ⁅f₂, h⁆⁆
  let gs := { g ^ i | i < 5 }

  have movedBy_c_ss_union := disj_elem.comm_elem_subset_iUnion movedBy_subset

  -- `c` is nontrivial, so there must exist a value it moves
  have ⟨y, y_in_movedBy_c⟩ := fixedBy_compl_nonempty_of_ne_one α disj_elem.comm_elem_nontrivial

  have gi_in_movedBy_c : ∀ i : Fin 5, g^i.val • y ∈ (fixedBy α c)ᶜ := by
    intro i
    have h₁ := movedBy_mem_fixedBy_of_commute (α := α) disj_elem.comm_elem_commute
    apply fixedBy_subset_fixedBy_zpow _ _ i.val at h₁
    rw [zpow_coe_nat] at h₁
    exact (smul_mem_of_set_mem_fixedBy h₁).mp y_in_movedBy_c

  have gi_in_image := fun i => (Set.mem_iUnion.mp (movedBy_c_ss_union (gi_in_movedBy_c i)))

  -- By the pigeonhole principle, two different powers of `g ^ i • y` will share a single set
  -- `(f₁^j₁ * f₂^j₂ • s)`.
  -- Note: I had trouble using the pigeonhole principle for `Set.Finite`
  have ⟨i₁, _, i₂, _, i_ne, same_choice⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by norm_num : Fintype.card (Fin 5) > Fintype.card (Fin 2 × Fin 2))
    (fun i _ => Finset.mem_univ (gi_in_image i).choose)
  let pair := (gi_in_image i₁).choose

  let f := (f₁ ^ pair.fst.val * f₂ ^ pair.snd.val)
  have gi₁_in_fst : g^(i₁.val) • y ∈ f • s := (gi_in_image i₁).choose_spec
  have gi₂_in_snd : g^(i₂.val) • y ∈ f • s := by
    unfold_let
    rw [same_choice]
    exact (gi_in_image i₂).choose_spec

  have gi₁_in_family : g^i₁.val ∈ gs := ⟨i₁.val, i₁.prop, rfl⟩
  have gi₂_in_family : g^i₂.val ∈ gs := ⟨i₂.val, i₂.prop, rfl⟩

  have gi₁_ne_gi₂ : g^i₁.val ≠ g^i₂.val := by
    intro eq
    apply i_ne
    rw [Fin.mk.injEq]
    cases g_orderOf with
    | inl orderOf_ge_5 =>
      exact pow_injOn_Iio_orderOf
        (lt_of_lt_of_le i₁.prop orderOf_ge_5)
        (lt_of_lt_of_le i₂.prop orderOf_ge_5)
        eq
    | inr orderOf_eq_zero =>
      rwa [← pow_inj_iff_of_orderOf_eq_zero orderOf_eq_zero]

  have fg_comm : ∀ i : ℕ, Commute f (g^i) := by
    intro i
    unfold_let
    have := disj_elem.fst_comm
    have := disj_elem.snd_comm
    apply Commute.mul_left
    all_goals {
      apply Commute.pow_left
      apply Commute.pow_right
      assumption
    }

  specialize pairwise_disj gi₁_in_family gi₂_in_family gi₁_ne_gi₂

  rw [Function.onFun,
    Set.smul_set_disjoint_inv_of_comm (Commute.pow_left (Commute.pow_right rfl _) _),
    Set.smul_set_disjoint f, ← mul_smul, ← mul_smul, (fg_comm _).inv_right, (fg_comm _).inv_right,
    Set.disjoint_iff_inter_eq_empty] at pairwise_disj

  rw [← Set.mem_empty_iff_false y, ← pairwise_disj]
  apply Set.mem_inter
  · rwa [← Set.mem_inv_smul_set_iff, ← mul_smul] at gi₁_in_fst
  · rwa [← Set.mem_inv_smul_set_iff, ← mul_smul] at gi₂_in_snd

/--
If `f` and `g` are algebraically disjoint, then `(fixedBy α f)ᶜ` and `(fixedBy α g^12)ᶜ` are
disjoint. The mysterious 12th power comes from the fact that it divides `2`, `3` and `4`, allowing
us to use the pigeonhole principle between `{1, g, g², g³, g⁴}` and `{1, f₁, f₂, f₁ * f₂}`.
-/
theorem IsAlgDisjoint.disjoint_movedBy {f g : G}
    (disj : IsAlgDisjoint f g) : Disjoint (fixedBy α f)ᶜ (fixedBy α (g^12))ᶜ := by
  by_contra not_disj
  let ⟨x, x_in_movedBy_f, x_in_movedBy_g12⟩ := Set.not_disjoint_iff.mp not_disj

  have g_period : 5 ≤ MulAction.period g x ∨ MulAction.period g x = 0 := by
    by_cases h : 0 < period g x
    · left
      refine MulAction.le_period h fun n n_pos n_lt_5 gpow_eq => x_in_movedBy_g12 ?x_fixed
      apply fixedBy_pow_subset_of_dvd α g _ gpow_eq
      apply dvd_twelve_of_lt_5_of_pos <;> assumption
    · right
      exact Nat.eq_zero_of_not_pos h

  let gs := { g ^ i | i < 5 }
  have gs_inj : gs.InjOn (· • x) := by
    cases g_period with
    | inl five_le_period =>
      apply Set.InjOn.mono _ (smul_injOn_pow_lt_period g x)
      intro h ⟨a, a_lt_5, ga_eq_h⟩
      exact ⟨a, Nat.lt_of_lt_of_le a_lt_5 five_le_period, ga_eq_h⟩
    | inr period_eq_zero =>
      apply Set.InjOn.mono _ (smul_injOn_zpow_of_period_eq_zero period_eq_zero)
      intro h ⟨a, _, ga_eq_h⟩
      use a
      rw [← ga_eq_h, zpow_coe_nat]

  let ⟨s₀, s₀_open, x_in_s₀, disj_s₀_fs₀⟩ := t2_separation_smul x_in_movedBy_f
  let ⟨s₁, s₁_open, x_in_s₁, pw_disj_gi⟩ := t2_separation_of_smul_injOn gs_inj (
    Set.Finite.image _ (Set.finite_Iio 5))

  have ⟨h, h_in_fixing, h_moving⟩ := LocallyDenseSMul.moving_elem_in_fixingSubgroup_compl
    G (s₀_open.inter s₁_open) ⟨x_in_s₀, x_in_s₁⟩
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at h_in_fixing

  have h_nc : ¬Commute f h := by
    intro comm
    apply h_moving
    nth_rewrite 2 [← one_smul G x]
    rw [← commutatorElement_eq_one_iff_commute.mpr comm.symm, ← Set.singleton_eq_singleton_iff,
      ← Set.smul_set_singleton, ← Set.smul_set_singleton, eq_comm]
    apply commutatorElement_smul_eq_of_subset_fixedBy_conj
    apply subset_trans (Set.singleton_subset_iff.mpr x_in_s₀)
    rw [Set.subset_inter_iff] at h_in_fixing
    apply subset_fixedBy_conj_of_movedBy_subset_of_disj h_in_fixing.left disj_s₀_fs₀

  refine not_isAlgDisjoint_of_pairwise_disjoint
    ?orderOf
    pw_disj_gi
    (h_in_fixing.trans (Set.inter_subset_right _ _))
    h_nc
    disj

  by_cases h_order: orderOf g = 0
  {
    right; assumption
  }
  cases g_period with
  | inl period_ge_5 =>
    left
    refine le_trans period_ge_5 (period_le_orderOf ?pos x)
    exact Nat.pos_of_ne_zero h_order
  | inr period_eq_zero =>
    exfalso
    exact (period_pos_of_orderOf_pos (Nat.pos_of_ne_zero h_order) x).ne' period_eq_zero

end Disjoint

section AlgSupport

-- Speeds up type class inference when writing `MulAut.conj g`:
private instance : CoeFun (G →* MulAut G) fun _ => G → MulAut G := inferInstance

/--
The algebraic support of an element `g` is the centralizer of all `f ^ 12`
for which `f` is algebraically disjoint from `g`.

It has a close relationship with the `(fixedBy α g)ᶜ` set,
and an order-preserving isomorphism between the two using `fixingSubgroup` can be constructed.
-/
def AlgSupport (g : G) : Subgroup G :=
  Subgroup.centralizer ((fun f' => f' ^ 12) '' { f : G | IsAlgDisjoint f g })

theorem AlgSupport.conj (g h : G) : MulAut.conj h • AlgSupport g = AlgSupport (h * g * h⁻¹) := by
  unfold AlgSupport
  simp_rw [Subgroup.pointwise_smul_centralizer, Set.smulSet, ← Set.image_smul, Set.image_image,
    MulAut.smul_def, MulAut.conj_apply, ← conj_pow,
    ← Set.image_image (g := fun f => f ^ 12) (f := fun f => h * f * h⁻¹)]

  apply congr_arg (fun s => Subgroup.centralizer ((fun f => f ^ 12) '' s))
  change (MulAut.conj h).toEquiv '' _ = _
  ext i
  rw [Equiv.image_eq_preimage, ← Equiv.invFun_as_coe, MulEquiv.invFun_eq_symm, Set.mem_preimage,
    MulAut.conj_symm_apply, Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · intro disj
    convert disj.conj h using 1
    repeat rw [← mul_assoc]
    simp only [mul_right_inv, one_mul, mul_inv_cancel_right]
  · intro disj
    convert disj.conj h⁻¹ using 1
    · rw [inv_inv]
    · repeat rw [← mul_assoc]
      simp only [mul_left_inv, one_mul, inv_inv, inv_mul_cancel_right]

/--
The algebraic support basis is made up of all the subgroups of `G` that can be obtained by taking
finite intersections of `AlgSupport`.

TODO: link to paper

Unlike the original paper, the bottom subgroup is allowed to be in this bases, which makes proofs
around ultrafilters easier.
-/
def AlgSupportBasis (G : Type*) [Group G] :=
  {H : Subgroup G // ∃ s : Set G, s.Finite ∧ H = ⨅ g ∈ s, AlgSupport g}

variable (G)

instance AlgSupportBasis.setLike : SetLike (AlgSupportBasis G) G where
  coe := fun H₁ => H₁.val.carrier
  coe_injective' := fun a b eq => by
    rw [← Subtype.coe_inj]
    ext g
    dsimp at eq
    rw [← Subgroup.mem_carrier, eq, Subgroup.mem_carrier]

instance AlgSupportBasis.semiLatticeInf : SemilatticeInf (AlgSupportBasis G) where
  inf := fun H₁ H₂ => ⟨
    H₁.val ⊓ H₂.val,
    by
      let ⟨s₁, s₁_finite, H₁_eq⟩ := H₁.prop
      let ⟨s₂, s₂_finite, H₂_eq⟩ := H₂.prop
      refine ⟨s₁ ∪ s₂, s₁_finite.union s₂_finite, ?iInf_eq⟩
      rw [iInf_union, H₁_eq, H₂_eq]
  ⟩
  inf_le_left := fun H₁ H₂ => inf_le_left (a := H₁.val) (b := H₂.val)
  inf_le_right := fun H₁ H₂ => inf_le_right (a := H₁.val) (b := H₂.val)
  le_inf := fun H₁ H₂ H₃ h₁₂ h₂₃ => (le_inf h₁₂ h₂₃ : H₁.val ≤ H₂.val ⊓ H₃.val)

instance AlgSupportBasis.orderTop : OrderTop (AlgSupportBasis G) where
  top := ⟨
    ⊤,
    by
      use ∅
      simp only [Set.finite_empty, Set.mem_empty_iff_false, not_false_eq_true, iInf_neg, iInf_top,
        and_self]
  ⟩
  le_top := fun H => (le_top : H.val ≤ ⊤)

/--
`G` acts on elements of the algebraic support basis by conjugation.
-/
instance AlgSupportBasis.mulAction : MulAction G (AlgSupportBasis G) where
  smul := fun h H => ⟨
    MulAut.conj h • H.val,
    by
      let ⟨s, s_finite, H_eq⟩ := H.prop
      refine ⟨MulAut.conj h • s, Set.Finite.smul_set s_finite, ?iInf_eq⟩
      simp_rw [H_eq, Subgroup.smul_iInf]
      refine Equiv.iInf_congr (MulAut.conj h) fun g =>
        iInf_congr_Prop Set.smul_mem_smul_set_iff (fun g_in_s => ?conj)
      rw [AlgSupport.conj]
      rfl
  ⟩
  one_smul := fun H => by
    apply Subtype.eq
    change MulAut.conj _ • _ = _
    simp only [map_one, one_smul]
  mul_smul := fun g h H => by
    apply Subtype.eq
    change MulAut.conj _ • _ = MulAut.conj _ • MulAut.conj _ • _
    rw [← mul_smul, map_mul]

variable {G} in
/--
The action on `AlgSupportBasis` is order-preserving.
-/
theorem AlgSupportBasis.smul_le_smul (H₁ H₂ : AlgSupportBasis G) (g : G) :
    g • H₁ ≤ g • H₂ ↔ H₁ ≤ H₂ := by
  change MulAut.conj g • H₁.val ≤ MulAut.conj g • H₂.val ↔ _
  rw [Subgroup.pointwise_smul_le_pointwise_smul_iff]
  rfl

end AlgSupport

end Rubin
