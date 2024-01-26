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

/--
A bundled pair `(fst, snd)` such that `fst`, `snd` and `⁅fst, ⁅snd, h⁆⁆` are elements
of the centralizer of `g` and `⁅fst, ⁅snd, h⁆⁆` is nontrivial.
-/
structure AlgDisjointElem (g h : G) :=
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

-- Note: not needed
/-
def AlgDisjointElem.comm_elem (elem : AlgDisjointElem g h) : G :=
  ⁅elem.fst, ⁅elem.snd, h⁆⁆

theorem AlgDisjointElem.comm_elem_commute (elem : AlgDisjointElem g h) :
    Commute elem.comm_elem g := elem.comm_elem_commute'

theorem AlgDisjointElem.comm_elem_nontrivial (elem : AlgDisjointElem g h) :
    elem.comm_elem ≠ 1 := elem.comm_elem_nontrivial'
-/

/--
The witness for the conjugation of `AlgDisjointElem g h` with `i`.
-/
def AlgDisjointElem.conj (elem : AlgDisjointElem g h) (i : G) :
    AlgDisjointElem (i * g * i⁻¹) (i * h * i⁻¹) where
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

/--
`f` is said to be algebraically disjoint with `g` if for all element `h` that doesn't commute with
`f`, one can construct `AlgDisjointElem g h`.
-/
def IsAlgDisjoint (f g : G) := ∀ h : G, ¬Commute f h → Nonempty (AlgDisjointElem g h)

-- def IsAlgDisjoint (f g : G) := Nonempty (AlgDisjointers f g)

theorem IsAlgDisjoint.conj {f g : G} (disj : IsAlgDisjoint f g) (h : G) :
    IsAlgDisjoint (h * f * h⁻¹) (h * g * h⁻¹) := by
  intro i nc
  rw [← Commute.conj_iff h⁻¹] at nc
  group at nc
  refine (disj _ nc).elim (fun elem => ⟨?elem⟩)
  have res := elem.conj h
  group at res
  rwa [zpow_neg_one] at res

/--
The algebraic centralizer of `g` contains all the elements `h` that commute with `f^12`,
such that `f` is some group element that is algebraically disjoint with `g`.

If the group action is locally moving and faithful on a topological space,
then `algCentralizer g = fixingSubgroup (interior (closure (fixedBy α g)))`.
-/
def algCentralizer (g : G) : Subgroup G :=
  Subgroup.centralizer { f^12 | (f : G) (_: IsAlgDisjoint f g) }

variable [T2Space α] [ContinuousConstSMul G α]

/--
If the action of `G` on `α` is continuous in `α`, then for all points not fixed by `g : G`,
there exists an open set `s` such that `x ∈ s` and `g • s` is disjoint from `s`.
-/
theorem t2_separation_smul {x : α} {g : G}
    (x_moved : x ∉ fixedBy α g) :
    ∃ s : Set α, IsOpen s ∧ x ∈ s ∧ Disjoint s (g • s) := by
  let ⟨s, t, s_open, t_open, gx_in_s, x_in_t, disj_st⟩ := t2_separation x_moved
  let u := (g⁻¹ • s) ∩ t
  have u_open : IsOpen u := (s_open.smul g⁻¹).inter t_open

  refine ⟨u, u_open, ⟨?gx_in_gs, x_in_t⟩, ?disj⟩
  · rwa [Set.mem_inv_smul_set_iff]
  · simp only [Set.smul_set_inter, smul_inv_smul]
    exact Set.disjoint_of_subset
      (Set.inter_subset_right _ _)
      (Set.inter_subset_left _ _)
      disj_st.symm

theorem t2_separation_smul_subset {x : α} {g : G} {s : Set α} (s_open : IsOpen s) (x_in_s : x ∈ s)
    (x_moved : x ∉ fixedBy α g) :
    ∃ t : Set α, IsOpen t ∧ x ∈ t ∧ t ⊆ s ∧ Disjoint t (g • t) := by
  let ⟨t, t_open, x_in_t, disj_t_gt⟩ := t2_separation_smul x_moved
  refine ⟨s ∩ t, s_open.inter t_open, ⟨x_in_s, x_in_t⟩, Set.inter_subset_left _ _, ?disj⟩
  rw [Set.smul_set_inter]
  exact Set.disjoint_of_subset (Set.inter_subset_right _ _) (Set.inter_subset_right _ _) disj_t_gt

variable (α) in
theorem isOpen_movedBy (g : G) : IsOpen (fixedBy α g)ᶜ := by
  refine isOpen_iff_forall_mem_open.mpr (fun x x_moved => ?ex_subset)
  let ⟨s, t, s_open, t_open, gx_in_s, x_in_t, disj_st⟩ := t2_separation x_moved

  exact ⟨
    (g⁻¹ • s) ∩ t,
    fun y ⟨gy_in_s, y_in_t⟩ =>
      Disjoint.ne_of_mem disj_st (Set.mem_inv_smul_set_iff.mp gy_in_s) y_in_t,
    (s_open.smul g⁻¹).inter t_open,
    ⟨Set.mem_inv_smul_set_iff.mpr gx_in_s, x_in_t⟩
  ⟩

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
    (isOpen_movedBy α f) x_in_movedBy_f x_in_movedBy_i
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

section MovingFamily

variable {G α : Type*} [Group G] [MulAction G α]

/--
A finite set of elements of `G` are a moving family for `x : α` if for all `g ≠ h` of the family,
`g • x ≠ h • x`.
-/
def MovingFamily (s: Set G) (x : α): Prop :=
  Set.Pairwise s (fun g h => g • x ≠ h • x)

theorem MovingFamily.ne_of_ne {s : Set G} {x : α} (family : MovingFamily s x) {g h : G}
    (g_in_s : g ∈ s) (h_in_s : h ∈ s) (g_ne_h : g ≠ h) : g • x ≠ h • x := by
  apply family <;> assumption

theorem MovingFamily.of_superset {s₁ s₂ : Set G} {x : α} (superset : s₁ ⊆ s₂)
    (family : MovingFamily s₂ x) : MovingFamily s₁ x := by
  apply Set.Pairwise.mono superset family

theorem MovingFamily.of_le_period (g : G) (x : α) :
    MovingFamily (Set.range (fun i : Fin (period g x) => g ^ i.val)) x := by
  intro h h_in_img i i_in_img h_ne_i ga_eq_gb
  let ⟨⟨a, a_lt_n⟩, ga_eq_h⟩ := h_in_img
  let ⟨⟨b, b_lt_n⟩, gb_eq_i⟩ := i_in_img
  dsimp only at ga_eq_h gb_eq_i

  rw [← ga_eq_h, ← gb_eq_i, MulAction.smul_pow_eq_of_period_dvd] at ga_eq_gb
  refine Nat.not_lt.mpr
    (Nat.le_of_dvd ?pos ga_eq_gb)
    (Int.natAbs_coe_sub_coe_lt_of_lt b_lt_n a_lt_n)

  rw [Int.natAbs_sub_pos_iff, ne_eq, Nat.cast_inj]
  exact fun eq => h_ne_i ((eq ▸ ga_eq_h) ▸ gb_eq_i)

theorem MovingFamily.of_period_eq_zero {g : G} {x : α} (period_eq_zero : period g x = 0) :
    MovingFamily (Set.range (fun i : ℤ => g ^ i)) x := by
  intro h h_in_img i i_in_img h_ne_i ga_eq_gb
  let ⟨a, ga_eq_h⟩ := h_in_img
  let ⟨b, gb_eq_i⟩ := i_in_img

  rw [← ga_eq_h, ← gb_eq_i, MulAction.smul_zpow_eq_of_period_dvd, period_eq_zero,
    Int.ofNat_zero, zero_dvd_iff, sub_eq_zero] at ga_eq_gb
  rw [← ga_eq_h, ← gb_eq_i, ga_eq_gb] at h_ne_i
  exact h_ne_i rfl

@[deprecated]
theorem MovingFamily.of_pow_moves_of_dvd {g : G} {x : α} (n f : ℕ)
    (g_pow_moves : g ^ f • x ≠ x) (f_dvd : ∀ i, 0 < i → i < n → i ∣ f) :
    MovingFamily (Set.range (fun i: Fin n => g ^ i.val)) x := by
  -- TODO: investigate how much of this can be moved to MulAction.period
  intro h h_in_img i i_in_img h_ne_i ga_eq_gb
  apply g_pow_moves
  rw [Set.mem_range] at h_in_img i_in_img
  let ⟨⟨a, a_lt_n⟩, ga_eq_h⟩ := h_in_img
  let ⟨⟨b, b_lt_n⟩, gb_eq_i⟩ := i_in_img
  dsimp only at ga_eq_h gb_eq_i

  have a_ne_b : a ≠ b := fun eq => h_ne_i ((eq ▸ ga_eq_h) ▸ gb_eq_i)
  rw [← ga_eq_h, ← gb_eq_i, smul_eq_iff_eq_inv_smul, ← mul_smul] at ga_eq_gb
  group at ga_eq_gb
  rw [add_comm, eq_comm, ← mem_fixedBy, ← sub_eq_add_neg] at ga_eq_gb

  rw [← zpow_ofNat, ← mem_fixedBy]
  apply fixedBy_zpow_subset_of_dvd α _ _ ga_eq_gb

  rw [← abs_dvd, Int.abs_eq_natAbs, Int.ofNat_dvd]
  apply f_dvd
  · rwa [← Nat.cast_lt (α := ℤ), Int.coe_natAbs, Int.ofNat_zero, abs_pos, ne_eq, sub_eq_zero,
      Nat.cast_inj, eq_comm]
  · exact Int.natAbs_coe_sub_coe_lt_of_lt a_lt_n b_lt_n


theorem MovingFamily.forall_ne_of_subset {s t: Set G} {g : G} (g_in_s : g ∈ s) (t_ss_s : t ⊆ s)
    (g_notin_t : g ∉ t) {x : α} (family : MovingFamily s x) :
    ∀ h ∈ t, g • x ≠ h • x := by
  intro h h_in_t
  apply family.ne_of_ne g_in_s (t_ss_s h_in_t)
  intro g_eq_h
  exact g_notin_t (g_eq_h ▸ h_in_t)

theorem MovingFamily.mem_movedBy_of_ne {s : Set G} {x : α} (family : MovingFamily s x) {g h : G}
    (g_in_s : g ∈ s) (h_in_s : h ∈ s) (g_ne_h : g ≠ h) : x ∈ (fixedBy α (h⁻¹ * g))ᶜ := by
  rw [Set.mem_compl_iff, mem_fixedBy, mul_smul, smul_eq_iff_eq_inv_smul, inv_inv]
  apply family.ne_of_ne <;> assumption

variable [TopologicalSpace α] [T2Space α] [ContinuousConstSMul G α]

/--
An open set `t` for which `Disjoint t ((h⁻¹ * g) • t)`, obtained from `t2_separation_smul`.
-/
noncomputable def MovingFamily.t2_of_pair {s : Set G} {x : α} (family : MovingFamily s x)
    {g h : G} (g_in_s : g ∈ s) (h_in_s : h ∈ s) (g_ne_h : g ≠ h) : Set α :=
  (t2_separation_smul (family.mem_movedBy_of_ne g_in_s h_in_s g_ne_h)).choose

theorem MovingFamily.t2_of_pair_isOpen {s : Set G} {x : α} (family : MovingFamily s x)
    {g h : G} (g_in_s : g ∈ s) (h_in_s : h ∈ s) (g_ne_h : g ≠ h) :
    IsOpen (family.t2_of_pair g_in_s h_in_s g_ne_h) :=
  (t2_separation_smul (family.mem_movedBy_of_ne g_in_s h_in_s g_ne_h)).choose_spec.1

theorem MovingFamily.x_in_t2_of_pair {s : Set G} {x : α} (family : MovingFamily s x)
    {g h : G} (g_in_s : g ∈ s) (h_in_s : h ∈ s) (g_ne_h : g ≠ h) :
    x ∈ (family.t2_of_pair g_in_s h_in_s g_ne_h) :=
  (t2_separation_smul (family.mem_movedBy_of_ne g_in_s h_in_s g_ne_h)).choose_spec.2.1

theorem MovingFamily.t2_of_pair_disjoint {s : Set G} {x : α} (family : MovingFamily s x)
    {g h : G} (g_in_s : g ∈ s) (h_in_s : h ∈ s) (g_ne_h : g ≠ h) :
    Disjoint (family.t2_of_pair g_in_s h_in_s g_ne_h)
      ((h⁻¹ * g) • (family.t2_of_pair g_in_s h_in_s g_ne_h)) :=
  (t2_separation_smul (family.mem_movedBy_of_ne g_in_s h_in_s g_ne_h)).choose_spec.2.2

/--
One can construct an open set `t` such that for every pair `g ≠ h` of `s`,
`g • t` is disjoint from `h • t`.
-/
theorem MovingFamily.t2_separation {s : Set G} {x : α} (family : MovingFamily s x)
    (s_finite : s.Finite) : ∃ t : Set α, IsOpen t ∧ x ∈ t ∧
      Set.Pairwise (s : Set G) (fun g h => Disjoint (g • t) (h • t)) := by
  let pairs := { pair : G × G | pair.1 ∈ s ∧ pair.2 ∈ s ∧ pair.1 ≠ pair.2 }
  have pairs_finite : Set.Finite pairs := by
    apply Set.Finite.subset (s_finite.prod s_finite)
    intro ⟨g, h⟩ ⟨g_in_s, h_in_s, _⟩
    exact ⟨g_in_s, h_in_s⟩

  let sets : pairs → Set α := fun ⟨pair, ⟨g_in_s, h_in_s, g_ne_h⟩⟩ =>
    family.t2_of_pair g_in_s h_in_s g_ne_h

  refine ⟨⋂ pair, sets pair, ?isOpen, ?x_in_sets, ?pairwise_disjoint⟩
  case isOpen =>
    have := pairs_finite.fintype
    apply isOpen_iInter_of_finite
    intro ⟨⟨g, h⟩, ⟨g_in_s, h_in_s, g_ne_h⟩⟩
    apply MovingFamily.t2_of_pair_isOpen
  case x_in_sets =>
    apply Set.mem_iInter_of_mem
    intro ⟨⟨g, h⟩, ⟨g_in_s, h_in_s, g_ne_h⟩⟩
    apply MovingFamily.x_in_t2_of_pair
  case pairwise_disjoint =>
    intro g g_in_s h h_in_s g_ne_h
    let pair : pairs := ⟨⟨g, h⟩, ⟨g_in_s, h_in_s, g_ne_h⟩⟩
    apply Set.disjoint_of_subset
    · show g • ⋂ pair, sets pair ⊆ g • sets pair
      apply Set.smul_set_mono
      apply Set.iInter_subset _ pair
    · show h • ⋂ pair, sets pair ⊆ h • sets pair
      apply Set.smul_set_mono
      apply Set.iInter_subset _ pair
    · rw [Set.smul_set_disjoint h⁻¹, inv_smul_smul]
      apply Disjoint.symm
      rw [← mul_smul]
      apply MovingFamily.t2_of_pair_disjoint

end MovingFamily

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

lemma MulAction.smul_pow_inj_of_le_period {g : G} {x : α} {n m : ℕ}
    (n_lt_period : n < MulAction.period g x) (m_lt_period : m < MulAction.period g x)
    (pow_eq : g ^ n = g ^ m): n = m := by
  rw [← mul_inv_eq_one, ← zpow_ofNat, ← zpow_ofNat, ← zpow_neg, ← zpow_add,
    ← sub_eq_add_neg] at pow_eq
  by_contra ne
  apply lt_iff_not_le.mp (Int.natAbs_coe_sub_coe_lt_of_lt m_lt_period n_lt_period)

  apply MulAction.period_le_natAbs_of_fixed
  · rwa [ne_eq, sub_eq_zero, Nat.cast_inj]
  · rw [pow_eq, one_smul]

lemma MulAction.smul_pow_inj_of_period_eq_zero {g : G} {x : α} {n m : ℕ}
    (period_eq_zero : MulAction.period g x = 0) (pow_eq : g ^ n = g ^ m) : n = m := by
  rw [← mul_inv_eq_one, ← zpow_ofNat, ← zpow_ofNat, ← zpow_neg, ← zpow_add,
    ← sub_eq_add_neg] at pow_eq
  by_contra ne

  rw [MulAction.period_eq_zero_iff_forall_zpow] at period_eq_zero
  apply period_eq_zero (↑n - ↑m)
  · rwa [ne_eq, sub_eq_zero, Nat.cast_inj]
  · rw [pow_eq, one_smul]

/--
If `f` and `g` are algebraically disjoint, then `(fixedBy α f)ᶜ` and `(fixedBy α g^12)ᶜ` are
disjoint. The mysterious 12th power that is introduced comes from the well-behavedness of `g^3` and
`g^4`.
-/
theorem IsAlgDisjoint.disjoint_movedBy [LocallyDenseSMul G α] [FaithfulSMul G α]
    [NoIsolatedPoints α] {f g : G}
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

  let fam := Set.range (fun i : Fin 5 => g ^ i.val)
  have fam_moving : MovingFamily fam x := by
    cases g_period with
    | inl five_le_period =>
      apply MovingFamily.of_superset _ (MovingFamily.of_le_period g x)
      intro h ⟨⟨a, a_lt_5⟩, ga_eq_h⟩
      refine ⟨⟨a, ?a_lt_period⟩, ga_eq_h⟩
      exact Nat.lt_of_lt_of_le a_lt_5 five_le_period
    | inr period_eq_zero =>
      apply MovingFamily.of_superset _ (MovingFamily.of_period_eq_zero period_eq_zero)
      intro h ⟨⟨a, a_lt_5⟩, ga_eq_h⟩
      use a
      rw [← ga_eq_h]
      simp only [zpow_coe_nat]

  let ⟨s₀, s₀_open, x_in_s₀, disj_s₀_fs₀⟩ := t2_separation_smul x_in_movedBy_f
  let ⟨s₁, s₁_open, x_in_s₁, pw_disj_gi⟩ := fam_moving.t2_separation (Set.finite_range _)

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

  -- TODO: split here
  clear s₀_open s₁_open x_in_s₁ x_in_s₀ h_moving disj_s₀_fs₀ fam_moving x_in_movedBy_g12
    not_disj x_in_movedBy_f

  -- We now have the prerequisites to use the algebraic disjointness hypothesis
  let ⟨f₁, f₂, f₁_comm, f₂_comm, comm_elem_comm, comm_elem_nt⟩ := disj h h_nc
  let c := ⁅f₁, ⁅f₂, h⁆⁆

  have movedBy_c_ss_union : (fixedBy α c)ᶜ
    ⊆ ⋃ (i : Fin 2 × Fin 2), (f₁^i.1.val * f₂^i.2.val) • (s₀ ∩ s₁) := by
    rw [Set.compl_subset_comm] at h_in_fixing

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

    -- fin_cases doesn't seem to be applicable when the term isn't in the hypothesis :/
    all_goals apply subset_trans _ (Set.smul_set_mono h_in_fixing)
    · apply Set.iInter_subset_of_subset ⟨0, 0⟩
      simp only [Fin.val_zero, pow_zero, mul_one, one_smul, subset_refl]
    · apply Set.iInter_subset_of_subset ⟨0, 1⟩
      simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one, one_mul, subset_refl]
    · apply Set.iInter_subset_of_subset ⟨1, 0⟩
      simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one, mul_one, subset_refl]
    · apply Set.iInter_subset_of_subset ⟨1, 1⟩
      simp only [Fin.val_one, pow_one, subset_refl]

  -- `c` is nontrivial, so there must exist a value it moves
  have ⟨y, y_in_movedBy_c⟩ := fixedBy_compl_nonempty_of_ne_one α comm_elem_nt


  have gi_in_movedBy_c : ∀ i : Fin 5, g^i.val • y ∈ (fixedBy α c)ᶜ := by
    intro i
    have h₁ := movedBy_mem_fixedBy_of_commute (α := α) comm_elem_comm
    apply fixedBy_subset_fixedBy_zpow _ _ i.val at h₁
    rw [zpow_coe_nat] at h₁
    rw [← smul_mem_of_set_mem_fixedBy h₁]
    exact y_in_movedBy_c

  have gi_in_image := fun i => (Set.mem_iUnion.mp (movedBy_c_ss_union (gi_in_movedBy_c i)))

  -- Note: Set's version gives me hell with this, but it probably leads to a cleaner proof
  have ⟨i₁, _, i₂, _, i_ne, same_choice⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by norm_num : Fintype.card (Fin 5) > Fintype.card (Fin 2 × Fin 2))
    (fun i _ => Finset.mem_univ (gi_in_image i).choose)
  let pair := (gi_in_image i₁).choose

  let f := (f₁ ^ pair.fst.val * f₂ ^ pair.snd.val)
  have gi₁_in_fst : g^(i₁.val) • y ∈ f • (s₀ ∩ s₁) := (gi_in_image i₁).choose_spec
  have gi₂_in_snd : g^(i₂.val) • y ∈ f • (s₀ ∩ s₁) := by
    unfold_let
    rw [same_choice]
    exact (gi_in_image i₂).choose_spec

  have gi₁_in_family : g^i₁.val ∈ fam := ⟨⟨i₁.val, i₁.prop⟩, rfl⟩
  have gi₂_in_family : g^i₂.val ∈ fam := ⟨⟨i₂.val, i₂.prop⟩, rfl⟩

  have gi₁_ne_gi₂ : g^i₁.val ≠ g^i₂.val := by
    intro eq
    apply i_ne
    rw [Fin.mk.injEq]
    cases g_period with
    | inl g_period_le_5 =>
      apply MulAction.smul_pow_inj_of_le_period (x := x) _ _ eq
      all_goals {
        apply lt_of_lt_of_le _ g_period_le_5
        apply Fin.is_lt
      }
    | inr period_eq_zero =>
      exact MulAction.smul_pow_inj_of_period_eq_zero period_eq_zero eq

  have fg_comm : ∀ i : ℕ, Commute f (g^i) := by
    intro i
    unfold_let
    apply Commute.mul_left
    all_goals {
      apply Commute.pow_left
      apply Commute.pow_right
      assumption
    }

  specialize pw_disj_gi gi₁_in_family gi₂_in_family gi₁_ne_gi₂
  rw [Set.smul_set_disjoint_inv_of_comm (Commute.pow_left (Commute.pow_right rfl _) _),
    Set.smul_set_disjoint f, ← mul_smul, ← mul_smul, (fg_comm _).inv_right, (fg_comm _).inv_right,
    Set.disjoint_iff_inter_eq_empty] at pw_disj_gi

  rw [← Set.mem_empty_iff_false y, ← pw_disj_gi]
  apply Set.mem_inter
  · rw [← Set.mem_inv_smul_set_iff, ← mul_smul] at gi₁_in_fst
    exact Set.smul_set_mono (Set.inter_subset_right s₀ s₁) gi₁_in_fst
  · rw [← Set.mem_inv_smul_set_iff, ← mul_smul] at gi₂_in_snd
    exact Set.smul_set_mono (Set.inter_subset_right s₀ s₁) gi₂_in_snd

end Rubin
