/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module conj_class_count
-/

import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes

/-! # Centralizer of a permutation and cardinality of conjugacy classes
  # in the symmetric and alternating groups

Let `α : Type` with `Fintype α` (and `DecidableEq α`).
The main goal of this file is to compute the cardinality of
conjugacy classes in `Equiv.Perm α` and `alternatingGroup α`.
Every `g : Equiv.Perm α` has a `cycleType α : Multiset ℕ`.
By `Equiv.Perm.isConj_iff_cycleType_eq`,
two permutations are conjugate in `Equiv.Perm α` iff
their cycle types are equal.
To compute the cardinality of the conjugacy classes, we could use
a purely combinatorial approach and compute the number of permutations
with given cycle type but we resorted to a more algebraic approach.

Given `g : Equiv.Perm α`, the conjugacy class of `g` is the orbit
of `g` under the action `ConjAct (Equiv.Perm α)`, and we use
the orbit-stabilizer theorem
(`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`)
to reduce the computation to the computation of the centralizer of `g`,
the subgroup of `Equiv.Perm α` consisting of all permutations
which commute with `g`. It is accessed here as
`MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`.

We compute this subgroup as follows.

* If `h : MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`, then the action
  of `h` by conjugation on `Equiv.Perm α` stabilizes `g.cycleFactorsFinset`.
  That induces an action of `MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  on `g.cycleFactorsFinset` which is defined via
  `Equiv.Perm.OnCycleFactors.subMulActionOnCycleFactors `

* This action defines a group morphism `Equiv.Perm.OnCycleFactors.φ g` from
  `MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  to `Equiv.Perm (g.cycleFactorsFinset)`

* `Equiv.Perm.OnCycleFactors.Iφ_eq_range` shows that the range of `Equiv.Perm.OnCycleFactors.φ g`
  is the subgroup `Iφ g` of `Equiv.Perm (g.cycleFactorsFinset)`
  consisting of permutations `τ` which preserve the length of the cycles.
  This is showed by constructing a right inverse `Equiv.Perm.OnCycleFactors.φ'`
  in `Equiv.Perm.OnCycleFactors.hφ'_is_rightInverse`.

* `Equiv.Perm.OnCycleFactors.hφ_range_card` computes the cardinality of
  `range (Equiv.Perm.OnCycleFactors.φ g)` as a product of factorials.

* For an element `z : Equiv.Perm α`, we then prove in
  `Equiv.Perm.OnCycleFactors.hφ_mem_ker_iff` that `ConjAct.toConjAct z` belongs to
  the kernel of `Equiv.Perm.OnCycleFactors.φ g` if and only if it permutes `g.fixedPoints`
  and it acts on each cycle of `g` as a power of that cycle.
  This gives a description of the kernel of `Equiv.Perm.OnCycleFactors.φ g` as the product
  of a symmetric group and of a product of cyclic groups.
  This analysis starts with the morphism `Equiv.Perm.OnCycleFactors.θ`,
  its injectivity `Equiv.Perm.OnCycleFactors.hθ_injective`,
  its range `Equiv.Perm.OnCycleFactors.hφ_ker_eq_θ_range`,
  and  its cardinality `Equiv.Perm.OnCycleFactors.hθ_range_card`.

* `Equiv.Perm.conj_stabilizer_card g` computes the cardinality
  of the centralizer of `g`

* `Equiv.Perm.conj_class_card_mul_eq g` computes the cardinality
  of the conjugacy class of `g`.

* We now can compute the cardinality of the set of permutations with given cycle type.
  The condition for this cardinality to be zero is given by
  `Equiv.Perm.card_of_cycleType_eq_zero_iff`
  which is itself derived from `Equiv.Perm.exists_with_cycleType_iff`.

* `Equiv.Perm.card_of_cycleType_mul_eq m` and `Equiv.Perm.card_of_cycleType m`
  compute this cardinality.

* `AlternatingGroup.of_cycleType_eq m` and `AlternatingGroup.card_of_cycleType m`
  give the analogous result in the subgroup `alternatingGroup α`

* `Equiv.Perm.OnCycleFactors.sign_ψ` computes the signature of the permutation induced given by `ψ`.

* Finally, `Equiv.Perm.OnCycleFactors.kerφ_le_alternating_iff`
  establishes on which iff-condition the centralizer of an even permutation
  is contained in `alternatingGroup α`.

  TODO : deduce the formula for the cardinality of the centralizers
  and conjugacy classes in `alternatingGroup α`.

-/

open scoped Pointwise

section permutations

variable {α : Type _} [Fintype α] [DecidableEq α]

theorem Equiv.Perm.disjoint_iff_support_disjoint
    {f g : Equiv.Perm α} :
    f.Disjoint g ↔ _root_.Disjoint f.support g.support := by
  simp only [Equiv.Perm.disjoint_iff_eq_or_eq,
    Finset.disjoint_iff_inter_eq_empty, ← Equiv.Perm.not_mem_support,
    ← Finset.mem_compl, ← Finset.mem_union, ← Finset.compl_inter,
    ← Finset.compl_eq_univ_iff, ← Finset.eq_univ_iff_forall]
#align equiv.perm.disjoint_iff_support_disjoint Equiv.Perm.disjoint_iff_support_disjoint

theorem Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff
    (g c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset) (x : α) :
    c = g.cycleOf x ↔ x ∈ c.support := by
  constructor
  · intro hcx
    rw [Equiv.Perm.mem_support, hcx, Equiv.Perm.cycleOf_apply_self,
      Ne.def, ← Equiv.Perm.cycleOf_eq_one_iff, ← hcx]
    exact Equiv.Perm.IsCycle.ne_one (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).left
  · intro hx; exact Equiv.Perm.cycle_is_cycleOf hx hc
#align equiv.perm.is_cycle_eq_cycle_of_iff Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff


end permutations

section CycleTypes

variable (α : Type _) [DecidableEq α] [Fintype α]

-- Maybe that should be a type rather than a Finset
/-- The `Finset (Equiv.Perm α)` of permutations with cycle type `c`-/
def Equiv.permWithCycleType (c : Multiset ℕ) :=
  Finset.filter (fun g : Equiv.Perm α => Equiv.Perm.cycleType g = c) Finset.univ
#align equiv.perm_with_cycle_type Equiv.permWithCycleType

variable {α}

/-- `a : α` belongs to the support of `k • g` iff
  `k⁻¹ * a` belongs to the support of `g` -/
theorem Equiv.Perm.conj_support_eq (k : ConjAct (Equiv.Perm α)) (g : Equiv.Perm α) (a : α) :
    a ∈ (k • g).support ↔ ConjAct.ofConjAct k⁻¹ a ∈ g.support := by
  simp only [Equiv.Perm.mem_support, ConjAct.smul_def]
  rw [not_iff_not]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, ConjAct.ofConjAct_inv]
  apply Equiv.apply_eq_iff_eq_symm_apply
#align equiv.perm.conj_support_eq Equiv.Perm.conj_support_eq

/-- A permutation `c` is a cycle of `g` iff `k * c * k⁻¹` is a cycle of `k * g * k⁻¹` -/
theorem Equiv.Perm.mem_cycleFactorsFinset_conj (g k c : Equiv.Perm α) :
    k * c * k⁻¹ ∈ (k * g * k⁻¹).cycleFactorsFinset ↔ c ∈ g.cycleFactorsFinset := by
  suffices imp_lemma :
    ∀ (g k c : Equiv.Perm α) (_ : c ∈ g.cycleFactorsFinset),
      k * c * k⁻¹ ∈ (k * g * k⁻¹).cycleFactorsFinset
  · constructor
    · intro h
      suffices ∀ h : Equiv.Perm α, h = k⁻¹ * (k * h * k⁻¹) * k by
        rw [this g, this c]
        apply imp_lemma
        exact h
      intro h
      group
    · apply imp_lemma g k c
  · intro g k c
    simp only [Equiv.Perm.mem_cycleFactorsFinset_iff]
    rintro ⟨hc, hc'⟩
    constructor
    exact Equiv.Perm.IsCycle.conj hc
    intro a ha
    simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
    apply hc'
    rw [Equiv.Perm.mem_support] at ha ⊢
    intro ha'; apply ha
    simp only [mul_smul, ← Equiv.Perm.smul_def] at ha' ⊢
    rw [ha']
    simp only [Equiv.Perm.smul_def, Equiv.Perm.apply_inv_self]
#align equiv.perm.mem_cycle_factors_conj Equiv.Perm.mem_cycleFactorsFinset_conj

theorem Equiv.Perm.cycleFactorsFinset_conj (g k : Equiv.Perm α) :
    (k * g * k⁻¹).cycleFactorsFinset =
      Finset.map (MulAut.conj k).toEquiv.toEmbedding g.cycleFactorsFinset := by
  ext c
  rw [Finset.mem_map_equiv]
  rw [← Equiv.Perm.mem_cycleFactorsFinset_conj g k]
  apply iff_of_eq
  apply congr_arg₂ _ _
  rfl
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv_symm, MulAut.conj_symm_apply]
  group
#align equiv.perm.cycle_factors_conj Equiv.Perm.cycleFactorsFinset_conj

/-- A permutation `c` is a cycle of `g` iff `k • c` is a cycle of `k • g` -/
theorem Equiv.Perm.mem_cycleFactorsFinset_conj'
    (k : ConjAct (Equiv.Perm α)) (g c : Equiv.Perm α) :
    k • c ∈ (k • g).cycleFactorsFinset ↔ c ∈ g.cycleFactorsFinset := by
  simp only [ConjAct.smul_def]
  apply Equiv.Perm.mem_cycleFactorsFinset_conj
#align equiv.perm.mem_cycle_factors_conj' Equiv.Perm.mem_cycleFactorsFinset_conj'

theorem Equiv.Perm.cycleFactorsFinset_conj_eq
    (k : ConjAct (Equiv.Perm α)) (g : Equiv.Perm α) :
    Equiv.Perm.cycleFactorsFinset (k • g) = k • Equiv.Perm.cycleFactorsFinset g := by
  ext c
  rw [← Equiv.Perm.mem_cycleFactorsFinset_conj' k⁻¹ (k • g) c]
  simp only [inv_smul_smul]
  exact Finset.inv_smul_mem_iff
#align equiv.perm.mem_cycle_factors_conj_eq Equiv.Perm.cycleFactorsFinset_conj_eq

open scoped Pointwise

/- NB. The converse of the next theorem is false. Commuting with every cycle of `g`
  means that we belong to the kernel of the action of `Equiv.Perm α` on `g.cycleFactorsFinset` -/
/-- If a permutation commutes with every cycle of `g`, then it commutes with `g` -/
theorem Equiv.Perm.commute_of_mem_cycleFactorsFinset_commute (k g : Equiv.Perm α)
    (hk : ∀ c ∈ g.cycleFactorsFinset, Commute k c) :
    Commute k g := by
  rw [← Equiv.Perm.cycleFactorsFinset_noncommProd g (Equiv.Perm.cycleFactorsFinset_mem_commute g)]
  apply Finset.noncommProd_commute
  simp only [id.def]
  exact hk
#align equiv.perm.commute_of_mem_cycles_factors_commute
  Equiv.Perm.commute_of_mem_cycleFactorsFinset_commute

/-- The cycles of a permutation commute with it -/
theorem Equiv.Perm.self_mem_cycle_factors_commute {g c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) : Commute c g := by
  apply Equiv.Perm.commute_of_mem_cycleFactorsFinset_commute
  intro c' hc'
  by_cases hcc' : c = c'
  rw [hcc']
  apply g.cycleFactorsFinset_mem_commute hc hc'; exact hcc'
#align equiv.perm.self_mem_cycle_factors_commute Equiv.Perm.self_mem_cycle_factors_commute

/-- If g and c commute, then g stabilizes the support of c -/
theorem Equiv.Perm.mem_support_of_commute {g c : Equiv.Perm α} (hgc : Commute g c) :
    ∀ x : α, x ∈ c.support ↔ g x ∈ c.support := by
  intro x
  simp only [Equiv.Perm.mem_support, not_iff_not, ← Equiv.Perm.mul_apply]
  rw [← hgc, Equiv.Perm.mul_apply]
  exact (Equiv.apply_eq_iff_eq g).symm
#align equiv.perm.mem_support_of_commute Equiv.Perm.mem_support_of_commute

/-- If `c` and `d` are cycles of `g`,
  then `d` stabilizes the support of `c` -/
theorem Equiv.Perm.mem_support_cycle_of_cycle {g d c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) (hd : d ∈ g.cycleFactorsFinset) :
    ∀ x : α, x ∈ c.support ↔ d x ∈ c.support := by
  intro x
  simp only [Equiv.Perm.mem_support, not_iff_not]
  by_cases h : c = d
  rw [← h, EmbeddingLike.apply_eq_iff_eq]
  rw [← Equiv.Perm.mul_apply,
      Commute.eq (Equiv.Perm.cycleFactorsFinset_mem_commute g hc hd h),
      Equiv.Perm.mul_apply, EmbeddingLike.apply_eq_iff_eq]

/-- If a permutation is a cycle of `g`, then its support is invariant under `g`-/
theorem Equiv.Perm.mem_cycleFactorsFinset_support {g c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) (a : α) : a ∈ c.support ↔ g a ∈ c.support := by
  apply Equiv.Perm.mem_support_of_commute
  exact (Equiv.Perm.self_mem_cycle_factors_commute hc).symm
#align equiv.perm.mem_cycle_factors_finset_support Equiv.Perm.mem_cycleFactorsFinset_support

-- USEFUL ?
/-- If `c` is a cycle of `g`, `x` belongs to the support of `g`
  and `y` belongs to the support of `c`,
  then `c` is the cycle of `x` for `g` iff `x` and `y` belong to the same cycle. -/
theorem _root_.Equiv.Perm.eq_cycleOf_iff_sameCycle {g : Equiv.Perm α}
    {c : g.cycleFactorsFinset} {x y : α}
    (hx : x ∈ g.support) (hy : y ∈ Equiv.Perm.support c):
    c = g.cycleOf x ↔ g.SameCycle y x := by
  rw [Equiv.Perm.cycle_is_cycleOf hy c.prop]
  constructor
  · intro hx'
    apply And.left
    rw [← Equiv.Perm.mem_support_cycleOf_iff]
    rw [hx', Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ← Equiv.Perm.mem_support]
    exact hx
  · intro hxy
    rw [Equiv.Perm.SameCycle.cycleOf_eq hxy]
#align on_cycle_factors.same_cycle_of_mem_support_iff Equiv.Perm.eq_cycleOf_iff_sameCycle

/-- If `x` and `y` are in the same cycle for `g`,
  `c` is a cycle of `g`, and `y` belongs to the support of `c`,
  then `c` is the cycle of `x` for `g`. -/
theorem _root_.Equiv.Perm.SameCycle.eq_cycleOf
    {g : Equiv.Perm α} (c : g.cycleFactorsFinset) {x y}
    (hx : g.SameCycle y x) (hy : y ∈ Equiv.Perm.support c):
    c = g.cycleOf x := by
  rw [Equiv.Perm.cycle_is_cycleOf hy c.prop, Equiv.Perm.SameCycle.cycleOf_eq hx]
#align on_cycle_factors.same_cycle.is_cycle_of Equiv.Perm.SameCycle.eq_cycleOf

theorem _root_.Equiv.Perm.sameCycle_of_mem_support
    {g : Equiv.Perm α} {x : α} (hx : x ∈ g.support) :
    ∃ c : g.cycleFactorsFinset, ∀ y ∈ Equiv.Perm.support c, g.SameCycle y x := by
  use ⟨g.cycleOf x, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx⟩
  intro y hy
  rw [← Equiv.Perm.eq_cycleOf_iff_sameCycle hx hy]
#align on_cycle_factors.same_cycle_of_mem_support Equiv.Perm.sameCycle_of_mem_support

theorem Equiv.Perm.subtypePerm_apply_pow_of_mem (g : Equiv.Perm α) (s : Finset α)
    (hs : ∀ x : α, x ∈ s ↔ g x ∈ s) (n : ℕ) (x : α) (hx : x ∈ s) :
    ((g.subtypePerm hs ^ n) (⟨x, hx⟩ : s) : α) = (g ^ n) x := by
  revert x
  induction' n with n hrec
  · -- zero case
    intro x hx
    simp only [pow_zero, Equiv.Perm.coe_one, id.def, Subtype.coe_mk]
  · -- induction case
    intro x hx
    simp only [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]
    apply hrec
#align equiv.perm.subtype_perm_apply_pow_of_mem Equiv.Perm.subtypePerm_apply_pow_of_mem

theorem Equiv.Perm.subtypePerm_apply_zpow_of_mem (g : Equiv.Perm α) (s : Finset α)
    (hs : ∀ x : α, x ∈ s ↔ g x ∈ s) (i : ℤ) (x : α) (hx : x ∈ s) :
    ((g.subtypePerm hs ^ i) (⟨x, hx⟩ : s) : α) = (g ^ i) x := by
  induction' i with i i
  -- nat case
  apply Equiv.Perm.subtypePerm_apply_pow_of_mem
  -- neg_succ case
  simp only [zpow_negSucc]
  apply Equiv.injective (g ^ (i + 1))
  simp only [Equiv.Perm.apply_inv_self]
  rw [← Equiv.Perm.subtypePerm_apply_pow_of_mem g s hs]
  rw [Finset.mk_coe, Equiv.Perm.apply_inv_self, Subtype.coe_mk]
  apply Finset.coe_mem
#align equiv.perm.subtype_perm_apply_zpow_of_mem Equiv.Perm.subtypePerm_apply_zpow_of_mem

/-- The support of a permutation is invariant -/
theorem Equiv.Perm.isInvariant_of_support_le {c : Equiv.Perm α} {s : Finset α}
    (hcs : c.support ≤ s) (x : α) : x ∈ s ↔ c x ∈ s := by
  by_cases hx' : x ∈ c.support
  · simp only [hcs hx', true_iff_iff]
    exact hcs (Equiv.Perm.apply_mem_support.mpr hx')
  rw [Equiv.Perm.not_mem_support.mp hx']
#align equiv.perm.le_support_is_invariant Equiv.Perm.isInvariant_of_support_le

/-- Restrict a permutation to its support -/
def Equiv.Perm.subtypePermOfSupport (c : Equiv.Perm α) : Equiv.Perm c.support :=
  Equiv.Perm.subtypePerm c fun _ : α => Equiv.Perm.apply_mem_support.symm
#align equiv.perm.subtype_perm_of_support Equiv.Perm.subtypePermOfSupport

/-- Restrict a permutation to a Finset containing its support -/
def Equiv.Perm.subtypePerm_of_support_le (c : Equiv.Perm α) (s : Finset α)
    (hcs : c.support ≤ s) : Equiv.Perm s :=
  Equiv.Perm.subtypePerm c (Equiv.Perm.isInvariant_of_support_le hcs)
#align equiv.perm.subtype_perm_of_support_le Equiv.Perm.subtypePerm_of_support_le

/-- Support of a cycle is nonempty -/
theorem Equiv.Perm.IsCycle.nonempty_support {g : Equiv.Perm α} (hg : g.IsCycle) :
    g.support.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, Ne.def, Equiv.Perm.support_eq_empty_iff]
  exact Equiv.Perm.IsCycle.ne_one hg
#align equiv.perm.support_of_cycle_nonempty Equiv.Perm.IsCycle.nonempty_support

/-- Centralizer of a cycle is a power of that cycle on the cycle -/
theorem Equiv.Perm.IsCycle.commute_iff' {g c : Equiv.Perm α} (hc : c.IsCycle) :
    Commute g c ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ g x ∈ c.support,
        Equiv.Perm.subtypePerm g hc' ∈ Subgroup.zpowers c.subtypePermOfSupport := by
  constructor
  · intro hgc
    let hgc' := Equiv.Perm.mem_support_of_commute hgc
    use hgc'
    obtain ⟨a, ha⟩ := Equiv.Perm.IsCycle.nonempty_support hc
    suffices : c.SameCycle a (g a)
    simp only [Equiv.Perm.SameCycle] at this
    obtain ⟨i, hi⟩ := this; use i
    ext ⟨x, hx⟩
    simp only [Equiv.Perm.subtypePermOfSupport, Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
    rw [Equiv.Perm.subtypePerm_apply_zpow_of_mem]
    suffices c.SameCycle a x by
      obtain ⟨j, rfl⟩ := this
      · simp only [← Equiv.Perm.mul_apply, Commute.eq (Commute.zpow_right hgc j)]
        rw [← zpow_add, add_comm i j, zpow_add]
        simp only [Equiv.Perm.mul_apply]
        simp only [EmbeddingLike.apply_eq_iff_eq]
        exact hi
    -- c.same_cycle a x,
    exact hc.sameCycle (mem_support.mp ha) (mem_support.mp hx)
    -- c.same_cycle a (g a),
    apply hc.sameCycle (mem_support.mp ha) (mem_support.mp ((hgc' a).mp ha))
  · -- converse
    rintro ⟨hc', h⟩
    obtain ⟨i, hi⟩ := h
    suffices hi' : ∀ x ∈ c.support, g x = (c ^ i) x
    · ext x
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      by_cases hx : x ∈ c.support
      · -- hx : x ∈ c.support
        rw [hi' x hx]
        rw [hi' (c x) (apply_mem_support.mpr hx)]
        simp only [← Equiv.Perm.mul_apply, ← zpow_add_one, ← zpow_one_add]
        rw [Int.add_comm 1 i]
      · -- hx : x ∉ c.support
        rw [not_mem_support.mp hx]; apply symm
        rw [← Equiv.Perm.not_mem_support]
        intro hx'; apply hx
        exact (hc' x).mpr hx'
    · -- proof of hi'
      intro x hx
      let hix := Equiv.Perm.congr_fun hi ⟨x, hx⟩
      simp only [← Subtype.coe_inj, Equiv.Perm.subtypePermOfSupport] at hix
      simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply,
        Equiv.Perm.subtypePerm_apply_zpow_of_mem] at hix
      exact hix.symm
#align equiv.perm.centralizer_of_cycle_on' Equiv.Perm.IsCycle.commute_iff'

lemma Equiv.Perm.ofSubtype_eq_iff {g c : Equiv.Perm α} {s : Finset α}
    (hg : ∀ x, x ∈ s ↔  g x ∈ s) :
    Equiv.Perm.ofSubtype (g.subtypePerm hg) = c ↔
      c.support ≤ s ∧
      ∀ (hc' : ∀ x, x ∈ s ↔ c x ∈ s), c.subtypePerm hc' = g.subtypePerm hg := by
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  constructor
  · intro h
    suffices hc : support c ≤ s
    use hc
    intro _ a ha
    rw [← h a, ofSubtype_apply_of_mem]
    rfl
    exact ha
    · intro a ha
      by_contra ha'
      rw [Equiv.Perm.mem_support, ← h a, ofSubtype_apply_of_not_mem] at ha
      exact ha rfl
      exact ha'
  · rintro ⟨hc, h⟩ a
    specialize h (isInvariant_of_support_le hc)
    by_cases ha : a ∈ s
    · rw [h a ha, ofSubtype_apply_of_mem]
      rfl
      exact ha
    · rw [ofSubtype_apply_of_not_mem]
      apply symm
      rw [← Equiv.Perm.not_mem_support]
      intro ha'
      exact ha (hc ha')
      exact ha

theorem Equiv.Perm.zpow_eq_ofSubtype_subtypePerm_iff
    {g c : Equiv.Perm α} {s : Finset α}
    (hg : ∀ x, x ∈ s ↔ g x ∈ s) (hc : c.support ⊆ s) (n : ℤ) :
    c ^ n = Equiv.Perm.ofSubtype (g.subtypePerm hg) ↔
      c.subtypePerm (Equiv.Perm.isInvariant_of_support_le hc) ^ n = g.subtypePerm hg := by
  constructor
  · intro h; ext ⟨x, hx⟩; let h' := Equiv.Perm.congr_fun h x
    simp only [h', Equiv.Perm.subtypePerm_apply_zpow_of_mem, Subtype.coe_mk,
      Equiv.Perm.subtypePerm_apply]
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
    exact hx
  · intro h; ext x
    rw [← h]
    by_cases hx : x ∈ s
    · rw [Equiv.Perm.ofSubtype_apply_of_mem]
      simp only [subtypePerm_zpow, subtypePerm_apply]
      exact hx
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
      rw [← Equiv.Perm.not_mem_support]
      intro hx'
      apply hx
      apply hc; apply Equiv.Perm.support_zpow_le; exact hx'
      exact hx
#align equiv.perm.zpow_eq_of_subtype_subtype_perm_iff Equiv.Perm.zpow_eq_ofSubtype_subtypePerm_iff

/-- A permutation `g` commutes with a cycle `c` if and only if
  `c.support` is invariant under `g`, and `g` acts on it as a power of `c`. -/
theorem Equiv.Perm.IsCycle.commute_iff {g c : Equiv.Perm α} (hc : c.IsCycle) :
    Commute g c ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ g x ∈ c.support,
        Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm g hc') ∈ Subgroup.zpowers c := by
  rw [Equiv.Perm.IsCycle.commute_iff' hc]
  apply exists_congr
  intro hc'
  simp only [Subgroup.mem_zpowers_iff]
  apply exists_congr
  intro k
  unfold subtypePermOfSupport
  rw [Equiv.Perm.subtypePerm_zpow]
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  apply forall_congr'
  intro a
  by_cases ha : a ∈ c.support
  · rw [imp_iff_right ha]
    apply Eq.congr rfl
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    rfl
    exact ha
  · rw [iff_true_left _]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    rw [← Equiv.Perm.not_mem_support]
    intro ha'; apply ha
    apply Equiv.Perm.support_zpow_le
    exact ha'
    exact ha
    exact fun b => False.elim (ha b)

theorem Equiv.Perm.IsCycle.forall_commute_iff (g z : Equiv.Perm α) :
    (∀ c ∈ g.cycleFactorsFinset, Commute z c) ↔
      ∀ c ∈ g.cycleFactorsFinset,
      ∃ (hc : ∀ x : α, x ∈ c.support ↔ z x ∈ c.support),
        Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm z hc) ∈ Subgroup.zpowers c := by
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  exact Equiv.Perm.IsCycle.commute_iff (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1

/-- A permutation restricted to the support of a cycle factor is that cycle factor -/
theorem Equiv.Perm.subtypePerm_on_cycleFactorsFinset {g c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) :
    g.subtypePerm (Equiv.Perm.mem_cycleFactorsFinset_support hc) =
      c.subtypePermOfSupport := by
  ext ⟨x, hx⟩
  simp only [subtypePerm_apply, Subtype.coe_mk, subtypePermOfSupport]
  exact ((mem_cycleFactorsFinset_iff.mp hc).2 x hx).symm
#align equiv.perm.subtype_perm_on_cycle_factor Equiv.Perm.subtypePerm_on_cycleFactorsFinset

theorem Equiv.Perm.commute_of_mem_cycleFactorsFinset_iff {g k c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) :
    Commute k c ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ k x ∈ c.support,
        k.subtypePerm hc' ∈ Subgroup.zpowers
          (g.subtypePerm (mem_cycleFactorsFinset_support hc)) := by
  rw [Equiv.Perm.IsCycle.commute_iff' (mem_cycleFactorsFinset_iff.mp hc).1]
  apply exists_congr
  intro hc'
  simp only [Subgroup.mem_zpowers_iff]
  apply exists_congr
  intro n
  unfold subtypePermOfSupport
  rw [Equiv.Perm.subtypePerm_on_cycleFactorsFinset hc]
  rfl
#align equiv.perm.centralizer_mem_cycle_factors_iff'
  Equiv.Perm.commute_of_mem_cycleFactorsFinset_iff

theorem Equiv.Perm.zpow_mod_card_support_cycleOf_self_apply [Fintype α]
    (f : Equiv.Perm α) (n : ℤ) (x : α) :
    (f ^ (n % ((Equiv.Perm.cycleOf f x).support.card) : ℤ) : Equiv.Perm α) x =
      (f ^ n) x := by
  by_cases hx : f x = x
  · rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx,
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx]
  · rw [← f.cycleOf_zpow_apply_self, ← f.cycleOf_zpow_apply_self,
      ← (f.isCycle_cycleOf hx).orderOf, zpow_mod_orderOf]
#align equiv.perm.zpow_mod_card_support_cycle_of_self_apply
  Equiv.Perm.zpow_mod_card_support_cycleOf_self_apply

theorem Equiv.Perm.cycle_zpow_mem_support_iff {g : Equiv.Perm α}
    (hg : g.IsCycle) {n : ℤ} {x : α} (hx : g x ≠ x) :
    (g ^ n) x = x ↔ n % g.support.card = 0 := by
  let q := n / g.support.card; let r := n % g.support.card
  change _ ↔ r = 0
  have div_euc : r + g.support.card * q = n ∧ 0 ≤ r ∧ r < g.support.card := by
    rw [← Int.ediv_emod_unique _]
    constructor; rfl; rfl
    simp only [Int.coe_nat_pos]
    apply lt_of_lt_of_le _ (Equiv.Perm.IsCycle.two_le_card_support hg); norm_num
  simp only [← hg.orderOf] at div_euc
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le div_euc.2.1
  simp only [hm, Nat.cast_nonneg, Nat.cast_lt, true_and_iff] at div_euc
  simp only [hm, Nat.cast_eq_zero]
  rw [← div_euc.1, zpow_add g, zpow_mul, zpow_ofNat]
  simp only [pow_orderOf_eq_one, zpow_ofNat, one_zpow, mul_one]
  have : (g ^ m) x = x ↔ g ^ m = 1 := by
    constructor
    · intro hgm
      simp [Equiv.Perm.IsCycle.pow_eq_one_iff hg]
      use x
    · intro hgm; rw [hgm]; simp only [Equiv.Perm.coe_one, id.def]
  rw [this, div_euc.1, ← hg.orderOf, hm]
  cases' dec_em (m = 0) with hm0 hm0'
  · simp only [hm0, pow_zero, Nat.cast_zero]
  · simp only [Nat.cast_eq_zero, hm0', iff_false]
    exact pow_ne_one_of_lt_orderOf' hm0' div_euc.2
#align equiv.perm.cycle_zpow_mem_support_iff Equiv.Perm.cycle_zpow_mem_support_iff


theorem Equiv.Perm.zpow_eq_zpow_on_iff (g : Equiv.Perm α)
    (m n : ℤ) (x : α) (hx : g x ≠ x) :
    (g ^ m) x = (g ^ n) x ↔
      m % (g.cycleOf x).support.card = n % (g.cycleOf x).support.card := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  conv_lhs => rw [← Int.sub_add_cancel m n, Int.add_comm, zpow_add]
  simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq,
    EuclideanDomain.mod_eq_zero]
  rw [← Equiv.Perm.cycleOf_zpow_apply_self g x]
  rw [Equiv.Perm.cycle_zpow_mem_support_iff]
  · simp only [EuclideanDomain.mod_eq_zero]
  · exact Equiv.Perm.isCycle_cycleOf g hx
  · simp only [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]; exact hx
#align equiv.perm.zpow_eq_zpow_on_iff Equiv.Perm.zpow_eq_zpow_on_iff

instance MulAction.decidableMemFixedBy {α β : Type _}
    [Monoid α] [DecidableEq β] [MulAction α β] (a : α) :
    DecidablePred fun b : β => b ∈ MulAction.fixedBy β a := by
  intro b
  simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
  infer_instance
#align mul_action.decidable_mem_fixed_by MulAction.decidableMemFixedBy

instance MulAction.decidableMemStabilizer {α β : Type _}
    [Group α] [DecidableEq β] [MulAction α β] (b : β) :
    DecidablePred fun g : α => g ∈ MulAction.stabilizer α b := by
  intro g
  simp only [mem_stabilizer_iff]
  infer_instance
#align mul_action.decidable_mem_stabilizer MulAction.decidableMemStabilizer

/-- The `toFun` map of the description of the centralizer of `g : Equiv.Perm α` -/
def Equiv.permConjStabilizerFun (g : Equiv.Perm α) :
    (Equiv.Perm (MulAction.fixedBy α g) ×
        ∀ c ∈ g.cycleFactorsFinset, Subgroup.zpowers (c : Equiv.Perm α)) →
      Equiv.Perm α :=
  fun uv : Equiv.Perm (MulAction.fixedBy α g) ×
      ∀ c ∈ g.cycleFactorsFinset, Subgroup.zpowers (c : Equiv.Perm α) =>
  Equiv.Perm.ofSubtype uv.fst *
    Finset.noncommProd g.cycleFactorsFinset
      (fun c => dite (c ∈ g.cycleFactorsFinset) (fun hc => uv.snd c hc) fun hc => 1)
      fun c hc d hd h => by
      simp only [Finset.mem_coe] at hc hd
      simp only [dif_pos hd, dif_pos hc]
      obtain ⟨m, hc'⟩ := Subgroup.mem_zpowers_iff.mp (uv.snd c hc).prop
      obtain ⟨n, hd'⟩ := Subgroup.mem_zpowers_iff.mp (uv.snd d hd).prop
      rw [← hc', ← hd']
      apply Commute.zpow_zpow
      exact g.cycleFactorsFinset_mem_commute hc hd h
#align equiv.perm_conj_stabilizer_fun Equiv.permConjStabilizerFun

theorem commute_ofSubtype_disjoint {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ a, ¬(p a ∧ q a)) (x : Equiv.Perm (Subtype p)) (y : Equiv.Perm (Subtype q)) :
    Commute (Equiv.Perm.ofSubtype x) (Equiv.Perm.ofSubtype y) := by
  apply Equiv.Perm.Disjoint.commute
  intro a
  by_cases hx : p a
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem y]
    apply Or.intro_right; rfl
    exact not_and.mp (hpq a) hx
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem x hx]
    apply Or.intro_left; rfl
#align commute_of_subtype_disjoint commute_ofSubtype_disjoint

end CycleTypes

namespace Equiv.Perm

variable {α : Type _} [DecidableEq α] [Fintype α] (g : Equiv.Perm α)

namespace OnCycleFactors

/-- The action by conjugation of `ConjAct (Equiv.Perm α)`
  on the cycles of a given permutation -/
def subMulAction : SubMulAction
    (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) (Equiv.Perm α) where
  carrier := (g.cycleFactorsFinset : Set (Equiv.Perm α))
  smul_mem' k c hc := by
    have := Equiv.Perm.cycleFactorsFinset_conj_eq (↑k) g
    rw [MulAction.mem_stabilizer_iff.mp k.prop] at this
    rw [this, Finset.coe_smul_finset]
    exact ⟨c, hc, rfl⟩
#align on_cycle_factors.sub_mul_action_on_cycle_factors Equiv.Perm.OnCycleFactors.subMulAction

/-- The conjugation action of `MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  on the cycles of a given permutation -/
instance mulAction :
    MulAction (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
      (g.cycleFactorsFinset : Set (Equiv.Perm α)) :=
  (subMulAction g).mulAction
#align on_cycle_factors.mul_action_on_cycle_factors Equiv.Perm.OnCycleFactors.mulAction

/-- The canonical morphism from `MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  to the group of permutations of `g.cycleFactorsFinset` -/
def φ := MulAction.toPermHom (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
    (g.cycleFactorsFinset : Set (Equiv.Perm α))
#align on_cycle_factors.φ Equiv.Perm.OnCycleFactors.φ

theorem φ_eq (k : ConjAct (Equiv.Perm α))
    (hk : k ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
    (c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset) :
    (φ g ⟨k, hk⟩ ⟨c, hc⟩ : Equiv.Perm α) = k • c := rfl
#align on_cycle_factors.φ_eq Equiv.Perm.OnCycleFactors.φ_eq

theorem φ_eq' (k : Equiv.Perm α)
    (hk : k ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
    (c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset) :
    (φ g ⟨ConjAct.toConjAct k, hk⟩ ⟨c, hc⟩ : Equiv.Perm α) = k * c * k⁻¹ :=  rfl
#align on_cycle_factors.φ_eq' Equiv.Perm.OnCycleFactors.φ_eq'

theorem φ_eq'2 (k : MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
    (c : g.cycleFactorsFinset) :
    (φ g k c : Equiv.Perm α) = ConjAct.ofConjAct (k : ConjAct (Equiv.Perm α)) *
      (c : Equiv.Perm α) * (ConjAct.ofConjAct (k : ConjAct (Equiv.Perm α))) ⁻¹ :=  rfl

variable {g}

/-- A `Basis` of a permutation is a choice of an element in each of its cycles -/
class _root_.Equiv.Perm.Basis (g : Equiv.Perm α) where
  /-- A choice of elements in each cycle -/
  (toFun : g.cycleFactorsFinset → α)
  /-- For each cycle, the chosen element belongs to the cycle -/
  (mem_support : ∀ c, toFun c ∈ (c : Equiv.Perm α).support)

/-- A `Basis` of a permutation is a choice of an element in each of its cycles -/
def _root_.Equiv.Perm.Basis' (g : Equiv.Perm α) :=
  Π (c : g.cycleFactorsFinset), (c : Equiv.Perm α).support

instance (g : Equiv.Perm α) :
  FunLike (Equiv.Perm.Basis g) (g.cycleFactorsFinset) (fun _ => α) := {
  coe := fun a => a.toFun
  coe_injective' := by
    intro a a' _
    cases a; cases a'; congr }

theorem _root_.Equiv.Perm.existsBasis (g : Equiv.Perm α) :
    Nonempty (Equiv.Perm.Basis g) := by
  suffices hsupp_ne :
    ∀ c : g.cycleFactorsFinset, (c : Equiv.Perm α).support.Nonempty
  exact ⟨fun c ↦ (hsupp_ne c).choose, fun c ↦ (hsupp_ne c).choose_spec⟩
  · intro c
    exact Equiv.Perm.IsCycle.nonempty_support
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.prop).1
#align on_cycle_factors.exists_base_points Equiv.Perm.existsBasis

-- delete?
theorem _root_.Equiv.Perm.Basis.mem_support'
    (a : Equiv.Perm.Basis g) (c : g.cycleFactorsFinset) :
    a c ∈ Equiv.Perm.support g :=
  Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop (a.mem_support c)
#align on_cycle_factors.ha'2 Equiv.Perm.Basis.mem_support

theorem _root_.Equiv.Perm.Basis.cycleOf_eq
    (a : Equiv.Perm.Basis g) (c : g.cycleFactorsFinset) :
    g.cycleOf (a c) = c :=
  (Equiv.Perm.cycle_is_cycleOf (a.mem_support c) c.prop).symm

/-- Given a basis `a` of `g`, this is the basic function that allows
  to define the inverse of `Equiv.Perm.OnCycleFactors.φ` :
  `Kf a e ⟨c, i⟩ = (g ^ i) (a (e c))` -/
def Kf (a : Equiv.Perm.Basis g) :
    Equiv.Perm g.cycleFactorsFinset → g.cycleFactorsFinset × ℤ → α :=
  fun e ⟨c, i⟩ => (g ^ i) (a (e c))
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.Kf Equiv.Perm.OnCycleFactors.Kf

/- -- This version would have been simpler, but doesn't work later
 -- because of the use of Function.extend which requires functions
 -- with *one* argument.
def Kf (a : Equiv.Perm.Basis g) (e : Equiv.Perm g.cycleFactorsFinset)
  (c : g.cycleFactorsFinset) (i : ℤ) : α :=
  (g ^ i) (a (e c))
-/
theorem Kf_def (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} {i : ℤ} :
    Kf a e ⟨c, i⟩ = (g ^ i) (a (e c)) :=
  rfl
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.Kf_apply Equiv.Perm.OnCycleFactors.Kf_def

theorem Kf_def_zero (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} :
    Kf a e ⟨c, 0⟩ = a (e c) :=
  rfl

theorem Kf_def_one (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} :
    Kf a e ⟨c, 1⟩ = g (a (e c)) :=
  rfl

/-- The multiplicative-additive property of `Equiv.Perm.OnCycleFactors.Kf` -/
theorem Kf_mul_add  (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset}
    {e e' : Equiv.Perm g.cycleFactorsFinset} {i j : ℤ} :
    Kf a (e' * e) ⟨c, i + j⟩ = (g ^ i) (Kf a e' ⟨e c, j⟩) := by
  simp only [Kf_def, zpow_add, Equiv.Perm.coe_mul, Function.comp_apply]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.Kf_apply' Equiv.Perm.OnCycleFactors.Kf_mul_add

/-- The additive property of `Equiv.Perm.OnCycleFactors.Kf` -/
theorem Kf_add  (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset}
    {e : Equiv.Perm g.cycleFactorsFinset} {i j : ℤ} :
    Kf a e ⟨c, i + j⟩ = (g ^ i) (Kf a 1 ⟨e c, j⟩) := by
  rw [← Kf_mul_add, one_mul]

/-- The additive property of `Equiv.Perm.OnCycleFactors.Kf` -/
theorem Kf_add'  (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset}
    {e : Equiv.Perm g.cycleFactorsFinset} {i j : ℤ} :
    Kf a e ⟨c, i + j⟩ = (g ^ i) (Kf a e ⟨c, j⟩) := by
  rw [← mul_one e, Kf_mul_add, mul_one]
  rfl

-- was ha''
-- DELETE?
theorem _root_.Equiv.Perm.Basis.eq_cycleOf (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset} {i : ℤ} :
    c = g.cycleOf ((g ^ i) (a c)) := by
  rw [Equiv.Perm.cycleOf_self_apply_zpow]
    -- ← Equiv.Perm.cycle_is_cycleOf (a.mem_support c) c.prop]
  rw [a.cycleOf_eq]
#align on_cycle_factors.ha'3 Equiv.Perm.Basis.eq_cycleOf

theorem _root_.Equiv.Perm.Basis.eq_cycleOf' (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset} {e : Equiv.Perm g.cycleFactorsFinset} {i : ℤ} :
    e c = g.cycleOf (Kf a e ⟨c, i⟩) := by
  rw [Kf_def, Equiv.Perm.cycleOf_self_apply_zpow, a.cycleOf_eq]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.haK1 Equiv.Perm.Basis.eq_cycleOf'

theorem _root_.Equiv.Perm.Basis.Kf_apply (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} {i : ℤ} :
    g (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i + 1⟩ := by
  rw [Kf_def, Kf_def, ← Equiv.Perm.mul_apply, ← zpow_one_add, add_comm 1 i]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.haK2 Equiv.Perm.Basis.Kf_apply

theorem _root_.Equiv.Perm.Basis.Kf_apply' (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c d : g.cycleFactorsFinset} {i : ℤ}
    (hd : d = e c) :
    (d : Equiv.Perm α) (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i + 1⟩ := by
  -- Kf e ⟨c, i⟩ = (g ^ i) (a (e c)) appartient au cycle de e c
  rw [hd]
  change (e c : Equiv.Perm α) _ = _
  rw [Equiv.Perm.Basis.eq_cycleOf', Equiv.Perm.cycleOf_apply_self,
    Equiv.Perm.Basis.Kf_apply]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.haK3 Equiv.Perm.Basis.Kf_apply'

theorem _root_.Equiv.Perm.Basis.Kf_apply'' (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c d : g.cycleFactorsFinset} {i : ℤ}
    (hd' : d ≠ e c) :
    (d : Equiv.Perm α) (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i⟩ := by
  suffices hdc : (d : Equiv.Perm α).Disjoint (e c : Equiv.Perm α)
  apply Or.resolve_right (Equiv.Perm.disjoint_iff_eq_or_eq.mp hdc (Kf a e ⟨c, i⟩))
  rw [Equiv.Perm.Basis.eq_cycleOf', Equiv.Perm.cycleOf_apply_self,
    ← Equiv.Perm.cycleOf_eq_one_iff, ← Equiv.Perm.Basis.eq_cycleOf']
  apply Equiv.Perm.IsCycle.ne_one
  refine' (Equiv.Perm.mem_cycleFactorsFinset_iff.mp _).1
  exact g
  exact (e c).prop
  apply g.cycleFactorsFinset_pairwise_disjoint d.prop (e c).prop
  rw [Function.Injective.ne_iff Subtype.coe_injective]
  exact hd'
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.haK4 Equiv.Perm.Basis.Kf_apply''

theorem _root_.Equiv.Perm.Basis.Kf_factorsThrough (a : Equiv.Perm.Basis g)
    {e e' : Equiv.Perm g.cycleFactorsFinset}
    (hee' : ∀ c : g.cycleFactorsFinset,
        (e c : Equiv.Perm α).support.card = (e' c : Equiv.Perm α).support.card) :
    (Kf a e').FactorsThrough (Kf a e) := by
  --    Kf e ci = Kf e dj → Kf e' ci = Kf e' dj,
  rintro ⟨c, i⟩ ⟨d, j⟩ He
  simp only [Kf_def] at He ⊢
  suffices hcd : c = d
  · rw [hcd] at He ⊢
    rw [g.zpow_eq_zpow_on_iff i j,
      ← Equiv.Perm.cycle_is_cycleOf (a := a (e d)) (a.mem_support _) (e d).prop] at He
    rw [g.zpow_eq_zpow_on_iff,
      ← Equiv.Perm.cycle_is_cycleOf (a := a (e' d)) (a.mem_support _) (e' d).prop, ← hee' d]
    exact He
    · rw [← Equiv.Perm.mem_support, ← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
        ← Equiv.Perm.cycle_is_cycleOf (a := a (e' d)) (a.mem_support _) (e' d).prop]
      exact (e' d).prop
    · rw [← Equiv.Perm.mem_support, ← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
        ← Equiv.Perm.cycle_is_cycleOf (a := a (e d)) (a.mem_support _) (e d).prop]
      exact (e d).prop
  · -- d = c
    apply Equiv.injective e
    rw [← Subtype.coe_inj, Equiv.Perm.Basis.eq_cycleOf, Equiv.Perm.Basis.eq_cycleOf, He]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.hkfg Equiv.Perm.Basis.Kf_factorsThrough

/-- Given a basis `a` of `g` and a permutation `τ` of `g.cycleFactorsFinset`,
  `k a τ` is a permutation that acts -/
noncomputable def k (a : Equiv.Perm.Basis g) (τ : Equiv.Perm g.cycleFactorsFinset) :=
  Function.extend (Kf a 1) (Kf a τ) id
#align on_cycle_factors.k Equiv.Perm.OnCycleFactors.k

theorem k_apply (a : Equiv.Perm.Basis g)
    (c : g.cycleFactorsFinset) (i : ℤ) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ (Kf a 1 ⟨c, i⟩) = Kf a τ ⟨c, i⟩ := by
  simp only [k]
  rw [Function.FactorsThrough.extend_apply (Equiv.Perm.Basis.Kf_factorsThrough a _) id ⟨c, i⟩]
  · intro c; simp only [← hτ c, Equiv.Perm.coe_one, id.def]
#align on_cycle_factors.k_apply Equiv.Perm.OnCycleFactors.k_apply

theorem k_apply_base (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset} {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ (a c) = a (τ c) :=
  k_apply a c 0 hτ
#align on_cycle_factors.k_apply_base Equiv.Perm.OnCycleFactors.k_apply_base

theorem k_apply_of_not_mem_support (a : Equiv.Perm.Basis g)
    {τ : Equiv.Perm g.cycleFactorsFinset} (x : α) (hx : x ∉ g.support) :
    k a τ x = x := by
  simp only [k]
  rw [Function.extend_apply']
  simp only [id.def]
  intro hyp
  obtain ⟨⟨c, i⟩, rfl⟩ := hyp
  apply hx
  rw [Kf_def, Equiv.Perm.zpow_apply_mem_support]
  apply Equiv.Perm.Basis.mem_support'
  -- exact ha'2 ha c
#align on_cycle_factors.k_apply_of_not_mem_support
  Equiv.Perm.OnCycleFactors.k_apply_of_not_mem_support

theorem mem_support_iff_exists_Kf (a : Equiv.Perm.Basis g) (x : α) :
    x ∈ g.support ↔
    ∃ (c : g.cycleFactorsFinset) (i : ℤ), x = Kf a 1 ⟨c, i⟩ := by
  constructor
  · intro hx
    rw [← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff] at hx
    use ⟨g.cycleOf x, hx⟩
    simp only [Kf_def, Equiv.Perm.coe_one, id.def]
    let ha := a.mem_support ⟨g.cycleOf x, hx⟩
    simp only [Subtype.coe_mk, Equiv.Perm.mem_support_cycleOf_iff] at ha
    obtain ⟨i, hi⟩ := ha.1.symm
    exact ⟨i, hi.symm⟩
  · rintro ⟨c, i, rfl⟩
    simp only [Kf_def, Equiv.Perm.zpow_apply_mem_support, Equiv.Perm.coe_one, id.def]
    apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop
    apply a.mem_support
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.mem_support_iff_exists_Kf
  Equiv.Perm.OnCycleFactors.mem_support_iff_exists_Kf

theorem k_commute_zpow (a : Equiv.Perm.Basis g) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) (j : ℤ) :
    k a τ ∘ (g ^ j : Equiv.Perm α) = (g ^ j : Equiv.Perm α) ∘ k a τ := by
  ext x
  simp only [Function.comp_apply]
  by_cases hx : x ∈ g.support
  · rw [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, i, rfl⟩ := hx
    rw [← Kf_add']
    rw [k_apply a c (j + i) hτ]
    rw [k_apply a c i hτ]
    rw [Kf_add']
  · rw [k_apply_of_not_mem_support a x hx]
    rw [k_apply_of_not_mem_support a ((g ^ j : Equiv.Perm α) x) _]
    rw [Equiv.Perm.zpow_apply_mem_support]
    exact hx
#align on_cycle_factors.k_commute_zpow Equiv.Perm.OnCycleFactors.k_commute_zpow

theorem k_commute (a : Equiv.Perm.Basis g) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ ∘ g = g ∘ k a τ := by
  simpa only [zpow_one] using k_commute_zpow a hτ 1
#align on_cycle_factors.k_commute Equiv.Perm.OnCycleFactors.k_commute

theorem k_apply_gen (a : Equiv.Perm.Basis g) {c : g.cycleFactorsFinset} {i : ℤ}
    {σ τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ (Kf a σ ⟨c, i⟩) = Kf a (τ * σ) ⟨c, i⟩ := by
  simp only [Kf_def]
  rw [← Function.comp_apply (f := k a τ), k_commute_zpow a hτ, Function.comp_apply]
  apply congr_arg
  dsimp
  have : ∀ (d) (τ : Equiv.Perm g.cycleFactorsFinset),
    a (τ d) = Kf a 1 (τ d, 0) :=
    fun d τ ↦ rfl
  rw [this _ σ,
    k_apply a (σ c) 0 hτ, ← Function.comp_apply (f := τ), ← Equiv.Perm.coe_mul,
    this _ (τ * σ)]
  rfl
#align on_cycle_factors.k_apply_gen Equiv.Perm.OnCycleFactors.k_apply_gen

theorem k_mul (a : Equiv.Perm.Basis g) (σ : Equiv.Perm g.cycleFactorsFinset)
    (hσ : ∀ c, (σ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card)
    (τ : Equiv.Perm g.cycleFactorsFinset)
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a σ ∘ k a τ = k a (σ * τ) := by
  ext x
  simp only [Function.comp_apply]
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, i, rfl⟩ := hx
    rw [k_apply a c i hτ, k_apply_gen _]
    rw [k_apply_gen]
    simp only [mul_one]
    · intro c
      rw [Equiv.Perm.coe_mul, Function.comp_apply, hσ, hτ]
    exact hσ
  · simp only [k_apply_of_not_mem_support a x hx]
#align on_cycle_factors.k_mul Equiv.Perm.OnCycleFactors.k_mul

theorem k_one (a : Equiv.Perm.Basis g) : k a (1 : Equiv.Perm g.cycleFactorsFinset) = id := by
  ext x
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, i, rfl⟩ := hx
    rw [k_apply]
    rfl
    intro c; rfl
  simp only [id.def, k_apply_of_not_mem_support a x hx]
#align on_cycle_factors.k_one Equiv.Perm.OnCycleFactors.k_one

theorem k_bij (a : Equiv.Perm.Basis g) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    Function.Bijective (k a τ) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine' And.intro _ rfl
  rw [Function.surjective_iff_hasRightInverse]
  use k a τ⁻¹
  rw [Function.rightInverse_iff_comp]
  rw [k_mul]; rw [mul_inv_self]; rw [k_one]
  exact hτ
  intro c; rw [← hτ (τ⁻¹ c), Equiv.Perm.apply_inv_self]
#align on_cycle_factors.k_bij Equiv.Perm.OnCycleFactors.k_bij

theorem k_cycle_apply (a : Equiv.Perm.Basis g) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card)
    (c : g.cycleFactorsFinset) (x : α) :
    k a τ ((c : Equiv.Perm α) x) = (τ c : Equiv.Perm α) (k a τ x) := by
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨d, j, rfl⟩ := hx
    by_cases hcd : c = d
    · rw [hcd, Equiv.Perm.Basis.Kf_apply',
        k_apply a d _ hτ, k_apply a d _ hτ, ← Equiv.Perm.Basis.Kf_apply']
      rfl
      simp only [Equiv.Perm.coe_one, id.def]
    · rw [Equiv.Perm.Basis.Kf_apply'' a,
        k_apply a _ _ hτ, Equiv.Perm.Basis.Kf_apply'' a]
      exact (Equiv.injective τ).ne_iff.mpr hcd
      exact hcd
  · suffices : ∀ (c : g.cycleFactorsFinset), (c : Equiv.Perm α) x = x
    simp only [this, k_apply_of_not_mem_support a x hx]
    · intro c
      rw [← Equiv.Perm.not_mem_support]
      apply Finset.not_mem_mono _ hx
      exact Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop
#align on_cycle_factors.k_cycle_apply Equiv.Perm.OnCycleFactors.k_cycle_apply

theorem hφ_eq_card_of_mem_range {τ} (hτ : τ ∈ (φ g).range) (c) :
    (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := hτ
  rw [φ_eq, ConjAct.smul_def, Equiv.Perm.support_conj]
  apply Finset.card_map
#align on_cycle_factors.hφ_eq_card_of_mem_range Equiv.Perm.OnCycleFactors.hφ_eq_card_of_mem_range

/-- Given `a : g.Basis` and a permutation of g.cycleFactorsFinset that
  preserve the lengths of the cycles, the permutation of `α` that
  moves the `Basis` and commutes with `g`
  -/
noncomputable def φ'Fun (a : Equiv.Perm.Basis g)
    {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    Equiv.Perm α :=
  Equiv.ofBijective (k a τ) (k_bij a hτ)
#align on_cycle_factors.φ'_fun Equiv.Perm.OnCycleFactors.φ'Fun

theorem φ'_mem_stabilizer (a : Equiv.Perm.Basis g)
    {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    ConjAct.toConjAct (φ'Fun a hτ) ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g := by
  rw [MulAction.mem_stabilizer_iff]
  rw [ConjAct.smul_def]
  rw [ConjAct.ofConjAct_toConjAct]
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  simp only [Equiv.Perm.coe_mul]
  simp only [φ'Fun]
  simp only [Function.comp_apply, Equiv.ofBijective_apply]
  rw [← Function.comp_apply (f := k a τ)]
  rw [k_commute a hτ]
  rfl
#align on_cycle_factors.φ'_mem_stabilizer Equiv.Perm.OnCycleFactors.φ'_mem_stabilizer

variable (g)

/-- The range of `Equiv.Perm.OnCycleFactors.φ` -/
def Iφ : Subgroup (Equiv.Perm g.cycleFactorsFinset) where
  carrier := {τ | ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Equiv.Perm.coe_one, id.def, eq_self_iff_true, imp_true_iff]
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Subtype.forall, Set.mem_setOf_eq, Equiv.Perm.coe_mul, Function.comp_apply]
    simp only [Subtype.forall, Set.mem_setOf_eq] at hσ hτ
    intro c hc
    rw [hσ, hτ]
  inv_mem' := by
    intro σ hσ
    simp only [Subtype.forall, Set.mem_setOf_eq]
    simp only [Subtype.forall, Set.mem_setOf_eq] at hσ
    intro c hc
    rw [← hσ ]
    simp only [Finset.coe_mem, Subtype.coe_eta, Equiv.Perm.apply_inv_self]
    simp only [Finset.coe_mem]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.Iφ Equiv.Perm.OnCycleFactors.Iφ

variable {g}

theorem mem_Iφ_iff {τ : Equiv.Perm g.cycleFactorsFinset} :
    τ ∈ Iφ g ↔ ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card := by
  simp only [Iφ]; rfl
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.mem_Iφ_iff Equiv.Perm.OnCycleFactors.mem_Iφ_iff

/-- Given `a : Equiv.Perm.Basis g`,
  we define a right inverse of `Equiv.Perm.OnCycleFactors.φ`, on `Iφ g` -/
noncomputable
def φ' (a : Equiv.Perm.Basis g) :
    Iφ g →* MulAction.stabilizer (ConjAct (Equiv.Perm α)) g  where
  toFun τhτ :=
    ⟨ConjAct.toConjAct (φ'Fun a (mem_Iφ_iff.mp τhτ.prop)),
      φ'_mem_stabilizer a (mem_Iφ_iff.mp τhτ.prop)⟩
  map_one' := by
    simp only [Subgroup.coe_one, Subgroup.mk_eq_one_iff, MulEquivClass.map_eq_one_iff]
    ext x
    simp only [φ'Fun, k_one, Equiv.ofBijective_apply, id_eq, Equiv.Perm.coe_one]
  map_mul' σ τ := by
    simp only [Subgroup.coe_mul, Submonoid.mk_mul_mk, Subtype.mk_eq_mk, ← ConjAct.toConjAct_mul]
    apply congr_arg
    ext x
    simp only [φ'Fun, ← k_mul _ _ σ.prop _ τ.prop,
      Equiv.ofBijective_apply, Function.comp_apply, Equiv.Perm.coe_mul]
#align on_cycle_factors.φ' Equiv.Perm.OnCycleFactors.φ'

theorem φ'_apply' (a : Equiv.Perm.Basis g) {τ} (hτ) (x) :
    (ConjAct.ofConjAct (φ' a ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α))) x = k a τ x :=
  rfl
#align on_cycle_factors.φ'_apply' Equiv.Perm.OnCycleFactors.φ'_apply'

theorem φ'_apply (a : Equiv.Perm.Basis g) (τ : Iφ g) (x) :
    ConjAct.ofConjAct (φ' a τ : ConjAct (Equiv.Perm α)) x = k a τ.val x :=
  rfl
#align on_cycle_factors.φ'_apply Equiv.Perm.OnCycleFactors.φ'_apply

theorem φ'_support_le (a : Equiv.Perm.Basis g) (τ : Iφ g) :
    (ConjAct.ofConjAct (φ' a τ : ConjAct (Equiv.Perm α))).support ≤
      g.support := by
  intro x
  simp only [Equiv.Perm.mem_support]
  intro hx' hx
  apply hx'
  rw [← Equiv.Perm.not_mem_support] at hx
  exact k_apply_of_not_mem_support a x hx

theorem hφ'_equivariant (a : Equiv.Perm.Basis g) (τ : Iφ g) (c : g.cycleFactorsFinset) :
    (φ' a τ  : ConjAct (Equiv.Perm α)) • (c : Equiv.Perm α) = τ.val c := by
  rw [ConjAct.smul_def]
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  exact k_cycle_apply a τ.prop c x

theorem hφ'_is_rightInverse (a : Equiv.Perm.Basis g) (τ : Iφ g) :
    (φ g) ((φ' a) τ) = (τ : Equiv.Perm g.cycleFactorsFinset) := by
  apply Equiv.Perm.ext
  rintro ⟨c, hc⟩
  rw [← Subtype.coe_inj]
  convert φ_eq'2 g ((φ' a τ)) ⟨c, hc⟩
  rw [eq_mul_inv_iff_mul_eq]
  ext x
  simp only [Finset.coe_sort_coe, Equiv.Perm.coe_mul, Function.comp_apply]
  apply symm
  exact (k_cycle_apply a τ.prop ⟨c, hc⟩ x)
#align on_cycle_factors.hφ'_is_right_inverse Equiv.Perm.OnCycleFactors.hφ'_is_rightInverse

theorem Iφ_eq_range : Iφ g = (φ g).range := by
  obtain ⟨a⟩ := g.existsBasis
  ext τ
  constructor
  · intro hτ
    exact ⟨(φ' a) ⟨τ, hτ⟩, hφ'_is_rightInverse a ⟨τ, hτ⟩⟩
  · rw [mem_Iφ_iff]
    exact hφ_eq_card_of_mem_range
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.Iφ_eq_range Equiv.Perm.OnCycleFactors.Iφ_eq_range

theorem hφ_mem_range_iff {τ} :
    τ ∈ (φ g).range ↔
      ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card := by
  simp only [← Iφ_eq_range, mem_Iφ_iff]
  rfl
#align on_cycle_factors.hφ_mem_range_iff Equiv.Perm.OnCycleFactors.hφ_mem_range_iff

/-
/- For the moment, we can only analyse the permutations which
  respect a fibration when there is a `Fintype` assumption on the base.
  So we have to view the lengths of the cycles
   as members of the Fintype `Fin (Fintype.card α + 1)` -/

/-- The lengths of the cycles, as a member of a Fintype -/
def fsc : g.cycleFactorsFinset → Fin (Fintype.card α + 1) :=
  fun c => ⟨(c : Equiv.Perm α).support.card,
    Nat.lt_succ_iff.mpr (c : Equiv.Perm α).support.card_le_univ⟩
#align on_cycle_factors.fsc Equiv.Perm.OnCycleFactors.fsc
-/

-- FIND A BETTER NAME
/-- The lengths of the cycles -/
abbrev fsc₀ (c : g.cycleFactorsFinset) : ℕ := (c : Equiv.Perm α).support.card

-- FIND A BETTER NAME
/-
lemma hlc (n) :
    Fintype.card {a : g.cycleFactorsFinset // fsc a = n } = g.cycleType.count ↑n := by
  rcases n with ⟨i, hi⟩
  -- Rewrite the Multiset.count as a Fintype.card
  have nd := (Finset.filter (fun a ↦ i = (Finset.card ∘ Equiv.Perm.support) a)
    (Equiv.Perm.cycleFactorsFinset g)).nodup
  rw [Equiv.Perm.cycleType_def, Fin.val_mk, Multiset.count_map, ← Finset.filter_val]
  rw [← Multiset.toFinset_card_of_nodup nd, ← Multiset.toFinset_eq nd]
  simp only [Function.comp_apply, Finset.filter_congr_decidable, ← Set.ncard_coe_Finset]
  -- Rewrite the LHS using an equiv as a Set.ncard
  let v : {x : g.cycleFactorsFinset // fsc x = ⟨i, hi⟩ } ≃
      {x : g.cycleFactorsFinset // i = (Finset.card ∘ Equiv.Perm.support) (x : Equiv.Perm α) } := by
    apply Equiv.subtypeEquiv (Equiv.Set.ofEq rfl)
    intro (a : g.cycleFactorsFinset)
    simp [fsc, eq_comm]
  rw [Fintype.card_congr v, ← Nat.card_eq_fintype_card, ← Set.coe_setOf, Set.Nat.card_coe_set_eq]
  -- Ugly hack
  change Set.ncard { x : g.cycleFactorsFinset | (x : Equiv.Perm α) ∈
    { x | i = Finset.card (Equiv.Perm.support x) } } = _
  simp only [Set.ncard_subtype]
  congr
  ext c
  simp [and_comm]
-/

lemma hlc₀ (n : ℕ) :
    Fintype.card {c : g.cycleFactorsFinset // fsc₀ c = n } = g.cycleType.count n  := by
  apply symm
  -- Rewrite the Multiset.count as a Fintype.card
  have nd := (Finset.filter (fun a ↦ n = (Finset.card ∘ Equiv.Perm.support) a)
    (Equiv.Perm.cycleFactorsFinset g)).nodup
  rw [Equiv.Perm.cycleType_def, Multiset.count_map, ← Finset.filter_val]
  rw [← Multiset.toFinset_card_of_nodup nd, ← Multiset.toFinset_eq nd]
  simp only [Function.comp_apply, Finset.filter_congr_decidable, Finset.filter_val]
  rw [← Set.ncard_coe_Finset]
  -- Rewrite the RHS using an equiv as a Set.ncard
  rw [← Nat.card_eq_fintype_card]
  change _ = Nat.card { c | fsc₀ c = n }
  rw [Set.Nat.card_coe_set_eq]
  -- Ugly hack
  change _ = Set.ncard { x : g.cycleFactorsFinset |
    (x : Equiv.Perm α) ∈ { x |  Finset.card (Equiv.Perm.support x) = n } }
  simp only [Set.ncard_subtype]
  congr
  ext c
  simp [and_comm, eq_comm]

theorem hφ_range'₀ :
    ((φ g).range : Set (Equiv.Perm (g.cycleFactorsFinset : Set (Equiv.Perm α)))) =
      {τ : Equiv.Perm g.cycleFactorsFinset | fsc₀ ∘ τ = fsc₀ } := by
  rw [← Iφ_eq_range]
  ext τ
  simp only [Finset.coe_sort_coe, Set.mem_setOf_eq, Function.funext_iff,
    Function.comp_apply, SetLike.mem_coe, mem_Iφ_iff, fsc₀]


/-
theorem hφ_range' :
    ((φ g).range : Set (Equiv.Perm (g.cycleFactorsFinset : Set (Equiv.Perm α)))) =
      {τ : Equiv.Perm g.cycleFactorsFinset | fsc ∘ τ = fsc} := by
  rw [← Iφ_eq_range]
  ext τ
  simp only [Finset.coe_sort_coe, Set.mem_setOf_eq, Function.funext_iff, Function.comp_apply]
  simp only [SetLike.mem_coe, mem_Iφ_iff]
  apply forall_congr'
  intro c
  simp only [← Function.Injective.eq_iff Fin.val_injective, fsc]
#align on_cycle_factors.hφ_range' Equiv.Perm.OnCycleFactors.hφ_range'
-/

/-
theorem hφ_range_card' :
    Nat.card (φ g).range =
      Fintype.card {k : Equiv.Perm g.cycleFactorsFinset | fsc ∘ k = fsc} := by
  simp_rw [← hφ_range', Nat.card_eq_fintype_card]
  rfl
#align on_cycle_factors.hφ_range_card' Equiv.Perm.OnCycleFactors.hφ_range_card'
-/

open BigOperators Nat

theorem hφ_range_card :
    Fintype.card (φ g).range =
      ∏ n in g.cycleType.toFinset, (g.cycleType.count n)! := by
  suffices : Fintype.card (φ g).range =
    Fintype.card { k : Equiv.Perm g.cycleFactorsFinset | fsc₀ ∘ k = fsc₀ }
  rw [this]
  simp_rw [Set.coe_setOf]
  rw [DomMulAct.stabilizer_card']
  simp_rw [hlc₀]
  apply Finset.prod_congr
  · ext n
    simp only [Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach, fsc₀, true_and,
      Subtype.exists, exists_prop, Multiset.mem_toFinset]
    simp only [cycleType_def, Function.comp_apply, Multiset.mem_map, Finset.mem_val]
  · exact fun _ _ => rfl
  · simp_rw [← hφ_range'₀]
    rfl
/-
theorem hφ_range_card :
    Fintype.card (φ g).range =
      ∏ n in g.cycleType.toFinset, (g.cycleType.count n)! := by
  -- I would like to avoid that detour through `hφ_range_card'`
  rw [← Nat.card_eq_fintype_card, hφ_range_card']
  simp_rw [Set.coe_setOf]
  rw [DomMulAct.stabilizer_card]
  simp_rw [hlc]
  rw [← Finset.prod_range fun i => (g.cycleType.count i)!]
  apply symm
  apply Finset.prod_subset_one_on_sdiff _ _ (fun _ _ ↦ rfl)
  · intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact le_trans
      (Equiv.Perm.le_card_support_of_mem_cycleType (Multiset.mem_toFinset.mp hi))
      (Finset.card_le_univ g.support)
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_range, Multiset.mem_toFinset] at hi
    rw [Multiset.count_eq_zero_of_not_mem hi.2]
    exact Nat.factorial_zero
#align on_cycle_factors.hφ_range_card Equiv.Perm.OnCycleFactors.hφ_range_card
-/

/-- A permutation `z : Equiv.Perm α` belongs to the kernel of `φ g` iff
  it commutes with each cycle of `g` -/
theorem hφ_mem_ker_iff (z : Equiv.Perm α) :
    ConjAct.toConjAct z ∈ (φ g).ker.map
      (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).subtype  ↔
        ∀ t ∈ g.cycleFactorsFinset, Commute z t := by
  constructor
  · intro hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨⟨k, hkK⟩, hk, hk'⟩ := hz
    simp only [MonoidHom.mem_ker] at hk
    intro t ht
    change z * t = t * z
    rw [← mul_inv_eq_iff_eq_mul, ← MulAut.conj_apply, ← ConjAct.ofConjAct_toConjAct z,
      ← ConjAct.smul_eq_mulAut_conj _ t, ← hk']
    simp only [Subgroup.coeSubtype, Subgroup.coe_mk]
    simp only [← φ_eq g k hkK t ht, hk]
    rfl
  · intro H
    rw [Subgroup.mem_map]
    use! ConjAct.toConjAct z
    · rw [MulAction.mem_stabilizer_iff]
      rw [ConjAct.smul_eq_mulAut_conj]
      rw [MulAut.conj_apply]
      rw [mul_inv_eq_iff_eq_mul]
      rw [ConjAct.ofConjAct_toConjAct]
      exact Equiv.Perm.commute_of_mem_cycleFactorsFinset_commute z g H
    simp only [MonoidHom.mem_ker]
    constructor
    · ext ⟨c, hc⟩
      rw [φ_eq']
      rw [H c hc]
      simp only [mul_inv_cancel_right, Equiv.Perm.coe_one, id.def, Subtype.coe_mk]
    · simp only [Subgroup.coeSubtype, Subgroup.coe_mk]
#align on_cycle_factors.hφ_mem_ker_iff Equiv.Perm.OnCycleFactors.hφ_mem_ker_iff

/- delete
lemma _root_.Finset.noncommProd_eq_one
    {α : Type*} [DecidableEq α] {β : Type*} [Monoid β]
    (s : Finset α) (f : α → β)
    (comm : Set.Pairwise ↑s fun a b => Commute (f a) (f b))
    (hf : ∀ a ∈ s, f a = 1) :
    s.noncommProd f comm = 1 := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.noncommProd_empty]
  | insert ha hs =>
      rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ ha]
      rw [hf _ (Finset.mem_insert_self _ _), one_mul]
      apply hs
      intro a ha
      exact hf _ (Finset.mem_insert_of_mem ha)
-/

lemma _root_.Equiv.Perm.cycleOf_ne_one_iff_mem (g : Equiv.Perm α) {x : α} :
    g.cycleOf x ≠ 1 ↔ g.cycleOf x ∈ g.cycleFactorsFinset := by
  rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.mem_support,
        ne_eq, Equiv.Perm.cycleOf_eq_one_iff]

/-- The direct description of the centralizer of `g` -/
def θAux (g : Equiv.Perm α) (k : Equiv.Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α))
    (x : α) : α :=
  if hx : g.cycleOf x ∈ g.cycleFactorsFinset
    then (v ⟨g.cycleOf x, hx⟩ : Equiv.Perm α) x
    else Equiv.Perm.ofSubtype k x

lemma θAux_apply_of_not_mem_cycleFactorsFinset {k} {v} {x}
    (hx : g.cycleOf x ∉ g.cycleFactorsFinset) :
    θAux g k v x = Equiv.Perm.ofSubtype k x := by
  rw [θAux, dif_neg hx]

lemma θAux_apply_of_mem_fixedPoints {k} {v} {x}
    (hx : x ∈ Function.fixedPoints g) :
    θAux g k v x = Equiv.Perm.ofSubtype k x := by
  rw [θAux, dif_neg]
  rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.not_mem_support]
  exact hx

lemma θAux_apply_of_mem_fixedPoints_mem {k} {v} {x}
    (hx : x ∈ Function.fixedPoints g) :
    θAux g k v x ∈ Function.fixedPoints g := by
  rw [θAux_apply_of_mem_fixedPoints hx, Equiv.Perm.ofSubtype_apply_of_mem k hx]
  exact (k _).prop

lemma θAux_apply_of_cycleOf_eq {k} {v} {x} (c : g.cycleFactorsFinset)
    (hx : g.cycleOf x = ↑c) : θAux g k v x = (v c : Equiv.Perm α) x := by
  suffices : c = ⟨g.cycleOf x, ?_⟩
  rw [this, θAux, dif_pos]
  rw [hx]; exact c.prop
  simp only [← Subtype.coe_inj, hx]

lemma θAux_apply_of_cycleOf_eq_mem {k} {v} {x} (c : g.cycleFactorsFinset)
    (hx : g.cycleOf x = ↑c) :
    g.cycleOf (θAux g k v x) = ↑c := by
  rw [θAux_apply_of_cycleOf_eq c hx]
  obtain ⟨m, hm⟩ := (v c).prop
  dsimp only at hm
  rw [← hm, ← hx]
  simp only [Equiv.Perm.cycleOf_zpow_apply_self, Equiv.Perm.cycleOf_self_apply_zpow]

lemma θAux_cycleOf_apply_eq {k} {v} {x} :
    g.cycleOf (θAux g k v x) = g.cycleOf x := by
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ rfl]
    obtain ⟨m, hm⟩ := (v _).prop
    dsimp only at hm
    rw [← hm]
    simp only [Equiv.Perm.cycleOf_zpow_apply_self, Equiv.Perm.cycleOf_self_apply_zpow]
  · rw [g.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.not_mem_support] at hx
    rw [g.cycleOf_eq_one_iff.mpr hx, g.cycleOf_eq_one_iff,
      ← Function.mem_fixedPoints_iff]
    apply θAux_apply_of_mem_fixedPoints_mem
    exact hx

lemma θAux_one (x : α) :
    θAux g 1 1 x = x := by
  unfold θAux
  split_ifs
  · simp only [Pi.one_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
  · simp only [map_one, Equiv.Perm.coe_one, id_eq]

lemma θAux_mul
    (k' : Equiv.Perm (Function.fixedPoints g))
    (v' : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α))
    (k : Equiv.Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α))
    (x : α) :
    (θAux g k' v') (θAux g k v x) =
      θAux g (k' * k : Equiv.Perm (Function.fixedPoints g))
        (v' * v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) x := by
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ (θAux_apply_of_cycleOf_eq_mem ⟨_, hx⟩ rfl),
      θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ rfl,
      θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ rfl]
    · simp only [ne_eq, Pi.mul_apply, Submonoid.coe_mul,
        Subgroup.coe_toSubmonoid, Equiv.Perm.coe_mul, Function.comp_apply]
  · have hx' : g.cycleOf (θAux g k v x) ∉ g.cycleFactorsFinset
    · rw [θAux_cycleOf_apply_eq]
      exact hx
    nth_rewrite 1 [θAux, dif_neg hx']
    simp only [θAux, dif_neg hx]
    simp only [map_mul, Equiv.Perm.coe_mul, Function.comp_apply]

lemma θAux_inv (k) (v) :
    Function.LeftInverse (θAux g k⁻¹ v⁻¹) (θAux g k v) := by
  intro x
  rw [θAux_mul]
  simp only [mul_left_inv, θAux_one]

/-- Given a permutation `g`, a permutation of its fixed points
  and a family of elements in the powers of the cycles of `g`,
  construct their product -/
def θFun (g : Equiv.Perm α)
    (k : Equiv.Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) :
    Equiv.Perm α := {
  toFun := θAux g k v
  invFun := θAux g k⁻¹ v⁻¹
  left_inv := θAux_inv k v
  right_inv := θAux_inv k⁻¹ v⁻¹ }

/-- The description of the kernel of `Equiv.Perm.OnCycleFactors.φ g` -/
def θ (g : Equiv.Perm α) : Equiv.Perm (Function.fixedPoints g) ×
    ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) →* Equiv.Perm α := {
  toFun     := fun kv ↦ θFun g kv.fst kv.snd
  map_one'  := by
    ext x
    simp only [θFun, Prod.fst_one, Prod.snd_one, Equiv.Perm.coe_one, id_eq,
      inv_one, Equiv.coe_fn_mk, θAux_one]
  map_mul'  := fun kv' kv ↦ by
    ext x
    simp only [θFun, Equiv.coe_fn_mk, Prod.fst_mul, Prod.snd_mul,
      Equiv.Perm.coe_mul, Equiv.coe_fn_mk, Function.comp_apply, θAux_mul] }
#align on_cycle_factors.ψ Equiv.Perm.OnCycleFactors.θ

theorem hθ_1 (uv) (x : α) (hx : x ∈ Function.fixedPoints g) :
    θ g uv x = uv.fst ⟨x, hx⟩ := by
  unfold θ; unfold θFun
  simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk]
  rw [θAux_apply_of_mem_fixedPoints, Equiv.Perm.ofSubtype_apply_of_mem]
  exact hx

theorem hθ_2 (uv) (x : α) (c : g.cycleFactorsFinset)  (hx :g.cycleOf x = ↑c) :
    θ g uv x = (uv.snd c : Equiv.Perm α) x := by
  unfold θ; unfold θFun
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk]
  exact θAux_apply_of_cycleOf_eq c hx

theorem hθ_single (c : g.cycleFactorsFinset) :
    θ g ⟨1, (Pi.mulSingle c ⟨c, Subgroup.mem_zpowers (c : Equiv.Perm α)⟩)⟩ = c  := by
  ext x
  by_cases hx : x ∈ Function.fixedPoints g
  · simp only [hθ_1 _ x hx, Equiv.Perm.coe_one, id_eq]
    apply symm
    rw [← Equiv.Perm.not_mem_support]
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, ← Equiv.Perm.not_mem_support] at hx
    intro hx'
    apply hx
    apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop hx'
  suffices hx' : g.cycleOf x ∈ g.cycleFactorsFinset
  rw [hθ_2 _ x ⟨g.cycleOf x, hx'⟩ rfl]
  dsimp only
  by_cases hc : c = ⟨Equiv.Perm.cycleOf g x, hx'⟩
  · rw [hc, Pi.mulSingle_eq_same, Equiv.Perm.cycleOf_apply_self]
  · rw [Pi.mulSingle_eq_of_ne' hc]
    simp only [OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
    apply symm
    rw [← Equiv.Perm.not_mem_support]
    intro hxc
    apply hc
    rw [← Subtype.coe_inj]
    dsimp only
    apply Equiv.Perm.cycle_is_cycleOf hxc c.prop
  rw [← Equiv.Perm.cycleOf_ne_one_iff_mem]
  simp only [ne_eq, Equiv.Perm.cycleOf_eq_one_iff]
  rw [Function.mem_fixedPoints_iff] at hx
  exact hx

theorem hθ_injective (g : Equiv.Perm α) : Function.Injective (θ g) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨u, v⟩
  unfold θ; unfold θFun
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.mem_ker, Equiv.Perm.ext_iff]
  simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_one, id_eq]
  intro huv
  simp only [Subgroup.mem_bot, Prod.mk_eq_one, MonoidHom.mem_ker]
  constructor
  · ext ⟨x, hx⟩
    simp only [Equiv.Perm.coe_one, id_eq]
    conv_rhs => rw [← huv x]
    rw [θAux_apply_of_mem_fixedPoints, Equiv.Perm.ofSubtype_apply_of_mem]
    exact hx
  · ext c x
    by_cases hx : g.cycleOf x = 1
    · simp only [Equiv.Perm.cycleOf_eq_one_iff, ← Equiv.Perm.not_mem_support] at hx
      simp only [Pi.one_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
      obtain ⟨m, hm⟩ := (v c).prop
      rw [← hm]
      dsimp
      rw [← Equiv.Perm.not_mem_support]
      intro hx'
      suffices : ¬ x ∈ Equiv.Perm.support c
      apply this
      apply Equiv.Perm.support_zpow_le _ _ hx'
      intro hx'
      apply hx
      apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop hx'
    · rw [← ne_eq, Equiv.Perm.cycleOf_ne_one_iff_mem] at hx
      simp only [Pi.one_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
      by_cases hc : g.cycleOf x = ↑c
      · rw [← θAux_apply_of_cycleOf_eq c hc, huv]
      · obtain ⟨m, hm⟩ := (v c).prop
        rw [← hm]
        dsimp
        rw [← Equiv.Perm.not_mem_support]
        intro hx'
        suffices : ¬ x ∈ Equiv.Perm.support c
        apply this
        apply Equiv.Perm.support_zpow_le _ _ hx'
        intro h
        exact hc (Equiv.Perm.cycle_is_cycleOf h c.prop).symm
-- #align on_cycle_factors.hψ_inj Equiv.Perm.OnCycleFactors.hψ_inj

theorem hφ_ker_eq_θ_range (z : Equiv.Perm α) :
    ConjAct.toConjAct z ∈
        Subgroup.map (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).subtype (φ g).ker ↔
      z ∈ (θ g).range := by
  constructor
  · rw [hφ_mem_ker_iff, Equiv.Perm.IsCycle.forall_commute_iff, MonoidHom.mem_range]
    intro Hz
    have hu : ∀ x : α,
      x ∈ Function.fixedPoints g ↔
        z x ∈ Function.fixedPoints g :=  by
      intro x
      simp only [Function.fixedPoints, Equiv.Perm.smul_def, Function.IsFixedPt]
      simp only [← Equiv.Perm.not_mem_support]
      simp only [Set.mem_setOf_eq, not_iff_not]
      constructor
      · intro hx
        let hx' := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx
        apply Equiv.Perm.mem_cycleFactorsFinset_support_le hx'
        obtain ⟨Hz'⟩ := Hz (g.cycleOf x)
          (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx)
        rw [← Hz' x, Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hx⟩
      · intro hzx
        let hzx' := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hzx
        apply Equiv.Perm.mem_cycleFactorsFinset_support_le hzx'
        obtain ⟨Hz'⟩ := Hz (g.cycleOf (z x)) hzx'
        rw [Hz' x, Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hzx⟩
    let u := Equiv.Perm.subtypePerm z hu
    let v : (c : g.cycleFactorsFinset) → (Subgroup.zpowers (c : Equiv.Perm α)) :=
      fun c => ⟨Equiv.Perm.ofSubtype
          (z.subtypePerm (Classical.choose (Hz c.val c.prop))),
            Classical.choose_spec (Hz c.val c.prop)⟩
    use ⟨u, v⟩
    ext x
    by_cases hx : g.cycleOf x = 1
    · rw [hθ_1 _ x]
      simp only [Equiv.Perm.subtypePerm_apply]
      simp only [Equiv.Perm.cycleOf_eq_one_iff] at hx
      exact hx
    · rw [hθ_2 _ x ⟨g.cycleOf x, (Equiv.Perm.cycleOf_ne_one_iff_mem g).mp hx⟩ rfl]
      change (v _ : Equiv.Perm α) x = _
      rw [Equiv.Perm.ofSubtype_apply_of_mem]
      rfl
      simp only [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ne_eq]
      simp only [Equiv.Perm.cycleOf_eq_one_iff] at hx
      exact hx

  · rintro ⟨⟨u, v⟩, h⟩
    rw [hφ_mem_ker_iff]

    rw [Equiv.Perm.IsCycle.forall_commute_iff]
    intro c hc
    suffices hc' : _
    use hc'
    suffices : Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm z hc') = v ⟨c, hc⟩
    rw [this]
    exact (v _).prop
    ext x
    by_cases hx : x ∈ c.support
    · rw [Equiv.Perm.ofSubtype_apply_of_mem, Equiv.Perm.subtypePerm_apply]
      dsimp
      rw [← h, hθ_2 _ x ⟨c, hc⟩]
      exact (Equiv.Perm.cycle_is_cycleOf hx hc).symm
      exact hx
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
      obtain ⟨m, hm⟩ := (v ⟨c, hc⟩).prop
      dsimp only at hm
      rw [← hm]
      apply symm
      rw [← Equiv.Perm.not_mem_support]
      intro hx'
      apply hx
      exact (Equiv.Perm.support_zpow_le c m) hx'
      exact hx
    · intro x
      simp only [← Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff g c hc]
      rw [← h]
      unfold θ; unfold θFun
      dsimp only [MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk]
      rw [θAux_cycleOf_apply_eq]
#align on_cycle_factors.hφ_ker_eq_ψ_range Equiv.Perm.OnCycleFactors.hφ_ker_eq_θ_range

lemma θ_range_eq : MonoidHom.range (θ g) =
    Subgroup.map (ConjAct.toConjAct.symm.toMonoidHom.comp
      (Subgroup.subtype (MulAction.stabilizer (ConjAct (Perm α)) g))) (MonoidHom.ker (φ g)) := by
  ext z
  rw [← hφ_ker_eq_θ_range]
  rfl

theorem hψ_range_card' (g : Equiv.Perm α) :
    Fintype.card (MonoidHom.range (θ g)) = Fintype.card (φ g).ker := by
  change Fintype.card (MonoidHom.range (θ g) : Set (Perm α)) = _
  rw [← Nat.card_eq_fintype_card, Set.Nat.card_coe_set_eq, θ_range_eq, ← Subgroup.map_map]
  rw [Subgroup.coe_map, Set.ncard_image_of_injective _ (by apply Equiv.injective)]
  rw [Subgroup.coe_map, Set.ncard_image_of_injective _ (Subgroup.subtype_injective _)]
  rw [← Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rfl
 #align on_cycle_factors.hψ_range_card' Equiv.Perm.OnCycleFactors.hψ_range_card'

theorem _root_.Equiv.Perm.card_fixedBy (g : Equiv.Perm α) :
    Fintype.card (MulAction.fixedBy α g) =
      Fintype.card α - g.cycleType.sum := by
  rw [Equiv.Perm.sum_cycleType, ← Finset.card_compl]
  simp only [Fintype.card_ofFinset, Set.mem_compl_iff, Finset.mem_coe,
    Equiv.Perm.mem_support, Classical.not_not]
  apply congr_arg
  ext x
  simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def, Finset.mem_filter, Finset.mem_univ,
    true_and_iff, Finset.mem_compl, Equiv.Perm.mem_support, Classical.not_not]
#align on_cycle_factors.equiv.perm.card_fixed_by Equiv.Perm.card_fixedBy

theorem _root_.Fintype.card_pfun (p : Prop) [Decidable p] (β : p → Type _) [∀ hp, Fintype (β hp)] :
    Fintype.card (∀ hp : p, β hp) = if h : p then Fintype.card (β h) else 1 := by
  by_cases hp : p
  · simp only [dif_pos hp]
    rw [Fintype.card_eq]
    exact ⟨@Equiv.funUnique p (β hp) (uniqueProp hp)⟩
  · simp only [dif_neg hp]
    rw [Fintype.card_eq_one_iff]
    use (fun h => False.elim (hp h))
    intro u; ext h; exfalso; exact hp h
#align on_cycle_factors.fintype.card_pfun Fintype.card_pfun

theorem hψ_range_card (g : Equiv.Perm α) :
    Fintype.card (θ g).range =
      (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod := by
  change Fintype.card ((θ g).range : Set (Equiv.Perm α)) = _
  simp only [MonoidHom.coe_range]
  rw [Set.card_range_of_injective (hθ_injective g)]
  rw [Fintype.card_prod]
  rw [Fintype.card_perm]
  rw [Fintype.card_pi]
  apply congr_arg₂ (· * ·)
  · -- fixed points
    apply congr_arg
    exact Equiv.Perm.card_fixedBy g
  · rw [Equiv.Perm.cycleType]
    simp only [Finset.univ_eq_attach, Finset.attach_val, Function.comp_apply]
    rw [Finset.prod_attach (s := g.cycleFactorsFinset)
      (f := fun a ↦ Fintype.card (Subgroup.zpowers (a : Equiv.Perm α)))]
    rw [Finset.prod]
    apply congr_arg
    apply Multiset.map_congr rfl
    intro x hx
    rw [Fintype.card_zpowers, Equiv.Perm.IsCycle.orderOf]
    simp only [Finset.mem_val, Equiv.Perm.mem_cycleFactorsFinset_iff] at hx
    exact hx.left
#align on_cycle_factors.hψ_range_card Equiv.Perm.OnCycleFactors.hψ_range_card

lemma θ_apply_fst (k : Equiv.Perm (MulAction.fixedBy α g)) :
    θ g ⟨k, 1⟩ = Equiv.Perm.ofSubtype k := by
  ext x
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [hθ_2 _ x ⟨g.cycleOf x, hx⟩ rfl]
    simp only [Pi.one_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def,
      ← Equiv.Perm.mem_support, ← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
    exact hx
  · rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.not_mem_support] at hx
    rw [hθ_1 _ x hx, Equiv.Perm.ofSubtype_apply_of_mem]
    rfl

lemma θ_apply_single (c : g.cycleFactorsFinset) (vc : Subgroup.zpowers (c : Equiv.Perm α)) :
    θ g ⟨1, Pi.mulSingle c vc⟩ = (vc : Equiv.Perm α) := by
  ext x
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [hθ_2 _ x ⟨g.cycleOf x, hx⟩ rfl]
    by_cases hc : g.cycleOf x = c
    · suffices : c = ⟨g.cycleOf x, hx⟩
      rw [← this]
      simp only [Pi.mulSingle_eq_same]
      rw [← Subtype.coe_inj, ← hc]
    · simp only [ne_eq]
      rw [Pi.mulSingle_eq_of_ne]
      simp only [OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
      apply symm
      obtain ⟨m, hm⟩ := vc.prop
      dsimp at hm
      rw [← hm, ← Equiv.Perm.not_mem_support]
      intro hx'
      apply hc
      apply symm
      apply Equiv.Perm.cycle_is_cycleOf
      apply Equiv.Perm.support_zpow_le _ _ hx'
      exact c.prop
      intro hc'
      apply hc
      rw [← hc']
  · rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.not_mem_support] at hx
    rw [hθ_1 _ x hx]
    dsimp only [Equiv.Perm.coe_one, id_eq]
    obtain ⟨m, hm⟩ := vc.prop
    dsimp only at hm
    rw [← hm]
    apply symm
    rw [← Equiv.Perm.not_mem_support] at hx ⊢
    intro hx'
    apply hx
    apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop
    apply Equiv.Perm.support_zpow_le _ _ hx'

theorem sign_ψ
    (k : Equiv.Perm (MulAction.fixedBy α g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) :
    Equiv.Perm.sign (θ g ⟨k, v⟩) =
      Equiv.Perm.sign k *
        Finset.univ.prod fun c =>
          Equiv.Perm.sign (v c : Equiv.Perm α) :=  by
  rw [← Prod.fst_mul_snd ⟨k, v⟩]
  simp only [map_mul]
  apply congr_arg₂
  · rw [θ_apply_fst, Equiv.Perm.sign_ofSubtype]
  · rw [← MonoidHom.inr_apply, ← MonoidHom.comp_apply]
    conv_lhs => rw [← Finset.noncommProd_mul_single v]
    simp only [Finset.noncommProd_map]
    rw [Finset.noncommProd_eq_prod]
    apply Finset.prod_congr rfl
    intro c _
    simp only [MonoidHom.inr_apply, MonoidHom.coe_comp, Function.comp_apply, θ_apply_single]
#align on_cycle_factors.sign_ψ Equiv.Perm.OnCycleFactors.sign_ψ

theorem odd_of_mem_kerφ
    (h : Subgroup.comap ConjAct.toConjAct.toMonoidHom
      (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) ≤ alternatingGroup α) :
    ∀ i ∈ g.cycleType, Odd i := by
  intro i hi
  rw [Equiv.Perm.cycleType_def g, Multiset.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  rw [← Finset.mem_def] at hc
  suffices Equiv.Perm.sign c = 1 by
    rw [Equiv.Perm.IsCycle.sign _, neg_eq_iff_eq_neg] at this
    · rw [Nat.odd_iff_not_even, Function.comp_apply]
      rw [← neg_one_pow_eq_one_iff_even (Int.neg_units_ne_self 1), this, ← Units.eq_iff]
      norm_num
    · rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc
      exact hc.left
  suffices c = θ g ⟨1, Pi.mulSingle ⟨c, hc⟩ ⟨c, Subgroup.mem_zpowers c⟩⟩ by
    rw [this]
    apply h
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    apply Subgroup.map_subtype_le
    rw [OnCycleFactors.hφ_ker_eq_θ_range]
    exact Set.mem_range_self _
  rw [θ_apply_single]

end OnCycleFactors

section Centralizer

open BigOperators Nat OnCycleFactors

-- Should one parenthesize the product ?
/-- Cardinality of a centralizer in `equiv.perm α` of a given `cycle_type` -/
theorem conj_stabilizer_card :
    Fintype.card (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) =
      (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (φ g).ker]
  rw [Fintype.card_congr (QuotientGroup.quotientKerEquivRange (φ g)).toEquiv]
  rw [hφ_range_card]
  rw [mul_comm]
  apply congr_arg₂ _ _ rfl
  · rw [← hψ_range_card]
    rw [hψ_range_card']
#align on_cycle_factors.equiv.perm.conj_stabilizer_card Equiv.Perm.conj_stabilizer_card

theorem _root_.Group.conj_class_eq_conj_orbit {G : Type _} [Group G] (g : G) :
    {k : G | IsConj g k} = MulAction.orbit (ConjAct G) g := by
  ext k
  simp only [Set.mem_setOf_eq, isConj_iff, MulAction.mem_orbit_iff, ConjAct.smul_def]
  constructor
  rintro ⟨c, hc⟩
  use ConjAct.toConjAct c; simp only [hc, ConjAct.ofConjAct_toConjAct]
  rintro ⟨x, hx⟩
  use ConjAct.ofConjAct x
#align on_cycle_factors.group.conj_class_eq_conj_orbit Group.conj_class_eq_conj_orbit

theorem _root_.Equiv.Perm.conj_class_card_mul_eq (g : Equiv.Perm α) :
    Fintype.card {h : Equiv.Perm α | IsConj g h} *
      (Fintype.card α - g.cycleType.sum)! *
      g.cycleType.prod *
      (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!) =
    (Fintype.card α)! := by
  classical
  simp_rw [Group.conj_class_eq_conj_orbit g]
  simp only [mul_assoc]
  rw [mul_comm]
  simp only [← mul_assoc]
  rw [← Equiv.Perm.conj_stabilizer_card g]
  rw [mul_comm]
  rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct (Equiv.Perm α)) g]
  rw [ConjAct.card, Fintype.card_perm]
#align on_cycle_factors.equiv.perm.conj_class_card_mul_eq Equiv.Perm.conj_class_card_mul_eq

theorem _root_.Multiset.prod_pos {R : Type _} [StrictOrderedCommSemiring R] (m : Multiset R)
    (h : ∀ a ∈ m, (0 : R) < a) : 0 < m.prod := by
  induction' m using Multiset.induction with a m ih
  · simp
  · rw [Multiset.prod_cons]
    exact
      mul_pos (h _ <| Multiset.mem_cons_self _ _)
        (ih fun a ha => h a <| Multiset.mem_cons_of_mem ha)
#align on_cycle_factors.multiset.prod_pos Multiset.prod_pos

/-- Cardinality of a conjugacy class in `Equiv.Perm α` of a given `cycleType` -/
theorem conj_class_card (g : Equiv.Perm α) :
    Fintype.card {h : Equiv.Perm α | IsConj g h} =
      (Fintype.card α)! /
        ((Fintype.card α - g.cycleType.sum)! *
          g.cycleType.prod *
          (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!)) := by
  rw [← Equiv.Perm.conj_class_card_mul_eq g]
  rw [Nat.div_eq_of_eq_mul_left _]
  simp only [← mul_assoc]
  -- This is the cardinal of the centralizer
  rw [← Equiv.Perm.conj_stabilizer_card g]
  refine' Fintype.card_pos
#align on_cycle_factors.equiv.perm.conj_class_card Equiv.Perm.conj_class_card

variable (α)

theorem card_of_cycleType_eq_zero_iff {m : Multiset ℕ} :
    (Finset.univ.filter fun g : Equiv.Perm α => g.cycleType = m).card = 0
    ↔ ¬ ((m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a)) := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    ← Equiv.Perm.exists_with_cycleType_iff, not_exists]
  aesop

theorem card_of_cycleType_mul_eq (m : Multiset ℕ) :
    (Finset.univ.filter fun g : Equiv.Perm α => g.cycleType = m).card *
        ((Fintype.card α - m.sum)! * m.prod *
          (∏ n in m.toFinset, (m.count n)!)) =
      if (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) then (Fintype.card α)! else 0 := by
  split_ifs with hm
  · -- nonempty case
    obtain ⟨g, hg⟩ := (Equiv.Perm.exists_with_cycleType_iff α).mpr hm
    suffices :
      (Finset.univ.filter fun h : Equiv.Perm α => h.cycleType = m) =
        Finset.univ.filter fun h : Equiv.Perm α => IsConj g h
    rw [this]
    rw [← Fintype.card_coe]
    rw [← Equiv.Perm.conj_class_card_mul_eq g]
    simp only [Fintype.card_coe, ← Set.toFinset_card, mul_assoc]
    rw [hg]
    congr
    · simp only [Finset.univ_filter_exists, Set.toFinset_setOf]
    · simp_rw [Equiv.Perm.isConj_iff_cycleType_eq, hg]
      apply Finset.filter_congr
      simp [eq_comm]
  · -- empty case
    convert MulZeroClass.zero_mul _
    exact (Equiv.Perm.card_of_cycleType_eq_zero_iff α).mpr hm
#align on_cycle_factors.equiv.perm.card_of_cycle_type_mul_eq Equiv.Perm.card_of_cycleType_mul_eq

/-- Cardinality of the set of `equiv.perm α` of given `cycle_type` -/
theorem card_of_cycleType (m : Multiset ℕ) :
    (Finset.univ.filter
      fun g : Equiv.Perm α => g.cycleType = m).card =
      if m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! * m.prod *
            (∏ n in m.toFinset, (m.count n)!))
      else 0 := by
  split_ifs with hm
  · -- nonempty case
    apply symm
    apply Nat.div_eq_of_eq_mul_left
    · apply Nat.mul_pos
      apply Nat.mul_pos
      · apply Nat.factorial_pos
      · apply Multiset.prod_pos
        exact fun a ha ↦ lt_of_lt_of_le (zero_lt_two) (hm.2 a ha)
      · apply Finset.prod_pos
        exact fun _ _ ↦ Nat.factorial_pos _
    rw [Equiv.Perm.card_of_cycleType_mul_eq, if_pos hm]
  · -- empty case
    exact (Equiv.Perm.card_of_cycleType_eq_zero_iff α).mpr hm
#align on_cycle_factors.equiv.perm.card_of_cycle_type Equiv.Perm.card_of_cycleType

end Centralizer

end Equiv.Perm

section AlternatingGroup

variable {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α)

open BigOperators Nat Equiv.Perm.OnCycleFactors

namespace AlternatingGroup

-- should be deleted
theorem of_cycleType_eq (m : Multiset ℕ) :
    Finset.map ⟨Subgroup.subtype (alternatingGroup α), Subgroup.subtype_injective _⟩
        (Finset.univ.filter fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m) =
      if Even (m.sum + Multiset.card m)
        then Finset.univ.filter fun g : Equiv.Perm α => g.cycleType = m
        else ∅ := by
  split_ifs with hm
  · ext g
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · intro hg; rw [Finset.mem_map] at hg
      obtain ⟨⟨k, hk⟩, hk', rfl⟩ := hg
      apply And.intro (Finset.mem_univ _)
      simp only [Finset.mem_filter, Finset.mem_univ, Subgroup.coe_mk, true_and_iff] at hk'
      simp only [Subgroup.coeSubtype, Function.Embedding.coeFn_mk, Subgroup.coe_mk]
      exact hk'
    · rintro ⟨_, hg⟩
      simp only [Subgroup.coeSubtype, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
        true_and_iff, Function.Embedding.coeFn_mk, exists_prop]
      use! g
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType, hg, Even.neg_one_pow hm]
  · rw [Finset.eq_empty_iff_forall_not_mem]
    intro g hg
    simp only [Subgroup.coeSubtype, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and_iff, Function.Embedding.coeFn_mk, exists_prop] at hg
    obtain ⟨⟨k, hk⟩, hkm, rfl⟩ := hg
    rw [← Nat.odd_iff_not_even] at hm
    simp only [Subgroup.coe_mk] at hkm
    simp only [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType,
      hkm, Odd.neg_one_pow hm, ← Units.eq_iff] at hk
    norm_num at hk
#align on_cycle_factors.alternating_group.of_cycle_type_eq AlternatingGroup.of_cycleType_eq

theorem card_of_cycleType_mul_eq (m : Multiset ℕ) :
    (Finset.univ.filter
      fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m).card *
        ((Fintype.card α - m.sum)! *
          (m.prod * (∏ n in m.toFinset, (m.count n)!))) =
      if ((m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.sum + Multiset.card m))
        then (Fintype.card α)!
        else 0 := by
  split_ifs with hm
  · -- m is an even cycle_type
    rw [← Finset.card_map]
    rw [AlternatingGroup.of_cycleType_eq]
    rw [if_pos]
    have := Equiv.Perm.card_of_cycleType_mul_eq α m
    simp only [mul_assoc] at this
    rw [this]
    rw [if_pos]
    exact hm.1
    exact hm.2
  · -- m does not correspond to a permutation, or to an odd one,
    rw [← Finset.card_map]
    rw [AlternatingGroup.of_cycleType_eq]
    rw [apply_ite Finset.card]
    rw [Finset.card_empty]
    rw [not_and_or] at hm
    by_cases hm' : Even (m.sum + Multiset.card m)
    rw [if_pos]
    rw [Equiv.Perm.card_of_cycleType]
    rw [if_neg]
    exact MulZeroClass.zero_mul _
    cases' hm with hm hm; exact hm; exfalso; exact hm hm'
    exact hm'
    rw [if_neg]; exact MulZeroClass.zero_mul _; exact hm'
#align on_cycle_factors.alternating_group.card_of_cycle_type_mul_eq
  AlternatingGroup.card_of_cycleType_mul_eq

theorem card_of_cycleType (m : Multiset ℕ) :
    (Finset.univ.filter fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m).card =
      if (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.sum + Multiset.card m) then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! *
            (m.prod * (∏ n in m.toFinset, (m.count n)!)))
      else 0 := by
  split_ifs with hm
  · -- m is an even cycle_type
    rw [← Finset.card_map]
    rw [AlternatingGroup.of_cycleType_eq]
    rw [if_pos]
    rw [Equiv.Perm.card_of_cycleType α m]
    rw [if_pos]
    simp only [mul_assoc]
    exact hm.1
    exact hm.2
  · -- m does not correspond to a permutation, or to an odd one,
    rw [← Finset.card_map]
    rw [AlternatingGroup.of_cycleType_eq]
    rw [apply_ite Finset.card]
    rw [Finset.card_empty]
    rw [not_and_or] at hm
    by_cases hm' : Even (m.sum + Multiset.card m)
    rw [if_pos]
    rw [Equiv.Perm.card_of_cycleType]
    rw [if_neg]
    cases' hm with hm hm; exact hm; exfalso; exact hm hm'
    exact hm'
    rw [if_neg]; exact hm'
#align on_cycle_factors.alternating_group.card_of_cycle_type AlternatingGroup.card_of_cycleType

theorem card_le_of_mem_kerφ
    (h : Subgroup.comap ConjAct.toConjAct.toMonoidHom
      (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) ≤ alternatingGroup α) :
    Fintype.card α ≤ g.cycleType.sum + 1 := by
  rw [← not_lt]
  intro hm
  rw [Nat.lt_iff_add_one_le, add_assoc] at hm
  change g.cycleType.sum + 2 ≤ _ at hm
  suffices 1 < Fintype.card (MulAction.fixedBy α g) by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    suffices : Equiv.Perm.sign (θ g ⟨Equiv.swap a b, 1⟩) ≠ 1
    · apply this
      apply h
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
      apply Subgroup.map_subtype_le
      rw [hφ_ker_eq_θ_range]
      exact Set.mem_range_self _
    rw [θ_apply_fst]
    simp only [Equiv.Perm.ofSubtype_swap_eq, Equiv.Perm.sign_swap', ne_eq,
      ite_eq_left_iff, Int.neg_units_ne_self, imp_false, not_not]
    rw [Subtype.coe_inj]
    exact hab
  · rw [Equiv.Perm.card_fixedBy g]
    rw [add_comm] at hm
    rw [Nat.lt_iff_add_one_le, Nat.le_sub_iff_add_le]
    exact hm
    rw [Equiv.Perm.sum_cycleType]
    exact Finset.card_le_univ _

-- FIND A BETTER NAME
theorem _root_.Equiv.Perm.OnCycleFactors.count_le_one_of_kerφ_le_alternating
    (h : Subgroup.comap ConjAct.toConjAct.toMonoidHom
      (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) ≤ alternatingGroup α) :
    ∀ i, g.cycleType.count i ≤ 1 := by
  rw [← Multiset.nodup_iff_count_le_one, Equiv.Perm.cycleType_def]
  rw [Multiset.nodup_map_iff_inj_on g.cycleFactorsFinset.nodup]
  simp only [Function.comp_apply, ← Finset.mem_def]
  by_contra hm
  push_neg at hm
  obtain ⟨c, hc, d, hd, hm, hm'⟩ := hm
  let τ : Equiv.Perm g.cycleFactorsFinset := Equiv.swap ⟨c, hc⟩ ⟨d, hd⟩
  obtain ⟨a⟩ := g.existsBasis
  suffices hτ : τ ∈ Iφ g
  let k : Equiv.Perm α := ConjAct.ofConjAct (φ' a ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α))
  have hk2 : ∀ c : g.cycleFactorsFinset, ConjAct.toConjAct k • (c : Equiv.Perm α) = τ c := by
    intro c
    rw [ConjAct.smul_def]
    simp only [ConjAct.ofConjAct_toConjAct]
    rw [mul_inv_eq_iff_eq_mul]
    ext x
    exact k_cycle_apply a hτ c x
  have hksup : k.support ≤ g.support := by
    intro x
    simp only [Equiv.Perm.mem_support]
    intro hx' hx; apply hx'
    rw [← Equiv.Perm.not_mem_support] at hx
    exact k_apply_of_not_mem_support a x hx
  suffices hsign_k : Equiv.Perm.sign k = -1
  · rw [h _, ← Units.eq_iff] at hsign_k
    exact Int.noConfusion hsign_k
    exact (φ' a ⟨τ, hτ⟩).prop
  · /- to prove that `sign k = -1`,
      we could prove that it is the product
      of the transpositions with disjoint supports
      [(g ^ n) (a c), (g ^ n) (a d)], for 0 ≤ n < c.support.card,
      which are in odd number by `odd_of_mem_kerφ`,
      but it will be sufficient to observe that `k ^ 2 = 1`
      (which implies that `k.cycleType` is of the form (2,2,…))
      and to control its support. -/
    suffices k.cycleType = Multiset.replicate c.support.card 2 by
      rw [Equiv.Perm.sign_of_cycleType]; rw [this]
      simp only [Multiset.sum_replicate, Algebra.id.smul_eq_mul, Multiset.card_replicate]
      rw [Odd.neg_one_pow]
      rw [Nat.odd_add']
      simp only [odd_of_mem_kerφ h c.support.card
        (by rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
            exact ⟨c, hc, rfl⟩),
        true_iff_iff]
      rw [mul_comm]; apply even_two_mul

    have hk_apply :
      ∀ (c : g.cycleFactorsFinset) (m n : ℕ),
        (k ^ m) ((g ^ n : Equiv.Perm α) (a c)) = (g ^ n) (a ((τ ^ m) c)) := by
      suffices : ∀ m n : ℕ, Commute (k ^ m) (g ^ n)
      intro c m n
      simp only [Commute, SemiconjBy] at this
      rw [← Equiv.Perm.mul_apply, this, Equiv.Perm.mul_apply, EmbeddingLike.apply_eq_iff_eq]
      induction' m with m hrec
      · simp only [_root_.pow_zero, Equiv.Perm.coe_one, id.def]
      · rw [_root_.pow_succ, Equiv.Perm.mul_apply]
        rw [hrec]
        rw [φ'_apply a ⟨τ, hτ⟩]
        rw [k_apply_base _ hτ]
        rw [_root_.pow_succ]; rw [Equiv.Perm.coe_mul]
        rfl
      apply Commute.pow_pow
      rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
      exact (φ' a ⟨τ, hτ⟩).prop
    suffices ∀ i ∈ k.cycleType, i = 2 by
      rw [← Multiset.eq_replicate_card] at this
      rw [this]
      congr
      --
      suffices this' : Multiset.sum (Equiv.Perm.cycleType k) = Finset.card (Equiv.Perm.support k)

      rw [this] at this'
      simp only [Multiset.sum_replicate, Algebra.id.smul_eq_mul] at this'
      rw [← mul_left_inj']
      rw [this']
      suffices this2 : k.support = c.support ∪ d.support
      rw [this2]; rw [Finset.card_union_eq _]
      suffices this3 : d.support.card = c.support.card
      rw [this3]; rw [mul_two]
      exact hm.symm
      rw [← Equiv.Perm.disjoint_iff_disjoint_support]
      by_contra hcd; apply hm'
      exact Set.Pairwise.eq g.cycleFactorsFinset_pairwise_disjoint hc hd hcd
      · -- k.support = c.support ∪ d.support
        ext x
        constructor
        · intro hx
          obtain ⟨cx, hcx⟩ := Equiv.Perm.sameCycle_of_mem_support (hksup hx)
          have hxcx : x ∈ (cx : Equiv.Perm α).support := by
            rw [Equiv.Perm.SameCycle.eq_cycleOf cx
                (hcx (a cx) (a.mem_support cx)) (a.mem_support cx),
              Equiv.Perm.mem_support_cycleOf_iff]
            constructor; rfl; exact hksup hx
          suffices : c = cx ∨ d = cx
          rw [Finset.mem_union]
          cases' this with hccx hdcx
          · apply Or.intro_left; rw [hccx]; exact hxcx
          · apply Or.intro_right; rw [hdcx]; exact hxcx
          · obtain ⟨n, _, hnx⟩ := (hcx (a cx) (a.mem_support cx)).exists_pow_eq'
            rw [Equiv.Perm.mem_support, ← hnx] at hx
            specialize hk_apply cx 1
            simp only [pow_one] at hk_apply
            rw [hk_apply] at hx
            rw [Function.Injective.ne_iff (Equiv.injective _)] at hx
            have hx' : τ cx ≠ cx := ne_of_apply_ne a hx
            rw [← Equiv.Perm.mem_support, Equiv.Perm.support_swap _] at hx'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
            cases' hx' with hx' hx'
            · apply Or.intro_left
              rw [hx']
            · apply Or.intro_right
              rw [hx']
            intro h; rw [← Subtype.coe_inj] at h; apply hm'; exact h
        · intro hx
          suffices hx' : Equiv.Perm.cycleOf g x = c ∨ Equiv.Perm.cycleOf g x = d
          obtain ⟨cx, hcx⟩ := Equiv.Perm.sameCycle_of_mem_support (x := x) ?_
          have hcx' := Equiv.Perm.SameCycle.eq_cycleOf cx
            (hcx (a cx) (a.mem_support cx)) (a.mem_support cx)
          obtain ⟨n, _, hnx⟩ := Equiv.Perm.SameCycle.exists_pow_eq'
            (hcx (a cx) (a.mem_support cx))
          specialize hk_apply cx 1
          simp only [pow_one] at hk_apply
          rw [← hnx, Equiv.Perm.mem_support, hk_apply]
          rw [Function.Injective.ne_iff (Equiv.injective _)]
          intro haτcx_eq_acx
          have : ¬Equiv.Perm.Disjoint (cx : Equiv.Perm α) (τ cx : Equiv.Perm α) := by
            rw [Equiv.Perm.disjoint_iff_support_disjoint]
            rw [Finset.not_disjoint_iff]
            use a cx
            apply And.intro (a.mem_support cx)
            rw [← haτcx_eq_acx]; exact a.mem_support (τ cx)
          have this' := (Set.Pairwise.eq
            g.cycleFactorsFinset_pairwise_disjoint cx.prop
            (τ cx).prop this).symm
          rw [Subtype.coe_inj] at this'
          rw [← Equiv.Perm.not_mem_support] at this'
          rw [Equiv.Perm.support_swap _] at this'
          simp only [Finset.mem_insert, Finset.mem_singleton] at this'
          apply this'
          simp only [← Subtype.coe_inj, Subtype.coe_mk, ← hcx']
          rw [Finset.mem_union] at hx
          rw [hcx']
          exact hx'
          · intro h
            simp only [← Subtype.coe_inj, Subtype.coe_mk] at h
            exact hm' h
          · simp only [Finset.mem_union] at hx
            cases hx with
            | inl hx =>
              apply Or.intro_left
              exact (Equiv.Perm.cycle_is_cycleOf hx hc).symm
            | inr hx =>
              apply Or.intro_right
              exact (Equiv.Perm.cycle_is_cycleOf hx hd).symm
      · norm_num
      · apply Equiv.Perm.sum_cycleType
    · rw [← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
      cases' hx' with hxc hxd
      · rw [hxc]
        exact hc
      · rw [hxd]
        exact hd
    -- ∀ i ∈ k.cycle_type, i = 2
    suffices hk2 : orderOf k = 2
    · have hk2' : Nat.Prime (orderOf k); rw [hk2]; exact Nat.prime_two
      obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hk2'
      intro i hi
      rw [hn, hk2, Multiset.mem_replicate] at hi
      exact hi.right
    apply orderOf_eq_prime
    · -- k ^ 2 = 1,
      ext x
      simp only [Equiv.Perm.coe_one, id.def]
      by_cases hx : x ∈ g.support
      · -- obtain ⟨cx, hcx, hcx'⟩ := hsame_cycle x hx,
        obtain ⟨cx, hcx⟩ := Equiv.Perm.sameCycle_of_mem_support hx
        -- have hcx' := on_cycle_factors.same_cycle.is_cycle_of ha cx hcx,
        obtain ⟨n, _, rfl⟩ := (hcx (a cx) (a.mem_support cx)).exists_pow_eq'
        convert hk_apply cx 2 n
        suffices hτ2 : τ ^ 2 = 1
        rw [hτ2, Equiv.Perm.coe_one, id.def]
        rw [pow_two]; rw [Equiv.swap_mul_self]
      · -- lorsque x ∉ g.support
        rw [← Equiv.Perm.not_mem_support]
        intro hx'; apply hx
        apply hksup
        apply Equiv.Perm.support_pow_le k 2
        exact hx'
    intro hk
    specialize hk2 ⟨c, hc⟩
    simp only [hk, ConjAct.toConjAct_one, Subtype.coe_mk, one_smul,
      Equiv.swap_apply_left] at hk2
    exact hm' hk2
  · intro x
    by_cases hx : x = ⟨c, hc⟩
    · rw [hx, Equiv.swap_apply_left]; exact hm.symm
    by_cases hx' : x = ⟨d, hd⟩
    · rw [hx', Equiv.swap_apply_right]; exact hm
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']

theorem _root_.Equiv.Perm.OnCycleFactors.kerφ_le_alternating_iff :
    Subgroup.comap ConjAct.toConjAct.toMonoidHom
      (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) ≤ alternatingGroup α ↔
    (∀ i ∈ g.cycleType, Odd i) ∧ Fintype.card α ≤ g.cycleType.sum + 1 ∧
      ∀ i, g.cycleType.count i ≤ 1 :=  by
  rw [SetLike.le_def]
  constructor
  · exact fun h ↦ ⟨odd_of_mem_kerφ h, card_le_of_mem_kerφ g h,
      count_le_one_of_kerφ_le_alternating g h⟩
  · rintro ⟨h_odd, h_fixed, h_count⟩ x hx
    suffices hx' : x ∈ (θ g).range
    obtain ⟨⟨y, uv⟩, rfl⟩ := MonoidHom.mem_range.mp hx'
    rw [Equiv.Perm.mem_alternatingGroup]
    have := sign_ψ (g := g) y uv
    rw [this]
    convert mul_one _
    · apply Finset.prod_eq_one
      rintro ⟨c, hc⟩ _
      obtain ⟨k, hk⟩ := (uv _).prop
      rw [← hk, map_zpow]
      convert one_zpow k
      simp only
      rw [Equiv.Perm.IsCycle.sign, Odd.neg_one_pow, neg_neg]
      apply h_odd
      rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
      use c
      exact ⟨hc, rfl⟩
      rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc
      exact hc.left

    · apply symm
      convert Equiv.Perm.sign_one
      rw [← Equiv.Perm.card_support_le_one]
      apply le_trans (Finset.card_le_univ _)
      change Fintype.card (MulAction.fixedBy α g) ≤ 1
      rw [Equiv.Perm.card_fixedBy g, tsub_le_iff_left]
      exact h_fixed
    -- x ∈ set.range (on_cycle_factors.ψ g)
    suffices : (φ g).ker = ⊤
    rw [← hφ_ker_eq_θ_range, this]
    simp only [Subgroup.coeSubtype, Subgroup.mem_map, Subgroup.mem_top, true_and]
    exact ⟨⟨x, hx⟩, rfl⟩

    -- (OnCycleFactors.φ g).ker = ⊤
    rw [eq_top_iff]
    intro y _
    suffices (φ g).range = ⊥ by
      rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← this, MonoidHom.mem_range]
      exact ⟨y, rfl⟩
    rw [eq_bot_iff]
    intro z
    rw [← Iφ_eq_range, Subgroup.mem_bot]
    intro hz
    apply Equiv.ext
    intro c
    rw [← Multiset.nodup_iff_count_le_one, Equiv.Perm.cycleType_def,
      Multiset.nodup_map_iff_inj_on (Equiv.Perm.cycleFactorsFinset g).nodup]
      at h_count
    rw [Equiv.Perm.coe_one, id.def, ← Subtype.coe_inj]
    exact h_count (z c) (z c).prop c c.prop (hz c)
#align kerφ_le_alternating_iff Equiv.Perm.OnCycleFactors.kerφ_le_alternating_iff


end AlternatingGroup
