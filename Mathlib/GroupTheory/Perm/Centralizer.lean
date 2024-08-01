/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Perm.ConjAct
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Mathlib.GroupTheory.Perm.DomMulAct

/-! # Centralizer of a permutation and cardinality of conjugacy classes
  # in the symmetric groups

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
  its injectivity `Equiv.Perm.OnCycleFactors.θ_injective`,
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

-/

open scoped Pointwise

@[to_additive instDecidablePredMemSetFixedByAddOfDecidableEq]
instance {α β : Type*} [Monoid α] [DecidableEq β] [MulAction α β] (a : α) :
    DecidablePred fun b : β => b ∈ MulAction.fixedBy β a := by
  intro b
  simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
  infer_instance

namespace Equiv.Perm

open MulAction Equiv Subgroup

variable {α : Type*} [DecidableEq α] [Fintype α] {g : Equiv.Perm α}

theorem CycleType.count_def (n : ℕ) :
    g.cycleType.count n =
      Fintype.card {c : g.cycleFactorsFinset // (c : Perm α).support.card = n } := by
  -- work on the LHS
  rw [cycleType, Multiset.count_eq_card_filter_eq]
  -- rewrite the `Fintype.card` as a `Finset.card`
  rw [Fintype.subtype_card, Finset.univ_eq_attach, Finset.filter_attach',
    Finset.card_map, Finset.card_attach]
  simp only [Function.comp_apply, Finset.card, Finset.filter_val, Multiset.filter_map, Multiset.card_map]
  apply congr_arg
  ext c
  apply congr_arg₂ _ rfl
  apply Multiset.filter_congr
  intro d h
  simp only [Function.comp_apply, eq_comm, Finset.mem_val.mp h, exists_const]

namespace OnCycleFactors

variable (g)

/-- The action by conjugation of `ConjAct (Equiv.Perm α)`
  on the cycles of a given permutation -/
def subMulAction : SubMulAction
    (stabilizer (ConjAct (Perm α)) g) (Perm α) where
  carrier := (g.cycleFactorsFinset : Set (Perm α))
  smul_mem' k c hc := by
    suffices g.cycleFactorsFinset = k • g.cycleFactorsFinset by
      rw [this, Finset.coe_smul_finset]
      exact Set.smul_mem_smul_set hc
    simpa only [mem_stabilizer_iff.mp k.prop]
      using cycleFactorsFinset_conj_eq (↑k) g

/-- The conjugation action of `MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  on the cycles of a given permutation -/
scoped instance mulAction :
    MulAction (stabilizer (ConjAct (Perm α)) g) (g.cycleFactorsFinset : Set (Perm α)) :=
  (subMulAction g).mulAction

/-- The canonical morphism from `MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  to the group of permutations of `g.cycleFactorsFinset` -/
def toPerm := toPermHom (stabilizer (ConjAct (Perm α)) g)
    (g.cycleFactorsFinset : Set (Perm α))

theorem toPerm_eq {k : ConjAct (Perm α)} (hk : k ∈ stabilizer (ConjAct (Perm α)) g)
    {c : Perm α} (hc : c ∈ g.cycleFactorsFinset) :
    (toPerm g ⟨k, hk⟩ ⟨c, hc⟩ : Perm α) = k • c := rfl

/-- The range of `Equiv.Perm.OnCycleFactors.toPerm`.

The equality is proved by `Equiv.Perm.OnCycleFactors.range_toPerm_eq_range`. -/
def range_toPerm : Subgroup (Perm g.cycleFactorsFinset) where
  carrier := {τ | ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card}
  one_mem' := by
    simp only [Set.mem_setOf_eq, coe_one, id_eq, eq_self_iff_true, imp_true_iff]
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Subtype.forall, Set.mem_setOf_eq, coe_mul, Function.comp_apply]
    simp only [Subtype.forall, Set.mem_setOf_eq] at hσ hτ
    intro c hc
    rw [hσ, hτ]
  inv_mem' := by
    intro σ hσ
    simp only [Subtype.forall, Set.mem_setOf_eq] at hσ ⊢
    intro c hc
    rw [← hσ]
    · simp only [Finset.coe_mem, Subtype.coe_eta, apply_inv_self]
    · simp only [Finset.coe_mem]

variable {g} in
theorem mem_range_toPerm_iff' {τ : Perm g.cycleFactorsFinset} :
    τ ∈ range_toPerm g ↔
      ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card :=
  Iff.rfl

variable {g} in
theorem card_eq_of_mem_toPerm_range {τ} (hτ : τ ∈ (toPerm g).range) (c) :
    (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := hτ
  rw [toPerm_eq, ConjAct.smul_def, Equiv.Perm.support_conj]
  apply Finset.card_map

/-- A permutation `z : Equiv.Perm α` belongs to the kernel of `φ g` iff
  it commutes with each cycle of `g` -/
theorem toConjAct_mem_ker_toPerm_iff (z : Perm α) :
    ConjAct.toConjAct z ∈ (toPerm g).ker.map
      (MulAction.stabilizer (ConjAct (Perm α)) g).subtype  ↔
        ∀ t ∈ g.cycleFactorsFinset, Commute z t := by
  constructor
  · intro hz
    rw [mem_map] at hz
    obtain ⟨⟨k, hkK⟩, hk, hk'⟩ := hz
    simp only [MonoidHom.mem_ker] at hk
    intro t ht
    rw [commute_iff_eq, ← mul_inv_eq_iff_eq_mul, ← MulAut.conj_apply,
      ← ConjAct.ofConjAct_toConjAct z, ← ConjAct.smul_eq_mulAut_conj _ t,
      ← hk']
    rw [DFunLike.ext_iff] at hk
    specialize hk ⟨t, ht⟩
    simp only [Finset.coe_sort_coe, coe_one, id_eq] at hk
    simp only [hk, coeSubtype, ← toPerm_eq g hkK ht, Finset.coe_sort_coe]
  · intro H
    rw [mem_map]
    refine ⟨⟨ConjAct.toConjAct z, ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, ConjAct.smul_eq_mulAut_conj,
        MulAut.conj_apply, mul_inv_eq_iff_eq_mul, ConjAct.ofConjAct_toConjAct]
      exact commute_of_mem_cycleFactorsFinset_commute z g H
    · simp only [MonoidHom.mem_ker]
      constructor
      · ext ⟨c, hc⟩ x
        rw [toPerm_eq, ConjAct.toConjAct_smul, H c hc]
        simp only [mul_inv_cancel_right, coe_one, id_eq, Subtype.coe_mk]
      · simp only [coeSubtype, coe_mk]


end OnCycleFactors

open OnCycleFactors Subgroup

/-- A `Basis` of a permutation is a choice of an element in each of its cycles -/
class Basis (g : Equiv.Perm α) where
  /-- A choice of elements in each cycle -/
  (toFun : g.cycleFactorsFinset → α)
  /-- For each cycle, the chosen element belongs to the cycle -/
  (mem_support : ∀ c, toFun c ∈ (c : Equiv.Perm α).support)

instance (g : Perm α) :
  DFunLike (Basis g) (g.cycleFactorsFinset) (fun _ => α) where
  coe a := a.toFun
  coe_injective' a a' _ := by cases a; cases a'; congr

namespace Basis

theorem nonempty (g : Perm α) : Nonempty (Basis g) := by
  have (c : g.cycleFactorsFinset) : (c : Perm α).support.Nonempty :=
    IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.prop).1
  exact ⟨fun c ↦ (this c).choose, fun c ↦ (this c).choose_spec⟩

variable (a : Basis g)

-- delete?
theorem mem_support' (c : g.cycleFactorsFinset) :
    a c ∈ support g :=
  mem_cycleFactorsFinset_support_le c.prop (a.mem_support c)

theorem cycleOf_eq (c : g.cycleFactorsFinset) :
    g.cycleOf (a c) = c :=
  (cycle_is_cycleOf (a.mem_support c) c.prop).symm

/-- Given a basis `a` of `g`, this is the basic function that allows
  to define the inverse of `Equiv.Perm.OnCycleFactors.toPerm` :
  `Kf a e ⟨c, i⟩ = (g ^ i) (a (e c))` -/
def Kf (e : Perm g.cycleFactorsFinset) (x : g.cycleFactorsFinset × ℤ) : α :=
  (g ^ x.2) (a (e x.1))

/- -- This version would have been simpler, but doesn't work later
 -- because of the use of Function.extend which requires functions
 -- with *one* argument.
def Kf (a : Equiv.Perm.Basis g) (e : Equiv.Perm g.cycleFactorsFinset)
  (c : g.cycleFactorsFinset) (i : ℤ) : α :=
  (g ^ i) (a (e c))
-/
theorem Kf_def {e : Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} {i : ℤ} :
    Kf a e ⟨c, i⟩ = (g ^ i) (a (e c)) :=
  rfl

theorem Kf_def_zero {e : Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} :
    Kf a e ⟨c, 0⟩ = a (e c) :=
  rfl

theorem Kf_def_one {e : Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} :
    Kf a e ⟨c, 1⟩ = g (a (e c)) :=
  rfl

/-- The multiplicative-additive property of `Equiv.Perm.OnCycleFactors.Kf` -/
theorem Kf_mul_add
    {c : g.cycleFactorsFinset}
    {e e' : Perm g.cycleFactorsFinset} {i j : ℤ} :
    Kf a (e' * e) ⟨c, i + j⟩ = (g ^ i) (Kf a e' ⟨e c, j⟩) := by
  simp only [Kf_def, zpow_add, coe_mul, Function.comp_apply]

/-- The additive property of `Equiv.Perm.OnCycleFactors.Kf` -/
theorem Kf_add {c : g.cycleFactorsFinset} {e : Perm g.cycleFactorsFinset} {i j : ℤ} :
    Kf a e ⟨c, i + j⟩ = (g ^ i) (Kf a 1 ⟨e c, j⟩) := by
  rw [← Kf_mul_add, one_mul]

/-- The additive property of `Equiv.Perm.OnCycleFactors.Kf` -/
theorem Kf_add' {c : g.cycleFactorsFinset} {e : Perm g.cycleFactorsFinset} {i j : ℤ} :
    Kf a e ⟨c, i + j⟩ = (g ^ i) (Kf a e ⟨c, j⟩) := by
  rw [← mul_one e, Kf_mul_add, mul_one]
  rfl

-- DELETE?
theorem eq_cycleOf {c : g.cycleFactorsFinset} {i : ℤ} :
    c = g.cycleOf ((g ^ i) (a c)) := by
  rw [cycleOf_self_apply_zpow, a.cycleOf_eq]

theorem eq_cycleOf' {c : g.cycleFactorsFinset} {e : Perm g.cycleFactorsFinset} {i : ℤ} :
    e c = g.cycleOf (Kf a e ⟨c, i⟩) := by
  rw [Kf_def, cycleOf_self_apply_zpow, a.cycleOf_eq]

theorem Kf_apply {e : Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} {i : ℤ} :
    g (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i + 1⟩ := by
  rw [Kf_def, Kf_def, ← mul_apply, ← zpow_one_add, add_comm 1 i]

theorem Kf_apply' {e : Perm g.cycleFactorsFinset} {c d : g.cycleFactorsFinset} {i : ℤ}
    (hd : d = e c) :
    (d : Perm α) (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i + 1⟩ := by
  -- Kf e ⟨c, i⟩ = (g ^ i) (a (e c)) appartient au cycle de e c
  rw [hd, eq_cycleOf', cycleOf_apply_self, Kf_apply]

theorem Kf_apply'' {e : Perm g.cycleFactorsFinset} {c d : g.cycleFactorsFinset} {i : ℤ}
    (hd' : d ≠ e c) :
    (d : Perm α) (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i⟩ := by
  suffices hdc : (d : Perm α).Disjoint (e c : Perm α) by
    apply Or.resolve_right (disjoint_iff_eq_or_eq.mp hdc (Kf a e ⟨c, i⟩))
    rw [eq_cycleOf', cycleOf_apply_self, ← cycleOf_eq_one_iff, ← eq_cycleOf']
    exact IsCycle.ne_one (mem_cycleFactorsFinset_iff.mp (e c).prop).1
  apply g.cycleFactorsFinset_pairwise_disjoint d.prop (e c).prop
  rw [Function.Injective.ne_iff Subtype.coe_injective]
  exact hd'

theorem Kf_factorsThrough
    {e e' : Perm g.cycleFactorsFinset}
    (hee' : ∀ c : g.cycleFactorsFinset,
      (e c : Perm α).support.card = (e' c : Perm α).support.card) :
    (Kf a e').FactorsThrough (Kf a e) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ He
  simp only [Kf_def] at He ⊢
  suffices hcd : c = d by
    rw [hcd] at He ⊢
    rw [g.zpow_eq_zpow_on_iff,
      ← cycle_is_cycleOf (a := a (e d)) (a.mem_support _) (e d).prop] at He
    rw [g.zpow_eq_zpow_on_iff,
      ← cycle_is_cycleOf (a := a (e' d)) (a.mem_support _) (e' d).prop, ← hee' d]
    exact He
    · rw [← Perm.mem_support, ← cycleOf_mem_cycleFactorsFinset_iff,
        ← cycle_is_cycleOf (a := a (e' d)) (a.mem_support _) (e' d).prop]
      exact (e' d).prop
    · rw [← Perm.mem_support, ← cycleOf_mem_cycleFactorsFinset_iff,
        ← cycle_is_cycleOf (a := a (e d)) (a.mem_support _) (e d).prop]
      exact (e d).prop
  · -- d = c
    apply Equiv.injective e
    rw [← Subtype.coe_inj, eq_cycleOf, eq_cycleOf, He]

/-- Given a basis `a` of `g` and a permutation `τ` of `g.cycleFactorsFinset`,
  `k a τ` is a permutation that acts as τ -/
noncomputable def k (τ : Perm g.cycleFactorsFinset) :=
  Function.extend (Kf a 1) (Kf a τ) id

theorem k_apply {c : g.cycleFactorsFinset} (i : ℤ) {τ : Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card) :
    k a τ (Kf a 1 ⟨c, i⟩) = Kf a τ ⟨c, i⟩ := by
  simp only [k]
  rw [Function.FactorsThrough.extend_apply (Kf_factorsThrough a _) id ⟨c, i⟩]
  · intro c
    simp only [← hτ c, coe_one, id_eq]

theorem k_apply_base {c : g.cycleFactorsFinset} {τ : Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card) :
    k a τ (a c) = a (τ c) :=
  k_apply a 0 hτ

theorem k_apply_of_not_mem_support
    {τ : Perm g.cycleFactorsFinset} (x : α) (hx : x ∉ g.support) :
    k a τ x = x := by
  rw [k, Function.extend_apply']
  · simp only [id_eq]
  · intro hyp
    obtain ⟨⟨c, i⟩, rfl⟩ := hyp
    apply hx
    rw [Kf_def, zpow_apply_mem_support]
    exact mem_support' a _

theorem mem_support_iff_exists_Kf (x : α) :
    x ∈ g.support ↔
    ∃ (c : g.cycleFactorsFinset) (i : ℤ), x = Kf a 1 ⟨c, i⟩ := by
  constructor
  · intro hx
    rw [← cycleOf_mem_cycleFactorsFinset_iff] at hx
    use ⟨g.cycleOf x, hx⟩
    simp only [Kf_def, coe_one, id_eq]
    let ha := a.mem_support ⟨g.cycleOf x, hx⟩
    simp only [Subtype.coe_mk, mem_support_cycleOf_iff] at ha
    obtain ⟨i, hi⟩ := ha.1.symm
    exact ⟨i, hi.symm⟩
  · rintro ⟨c, i, rfl⟩
    simp only [Kf_def, zpow_apply_mem_support, coe_one, id_eq]
    apply mem_cycleFactorsFinset_support_le c.prop
    apply a.mem_support

theorem k_commute_zpow {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card) (j : ℤ) :
    k a τ ∘ (g ^ j : Perm α) = (g ^ j : Perm α) ∘ k a τ := by
  ext x
  simp only [Function.comp_apply]
  by_cases hx : x ∈ g.support
  · rw [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, i, rfl⟩ := hx
    rw [← Kf_add']
    rw [k_apply a (j + i) hτ]
    rw [k_apply a i hτ]
    rw [Kf_add']
  · rw [k_apply_of_not_mem_support a x hx]
    rw [k_apply_of_not_mem_support a ((g ^ j : Perm α) x) _]
    rw [Equiv.Perm.zpow_apply_mem_support]
    exact hx

theorem k_commute {τ : Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card) :
    k a τ ∘ g = g ∘ k a τ := by
  simpa only [zpow_one] using k_commute_zpow a hτ 1

theorem k_apply_gen {c : g.cycleFactorsFinset} {i : ℤ}
    {σ τ : Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card) :
    k a τ (Kf a σ ⟨c, i⟩) = Kf a (τ * σ) ⟨c, i⟩ := by
  simp only [Kf_def]
  rw [← Function.comp_apply (f := k a τ), k_commute_zpow a hτ, Function.comp_apply]
  apply congr_arg
  dsimp
  have (d) (τ : Perm g.cycleFactorsFinset) : a (τ d) = Kf a 1 (τ d, 0) := rfl
  rw [this _ σ, k_apply a 0 hτ, ← Function.comp_apply (f := τ),
    ← coe_mul, this _ (τ * σ)]
  rfl

theorem k_mul {σ : Equiv.Perm g.cycleFactorsFinset}
    (hσ : ∀ c, (σ c : Perm α).support.card = (c : Perm α).support.card)
    {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card) :
    k a σ ∘ k a τ = k a (σ * τ) := by
  ext x
  simp only [Function.comp_apply]
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, i, rfl⟩ := hx
    rw [k_apply a i hτ, k_apply_gen _]
    rw [k_apply_gen]
    simp only [mul_one]
    · intro c
      rw [coe_mul, Function.comp_apply, hσ, hτ]
    exact hσ
  · simp only [k_apply_of_not_mem_support a x hx]

theorem k_one : k a (1 : Perm g.cycleFactorsFinset) = id := by
  ext x
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, i, rfl⟩ := hx
    rw [k_apply]
    rfl
    intro c; rfl
  simp only [id_eq, k_apply_of_not_mem_support a x hx]

theorem k_bij {τ : Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card) :
    Function.Bijective (k a τ) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine' And.intro _ rfl
  rw [Function.surjective_iff_hasRightInverse]
  use k a τ⁻¹
  rw [Function.rightInverse_iff_comp, k_mul a hτ, mul_inv_self, k_one]
  intro c; rw [← hτ (τ⁻¹ c), Equiv.Perm.apply_inv_self]

theorem k_cycle_apply {τ : Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card)
    (c : g.cycleFactorsFinset) (x : α) :
    k a τ ((c : Perm α) x) = (τ c : Perm α) (k a τ x) := by
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨d, j, rfl⟩ := hx
    by_cases hcd : c = d
    · rw [hcd, a.Kf_apply' (by simp only [coe_one, id_eq]), a.k_apply _ hτ,
        k_apply a _ hτ, ← Kf_apply' a rfl]
    · rw [a.Kf_apply'' hcd,
        k_apply a _ hτ, a.Kf_apply'']
      exact (Equiv.injective τ).ne_iff.mpr hcd
  · suffices ∀ (c : g.cycleFactorsFinset), (c : Perm α) x = x by
      simp only [this, k_apply_of_not_mem_support a x hx]
    · intro c
      rw [← not_mem_support]
      exact Finset.not_mem_mono (mem_cycleFactorsFinset_support_le c.prop) hx

/-- Given `a : g.Basis` and a permutation of g.cycleFactorsFinset that
  preserve the lengths of the cycles, the permutation of `α` that
  moves the `Basis` and commutes with `g`
  -/
noncomputable def ofPerm'
    {τ : Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card) :
    Perm α :=
  ofBijective (k a τ) (k_bij a hτ)

theorem ofPerm'_mem_stabilizer
    {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    ConjAct.toConjAct (ofPerm' a hτ) ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g := by
  rw [MulAction.mem_stabilizer_iff]
  rw [ConjAct.smul_def]
  rw [ConjAct.ofConjAct_toConjAct]
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  simp only [coe_mul]
  simp only [ofPerm']
  simp only [Function.comp_apply, ofBijective_apply]
  rw [← Function.comp_apply (f := k a τ)]
  rw [k_commute a hτ]
  rfl

/-- Given `a : Equiv.Perm.Basis g`,
  we define a right inverse of `Equiv.Perm.OnCycleFactors.toPerm`, on `range_toPerm g` -/
noncomputable
def ofPerm :
    range_toPerm g →* MulAction.stabilizer (ConjAct (Perm α)) g  where
  toFun τhτ :=
    ⟨ConjAct.toConjAct (ofPerm' a (mem_range_toPerm_iff'.mp τhτ.prop)),
      ofPerm'_mem_stabilizer a (mem_range_toPerm_iff'.mp τhτ.prop)⟩
  map_one' := by
    simp only [OneMemClass.coe_one, Submonoid.mk_eq_one, MulEquivClass.map_eq_one_iff]
    ext x
    simp only [ofPerm', k_one, Equiv.ofBijective_apply, id_eq, Equiv.Perm.coe_one]
  map_mul' σ τ := by
    simp only [Subgroup.coe_mul, Submonoid.mk_mul_mk, Subtype.mk_eq_mk, ← ConjAct.toConjAct_mul]
    apply congr_arg
    ext x
    simp only [ofPerm', ← k_mul a σ.prop τ.prop, ofBijective_apply, Function.comp_apply, coe_mul]

theorem ofPerm_apply {τ} (hτ) (x) :
    (ConjAct.ofConjAct (ofPerm a ⟨τ, hτ⟩ : ConjAct (Perm α))) x = k a τ x :=
  rfl

theorem ofPerm_apply_mk (τ : range_toPerm g) (x) :
    ConjAct.ofConjAct (ofPerm a τ : ConjAct (Perm α)) x = k a τ.val x :=
  rfl

theorem ofPerm_apply_mk' (τ : Perm (g.cycleFactorsFinset)) (hτ : τ ∈ range_toPerm g) (x) :
    ConjAct.ofConjAct (ofPerm a ⟨τ, hτ⟩ : ConjAct (Perm α)) x = k a τ x :=
  rfl


theorem ofPerm_support_le (τ : range_toPerm g) :
    (ConjAct.ofConjAct (ofPerm a τ : ConjAct (Perm α))).support ≤
      g.support := by
  intro x
  simp only [Perm.mem_support]
  intro hx' hx
  apply hx'
  rw [← Perm.not_mem_support] at hx
  exact k_apply_of_not_mem_support a x hx

theorem ofPerm_equivariant (τ : range_toPerm g) (c : g.cycleFactorsFinset) :
    (ofPerm a τ  : ConjAct (Perm α)) • (c : Perm α) = τ.val c := by
  rw [ConjAct.smul_def]
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  exact k_cycle_apply a τ.prop c x

theorem ofPerm_rightInverse (τ : range_toPerm g) :
    (OnCycleFactors.toPerm g) ((ofPerm a) τ) = (τ : Perm g.cycleFactorsFinset) := by
  apply ext
  intro ⟨c, hc⟩
  rw [← Subtype.coe_inj, toPerm_eq, ofPerm_equivariant a τ ⟨c, hc⟩]
  rfl

end Basis
namespace OnCycleFactors

open Basis BigOperators Nat Equiv.Perm Equiv Subgroup

theorem range_toPerm_eq_range : range_toPerm g = (toPerm g).range := by
  obtain ⟨a⟩ := Basis.nonempty g
  ext τ
  constructor
  · exact fun hτ ↦ ⟨(ofPerm a) ⟨τ, hτ⟩, ofPerm_rightInverse a ⟨τ, hτ⟩⟩
  · rw [mem_range_toPerm_iff']
    exact card_eq_of_mem_toPerm_range

theorem mem_range_toPerm_iff {τ} : τ ∈ (toPerm g).range ↔
    ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card := by
  simp only [← range_toPerm_eq_range, mem_range_toPerm_iff', Subtype.forall, Finset.coe_sort_coe]

theorem card_range_toPerm :
    Fintype.card (toPerm g).range =
      ∏ n in g.cycleType.toFinset, (g.cycleType.count n)! := by
  let sc (c : g.cycleFactorsFinset) : ℕ := (c : Perm α).support.card
  suffices Fintype.card (toPerm g).range =
    Fintype.card { k : Perm g.cycleFactorsFinset | sc ∘ k = sc } by
    simp only [this, Set.coe_setOf, DomMulAct.stabilizer_card', ← CycleType.count_def]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext n
    simp only [Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach,
        sc, true_and, Subtype.exists, exists_prop, Multiset.mem_toFinset]
    simp only [cycleType_def, Function.comp_apply, Multiset.mem_map, Finset.mem_val]
  suffices ((toPerm g).range : Set (Perm (g.cycleFactorsFinset : Set (Perm α)))) =
      {τ : Perm g.cycleFactorsFinset | sc ∘ τ = sc } by
      simp_rw [← this]
      rfl
  ext τ
  simp [← range_toPerm_eq_range, mem_range_toPerm_iff', sc, Function.funext_iff]

section Kernel
/- Here, we describe the kernel of `g.OnCycleFactors.toPerm` -/

open BigOperators Nat OnCycleFactors Subgroup

variable {k : Perm (Function.fixedPoints g)}
  {v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)}
  {x : α}

/- (ofSubtype k) * (by
variable (k) (v) in
  apply Finset.univ.noncommProd (fun c ↦ (v c : Perm α))
  rintro a _ b _ h
  obtain ⟨m, hm⟩ := (v a).prop
  obtain ⟨n, hn⟩ := (v b).prop
  rw [← hm, ← hn]
  apply Commute.zpow_zpow
  apply g.cycleFactorsFinset_mem_commute a.prop b.prop
  rw [ne_eq, Subtype.coe_inj, ← ne_eq]
  exact h) -/

variable (k) (v) (x) in
/-- An auxiliary function to define the parametrization of the kernel of `g.OnCycleFactors.toPerm` -/
def θAux : α :=
  if hx : g.cycleOf x ∈ g.cycleFactorsFinset
  then (v ⟨g.cycleOf x, hx⟩ : Perm α) x
  else ofSubtype k x

lemma θAux_apply_of_mem_fixedPoints (hx : x ∈ Function.fixedPoints g) :
    θAux k v x = ofSubtype k x := by
  rw [θAux, dif_neg]
  rw [cycleOf_mem_cycleFactorsFinset_iff, not_mem_support, hx]

lemma θAux_apply_of_mem_fixedPoints_mem (hx : x ∈ Function.fixedPoints g) :
    θAux k v x ∈ Function.fixedPoints g := by
  rw [θAux_apply_of_mem_fixedPoints hx, ofSubtype_apply_of_mem k hx]
  exact (k _).prop

lemma cycleOf_θAux_apply_eq :
    g.cycleOf (θAux k v x) = g.cycleOf x := by
  unfold θAux
  split_ifs with hx
  · let c : g.cycleFactorsFinset := ⟨g.cycleOf x, hx⟩
    change g.cycleOf ((v c : Perm α) x) = g.cycleOf x
    obtain ⟨m, hm⟩ := (v c).prop
    rw [← hm, cycleOf_zpow_apply_self, cycleOf_self_apply_zpow]
  · rw [cycleOf_mem_cycleFactorsFinset_iff, not_mem_support] at hx
    rw [g.cycleOf_eq_one_iff.mpr hx, cycleOf_eq_one_iff, ofSubtype_apply_of_mem k hx]
    exact Subtype.coe_prop (k ⟨x, hx⟩)

lemma θAux_apply_of_cycleOf_eq (c : g.cycleFactorsFinset) (hx : g.cycleOf x = ↑c) :
    θAux k v x = (v c : Equiv.Perm α) x := by
  suffices c = ⟨g.cycleOf x, by simp only [hx, c.prop]⟩ by
    rw [this, θAux, dif_pos]
  simp only [← Subtype.coe_inj, hx]

variable (x) in
lemma θAux_one : θAux (g := g) 1 1 x = x := by
  unfold θAux
  split_ifs
  · simp only [Pi.one_apply, OneMemClass.coe_one, coe_one, id_eq]
  · simp only [map_one, coe_one, id_eq]

lemma θAux_mul
    (k' : Perm (Function.fixedPoints g))
    (v' : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α))
    (x : α) :
    (θAux k' v') (θAux k v x) =
      θAux (k' * k) (v' * v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)) x := by
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩
      (by rw [cycleOf_θAux_apply_eq]),
      -- (θAux_apply_of_cycleOf_eq_mem ⟨_, hx⟩ rfl),
      θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ rfl,
      θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ rfl]
    simp only [ne_eq, Pi.mul_apply, Submonoid.coe_mul,
      Subgroup.coe_toSubmonoid, coe_mul, Function.comp_apply]
  · nth_rewrite 1 [θAux, dif_neg]
    simp only [θAux, dif_neg hx]
    · simp only [map_mul, coe_mul, Function.comp_apply]
    · simp only [cycleOf_θAux_apply_eq, hx, not_false_eq_true]

variable (k) (v) in
lemma θAux_inv :
    Function.LeftInverse (θAux k⁻¹ v⁻¹) (θAux k v) := fun x ↦ by
  simp only [θAux_mul, mul_left_inv, θAux_one]

variable (k v) in
/-- Given a permutation `g`, a permutation of its fixed points
  and a family of elements in the powers of the cycles of `g`,
  construct their product -/
def θFun : Equiv.Perm α := {
  toFun := θAux k v
  invFun := θAux k⁻¹ v⁻¹
  left_inv := θAux_inv k v
  right_inv := θAux_inv k⁻¹ v⁻¹ }

/-- The description of the kernel of `Equiv.Perm.OnCycleFactors.φ g` -/
def θ (g : Perm α) : Perm (Function.fixedPoints g) ×
    ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) →* Equiv.Perm α := {
  toFun     := fun kv ↦ θFun kv.fst kv.snd
  map_one'  := by
    ext x
    simp only [θFun, Prod.fst_one, Prod.snd_one, coe_one, id_eq,
      inv_one, coe_fn_mk, θAux_one]
  map_mul'  := fun kv' kv ↦ by
    ext x
    simp only [θFun, coe_fn_mk, Prod.fst_mul, Prod.snd_mul,
      coe_mul, coe_fn_mk, Function.comp_apply, θAux_mul] }

theorem θ_apply_of_mem_fixedPoints (uv) (x : α) (hx : x ∈ Function.fixedPoints g) :
    θ g uv x = uv.fst ⟨x, hx⟩ := by
  unfold θ θFun
  simp only [coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk, coe_fn_mk]
  rw [θAux_apply_of_mem_fixedPoints, Equiv.Perm.ofSubtype_apply_of_mem]
  exact hx

theorem θ_apply_of_cycleOf_eq (uv) (x : α) (c : g.cycleFactorsFinset)  (hx : g.cycleOf x = ↑c) :
    θ g uv x = (uv.snd c : Perm α) x := by
  unfold θ θFun
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk]
  exact θAux_apply_of_cycleOf_eq c hx

theorem θ_apply_single (c : g.cycleFactorsFinset) :
    θ g ⟨1, (Pi.mulSingle c ⟨c, Subgroup.mem_zpowers (c : Perm α)⟩)⟩ = c  := by
  ext x
  by_cases hx : x ∈ Function.fixedPoints g
  · simp only [θ_apply_of_mem_fixedPoints _ x hx, coe_one, id_eq]
    apply symm
    rw [← not_mem_support]
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, ← not_mem_support] at hx
    intro hx'
    apply hx
    apply mem_cycleFactorsFinset_support_le c.prop hx'
  suffices hx' : g.cycleOf x ∈ g.cycleFactorsFinset by
    rw [θ_apply_of_cycleOf_eq _ x ⟨g.cycleOf x, hx'⟩ rfl]
    dsimp only
    by_cases hc : c = ⟨cycleOf g x, hx'⟩
    · rw [hc, Pi.mulSingle_eq_same, cycleOf_apply_self]
    · rw [Pi.mulSingle_eq_of_ne' hc]
      simp only [OneMemClass.coe_one, coe_one, id_eq]
      rw [eq_comm, ← not_mem_support]
      intro hxc
      apply hc
      simp only [← Subtype.coe_inj]
      apply cycle_is_cycleOf hxc c.prop
  rw [← cycleOf_ne_one_iff_mem_cycleFactorsFinset]
  simp only [ne_eq, cycleOf_eq_one_iff]
  rw [Function.mem_fixedPoints_iff] at hx
  exact hx

theorem θ_injective (g : Perm α) : Function.Injective (θ g) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨u, v⟩
  unfold θ; unfold θFun
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.mem_ker, ext_iff]
  simp only [coe_fn_mk, coe_one, id_eq]
  intro huv
  simp only [Subgroup.mem_bot, Prod.mk_eq_one, MonoidHom.mem_ker]
  constructor
  · ext ⟨x, hx⟩
    simp only [coe_one, id_eq]
    conv_rhs => rw [← huv x]
    rw [θAux_apply_of_mem_fixedPoints, ofSubtype_apply_of_mem]
    exact hx
  · ext c x
    by_cases hx : g.cycleOf x = 1
    · simp only [cycleOf_eq_one_iff, ← not_mem_support] at hx
      simp only [Pi.one_apply, OneMemClass.coe_one, coe_one, id_eq]
      obtain ⟨m, hm⟩ := (v c).prop
      rw [← hm]
      dsimp only
      rw [← not_mem_support]
      intro hx'
      apply hx
      apply support_zpow_le _ _ at hx'
      apply mem_cycleFactorsFinset_support_le c.prop hx'
    · rw [← ne_eq, cycleOf_ne_one_iff_mem_cycleFactorsFinset] at hx
      simp only [Pi.one_apply, OneMemClass.coe_one, coe_one, id_eq]
      by_cases hc : g.cycleOf x = ↑c
      · rw [← θAux_apply_of_cycleOf_eq c hc, huv]
      · obtain ⟨m, hm⟩ := (v c).prop
        rw [← hm]
        dsimp
        rw [← not_mem_support]
        intro hx'
        refine hc (cycle_is_cycleOf ?_ c.prop).symm
        exact support_zpow_le _ _ hx'

theorem hφ_ker_eq_θ_range (z : Perm α) :
    ConjAct.toConjAct z ∈
        Subgroup.map (MulAction.stabilizer (ConjAct (Perm α)) g).subtype (toPerm g).ker ↔
      z ∈ (θ g).range := by
  constructor
  · rw [toConjAct_mem_ker_toPerm_iff, IsCycle.forall_commute_iff, MonoidHom.mem_range]
    intro Hz
    have hu : ∀ x : α,
      x ∈ Function.fixedPoints g ↔
        z x ∈ Function.fixedPoints g :=  by
      intro x
      simp only [Function.fixedPoints, smul_def, Function.IsFixedPt]
      simp only [← not_mem_support]
      simp only [Set.mem_setOf_eq, not_iff_not]
      constructor
      · intro hx
        let hx' := cycleOf_mem_cycleFactorsFinset_iff.mpr hx
        apply mem_cycleFactorsFinset_support_le hx'
        obtain ⟨Hz'⟩ := Hz (g.cycleOf x) hx'
        rw [← Hz' x, Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hx⟩
      · intro hzx
        let hzx' := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hzx
        apply Equiv.Perm.mem_cycleFactorsFinset_support_le hzx'
        obtain ⟨Hz'⟩ := Hz (g.cycleOf (z x)) hzx'
        rw [Hz' x, Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hzx⟩
    set u := subtypePerm z hu
    set v : (c : g.cycleFactorsFinset) → (Subgroup.zpowers (c : Perm α)) :=
      fun c => ⟨ofSubtype
          (z.subtypePerm (Classical.choose (Hz c.val c.prop))),
            Classical.choose_spec (Hz c.val c.prop)⟩
    use ⟨u, v⟩
    ext x
    by_cases hx : g.cycleOf x = 1
    · rw [θ_apply_of_mem_fixedPoints _ x]
      simp only [u, subtypePerm_apply]
      simpa only [cycleOf_eq_one_iff] using hx
    · rw [θ_apply_of_cycleOf_eq _ x ⟨g.cycleOf x, (cycleOf_ne_one_iff_mem_cycleFactorsFinset g).mp hx⟩ rfl]
      rw [ofSubtype_apply_of_mem]
      · rfl
      · simp only [Perm.mem_support, cycleOf_apply_self, ne_eq]
        simpa only [cycleOf_eq_one_iff] using hx

  · rw [toConjAct_mem_ker_toPerm_iff, IsCycle.forall_commute_iff]
    rintro ⟨⟨u, v⟩, h⟩ c hc
    refine ⟨?_, ?_⟩
    · intro x
      simp only [← eq_cycleOf_of_mem_cycleFactorsFinset_iff g c hc]
      rw [← h]
      unfold θ θFun
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, coe_fn_mk, cycleOf_θAux_apply_eq]
    · suffices ofSubtype (subtypePerm z _) = v ⟨c, hc⟩ by
        rw [this]
        exact (v _).prop
      ext x
      by_cases hx : x ∈ c.support
      · rw [ofSubtype_apply_of_mem, subtypePerm_apply]
        · dsimp only [id_eq, MonoidHom.coe_mk, OneHom.coe_mk, coe_fn_mk, eq_mpr_eq_cast]
          rw [← h, θ_apply_of_cycleOf_eq _ x ⟨c, hc⟩]
          exact (cycle_is_cycleOf hx hc).symm
        · exact hx
      · rw [ofSubtype_apply_of_not_mem]
        · obtain ⟨m, hm⟩ := (v ⟨c, hc⟩).prop
          rw [← hm, eq_comm, ← not_mem_support]
          intro hx'
          apply hx
          exact (support_zpow_le c m) hx'
        · exact hx

lemma θ_range_eq : MonoidHom.range (θ g) = Subgroup.map
    (ConjAct.toConjAct.symm.toMonoidHom.comp
      (Subgroup.subtype (MulAction.stabilizer (ConjAct (Perm α)) g)))
    (MonoidHom.ker (toPerm g)) := by
  ext z
  rw [← hφ_ker_eq_θ_range]
  rfl

theorem θ_range_card (g : Equiv.Perm α) :
    Fintype.card (θ g).range =
      (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod := by
  change Fintype.card ((θ g).range : Set (Equiv.Perm α)) = _
  simp only [MonoidHom.coe_range]
  rw [Set.card_range_of_injective (θ_injective g)]
  rw [Fintype.card_prod]
  rw [Fintype.card_perm]
  rw [Fintype.card_pi]
  apply congr_arg₂ (· * ·)
  · -- fixed points
    apply congr_arg
    exact card_fixedPoints g
  · rw [cycleType]
    simp only [Finset.univ_eq_attach, Finset.attach_val, Function.comp_apply]
    rw [Finset.prod_attach (s := g.cycleFactorsFinset)
      (f := fun a ↦ Fintype.card (Subgroup.zpowers (a : Perm α)))]
    rw [Finset.prod]
    apply congr_arg
    apply Multiset.map_congr rfl
    intro x hx
    rw [Fintype.card_zpowers, IsCycle.orderOf]
    simp only [Finset.mem_val, mem_cycleFactorsFinset_iff] at hx
    exact hx.left

lemma θ_apply_fst (k : Perm (Function.fixedPoints g)) :
    θ g ⟨k, 1⟩ = ofSubtype k := by
  ext x
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [θ_apply_of_cycleOf_eq _ x ⟨g.cycleOf x, hx⟩ rfl]
    simp only [Pi.one_apply, OneMemClass.coe_one, coe_one, id_eq]
    rw [ofSubtype_apply_of_not_mem]
    simpa [cycleOf_mem_cycleFactorsFinset_iff, Perm.mem_support] using hx
  · rw [cycleOf_mem_cycleFactorsFinset_iff, Perm.not_mem_support] at hx
    rw [θ_apply_of_mem_fixedPoints _ x hx, Equiv.Perm.ofSubtype_apply_of_mem]

example (α β : Type*) (a x : α) (b y : β) :
  (⟨a, b⟩ : α × β) = ⟨x, y⟩ ↔ a = x ∧ b = y := by
  exact Prod.mk.inj_iff

example (α β : Type*) [Group α] [Group β] (a : α) (b : β) (m : ℤ) :
  (⟨a, b⟩ : α × β) ^ m = ⟨a ^ m, b ^ m⟩ := by
  rw [@Prod.pow_mk]

@[to_additive]
def Pi.mulSingle_pow {I : Type*} {f : I → Type*} [DecidableEq I]
  [(i : I) → Monoid (f i)]
  (i : I) (x : f i) (n : ℕ) :
  Pi.mulSingle i (x ^ n) = (Pi.mulSingle i x) ^ n := by
  ext s
  classical
  rw [Pi.pow_apply]
  by_cases h : s = i
  · rw [h, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, one_pow]

@[to_additive]
def Pi.mulSingle_zpow {I : Type*} {f : I → Type*} [DecidableEq I] [(i : I) → Group (f i)]
  (i : I) (x : f i) (n : ℤ) :
  Pi.mulSingle i (x ^ n) = (Pi.mulSingle i x) ^ n := by
  ext s
  classical
  rw [Pi.pow_apply]
  by_cases h : s = i
  · rw [h, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, one_zpow]

lemma θ_apply_single_zpowers (c : g.cycleFactorsFinset) (vc : Subgroup.zpowers (c : Equiv.Perm α)) :
    θ g ⟨1, Pi.mulSingle c vc⟩ = (vc : Equiv.Perm α) := by
  obtain ⟨m, hm⟩ := vc.prop
  simp only at hm
  suffices vc = ⟨(c : Perm α), mem_zpowers _⟩ ^ m by
    rw [this, ← one_zpow m, Pi.mulSingle_zpow, ← Prod.pow_mk, map_zpow,
      θ_apply_single, SubgroupClass.coe_zpow]
  rw [← Subtype.coe_inj, ← hm, SubgroupClass.coe_zpow]

end Kernel

end OnCycleFactors

open Nat
variable (g)

-- Should one parenthesize the product ?
/-- Cardinality of the centralizer in `Equiv.Perm α` of a permutation given `cycleType` -/
theorem conj_stabilizer_card :
    Fintype.card (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) =
      (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!) := by
  rw [← Nat.card_eq_fintype_card,
    card_eq_card_quotient_mul_card_subgroup (OnCycleFactors.toPerm g).ker,
    Nat.card_eq_fintype_card,
    Fintype.card_congr (QuotientGroup.quotientKerEquivRange (toPerm g)).toEquiv,
    card_range_toPerm, mul_comm]
  apply congr_arg₂ _ _ rfl
  rw [← θ_range_card, ← Nat.card_eq_fintype_card]
  simp only [← SetLike.coe_sort_coe, Set.Nat.card_coe_set_eq]
  rw [θ_range_eq, ← map_map,
    coe_map, Set.ncard_image_of_injective _ (by exact MulEquiv.injective _),
    coe_map, Set.ncard_image_of_injective _ (subtype_injective _)]

theorem card_isConj_mul_eq (g : Equiv.Perm α) :
    Fintype.card {h : Equiv.Perm α | IsConj g h} *
      (Fintype.card α - g.cycleType.sum)! *
      g.cycleType.prod *
      (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!) =
    (Fintype.card α)! := by
  classical
  simp only [mul_assoc]
  rw [mul_comm]
  simp only [← mul_assoc]
  rw [← conj_stabilizer_card g, mul_comm]
  convert MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct (Perm α)) g
  · ext h
    simp only [Set.mem_setOf_eq, ConjAct.mem_orbit_conjAct, isConj_comm]
  · rw [ConjAct.card, Fintype.card_perm]

/-- Cardinality of a conjugacy class in `Equiv.Perm α` of a given `cycleType` -/
theorem card_isConj_eq (g : Equiv.Perm α) :
    Fintype.card {h : Equiv.Perm α | IsConj g h} =
      (Fintype.card α)! /
        ((Fintype.card α - g.cycleType.sum)! *
          g.cycleType.prod *
          (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!)) := by
  rw [← card_isConj_mul_eq g, Nat.div_eq_of_eq_mul_left _]
  · simp only [← mul_assoc]
  -- This is the cardinal of the centralizer
  · rw [← conj_stabilizer_card g]
    apply Fintype.card_pos

variable (α)

theorem card_of_cycleType_eq_zero_iff {m : Multiset ℕ} :
    (Finset.univ.filter fun g : Equiv.Perm α => g.cycleType = m).card = 0
    ↔ ¬ ((m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a)) := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    ← exists_with_cycleType_iff, not_exists]
  aesop

theorem card_of_cycleType_mul_eq (m : Multiset ℕ) :
    (Finset.univ.filter fun g : Equiv.Perm α => g.cycleType = m).card *
        ((Fintype.card α - m.sum)! * m.prod *
          (∏ n in m.toFinset, (m.count n)!)) =
      if (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) then (Fintype.card α)! else 0 := by
  split_ifs with hm
  · -- nonempty case
    obtain ⟨g, hg⟩ := (exists_with_cycleType_iff α).mpr hm
    suffices (Finset.univ.filter fun h : Equiv.Perm α => h.cycleType = m) =
        Finset.univ.filter fun h : Equiv.Perm α => IsConj g h by
      rw [this, ← Fintype.card_coe, ← card_isConj_mul_eq g]
      simp only [Fintype.card_coe, ← Set.toFinset_card, mul_assoc, hg,
        Finset.univ_filter_exists, Set.toFinset_setOf]
    simp_rw [isConj_iff_cycleType_eq, hg]
    apply Finset.filter_congr
    simp [eq_comm]
  · -- empty case
    convert MulZeroClass.zero_mul _
    exact (card_of_cycleType_eq_zero_iff α).mpr hm

/-- Cardinality of the `Finset` of `Equiv.Perm α` of given `cycleType` -/
theorem card_of_cycleType (m : Multiset ℕ) :
    (Finset.univ.filter
      fun g : Perm α => g.cycleType = m).card =
      if m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! * m.prod * (∏ n in m.toFinset, (m.count n)!))
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
      · exact Finset.prod_pos (fun _ _ ↦ Nat.factorial_pos _)
    rw [card_of_cycleType_mul_eq, if_pos hm]
  · -- empty case
    exact (card_of_cycleType_eq_zero_iff α).mpr hm

end Equiv.Perm
