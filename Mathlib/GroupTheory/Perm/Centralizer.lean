/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

-/

import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
-- import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Perm.ConjAct
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Mathlib.GroupTheory.Perm.DomMulAct

/-! # Centralizer of a permutation and cardinality of conjugacy classes
  # in the symmetric groups

Let `α : Type` with `Fintype α` (and `DecidableEq α`).
The main goal of this file is to compute the cardinality of
conjugacy classes in `Equiv.Perm α`.
Every `g : Equiv.Perm α` has a `cycleType α : Multiset ℕ`.
By `Equiv.Perm.isConj_iff_cycleType_eq`,
two permutations are conjugate in `Equiv.Perm α` iff
their cycle types are equal.
To compute the cardinality of the conjugacy classes, we could use
a purely combinatorial approach and compute the number of permutations
with given cycle type but we resorted to a more algebraic approach
based on the study of the centralizer of a permutation `g`.

Given `g : Equiv.Perm α`, the conjugacy class of `g` is the orbit
of `g` under the action `ConjAct (Equiv.Perm α)`, and we use the
orbit-stabilizer theorem
(`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`) to reduce
the computation to the computation of the centralizer of `g`, the
subgroup of `Equiv.Perm α` consisting of all permutations which
commute with `g`. It is accessed here as `MulAction.stabilizer
(ConjAct (Equiv.Perm α)) g` and
`Equiv.Perm.centralizer_eq_comap_stabilizer`.

We compute this subgroup as follows.

* If `h : Subgroup.centralizer {g}`, then the action of `ConjAct.toConjAct h`
by conjugation on `Equiv.Perm α` stabilizes `g.cycleFactorsFinset`.
That induces an action of `Subgroup.centralizer {g}` on
`g.cycleFactorsFinset` which is defined via
`Equiv.Perm.OnCycleFactors.subMulActionOnCycleFactors `

* This action defines a group morphism `Equiv.Perm.OnCycleFactors.toPermHom g`
from `Subgroup.centralizer {g}` to `Equiv.Perm g.cycleFactorsFinset`

* `Equiv.Perm.OnCycleFactors.toPermHom_range'` is the subgroup of
`Equiv.Perm g.cycleFactorsFinset` consisting of permutations that
preserve the cardinality of the support.

* `Equiv.Perm.OnCycleFactors.range_eq_range_toPermHom'  shows that
the range of `Equiv.Perm.OnCycleFactors.toPermHom g`
is the subgroup `toPermHom_range' g` of `Equiv.Perm g.cycleFactorsFinset`.

This is showed by constructing a right inverse
`Equiv.Perm.Basis.toCentralizer`, as established by
`Equiv.Perm.Basis.toCentralizer_rightInverse`.

* `Equiv.Perm.OnCycleFactors.nat_card_range_toPermHom` computes the
cardinality of `(Equiv.Perm.OnCycleFactors.toPermHom g).range`
as a product of factorials.

* `Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff` proves that `k :
  Subgroup.centralizer {g}` belongs to the kernel of
  `Equiv.Perm.OnCycleFactors.toPermHom g` if and only if it commutes with
  each cycle of `g`.  This is equivalent to the conjunction of two properties:
  * `k` preserves the set of fixed points of `g``
  * on each cycle `c`, `k` acts as a power of that cycle

  This allows to give a description of the kernel of
  `Equiv.Perm.OnCycleFactors.toPermHom g` as the product of a
  symmetric group and of a product of cyclic groups.  This analysis
  starts with the morphism `Equiv.Perm.OnCycleFactors.θ`, its
  injectivity `Equiv.Perm.OnCycleFactors.θ_injective`, its range
  `Equiv.Perm.OnCycleFactors.θ_range_eq`, and  its cardinality
  `Equiv.Perm.OnCycleFactors.θ_range_card`.

* `Equiv.Perm.nat_card_centralizer g` computes the cardinality
  of the centralizer of `g`

* `Equiv.Perm.card_isConj_mul_eq g`computes the cardinality
  of the conjugacy class of `g`.

* We now can compute the cardinality of the set of permutations with given cycle type.
  The condition for this cardinality to be zero is given by
  `Equiv.Perm.card_of_cycleType_eq_zero_iff`
  which is itself derived from `Equiv.Perm.exists_with_cycleType_iff`.

* `Equiv.Perm.card_of_cycleType_mul_eq m` and `Equiv.Perm.card_of_cycleType m`
  compute this cardinality.

-/

section

variable {G : Type*} [Group G] (g : G)

theorem Subgroup.centralizer_eq_comap_stabilizer :
    Subgroup.centralizer {g} = Subgroup.comap ConjAct.toConjAct.toMonoidHom
      (MulAction.stabilizer (ConjAct G) g) := by
  ext k
  simp only [MulEquiv.toMonoidHom_eq_coe, mem_comap, MonoidHom.coe_coe,
    MulAction.mem_stabilizer_iff]
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, ConjAct.toConjAct_smul]
  rw [eq_comm]
  exact Iff.symm mul_inv_eq_iff_eq_mul

theorem Subgroup.nat_card_centralizer_nat_card_stabilizer :
    Nat.card (Subgroup.centralizer {g}) =
      Nat.card (MulAction.stabilizer (ConjAct G) g) := by
  simp only [← SetLike.coe_sort_coe, Set.Nat.card_coe_set_eq]
  rw [Subgroup.centralizer_eq_comap_stabilizer, Subgroup.coe_comap,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  erw [Set.preimage_equiv_eq_image_symm]
  exact Set.ncard_image_of_injective _ ConjAct.ofConjAct.injective

variable {g} in
lemma Subgroup.mem_centralizer_singleton_iff {k : G} :
    k ∈ Subgroup.centralizer {g} ↔ k * g = g * k := by
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  rw [eq_comm]


end

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
  simp only [Function.comp_apply, Finset.card, Finset.filter_val,
    Multiset.filter_map, Multiset.card_map]
  apply congr_arg
  ext c
  apply congr_arg₂ _ rfl
  apply Multiset.filter_congr
  intro d h
  simp only [Function.comp_apply, eq_comm, Finset.mem_val.mp h, exists_const]

namespace OnCycleFactors

variable (g)

variable {g} in
lemma Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset
    (k : Subgroup.centralizer {g}) (c : g.cycleFactorsFinset) :
    ConjAct.toConjAct (k : Perm α) • (c : Perm α) ∈ g.cycleFactorsFinset := by
  suffices (g.cycleFactorsFinset : Set (Perm α)) =
    (ConjAct.toConjAct (k : Perm α)) • (g.cycleFactorsFinset) by
    rw [← Finset.mem_coe, this]
    simp only [Set.smul_mem_smul_set_iff, Finset.mem_coe, Finset.coe_mem]
  have this := cycleFactorsFinset_conj_eq (ConjAct.toConjAct (k : Perm α)) g
  rw [ConjAct.toConjAct_smul, Subgroup.mem_centralizer_singleton_iff.mp k.prop, mul_assoc] at this
  simp only [mul_right_inv, mul_one] at this
  conv_lhs => rw [this]
  simp only [Finset.coe_smul_finset]

/-- The action by conjugation of `Subgroup.centraliser {g}`
  on the cycles of a given permutation -/
def Subgroup.Centralizer.cycleFactorsFinset_mulAction :
    MulAction (Subgroup.centralizer {g}) g.cycleFactorsFinset where
  smul k c := ⟨ConjAct.toConjAct (k : Perm α) • (c : Perm α),
    Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k c⟩
  one_smul c := by
    rw [← Subtype.coe_inj]
    change ConjAct.toConjAct (1 : Perm α) • (c : Perm α) = c
    simp only [map_one, one_smul]
  mul_smul k l c := by
    simp only [← Subtype.coe_inj]
    change ConjAct.toConjAct (k * l : Perm α) • (c : Perm α) =
      ConjAct.toConjAct (k : Perm α) • (ConjAct.toConjAct (l : Perm α)) • (c : Perm α)
    simp only [map_mul, mul_smul]

/-- The conjugation action of `Subgroup.centralizer {g}` on `g.cycleFactorsFinset` -/
scoped instance : MulAction (Subgroup.centralizer {g}) (g.cycleFactorsFinset) :=
  (Subgroup.Centralizer.cycleFactorsFinset_mulAction g)

/-- The canonical morphism from `Subgroup.centralizer {g}`
  to the group of permutations of `g.cycleFactorsFinset` -/
def toPermHom := MulAction.toPermHom (Subgroup.centralizer {g}) g.cycleFactorsFinset

theorem centralizer_smul_def (k : Subgroup.centralizer {g}) (c : g.cycleFactorsFinset) :
    k • c = ⟨k * c * k⁻¹, Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k c⟩ :=
  rfl

theorem toPermHom_apply (k : Subgroup.centralizer {g}) (c :  g.cycleFactorsFinset) :
    (toPermHom g k c) = k • c := rfl

theorem coe_toPermHom (k : Subgroup.centralizer {g}) (c :  g.cycleFactorsFinset) :
    (toPermHom g k c : Perm α) = k * c * (k : Perm α)⁻¹ := rfl

/-- The range of `Equiv.Perm.OnCycleFactors.toPermHom`.

The equality is proved by `Equiv.Perm.OnCycleFactors.range_eq_range_toPermHom'`. -/
def range_toPermHom' : Subgroup (Perm g.cycleFactorsFinset) where
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
theorem mem_range_toPermHom'_iff {τ : Perm g.cycleFactorsFinset} :
    τ ∈ range_toPermHom' g ↔
      ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card :=
  Iff.rfl

/-- `k : Subgroup.centralizer {g}` belongs to the kernel of `toPermHom g`
iff it commutes with each cycle of `g` -/
theorem mem_ker_toPermHom_iff (k : Subgroup.centralizer {g}) :
    k ∈ (toPermHom g).ker ↔
      ∀ c ∈ g.cycleFactorsFinset, Commute (k : Perm α) c := by
  simp only [toPermHom, MonoidHom.mem_ker, DFunLike.ext_iff]
  simp only [coe_one, id_eq, Subtype.forall]
  apply forall₂_congr
  intro c hc
  simp only [MulAction.toPermHom_apply, toPerm_apply, ← Subtype.coe_inj,
    commute_iff_eq, centralizer_smul_def, InvMemClass.coe_inv,
    mul_inv_eq_iff_eq_mul]

end OnCycleFactors

open OnCycleFactors Subgroup

/-- A `Basis` of a permutation is a choice of an element in each of its cycles -/
class Basis (g : Equiv.Perm α) where
  /-- A choice of elements in each cycle -/
  (toFun : g.cycleFactorsFinset → α)
  /-- For each cycle, the chosen element belongs to the cycle -/
  (mem_support_self' : ∀ c, toFun c ∈ (c : Perm α).support)

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

theorem mem_support_self (c : g.cycleFactorsFinset) :
    a c ∈ (c : Perm α).support := a.mem_support_self' c

theorem injective : Function.Injective a := by
  intro c d h
  rw [← Subtype.coe_inj]
  apply g.cycleFactorsFinset_pairwise_disjoint.eq c.prop d.prop
  simp only [Disjoint, not_forall, not_or]
  use a c
  conv_rhs => rw [h]
  simp only [← Perm.mem_support, a.mem_support_self c, a.mem_support_self d, and_self]

theorem cycleOf_eq (c : g.cycleFactorsFinset) :
    g.cycleOf (a c) = c :=
  (cycle_is_cycleOf (a.mem_support_self c) c.prop).symm

-- The presence of `e` in this definition may look unnecessary but
-- is useful for the definition of `k` below
/-- Given a basis `a` of `g`, this is the basic function that allows
  to define the inverse of `Equiv.Perm.OnCycleFactors.toPerm` :
  `Kf a e ⟨c, i⟩ = (g ^ i) (a (e c))` -/
def Kf (e : range_toPermHom' g) (x : g.cycleFactorsFinset × ℤ) : α :=
  (g ^ x.2) (a ((e : Perm g.cycleFactorsFinset) x.1))

/- -- This version would have been simpler, but doesn't work later
 -- because of the use of Function.extend which requires functions
 -- with *one* argument.
def Kf (a : Equiv.Perm.Basis g) (e : Equiv.Perm g.cycleFactorsFinset)
  (c : g.cycleFactorsFinset) (i : ℤ) : α :=
  (g ^ i) (a (e c))
-/

variable {e e' : range_toPermHom' g} {c d : g.cycleFactorsFinset} {i j : ℤ}

theorem Kf_def :
    Kf a e ⟨c, i⟩ = (g ^ i) (a ((e : Perm g.cycleFactorsFinset) c)) := rfl

theorem Kf_def_zero :
    Kf a e ⟨c, 0⟩ = a ((e: Perm g.cycleFactorsFinset) c) := rfl

theorem Kf_def_one :
    Kf a e ⟨c, 1⟩ = g (a ((e : Perm g.cycleFactorsFinset) c)) := rfl

/-- The multiplicative-additive property of `Equiv.Perm.OnCycleFactors.Kf` -/
theorem Kf_mul_add :
    Kf a (e' * e) ⟨c, i + j⟩ =
      (g ^ i) (Kf a e' ⟨(e : Perm g.cycleFactorsFinset) c, j⟩) := by
  simp only [Kf_def, zpow_add, Submonoid.coe_mul, coe_toSubmonoid, coe_mul, Function.comp_apply]

/-- The additive property of `Equiv.Perm.OnCycleFactors.Kf` -/
theorem Kf_add : Kf a e ⟨c, i + j⟩ = (g ^ i) (Kf a 1 ⟨(e : Perm g.cycleFactorsFinset) c, j⟩) := by
  rw [← Kf_mul_add, one_mul]

/-- The additive property of `Equiv.Perm.OnCycleFactors.Kf` -/
theorem Kf_add' :
    Kf a e ⟨c, i + j⟩ = (g ^ i) (Kf a e ⟨c, j⟩) := by
  rw [← mul_one e, Kf_mul_add, mul_one]
  rfl

theorem cycleOf_Kf_apply_eq :
    g.cycleOf (Kf a e ⟨c, i⟩) = (e : Perm g.cycleFactorsFinset) c := by
  rw [Kf_def, cycleOf_self_apply_zpow, a.cycleOf_eq]

theorem Kf_apply : g (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i + 1⟩ := by
  rw [Kf_def, Kf_def, ← mul_apply, ← zpow_one_add, add_comm 1 i]

theorem Kf_apply_of_eq (hd : d = (e : Perm g.cycleFactorsFinset) c) :
    (d : Perm α) (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i + 1⟩ := by
  -- Kf e ⟨c, i⟩ = (g ^ i) (a (e c)) appartient au cycle de e c
  rw [hd, ← cycleOf_Kf_apply_eq, cycleOf_apply_self, Kf_apply]

theorem Kf_apply_of_ne (hd' : d ≠ (e : Perm g.cycleFactorsFinset) c) :
    (d : Perm α) (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i⟩ := by
  suffices hdc : (d : Perm α).Disjoint ((e : Perm g.cycleFactorsFinset) c : Perm α) by
    apply Or.resolve_right (disjoint_iff_eq_or_eq.mp hdc (Kf a e ⟨c, i⟩))
    rw [← cycleOf_Kf_apply_eq, cycleOf_apply_self, ← cycleOf_eq_one_iff, cycleOf_Kf_apply_eq]
    exact IsCycle.ne_one (mem_cycleFactorsFinset_iff.mp ((e : Perm g.cycleFactorsFinset) c).prop).1
  apply g.cycleFactorsFinset_pairwise_disjoint d.prop ((e : Perm g.cycleFactorsFinset) c).prop
  rw [Function.Injective.ne_iff Subtype.coe_injective]
  exact hd'

theorem Kf_factorsThrough :
    (Kf a e').FactorsThrough (Kf a e) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ He
  suffices hcd : c = d by
    simp only [Kf_def, hcd] at He ⊢
    rw [g.zpow_eq_zpow_on_iff,
      ← cycle_is_cycleOf (a.mem_support_self _) (Finset.coe_mem _),
      mem_range_toPermHom'_iff.mp e.prop] at He
    · rw [g.zpow_eq_zpow_on_iff]
      rw [ ← cycle_is_cycleOf (a.mem_support_self _) (Finset.coe_mem _)]
      · simp only [mem_range_toPermHom'_iff.mp e'.prop]
        exact He
      · rw [← Perm.mem_support, ← cycleOf_mem_cycleFactorsFinset_iff,
        ← cycle_is_cycleOf (a.mem_support_self _) (Finset.coe_mem _)]
        apply Finset.coe_mem
    · rw [← Perm.mem_support, ← cycleOf_mem_cycleFactorsFinset_iff,
        ← cycle_is_cycleOf  (a.mem_support_self _) (Finset.coe_mem _)]
      apply Finset.coe_mem
  -- c = d
  apply_fun g.cycleOf at He
  simpa only [cycleOf_Kf_apply_eq, Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] using He

variable (σ τ : range_toPermHom' g) (c d : g.cycleFactorsFinset) (i j : ℤ)

/-- Given a basis `a` of `g` and a permutation `τ` of `g.cycleFactorsFinset`,
  `Equiv.Perm.Basis.ofPerm a τ` is a permutation that acts by conjugation
  as `τ` on `g.cycleFactorsFinset`

`Equiv.Perm.Basis.ofPerm'  will turn it into a permutation and
`Equiv.Perm.Basis.ofPerm_rightInverse` proves that it acts as requested -/
noncomputable def k : α → α :=
  Function.extend (Kf a (1 : range_toPermHom' g)) (Kf a τ) id

theorem k_apply_Kf_one :
    k a τ (Kf a (1 : range_toPermHom' g) ⟨c, i⟩) = Kf a τ ⟨c, i⟩ :=
  (Kf_factorsThrough a).extend_apply id ⟨c, i⟩

theorem k_apply_basis :
    k a τ (a c) = a ((τ : Perm g.cycleFactorsFinset) c) :=
  k_apply_Kf_one a τ c 0

theorem k_apply_of_not_mem_support {x : α} (hx : x ∉ g.support) :
    k a τ x = x := by
  rw [k, Function.extend_apply']
  · simp only [id_eq]
  · intro hyp
    obtain ⟨⟨c, i⟩, rfl⟩ := hyp
    apply hx
    simp only [Kf_def, zpow_apply_mem_support, coe_one, id_eq]
    apply mem_cycleFactorsFinset_support_le c.prop
    exact mem_support_self a c

theorem mem_support_iff_mem_support_of_mem_cycleFactorsFinset {x : α} :
    x ∈ g.support ↔
    ∃ c ∈ g.cycleFactorsFinset, x ∈ c.support := by
  constructor
  · intro h
    use g.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr h
    rw [mem_support_cycleOf_iff]
    refine ⟨SameCycle.refl g x, h⟩
  · rintro ⟨c, hc, hx⟩
    exact mem_cycleFactorsFinset_support_le hc hx

/- theorem mem_support_iff_exists_Kf (x : α) :
    x ∈ g.support ↔
    ∃ c, ∃ (hc : c ∈ g.cycleFactorsFinset), ∃ i, g.cycleOf x = c ∧ x = Kf a 1 ⟨⟨c,hc⟩, i⟩ := by
  rw [mem_support_iff_mem_support_of_mem_cycleFactorsFinset]
  apply exists_congr
  intro c
  constructor
  · rintro ⟨hc, hx⟩
    use hc
    have hxc : c = g.cycleOf x := cycle_is_cycleOf hx hc
    have ha : a ⟨c, hc⟩ ∈ (g.cycleOf x).support := hxc ▸ (a.mem_support_self _)
    simp only [Subtype.coe_mk, mem_support_cycleOf_iff] at ha
    obtain ⟨i, hi⟩ := ha.1.symm
    use i, hxc.symm, hi.symm
  · rintro ⟨hc, i, hxc, _⟩
    refine ⟨hc, ?_⟩
    rw [← eq_cycleOf_of_mem_cycleFactorsFinset_iff g c hc x]
    exact hxc.symm -/

theorem mem_support_iff_exists_Kf (x : α) :
    x ∈ g.support ↔
    ∃ c : g.cycleFactorsFinset, ∃ i, g.cycleOf x = c ∧ x = Kf a 1 ⟨c, i⟩ := by
  rw [mem_support_iff_mem_support_of_mem_cycleFactorsFinset]
  constructor
  · rintro ⟨c, hc, h⟩
    use ⟨c, hc⟩
    have hxc : c = g.cycleOf x := cycle_is_cycleOf h hc
    have ha : a ⟨c, hc⟩ ∈ (g.cycleOf x).support := hxc ▸ (a.mem_support_self _)
    simp only [Subtype.coe_mk, mem_support_cycleOf_iff] at ha
    obtain ⟨i, hi⟩ := ha.1.symm
    use i, hxc.symm, hi.symm
  · intro h
    obtain ⟨c, i, hxc, hx⟩ := h
    use c, c.prop
    rwa [eq_comm, eq_cycleOf_of_mem_cycleFactorsFinset_iff _ _ c.prop] at hxc

theorem k_commute_zpow_apply (x : α) :
    k a τ ((g ^ j) x) = (g ^ j) (k a τ x) := by
  by_cases hx : x ∈ g.support
  · rw [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, hc, i, hxc, rfl⟩ := hx
    rw [← Kf_add']
    erw [k_apply_Kf_one, k_apply_Kf_one] --  a _ c (j + i)]
    rw [Kf_add']
  · rw [k_apply_of_not_mem_support a τ hx, k_apply_of_not_mem_support a]
    rw [Equiv.Perm.zpow_apply_mem_support]
    exact hx

theorem k_commute_zpow :
    k a τ ∘ (g ^ j : Perm α) = (g ^ j : Perm α) ∘ k a τ := by
  ext x
  simp only [Function.comp_apply, k_commute_zpow_apply a τ]

theorem k_commute :
    k a τ ∘ g = g ∘ k a τ := by
  simpa only [zpow_one] using k_commute_zpow a τ 1

theorem k_apply_Kf :
    k a τ (Kf a σ ⟨c, i⟩) = Kf a (τ * σ) ⟨c, i⟩ := by
  simp only [Kf_def]
  rw [← Function.comp_apply (f := k a τ), k_commute_zpow a τ]
  simp only [k_apply_basis, Submonoid.coe_mul, coe_toSubmonoid, coe_mul, Function.comp_apply]

theorem k_mul : k a σ ∘ k a τ = k a (σ * τ) := by
  ext x
  simp only [Function.comp_apply]
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨_, _, _, _, rfl⟩ := hx
    simp only [k_apply_Kf_one, k_apply_Kf, mul_one]
  · simp only [k_apply_of_not_mem_support a _ hx]

theorem k_one : k a (1 : range_toPermHom' g)= id := by
  ext x
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨_, _, _, _, rfl⟩ := hx
    rw [k_apply_Kf_one, id_eq]
  · simp only [id_eq, k_apply_of_not_mem_support a _ hx]

theorem k_bij : Function.Bijective (k a τ) := by
  simp only [Fintype.bijective_iff_surjective_and_card, and_true,
    Function.surjective_iff_hasRightInverse]
  use k a τ⁻¹
  rw [Function.rightInverse_iff_comp, k_mul a, mul_inv_self, k_one]

theorem k_cycle_apply (x : α) :
    k a τ ((c : Perm α) x) = ((τ : Perm g.cycleFactorsFinset) c : Perm α) (k a τ x) := by
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨d, _, _, rfl⟩ := hx
    by_cases hcd : c = d
    · rw [hcd, a.Kf_apply_of_eq, k_apply_Kf_one, k_apply_Kf_one, ← a.Kf_apply_of_eq rfl]
      simp only [OneMemClass.coe_one, coe_one, id_eq]
    · rw [a.Kf_apply_of_ne hcd, k_apply_Kf_one, a.Kf_apply_of_ne]
      exact (Equiv.injective _).ne_iff.mpr hcd
  · suffices ∀ (c : g.cycleFactorsFinset), (c : Perm α) x = x by
      simp only [this, k_apply_of_not_mem_support a _ hx]
    · intro c
      rw [← not_mem_support]
      exact Finset.not_mem_mono (mem_cycleFactorsFinset_support_le c.prop) hx

/-- Given `a : g.Basis` and a permutation of g.cycleFactorsFinset that
  preserve the lengths of the cycles, the permutation of `α` that
  moves the `Basis` and commutes with `g`
  -/
noncomputable def ofPerm : Perm α :=
  ofBijective (k a τ) (k_bij a τ)

theorem ofPerm_apply (x) :
    (ofPerm a τ) x = k a τ x := rfl

theorem ofPerm_support_le :
    (ofPerm a τ).support ≤ g.support := by
  intro x
  simp only [Perm.mem_support, ne_eq, not_imp_not]
  rw [← Perm.not_mem_support]
  exact k_apply_of_not_mem_support a _

theorem mem_ofPerm_support_iff (x : α) :
    x ∈ (ofPerm a τ).support ↔
      ∃ c : g.cycleFactorsFinset,
        g.cycleOf x = c ∧ c ∈ (τ : Perm g.cycleFactorsFinset).support := by
  by_cases hx : x ∈ g.support
  · obtain ⟨c, i, hc, hci⟩ := (Equiv.Perm.Basis.mem_support_iff_exists_Kf a x).mp hx
    rw [show x ∈ (ofPerm a τ : Perm α).support ↔
      ∃ c : g.cycleFactorsFinset, g.cycleOf x = c ∧ x ∈ (ofPerm a τ : Perm α).support
        from ⟨fun h ↦ ⟨c, hc, h⟩, fun ⟨_, _, h⟩ ↦ h⟩]
    apply exists_congr
    simp only [and_congr_right_iff]
    intro d hd
    have hc' : c = d := Subtype.coe_injective (by simp only [← hc, hd])
    rw [← hc']
    simp only [Equiv.Perm.mem_support, ne_eq, not_iff_not]
    rw [ofPerm_apply]
    simp only [hci, k_apply_Kf_one, Kf_def, k_commute_zpow_apply]
    simp only [OneMemClass.coe_one, coe_one, id_eq, EmbeddingLike.apply_eq_iff_eq, k_apply_basis]
    exact a.injective.eq_iff
  · have := Equiv.Perm.Basis.ofPerm_support_le a τ
    have : x ∉ (ofPerm a τ : Perm α).support := by
      intro hx'; apply hx
      exact Equiv.Perm.Basis.ofPerm_support_le a τ hx'
    simp only [this, mem_support, ne_eq, Subtype.exists, exists_and_left, exists_eq_left',
      false_iff, not_exists, Decidable.not_not]
    intro hc
    simp only [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff] at hc
    contradiction

theorem ofPerm_support :
    (ofPerm a τ).support = Finset.biUnion (τ : Perm g.cycleFactorsFinset).support
        (fun c ↦ (c : Perm α).support) := by
  ext x
  simp only [mem_ofPerm_support_iff a τ, Finset.mem_biUnion, Subtype.exists]
  apply exists_congr; intro c
  apply exists_congr; intro hc
  rw [and_comm, and_congr_right_iff]
  intro _
  constructor
  · intro h
    simpa only [cycleOf_apply_self, ne_eq, ← h,
      cycleOf_mem_cycleFactorsFinset_iff, mem_support] using hc
  · exact fun h ↦ (cycle_is_cycleOf h hc).symm

theorem card_ofPerm_support :
    (ofPerm a τ).support.card =  (τ : Perm g.cycleFactorsFinset).support.sum
        (fun c ↦ (c : Perm α).support.card) := by
  rw [ofPerm_support, Finset.card_biUnion]
  intro c _ d _ h
  apply Equiv.Perm.Disjoint.disjoint_support
  have := g.cycleFactorsFinset_pairwise_disjoint.eq c.prop d.prop
  rw [not_imp_comm] at this
  apply this
  exact Subtype.coe_ne_coe.mpr h


theorem ofPerm_mem_centralizer :
    ofPerm a τ ∈ Subgroup.centralizer {g} := by
  rw [mem_centralizer_singleton_iff, ← DFunLike.coe_fn_eq]
  simp only [coe_mul, ofPerm]
  exact k_commute a τ

/-- Given `a : Equiv.Perm.Basis g`,
we define a right inverse of `Equiv.Perm.OnCycleFactors.toPermHom`,
on `range_toPermHom' g` -/
noncomputable def toCentralizer :
    range_toPermHom' g →* Subgroup.centralizer {g}  where
  toFun τ := ⟨ofPerm a τ, ofPerm_mem_centralizer a τ⟩
  map_one' := by
    simp only [Submonoid.mk_eq_one]
    ext x
    simp only [ofPerm, k_one, ofBijective_apply, id_eq, coe_one]
  map_mul' σ τ := by
    simp only [ofPerm, Submonoid.mk_mul_mk, Subtype.mk.injEq]
    ext x
    simp only [← k_mul a, ofBijective_apply, Function.comp_apply, coe_mul]

theorem toCentralizer_apply (x) :
    (toCentralizer a τ : Perm α) x = k a τ x :=
  rfl

theorem toCentralizer_equivariant :
    (toCentralizer a τ) • c = (τ : Perm g.cycleFactorsFinset) c := by
  rw [centralizer_smul_def, ← Subtype.coe_inj]
  simp only [InvMemClass.coe_inv, mul_inv_eq_iff_eq_mul]
  ext x
  exact k_cycle_apply a τ c x

theorem toCentralizer_rightInverse :
    (OnCycleFactors.toPermHom g) (toCentralizer a τ) = (τ : Perm g.cycleFactorsFinset) := by
  apply ext
  intro c
  rw [OnCycleFactors.toPermHom_apply, toCentralizer_equivariant]

end Basis

namespace OnCycleFactors

open Basis BigOperators Nat Equiv.Perm Equiv Subgroup

theorem mem_range_toPermHom_iff {τ} : τ ∈ (toPermHom g).range ↔
    ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card := by
  constructor
  · rintro ⟨k, rfl⟩ c
    rw [coe_toPermHom, Equiv.Perm.support_conj]
    apply Finset.card_map
  · obtain ⟨a⟩ := Basis.nonempty g
    exact fun hτ ↦ ⟨toCentralizer a ⟨τ, hτ⟩, toCentralizer_rightInverse a ⟨τ, hτ⟩⟩

theorem mem_range_toPermHom_iff' {τ} : τ ∈ (toPermHom g).range ↔
    (fun (c : g.cycleFactorsFinset) ↦ (c : Perm α).support.card) ∘ τ =
      fun (c : g.cycleFactorsFinset) ↦ (c : Perm α).support.card := by
  rw [mem_range_toPermHom_iff, Function.funext_iff]
  simp only [Finset.coe_sort_coe, Subtype.forall, Function.comp_apply]

theorem range_toPermHom_eq_range_toPermHom' : (toPermHom g).range = range_toPermHom' g := by
  ext τ
  rw [mem_range_toPermHom_iff, mem_range_toPermHom'_iff]

theorem nat_card_range_toPermHom :
    Nat.card (toPermHom g).range =
      ∏ n in g.cycleType.toFinset, (g.cycleType.count n)! := by
  classical
  let sc (c : g.cycleFactorsFinset) : ℕ := (c : Perm α).support.card
  suffices Fintype.card (toPermHom g).range =
    Fintype.card { k : Perm g.cycleFactorsFinset | sc ∘ k = sc } by
    simp only [Nat.card_eq_fintype_card, this, Set.coe_setOf,
      DomMulAct.stabilizer_card', ← CycleType.count_def]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext n
    simp only [Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach,
        sc, true_and, Subtype.exists, exists_prop, Multiset.mem_toFinset]
    simp only [cycleType_def, Function.comp_apply, Multiset.mem_map, Finset.mem_val]
  simp only [← SetLike.coe_sort_coe, Fintype.card_eq_nat_card]
  congr
  ext τ
  erw [mem_range_toPermHom_iff'] -- rw doesn't work
  simp only [Finset.coe_sort_coe, Set.mem_setOf_eq]

section Kernel
/- Here, we describe the kernel of `g.OnCycleFactors.toPermHom` -/

open BigOperators Nat OnCycleFactors Subgroup

variable {u k : Perm (Function.fixedPoints g)}
  {v v' : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)}
  {x : α}

lemma pairdisjoint₂ :
    Pairwise fun (i : g.cycleFactorsFinset) (j : g.cycleFactorsFinset) ↦
      ∀ (x y : Perm α), x ∈ zpowers ↑i → y ∈ zpowers ↑j → Disjoint x y :=
  fun c d  hcd ↦ fun x y hx hy ↦ by
  obtain ⟨m, hm⟩ := hx; obtain ⟨n, hn⟩ := hy
  simp only [← hm, ← hn]
  apply Disjoint.zpow_disjoint_zpow
  exact g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop
    (Subtype.coe_ne_coe.mpr hcd)

lemma paircommute₂ :
    Pairwise fun (i : g.cycleFactorsFinset) (j : g.cycleFactorsFinset) ↦
      ∀ (x y : Perm α), x ∈ zpowers ↑i → y ∈ zpowers ↑j → Commute x y :=
  pairdisjoint₂.mono (fun _ _ ↦ forall₂_imp (fun _ _ h hx hy ↦ (h hx hy).commute))

@[to_additive]
lemma _root_.MonoidHom.commute_noncommPiCoprod
    {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, Monoid (H i)] {P : Type*} [Monoid P]
    (f : (i : ι) → H i →* P) (comm) (p : P) (hcomm : ∀ i (x : H i), Commute p (f i x))
    (h : (i : ι) → H i) :
    Commute p (MonoidHom.noncommPiCoprod f comm h) := by
  dsimp only [MonoidHom.noncommPiCoprod, MonoidHom.coe_mk, OneHom.coe_mk]
  apply Finset.noncommProd_induction
  exact fun x y ↦ Commute.mul_right
  exact Commute.one_right _
  exact fun x _ ↦ hcomm x (h x)

lemma _root_.MonoidHom.noncommPiCoprod_apply {ι : Type*} [Fintype ι]
    {H : ι → Type*} [∀ i, Monoid (H i)]
    {P : Type*} [Monoid P] (f : (i : ι) → (H i) →* P) (comm)
    (u : (i : ι) → H i) :
    MonoidHom.noncommPiCoprod f comm u = Finset.noncommProd Finset.univ (fun i ↦ f i (u i))
      (Pairwise.set_pairwise (fun ⦃i j⦄ a ↦ comm a (u i) (u j)) _) := by
  dsimp only [MonoidHom.noncommPiCoprod, MonoidHom.coe_mk, OneHom.coe_mk]

lemma _root_.Subgroup.noncommPiCoprod_apply {G : Type*} [Group G] {ι : Type*} [Fintype ι]
    {H : ι → Subgroup G} (comm) (u : (i : ι) → H i) :
    Subgroup.noncommPiCoprod comm u = Finset.noncommProd Finset.univ (fun i ↦ u i)
      (fun i _ j _ h ↦ comm h _ _ (u i).prop (u j).prop) := by
  simp only [noncommPiCoprod, MonoidHom.noncommPiCoprod,
    coeSubtype, MonoidHom.coe_mk, OneHom.coe_mk]

lemma _root_.Equiv.Perm.support_zpowers_of_mem_cycleFactorsFinset_le
    {c : g.cycleFactorsFinset} (v : zpowers (c : Perm α)) :
    (v : Perm α).support ⊆ g.support := by
  obtain ⟨m, hm⟩ := v.prop
  simp only [← hm]
  apply subset_trans (support_zpow_le _ _) (mem_cycleFactorsFinset_support_le c.prop)

lemma _root_.Equiv.Perm.disjoint_ofSubtype_of_memFixedPoints_self
    (u : Perm (Function.fixedPoints g)) : Disjoint (ofSubtype u) g := by
  rw [disjoint_iff_eq_or_eq]
  intro x
  by_cases hx : x ∈ Function.fixedPoints g
  · right; exact hx
  · left; rw [ofSubtype_apply_of_not_mem u hx]

lemma disjoint₁₂ (u : Perm (Function.fixedPoints ⇑g))
    (v : (c : { x // x ∈ g.cycleFactorsFinset }) → ↥(zpowers (c : Perm α))) :
    Disjoint (ofSubtype u) ((noncommPiCoprod paircommute₂) v) := by
  apply Finset.noncommProd_induction
  · intro a _ b _ h
    apply paircommute₂ h
    simp
    simp
  · intro x y
    exact Disjoint.mul_right
  · exact disjoint_one_right _
  · intro c _
    simp only [coeSubtype]
    exact Disjoint.mono (disjoint_ofSubtype_of_memFixedPoints_self u)
      le_rfl (support_zpowers_of_mem_cycleFactorsFinset_le (v c))

lemma commute₁₂ : ∀ (m : Perm ↑(Function.fixedPoints ⇑g))
    (n : (c : { x // x ∈ g.cycleFactorsFinset }) → ↥(zpowers (c : Perm α))),
    Commute (ofSubtype m) ((noncommPiCoprod paircommute₂) n) :=
  fun u v ↦ Disjoint.commute (disjoint₁₂ u v)

variable (g) in
def θHom : (Perm (Function.fixedPoints g)) ×
        ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)) →*
      Perm α :=
  MonoidHom.noncommCoprod (ofSubtype) (Subgroup.noncommPiCoprod paircommute₂) (commute₁₂)

theorem _root_.Equiv.Perm.support_ofSubtype {p : α → Prop} [DecidablePred p]
    (u : Perm (Subtype p)) :
    (ofSubtype u).support = u.support.map (Function.Embedding.subtype p) := by
  ext x
  simp only [mem_support, ne_eq, Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists,
    exists_and_right, exists_eq_right, not_iff_comm, not_exists, not_not]
  by_cases hx : p x
  · simp only [forall_prop_of_true hx, ofSubtype_apply_of_mem u hx, ← Subtype.coe_inj]
  · simp only [forall_prop_of_false hx, true_iff, ofSubtype_apply_of_not_mem u hx]

variable {ι : Type*} (k : ι → Perm α) (s : Finset ι)
    (hs : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j))

theorem _root_.Equiv.Perm.Disjoint.disjoint_noncommProd
    (f : Perm α) (hf : ∀ i ∈ s, f.Disjoint (k i)) :
    f.Disjoint (s.noncommProd k (hs.imp (fun _ _ ↦ Perm.Disjoint.commute))) :=
      by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ hi]
    apply Equiv.Perm.Disjoint.mul_right (hf i _) (hrec hs' _)
    · simp
    · intro j hj
      exact hf j (Finset.mem_insert_of_mem hj)

theorem _root_.Equiv.Perm.Disjoint.support_noncommProd :
    (s.noncommProd k (hs.imp (fun _ _ ↦ Perm.Disjoint.commute))).support =
      s.biUnion fun i ↦ (k i).support := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ hi, Finset.biUnion_insert]
    rw [Equiv.Perm.Disjoint.support_mul, hrec hs']
    apply Disjoint.disjoint_noncommProd _ _ hs'
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]

theorem _root_.Equiv.Perm.Disjoint.cycleType_mul
    {f g : Perm α} (h : f.Disjoint g) :
    (f * g).cycleType = f.cycleType + g.cycleType := by
  simp only [cycleType]
  rw [h.cycleFactorsFinset_mul_eq_union]
  simp only [Finset.union_val, Function.comp_apply]
  rw [← Multiset.add_eq_union_iff_disjoint.mpr _, Multiset.map_add]
  simp only [Finset.disjoint_val, Disjoint.disjoint_cycleFactorsFinset h]

theorem _root_.Equiv.Perm.Disjoint.cycleType_noncommProd :
    (s.noncommProd k (hs.imp (fun _ _ ↦ Perm.Disjoint.commute))).cycleType =
      s.sum fun i ↦ (k i).cycleType := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ hi, Finset.sum_insert hi]
    rw [Equiv.Perm.Disjoint.cycleType_mul, hrec hs']
    apply Disjoint.disjoint_noncommProd _ _ hs'
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]

theorem support_θHom :
    support (θHom g (u,v)) = u.support.map (Function.Embedding.subtype _) ∪
      Finset.univ.biUnion fun c ↦  support (v c : Perm α) := by
  simp only [θHom, MonoidHom.noncommCoprod_apply]
  rw [Disjoint.support_mul (disjoint₁₂ u v), u.support_ofSubtype]
  apply congr_arg₂ _ rfl
  rw [noncommPiCoprod_apply, Disjoint.support_noncommProd]
  exact fun i _ j _ h ↦ pairdisjoint₂ h _ _ (v i).prop (v j).prop

theorem support_θHom_of_fst_eq_one :
    support (θHom g (u,v)) ⊆ g.support ↔ u = 1 := by
  classical
  rw [support_θHom]
  rw [Finset.union_subset_iff, Finset.biUnion_subset]
  rw [Finset.map_subset_iff_subset_preimage]
  suffices  g.support.preimage (Function.Embedding.subtype _) _ = ∅ by
    rw [this, Finset.subset_empty, Equiv.Perm.support_eq_empty_iff]
    convert and_true_iff _
    rw [iff_true]
    intro c _
    exact support_zpowers_of_mem_cycleFactorsFinset_le (v c)
  ext x
  simp only [Function.Embedding.coe_subtype, Finset.mem_preimage, mem_support, ne_eq,
    Finset.not_mem_empty, iff_false, Decidable.not_not]
  exact x.prop

lemma _root_.Set.disjoint_of_le_iff_left_eq_empty {u v : Set α} (h : u ⊆ v) :
    _root_.Disjoint u v ↔ u = ∅ := by
  simp only [disjoint_iff, inf_eq_left.mpr h, Set.bot_eq_empty]

lemma _root_.Finset.disjoint_of_le_iff_left_eq_empty {u v : Set α} (h : u ⊆ v) :
    _root_.Disjoint u v ↔ u = ∅ := by
  simp only [disjoint_iff, inf_eq_left.mpr h, Set.bot_eq_empty]

lemma _root_.disjoint_of_le_iff_left_eq_bot
    {α : Type*} [SemilatticeInf α] [OrderBot α] {a b : α} (h : a ≤ b) :
    _root_.Disjoint a b ↔ a = ⊥ := by
  simp only [disjoint_iff, inf_eq_left.mpr h]

theorem θHom_disjoint_iff (f : Perm α) :
    Disjoint (θHom g (u,v)) f ↔ Disjoint (ofSubtype u) f ∧ ∀ c, Disjoint (v c : Perm α) f := by
  classical
  simp only [disjoint_iff_disjoint_support, support_θHom, Finset.disjoint_union_left,
    Finset.disjoint_biUnion_left]
  apply and_congr
  · rw [← support_ofSubtype]
  · simp only [Finset.univ_eq_attach, Finset.mem_attach, true_implies, Subtype.forall]

theorem θHom_disjoint_self_iff :
    Disjoint (θHom g (u,v)) g ↔ v = 1 := by
  rw [θHom_disjoint_iff]
  convert true_and_iff _
  · rw [iff_true]
    exact disjoint_ofSubtype_of_memFixedPoints_self u
  · constructor
    · intro hv; simp [hv]
    · rw [Function.funext_iff]
      apply forall_imp
      intro c h
      rw [disjoint_iff_disjoint_support, disjoint_of_le_iff_left_eq_bot _] at h
      simpa only [Finset.bot_eq_empty, support_eq_empty_iff, OneMemClass.coe_eq_one] using h
      exact support_zpowers_of_mem_cycleFactorsFinset_le _

theorem θHom_disjoint_cycle_iff {c : g.cycleFactorsFinset} :
    Disjoint (θHom g (u,v)) c ↔ v c = 1 := by
  rw [θHom_disjoint_iff]
  classical
  convert true_and_iff _
  · rw [iff_true]
    exact Equiv.Perm.Disjoint.mono (disjoint_ofSubtype_of_memFixedPoints_self u) le_rfl
      (mem_cycleFactorsFinset_support_le c.prop)
  · constructor
    · intro hc
      intro d
      by_cases h : c = d
      · rw [← h, hc]; simp
      · apply Disjoint.mono (cycleFactorsFinset_pairwise_disjoint g d.prop c.prop _) _ le_rfl
        exact Subtype.coe_ne_coe.mpr fun a ↦ h (id (Eq.symm a))
        obtain ⟨m, hm⟩ := (v d).prop
        simp only [← hm]
        exact support_zpow_le _ m
    · intro h
      specialize h c
      rw [disjoint_iff_disjoint_support, disjoint_of_le_iff_left_eq_bot _] at h
      simpa using h
      obtain ⟨m, hm⟩ := (v c).prop; simp only [← hm]; exact support_zpow_le _ m

theorem _root_.MulHom.noncommCoprod_apply' {M : Type*} {N : Type*}
    {P : Type*} [Mul M] [Mul N] [Semigroup P]
    (f : M →ₙ* P) (g : N →ₙ* P) (comm : ∀ (m : M) (n : N), Commute (f m) (g n)) (mn : M × N) :
    (f.noncommCoprod g comm) mn = g mn.2 * f mn.1 := by
  rw [← comm, MulHom.noncommCoprod_apply]

theorem _root_.MonoidHom.noncommCoprod_apply' {M : Type*} {N : Type*}
    {P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (f : M →* P) (g : N →* P) (comm : ∀ (m : M) (n : N), Commute (f m) (g n)) (mn : M × N) :
    (f.noncommCoprod g comm) mn = g mn.2 * f mn.1 := by
  rw [← comm, MonoidHom.noncommCoprod_apply]

theorem θHom_apply (x : α) : θHom g (u,v) x =
    if hx : g.cycleOf x ∈ g.cycleFactorsFinset
    then (v ⟨g.cycleOf x, hx⟩ : Perm α) x
    else ofSubtype u x := by
  split_ifs with hx
  · let v' := Function.update v ⟨g.cycleOf x, hx⟩ 1
    let w : (c : g.cycleFactorsFinset) → zpowers (c : Perm α) :=
      Pi.mulSingle (⟨g.cycleOf x, hx⟩ : g.cycleFactorsFinset) (v ⟨g.cycleOf x, hx⟩)
    have : (u, v) = (1, w) * (u, v') := by
      simp only [Prod.mk_mul_mk, one_mul, Prod.mk.injEq, true_and, v', w]
      apply funext
      intro c
      by_cases hc : c = ⟨g.cycleOf x, hx⟩
      · rw [Pi.mul_apply, ← hc, Function.update_same, Pi.mulSingle_eq_same, mul_one]
      · rw [Pi.mul_apply, Function.update_noteq hc, Pi.mulSingle_eq_of_ne hc, one_mul]
    rw [this, map_mul, mul_apply]
    suffices θHom g (u,v') x = x by
      rw [this]
      simp only [θHom, MonoidHom.noncommCoprod_apply, map_one, one_mul]
      simp only [w, Subgroup.noncommPiCoprod_mulSingle]
    suffices Equiv.Perm.Disjoint (θHom g (u,v')) (⟨g.cycleOf x, hx⟩ : g.cycleFactorsFinset) by
      rw [Equiv.Perm.disjoint_iff_eq_or_eq] at this
      apply Classical.or_iff_not_imp_right.mp (this x)
      simp only [cycleOf_apply_self]
      rwa [cycleOf_mem_cycleFactorsFinset_iff, mem_support] at hx
    rw [θHom_disjoint_cycle_iff]
    simp only [v', Function.update_same]
  · rw [show (u, v) = (u, 1) * (1, v) by rfl, map_mul, mul_apply]
    rw [cycleOf_mem_cycleFactorsFinset_iff] at hx
    suffices θHom g (1,v) x = x by
      rw [this]
      simp only [θHom, MonoidHom.noncommCoprod_apply, map_one, mul_one]
    have hv : support (θHom g (1,v)) ⊆ support g := by
      rw [support_θHom_of_fst_eq_one]
    rw [← not_mem_support]
    exact fun a ↦ hx (hv a)

theorem θHom_apply_of_cycleOf_eq {x : α} {c : g.cycleFactorsFinset}
    (hx : x ∈ (c : Perm α).support) : θHom g (u,v) x = (v c : Perm α) x := by
  sorry

theorem θHom_apply_of_cycleOf_not_mem {x : α} (hx : g.cycleOf x ∉ g.cycleFactorsFinset) :
    θHom g (u,v) x = ofSubtype u x := by
  sorry

/- variable (k) (v) (x) in
/-- An auxiliary function to define the parametrization
of the kernel of `g.OnCycleFactors.toPerm` -/
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
-/

/-
section

variable (u :Perm (Function.fixedPoints ⇑g))
  (v : (c : g.cycleFactorsFinset) → ↥(zpowers (c : Perm α)))
  (k : Perm α) (hk : k = θ g ⟨u, v⟩)

theorem cycleType_θ_left :
    ((θ g) (u, 1)).cycleType = u.cycleType := by
  unfold θ θFun θAux
  simp only [Pi.inv_apply, InvMemClass.coe_inv, map_inv, MonoidHom.coe_mk, OneHom.coe_mk,
    Pi.one_apply, OneMemClass.coe_one, coe_one, id_eq, dite_eq_ite, inv_one]
  sorry

theorem cycleType_θ
    (k : Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)) :
    cycleType (θ g ⟨k, v⟩) = cycleType k +
        Finset.univ.sum fun c => cycleType (v c : Perm α) :=  by
  rw [← Prod.fst_mul_snd ⟨k, v⟩]
  simp only [map_mul]
  suffices huv : Disjoint _ _ by
    conv_lhs => simp only [cycleType]
    rw [Disjoint.cycleFactorsFinset_mul_eq_union huv]
    simp only [Finset.union_val]
    rw [← Multiset.add_eq_union_iff_disjoint.mpr _]
    simp only [Function.comp_apply, Multiset.map_add]

    sorry
    sorry
  sorry
  /- apply congr_arg₂
  · simp only [θ_apply_fst, sign_ofSubtype]
  · rw [← MonoidHom.inr_apply, ← MonoidHom.comp_apply]
    conv_lhs => rw [← Finset.noncommProd_mul_single v]
    simp only [Finset.map_noncommProd]
    rw [Finset.noncommProd_eq_prod]
    apply Finset.prod_congr rfl
    intro c _
    simp only [MonoidHom.inr_apply, MonoidHom.coe_comp, Function.comp_apply]
    rw [θ_apply_single_zpowers] -/


example (x : α) (hx : x ∈ Function.fixedPoints g) :
    (k.cycleOf x).support.card = (u.cycleOf ⟨x, hx⟩).support.card := by
  sorry

example (x : α) (c : g.cycleFactorsFinset) (hx : g.cycleOf x = c) :
    (k.cycleOf x).support.card = 0 := sorry

end -/

/-
theorem θ_apply_mem_support_iff (uv) (x : α) (c : g.cycleFactorsFinset) :
    θ g uv x ∈ (c : Perm α).support ↔ x ∈ (c : Perm α).support := by
  by_cases hx : x ∈ g.support
  · obtain ⟨d, hd, hx⟩ := mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hx
    by_cases hcd : c = d
    · simp only [hcd, hx, iff_true]
      rw [θ_apply_of_cycleOf_eq _ x ⟨d, hd⟩]
      sorry
      sorry
    · sorry
  · rw [not_mem_support, ← Function.mem_fixedPoints_iff] at hx
    rw [θ_apply_of_mem_fixedPoints _ _ hx, ← not_iff_not]
    suffices ∀ y (_ : y ∈ Function.fixedPoints g), y ∉ (c : Perm α).support by
      simp only [this x hx, not_false_eq_true, iff_true, this _ (Subtype.coe_prop _)]
    intro y hy
    rw [Function.mem_fixedPoints_iff, ← not_mem_support] at hy
    intro hy'; apply hy
    exact mem_cycleFactorsFinset_support_le c.prop hy'

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
-/

theorem θHom_injective (g : Perm α) : Function.Injective (θHom g) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro (u,v)
  simp only [MonoidHom.mem_ker, mem_bot, Prod.mk_eq_one]
  suffices ∀ (f : Perm α), f = 1 ↔ Disjoint f g ∧ f.support ⊆ g.support by
    rw [this, θHom_disjoint_self_iff, and_comm (a := u = 1)]
    rintro ⟨rfl, h⟩
    rw [support_θHom_of_fst_eq_one] at h
    refine ⟨rfl, h⟩
  intro f
  constructor
  · intro h; simp [h]
  · rintro ⟨h, h'⟩
    rwa [disjoint_iff_disjoint_support, disjoint_of_le_iff_left_eq_bot h',
      Finset.bot_eq_empty, support_eq_empty_iff] at h

theorem mem_θHom_range_iff {p : Perm α} : p ∈ (θHom g).range ↔
    (∃ (hp : p ∈ Subgroup.centralizer {g}),
      (⟨p, hp⟩ : Subgroup.centralizer {g}) ∈ (toPermHom g).ker) := by
  constructor
  · rintro ⟨⟨u, v⟩, h⟩
    simp only [mem_ker_toPermHom_iff, IsCycle.forall_commute_iff]
    have H : ∀ c ∈ g.cycleFactorsFinset, ∀ x, (x ∈ c.support ↔ p x ∈ c.support) := fun c hc x ↦ by
      simp only [← eq_cycleOf_of_mem_cycleFactorsFinset_iff g c hc]
      rw [← h]
      rw [θHom_apply]
      split_ifs with hx
      · obtain ⟨m, hm⟩ := (v ⟨g.cycleOf x, hx⟩).prop
        simp only [← hm, cycleOf_zpow_apply_self, cycleOf_self_apply_zpow]
      · simp only [ne_of_mem_of_not_mem hc hx, false_iff]
        suffices g.cycleOf (ofSubtype u x) = 1 by
          rw [mem_cycleFactorsFinset_iff] at hc
          rw [this]
          exact hc.1.ne_one
        rw [cycleOf_mem_cycleFactorsFinset_iff, not_mem_support,
          ← Function.mem_fixedPoints_iff] at hx
        rw [cycleOf_eq_one_iff, ← Function.mem_fixedPoints_iff, ofSubtype_apply_of_mem u hx]
        exact Subtype.coe_prop (u ⟨x, hx⟩)
    have H1 (c) (hc : c ∈ g.cycleFactorsFinset) (x) (hx : x ∈ c.support) :
        θHom g (u, v) x = (v ⟨c, hc⟩ : Perm α) x := by
      suffices hx' : _ by
        rw [θHom_apply, dif_pos hx']
        suffices (⟨g.cycleOf x, hx'⟩ : g.cycleFactorsFinset) = ⟨c, hc⟩ by
          rw [this]
        simp [← Subtype.coe_inj, Subtype.coe_eta, cycle_is_cycleOf hx hc]
      rw [cycleOf_mem_cycleFactorsFinset_iff]
      exact mem_cycleFactorsFinset_support_le hc hx

    have H' : ∀ c (hc : c ∈ g.cycleFactorsFinset),
      ofSubtype (p.subtypePerm (H c hc)) ∈ zpowers c := fun c hc ↦ by
      suffices ofSubtype (subtypePerm p _) = v ⟨c, hc⟩ by
        rw [this]
        exact (v _).prop
      ext x
      by_cases hx : x ∈ c.support
      · rw [ofSubtype_apply_of_mem, subtypePerm_apply]
        · dsimp only [id_eq, MonoidHom.coe_mk, OneHom.coe_mk, coe_fn_mk, eq_mpr_eq_cast]
          rw [← h, H1 c hc x hx]
        · exact hx
      · rw [ofSubtype_apply_of_not_mem]
        · obtain ⟨m, hm⟩ := (v ⟨c, hc⟩).prop
          rw [← hm, eq_comm, ← not_mem_support]
          intro hx'
          apply hx
          exact (support_zpow_le c m) hx'
        · exact hx

    have hp : ∀ c ∈ g.cycleFactorsFinset, p * c = c * p := by
      intro c hc
      ext x
      simp only [id_eq, coe_mul, Function.comp_apply]
      by_cases hx : x ∈ c.support
      · -- set w := v ⟨c, hc⟩
        -- have hxc : c = g.cycleOf x := cycle_is_cycleOf hx hc
        rw [← h, H1 c hc x hx, H1 c hc _ (by simp only [apply_mem_support, hx])]
        simp only [← mul_apply]
        apply DFunLike.congr_fun
        rw [← commute_iff_eq]
        obtain ⟨m, hm⟩ := (v ⟨c, hc⟩).prop
        simp only [← hm]
        exact Commute.zpow_left rfl m

      · rw [not_mem_support.mp hx]
        rw [H c hc x] at hx
        rw [not_mem_support.mp hx]
    have hp' : p ∈ centralizer {g} := by
      simp only [mem_centralizer_singleton_iff, ← commute_iff_eq]
      rw [← g.cycleFactorsFinset_noncommProd]
      apply Finset.noncommProd_commute
      intro c hc
      simp only [id_eq]
      exact hp c hc
    use hp'
    intro c hc
    exact ⟨H c hc, H' c hc⟩
  · rintro ⟨hp_mem, hp⟩
    simp only [mem_ker_toPermHom_iff, IsCycle.forall_commute_iff] at hp
    rw [MonoidHom.mem_range]
    have hu : ∀ x : α,
      x ∈ Function.fixedPoints g ↔ p x ∈ Function.fixedPoints g :=  by
      intro x
      simp only [Function.fixedPoints, smul_def, Function.IsFixedPt]
      simp only [← not_mem_support]
      simp only [Set.mem_setOf_eq, not_iff_not]
      constructor
      · intro hx
        let hx' := cycleOf_mem_cycleFactorsFinset_iff.mpr hx
        apply mem_cycleFactorsFinset_support_le hx'
        obtain ⟨hp'⟩ := hp (g.cycleOf x) hx'
        rw [← hp' x, Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hx⟩
      · intro hzx
        let hzx' := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hzx
        apply Equiv.Perm.mem_cycleFactorsFinset_support_le hzx'
        obtain ⟨hp'⟩ := hp (g.cycleOf (p x)) hzx'
        rw [hp' x, Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hzx⟩
    set u := subtypePerm p hu
    set v : (c : g.cycleFactorsFinset) → (Subgroup.zpowers (c : Perm α)) :=
      fun c => ⟨ofSubtype
          (p.subtypePerm (Classical.choose (hp c.val c.prop))),
            Classical.choose_spec (hp c.val c.prop)⟩
    use ⟨u, v⟩
    ext x
    rw [θHom_apply]
    split_ifs with hx
    · simp only [v]
      rw [ofSubtype_apply_of_mem]
      rfl
      rw [cycleOf_mem_cycleFactorsFinset_iff, mem_support] at hx
      rwa [mem_support, cycleOf_apply_self, ne_eq]
    · simp only [u]
      rw [ofSubtype_apply_of_mem, subtypePerm_apply]
      rw [cycleOf_mem_cycleFactorsFinset_iff, not_mem_support] at hx
      exact hx

lemma θHom_range_le_centralizer : (θHom g).range ≤ centralizer {g} := fun p hp ↦ by
    rw [mem_θHom_range_iff] at hp
    obtain ⟨hp, _⟩ := hp
    exact hp

lemma θHom_range_eq : (θHom g).range = (toPermHom g).ker.map (Subgroup.subtype _) := by
  ext p
  simp only [mem_θHom_range_iff, mem_map, coeSubtype, Subtype.exists,
    exists_and_right, exists_eq_right]

theorem θHom_range_card (g : Equiv.Perm α) :
    Fintype.card (θHom g).range =
      (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod := by
  change Fintype.card ((θHom g).range : Set (Equiv.Perm α)) = _
  simp only [MonoidHom.coe_range]
  rw [Set.card_range_of_injective (θHom_injective g)]
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

/- lemma θHom_apply_fst (k : Perm (Function.fixedPoints g)) :
    θHom g ⟨k, 1⟩ = ofSubtype k := by
  ext x
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [θ_apply_of_cycleOf_eq _ x ⟨g.cycleOf x, hx⟩ rfl]
    simp only [Pi.one_apply, OneMemClass.coe_one, coe_one, id_eq]
    rw [ofSubtype_apply_of_not_mem]
    simpa [cycleOf_mem_cycleFactorsFinset_iff, Perm.mem_support] using hx
  · rw [cycleOf_mem_cycleFactorsFinset_iff, Perm.not_mem_support] at hx
    rw [θ_apply_of_mem_fixedPoints _ x hx, Equiv.Perm.ofSubtype_apply_of_mem]

lemma θ_apply_single_zpowers
    (c : g.cycleFactorsFinset) (vc : Subgroup.zpowers (c : Equiv.Perm α)) :
    θ g ⟨1, Pi.mulSingle c vc⟩ = (vc : Equiv.Perm α) := by
  obtain ⟨m, hm⟩ := vc.prop
  simp only at hm
  suffices vc = ⟨(c : Perm α), mem_zpowers _⟩ ^ m by
    rw [this, ← one_zpow m, Pi.mulSingle_zpow, ← Prod.pow_mk, map_zpow,
      θ_apply_single, SubgroupClass.coe_zpow]
  rw [← Subtype.coe_inj, ← hm, SubgroupClass.coe_zpow]
-/

end Kernel

end OnCycleFactors

open Nat
variable (g)

-- Should one parenthesize the product ?
/-- Cardinality of the centralizer in `Equiv.Perm α` of a permutation given `cycleType` -/
theorem nat_card_centralizer :
    Nat.card (Subgroup.centralizer {g}) =
      (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!) := by
  classical
  rw [card_eq_card_quotient_mul_card_subgroup (OnCycleFactors.toPermHom g).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (toPermHom g)).toEquiv,
    nat_card_range_toPermHom, mul_comm]
  apply congr_arg₂ _ _ rfl
  rw [← θHom_range_card, ← Nat.card_eq_fintype_card]
  simp only [← SetLike.coe_sort_coe, Set.Nat.card_coe_set_eq]
  rw [θHom_range_eq, coe_map, Set.ncard_image_of_injective _ (subtype_injective _)]

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
  rw [← nat_card_centralizer g, mul_comm,
    Subgroup.nat_card_centralizer_nat_card_stabilizer, Nat.card_eq_fintype_card]
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
  · rw [← nat_card_centralizer g]
    apply Nat.card_pos

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




#exit

@[to_additive]
theorem _root_.Finset.commute_noncommProd_left
    {ι M : Type*} [Monoid M] {f : ι → M} {s : Finset ι}
    {m : M} (hm : ∀ i ∈ s, Commute m (f i))
    (hf : Set.Pairwise s (fun i j ↦ Commute (f i) (f j))) :
    Commute (s.noncommProd f hf) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his hrec =>
    have hf' : Set.Pairwise s (fun i j ↦ Commute (f i) (f j)) :=
      hf.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    have hm' : ∀ i ∈ s, Commute m (f i) := fun i hi ↦ hm i (Finset.mem_insert_of_mem hi)
    rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ his]
    exact Commute.mul_left (hm i (Finset.mem_insert_self i s)).symm (hrec hm' hf')

@[to_additive]
theorem _root_.Finset.commute_noncommProd_right
    {ι M : Type*} [Monoid M] {f : ι → M} {s : Finset ι}
    {m : M} (hm : ∀ i ∈ s, Commute m (f i))
    (hf : Set.Pairwise s (fun i j ↦ Commute (f i) (f j))) :
    Commute m (s.noncommProd f hf) :=
  (Finset.commute_noncommProd_left hm hf).symm

@[to_additive]
theorem _root_.Finset.noncommProd_mul
    {ι M : Type*} [Monoid M] {f : ι → M} {g : ι → M}
    {s : Finset ι}
    (hf : Set.Pairwise s (fun i j ↦ Commute (f i) (f j)))
    (hg : Set.Pairwise s (fun i j ↦ Commute (g i) (g j)))
    (hfg : ∀ i ∈ s, ∀ j ∈ s, Commute (f i) (g j)) :
    s.noncommProd (fun i ↦ f i * g i) (fun i hi j hj h ↦
      Commute.mul_left
        (Commute.mul_right (hf hi hj h) (hfg i hi j hj))
        (Commute.mul_right (hfg j hj i hi).symm (hg hi hj h))) =
      s.noncommProd (fun i ↦ f i) hf * s.noncommProd (fun i ↦ g i) hg := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his hrec =>
    have hf' : Set.Pairwise s (fun i j ↦ Commute (f i) (f j)) :=
      hf.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    have hg' : Set.Pairwise s (fun i j ↦ Commute (g i) (g j)) :=
      hg.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    have hfg' : ∀ i ∈ s, ∀ j ∈ s, Commute (f i) (g j) := fun i hi j hj ↦
      hfg i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    simp only [Finset.noncommProd_insert_of_not_mem _ _ _ _ his]
    simp only [mul_assoc]; apply congr_arg₂ _ rfl
    rw [hrec hf' hg' hfg']
    simp only [← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [← commute_iff_eq]
    apply Finset.commute_noncommProd_right
    exact fun j hj ↦ (hfg j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i s)).symm

@[to_additive]
theorem _root_.Finset.noncommProd_eq_one {ι M : Type*} [Monoid M] {f : ι → M}
    {s : Finset ι}
    (hs : Set.Pairwise s (fun i j ↦ Commute (f i) (f j)))
    (hs' : ∀ i ∈ s, f i = 1) :
    s.noncommProd f hs = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his hrec =>
    have hs : Set.Pairwise s fun i j ↦ Commute (f i) (f j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ his, hrec hs, mul_one, hs']
    exact Finset.mem_insert_self i s
    exact fun j hj ↦ hs' j (Finset.mem_insert_of_mem hj)

lemma v_disjoint : Set.Pairwise (Finset.univ : Finset g.cycleFactorsFinset)
    fun a b ↦ Disjoint (v a : Perm α) (v' b : Perm α) := by
  intro a _ b _ h
  obtain ⟨m, hm⟩ := (v a).prop
  obtain ⟨n, hn⟩ := (v' b).prop
  rw [← hm, ← hn]
  simp only
  apply Disjoint.zpow_disjoint_zpow
  apply g.cycleFactorsFinset_pairwise_disjoint a.prop b.prop
  exact Subtype.coe_ne_coe.mpr h

@[to_additive]
theorem _root_.Finset.noncommProd_eq_single {ι M : Type*} [Monoid M] {f : ι → M}
    {s : Finset ι}
    (hfs : Set.Pairwise s (fun i j ↦ Commute (f i) (f j)))
    {i : ι} (hi : i ∈ s) (hfis : ∀ j ∈ s, j ≠ i → f j = 1) :
    s.noncommProd f hfs = f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exfalso; contradiction
  | @insert j s hjs hrec =>
    have hfs' : Set.Pairwise s (fun i j ↦ Commute (f i) (f j)) :=
      hfs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ hjs]
    by_cases h : j = i
    · simp only [h]
      convert mul_one _
      apply Finset.noncommProd_eq_one
      intro k hk
      apply hfis k (Finset.mem_insert_of_mem hk)
        <| h.symm ▸ ne_of_mem_of_not_mem hk hjs
    · rw [hfis j (s.mem_insert_self j) h, one_mul, hrec hfs']
      · apply Finset.mem_of_mem_insert_of_ne hi (Ne.symm h)
      · intro k hk
        exact hfis k (s.mem_insert_of_mem hk)

lemma v_commute : Set.Pairwise (Finset.univ : Finset g.cycleFactorsFinset)
    fun a b ↦ Commute (v a : Perm α) (v' b : Perm α) :=
  v_disjoint.imp (fun _ _ ↦ Perm.Disjoint.commute)

variable {ι : Type*} (k : ι → Perm α) (s : Finset ι)
    (hs : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j))

example : (s : Set ι).Pairwise fun i j ↦ Commute (k i) (k j) :=
  hs.imp (fun _ _ ↦ Perm.Disjoint.commute)

variable (u v) in
lemma disjoint_θu_θv : Disjoint (ofSubtype u)
    (Finset.univ.noncommProd (fun c ↦ (v c : Perm α)) v_commute) := by
  apply Equiv.Perm.Disjoint.disjoint_noncommProd _ _ (by exact v_disjoint)
  intro c _
  obtain ⟨m, hm⟩ := (v c).prop
  rw [← hm, ← zpow_one (ofSubtype u)]
  apply Equiv.Perm.Disjoint.zpow_disjoint_zpow
  intro x
  rw [Classical.or_iff_not_imp_right, ← ne_eq, ← mem_support]
  intro hx
  apply Equiv.Perm.ofSubtype_apply_of_not_mem
  rw [Function.mem_fixedPoints_iff, ← ne_eq, ← Equiv.Perm.mem_support]
  exact mem_cycleFactorsFinset_support_le c.prop hx

def newθ : Perm α := (ofSubtype u) *
    (Finset.univ.noncommProd (fun c ↦ (v c : Perm α)) v_commute)

lemma pairdisjoint : Pairwise fun (c : g.cycleFactorsFinset) d ↦
  ∀ (x : ↥(zpowers (c : Perm α))) (y : ↥(zpowers (d : Perm α))),
    Disjoint (((fun c ↦ (zpowers (c : Perm α)).subtype) c) x)
      (((fun c ↦ (zpowers (c : Perm α)).subtype) d) y) := fun c d hcd ↦
  fun x y ↦ by
  simp only [coeSubtype]
  obtain ⟨m, hm⟩ := x.prop; obtain ⟨n, hn⟩ := y.prop
  simp only [← hm, ← hn]
  apply Disjoint.zpow_disjoint_zpow
  exact g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop
    (Subtype.coe_ne_coe.mpr hcd)

lemma paircommute : Pairwise fun (c : g.cycleFactorsFinset) d ↦
  ∀ (x : ↥(zpowers (c : Perm α))) (y : ↥(zpowers (d : Perm α))),
    Commute (((fun c ↦ (zpowers (c : Perm α)).subtype) c) x)
      (((fun c ↦ (zpowers (c : Perm α)).subtype) d) y) :=
  Pairwise.mono pairdisjoint (fun _ _ ↦ forall₂_imp (fun _ _ ↦ Disjoint.commute))

lemma pairdisjoint' (u : Perm ↑(Function.fixedPoints ⇑g))
    (v : (c : { x // x ∈ g.cycleFactorsFinset }) → ↥(zpowers (c : Perm α))) :
    Disjoint (ofSubtype u)
      ((MonoidHom.noncommPiCoprod (fun c ↦ Subgroup.subtype _)  paircommute) v) := by
  sorry

lemma paircommute' (u : Perm ↑(Function.fixedPoints ⇑g))
    (v : (c : { x // x ∈ g.cycleFactorsFinset }) → ↥(zpowers (c : Perm α))) :
    Commute (ofSubtype u)
      ((MonoidHom.noncommPiCoprod (fun _ ↦ Subgroup.subtype _)  paircommute) v) :=
  (pairdisjoint' u v).commute

def renewθHom : (Perm (Function.fixedPoints g)) ×
        ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)) →*
      Perm α :=
  MonoidHom.noncommCoprod (ofSubtype)
    (MonoidHom.noncommPiCoprod (fun c ↦ Subgroup.subtype _) (paircommute))
    (sorry)

lemma pairdisjoint₂ :
    Pairwise fun (i : g.cycleFactorsFinset) (j : g.cycleFactorsFinset) ↦
      ∀ (x y : Perm α), x ∈ zpowers ↑i → y ∈ zpowers ↑j → Disjoint x y :=
  fun c d  hcd ↦ fun x y hx hy ↦ by
  obtain ⟨m, hm⟩ := hx; obtain ⟨n, hn⟩ := hy
  simp only [← hm, ← hn]
  apply Disjoint.zpow_disjoint_zpow
  exact g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop
    (Subtype.coe_ne_coe.mpr hcd)

example (p q : α → Prop) (u v : α → α → Prop) (h : ∀ x y, u x y → v x y)
  (H : ∀ x y, p x → q y → u x y) : (∀ x y, p x → q y → v x y) := by
  exact fun x y a b ↦ h x y (H x y a b)

lemma paircommute₂ :
    Pairwise fun (i : g.cycleFactorsFinset) (j : g.cycleFactorsFinset) ↦
      ∀ (x y : Perm α), x ∈ zpowers ↑i → y ∈ zpowers ↑j → Commute x y :=
  pairdisjoint₂.mono (fun _ _ ↦ forall₂_imp (fun _ _ h hx hy ↦ (h hx hy).commute))

example : ((c : { x // x ∈ g.cycleFactorsFinset }) → (zpowers (c : Perm α)))
    →* Perm α := by
  exact Subgroup.noncommPiCoprod
    (H := fun (c : g.cycleFactorsFinset) ↦ zpowers (c : Perm α))  paircommute₂

lemma MonoidHom.commute_noncommPiCoprod
    {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, Monoid (H i)] {P : Type*} [Monoid P]
    (f : (i : ι) → H i →* P) (comm) (p : P) (hcomm : ∀ i (x : H i), Commute p (f i x))
    (h : (i : ι) → H i) :
    Commute p (MonoidHom.noncommPiCoprod f comm h) := by
  dsimp only [MonoidHom.noncommPiCoprod, MonoidHom.coe_mk, OneHom.coe_mk]
  apply Finset.noncommProd_induction
  exact fun x y ↦ Commute.mul_right
  exact Commute.one_right _
  exact fun x _ ↦ hcomm x (h x)

lemma disjoint₁₂ : ∀ (m : Perm ↑(Function.fixedPoints ⇑g))
    (n : (c : { x // x ∈ g.cycleFactorsFinset }) → ↥(zpowers (c : Perm α))),
    Disjoint (ofSubtype m) ((noncommPiCoprod paircommute₂) n) := by
  intro u v
  dsimp only [noncommPiCoprod, MonoidHom.coe_mk, OneHom.coe_mk]
  apply Finset.noncommProd_induction
  · intro a _ b _ h
    apply paircommute₂ h
    simp
    simp
  · intro x y
    exact Disjoint.mul_right
  · exact disjoint_one_right _
  · intro c _
    simp only [coeSubtype]
    obtain ⟨m, hm⟩ := (v c).prop
    rw [← hm, ← zpow_one (ofSubtype u)]
    apply Equiv.Perm.Disjoint.zpow_disjoint_zpow
    intro x
    rw [Classical.or_iff_not_imp_right, ← ne_eq, ← mem_support]
    intro hx
    apply Equiv.Perm.ofSubtype_apply_of_not_mem
    rw [Function.mem_fixedPoints_iff, ← ne_eq, ← Equiv.Perm.mem_support]
    exact mem_cycleFactorsFinset_support_le c.prop hx

def renewθHom' : (Perm (Function.fixedPoints g)) ×
        ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)) →*
      Perm α :=
  MonoidHom.noncommCoprod (ofSubtype) (Subgroup.noncommPiCoprod paircommute₂)
    (sorry)

def newθHom : (Perm (Function.fixedPoints g)) ×
        ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)) →*
      Perm α where
  toFun uv := (ofSubtype uv.1) *
    (Finset.univ.noncommProd (fun c ↦ (uv.2 c : Perm α)) v_commute)
  map_one' := by
    simp only [Prod.fst_one, map_one, Prod.snd_one, Pi.one_apply,
      OneMemClass.coe_one, one_mul]
    apply Finset.noncommProd_eq_one
    simp
  map_mul' uv uv' := by
    simp only [Prod.fst_mul, map_mul, Prod.snd_mul, Pi.mul_apply]
    simp only [Submonoid.coe_mul, coe_toSubmonoid]
    have := (disjoint_θu_θv uv'.1 uv.2).commute
    rw [commute_iff_eq] at this
    conv_rhs => rw [mul_assoc]
    nth_rewrite 2 [← mul_assoc]
    rw [← this]
    simp only [mul_assoc]
    congr
    apply Finset.noncommProd_mul
    intro i _ j _
    obtain ⟨m, hm⟩ := (uv.2 i).prop
    obtain ⟨n, hn⟩ := (uv'.2 j).prop
    simp only [← hm, ← hn]
    apply Commute.zpow_zpow
    by_cases h : (i : Perm α) = j
    · rw [h]; apply Commute.refl
    · exact g.cycleFactorsFinset_mem_commute i.prop j.prop h

variable (uv : (Perm (Function.fixedPoints g)) ×
        ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)))

theorem newθHom_apply_fst (u : Perm (Function.fixedPoints g)) :
    newθHom (u, 1) = ofSubtype u := by
  simp only [newθHom, MonoidHom.coe_mk, OneHom.coe_mk, Pi.one_apply,
    OneMemClass.coe_one, mul_right_eq_self]
  apply Finset.noncommProd_eq_one
  exact fun _ _ ↦ rfl

theorem newθHom_apply_single (c : g.cycleFactorsFinset) (w : Subgroup.zpowers (c : Perm α)) :
    newθHom (1, Function.update (fun _ ↦ 1) c w) = w := by
  simp only [newθHom, MonoidHom.coe_mk, OneHom.coe_mk, map_one,
    one_mul]
  rw [Finset.noncommProd_eq_single _ (Finset.mem_univ c)]
  · rw [Function.update_same]
  · intro j _ hj
    rw [Function.update_noteq hj, OneMemClass.coe_one]

theorem newθHom_support : support (newθHom uv) =
    ((support uv.1).map (Function.Embedding.subtype _)) ∪
      (Finset.univ.biUnion
        fun (c : g.cycleFactorsFinset) ↦  support (uv.2 c : Perm α)) := by
  classical
  simp only [newθHom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Equiv.Perm.Disjoint.support_mul (disjoint_θu_θv uv.1 uv.2),
    Equiv.Perm.Disjoint.support_noncommProd]
  congr
  · ext x
    by_cases hx : x ∈ Function.fixedPoints g
    · rw [mem_support, ofSubtype_apply_of_mem uv.1 hx]
      have : (uv.1 ⟨x, hx⟩ : α) ≠ x ↔ ⟨x, hx⟩ ∈ support uv.1 := by
        rw [mem_support, not_iff_not, ← Subtype.coe_inj]
      rw [this]
      simp only [Finset.mem_map, Function.Embedding.coe_subtype,
        Subtype.exists, exists_and_right, exists_eq_right]
      rw [exists_prop_of_true hx]
    · rw [mem_support, ofSubtype_apply_of_not_mem uv.1 hx]
      simp only [ne_eq, not_true_eq_false, Finset.mem_map,
        Function.Embedding.coe_subtype, Subtype.exists, exists_and_right,
        exists_eq_right, false_iff, exists_prop_of_false hx]
  · exact v_disjoint

theorem newθHom_apply_of_cycleOf_eq
    (c : g.cycleFactorsFinset) (hx : g.cycleOf x = ↑c) :
    newθHom uv x = (uv.2 c : Perm α) x := by
  rcases uv with ⟨u, v⟩
  set v' := Function.update v c 1 with hv'
  set w := Function.update (fun (c : g.cycleFactorsFinset) ↦
    (1 : zpowers (c : Perm α))) c (v c) with hw
  suffices (u, v) = (1, w) * (u, v') by
    rw [this, map_mul, mul_apply]
    simp only [Prod.mk_mul_mk, one_mul, Pi.mul_apply, Submonoid.coe_mul, coe_toSubmonoid, coe_mul,
      Function.comp_apply]
    suffices (newθHom (u, v')) x = x by
      rw [this]
      suffices (v' c : Perm α) x = x by
        rw [this, newθHom_apply_single c (v c), hw, Function.update_same]
      simp [hv']
    rw [← not_mem_support]
    suffices (∀ (hx : x ∈ Function.fixedPoints g), u ⟨x, hx⟩ = ⟨x, hx⟩) ∧
      ∀ c (hc : c ∈ g.cycleFactorsFinset), (v' ⟨c, hc⟩ : Perm α) x = x by
      simp [newθHom_support, this]
    constructor
    · intro h; exfalso
      rw [Function.mem_fixedPoints_iff, ← not_mem_support] at h
      apply h
      rw [eq_comm, eq_cycleOf_of_mem_cycleFactorsFinset_iff _ _ c.prop] at hx
      exact mem_cycleFactorsFinset_support_le c.prop hx
    · intro d hd
      simp only [v']
      by_cases h : c = ⟨d, hd⟩
      · rw [h, Function.update_same]
        simp
      · rw [Function.update_noteq (Ne.symm h)]
        obtain ⟨m, hm⟩ := (v ⟨d, hd⟩).prop
        rw [← hm]
        simp only
        apply zpow_apply_eq_self_of_apply_eq_self
        rw [← not_mem_support, ← g.eq_cycleOf_of_mem_cycleFactorsFinset_iff d hd, hx]
        rw [← Subtype.coe_inj] at h
        exact Ne.symm h
  simp only [Prod.mk_mul_mk, one_mul, Prod.mk.injEq, true_and]
  simp only [w, v', ← Function.update_mul, mul_one]
  convert (Function.update_eq_self _ _).symm
  exact Subtype.instDecidableEq

lemma newθHom_apply_of_mem_fixedPoints (hx : x ∈ Function.fixedPoints g) :
    newθHom uv x = ofSubtype uv.1 x := by
  rw [show uv = ⟨uv.1, 1⟩ * ⟨1, uv.2⟩ by rfl]
  rw [map_mul]
  simp only [coe_mul, Function.comp_apply, Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta]
  suffices newθHom ⟨1, uv.2⟩ x = x by
    rw [this, newθHom_apply_fst]
  rw [← not_mem_support, newθHom_support]
  suffices ∀ (c : Perm α) (hc : c ∈ g.cycleFactorsFinset),
      (uv.2 ⟨c, hc⟩ : Perm α) x = x by
    simp [this]
  intro c hc
  obtain ⟨m, hm⟩ := (uv.2 ⟨c, hc⟩).prop
  simp only [← hm]
  apply zpow_apply_eq_self_of_apply_eq_self
  simp only [Function.mem_fixedPoints_iff, ← not_mem_support] at hx
  rw [← not_mem_support]
  intro h; apply hx (mem_cycleFactorsFinset_support_le hc h)

lemma cycleOf_mem_cycleFactorsFinset_iff' :
    g.cycleOf x ∈ g.cycleFactorsFinset ↔ x ∉ Function.fixedPoints g := by
  rw [cycleOf_mem_cycleFactorsFinset_iff, Function.mem_fixedPoints_iff, mem_support, ne_eq]

theorem newθHom_apply_eq : newθHom uv x =
    if hx : g.cycleOf x ∈ g.cycleFactorsFinset
    then (uv.2 ⟨g.cycleOf x, hx⟩ : Perm α) x
    else ofSubtype uv.1 x := by
  split_ifs with hx
  · exact newθHom_apply_of_cycleOf_eq uv ⟨g.cycleOf x, hx⟩ rfl
  · apply newθHom_apply_of_mem_fixedPoints uv
    rw [cycleOf_mem_cycleFactorsFinset_iff'] at hx
    exact Set.not_mem_compl_iff.mp hx


