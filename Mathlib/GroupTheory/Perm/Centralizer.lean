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

section noncommProd

open MonoidHom Subgroup Finset

@[to_additive]
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

@[to_additive]
lemma MonoidHom.noncommPiCoprod_apply {ι : Type*} [Fintype ι]
    {H : ι → Type*} [∀ i, Monoid (H i)]
    {P : Type*} [Monoid P] (f : (i : ι) → (H i) →* P) (comm)
    (u : (i : ι) → H i) :
    MonoidHom.noncommPiCoprod f comm u = Finset.noncommProd Finset.univ (fun i ↦ f i (u i))
      (Pairwise.set_pairwise (fun ⦃i j⦄ a ↦ comm a (u i) (u j)) _) := by
  dsimp only [MonoidHom.noncommPiCoprod, MonoidHom.coe_mk, OneHom.coe_mk]

@[to_additive]
lemma Subgroup.noncommPiCoprod_apply {G : Type*} [Group G] {ι : Type*} [Fintype ι]
    {H : ι → Subgroup G} (comm) (u : (i : ι) → H i) :
    Subgroup.noncommPiCoprod comm u = Finset.noncommProd Finset.univ (fun i ↦ u i)
      (fun i _ j _ h ↦ comm h _ _ (u i).prop (u j).prop) := by
  simp only [Subgroup.noncommPiCoprod, MonoidHom.noncommPiCoprod,
    coeSubtype, MonoidHom.coe_mk, OneHom.coe_mk]

theorem MulHom.noncommCoprod_apply' {M : Type*} {N : Type*}
    {P : Type*} [Mul M] [Mul N] [Semigroup P]
    (f : M →ₙ* P) (g : N →ₙ* P) (comm : ∀ (m : M) (n : N), Commute (f m) (g n)) (mn : M × N) :
    (f.noncommCoprod g comm) mn = g mn.2 * f mn.1 := by
  rw [← comm, MulHom.noncommCoprod_apply]

theorem MonoidHom.noncommCoprod_apply' {M : Type*} {N : Type*}
    {P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (f : M →* P) (g : N →* P) (comm : ∀ (m : M) (n : N), Commute (f m) (g n)) (mn : M × N) :
    (f.noncommCoprod g comm) mn = g mn.2 * f mn.1 := by
  rw [← comm, MonoidHom.noncommCoprod_apply]

end noncommProd

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

section Disjoint

lemma Set.disjoint_of_le_iff_left_eq_empty {α : Type*} {u v : Set α} (h : u ⊆ v) :
    Disjoint u v ↔ u = ∅ := by
  simp only [disjoint_iff, inf_eq_left.mpr h, Set.bot_eq_empty]

lemma Finset.disjoint_of_le_iff_left_eq_empty {α : Type*} {u v : Set α} (h : u ⊆ v) :
    Disjoint u v ↔ u = ∅ := by
  simp only [disjoint_iff, inf_eq_left.mpr h, Set.bot_eq_empty]

lemma disjoint_of_le_iff_left_eq_bot
    {α : Type*} [SemilatticeInf α] [OrderBot α] {a b : α} (h : a ≤ b) :
    Disjoint a b ↔ a = ⊥ := by
  simp only [disjoint_iff, inf_eq_left.mpr h]

end Disjoint

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

theorem isCycleOn_support_of_mem_cycleFactorsFinset (c : g.cycleFactorsFinset) :
    IsCycleOn g (c : Perm α).support := by
  suffices Finset.Nonempty (c : Perm α).support by
    obtain ⟨x, hx⟩ := this
    convert isCycleOn_support_cycleOf g x
    exact cycle_is_cycleOf hx c.prop
  rw [← Finset.card_pos]
  apply lt_of_lt_of_le Nat.zero_lt_two
  exact IsCycle.two_le_card_support (mem_cycleFactorsFinset_iff.mp c.prop).1

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

theorem mem_fixedPoints_iff_apply_mem_of_mem_centralizer
    {p : Perm α} (hp : p ∈ Subgroup.centralizer {g}) {x} :
    x ∈ Function.fixedPoints g ↔ p x ∈ Function.fixedPoints g :=  by
  simp only [mem_centralizer_singleton_iff] at hp
  simp only [Function.mem_fixedPoints_iff]
  rw [← mul_apply, ← hp, mul_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

lemma support_zpowers_of_mem_cycleFactorsFinset_le
    {c : g.cycleFactorsFinset} (v : zpowers (c : Perm α)) :
    (v : Perm α).support ⊆ g.support := by
  obtain ⟨m, hm⟩ := v.prop
  simp only [← hm]
  apply subset_trans (support_zpow_le _ _) (mem_cycleFactorsFinset_support_le c.prop)

lemma disjoint_ofSubtype_of_memFixedPoints_self
    (u : Perm (Function.fixedPoints g)) : Disjoint (ofSubtype u) g := by
  rw [disjoint_iff_eq_or_eq]
  intro x
  by_cases hx : x ∈ Function.fixedPoints g
  · right; exact hx
  · left; rw [ofSubtype_apply_of_not_mem u hx]

theorem support_ofSubtype {p : α → Prop} [DecidablePred p]
    (u : Perm (Subtype p)) :
    (ofSubtype u).support = u.support.map (Function.Embedding.subtype p) := by
  ext x
  simp only [mem_support, ne_eq, Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists,
    exists_and_right, exists_eq_right, not_iff_comm, not_exists, not_not]
  by_cases hx : p x
  · simp only [forall_prop_of_true hx, ofSubtype_apply_of_mem u hx, ← Subtype.coe_inj]
  · simp only [forall_prop_of_false hx, true_iff, ofSubtype_apply_of_not_mem u hx]

theorem Disjoint.disjoint_noncommProd {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Commute (k i) (k j))
    (f : Perm α) (hf : ∀ i ∈ s, f.Disjoint (k i)) :
    f.Disjoint (s.noncommProd k (hs)) := by
  apply Finset.noncommProd_induction
  · exact fun g h ↦ Disjoint.mul_right
  · exact disjoint_one_right f
  · exact hf

/- theorem Disjoint.disjoint_noncommProd' {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Disjoint (k i) (k j))
    (f : Perm α) (hf : ∀ i ∈ s, f.Disjoint (k i)) :
    f.Disjoint (s.noncommProd k (hs.imp (fun _ _ ↦ Perm.Disjoint.commute))) := by
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
      exact hf j (Finset.mem_insert_of_mem hj) -/

theorem Disjoint.support_noncommProd
    {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Disjoint (k i) (k j)) :
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
    apply Disjoint.disjoint_noncommProd
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]

theorem Disjoint.cycleType_mul
    {f g : Perm α} (h : f.Disjoint g) :
    (f * g).cycleType = f.cycleType + g.cycleType := by
  simp only [Perm.cycleType]
  rw [h.cycleFactorsFinset_mul_eq_union]
  simp only [Finset.union_val, Function.comp_apply]
  rw [← Multiset.add_eq_union_iff_disjoint.mpr _, Multiset.map_add]
  simp only [Finset.disjoint_val, Disjoint.disjoint_cycleFactorsFinset h]

theorem Disjoint.cycleType_noncommProd
    {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Disjoint (k i) (k j))
    (hs' : Set.Pairwise s fun i j ↦ Commute (k i) (k j) :=
      hs.imp (fun _ _ ↦ Perm.Disjoint.commute)):
    (s.noncommProd k hs').cycleType = s.sum fun i ↦ (k i).cycleType := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ hi, Finset.sum_insert hi]
    rw [Equiv.Perm.Disjoint.cycleType_mul, hrec hs']
    apply Disjoint.disjoint_noncommProd
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]

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

variable (τ : range_toPermHom' g)

/-- The function that will provide a right inverse `toCentralizer` to `toPermHom` -/
noncomputable def newK (x : α) : α := by
  if hx : g.cycleOf x ∈ g.cycleFactorsFinset
  then
    let h := mem_support_cycleOf_iff.mp (a.mem_support_self ⟨g.cycleOf x, hx⟩)
    exact (g ^ h.1.symm.choose) (a ((τ : Perm g.cycleFactorsFinset) ⟨g.cycleOf x, hx⟩))
  else exact x

theorem mem_fixedPoints_or_exists_zpow_eq (x : α) : x ∈ Function.fixedPoints g ∨
    ∃ (c : g.cycleFactorsFinset) (_ : x ∈ (c : Perm α).support) (m : ℤ), (g ^ m) (a c) = x := by
  rw [Classical.or_iff_not_imp_left]
  intro hx
  rw [Function.mem_fixedPoints_iff, ← ne_eq, ← mem_support,
    ← cycleOf_mem_cycleFactorsFinset_iff] at hx
  let c : g.cycleFactorsFinset := ⟨g.cycleOf x, hx⟩
  have hc : x ∈ (c : Perm α).support := by
    rw [mem_support_cycleOf_iff]
    rw [← cycleOf_mem_cycleFactorsFinset_iff]
    simp [SameCycle.rfl, hx, and_self]
  exact ⟨c, hc, (mem_support_cycleOf_iff.mp (a.mem_support_self c)).1.symm⟩

theorem newK_apply_of_cycleOf_mem {x : α} {c : g.cycleFactorsFinset}
    (hx : x ∈ (c : Perm α).support) {m : ℤ} (hm : (g ^ m) (a c) = x) :
    newK a τ x = (g ^ m) (a ((τ  : Perm g.cycleFactorsFinset) c)) := by
  have hx' : c = g.cycleOf x := cycle_is_cycleOf hx (Subtype.prop c)
  have hx'' : g.cycleOf x ∈ g.cycleFactorsFinset := hx' ▸ c.prop
  let h := mem_support_cycleOf_iff.mp (a.mem_support_self ⟨g.cycleOf x, hx''⟩)
  set n := h.1.symm.choose
  have hn : (g ^ n) (a c) = x := by
    rw [← h.1.symm.choose_spec]
    congr
    rw [← Subtype.coe_inj, hx']
  suffices newK a τ x = (g ^ n) (a ((τ : Perm g.cycleFactorsFinset) c)) by
    rw [this, IsCycleOn.zpow_apply_eq_zpow_apply
      (isCycleOn_support_of_mem_cycleFactorsFinset ((τ : Perm g.cycleFactorsFinset) c))
      (mem_support_self a ((τ : Perm g.cycleFactorsFinset) c))]
    simp only [τ.prop c]
    rw [← IsCycleOn.zpow_apply_eq_zpow_apply
      (isCycleOn_support_of_mem_cycleFactorsFinset c) (mem_support_self a c)]
    rw [hn, hm]
  simp only [newK, dif_pos hx'']
  congr
  exact hx'.symm

theorem newK_apply_of_mem_fixedPoints {x : α} (hx : x ∈ Function.fixedPoints g) :
    newK a τ x = x := by
  rw [newK, dif_neg]
  rw [cycleOf_mem_cycleFactorsFinset_iff, not_mem_support]
  exact hx

theorem zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff
    {x :α} {m : ℤ} {c : g.cycleFactorsFinset} :
    (g ^ m) x ∈ (c : Perm α).support ↔ x ∈ (c : Perm α).support := by
  rw [← g.eq_cycleOf_of_mem_cycleFactorsFinset_iff _ c.prop]
  rw [cycleOf_self_apply_zpow g m x]
  rw [eq_cycleOf_of_mem_cycleFactorsFinset_iff _ _ c.prop]

theorem newK_apply_mem_support_cycle_iff {x : α} {c : g.cycleFactorsFinset} :
    newK a τ x ∈ ((τ : Perm g.cycleFactorsFinset) c : Perm α).support ↔
      x ∈ (c : Perm α).support := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨d, hd, m, hm⟩)
  · simp only [newK_apply_of_mem_fixedPoints a τ hx]
    suffices ∀ (d : g.cycleFactorsFinset), x ∉ (d : Perm α).support by
      simp only [this]
    intro d hx'
    rw [Function.mem_fixedPoints_iff, ← not_mem_support] at hx
    apply hx
    exact mem_cycleFactorsFinset_support_le d.prop hx'
  · rw [newK_apply_of_cycleOf_mem a τ hd hm] --
    rw [zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff]
    by_cases h : c = d
    · simp only [h, hd, iff_true, mem_support_self]
    · have H : Disjoint (c : Perm α) (d : Perm α) :=
        cycleFactorsFinset_pairwise_disjoint g c.prop d.prop (Subtype.coe_ne_coe.mpr h)
      have H' : Disjoint ((τ : Perm g.cycleFactorsFinset) c : Perm α)
        ((τ : Perm g.cycleFactorsFinset) d : Perm α) :=
        cycleFactorsFinset_pairwise_disjoint g ((τ : Perm g.cycleFactorsFinset) c).prop
          ((τ : Perm g.cycleFactorsFinset) d).prop (by
          intro h'; apply h
          simpa only [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] using h')
      rw [disjoint_iff_disjoint_support, Finset.disjoint_right] at H H'
      simp only [H hd, H' (mem_support_self a _)]

theorem newK_apply_mem_fixedPoints_iff {x : α} :
    newK a τ x ∈ Function.fixedPoints g ↔ x ∈ Function.fixedPoints g := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [hx, newK_apply_of_mem_fixedPoints a τ hx]
  · rw [newK_apply_of_cycleOf_mem a τ hc hm, ← hm]
    simp only [Function.mem_fixedPoints_iff, ← not_mem_support]
    simp only [zpow_apply_mem_support, not_iff_not]
    simp only [Finset.coe_mem,
      mem_cycleFactorsFinset_support_le _ (mem_support_self a _)]

theorem newK_commute_zpow_apply (x : α) (j : ℤ) :
    newK a τ ((g ^ j) x) = (g ^ j) (newK a τ x) := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | hx)
  · rw [newK_apply_of_mem_fixedPoints a τ hx, newK_apply_of_mem_fixedPoints]
    rw [Function.mem_fixedPoints_iff]
    simp only [← mul_apply, ← zpow_one_add, add_comm]
    conv_rhs => rw [← hx, ← mul_apply, ← zpow_add_one]
  · obtain ⟨c, hc, m, hm⟩ := hx
    have hm' : (g ^ (j + m)) (a c) = (g ^ j) x := by rw [zpow_add, mul_apply, hm]
    rw [newK_apply_of_cycleOf_mem a τ hc hm, newK_apply_of_cycleOf_mem a τ _ hm',
      ← mul_apply, ← zpow_add]
    exact zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff.mpr hc

theorem newK_mul (σ τ : range_toPermHom' g) (x) :
    newK a (σ * τ) x = (newK a σ) (newK a τ x) := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [newK_apply_of_mem_fixedPoints a _ hx]
  · simp only [newK_apply_of_cycleOf_mem a _ hc hm]
    rw [newK_apply_of_cycleOf_mem a _ _ rfl]
    rfl
    rw [zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff]
    apply mem_support_self

theorem newK_one (x : α) : (newK a 1) x = x := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · rw [newK_apply_of_mem_fixedPoints a _ hx]
  · rw [newK_apply_of_cycleOf_mem a _ hc hm, OneMemClass.coe_one, coe_one, id_eq, hm]

/-- Given `a : g.Basis` and a permutation of `g.cycleFactorsFinset` that
  preserve the lengths of the cycles, a permutation of `α` that
  moves the `Basis` and commutes with `g` -/
noncomputable def ofPermHom : range_toPermHom' g →* Perm α where
  toFun τ := {
    toFun := newK a τ
    invFun := newK a τ⁻¹
    left_inv := fun x ↦ by rw [← newK_mul, inv_mul_self, newK_one]
    right_inv := fun x ↦ by rw [← newK_mul, mul_right_inv, newK_one] }
  map_one' := ext fun x ↦ newK_one a x
  map_mul' := fun σ τ ↦ ext fun x ↦ by simp [mul_apply, newK_mul a σ τ x]

theorem ofPermHom_support :
    (ofPermHom a τ).support = Finset.biUnion (τ : Perm g.cycleFactorsFinset).support
        (fun c ↦ (c : Perm α).support) := by
  ext x
  simp only [mem_support, Finset.mem_biUnion]
  change newK a τ x ≠ x ↔ _
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [newK_apply_of_mem_fixedPoints a τ hx, ne_eq, not_true_eq_false, false_iff]
    rw [Function.mem_fixedPoints_iff] at hx
    simp only [← mem_support]
    intro h
    obtain ⟨c, _, h'⟩ := h
    exact mem_support.mp ((mem_cycleFactorsFinset_support_le c.prop) h') hx
  · rw [newK_apply_of_cycleOf_mem a τ hc hm]
    nth_rewrite 1 [← hm]
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, (a.injective).eq_iff]
    rw [not_iff_comm]
    by_cases H : (τ : Perm g.cycleFactorsFinset) c = c
    · simp only [H, iff_true]
      push_neg
      intro d hd
      rw [← not_mem_support]
      have := g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop
      rw [disjoint_iff_disjoint_support, Finset.disjoint_left] at this
      refine this ?_ hc
      intro h
      rw [Subtype.coe_inj] at h
      exact hd (h ▸ H)
    · simp only [H, iff_false, not_not]
      exact ⟨c, H, mem_support.mp hc⟩

theorem card_ofPermHom_support :
    (ofPermHom a τ).support.card =  (τ : Perm g.cycleFactorsFinset).support.sum
        (fun c ↦ (c : Perm α).support.card) := by
  rw [ofPermHom_support, Finset.card_biUnion]
  intro c _ d _ h
  apply Equiv.Perm.Disjoint.disjoint_support
  apply g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop (Subtype.coe_ne_coe.mpr h)

theorem ofPermHom_mem_centralizer :
    ofPermHom a τ ∈ Subgroup.centralizer {g} := by
  rw [mem_centralizer_singleton_iff]
  ext x
  simp only [mul_apply]
  exact newK_commute_zpow_apply a τ x 1

/-- Given `a : Equiv.Perm.Basis g`,
we define a right inverse of `Equiv.Perm.OnCycleFactors.toPermHom`,
on `range_toPermHom' g` -/
noncomputable def toCentralizer :
    range_toPermHom' g →* Subgroup.centralizer {g}  where
  toFun τ := ⟨ofPermHom a τ, ofPermHom_mem_centralizer a τ⟩
  map_one' := by simp only [map_one, Submonoid.mk_eq_one]
  map_mul' σ τ := by simp only [map_mul, Submonoid.mk_mul_mk]

theorem toCentralizer_apply (x) : (toCentralizer a τ : Perm α) x = newK a τ x := rfl

variable (c) in
theorem toCentralizer_equivariant :
    (toCentralizer a τ) • c = (τ : Perm g.cycleFactorsFinset) c := by
  rw [centralizer_smul_def, ← Subtype.coe_inj]
  simp only [InvMemClass.coe_inv, mul_inv_eq_iff_eq_mul]
  ext x
  simp only [mul_apply]
  change newK a τ ((c : Perm α) x) = ((τ : Perm g.cycleFactorsFinset) c : Perm α) (newK a τ x)
  by_cases hx : x ∈ (c : Perm α).support
  · rw [(mem_cycleFactorsFinset_iff.mp c.prop).2 x hx]
    have := newK_commute_zpow_apply a τ x 1
    simp only [zpow_one] at this
    rw [this]
    rw [← (mem_cycleFactorsFinset_iff.mp ((τ : Perm g.cycleFactorsFinset) c).prop).2]
    rw [newK_apply_mem_support_cycle_iff]
    exact hx
  · rw [not_mem_support.mp hx, eq_comm, ← not_mem_support, newK_apply_mem_support_cycle_iff]
    exact hx

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

lemma disjoint₁₂ (u : Perm (Function.fixedPoints ⇑g))
    (v : (c : { x // x ∈ g.cycleFactorsFinset }) → ↥(zpowers (c : Perm α))) :
    Disjoint (ofSubtype u) ((noncommPiCoprod paircommute₂) v) := by
  apply Finset.noncommProd_induction
  · intro a _ b _ h
    apply paircommute₂ h <;> simp only [coeSubtype, SetLike.coe_mem]
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
/-- The parametrization of the kernel of `toPermHom` -/
def θHom : (Perm (Function.fixedPoints g)) ×
    ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)) →*
      Perm α :=
  MonoidHom.noncommCoprod (ofSubtype) (Subgroup.noncommPiCoprod paircommute₂) (commute₁₂)

variable {ι : Type*} (k : ι → Perm α) (s : Finset ι)
    (hs : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j))

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

theorem θHom_apply_of_mem_support_cycle {c} {x}
    (hc : c ∈ g.cycleFactorsFinset) (hx : x ∈ c.support) :
    θHom g (u, v) x = (v ⟨c, hc⟩ : Perm α) x := by
  suffices hx' : _ by
    rw [θHom_apply, dif_pos hx']
    suffices (⟨g.cycleOf x, hx'⟩ : g.cycleFactorsFinset) = ⟨c, hc⟩ by
      rw [this]
    simp [← Subtype.coe_inj, Subtype.coe_eta, cycle_is_cycleOf hx hc]
  rw [cycleOf_mem_cycleFactorsFinset_iff]
  exact mem_cycleFactorsFinset_support_le hc hx

theorem θHom_apply_of_cycleOf_eq {x : α} {c : g.cycleFactorsFinset}
    (hx : x ∈ (c : Perm α).support) : θHom g (u,v) x = (v c : Perm α) x :=
  θHom_apply_of_mem_support_cycle _ hx

theorem θHom_apply_of_cycleOf_not_mem {x : α} (hx : g.cycleOf x ∉ g.cycleFactorsFinset) :
    θHom g (u,v) x = ofSubtype u x := by
  rw [θHom_apply, dif_neg hx]

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

theorem θHom_apply_mem_support_cycle_iff_apply_mem
    (c : Perm α) (hc : c ∈ g.cycleFactorsFinset) (x) :
    x ∈ c.support ↔ θHom g (u, v) x ∈ c.support := by
  simp only [← eq_cycleOf_of_mem_cycleFactorsFinset_iff g c hc]
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

theorem θHom_apply_mem_centralizer : θHom g (u,v) ∈ Subgroup.centralizer {g} := by
  rw [mem_centralizer_singleton_iff]
  set p := θHom g (u,v) with h
  suffices ∀ c ∈ g.cycleFactorsFinset, p * c = c * p by
    rw [← g.cycleFactorsFinset_noncommProd]
    apply Finset.noncommProd_commute
    intro c hc
    simp only [id_eq]
    exact this c hc
  intro c hc
  ext x
  simp only [id_eq, coe_mul, Function.comp_apply]
  by_cases hx : x ∈ c.support
  · rw [h, θHom_apply_of_mem_support_cycle hc hx,
      θHom_apply_of_mem_support_cycle hc (by simp only [apply_mem_support, hx])]
    simp only [← mul_apply]
    apply DFunLike.congr_fun
    rw [← commute_iff_eq]
    obtain ⟨m, hm⟩ := (v ⟨c, hc⟩).prop
    simp only [← hm]
    exact Commute.zpow_left rfl m
  · rw [not_mem_support.mp hx, eq_comm]
    rw [← not_mem_support, ← θHom_apply_mem_support_cycle_iff_apply_mem c hc]
    exact hx

lemma θHom_range_le_centralizer : (θHom g).range ≤ centralizer {g} := by
  rintro _ ⟨⟨u, v⟩, rfl⟩
  exact θHom_apply_mem_centralizer


theorem mem_θHom_range_iff {p : Perm α} : p ∈ (θHom g).range ↔
    (∃ (hp : p ∈ Subgroup.centralizer {g}),
      (⟨p, hp⟩ : Subgroup.centralizer {g}) ∈ (toPermHom g).ker) := by
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    simp only [mem_ker_toPermHom_iff, IsCycle.forall_commute_iff]
    use θHom_apply_mem_centralizer
    intro c hc
    use θHom_apply_mem_support_cycle_iff_apply_mem c hc
    suffices ofSubtype (subtypePerm (θHom g (u,v)) _) = v ⟨c, hc⟩ by
      rw [this]
      exact (v _).prop
    ext x
    by_cases hx : x ∈ c.support
    · rw [ofSubtype_apply_of_mem, subtypePerm_apply]
      · dsimp only [id_eq, MonoidHom.coe_mk, OneHom.coe_mk, coe_fn_mk, eq_mpr_eq_cast]
        rw [θHom_apply_of_mem_support_cycle hc hx]
      · exact hx
    · rw [ofSubtype_apply_of_not_mem]
      · obtain ⟨m, hm⟩ := (v ⟨c, hc⟩).prop
        rw [← hm, eq_comm, ← not_mem_support]
        intro hx'
        apply hx
        exact (support_zpow_le c m) hx'
      · exact hx
  · rintro ⟨hp_mem, hp⟩
    set u : Perm (Function.fixedPoints g) :=
      subtypePerm p (fun x ↦ mem_fixedPoints_iff_apply_mem_of_mem_centralizer hp_mem)
    simp only [mem_ker_toPermHom_iff, IsCycle.forall_commute_iff] at hp
    set v : (c : g.cycleFactorsFinset) → (Subgroup.zpowers (c : Perm α)) :=
      fun c => ⟨ofSubtype
          (p.subtypePerm (Classical.choose (hp c.val c.prop))),
            Classical.choose_spec (hp c.val c.prop)⟩
    use (u, v)
    ext x
    rw [θHom_apply]
    split_ifs with hx
    · rw [cycleOf_mem_cycleFactorsFinset_iff, mem_support] at hx
      rw [ofSubtype_apply_of_mem, subtypePerm_apply]
      rwa [mem_support, cycleOf_apply_self, ne_eq]
    · rw [cycleOf_mem_cycleFactorsFinset_iff, not_mem_support] at hx
      rwa [ofSubtype_apply_of_mem, subtypePerm_apply]

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


#exit--
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
/- we have points a, b on two cycles c, d of the same length
we want to define a function that maps g ^ i a to g ^ i b for all i
take m such that x = g ^ m a, set y = g ^ m b

to get the general function that maps an adequate permutation of cycles:
- if x belongs to a cycle c
  get m using sameCycle such that x = g ^ m a.c
  apply g ^ m a.(τ c)
- otherwise, apply x

this should allow to suppress the mention of i in the definition

-/
/- variable {e e' : range_toPermHom' g} {c d : g.cycleFactorsFinset} {i j : ℤ}


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
  preserve the lengths of the cycles, a permutation of `α` that
  moves the `Basis` and commutes with `g`
  -/
noncomputable def ofPerm : Perm α :=
  ofBijective (k a τ) (k_bij a τ)

theorem ofPerm_apply (x) :
    (ofPerm a τ) x = k a τ x := rfl
-/

/- theorem ofPermHom_support_le :
    (ofPermHom a τ).support ≤ g.support := by
  intro x
  simp only [Perm.mem_support, ne_eq, not_imp_not]
  rw [← Perm.not_mem_support]
  sorry -- exact k_apply_of_not_mem_support a _
-/

/-
theorem mem_ofPermHom_support_iff (x : α) :
    x ∈ (ofPermHom a τ).support ↔
      ∃ c : g.cycleFactorsFinset,
        g.cycleOf x = c ∧ c ∈ (τ : Perm g.cycleFactorsFinset).support := by
  sorry
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
-/


