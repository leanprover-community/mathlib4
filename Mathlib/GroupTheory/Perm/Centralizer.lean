/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.Perm.ConjAct
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.Rank

/-!
# Centralizer of a permutation and cardinality of conjugacy classes in the symmetric groups

Let `α : Type` with `Fintype α` (and `DecidableEq α`).
The main goal of this file is to compute the cardinality of
conjugacy classes in `Equiv.Perm α`.
Every `g : Equiv.Perm α` has a `g.cycleType : Multiset ℕ`.
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
(ConjAct (Equiv.Perm α)) g` and `Subgroup.centralizer_eq_comap_stabilizer`.

We compute this subgroup as follows.

* If `h : Subgroup.centralizer {g}`, then the action of `ConjAct.toConjAct h`
  by conjugation on `Equiv.Perm α` stabilizes `g.cycleFactorsFinset`.
  That induces an action of `Subgroup.centralizer {g}` on
  `g.cycleFactorsFinset` which is defined as an instance.

* This action defines a group morphism `Equiv.Perm.OnCycleFactors.toPermHom g`
  from `Subgroup.centralizer {g}` to `Equiv.Perm g.cycleFactorsFinset`.

* `Equiv.Perm.OnCycleFactors.range_toPermHom'` is the subgroup of
  `Equiv.Perm g.cycleFactorsFinset` consisting of permutations that
  preserve the cardinality of the support.

* `Equiv.Perm.OnCycleFactors.range_toPermHom_eq_range_toPermHom'` shows that
  the range of `Equiv.Perm.OnCycleFactors.toPermHom g`
  is the subgroup `Equiv.Perm.OnCycleFactors.toPermHom_range' g`
  of `Equiv.Perm g.cycleFactorsFinset`.

This is shown by constructing a right inverse
`Equiv.Perm.Basis.toCentralizer`, as established by
`Equiv.Perm.Basis.toPermHom_apply_toCentralizer`.

* `Equiv.Perm.OnCycleFactors.nat_card_range_toPermHom` computes the
  cardinality of `(Equiv.Perm.OnCycleFactors.toPermHom g).range`
  as a product of factorials.

* `Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff` proves that
  `k : Subgroup.centralizer {g}` belongs to the kernel of
  `Equiv.Perm.OnCycleFactors.toPermHom g` if and only if it commutes with
  each cycle of `g`.  This is equivalent to the conjunction of two properties:
  * `k` preserves the set of fixed points of `g`;
  * on each cycle `c`, `k` acts as a power of that cycle.

This allows to give a description of the kernel of
`Equiv.Perm.OnCycleFactors.toPermHom g` as the product of a
symmetric group and of a product of cyclic groups.  This analysis
starts with the morphism `Equiv.Perm.OnCycleFactors.kerParam`, its
injectivity `Equiv.Perm.OnCycleFactors.kerParam_injective`, its range
`Equiv.Perm.OnCycleFactors.kerParam_range_eq`, and its cardinality
`Equiv.Perm.OnCycleFactors.kerParam_range_card`.

* `Equiv.Perm.OnCycleFactors.sign_kerParam_apply_apply` computes the signature
  of the permutation induced given by `Equiv.Perm.OnCycleFactors.kerParam`.

* `Equiv.Perm.nat_card_centralizer g` computes the cardinality
  of the centralizer of `g`.

* `Equiv.Perm.card_isConj_mul_eq g`computes the cardinality
  of the conjugacy class of `g`.

* We now can compute the cardinality of the set of permutations with given cycle type.
  The condition for this cardinality to be zero is given by
  `Equiv.Perm.card_of_cycleType_eq_zero_iff`
  which is itself derived from `Equiv.Perm.exists_with_cycleType_iff`.

* `Equiv.Perm.card_of_cycleType_mul_eq m` and `Equiv.Perm.card_of_cycleType m`
  compute this cardinality.

-/

open scoped Finset Pointwise

namespace Equiv.Perm

open MulAction Equiv Subgroup

variable {α : Type*} [DecidableEq α] [Fintype α] {g : Equiv.Perm α}

namespace OnCycleFactors

variable (g)

variable {g} in
lemma Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset {k c : Perm α}
    (k_mem : k ∈ centralizer {g}) (c_mem : c ∈ g.cycleFactorsFinset) :
    ConjAct.toConjAct k • c ∈ g.cycleFactorsFinset := by
  suffices (g.cycleFactorsFinset : Set (Perm α)) =
    (ConjAct.toConjAct k) • g.cycleFactorsFinset by
    rw [← Finset.mem_coe, this]
    simp only [Set.smul_mem_smul_set_iff, Finset.mem_coe, c_mem]
  have this := cycleFactorsFinset_conj_eq (ConjAct.toConjAct (k : Perm α)) g
  rw [ConjAct.toConjAct_smul, mem_centralizer_singleton_iff.mp k_mem, mul_assoc] at this
  simp only [mul_inv_cancel, mul_one] at this
  conv_lhs => rw [this]
  simp only [Finset.coe_smul_finset]

/-- The action by conjugation of `Subgroup.centralizer {g}`
  on the cycles of a given permutation -/
def Subgroup.Centralizer.cycleFactorsFinset_mulAction :
    MulAction (centralizer {g}) g.cycleFactorsFinset where
  smul k c := ⟨ConjAct.toConjAct (k : Perm α) • c.val,
    Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k.prop c.prop⟩
  one_smul c := by
    rw [← Subtype.coe_inj]
    change ConjAct.toConjAct (1 : Perm α) • c.val = c
    simp only [map_one, one_smul]
  mul_smul k l c := by
    simp only [← Subtype.coe_inj]
    change ConjAct.toConjAct (k * l : Perm α) • c.val =
      ConjAct.toConjAct (k : Perm α) • (ConjAct.toConjAct (l : Perm α)) • c.val
    simp only [map_mul, mul_smul]

/-- The conjugation action of `Subgroup.centralizer {g}` on `g.cycleFactorsFinset` -/
scoped instance : MulAction (centralizer {g}) (g.cycleFactorsFinset) :=
  (Subgroup.Centralizer.cycleFactorsFinset_mulAction g)

/-- The canonical morphism from `Subgroup.centralizer {g}`
  to the group of permutations of `g.cycleFactorsFinset` -/
def toPermHom := MulAction.toPermHom (centralizer {g}) g.cycleFactorsFinset

theorem centralizer_smul_def (k : centralizer {g}) (c : g.cycleFactorsFinset) :
    k • c = ⟨k * c * k⁻¹,
      Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k.prop c.prop⟩ :=
  rfl

@[simp]
theorem val_centralizer_smul (k : Subgroup.centralizer {g}) (c : g.cycleFactorsFinset) :
    ((k • c :) : Perm α) = k * c * k⁻¹ :=
  rfl

theorem toPermHom_apply (k : centralizer {g}) (c : g.cycleFactorsFinset) :
    (toPermHom g k c) = k • c := rfl

theorem coe_toPermHom (k : centralizer {g}) (c : g.cycleFactorsFinset) :
    (toPermHom g k c : Perm α) = k * c * (k : Perm α)⁻¹ := rfl

/-- The range of `Equiv.Perm.OnCycleFactors.toPermHom`.

The equality is proved by `Equiv.Perm.OnCycleFactors.range_toPermHom_eq_range_toPermHom'`. -/
def range_toPermHom' : Subgroup (Perm g.cycleFactorsFinset) where
  carrier := {τ | ∀ c, #(τ c).val.support = #c.val.support}
  one_mem' := by
    simp only [Set.mem_setOf_eq, coe_one, id_eq, imp_true_iff]
  mul_mem' hσ hτ := by
    simp only [Subtype.forall, Set.mem_setOf_eq, coe_mul, Function.comp_apply]
    simp only [Subtype.forall, Set.mem_setOf_eq] at hσ hτ
    intro c hc
    rw [hσ, hτ]
  inv_mem' hσ := by
    simp only [Subtype.forall, Set.mem_setOf_eq] at hσ ⊢
    intro c hc
    rw [← hσ]
    · simp only [Finset.coe_mem, Subtype.coe_eta, apply_inv_self]
    · simp only [Finset.coe_mem]

variable {g} in
theorem mem_range_toPermHom'_iff {τ : Perm g.cycleFactorsFinset} :
    τ ∈ range_toPermHom' g ↔ ∀ c, #(τ c).val.support = #c.val.support :=
  Iff.rfl

variable (k : centralizer {g})

/-- `k : Subgroup.centralizer {g}` belongs to the kernel of `toPermHom g`
  iff it commutes with each cycle of `g` -/
theorem mem_ker_toPermHom_iff :
    k ∈ (toPermHom g).ker ↔ ∀ c ∈ g.cycleFactorsFinset, Commute (k : Perm α) c := by
  simp only [toPermHom, MonoidHom.mem_ker, DFunLike.ext_iff, Subtype.forall]
  refine forall₂_congr (fun _ _ ↦ ?_)
  simp [← Subtype.coe_inj, commute_iff_eq, mul_inv_eq_iff_eq_mul]

end OnCycleFactors

open OnCycleFactors

/-- A `Basis` of a permutation is a choice of an element in each of its cycles -/
structure Basis (g : Equiv.Perm α) where
  /-- A choice of elements in each cycle -/
  (toFun : g.cycleFactorsFinset → α)
  /-- For each cycle, the chosen element belongs to the cycle -/
  (mem_support_self' : ∀ (c : g.cycleFactorsFinset), toFun c ∈ c.val.support)

instance (g : Perm α) : FunLike (Basis g) g.cycleFactorsFinset α where
  coe a := a.toFun
  coe_injective' a a' _ := by cases a; cases a'; congr

namespace Basis

theorem nonempty (g : Perm α) : Nonempty (Basis g) := by
  have (c : g.cycleFactorsFinset) : c.val.support.Nonempty :=
    IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.prop).1
  exact ⟨fun c ↦ (this c).choose, fun c ↦ (this c).choose_spec⟩

variable (a : Basis g) (c : g.cycleFactorsFinset)

theorem mem_support_self :
    a c ∈ c.val.support := a.mem_support_self' c

theorem injective : Function.Injective a := by
  intro c d h
  rw [← Subtype.coe_inj]
  apply g.cycleFactorsFinset_pairwise_disjoint.eq c.prop d.prop
  simp only [Disjoint, not_forall, not_or]
  use a c
  conv_rhs => rw [h]
  simp only [← Perm.mem_support, a.mem_support_self c, a.mem_support_self d, and_self]

theorem cycleOf_eq : g.cycleOf (a c) = c :=
  (cycle_is_cycleOf (a.mem_support_self c) c.prop).symm

theorem sameCycle {x : α} (hx : g.cycleOf x ∈ g.cycleFactorsFinset) :
    g.SameCycle (a ⟨g.cycleOf x, hx⟩) x :=
  (mem_support_cycleOf_iff.mp (a.mem_support_self ⟨g.cycleOf x, hx⟩)).1.symm

variable (τ : range_toPermHom' g)

/-- The function that will provide a right inverse `toCentralizer` to `toPermHom` -/
def ofPermHomFun (x : α) : α :=
  if hx : g.cycleOf x ∈ g.cycleFactorsFinset
  then
    (g ^ (Nat.find (a.sameCycle hx).exists_nat_pow_eq))
      (a ((τ : Perm g.cycleFactorsFinset) ⟨g.cycleOf x, hx⟩))
  else x

theorem mem_fixedPoints_or_exists_zpow_eq (x : α) :
    x ∈ Function.fixedPoints g ∨
      ∃ (c : g.cycleFactorsFinset) (_ : x ∈ c.val.support) (m : ℤ), (g ^ m) (a c) = x := by
  rw [Classical.or_iff_not_imp_left]
  intro hx
  rw [Function.mem_fixedPoints_iff, ← ne_eq, ← mem_support,
    ← cycleOf_mem_cycleFactorsFinset_iff] at hx
  refine ⟨⟨g.cycleOf x, hx⟩, ?_, (a.sameCycle hx)⟩
  rw [mem_support_cycleOf_iff, ← cycleOf_mem_cycleFactorsFinset_iff]
  simp [SameCycle.rfl, hx, and_self]

theorem ofPermHomFun_apply_of_cycleOf_mem {x : α} {c : g.cycleFactorsFinset}
    (hx : x ∈ c.val.support) {m : ℤ} (hm : (g ^ m) (a c) = x) :
    ofPermHomFun a τ x = (g ^ m) (a ((τ : Perm g.cycleFactorsFinset) c)) := by
  have hx' : c = g.cycleOf x := cycle_is_cycleOf hx (Subtype.prop c)
  have hx'' : g.cycleOf x ∈ g.cycleFactorsFinset := hx' ▸ c.prop
  set n := Nat.find (a.sameCycle hx'').exists_nat_pow_eq
  have hn : (g ^ (n : ℤ)) (a c) = x := by
    rw [← Nat.find_spec (a.sameCycle hx'').exists_nat_pow_eq, zpow_natCast]
    congr
    rw [← Subtype.coe_inj, hx']
  suffices ofPermHomFun a τ x = (g ^ (n : ℤ)) (a ((τ : Perm g.cycleFactorsFinset) c)) by
    rw [this, IsCycleOn.zpow_apply_eq_zpow_apply
      (isCycleOn_support_of_mem_cycleFactorsFinset ((τ : Perm g.cycleFactorsFinset) c).prop)
      (mem_support_self a ((τ : Perm g.cycleFactorsFinset) c))]
    simp only [τ.prop c]
    rw [← IsCycleOn.zpow_apply_eq_zpow_apply
      (isCycleOn_support_of_mem_cycleFactorsFinset c.prop) (mem_support_self a c)]
    rw [hn, hm]
  simp only [ofPermHomFun, dif_pos hx'']
  congr
  exact hx'.symm

theorem ofPermHomFun_apply_of_mem_fixedPoints {x : α} (hx : x ∈ Function.fixedPoints g) :
    ofPermHomFun a τ x = x := by
  rw [ofPermHomFun, dif_neg]
  rw [cycleOf_mem_cycleFactorsFinset_iff, notMem_support]
  exact hx

theorem ofPermHomFun_apply_mem_support_cycle_iff {x : α} {c : g.cycleFactorsFinset} :
    ofPermHomFun a τ x ∈ ((τ : Perm g.cycleFactorsFinset) c : Perm α).support ↔
      x ∈ c.val.support := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨d, hd, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a τ hx]
    suffices ∀ (d : g.cycleFactorsFinset), x ∉ (d : Perm α).support by
      simp only [this]
    intro d hx'
    rw [Function.mem_fixedPoints_iff, ← notMem_support] at hx
    apply hx
    exact mem_cycleFactorsFinset_support_le d.prop hx'
  · rw [ofPermHomFun_apply_of_cycleOf_mem a τ hd hm] --
    rw [zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff]
    by_cases h : c = d
    · simp only [h, hd, mem_support_self]
    · have H : Disjoint c.val d.val :=
        cycleFactorsFinset_pairwise_disjoint g c.prop d.prop (Subtype.coe_ne_coe.mpr h)
      have H' : Disjoint ((τ : Perm g.cycleFactorsFinset) c : Perm α)
        ((τ : Perm g.cycleFactorsFinset) d : Perm α) :=
        cycleFactorsFinset_pairwise_disjoint g ((τ : Perm g.cycleFactorsFinset) c).prop
          ((τ : Perm g.cycleFactorsFinset) d).prop (by
          intro h'; apply h
          simpa only [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] using h')
      rw [disjoint_iff_disjoint_support, Finset.disjoint_right] at H H'
      simp only [H hd, H' (mem_support_self a _)]

theorem ofPermHomFun_commute_zpow_apply (x : α) (j : ℤ) :
    ofPermHomFun a τ ((g ^ j) x) = (g ^ j) (ofPermHomFun a τ x) := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | hx)
  · rw [ofPermHomFun_apply_of_mem_fixedPoints a τ hx, ofPermHomFun_apply_of_mem_fixedPoints]
    rw [Function.mem_fixedPoints_iff]
    simp only [← mul_apply, ← zpow_one_add, add_comm]
    conv_rhs => rw [← hx, ← mul_apply, ← zpow_add_one]
  · obtain ⟨c, hc, m, hm⟩ := hx
    have hm' : (g ^ (j + m)) (a c) = (g ^ j) x := by rw [zpow_add, mul_apply, hm]
    rw [ofPermHomFun_apply_of_cycleOf_mem a τ hc hm, ofPermHomFun_apply_of_cycleOf_mem a τ _ hm',
      ← mul_apply, ← zpow_add]
    exact zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff.mpr hc

theorem ofPermHomFun_mul (σ τ : range_toPermHom' g) (x) :
    ofPermHomFun a (σ * τ) x = (ofPermHomFun a σ) (ofPermHomFun a τ x) := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a _ hx]
  · simp only [ofPermHomFun_apply_of_cycleOf_mem a _ hc hm]
    rw [ofPermHomFun_apply_of_cycleOf_mem a _ _ rfl]
    · rfl
    · rw [zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff]
      apply mem_support_self

theorem ofPermHomFun_one (x : α) : (ofPermHomFun a 1) x = x := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · rw [ofPermHomFun_apply_of_mem_fixedPoints a _ hx]
  · rw [ofPermHomFun_apply_of_cycleOf_mem a _ hc hm, OneMemClass.coe_one, coe_one, id_eq, hm]

/-- Given `a : g.Basis` and a permutation of `g.cycleFactorsFinset` that
  preserve the lengths of the cycles, a permutation of `α` that
  moves the `Basis` and commutes with `g` -/
noncomputable def ofPermHom : range_toPermHom' g →* Perm α where
  toFun τ := {
    toFun := ofPermHomFun a τ
    invFun := ofPermHomFun a τ⁻¹
    left_inv := fun x ↦ by rw [← ofPermHomFun_mul, inv_mul_cancel, ofPermHomFun_one]
    right_inv := fun x ↦ by rw [← ofPermHomFun_mul, mul_inv_cancel, ofPermHomFun_one] }
  map_one' := ext fun x ↦ ofPermHomFun_one a x
  map_mul' := fun σ τ ↦ ext fun x ↦ by simp [mul_apply, ofPermHomFun_mul a σ τ x]

theorem ofPermHom_apply (τ) (x) : a.ofPermHom τ x = a.ofPermHomFun τ x := rfl

theorem ofPermHom_support :
    (ofPermHom a τ).support =
      (τ : Perm g.cycleFactorsFinset).support.biUnion (fun c ↦ c.val.support) := by
  ext x
  simp only [mem_support, Finset.mem_biUnion, ofPermHom_apply]
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a τ hx, ne_eq, not_true_eq_false, false_iff,
      ← mem_support]
    rintro ⟨c, -, hc⟩
    rw [Function.mem_fixedPoints_iff] at hx
    exact mem_support.mp ((mem_cycleFactorsFinset_support_le c.prop) hc) hx
  · rw [ofPermHomFun_apply_of_cycleOf_mem a τ hc hm]
    conv_lhs => rw [← hm]
    rw [(g ^ m).injective.ne_iff, a.injective.ne_iff, not_iff_comm]
    by_cases H : (τ : Perm g.cycleFactorsFinset) c = c
    · simp only [H, iff_true]
      push_neg
      intro d hd
      rw [← notMem_support]
      have := g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop
      rw [disjoint_iff_disjoint_support, Finset.disjoint_left] at this
      exact this (by aesop) hc
    · simpa only [H, iff_false, not_not] using ⟨c, H, mem_support.mp hc⟩

theorem card_ofPermHom_support :
    #(ofPermHom a τ).support = ∑ c ∈ (τ : Perm g.cycleFactorsFinset).support, #c.val.support := by
  rw [ofPermHom_support, Finset.card_biUnion]
  intro c _ d _ h
  apply Equiv.Perm.Disjoint.disjoint_support
  apply g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop (Subtype.coe_ne_coe.mpr h)

theorem ofPermHom_mem_centralizer :
    a.ofPermHom τ ∈ centralizer {g} := by
  rw [mem_centralizer_singleton_iff]
  ext x
  simp only [mul_apply]
  exact ofPermHomFun_commute_zpow_apply a τ x 1

/-- Given `a : Equiv.Perm.Basis g`,
we define a right inverse of `Equiv.Perm.OnCycleFactors.toPermHom`,
on `range_toPermHom' g` -/
noncomputable def toCentralizer :
    range_toPermHom' g →* centralizer {g}  where
  toFun τ := ⟨ofPermHom a τ, ofPermHom_mem_centralizer a τ⟩
  map_one' := by simp only [map_one, mk_eq_one]
  map_mul' σ τ := by simp only [map_mul, MulMemClass.mk_mul_mk]

theorem toCentralizer_apply (x) : (toCentralizer a τ : Perm α) x = ofPermHomFun a τ x := rfl

theorem toCentralizer_equivariant :
    (toCentralizer a τ) • c = (τ : Perm g.cycleFactorsFinset) c := by
  simp only [← Subtype.coe_inj, val_centralizer_smul, InvMemClass.coe_inv, mul_inv_eq_iff_eq_mul]
  ext x
  simp only [mul_apply, toCentralizer_apply]
  by_cases hx : x ∈ c.val.support
  · rw [(mem_cycleFactorsFinset_iff.mp c.prop).2 x hx]
    have := ofPermHomFun_commute_zpow_apply a τ x 1
    simp only [zpow_one] at this
    rw [this, ← (mem_cycleFactorsFinset_iff.mp ((τ : Perm g.cycleFactorsFinset) c).prop).2]
    rw [ofPermHomFun_apply_mem_support_cycle_iff]
    exact hx
  · rw [notMem_support.mp hx, eq_comm, ← notMem_support,
      ofPermHomFun_apply_mem_support_cycle_iff]
    exact hx

theorem toPermHom_apply_toCentralizer :
    (toPermHom g) (toCentralizer a τ) = (τ : Perm g.cycleFactorsFinset) := by
  apply ext
  intro c
  rw [OnCycleFactors.toPermHom_apply, toCentralizer_equivariant]

end Basis

namespace OnCycleFactors

open Basis BigOperators Nat Equiv.Perm

theorem mem_range_toPermHom_iff {τ} : τ ∈ (toPermHom g).range ↔
    ∀ c, #(τ c).val.support = #c.val.support := by
  constructor
  · rintro ⟨k, rfl⟩ c
    rw [coe_toPermHom, Equiv.Perm.support_conj]
    apply Finset.card_map
  · obtain ⟨a⟩ := Basis.nonempty g
    exact fun hτ ↦ ⟨toCentralizer a ⟨τ, hτ⟩, toPermHom_apply_toCentralizer a ⟨τ, hτ⟩⟩

/-- Unapplied variant of `Equiv.Perm.mem_range_toPermHom_iff` -/
theorem mem_range_toPermHom_iff' {τ} : τ ∈ (toPermHom g).range ↔
    (fun (c : g.cycleFactorsFinset) ↦ #c.val.support) ∘ τ =
      fun (c : g.cycleFactorsFinset) ↦ #c.val.support := by
  rw [mem_range_toPermHom_iff, funext_iff]
  simp only [Subtype.forall, Function.comp_apply]

/-- Computes the range of `Equiv.Perm.toPermHom g` -/
theorem range_toPermHom_eq_range_toPermHom' :
    (toPermHom g).range = range_toPermHom' g := by
  ext τ
  rw [mem_range_toPermHom_iff, mem_range_toPermHom'_iff]

theorem nat_card_range_toPermHom :
    Nat.card (toPermHom g).range =
      ∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)! := by
  classical
  set sc := fun (c : g.cycleFactorsFinset) ↦ #c.val.support with hsc
  suffices Fintype.card (toPermHom g).range =
    Fintype.card { k : Perm g.cycleFactorsFinset | sc ∘ k = sc } by
    simp only [Nat.card_eq_fintype_card, this, Set.coe_setOf, DomMulAct.stabilizer_card', hsc,
      Finset.univ_eq_attach]
    simp_rw [← CycleType.count_def]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_image, Finset.mem_attach,
        true_and, Subtype.exists, exists_prop, Multiset.mem_toFinset]
    simp only [cycleType_def, Function.comp_apply, Multiset.mem_map, Finset.mem_val]
  simp only [← SetLike.coe_sort_coe, Fintype.card_eq_nat_card]
  congr
  ext
  rw [SetLike.mem_coe, mem_range_toPermHom_iff', Set.mem_setOf_eq]

section Kernel
/- Here, we describe the kernel of `g.OnCycleFactors.toPermHom` -/

variable (g) in
/-- The parametrization of the kernel of `toPermHom` -/
def kerParam : (Perm (Function.fixedPoints g)) ×
    ((c : g.cycleFactorsFinset) → Subgroup.zpowers c.val) →* Perm α :=
  MonoidHom.noncommCoprod ofSubtype (Subgroup.noncommPiCoprod g.pairwise_commute_of_mem_zpowers)
    g.commute_ofSubtype_noncommPiCoprod

theorem kerParam_apply {u : Perm (Function.fixedPoints g)}
    {v : (c : g.cycleFactorsFinset) → Subgroup.zpowers c.val} {x : α} :
    kerParam g (u,v) x =
    if hx : g.cycleOf x ∈ g.cycleFactorsFinset
    then (v ⟨g.cycleOf x, hx⟩ : Perm α) x
    else ofSubtype u x := by
  split_ifs with hx
  · have hx' := hx
    rw [cycleOf_mem_cycleFactorsFinset_iff, mem_support, Ne, ← Function.mem_fixedPoints_iff] at hx'
    rw [kerParam, MonoidHom.noncommCoprod_apply', mul_apply, ofSubtype_apply_of_not_mem u hx',
      noncommPiCoprod_apply, ← Finset.noncommProd_erase_mul _ (Finset.mem_univ ⟨g.cycleOf x, hx⟩),
      mul_apply, ← notMem_support]
    contrapose! hx'
    obtain ⟨a, ha1, ha2⟩ := mem_support_of_mem_noncommProd_support hx'
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Ne, Subtype.ext_iff] at ha1
    have key := cycleFactorsFinset_pairwise_disjoint g a.2 hx ha1
    rw [disjoint_iff_disjoint_support, Finset.disjoint_left] at key
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (v a).2
    replace ha2 := key (support_zpow_le a.1 k (hk ▸ ha2))
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (v ⟨g.cycleOf x, hx⟩).2
    rwa [← hk, zpow_apply_mem_support, notMem_support, cycleOf_apply_self] at ha2
  · rw [cycleOf_mem_cycleFactorsFinset_iff] at hx
    rw [kerParam, MonoidHom.noncommCoprod_apply, mul_apply, Equiv.apply_eq_iff_eq,
      ← notMem_support]
    contrapose! hx
    obtain ⟨a, -, ha⟩ := mem_support_of_mem_noncommProd_support
      (comm := fun a ha b hb h ↦ g.pairwise_commute_of_mem_zpowers h (v a) (v b) (v a).2 (v b).2) hx
    exact support_zpowers_of_mem_cycleFactorsFinset_le (v a) ha

theorem kerParam_injective (g : Perm α) : Function.Injective (kerParam g) := by
  rw [kerParam, MonoidHom.noncommCoprod_injective]
  refine ⟨ofSubtype_injective, ?_, ?_⟩
  · apply MonoidHom.injective_noncommPiCoprod_of_iSupIndep
    · intro a
      simp only [range_subtype, ne_eq]
      simp only [zpowers_eq_closure, ← closure_iUnion]
      apply disjoint_closure_of_disjoint_support
      rintro - ⟨-⟩ - ⟨-, ⟨b, rfl⟩, -, ⟨h, rfl⟩, ⟨-⟩⟩
      rw [← disjoint_iff_disjoint_support]
      apply cycleFactorsFinset_pairwise_disjoint g a.2 b.2
      simp only [ne_eq, ← Subtype.ext_iff]
      exact ne_comm.mp h
    · exact fun i ↦ subtype_injective _
  · rw [noncommPiCoprod_range, ← ofSubtype.range.closure_eq]
    simp only [zpowers_eq_closure, ← closure_iUnion]
    apply disjoint_closure_of_disjoint_support
    rintro - ⟨a, rfl⟩ - ⟨-, ⟨b, rfl⟩, ⟨-⟩⟩
    exact (ofSubtype_support_disjoint a).mono_right (mem_cycleFactorsFinset_support_le b.2)

theorem kerParam_range_eq :
    (kerParam g).range = (toPermHom g).ker.map (Subgroup.subtype _) := by
  apply le_antisymm
  · rw [kerParam, MonoidHom.noncommCoprod_range, sup_le_iff, noncommPiCoprod_range, iSup_le_iff]
    simp only [zpowers_le]
    constructor
    · rintro - ⟨a, rfl⟩
      refine ⟨⟨ofSubtype a, ?_⟩, ?_, rfl⟩
      · rw [mem_centralizer_singleton_iff]
        exact Disjoint.commute (disjoint_iff_disjoint_support.mpr (ofSubtype_support_disjoint a))
      · exact Perm.ext fun x ↦ Subtype.ext (disjoint_iff_disjoint_support.mpr
          ((ofSubtype_support_disjoint a).mono_right
            (mem_cycleFactorsFinset_support_le x.2))).commute.mul_inv_cancel
    · intro i
      refine ⟨⟨i, mem_centralizer_singleton_iff.mpr (self_mem_cycle_factors_commute i.2)⟩, ?_, rfl⟩
      exact Perm.ext fun x ↦ Subtype.ext (cycleFactorsFinset_mem_commute' g i.2 x.2).mul_inv_cancel
  · rintro - ⟨p, hp, rfl⟩
    simp only [coe_subtype]
    set u : Perm (Function.fixedPoints g) :=
      subtypePerm p (fun x ↦ apply_mem_fixedPoints_iff_mem_of_mem_centralizer p.2)
    simp only [SetLike.mem_coe, mem_ker_toPermHom_iff, IsCycle.forall_commute_iff] at hp
    set v : (c : g.cycleFactorsFinset) → (Subgroup.zpowers c.val) :=
      fun c => ⟨ofSubtype
          (p.1.subtypePerm (Classical.choose (hp c.val c.prop))),
            Classical.choose_spec (hp c.val c.prop)⟩
    use (u, v)
    ext x
    rw [kerParam_apply]
    split_ifs with hx
    · rw [cycleOf_mem_cycleFactorsFinset_iff, mem_support] at hx
      rw [ofSubtype_apply_of_mem, subtypePerm_apply]
      rwa [mem_support, cycleOf_apply_self, ne_eq]
    · rw [cycleOf_mem_cycleFactorsFinset_iff, notMem_support] at hx
      rwa [ofSubtype_apply_of_mem, subtypePerm_apply]

theorem kerParam_range_le_centralizer :
    (kerParam g).range ≤ Subgroup.centralizer {g} := by
  rw [kerParam_range_eq]
  exact map_subtype_le (toPermHom g).ker

theorem kerParam_range_card (g : Equiv.Perm α) :
    Fintype.card (kerParam g).range = (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod := by
  rw [Fintype.card_coeSort_range (kerParam_injective g)]
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_pi, card_fixedPoints]
  apply congr_arg
  rw [Finset.univ_eq_attach, g.cycleFactorsFinset.prod_attach (fun i ↦ Fintype.card (zpowers i)),
    cycleType, Finset.prod_map_val]
  refine Finset.prod_congr rfl (fun x hx ↦ ?_)
  rw [Fintype.card_zpowers, (mem_cycleFactorsFinset_iff.mp hx).1.orderOf, Function.comp_apply]

end Kernel

section Sign

open Function

variable {a : Type*} (g : Perm α) (k : Perm (fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α))

theorem sign_kerParam_apply_apply :
    sign (kerParam g ⟨k, v⟩) = sign k * ∏ c, sign (v c).val := by
  rw [kerParam, MonoidHom.noncommCoprod_apply, ← Prod.fst_mul_snd ⟨k, v⟩, Prod.mk_mul_mk, mul_one,
    one_mul, map_mul, sign_ofSubtype, Finset.univ_eq_attach, mul_right_inj, ← MonoidHom.comp_apply,
    Subgroup.noncommPiCoprod, MonoidHom.comp_noncommPiCoprod _, MonoidHom.noncommPiCoprod_apply,
    Finset.univ_eq_attach, Finset.noncommProd_eq_prod]
  simp

theorem cycleType_kerParam_apply_apply :
    cycleType (kerParam g ⟨k, v⟩) = cycleType k + ∑ c, (v c).val.cycleType := by
  let U := (Finset.univ : Finset { x // x ∈ g.cycleFactorsFinset }).toSet
  have hU : U.Pairwise fun i j ↦ (v i).val.Disjoint (v j).val := fun c _ d _ h ↦ by
    obtain ⟨m, hm⟩ := (v c).prop
    obtain ⟨n, hn⟩ := (v d).prop
    simp only [← hm, ← hn]
    apply Disjoint.zpow_disjoint_zpow
    apply cycleFactorsFinset_pairwise_disjoint g c.prop d.prop
    exact Subtype.coe_ne_coe.mpr h
  rw [kerParam, MonoidHom.noncommCoprod_apply, ← Prod.fst_mul_snd ⟨k, v⟩, Prod.mk_mul_mk, mul_one,
    one_mul, Finset.univ_eq_attach, Disjoint.cycleType (disjoint_ofSubtype_noncommPiCoprod g k v),
    Subgroup.noncommPiCoprod_apply, Disjoint.cycleType_noncommProd hU, Finset.univ_eq_attach]
  exact congr_arg₂ _ cycleType_ofSubtype rfl

end Sign

end OnCycleFactors

open Nat

variable (g : Perm α)

-- Should one parenthesize the product ?
/-- Cardinality of the centralizer in `Equiv.Perm α` of a permutation given `cycleType` -/
theorem nat_card_centralizer :
    Nat.card (centralizer {g}) =
      (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)!) := by
  rw [← (toPermHom g).ker.card_mul_index, index_ker, nat_card_range_toPermHom,
    ← kerParam_range_card, ← Nat.card_eq_fintype_card, kerParam_range_eq, card_subtype]

theorem card_isConj_mul_eq :
    Nat.card {h : Perm α | IsConj g h} *
      ((Fintype.card α - g.cycleType.sum)! *
      g.cycleType.prod *
      (∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)!)) =
    (Fintype.card α)! := by
  classical
  rw [Nat.card_eq_fintype_card, ← nat_card_centralizer g]
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer, Nat.card_eq_fintype_card]
  convert MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct (Perm α)) g
  · ext h
    simp only [Set.mem_setOf_eq, ConjAct.mem_orbit_conjAct, isConj_comm]
  · rw [ConjAct.card, Fintype.card_perm]

/-- Cardinality of a conjugacy class in `Equiv.Perm α` of a given `cycleType` -/
theorem card_isConj_eq :
    Nat.card {h : Perm α | IsConj g h} =
      (Fintype.card α)! /
        ((Fintype.card α - g.cycleType.sum)! *
          g.cycleType.prod *
          (∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)!)) := by
  rw [← card_isConj_mul_eq g, Nat.div_eq_of_eq_mul_left _]
  · rfl
  -- This is the cardinal of the centralizer
  · rw [← nat_card_centralizer g]
    apply Nat.card_pos

variable (α)

theorem card_of_cycleType_eq_zero_iff {m : Multiset ℕ} :
    #({g | g.cycleType = m} : Finset (Perm α)) = 0
      ↔ ¬ ((m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a)) := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    ← exists_with_cycleType_iff, not_exists]
  simp

theorem card_of_cycleType_mul_eq (m : Multiset ℕ) :
    #({g | g.cycleType = m} : Finset (Perm α)) *
      ((Fintype.card α - m.sum)! * m.prod * (∏ n ∈ m.toFinset, (m.count n)!)) =
      if (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) then (Fintype.card α)! else 0 := by
  split_ifs with hm
  · -- nonempty case
    classical
    obtain ⟨g, rfl⟩ := (exists_with_cycleType_iff α).mpr hm
    convert card_isConj_mul_eq g
    simp_rw [Set.coe_setOf, Nat.card_eq_fintype_card, ← Fintype.card_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, ← isConj_iff_cycleType_eq, isConj_comm (g := g)]
  · -- empty case
    rw [(card_of_cycleType_eq_zero_iff α).mpr hm, zero_mul]

/-- Cardinality of the `Finset` of `Equiv.Perm α` of given `cycleType` -/
theorem card_of_cycleType (m : Multiset ℕ) :
    #({g | g.cycleType = m} : Finset (Perm α)) =
      if m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! * m.prod * (∏ n ∈ m.toFinset, (m.count n)!))
      else 0 := by
  split_ifs with hm
  · -- nonempty case
    apply symm
    apply Nat.div_eq_of_eq_mul_left
    · have : 0 < m.prod := Multiset.prod_pos <| fun a ha => zero_lt_two.trans_le (hm.2 a ha)
      positivity
    rw [card_of_cycleType_mul_eq, if_pos hm]
  · -- empty case
    exact (card_of_cycleType_eq_zero_iff α).mpr hm

open Fintype in
variable {α} in
/-- The number of cycles of given length -/
lemma card_of_cycleType_singleton {n : ℕ} (hn' : 2 ≤ n) (hα : n ≤ card α) :
    #({g | g.cycleType = {n}} : Finset (Perm α)) = (n - 1)! * (choose (card α) n) := by
  have hn₀ : n ≠ 0 := by omega
  have aux : n ! = (n - 1)! * n := by rw [mul_comm, mul_factorial_pred hn₀]
  rw [mul_comm, ← Nat.mul_left_inj hn₀, mul_assoc, ← aux, ← Nat.mul_left_inj (factorial_ne_zero _),
    Nat.choose_mul_factorial_mul_factorial hα, mul_assoc]
  simpa [ite_and, if_pos hα, if_pos hn', mul_comm _ n, mul_assoc]
    using card_of_cycleType_mul_eq α {n}

end Equiv.Perm
