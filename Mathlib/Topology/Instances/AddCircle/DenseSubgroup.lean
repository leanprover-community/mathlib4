/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Real.Irrational
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Irrational rotation is minimal

In this file we prove that the multiples of an irrational element of an `AddCircle` are dense.
Moreover, an additive subgroup of the circle is dense
iff it is not generated by a single element of finite additive order.

## Implementation detais

The statements can likely be generalized/multiplicativized to refer to `zpowers` of an irrational
element of a `Circle`, where one has `Real.log a b` is irrational as opposed to `a / b`.
-/

open Set Filter
open scoped Pointwise Topology

/-- The additive subgroup of real numbers generated by `a` and `b` is dense
iff `a / b` is an irrational number.

Here we rely on the fact that `a / 0 = 0` in Mathlib,
so we don't need to add `b ≠ 0` as an assumption. -/
theorem dense_addSubgroupClosure_pair_iff {a b : ℝ} :
    Dense (AddSubgroup.closure {a, b} : Set ℝ) ↔ Irrational (a / b) := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [pair_comm]
    simpa [← AddSubgroup.zmultiples_eq_closure] using not_denseRange_zsmul
  constructor
  · rintro hd ⟨r, hr⟩
    refine not_denseRange_zsmul (a := b / r.den) <| hd.mono ?_
    rw [← AddSubgroup.coe_zmultiples, SetLike.coe_subset_coe, AddSubgroup.closure_le,
      AddSubgroup.coe_zmultiples, pair_subset_iff]
    refine ⟨⟨r.num, ?_⟩, r.den, ?_⟩
    · field_simp [mul_div_left_comm _ b, ← Rat.cast_def, hr]
    · field_simp
  · intro h
    contrapose! h
    rcases (AddSubgroup.dense_or_cyclic _).resolve_left h with ⟨c, hc⟩
    have : {a, b} ⊆ range (· • c : ℤ → ℝ) := by
      rw [← AddSubgroup.coe_zmultiples, AddSubgroup.zmultiples_eq_closure, ← hc]
      apply AddSubgroup.subset_closure
    rcases pair_subset_iff.1 this with ⟨⟨m, rfl⟩, n, rfl⟩
    simp_all [mul_div_mul_right]

namespace AddCircle

/-- The multiples of a number `a` are dense on a circle of length `p` iff `a / p` is irrational. -/
theorem denseRange_zsmul_coe_iff {a p : ℝ} :
    DenseRange (· • a : ℤ → AddCircle p) ↔ Irrational (a / p) := by
  rw [← dense_addSubgroupClosure_pair_iff, DenseRange,
    ← QuotientAddGroup.dense_preimage_mk, ← QuotientAddGroup.coe_mk',
    ← AddSubgroup.coe_zmultiples, ← AddSubgroup.coe_comap, ← AddMonoidHom.map_zmultiples,
    AddSubgroup.comap_map_eq, QuotientAddGroup.ker_mk', AddSubgroup.zmultiples_eq_closure,
    AddSubgroup.zmultiples_eq_closure, ← AddSubgroup.closure_union, insert_eq]

/-- The multiples of a number `a` are dense on a circle of length `p ≠ 0`
iff `a` has infinite additive order. -/
theorem denseRange_zsmul_iff' {p : ℝ} {a : AddCircle p} (hp : p ≠ 0) :
    DenseRange (· • a : ℤ → AddCircle p) ↔ addOrderOf a = 0 := by
  rcases QuotientAddGroup.mk_surjective a with ⟨a, rfl⟩
  rw [denseRange_zsmul_coe_iff, addOrderOf_eq_zero_iff, isOfFinAddOrder_iff_nsmul_eq_zero]
  simp only [← coe_nsmul, coe_eq_zero_iff, not_exists, not_and, zsmul_eq_mul, nsmul_eq_mul]
  constructor
  · intro hi n hn m h
    rw [mul_comm _ a, ← div_eq_div_iff] at h <;> try positivity
    exact hi.ne_rat (m / n) (mod_cast h.symm)
  · rintro h ⟨r, hr⟩
    refine h r.den r.den_pos r.num ?_
    rw [mul_comm _ a, ← div_eq_div_iff, ← Rat.cast_def, hr] <;> try positivity

/-- The multiples of a number `a` are dense on a circle of length `0 < p`
iff `a` has infinite additive order. -/
theorem denseRange_zsmul_iff {p : ℝ} [hp : Fact (0 < p)] {a : AddCircle p} :
    DenseRange (· • a : ℤ → AddCircle p) ↔ addOrderOf a = 0 :=
  denseRange_zsmul_iff' hp.out.ne'

/-- A subgroup of the circle `ℝ⧸pℤ`, `p ≠ 0`, is dense
iff it is not generated by a single element of finite additive order. -/
theorem dense_addSubgroup_iff_ne_zmultiples' {p : ℝ} (hp : p ≠ 0) {s : AddSubgroup (AddCircle p)} :
    Dense (s : Set (AddCircle p)) ↔ ∀ a, addOrderOf a ≠ 0 → s ≠ .zmultiples a := by
  constructor
  · rintro hd a ha rfl
    rw [AddSubgroup.coe_zmultiples, ← DenseRange, denseRange_zsmul_iff' hp] at hd
    exact ha hd
  · intro h
    contrapose! h
    obtain ⟨a, rfl⟩ : ∃ a, s = .zmultiples a := by
      rw [← QuotientAddGroup.dense_preimage_mk, ← QuotientAddGroup.coe_mk',
        ← AddSubgroup.coe_comap, xor_iff_not_iff'.1 (AddSubgroup.dense_xor'_cyclic _)] at h
      rcases h with ⟨a, ha⟩
      use a
      rw [← QuotientAddGroup.coe_mk', ← AddMonoidHom.map_zmultiples, ← ha,
        AddSubgroup.map_comap_eq_self_of_surjective]
      exact Quot.mk_surjective
    exact ⟨a, (denseRange_zsmul_iff' hp).not.mp h, rfl⟩

/-- A subgroup of the circle `ℝ⧸pℤ`, `0 < p`, is dense
iff it is not generated by a single element of finite additive order. -/
theorem dense_addSubgroup_iff_ne_zmultiples {p : ℝ} [Fact (0 < p)] {s : AddSubgroup (AddCircle p)} :
    Dense (s : Set (AddCircle p)) ↔ ∀ a, addOrderOf a ≠ 0 → s ≠ .zmultiples a :=
  dense_addSubgroup_iff_ne_zmultiples' (Fact.out : 0 < p).ne'

end AddCircle
