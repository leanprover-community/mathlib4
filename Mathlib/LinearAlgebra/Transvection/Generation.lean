/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.LinearAlgebra.Projectivization.Action

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Transvections generate the special linear group

We prove the theorem of [Dieudonné-1955][J. Dieudonné, “Sur les générateurs
des groupes classiques”].

-/

@[expose] public section

theorem add_sub_sub_eq {G : Type*} [AddCommGroup G] (a b c d : G) :
    a + b - c - d = a - c + b - d := by
   abel

namespace SpecialLinearGroup

section generation

open Module.End Module Submodule

section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

abbrev fixedSubmodule (e : SpecialLinearGroup R V) :
    Submodule R V :=
  eigenspace (e : End R V) (1 : R)

theorem mem_fixedSubmodule_iff {e : SpecialLinearGroup R V} {v : V} :
    v ∈ e.fixedSubmodule ↔ e v = v := by simp

theorem fixedSubmodule_eq_top_iff {e : SpecialLinearGroup R V} :
    e.fixedSubmodule = ⊤ ↔ e = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by aesop⟩
  ext v
  suffices v ∈ e.fixedSubmodule by simpa using this
  simp [h]

theorem inf_fixedSubmodule_le_fixedSubmodule_mul (e f : SpecialLinearGroup R V) :
    e.fixedSubmodule ⊓ f.fixedSubmodule ≤ (e * f).fixedSubmodule := by
  intro; aesop

theorem mem_fixedSubmodule_transvection_iff {f : Module.Dual R V} {v : V} {hfv : f v = 0} {x : V} :
    x ∈ fixedSubmodule (transvection hfv) ↔ f x • v = 0 := by
  simp only [mem_fixedSubmodule_iff, transvection.apply, add_eq_left]

theorem fixedSubmodule_transvection_le {f : Module.Dual R V} {v : V} (hfv : f v = 0) :
    LinearMap.ker f ≤ fixedSubmodule (transvection hfv) := fun x hx ↦ by
  simp only [LinearMap.mem_ker] at hx
  rw [mem_fixedSubmodule_transvection_iff]
  simp [hx]

open scoped Pointwise

theorem transvections_pow_mono :
    Monotone (fun n : ℕ ↦ (transvections R V) ^ n) :=
  Set.pow_right_monotone one_mem_transvections

/-- The minimal number of transvections to write an element of the special linear group.

It is a priori a member of `ℕ∞`, but we will prove that it is a natural number. -/
noncomputable
def transvectionDegree (e : SpecialLinearGroup R V) : ℕ∞ :=
  sInf (Nat.cast '' {n | e ∈ (transvections R V) ^ n })

lemma transvectionDegree_eq_top_iff {e : SpecialLinearGroup R V} :
    transvectionDegree e = ⊤ ↔ {n | e ∈ transvections R V ^ n} = ∅ := by
  simp [transvectionDegree, Set.eq_empty_iff_forall_notMem]

@[simp] theorem transvectionDegree_one :
    transvectionDegree (1 : SpecialLinearGroup R V) = 0 := by
  simp [transvectionDegree, ENat.sInf_eq_zero]

theorem transvectionDegree_le_iff {e : SpecialLinearGroup R V} {n : ℕ} :
    transvectionDegree e ≤ n ↔ e ∈ (transvections R V) ^ n := by
  constructor
  · intro he
    have h : Set.Nonempty {n | e ∈ transvections R V ^ n} := by
      rw [Set.nonempty_iff_ne_empty]
      contrapose! he
      simp [transvectionDegree, he]
    rw [transvectionDegree, sInf_image, ← ENat.coe_sInf h, Nat.cast_le] at he
    exact transvections_pow_mono he (Nat.sInf_mem h)
  · intro he
    simp only [transvectionDegree, sInf_le_iff, mem_lowerBounds, Set.mem_image, Set.mem_setOf_eq,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro b hb
    exact hb n he

theorem transvectionDegree_mul_le {e f : SpecialLinearGroup R V} :
    transvectionDegree (e * f) ≤ transvectionDegree e + transvectionDegree f := by
  induction he : transvectionDegree e with
  | top => simp
  | coe m =>
    induction hf : transvectionDegree f with
    | top => simp
    | coe n =>
      replace he := le_of_eq he
      replace hf := le_of_eq hf
      rw [← ENat.coe_add]
      rw [transvectionDegree_le_iff] at he hf ⊢
      rw [pow_add]
      exact Set.mul_mem_mul he hf

theorem transvectionDegree_le_one_iff {e : SpecialLinearGroup R V} :
    transvectionDegree e ≤ 1 ↔ e ∈ transvections R V := by
  rw [← ENat.coe_one, transvectionDegree_le_iff, pow_one]

theorem transvectionDegree_le_of_transvection_mul
    (e t : SpecialLinearGroup R V) (ht : t ∈ transvections R V) :
    transvectionDegree e ≤ transvectionDegree (t * e) + 1 := by
  nth_rewrite 1 [← inv_mul_cancel_left t e]
  rw [add_comm]
  apply le_trans transvectionDegree_mul_le
  apply add_le_add_left
  rwa [transvectionDegree_le_one_iff, inv_mem_transvections]

end

open Pointwise

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem fixedSubmodule_transvection_eq_iff
    {f : Module.Dual K V} {v : V} (hfv : f v = 0) :
    fixedSubmodule (transvection hfv) = LinearMap.ker f ↔
      f = 0 ∨ v ≠ 0 := by
  constructor
  · intro h
    by_cases hf : f = 0
    · simp [hf]
    right
    have : ∃ x, f x ≠ 0 := by
      contrapose! hf
      exact LinearMap.ext hf
    obtain ⟨x, hx⟩ := this
    rw [Submodule.ext_iff] at h
    specialize h x
    rw [mem_fixedSubmodule_transvection_iff, LinearMap.mem_ker] at h
    aesop
  · intro h
    apply le_antisymm _ (fixedSubmodule_transvection_le hfv)
    intro x hx
    simp only [mem_fixedSubmodule_transvection_iff, smul_eq_zero] at hx
    simp only [LinearMap.mem_ker]
    aesop

theorem map_eq_of_mem_fixingSubgroup
    (W : Submodule K V) (e : SpecialLinearGroup K V)
    (he : e ∈ fixingSubgroup _ W.carrier) :
    map e.val W = W := by
  ext v
  simp [mem_fixingSubgroup_iff] at he
  refine ⟨fun ⟨w, hv, hv'⟩ ↦ ?_, fun hv ↦ ?_⟩
  · simp only [SetLike.mem_coe] at hv hv'
    rwa [← hv', he w hv]
  · refine ⟨v, hv, he v hv⟩

variable [Module.Finite K V]

theorem finrank_le_one_add_finrank_fixedSubmodule_of_mem_transvections
    {t : SpecialLinearGroup K V} (ht : t ∈ transvections K V) :
    finrank K V ≤ 1 + finrank K t.fixedSubmodule := by
  obtain ⟨f, v, hfv, rfl⟩ := ht
  have := Submodule.finrank_mono (fixedSubmodule_transvection_le hfv)
  rw [← Nat.add_le_add_iff_left (n := 1)] at this
  refine le_trans ?_ this
  rw [← (LinearMap.ker f).finrank_quotient_add_finrank,
      f.quotKerEquivRange.finrank_eq]
  simp only [add_le_add_iff_right]
  rw [← Module.finrank_self K]
  apply Submodule.finrank_le

theorem finrank_fixedSubmodule_add_le (e f : SpecialLinearGroup K V) :
    finrank K e.fixedSubmodule + finrank K f.fixedSubmodule ≤
      finrank K ↥(e.fixedSubmodule ⊔ f.fixedSubmodule) +
        finrank K (e * f).fixedSubmodule := by
  have := finrank_mono (inf_fixedSubmodule_le_fixedSubmodule_mul e f)
  rwa [← Nat.add_le_add_iff_left, finrank_sup_add_finrank_inf_eq] at this

theorem le_one_add_finrank_fixedSubmodule_transvection_mul
    (e t : SpecialLinearGroup K V) (ht : t ∈ transvections K V) :
    finrank K e.fixedSubmodule ≤ 1 + finrank K (t * e).fixedSubmodule := by
  have := finrank_fixedSubmodule_add_le t e
  have := finrank_le_one_add_finrank_fixedSubmodule_of_mem_transvections ht
  have : finrank K ↥(t.fixedSubmodule ⊔ e.fixedSubmodule) ≤ finrank K V :=
    finrank_le _
  linarith

theorem finrank_fixedSubmodule_transvection_mul_le
    (e t : SpecialLinearGroup K V) (ht : t ∈ transvections K V) :
     finrank K (t * e).fixedSubmodule ≤ 1 + finrank K e.fixedSubmodule := by
  conv_rhs => rw [show e = t⁻¹ * (t * e) from by aesop]
  rw [← inv_mem_transvections] at ht
  exact le_one_add_finrank_fixedSubmodule_transvection_mul (t * e) t⁻¹ ht

theorem le_one_add_finrank_fixedSubmodule_mul_transvection
    (e t : SpecialLinearGroup K V) (ht : t ∈ transvections K V) :
    finrank K e.fixedSubmodule ≤ 1 + finrank K (e * t).fixedSubmodule := by
  have := finrank_fixedSubmodule_add_le e t
  have := finrank_le_one_add_finrank_fixedSubmodule_of_mem_transvections ht
  have : finrank K ↥(e.fixedSubmodule ⊔ t.fixedSubmodule) ≤ finrank K V :=
    finrank_le _
  linarith

theorem finrank_fixedSubmodule_mul_transvection_le
    (e t : SpecialLinearGroup K V) (ht : t ∈ transvections K V) :
    finrank K (e * t).fixedSubmodule ≤ 1 + finrank K e.fixedSubmodule := by
  conv_rhs => rw [show e = (e * t) * t⁻¹ from by aesop]
  rw [← inv_mem_transvections] at ht
  exact le_one_add_finrank_fixedSubmodule_mul_transvection (e * t) t⁻¹ ht

/-- If an element of `SpecialLinearGroup K V` fixes a submodule `W`,
this is the element of `SpecialLinearGroup K (V ⧸ W)` deduced by quotient (as a `MonoidHom`). -/
def mkQ (W : Submodule K V) :
    fixingSubgroup (SpecialLinearGroup K V) W.carrier →* SpecialLinearGroup K (V ⧸ W) where
  toFun := fun ⟨e, he⟩ ↦
    { val := Quotient.equiv W W e (map_eq_of_mem_fixingSubgroup W e he)
      property := by
        simp only [carrier_eq_coe, mem_fixingSubgroup_iff, SetLike.mem_coe,
          smul_def] at he
        rw [← Units.val_inj, LinearEquiv.coe_det, Units.val_one]
        set f := LinearMap.restrict e (p := W) (q := W)
          (fun v hv ↦ by aesop) with hf
        change LinearMap.det (W.mapQ W e (fun v hv ↦ by aesop)) = 1
        suffices f = LinearMap.id by
          have that := e.property
          rwa [← Units.val_inj, LinearEquiv.coe_det, Units.val_one,
            LinearMap.det_eq_det_mul_det W e (fun v hv ↦ by
              simpa [he v hv]),
            ← hf, this, LinearMap.det_id, one_mul] at that
        aesop }
  map_one' := by aesop
  map_mul' e f := by
    simp only
    ext v
    obtain ⟨w, rfl⟩ := W.mkQ_surjective v
    simp

/-- For `e : SpecialLinearGroup K V`, the element
of `SpecialLinearGroup K (V ⧸ e.fixedSubmodule) induced by `e`. -/
def reduce (e : SpecialLinearGroup K V) :
    SpecialLinearGroup K (V ⧸ e.fixedSubmodule) :=
  mkQ e.fixedSubmodule ⟨e, by simp [mem_fixingSubgroup_iff]⟩

theorem reduce_apply (e : SpecialLinearGroup K V) (v : V) :
    e.reduce (Submodule.Quotient.mk v) = Submodule.Quotient.mk (e v) :=
  rfl

theorem reduce_eq_smul_id (e : SpecialLinearGroup K V) (a : K) :
    e.reduce = a • LinearMap.id (R := K) (M := V ⧸ e.fixedSubmodule) ↔
      ∀ v, e v - a • v ∈ e.fixedSubmodule := by
  rw [Submodule.linearMap_qext_iff, LinearMap.ext_iff]
  apply forall_congr'
  intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply, reduce_apply]
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, ← Submodule.mkQ_apply,
    ← map_smul]
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, Submodule.ker_mkQ]

theorem reduce_eq_one (e : SpecialLinearGroup K V) :
    e.reduce = 1 ↔ ∀ v, e v - v ∈ e.fixedSubmodule := by
  rw [← Subtype.coe_inj, ← LinearEquiv.toLinearMap_inj]
  simpa using reduce_eq_smul_id e 1

/-- An element of the special linear group is exceptional if
  it is a nontrivial homothety modulo the eigenspace for eigenvalue 1. -/
abbrev IsExceptional (e : SpecialLinearGroup K V) : Prop :=
  e.reduce ≠ 1 ∧ ∃ a : K, e.reduce = a • (LinearMap.id (M := V ⧸ e.fixedSubmodule) (R := K))

theorem _root_.Submodule.eq_top_iff_finrank_eq {W : Submodule K V} :
    W = ⊤ ↔ finrank K W = finrank K V := by
  refine ⟨fun h ↦ by rw [h, finrank_top], fun h ↦ ?_⟩
  apply Submodule.eq_of_le_of_finrank_le le_top
  rw [finrank_top, h]

theorem _root_.Submodule.sup_span_eq_top
    {W : Submodule K V} {v : V} (hW : finrank K (V ⧸ W) ≤ 1) (hv : v ∉ W) :
    W ⊔ Submodule.span K {v} = ⊤ := by
  apply Submodule.eq_top_of_disjoint
  · rw [← W.finrank_quotient_add_finrank, add_comm, add_le_add_iff_left]
    apply le_trans hW
    suffices v ≠ 0 by simpa
    aesop
  · exact Submodule.disjoint_span_singleton_of_notMem hv

theorem mem_transvections_iff_finrank_le_one (e : SpecialLinearGroup K V) :
    e ∈ transvections K V ↔ finrank K (V ⧸ e.fixedSubmodule) ≤ 1 := by
  constructor
  · rintro ⟨f, v, hfv, he⟩
    rw [← Nat.add_le_add_iff_right (n := finrank K e.fixedSubmodule),
      Submodule.finrank_quotient_add_finrank]
    suffices LinearMap.ker f ≤ e.fixedSubmodule by
      replace this := Submodule.finrank_mono this
      rw [← Nat.add_le_add_iff_left (n := 1)] at this
      refine le_trans ?_ this
      rw [← (LinearMap.ker f).finrank_quotient_add_finrank,
          f.quotKerEquivRange.finrank_eq]
      simp only [add_le_add_iff_right]
      rw [← Module.finrank_self K]
      apply Submodule.finrank_le
    intro x hx
    simp only [LinearMap.mem_ker] at hx
    simp [he, LinearMap.transvection.apply, hx]
  · intro h
    by_cases he : e = 1
    · use 0, 0, by simp, by aesop
    have he' : e.fixedSubmodule ≠ ⊤ := by
      rwa [ne_eq, fixedSubmodule_eq_top_iff]
    obtain ⟨w : V, hw : w ∉ e.fixedSubmodule⟩ :=
      SetLike.exists_not_mem_of_ne_top e.fixedSubmodule he' rfl
    obtain ⟨f, hfw, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
    set v := (f w)⁻¹ • (e w - w)
    have hf' : e.fixedSubmodule = LinearMap.ker f := by
      rw [← LinearMap.le_ker_iff_map] at hf
      apply Submodule.eq_of_le_of_finrank_le hf
      suffices finrank K (V ⧸ LinearMap.ker f) = 1 by
        have := e.fixedSubmodule.finrank_quotient_add_finrank
        have := (LinearMap.ker f).finrank_quotient_add_finrank
        linarith
      rw [← Nat.add_left_inj, Submodule.finrank_quotient_add_finrank]
      rw [← f.finrank_ker_add_one_of_ne_zero, add_comm]
      aesop
    have eq_top : e.fixedSubmodule ⊔ Submodule.span K {w} = ⊤ :=
      Submodule.sup_span_eq_top h hw
    suffices hfv : f v = 0 by
      use f, v, hfv
      rw [← Subtype.coe_inj, ← LinearEquiv.toLinearMap_inj,
        ← sub_eq_zero, ← LinearMap.ker_eq_top, eq_top_iff, ← eq_top]
      simp only [transvection.coe_toLinearEquiv, LinearEquiv.transvection.coe_toLinearMap,
        sup_le_iff, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearEquiv.coe_coe]
      constructor
      · intro x hx
        suffices f x = 0 by
          simpa [this, LinearMap.transvection.apply, sub_eq_zero] using hx
        rwa [hf', LinearMap.mem_ker] at hx
      · simp [v, LinearMap.transvection.apply]
        field_simp
        aesop
    suffices e w - w ∈ LinearMap.ker f by
      simp only [LinearMap.mem_ker, map_sub] at this
      simp only [v, map_smul]
      convert smul_zero _
      simpa using this
    rw [← hf', ← Submodule.ker_mkQ e.fixedSubmodule, LinearMap.mem_ker]
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_sub]
    simp only [← reduce_apply, sub_eq_zero]
    suffices e.reduce = 1 by simp [this]
    suffices Subsingleton (SpecialLinearGroup K (V ⧸ e.fixedSubmodule)) by
      exact Subsingleton.eq_one e.reduce
    exact subsingleton_of_finrank_le_one h

theorem finrank_le_add_finrank_fixedSubmodule
    {n : ℕ} {e : SpecialLinearGroup K V} (he : e ∈ transvections K V ^ n) :
    finrank K V ≤ n + finrank K e.fixedSubmodule := by
  induction n generalizing e with
  | zero =>
    simp only [pow_zero, Set.mem_one] at he
    rw [zero_add]
    suffices e.fixedSubmodule = ⊤ by
      rw [this, finrank_top]
    aesop
  | succ n hind =>
    rw [pow_succ] at he
    obtain ⟨f, hf, t, ht, he⟩ := he
    refine Nat.le_trans (hind hf) ?_
    rw [← he, add_assoc, Nat.add_le_add_iff_left]
    exact le_one_add_finrank_fixedSubmodule_mul_transvection f t ht

theorem finrank_le_transvectionDegree_add (e : SpecialLinearGroup K V) :
    finrank K V ≤ transvectionDegree e + finrank K e.fixedSubmodule := by
  induction hn : transvectionDegree e with
  | top => simp
  | coe n =>
    rw [← ENat.coe_add, ENat.coe_le_coe]
    apply finrank_le_add_finrank_fixedSubmodule
    rw [← transvectionDegree_le_iff, hn]

theorem fincorank_le_transvectionDegree (e : SpecialLinearGroup K V) :
    finrank K (V ⧸ e.fixedSubmodule) ≤ transvectionDegree e := by
  rw [← ENat.add_le_add_iff_right (ENat.coe_ne_top _),
    ← ENat.coe_add, Submodule.finrank_quotient_add_finrank]
  exact finrank_le_transvectionDegree_add e

lemma _root_.Submodule.exists_dual_map_eq_bot_of_notMem'
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {p : Submodule K V} {x : V} (hx : x ∉ p) :
    ∃ f : Dual K V, f x = 1 ∧ map f p = ⊥ := by
  obtain ⟨g, hfu, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  rw [← LinearMap.le_ker_iff_map] at *
  use (g x)⁻¹ • g
  aesop

theorem finrank_sup_span_singleton {p : Submodule K V} {v : V} (hv : v ∉ p) :
    finrank K (p ⊔ Submodule.span K {v} : Submodule K V) = finrank K p + 1 := by
  rw [← Nat.add_left_inj, Submodule.finrank_sup_add_finrank_inf_eq, add_assoc]
  simp only [Nat.add_left_cancel_iff]
  rw [finrank_span_singleton (by aesop)]
  simp only [Nat.left_eq_add, finrank_eq_zero]
  rw [eq_bot_iff]
  intro x
  simp only [Submodule.mem_inf, Submodule.mem_span_singleton]
  rintro ⟨hx, ⟨a, hx'⟩⟩
  suffices a = 0 by simp [← hx', this]
  contrapose hv
  suffices v = (1 / a) • x by
    rw [this]
    exact p.smul_mem _ hx
  aesop

theorem fixedSubmodule_transvection_mul
    {e : SpecialLinearGroup K V} {f : Dual K V} {v : V}
    (hv : v ∉ e.fixedSubmodule) (hf : e.fixedSubmodule.map f = ⊥)
    (hfv : f (v - e v) = 0) (hfv' : f (e v) = 1) :
    (transvection hfv * e).fixedSubmodule = e.fixedSubmodule ⊔ (Submodule.span K {v}) := by
  symm
  suffices _ by
    apply Submodule.eq_of_le_of_finrank_le this
    rw [finrank_sup_span_singleton hv, add_comm]
    apply finrank_fixedSubmodule_transvection_mul_le
    apply mem_transvections
  simp only [sup_le_iff, Submodule.span_singleton_le_iff_mem]
  have ht : e.fixedSubmodule ≤ (transvection hfv).fixedSubmodule := fun x hx ↦ by
    rw [mem_fixedSubmodule_transvection_iff, smul_eq_zero]
    left
    rw [← Submodule.mem_bot K, ← hf]
    exact mem_map_of_mem hx
  constructor
  · -- e.fixedSubmodule ≤ e'.fixedSubmodule
    intro x hx
    simp only [mem_fixedSubmodule_iff, coe_mul, LinearEquiv.mul_apply]
    suffices transvection hfv x = x by
      simp only [mem_fixedSubmodule_iff] at hx
      simp only [hx, this]
    rw [← mem_fixedSubmodule_iff]
    exact ht hx
  · -- u ∈ e.fixedSubmodule
    simp only [mem_fixedSubmodule_iff, coe_mul, LinearEquiv.mul_apply,
      transvection.apply]
    simp [hfv']

/-- If an element `e` of `SpecialLinearGroup K V` is such that `e.reduce = 1`,
then `e` is the product of at most `finrank K (V ⧸ e.fixedSubmodule)` transvections.

This is the first non-exceptional case in Dieudonné's theorem. -/
theorem transvectionDegree_le_of_reduce_eq_one
    (e : SpecialLinearGroup K V) (he : e.reduce = 1) :
    e.transvectionDegree ≤ finrank K (V ⧸ e.fixedSubmodule) := by
  induction h : finrank K (V ⧸ e.fixedSubmodule) generalizing e he with
  | zero =>
    suffices e = 1 by simp [this, transvectionDegree_one]
    ext v
    suffices v ∈ e.fixedSubmodule by simpa using this
    suffices e.fixedSubmodule = ⊤ by simp [this]
    apply Submodule.eq_top_of_finrank_eq
    rw [← Nat.add_right_inj (n := 0), ← h, Submodule.finrank_quotient_add_finrank,h, zero_add]
  | succ n hind =>
    match n with
    | 0 =>
      rw [zero_add, Nat.cast_one, transvectionDegree_le_one_iff,
        mem_transvections_iff_finrank_le_one, h]
    | n + 1 =>
      simp only [add_assoc, Nat.reduceAdd] at h
      have : ∃ u : V, u ∉ e.fixedSubmodule := by
        by_contra! he
        rw [← eq_top_iff'] at he
        rw [he, ← Nat.add_left_inj, Submodule.finrank_quotient_add_finrank, finrank_top] at h
        simp at h
      obtain ⟨u, hu⟩ := this
      have hu' : e u - u ∈ e.fixedSubmodule := by
        rw [← e.fixedSubmodule.ker_mkQ, LinearMap.mem_ker,
          map_sub, sub_eq_zero]
        simp [← reduce_apply, he]
      simp only at hu'
      have hu'' : e u - u ≠ 0 := by
        rwa [ne_eq, sub_eq_zero, ← mem_fixedSubmodule_iff]
      simp only at hu''
      obtain ⟨f, hfu, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem' hu
      set t := SpecialLinearGroup.transvection (f := f) (v := u - e u) (by
        simp only [← LinearMap.mem_ker]
        rw [← LinearMap.le_ker_iff_map] at hf
        apply hf
        rwa [sub_mem_comm_iff] at hu') with ht
      have ht_fixed : e.fixedSubmodule ≤ t.fixedSubmodule := fun x hx ↦ by
        simp only [mem_fixedSubmodule_iff, ht, transvection.apply, add_eq_left, smul_eq_zero]
        rw [← LinearMap.le_ker_iff_map] at hf
        exact Or.inl (hf hx)
      rw [ENat.coe_add, ENat.coe_one]
      apply le_trans (transvectionDegree_le_of_transvection_mul e t (mem_transvections _))
      apply add_le_add_left
      set e' := t * e with he'
      have he'_rank : finrank K (e.fixedSubmodule ⊔ Submodule.span K {u} : Submodule K V) =
        finrank K e.fixedSubmodule + 1 :=
        finrank_sup_span_singleton hu
      have he'_fixed : e'.fixedSubmodule = e.fixedSubmodule ⊔ Submodule.span K {u} := by
        apply fixedSubmodule_transvection_mul hu hf
        rw [← hfu, ← sub_eq_zero, ← map_sub, ← Submodule.mem_bot K, ← hf]
        exact mem_map_of_mem hu'
      apply hind
      · simp only [reduce_eq_one, he'_fixed] at he ⊢
        intro v
        simp only [he', ht, coe_mul, LinearEquiv.mul_apply,
          transvection.apply, add_sub_right_comm]
        apply Submodule.mem_sup_left
        apply Submodule.add_mem _ (he v)
        apply Submodule.smul_mem
        rwa [← Submodule.neg_mem_iff, neg_sub]
      · rw [← Nat.add_left_inj (n := 1), add_assoc]
        simp only [Nat.reduceAdd]
        rw [add_comm _ 1]
        rw [← Nat.add_left_inj, add_assoc, Submodule.finrank_quotient_add_finrank, he'_fixed]
        rw [he'_rank, ← h, ← add_assoc]
        rw [Submodule.finrank_quotient_add_finrank, add_comm]

theorem _root_.LinearMap.eq_smul_id
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {f : V →ₗ[K] V}
    (h : ∀ v, ¬ LinearIndependent K ![v, f v]) :
    ∃ a : K, f = a • LinearMap.id (R := K) (M := V) := by
  nontriviality V
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  have h' (v : V) (hv : v ≠ 0) : ∃ a : K, f v = a • v := by
    specialize h v
    simp only [LinearIndependent.pair_iff, not_forall] at h
    obtain ⟨x, y, hxy, h⟩ := h
    suffices y ≠ 0 by
      use (- x / y)
      rw [← IsUnit.smul_left_cancel (Ne.isUnit this),
        ← mul_smul]
      field_simp
      rwa [← sub_eq_zero, neg_smul, sub_neg_eq_add, add_comm]
    intro hy
    refine h ⟨?_, hy⟩
    simp only [hy, zero_smul, add_zero, smul_eq_zero] at hxy
    exact Or.resolve_right hxy hv
  obtain ⟨a, hau⟩ := h' u hu
  use a
  ext v
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨b, hbv⟩ := h' v hv
  suffices b = a by simp [this, hbv]
  by_cases huv : LinearIndependent K ![u, v]
  · rw [LinearIndependent.pair_iff] at huv
    have : u + v ≠ 0 := fun h ↦ by simpa [h] using huv 1 1
    obtain ⟨c, hcw⟩ := h' (u + v) this
    simp only [map_add, hau, hbv, smul_add] at hcw
    rw [← sub_eq_zero, add_sub_add_comm, ← sub_smul, ← sub_smul] at hcw
    specialize huv _ _ hcw
    simp only [sub_eq_zero] at huv
    rw [huv.2, huv.1]
  · simp only [LinearIndependent.pair_iff, not_forall, not_and] at huv
    obtain ⟨x, y, hxy, h'⟩ := huv
    have hx : x ≠ 0 := fun hx ↦ by
      simp only [hx, zero_smul, zero_add, smul_eq_zero] at hxy
      apply h' hx
      exact Or.resolve_right hxy hv
    suffices b • u = a • u by
      rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at this
      exact Or.resolve_right this hu
    suffices x • b • u = x • a • u by
      rw [← sub_eq_zero, ← smul_sub, smul_eq_zero, sub_eq_zero] at this
      apply Or.resolve_left this hx
    rw [← eq_neg_iff_add_eq_zero] at hxy
    rw [← hau, ← map_smul, hxy, map_neg, map_smul, hbv, smul_comm x b, smul_comm y b, hxy]
    simp

theorem _root_.LinearMap.center
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {f : End K V} :
    f ∈ Subalgebra.center K (End K V) ↔ ∃ a : K, f = a • LinearMap.id  := by
  nontriviality V
  refine ⟨fun hf ↦ ?_, fun ⟨a, hfa⟩ ↦ ?_⟩
  · apply LinearMap.eq_smul_id
    intro v hv
    have : v ≠ 0 := hv.ne_zero 0
    apply this
    suffices ∃ g : End K V, g v = v ∧ g (f v) = v + f v by
      obtain ⟨g, hgv, hgfv⟩ := this
      rw [Subalgebra.mem_center_iff] at hf
      specialize hf g
      rw [LinearMap.ext_iff] at hf
      specialize hf v
      simpa [hgfv, hgv] using hf
    suffices ∃ φ : Dual K V, φ v = 0 ∧ φ (f v) = 1 by
      obtain ⟨φ, hφv, hφfv⟩ := this
      use LinearMap.transvection φ v
      simp [LinearMap.transvection.apply, hφv, hφfv, add_comm]
    obtain ⟨φ, hφ, hφ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
        (x := f v) (p := K ∙ v) (fun h ↦ by
          rw [mem_span_singleton] at h
          obtain ⟨a, ha⟩ := h
          rw [LinearIndependent.pair_iff] at hv
          apply one_ne_zero (α := K)
          simpa [← ha] using hv (-a) 1) inferInstance
    use (φ (f v))⁻¹ • φ
    constructor
    · simp only [LinearMap.smul_apply]
      convert smul_zero _
      rw [← mem_bot K, ← hφ']
      apply mem_map_of_mem
      simp
    field_simp
    aesop
  · rw [Subalgebra.mem_center_iff]
    aesop

/-- If an element `e` of `SpecialLinearGroup K V` is such that
  `e.reduce` is not a homothety, then `e` is the product of at
  most `finrank K (V ⧸ e.fixedSubmodule)` transvections.

This is the second non-exceptional case in Dieudonné's theorem. -/
theorem transvectionDegree_of_reduce_ne_smul_id
    (e : SpecialLinearGroup K V)
    (he : ∀ a : K, e.reduce ≠ a • LinearMap.id (R := K) (M := V ⧸ e.fixedSubmodule)) :
    e.transvectionDegree ≤ finrank K (V ⧸ e.fixedSubmodule) := by
  induction h : finrank K (V ⧸ e.fixedSubmodule) generalizing e he with
  | zero =>
    -- this part is identical, makes a lemma ?
    suffices e = 1 by simp [this, transvectionDegree_one]
    ext v
    suffices v ∈ e.fixedSubmodule by simpa using this
    suffices e.fixedSubmodule = ⊤ by simp [this]
    apply Submodule.eq_top_of_finrank_eq
    rw [← Nat.add_right_inj (n := 0), ← h, Submodule.finrank_quotient_add_finrank,h, zero_add]
  | succ n hind =>
    match n with
    | 0 =>
      -- this part is identical
      rw [zero_add, Nat.cast_one, transvectionDegree_le_one_iff,
        mem_transvections_iff_finrank_le_one, h]
    | n + 1 =>
      rw [ENat.coe_add, ENat.coe_one]
      simp only [add_assoc, Nat.reduceAdd] at h
      have : ∃ v, LinearIndependent K ![v, e.reduce v] := by
        by_contra! h
        obtain ⟨a, ha⟩ := LinearMap.eq_smul_id h
        exact he a ha
      obtain ⟨v, hu⟩ := this
      obtain ⟨u, rfl⟩ := e.fixedSubmodule.mkQ_surjective v
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, mkQ_apply,
        SpecialLinearGroup.reduce_apply] at hu
      simp only [LinearIndependent.pair_iff] at  hu
      have hu' : e u ∉ e.fixedSubmodule ⊔ Submodule.span K {e u - u} := fun hu' ↦ by
        rw [Submodule.mem_sup] at hu'
        obtain ⟨y, hy, z, hz, hu'⟩ := hu'
        rw [Submodule.mem_span_singleton] at hz
        obtain ⟨a, rfl⟩ := hz
        specialize hu a (1 - a) ?_
        · simp only [← mkQ_apply, ← map_smul, ← map_add, ← LinearMap.mem_ker,
            Submodule.ker_mkQ]
          convert hy
          simp only at hu'
          rw [eq_comm, ← sub_eq_iff_eq_add, eq_comm] at hu'
          rw [map_smul, hu']
          module
        · aesop
      let t (f : Dual K V) (hf : e.fixedSubmodule ⊔ K ∙ (e u - u) ≤ LinearMap.ker f) :
        SpecialLinearGroup K V :=
        SpecialLinearGroup.transvection (f := f) (v := u - e u) (by
          simp only [← LinearMap.mem_ker]
          apply hf
          apply Submodule.mem_sup_right
          rw [mem_span_singleton]
          exact ⟨-1, by simp⟩)
      have ht_fixed (f : Dual K V) (hf : e.fixedSubmodule ⊔ K ∙ (e u - u) ≤ LinearMap.ker f) :
           e.fixedSubmodule ≤ (t f hf : SpecialLinearGroup K V).fixedSubmodule := fun x hx ↦ by
        simp only [mem_fixedSubmodule_iff, t]
        simp only [transvection.coe_toLinearEquiv, LinearEquiv.transvection.coe_apply,
          LinearMap.transvection.apply, add_eq_left, smul_eq_zero]
        left
        rw [← LinearMap.mem_ker]
        apply hf
        apply Submodule.mem_sup_left hx
      have he'_rank :
        finrank K (e.fixedSubmodule ⊔ Submodule.span K {u} : Submodule K V) =
          finrank K e.fixedSubmodule + 1 := by
        apply finrank_sup_span_singleton
        contrapose! hu'
        suffices e u = u by simp [this]
        rwa [mem_fixedSubmodule_iff] at hu'
      have he'_rank' :
        finrank K (V ⧸ (e.fixedSubmodule ⊔ Submodule.span K {u})) = n + 1 := by
        rw [← Nat.add_left_inj (n := 1), add_assoc]
        simp only [Nat.reduceAdd]
        rw [add_comm _ 1]
        rw [← Nat.add_left_inj, add_assoc, Submodule.finrank_quotient_add_finrank, he'_rank]
        rw [← h, ← add_assoc]
        rw [Submodule.finrank_quotient_add_finrank, add_comm]
      have he'_fixed (f : Dual K V) (hf : e.fixedSubmodule ⊔ K ∙ (e u - u) ≤ LinearMap.ker f)
        (hfu : f (e u) = 1) :
        (t f hf * e).fixedSubmodule = e.fixedSubmodule ⊔ Submodule.span K {u} := by
        apply fixedSubmodule_transvection_mul
        · contrapose hu'
          apply mem_sup_left
          rw [mem_fixedSubmodule_iff] at hu' ⊢
          simp [hu']
        · rw [eq_bot_iff]
          rw [Submodule.gc_map_comap, Submodule.comap_bot]
          exact le_trans le_sup_left hf
        exact hfu
      obtain ⟨f, hfv, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem' hu'
      rw [← LinearMap.le_ker_iff_map] at hf
      set e' := t f hf * e with e'_def
      by_cases he' : e'.transvectionDegree ≤ n + 1
      · -- this is the easy case where one knows that `e'` is
        -- the product of at most `n + 1` transvections
        apply le_trans (transvectionDegree_le_of_transvection_mul e (t f hf) (mem_transvections _))
        apply add_le_add_left he'
      -- in the remaining case, one has `0 < n`
      have hn_pos : 0 < n := by
        contrapose! he'
        simp only [nonpos_iff_eq_zero] at he'
        rw [← ENat.coe_one, ← ENat.coe_add, ← he'_rank', ← he'_fixed f hf hfv, ← e'_def]
        apply transvectionDegree_le_of_reduce_eq_one e'
        suffices Subsingleton (SpecialLinearGroup K (V ⧸ e'.fixedSubmodule)) by
          exact Subsingleton.eq_one e'.reduce
        apply subsingleton_of_finrank_le_one
        rw [he'_fixed f hf hfv, he'_rank', he']
      -- and we will need to modify `e'` by changing `f`.
      -- the induction hypothesis implies that `e'.reduce` is a homothety
      have : ∃ a : K, e'.reduce = a • LinearMap.id (R := K) (M := V ⧸ e'.fixedSubmodule) := by
        contrapose! he'
        apply hind e' he'
        rw [e'_def, he'_fixed f hf hfv, he'_rank']
      obtain ⟨a , ha⟩ := this
      have hne_top : (e.fixedSubmodule ⊔ K ∙ (e u - u) ⊔ K ∙ u : Submodule K V) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro h
        suffices n + 1 ≤ 1 by
          apply Nat.pos_iff_ne_zero.mp hn_pos
          simpa using this
        rw [sup_right_comm] at h
        rw [← he'_rank', ← Nat.add_le_add_iff_right, finrank_quotient_add_finrank,
          ← finrank_top K V, ← h, add_comm]
        apply le_trans (Submodule.finrank_add_le_finrank_add_finrank _ _)
        simp only [add_le_add_iff_left]
        apply le_trans (finrank_span_le_card {e u - u})
        simp
      obtain ⟨g : Dual K V, hg1 : g ≠ 0, hg2⟩ :=
        Submodule.exists_dual_map_eq_bot_of_lt_top hne_top inferInstance
      have hg : e.fixedSubmodule ⊔ K ∙ (e u - u) ≤ LinearMap.ker (f + g) := fun x hx ↦ by
        simp only [LinearMap.mem_ker, LinearMap.add_apply]
        suffices f x = 0 by
          rw [this, zero_add, ← Submodule.mem_bot K, ← hg2]
          exact mem_map_of_mem (mem_sup_left hx)
        rw [← LinearMap.mem_ker]
        exact hf hx
      have hgv : (f + g) (e u) = 1 := by
        simp only [LinearMap.add_apply, hfv, add_eq_left]
        rw [← Submodule.mem_bot K, ← hg2]
        apply mem_map_of_mem
        rw [sup_assoc]
        apply mem_sup_right
        simp only [mem_sup, mem_span_singleton, exists_exists_eq_and]
        use 1, 1, by simp
      let e'' := t (f + g) hg * e
      suffices transvectionDegree e'' ≤ n + 1 by
        apply le_trans <|
          transvectionDegree_le_of_transvection_mul e (t (f + g) hg) (mem_transvections _)
        apply add_le_add_left this
      apply hind
      · intro b hb
        rw [reduce_eq_smul_id] at ha hb
        have (v : V) : g (e v) • (u - e u) - (b - a) • v ∈ e.fixedSubmodule ⊔ K ∙ u := by
          specialize ha v
          specialize hb v
          simp only [e', he'_fixed f hf hfv] at ha
          simp only [e'', he'_fixed (f + g) hg hgv] at hb
          simp only [coe_mul, LinearEquiv.mul_apply, transvection.coe_toLinearEquiv,
            LinearEquiv.transvection.coe_apply, LinearMap.transvection.apply, t] at ha hb
          convert Submodule.sub_mem _ hb ha using 1
          simp only [smul_sub, LinearMap.add_apply, add_smul]
          module
        simp only at this
        exfalso
        set c := b - a
        by_cases hc : c = 0
        · simp only [hc, zero_smul, sub_zero] at this
          suffices ∃ v, g (e v) = 1 by
            obtain ⟨v, hv⟩ := this
            specialize this v
            simp only [hv, one_smul, mem_sup, mem_span_singleton, exists_exists_eq_and] at this ⊢
            obtain ⟨y, hy, k, this⟩ := this
            apply one_ne_zero (α := K)
            refine (hu (k - 1) 1 ?_).right
            simp only [← e.fixedSubmodule.mkQ_apply, ← map_smul, one_smul, ← map_add,
              ← LinearMap.mem_ker, Submodule.ker_mkQ]
            rw [← Submodule.neg_mem_iff] at hy
            convert hy using 1
            rw [eq_comm, ← sub_eq_iff_eq_add] at this
            rw [← this]
            module
          suffices ∃ w, g w ≠ 0 by
            obtain ⟨w, hw⟩ := this
            use (1 / g w) • e⁻¹ w
            simp [hw]
          contrapose! hg1
          rwa [LinearMap.ext_iff]
        · rw [lt_top_iff_ne_top] at hne_top
          apply hne_top
          rw [eq_top_iff]
          intro v _
          rw [sup_right_comm, Submodule.mem_sup]
          simp only [Submodule.mem_span_singleton, exists_exists_eq_and]
          specialize this v
          set z := g (e v) • (u - e u) - c • v with hz
          suffices that : - (1 / c) • z + (- g (e v) / c) • (e u - u) = v by
            refine ⟨_, ?_, _, that⟩
            exact smul_mem (e.fixedSubmodule ⊔ K ∙ u) (-(1 / c)) this
          rw [← IsUnit.smul_left_cancel (a := c)]
          · simp only [one_div, neg_smul, smul_add, smul_neg, hz, ← mul_smul]
            field_simp
            module
          · rwa [isUnit_iff_ne_zero]
      · rw [he'_fixed (f + g) hg, he'_rank']
        simp only [LinearMap.add_apply, hfv, add_eq_left]
        rw [← Submodule.mem_bot K, ← hg2]
        apply Submodule.mem_map_of_mem
        rw [sup_assoc]
        apply Submodule.mem_sup_right
        simp only [mem_sup, mem_span_singleton, exists_exists_eq_and]
        use 1, 1, by module

-- delete
theorem ENat.eq_coe_sub_coe_iff {a : ℕ∞} {b c : ℕ} (h : b ≤ c) :
    a = c - b ↔ c = a + b := by
  induction a with
  | top => simp [← ENat.coe_sub]
  | coe a =>
    simp only [← ENat.coe_add, ← ENat.coe_sub, ENat.coe_inj]; aesop

theorem _root_.Module.Dual.finrank_le_one_add_finrank_ker_inf
    (f : Dual K V) (W : Submodule K V) :
    finrank K W ≤ 1 + finrank K (LinearMap.ker f ⊓ W : Submodule K V) := by
  rw [add_comm, ← Nat.add_le_add_iff_left, ← add_assoc,
      finrank_sup_add_finrank_inf_eq, add_assoc, add_comm _ 1,
      ← add_assoc, add_le_add_iff_right]
  apply le_trans (finrank_le _)
  by_cases hf : f = 0
  · rw [hf, LinearMap.ker_zero, finrank_top]
    exact Nat.le_add_right (finrank K V) 1
  · rw [Dual.finrank_ker_add_one_of_ne_zero hf]

/-- If an element of `SpecialLinearGroup K V` is not exceptional,
then it is a product of exactly `finrank K (V ⧸ e.fixedSubmodule)` transvection,
and not less. (Dieudonné's theorem) -/
theorem transvectionDegree_of_not_isExceptional
    {e : SpecialLinearGroup K V} (he : ¬ IsExceptional e) :
    transvectionDegree e = finrank K (V ⧸ e.fixedSubmodule) := by
  apply le_antisymm _ (fincorank_le_transvectionDegree e)
  simp only [IsExceptional, ne_eq, not_and, not_exists] at he
  by_cases h : e.reduce = 1
  · exact transvectionDegree_le_of_reduce_eq_one e h
  · exact transvectionDegree_of_reduce_ne_smul_id e (he h)

example (e : SpecialLinearGroup K V) (a : K) (he1 : e ≠ 1)
    (he : e = a • LinearMap.id (R := K) (M := V)) :
    e ∉ (transvections K V) ^ ((finrank K V)) := by
  induction hn : finrank K V generalizing V with
  | zero => simpa using he1
  | succ n hind =>
    rw [pow_succ]
    rintro ⟨e', he', t, ⟨f, v, hfv, rfl⟩, h⟩
    simp only at h
    rw [eq_comm, ← mul_inv_eq_iff_eq_mul,  transvection.inv _ (by simp [hfv]), ← Subtype.coe_inj, LinearEquiv.ext_iff] at h
    generalize_proofs _ hfv' at h
    have he'_eq (x : V) : e' x = a • x - a • f x • v := by
      specialize h x
      simp [LinearMap.transvection.apply] at h
      rw [← LinearEquiv.coe_toLinearMap, he] at h
      simp_rw [← h]
      simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
      module
    have he'_fixed: e'.fixedSubmodule = K ∙ v := sorry
    have he'_red : e'.reduce = a • LinearMap.id (R := K) (M := V ⧸ e'.fixedSubmodule) := sorry
    apply hind e'.reduce ?_ ?_ ?_
    · sorry
    · sorry
      -- soit 0 < n et c'est OK, a ≠ 1
      -- soit n = 0, et a = 1 aussi
    · sorry -- he'_eq et he'_red
    · sorry



/-- If an element of `SpecialLinearGroup K V` is a product of
exactly `finrank K (V ⧸ e.fixedSubmodule)` transvections,
then it is not exceptional. (Dieudonné's theorem) -/
example (e : SpecialLinearGroup K V)
    (n : ℕ) (hn : n = finrank K (V ⧸ e.fixedSubmodule))
    (he : e ∈ transvections K V ^ n) :
    ¬ IsExceptional e := by
  intro he'
  have : ∃ t : Fin (finrank K V) → SpecialLinearGroup K V,
    e = Fin.prod t ∧ ∀ i, t i ∈ transvections K V := sorry
  obtain ⟨t, he', ht⟩ := this
  set f := fun i ↦ (ht i).choose
  set v := fun i ↦ (ht i).choose_spec.choose
  have hfv (i) : f i (v i) = 0 := (ht i).choose_spec.choose_spec.choose
  have ht (i) : t i = transvection (hfv i) := (ht i).choose_spec.choose_spec.choose_spec
  have he_fixed : e.fixedSubmodule = iInf (fun i ↦ LinearMap.ker (f i)) :=
    sorry
  induction n generalizing e with
  | zero =>
    simp only [pow_zero, Set.mem_one] at he
    rw [he]
    intro he'
    exact he'.1 (map_one _)
  | succ n hind =>
    rw [pow_succ, Set.mem_mul] at he
    obtain ⟨e', he', t, ⟨f, v, hfv, rfl⟩, he⟩ := he
    have this : e.fixedSubmodule = LinearMap.ker f ⊓ e'.fixedSubmodule := by
      symm
      apply Submodule.eq_of_le_of_finrank_le
      · replace he := congr($he x)
        simp only [SetLike.mem_coe, mem_fixedSubmodule_iff] at hxe
        simp only [SetLike.mem_coe, LinearMap.mem_ker] at hfx
        simpa [eq_comm, LinearMap.transvection.apply, hfx, hxe, mem_fixedSubmodule_iff] using he
      rw [← Nat.add_le_add_iff_left, Submodule.finrank_quotient_add_finrank, ← hn]
      apply le_trans (finrank_le_add_finrank_fixedSubmodule he')
      simp only [add_assoc, add_le_add_iff_left]
      exact Dual.finrank_le_one_add_finrank_ker_inf f e'.fixedSubmodule
    have that : ¬ (e'.IsExceptional) := by
      apply hind _ _ he'
      apply le_antisymm
      · rw [← Nat.add_le_add_iff_right, hn,
        ← Nat.add_le_add_iff_right, finrank_quotient_add_finrank,
        this]
        rw [← finrank_quotient_add_finrank e'.fixedSubmodule]
        simp only [add_assoc, add_le_add_iff_left]
        exact Dual.finrank_le_one_add_finrank_ker_inf f e'.fixedSubmodule
      · rw [← Nat.add_le_add_iff_right, finrank_quotient_add_finrank]
        exact finrank_le_add_finrank_fixedSubmodule he'
    ---
    rintro ⟨her_ne_one, a, her_eq⟩
    have : Submodule.map e'.val (LinearMap.ker f) ≤ LinearMap.ker f := by
      rintro _ ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker] at hx ⊢
      have : ∀ x ∈ LinearMap.ker f, e' x = a • x := fun x hx ↦ by
        rw [eq_comm, ← mul_inv_eq_iff_eq_mul] at he
        rw [← he]
        simp only [coe_mul, coe_inv, transvection.coe_toLinearEquiv, LinearEquiv.mul_apply,
          LinearEquiv.coe_inv]
        rw [LinearEquiv.transvection.symm_eq' _ (by simp [hfv])]
        rw [LinearEquiv.transvection.apply]
        simp

      replace he := congr($he x)
      simp only [coe_mul, transvection.coe_toLinearEquiv, LinearEquiv.mul_apply,
        LinearEquiv.transvection.coe_apply, LinearMap.transvection.apply, hx, zero_smul,
        add_zero] at he
      rw [



    intro hex
    unfold IsExceptional at hex
    obtain ⟨hex, a, her⟩ := hex

    apply that
    constructor
    · sorry
    · use a
      ext x
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq]
      have : e.fixedSubmodule ≤ e'.fixedSubmodule := by
        rw [this]
        apply inf_le_right
      simp only [mkQ_apply, reduce_apply e' x]
      rw [Submodule.linearMap_qext_iff, LinearMap.ext_iff] at her
      specialize her x
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, mkQ_apply,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq, reduce_apply] at her
      simp only [← he] at her
      simp only [coe_mul, transvection.coe_toLinearEquiv, LinearEquiv.mul_apply,
        LinearEquiv.transvection.coe_apply, LinearMap.transvection.apply] at her
      simp only [map_add, map_smul, Quotient.mk_add, Quotient.mk_smul] at her
      rw [eq_comm, ← sub_eq_iff_eq_add] at her
      rw [← mkQ_apply]
      rw [← Submodule.factor_comp_mk this, LinearMap.comp_apply,
        mkQ_apply, ← her]
      simp


      simp only [← mkQ_apply]
      rw [mkQ_apply, ← Submodule.factor_comp_mk this]
      simp only [LinearMap.comp_apply]





#exit

example (a b c : V) : a + b - c = a - c + b := by
  exact add_sub_right_comm a b c
theorem finrank_lt_transvectionDegree_add_of_isExceptional
    (e : SpecialLinearGroup K V) (he : IsExceptional e) :
    finrank K V < transvectionDegree e +
      finrank K e.fixedSubmodule := by
  sorry

theorem _root_.Module.Basis.sumExtend_apply_left {ι K V : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V] {v : ι → V}
    (hs : LinearIndependent K v) (i : ι) :
    Module.Basis.sumExtend hs (Sum.inl i) = v i := by
  simp only [Basis.sumExtend, Equiv.trans_def, Basis.coe_reindex, Basis.coe_extend, Equiv.symm_symm,
    Equiv.coe_trans, Function.comp_apply]
  rfl

theorem exists_mem_transvections_apply_eq_of_indep {u v : V}
    (h : LinearIndependent K ![u, v]) :
    ∃ t ∈ transvections K V, v = t • u := by
  have : ∃ f : Dual K V, f (v - u) = 0 ∧ f u = 1 := by
    replace h : LinearIndepOn K ![u, v] ⊤ :=
      linearIndepOn_iff.mpr fun l a a_1 ↦ h a_1
    set ι := ↑(⊤ : Set (Fin 2)) ⊕ ↑(Basis.sumExtendIndex h)
    set b : Basis ι K V := Module.Basis.sumExtend h with hb
    let i : ι := Sum.inl (⟨0, Set.mem_univ 0⟩)
    let j : ι := Sum.inl (⟨1, Set.mem_univ 1⟩)
    have hi : b i = u := Module.Basis.sumExtend_apply_left h ⟨0, Set.mem_univ 0⟩
    have hj : b j = v := Basis.sumExtend_apply_left h ⟨1, Set.mem_univ 1⟩
    use b.coord i + b.coord j
    rw [← hi, ← hj]
    have hij : i ≠ j := by simp [ne_eq, i, j, Sum.inl_injective.eq_iff]
    simp [Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne' hij]
  obtain ⟨f, hvu, hx⟩ := this
  refine ⟨SpecialLinearGroup.transvection hvu, ⟨f, v - u, hvu, rfl⟩, ?_⟩
  simp [transvection, LinearMap.transvection.apply, hx]

theorem exists_mem_transvections_apply_eq_of_indep'
    {W : Submodule K V} {u v : V}
    (hu : u ∉ W) (hv : u ∉ W)
    (h : LinearIndependent K ![u, v]) :
    ∃ t ∈ transvections K V, t ∈ fixingSubgroup _ W.carrier ∧ v = t • u := by
  sorry /-
  have : ∃ f : Dual K V, W ≤ LinearMap.ker f ∧ f (v - u) = 0 ∧ f u = 1 := by
    replace h : LinearIndepOn K ![u, v] ⊤ :=
      linearIndepOn_iff.mpr fun l a a_1 ↦ h a_1
    set ι := ↑(⊤ : Set (Fin 2)) ⊕ ↑(Basis.sumExtendIndex h)
    set b : Basis ι K V := Module.Basis.sumExtend h with hb
    let i : ι := Sum.inl (⟨0, Set.mem_univ 0⟩)
    let j : ι := Sum.inl (⟨1, Set.mem_univ 1⟩)
    have hi : b i = u := Module.Basis.sumExtend_apply_left h ⟨0, Set.mem_univ 0⟩
    have hj : b j = v := Basis.sumExtend_apply_left h ⟨1, Set.mem_univ 1⟩
    use b.coord i + b.coord j
    rw [← hi, ← hj]
    have hij : i ≠ j := by simp [ne_eq, i, j, Sum.inl_injective.eq_iff]
    simp [Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne' hij]
  obtain ⟨f, hvu, hx⟩ := this
  refine ⟨SpecialLinearGroup.transvection hvu, ⟨f, v - u, hvu, rfl⟩, ?_⟩
  simp [transvection, LinearMap.transvection.apply, hx] -/


lemma linearIndependent_of_not_mem_span {x y z : V} (hx : x ≠ 0)
    (hz : z ∉ Submodule.span K {x, y}) :
    LinearIndependent K ![x, z] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [and_comm]
  by_contra! h'
  apply hz
  by_cases ht : t = 0
  · exfalso
    apply h' ht
    simpa [ht, hx] using hst
  rw [Submodule.mem_span_insert]
  refine ⟨ -(s / t), 0, Submodule.zero_mem _, ?_⟩
  rw [add_zero, ← sub_eq_zero, neg_smul, sub_neg_eq_add,
    ← smul_eq_zero_iff_right ht, smul_add, smul_smul,
    add_comm, mul_div_cancel₀ s ht, hst]

theorem transvections_isPretransitive (h2 : 2 ≤ finrank K V) :
    MulAction.IsPretransitive (Subgroup.closure (transvections K V)) {v : V | v ≠ 0} where
  exists_smul_eq x y := by
    classical
    wlog h : LinearIndependent K ![x.val , y.val] with hyp
    · suffices ∃ z : V, z ∉ Submodule.span K {x.val, y.val} by
        obtain ⟨z, hz⟩ := this
        have hz0 : z ≠ 0 := fun h ↦ hz <| by
          rw [h]
          exact zero_mem _
        have hxz : LinearIndependent K ![x.val, z] := by
          exact linearIndependent_of_not_mem_span x.prop hz
        have hzy : LinearIndependent K ![z, y.val] := by
          rw [LinearIndependent.pair_symm_iff]
          apply linearIndependent_of_not_mem_span y.prop (y := x.val)
          convert hz using 3
          grind
        obtain ⟨g, hg⟩ := hyp h2 x ⟨z, hz0⟩ hxz
        obtain ⟨h, hh⟩ := hyp h2 ⟨z, hz0⟩ y hzy
        use h * g
        simp [mul_smul, hg, hh]
      suffices Submodule.span K {x.val, y.val} ≠ ⊤ by
        by_contra! hz
        apply this
        rw [eq_top_iff]
        exact fun z _ ↦ hz z
      intro h'
      have : Set.finrank K {x.val, y.val} < 2 := by
        apply Nat.lt_of_le_of_ne _ ?_
        · rw [← Finset.coe_pair]
          exact le_trans (finrank_span_finset_le_card _) Finset.card_le_two
        rw [eq_comm]
        simpa [linearIndependent_iff_card_eq_finrank_span, Set.pair_comm] using h
      rw [← not_le] at this
      apply this
      simp only [Set.finrank]
      rwa [h', finrank_top]
    obtain ⟨g, hg, hgxy⟩ := exists_mem_transvections_apply_eq_of_indep h
    use ⟨g, Subgroup.subset_closure hg⟩
    simp only [Subgroup.smul_def, ne_eq, Set.coe_setOf]
    rw [smul_eq_iff g x y, hgxy]

example (W : Submodule K V) :
    Set (fixingSubgroup (SpecialLinearGroup K V) W.carrier) := by
  exact (fixingSubgroup  _ _).subtype ⁻¹' (transvections K V)

open scoped Set.Notation in
theorem transvections_isPretransitive_fixingSubgroup
    (W : Submodule K V) (h2 : 2 ≤ finrank K V) :
    MulAction.IsPretransitive
      (Subgroup.closure
        ((fixingSubgroup (SpecialLinearGroup K V) W.carrier).subtype ⁻¹' (transvections K V)))
      {v : V | v ∉ W} where
  exists_smul_eq := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Set.mem_setOf_eq] at hx hy
    classical
    wlog h : LinearIndependent K ![x , y] with hyp
    · suffices ∃ z : V, z ∉ W ⊔ Submodule.span K {x, y} by
        obtain ⟨z, hz⟩ := this
        have hz0 : z ≠ 0 := fun h ↦ hz <| by
          rw [h]
          exact zero_mem _
        have hxz : LinearIndependent K ![x, z] := by
          sorry -- exact linearIndependent_of_not_mem_span hx hz
        have hzy : LinearIndependent K ![z, y] := by
          rw [LinearIndependent.pair_symm_iff]
          sorry -- apply linearIndependent_of_not_mem_span hy (y := x)
          convert hz using 3
          grind
        obtain ⟨g, hg⟩ := hyp W h2 x hx z hz0 hxz
        obtain ⟨h, hh⟩ := hyp h2 ⟨z, hz0⟩ y hzy
        use h * g
        simp [mul_smul, hg, hh]
      suffices Submodule.span K {x.val, y.val} ≠ ⊤ by
        by_contra! hz
        apply this
        rw [eq_top_iff]
        exact fun z _ ↦ hz z
      intro h'
      have : Set.finrank K {x.val, y.val} < 2 := by
        apply Nat.lt_of_le_of_ne _ ?_
        · rw [← Finset.coe_pair]
          exact le_trans (finrank_span_finset_le_card _) Finset.card_le_two
        rw [eq_comm]
        simpa [linearIndependent_iff_card_eq_finrank_span, Set.pair_comm] using h
      rw [← not_le] at this
      apply this
      simp only [Set.finrank]
      rwa [h', finrank_top]
    obtain ⟨g, hg, hgxy⟩ := exists_mem_transvections_apply_eq_of_indep h
    use ⟨g, Subgroup.subset_closure hg⟩
    simp only [Subgroup.smul_def, ne_eq, Set.coe_setOf]
    rw [smul_eq_iff g x y, hgxy]

theorem closure_transvection [Module.Finite K V] :
    Subgroup.closure (transvections K V) = ⊤ := by
  rw [eq_top_iff]
  nontriviality V
  wlog h2 : 2 ≤ Module.finrank K V
  · suffices Subsingleton (SpecialLinearGroup K V) by simp
    rw [not_le, Nat.lt_succ_iff] at h2
    apply subsingleton_of_finrank_eq_one
    apply le_antisymm h2
    rwa [Nat.add_one_le_iff, finrank_pos_iff]
  suffices ∀ (n : ℕ) (e : SpecialLinearGroup K V)
    (hn : n = finrank K (eigenspace (e : End K V) (1 : K))),
      e ∈ Subgroup.closure (transvections K V) by
    intro e _
    apply this _ e rfl
  intro n
  induction n using Nat.strong_decreasing_induction with
  | base =>
    use finrank K V
    intro m hm e he
    rw [gt_iff_lt, he, ← not_le] at hm
    exact hm.elim (Submodule.finrank_le _)
  | step n hind=>
    intro e he
    set W := eigenspace (e : End K V) (1 : K) with hW
    by_cases H : W = ⊤
    · suffices e = 1 by
        rw [this]; exact one_mem _
      ext v
      change (e : End K V) v = v
      conv_rhs => rw [← one_smul K v]
      rw [← mem_eigenspace_iff, ← hW, H]
      exact Submodule.mem_top
    · obtain ⟨v, hv⟩ := SetLike.exists_not_mem_of_ne_top W H rfl
      have hv' := hv
      rw [hW, mem_eigenspace_iff, one_smul] at hv'
      have H' : finrank K W < finrank K V - 1 := sorry
      -- e' = t f u ∘ e
      -- f = 0 sur W, f u = 0
      -- e' v = (t f u) (e v) = e v + f (e v) • u = v
      -- u = v - e v, f (e v) = f (v) = 1
      have := transvections_isPretransitive h2
      have := this.exists_smul_eq
        ⟨(e : End K V) v, fun h ↦ hv' <| by rw [h, eq_comm];simpa using h⟩
        ⟨v, fun h ↦ hv' <| by rw [h, map_zero]⟩
      obtain ⟨⟨t, ht⟩, htv⟩ := this
      set e' := t * e with he'
      rw [← inv_mul_eq_iff_eq_mul] at he'
      rw [← he']
      apply Subgroup.mul_mem _ (Subgroup.inv_mem _ ht)
      apply hind _ _ e' rfl
      set W' := W ⊔ Submodule.span K {(e : End K V) v - v} with hW'
      rw [gt_iff_lt, he]
      apply Submodule.finrank_lt_finrank_of_lt
      rw [lt_iff_le_and_ne]
      constructor


      have hv' : v ∉ W' := fun h ↦ by
        rw [hW', Submodule.mem_sup] at h
        obtain ⟨w, hw, z, hz, hwz⟩ := h
        simp [Submodule.mem_span_singleton] at hz
        obtain ⟨a, rfl⟩ := hz
        have ha : a ≠ 0 := fun h ↦ by
          apply hv
          rwa [← hwz, h, zero_smul, add_zero]
        sorry
      sorry

end generation

end SpecialLinearGroup

#exit

section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (W : Submodule R V)

theorem linearIndependent_sum (ι κ : Type*) (b : ι → W) (c : κ → V ⧸ W)
    (hb : LinearIndependent R b) (hc : LinearIndependent R c) :
    LinearIndependent R
      (Sum.elim (fun i ↦ (b i : V)) ((Function.surjInv W.mkQ_surjective) ∘ c)) := by
  rw [linearIndependent_iff]
  intro a ha
  set a' := Finsupp.sumFinsuppLEquivProdFinsupp R a with ha'
  rw [← LinearEquiv.symm_apply_eq] at ha'
  suffices a' = 0 by rw [← ha', this, map_zero]
  rw [Prod.ext_iff]
  simp only [Prod.fst_zero, Prod.snd_zero]
  rw [← ha'] at ha
  -- nonterminal simp
  simp [Finsupp.linearCombination_apply, Finsupp.sum_sumElim] at ha
  suffices a'.2 = 0 by
    simp only [this, and_true]
    rw [linearIndependent_iff] at hb
    specialize hb a'.1
    apply hb
    rw [Finsupp.linearCombination_apply]
    rwa [this, Finsupp.sum_zero_index, add_zero,
      Finsupp.sum_congr (g2 := (fun i a ↦ W.subtype (a • (b i)))) (by simp),
      ← map_finsuppSum, LinearMap.map_eq_zero_iff _ W.subtype_injective] at ha
  replace ha := LinearMap.congr_arg (f := W.mkQ) ha
  simp only [map_add] at ha
  suffices W.mkQ _ = 0 by
    rw [linearIndependent_iff] at hc
    specialize hc a'.2
    apply hc
    rw [Finsupp.linearCombination_apply]
    rwa [this, zero_add, map_finsuppSum, map_zero,
      Finsupp.sum_congr (g2 := fun k a ↦ a • (c k))] at ha
    intro k _
    simp [Function.surjInv_eq W.mkQ_surjective (c k)]
  rw [map_finsuppSum]
  convert Finsupp.sum_zero with i r
  simp only [Function.comp_apply, Sum.elim_inl, map_smul, Submodule.mkQ_apply]
  convert smul_zero _
  simp


variable [Module.Free R W]
    [Module.Free R (V ⧸ W)] [Module.Finite R V]
    (f : V →ₗ[R] V) (hfW : W ≤ W.comap f)

example (hfW : W ≤ W.comap f) : V ⧸ W →ₗ[R] V ⧸ W :=
  Submodule.mapQ W W f hfW

example (hfW : W ≤ W.comap f) : W →ₗ[R] W :=
  f.restrict hfW


end

#exit
example (e : V →ₗ[K] V) (W W' : Submodule K V) (he : W ≤ W'.comap e) :
    V ⧸ W →ₗ[K] V ⧸ W' :=
  W.liftQ (W'.mkQ ∘ₗ e) (fun v hv ↦ by simpa using he hv)

example (e : V →ₗ[K] V) (W W' : Submodule K V) (he : W.map e ≤ W') :
    V ⧸ W →ₗ[K] V ⧸ W' :=
  W.liftQ (W'.mkQ ∘ₗ e) (fun v hv ↦ by aesop)

example (e : V →ₗ[K] V) (W : Submodule K V) (he : W ≤ W.comap e) :
    V ⧸ W →ₗ[K] V ⧸ W :=
  W.mapQ W e he

example (e : V →ₗ[K] V) (W : Submodule K V) (he : W.map e ≤ W) :
    V ⧸ W →ₗ[K] V ⧸ W :=
  W.mapQ W e (Submodule.map_le_iff_le_comap.mp he)

example (e : V →ₗ[K] V) (W : Submodule K V) (he : W ≤ W.comap e) :
    W →ₗ[K] W := by
  exact e.restrict he

example (e : V ≃ₗ[K] V) (W W' : Submodule K V) (he : W = W'.comap e) :
    (V ⧸ W) ≃ₗ[K] (V ⧸ W') where
  toLinearMap := W.liftQ (W'.mkQ ∘ₗ e) (fun v hv ↦ by
    simpa [he] using hv)
  invFun := W'.liftQ (W.mkQ ∘ₗe.symm) (fun v hv ↦ by
    simpa [he] using hv)
  left_inv v' := by
    obtain ⟨v, rfl⟩ := W.mkQ_surjective v'
    simp
  right_inv v' := by
    obtain ⟨v, rfl⟩ := W'.mkQ_surjective v'
    simp

example (e : V ≃ₗ[K] V) (W W' : Submodule K V)
    (he : W = W'.comap e) :
    (V ⧸ W) ≃ₗ[K] (V ⧸ W') := by
  apply Submodule.Quotient.equiv W W' e
  erw [Submodule.map_equiv_eq_comap_symm e W]
  aesop


