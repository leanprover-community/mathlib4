/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Wanyi He, Jiedong Jiang
-/
import Mathlib.RingTheory.FilteredAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
/-!

-/
universe u

variable {ι : Type*} [OrderedCancelAddCommMonoid ι]

section GeneralGraded

variable {A : Type*} [AddCommGroup A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]

variable (F : ι → σ) (F_lt : outParam <| ι → σ)

@[nolint unusedArguments]
instance [IsFiltration F F_lt] (i : ι) : Setoid (AddSubgroupClass.subtype (F i)).range :=
  QuotientAddGroup.leftRel
  ((AddSubgroupClass.subtype (F_lt i)).range.addSubgroupOf (AddSubgroupClass.subtype (F i)).range)

/-- `GradedPiece i` of the associated graded ring is defined as `F i` quotient by `F_lt i`-/
abbrev GradedPiece (i : ι) := (AddSubgroupClass.subtype (F i)).range ⧸
    (AddSubgroupClass.subtype (F_lt i)).range.addSubgroupOf (AddSubgroupClass.subtype (F i)).range

namespace GradedPiece

/--Obtaining an element of `GradedPiece i` from an element of `F i`-/
def mk {i : ι} (x : (AddSubgroupClass.subtype (F i)).range) : GradedPiece F F_lt i := ⟦x⟧

section

omit [OrderedCancelAddCommMonoid ι]

@[simp]
lemma mk_eq {i : ι} (x : (AddSubgroupClass.subtype (F i)).range) : mk F F_lt x = ⟦x⟧ := rfl

lemma mk_zero {i : ι} : mk F F_lt 0  = (0 : GradedPiece F F_lt i) := rfl

lemma HEq_rfl {i j : ι} {r : A} (h : i = j)
    (hi : r ∈ (AddSubgroupClass.subtype (F i)).range)
    (hj : r ∈ (AddSubgroupClass.subtype (F j)).range) :
    HEq (mk F F_lt ⟨r, hi⟩) (mk F F_lt ⟨r, hj⟩) :=
  h ▸ HEq.rfl

lemma HEq_eq_mk_eq {i j : ι} {x : GradedPiece F F_lt i} {y : GradedPiece F F_lt j} {r s : A}
    (h : i = j) (e : r = s) (hi : r ∈ (AddSubgroupClass.subtype (F i)).range)
    (hj : s ∈ (AddSubgroupClass.subtype (F j)).range)
    (hx : x = mk F F_lt ⟨r, hi⟩) (hy : y = mk F F_lt ⟨s, hj⟩) : HEq x y := by
  rw [hx, hy]
  subst e
  exact HEq_rfl F F_lt h hi hj

-- Will be easier to use if HMul intances for F i is added and some other refactor is done.
lemma HEq_eq_mk_coe_eq {i j : ι} {x : GradedPiece F F_lt i} {y : GradedPiece F F_lt j}
    (r : (AddSubgroupClass.subtype (F i)).range) (s : (AddSubgroupClass.subtype (F j)).range)
    (h : i = j) (e : (r : A) = (s : A)) (hx : x = mk F F_lt r) (hy : y = mk F F_lt s) : HEq x y :=
  HEq_eq_mk_eq F F_lt h e r.2 (e ▸ s.2) hx hy

end

variable [IsFiltration F F_lt]

omit [OrderedCancelAddCommMonoid ι] in
lemma mk_congr {i : ι} (x y : (AddSubgroupClass.subtype (F i)).range) (h : x = y) :
    mk F F_lt x = mk F F_lt y := congrArg (mk F F_lt) h

lemma sound {i : ι} (x y : (AddSubgroupClass.subtype (F i)).range) :
    x ≈ y → mk F F_lt x = mk F F_lt y := Quotient.sound

@[simp]
lemma exact {i : ι} (x y : (AddSubgroupClass.subtype (F i)).range) :
    mk F F_lt x = mk F F_lt y → x ≈ y := Quotient.exact

end GradedPiece

end GeneralGraded

section

instance {R : Type u} [Ring R] {σ : Type*} [SetLike σ R] [AddSubgroupClass σ R]
    (F : ι → σ) (F_lt : outParam <| ι → σ) [IsRingFiltration F F_lt] :
    One (GradedPiece F F_lt 0) where
  one := ⟦⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩⟧

end

section GradedRing

variable {R : Type u} [Ring R] {σ : Type*} [SetLike σ R] [AddSubgroupClass σ R]

variable (F : ι → σ) (F_lt : outParam <| ι → σ)

section HasGMul

/--The class of filtrations that can obtain a well defined `GradedMul`
from the multiplication `F i → F j → F (i + j)` -/
class hasGMul extends IsRingFiltration F F_lt : Prop where
  F_lt_mul_mem {i j : ι} {x y} : x ∈ F_lt i → y ∈ F j → x * y ∈ F_lt (i + j)
  mul_F_lt_mem {i j : ι} {x y} : x ∈ F i → y ∈ F_lt j → x * y ∈ F_lt (i + j)

omit [AddSubgroupClass σ R] in
lemma hasGMul_int (F : ℤ → σ) (mono : ∀ {a b : ℤ}, a ≤ b → F a ≤ F b) (one_mem : 1 ∈ F 0)
    (mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)) :
    hasGMul F (fun n ↦ F (n - 1)) := {
    IsRingFiltration_int F mono one_mem mul_mem with
    F_lt_mul_mem := fun h1 h2 ↦ by
      have := mul_mem h1 h2
      rwa [sub_add_eq_add_sub] at this
    mul_F_lt_mem := fun h1 h2 ↦ by
      have := mul_mem h1 h2
      rwa [add_sub_assoc'] at this }

lemma hasGMul_AddSubgroup (F : ι → AddSubgroup R) (F_lt : outParam <| ι → AddSubgroup R)
    [IsRingFiltration F F_lt] : hasGMul F F_lt where
  F_lt_mul_mem := by
    intro i j x y hx hy
    let S : AddSubgroup R := {
      carrier := {z | z * y ∈ F_lt (i + j)}
      add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, add_mul, add_mem ha.out hb.out]
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_mul, zero_mem]
      neg_mem' := by simp only [Set.mem_setOf_eq, neg_mul, neg_mem_iff, imp_self, implies_true]}
    exact IsFiltration.is_sup S i (fun k hk z hz ↦
      IsFiltration.is_le (add_lt_add_right hk j) (IsRingFiltration.mul_mem hz hy)) hx
  mul_F_lt_mem := by
    intro i j x y hx hy
    let S : AddSubgroup R := {
      carrier := {z | x * z ∈ F_lt (i + j)}
      add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, mul_add, add_mem ha.out hb.out]
      zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero, zero_mem]
      neg_mem' := by simp only [Set.mem_setOf_eq, mul_neg, neg_mem_iff, imp_self, implies_true]}
    exact IsFiltration.is_sup S j (fun k hk z hz ↦
      IsFiltration.is_le (add_lt_add_left hk i) (IsRingFiltration.mul_mem hx hz)) hy

/--The multiplication `F i → F j → F (i + j)` defined as the multiplication of its value. -/
def IsRingFiltration.hMul [IsRingFiltration F F_lt] (i j : ι)
    (x : (AddSubgroupClass.subtype (F i)).range) (y : (AddSubgroupClass.subtype (F j)).range) :
    (AddSubgroupClass.subtype (F (i + j))).range where
  val := x * y
  property := by
    rcases x.2 with ⟨x', hx'⟩
    rcases y.2 with ⟨y', hy'⟩
    simp [← hx', ← hy', IsRingFiltration.mul_mem x'.2 y'.2]

instance [IsRingFiltration F F_lt] {i j : ι} :
    HMul (AddSubgroupClass.subtype (F i)).range (AddSubgroupClass.subtype (F j)).range
    (AddSubgroupClass.subtype (F (i + j))).range where
  hMul := IsRingFiltration.hMul F F_lt i j

variable [hasGMul F F_lt]

lemma hasGMul.mul_equiv_mul {i j : ι} ⦃x₁ x₂ : (AddSubgroupClass.subtype (F i)).range⦄
    (hx : x₁ ≈ x₂) ⦃y₁ y₂ : (AddSubgroupClass.subtype (F j)).range⦄ (hy : y₁ ≈ y₂) :
    x₁ * y₁ ≈ x₂ * y₂ := by
  simp only [HasEquiv.Equiv, QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_add, NegMemClass.coe_neg, AddMonoidHom.mem_range, AddSubgroupClass.coeSubtype,
    Subtype.exists, exists_prop, exists_eq_right] at hx hy ⊢
  have eq : - ((x₁ * y₁) : (AddSubgroupClass.subtype (F (i + j))).range).1 +
    ((x₂ * y₂) : (AddSubgroupClass.subtype (F (i + j))).range).1 =
    (- x₁ + x₂) * y₁ + x₂ * (- y₁ + y₂) := by noncomm_ring
  rw [eq]
  rcases y₁.2 with ⟨y₁', hy₁'⟩
  rcases x₂.2 with ⟨x₂', hx₂'⟩
  exact add_mem (hasGMul.F_lt_mul_mem (F := F) hx (by simp [← hy₁']))
    (hasGMul.mul_F_lt_mem (F := F) (by simp [← hx₂']) hy)

/--The multiplication `GradedPiece F F_lt i → GradedPiece F F_lt j → GradedPiece F F_lt (i + j)`
lifted from the multiplication `F i → F j → F (i + j)`-/
def hasGMul.gradedMul {i j : ι} (x : GradedPiece F F_lt i) (y : GradedPiece F F_lt j) :
    GradedPiece F F_lt (i + j) :=
  Quotient.map₂ (· * ·) (hasGMul.mul_equiv_mul F F_lt) x y

instance hMul {i j : ι} :
    HMul (GradedPiece F F_lt i) (GradedPiece F F_lt j) (GradedPiece F F_lt (i + j)) where
  hMul := hasGMul.gradedMul F F_lt

namespace GradedPiece

section HEq

lemma mk_mul {i j : ι}
    (x : (AddSubgroupClass.subtype (F i)).range) (y : (AddSubgroupClass.subtype (F j)).range) :
    mk F F_lt x * mk F F_lt y = mk F F_lt (x * y) := rfl

lemma gradedMul_def {i j : ι}
    (x : (AddSubgroupClass.subtype (F i)).range) (y : (AddSubgroupClass.subtype (F j)).range) :
    mk F F_lt (IsRingFiltration.hMul F F_lt i j x y) =
    hasGMul.gradedMul F F_lt (mk F F_lt x) (mk F F_lt y) := rfl

end HEq

end GradedPiece

namespace GradedMul

open GradedPiece

instance : GradedMonoid.GMul (GradedPiece F F_lt) where
  mul := hasGMul.gradedMul F F_lt

instance : GradedMonoid.GOne (GradedPiece F F_lt) where
  one := (1 : GradedPiece F F_lt 0)

lemma GradedPiece.HEq_one_mul {i : ι} (x : GradedPiece F F_lt i) :
    HEq ((1 : GradedPiece F F_lt 0) * x) x := by
  let rx := Quotient.out x
  let r1 : (AddSubgroupClass.subtype (F 0)).range := ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩
  apply HEq_eq_mk_eq F F_lt (zero_add i) (one_mul (rx : R))
  · convert (gradedMul_def F F_lt r1 rx).symm
    exact (Quotient.out_eq' x).symm
  · exact (Quotient.out_eq' x).symm
  · rcases rx.2 with ⟨rx', hrx'⟩
    simp [← hrx']

lemma GradedPiece.HEq_mul_one {i : ι} (x : GradedPiece F F_lt i) :
    HEq (x * (1 : GradedPiece F F_lt 0)) x := by
  let rx := Quotient.out x
  let r1 : (AddSubgroupClass.subtype (F 0)).range := ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩
  apply HEq_eq_mk_eq F F_lt (add_zero i) (mul_one (rx : R))
  · convert (gradedMul_def F F_lt rx r1).symm
    exact (Quotient.out_eq' x).symm
  · exact (Quotient.out_eq' x).symm
  · rcases rx.2 with ⟨rx', hrx'⟩
    simp [← hrx']

lemma GradedPiece.HEq_mul_assoc {i j k : ι}
    (a : GradedPiece F F_lt i) (b : GradedPiece F F_lt j) (c : GradedPiece F F_lt k) :
    HEq (a * b * c) (a * (b * c)) := by
  let ra := Quotient.out a
  let rb := Quotient.out b
  let rc := Quotient.out c
  apply HEq_eq_mk_eq F F_lt (add_assoc i j k) (mul_assoc (ra : R) rb rc)
  · show a * b * c = ⟦ra * rb * rc⟧
    convert (gradedMul_def F F_lt (ra * rb) rc).symm
    · convert (gradedMul_def F F_lt ra rb).symm
      · exact (Quotient.out_eq' a).symm
      · exact (Quotient.out_eq' b).symm
    · exact (Quotient.out_eq' c).symm
  · show a * (b * c) = ⟦ra * (rb * rc)⟧
    convert (gradedMul_def F F_lt ra (rb * rc)).symm
    · exact (Quotient.out_eq' a).symm
    · convert (gradedMul_def F F_lt rb rc).symm
      · exact (Quotient.out_eq' b).symm
      · exact (Quotient.out_eq' c).symm

omit [hasGMul F F_lt] in
lemma Filtration.pow_mem [IsRingFiltration F F_lt] (n : ℕ) {i : ι}
    (x : (AddSubgroupClass.subtype (F i)).range) : (x : R) ^ n ∈
    (AddSubgroupClass.subtype (F (n • i))).range := by
  induction' n with d hd
  · use ⟨1, by simpa only [zero_smul] using IsRingFiltration.one_mem⟩
    simp
  · rcases x.2 with ⟨x', hx'⟩
    rcases hd with ⟨xd', hxd'⟩
    rw [pow_succ, ← hxd', ← hx']
    simpa [succ_nsmul i d] using (IsRingFiltration.mul_mem xd'.2 x'.2)

lemma Filtration.pow_lift (n : ℕ) {i : ι}
    (x₁ x₂ : (AddSubgroupClass.subtype (F i)).range) (h : x₁ ≈ x₂) :
    (⟨x₁ ^ n, Filtration.pow_mem F F_lt n x₁⟩ : (AddSubgroupClass.subtype (F (n • i))).range) ≈
    (⟨x₂ ^ n, Filtration.pow_mem F F_lt n x₂⟩ : (AddSubgroupClass.subtype (F (n • i))).range) := by
  induction' n with d hd
  · simp only [pow_zero, mk_eq, exact]
  · simp only [pow_succ]
    simp only [HasEquiv.Equiv, QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf,
      AddSubgroup.coe_add, NegMemClass.coe_neg, AddMonoidHom.mem_range, AddSubgroupClass.coeSubtype,
      Subtype.exists, exists_prop, exists_eq_right] at h hd ⊢
    have mem1 : x₁.1 ^ d * x₂.1 - x₁.1 ^ d * x₁.1 ∈ F_lt ((d + 1) • i) := by
      rw [← mul_sub, sub_eq_neg_add]
      have := Filtration.pow_mem F F_lt d x₁
      simp only [AddMonoidHom.mem_range, AddSubgroupClass.coeSubtype, Subtype.exists, exists_prop,
        exists_eq_right] at this
      simpa [succ_nsmul i d] using hasGMul.mul_F_lt_mem this h
    have mem2 : x₂.1 ^ d * x₂.1 - x₁.1 ^ d * x₂.1 ∈ F_lt ((d + 1) • i) := by
      rw [← sub_mul, sub_eq_neg_add]
      rcases x₂.2 with ⟨x₂', hx₂'⟩
      have : x₂.1 ∈ F i := by simp [← hx₂']
      simpa [succ_nsmul i d] using hasGMul.F_lt_mul_mem hd this
    have : -(x₁.1 ^ d * x₁.1) + x₂.1 ^ d * x₂.1 =
      x₁.1 ^ d * x₂.1 - x₁.1 ^ d * x₁.1 + (x₂.1 ^ d * x₂.1 - x₁.1 ^ d * x₂.1) := by abel
    rw [this]
    exact add_mem mem1 mem2

/--The graded nat power between graded pieces. -/
def GradedPiece.gnpow (n : ℕ) {i : ι} : GradedPiece F F_lt i → GradedPiece F F_lt (n • i) :=
    Quotient.map (fun x ↦ ⟨x.1 ^ n, Filtration.pow_mem F F_lt n x⟩)
  (fun x₁ x₂ h ↦ Filtration.pow_lift F F_lt n x₁ x₂ h)

lemma gnpow_def (n : ℕ) {i : ι} (x : (AddSubgroupClass.subtype (F i)).range) :
    mk F F_lt ⟨x.1 ^ n, Filtration.pow_mem F F_lt n x⟩ = GradedPiece.gnpow F F_lt n (mk F F_lt x) :=
  rfl

lemma GradedPiece.gnpow_zero' {i : ι} (x : GradedPiece F F_lt i) :
    HEq (gnpow F F_lt 0 x) (1 : GradedPiece F F_lt 0) := by
  let rx := Quotient.out x
  let r1 : (AddSubgroupClass.subtype (F 0)).range := ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩
  apply HEq_eq_mk_eq F F_lt (zero_nsmul i) (pow_zero rx.1) (Filtration.pow_mem F F_lt 0 rx)
    r1.2 _ rfl
  simp only [gnpow_def F F_lt 0 rx, rx, mk_eq]
  nth_rw 1 [← Quotient.out_eq x]

lemma GradedPiece.gnpow_succ' (n : ℕ) {i : ι} (x : GradedPiece F F_lt i) :
    HEq (gnpow F F_lt n.succ x) (gnpow F F_lt n x * x) := by
  let rx := Quotient.out x
  have mk_rx : mk F F_lt rx = x := by
    nth_rw 1 [← Quotient.out_eq x]
    rfl
  have : rx.1 ^ n * rx.1 ∈ (AddSubgroupClass.subtype (F (n • i + i))).range := by
    rcases rx.2 with ⟨rx', hrx'⟩
    rcases (Filtration.pow_mem F F_lt n rx) with ⟨rxn', hrxn'⟩
    use ⟨rx.1 ^ n * rx.1, IsRingFiltration.mul_mem (by simp [← hrxn']) (by simp [← hrx'])⟩
    rfl
  apply HEq_eq_mk_eq F F_lt (succ_nsmul i n) (pow_succ rx.1 n)
    (Filtration.pow_mem F F_lt (n + 1) rx) this
  · rw [gnpow_def, mk_rx]
  · rw [← mk_rx, ← gnpow_def]
    rfl

instance : GradedMonoid.GMonoid (GradedPiece F F_lt) where
  one_mul := fun ⟨i, a⟩ => Sigma.ext (by simp) (GradedPiece.HEq_one_mul F F_lt a)
  mul_one := fun ⟨i, a⟩ => Sigma.ext (by simp) (GradedPiece.HEq_mul_one F F_lt a)
  mul_assoc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    Sigma.ext (add_assoc i j k) (GradedPiece.HEq_mul_assoc F F_lt a b c)
  gnpow := GradedPiece.gnpow F F_lt
  gnpow_zero' := fun ⟨i, a⟩ ↦ Sigma.ext (zero_nsmul i) (GradedPiece.gnpow_zero' F F_lt a)
  gnpow_succ' :=  fun n ⟨i, a⟩ ↦ Sigma.ext (succ_nsmul i n) (GradedPiece.gnpow_succ' F F_lt n a)

lemma GradedPiece.mul_zero {i j : ι} (a : GradedPiece F F_lt i) :
    a * (0 : GradedPiece F F_lt j) = 0 := by
  rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
  induction a using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp only [ZeroMemClass.coe_zero, mul_zero, QuotientAddGroup.leftRel_apply, add_zero, neg_mem_iff]
  use 0
  simpa only [AddSubgroupClass.coeSubtype, ZeroMemClass.coe_zero, AddSubgroup.coeSubtype]
    using (MulZeroClass.mul_zero _).symm

lemma GradedPiece.zero_mul {i j : ι} (a : GradedPiece F F_lt i) :
    (0 : GradedPiece F F_lt j) * a = 0 := by
  rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
  induction a using Quotient.ind'
  change Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp only [ZeroMemClass.coe_zero, zero_mul, QuotientAddGroup.leftRel_apply, add_zero, neg_mem_iff]
  use 0
  simpa only [AddSubgroupClass.coeSubtype, ZeroMemClass.coe_zero, AddSubgroup.coeSubtype]
    using (MulZeroClass.zero_mul _).symm

lemma GradedPiece.mul_add {i j : ι} (a : GradedPiece F F_lt i) (b c : GradedPiece F F_lt j) :
    a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind'
  induction b using Quotient.ind'
  induction c using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
  rename_i a1 a2 a3
  have : -(a1 * (a2 + a3)).1 + ((a1 * a2).1 + (a1 * a3).1) = 0 := by
    have : -(a1.1 * (a2.1 + a3.1)) + (a1.1 * a2.1 + a1.1 * a3.1) = 0 := by noncomm_ring
    rw [← this]
    rfl
  rw [this]
  exact zero_mem (F_lt (i + j))

lemma GradedPiece.add_mul {i j : ι} (a b : GradedPiece F F_lt i) (c : GradedPiece F F_lt j) :
    (a + b) * c = a * c + b * c := by
  induction a using Quotient.ind'
  induction b using Quotient.ind'
  induction c using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
  rename_i a1 a2 a3
  have : -((a1 + a2) * a3).1 + ((a1 * a3).1 + (a2 * a3).1) = 0 := by
    have : -((a1.1 + a2.1) * a3.1) + (a1.1 * a3.1 + a2.1 * a3.1) = 0 := by noncomm_ring
    rw [← this]
    rfl
  rw [this]
  exact zero_mem (F_lt (i + j))

/--The nat scalar multiple in `GradedPiece F F_lt 0`-/
def GradedPiece.natCast (n : ℕ) : GradedPiece F F_lt 0 :=
  mk F F_lt (n • ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩)

lemma GradedPiece.natCast_zero : (natCast F F_lt 0 : GradedPiece F F_lt 0) = 0 := by
  show mk F F_lt (0 • ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩) = 0
  simp only [zero_smul, mk_eq]
  rfl

lemma GradedPiece.natCast_succ (n : ℕ) : (natCast F F_lt n.succ : GradedPiece F F_lt 0) =
    (natCast F F_lt n : GradedPiece F F_lt 0) + 1 := by
  show mk F F_lt (n.succ • ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩) =
    mk F F_lt (n • ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩) +
    mk F F_lt (⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩)
  simp only [Nat.succ_eq_add_one, AddSubmonoidClass.mk_nsmul, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, mul_one]
  rfl

instance : DirectSum.GSemiring (GradedPiece F F_lt) :=
{ GradedMul.instGMonoidGradedPiece F F_lt with
  mul_zero := GradedPiece.mul_zero F F_lt
  zero_mul := GradedPiece.zero_mul F F_lt
  mul_add := GradedPiece.mul_add F F_lt
  add_mul := GradedPiece.add_mul F F_lt
  natCast := GradedPiece.natCast F F_lt
  natCast_zero := GradedPiece.natCast_zero F F_lt
  natCast_succ := GradedPiece.natCast_succ F F_lt }

/--The int scalar multiple in `GradedPiece F F_lt 0`-/
def GradedPiece.intCast (n : ℤ) : GradedPiece F F_lt 0 :=
  mk F F_lt (n • ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩)

lemma GradedPiece.intCast_ofNat (n : ℕ) : intCast F F_lt n = natCast F F_lt n := by
  show mk F F_lt ((n : ℤ) • ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩) =
    mk F F_lt (n • ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩)
  simp

lemma GradedPiece.intCast_negSucc_ofNat (n : ℕ) :
    intCast F F_lt (Int.negSucc n) = - (natCast F F_lt (n + 1)) := by
  show mk F F_lt ((Int.negSucc n) • ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩) =
    - mk F F_lt ((n + 1) • ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩)
  simp only [negSucc_zsmul, AddSubmonoidClass.mk_nsmul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    mul_one, mk_eq, QuotientAddGroup.mk_neg]

instance : DirectSum.GRing (GradedPiece F F_lt) where
  intCast := GradedPiece.intCast F F_lt
  intCast_ofNat := GradedPiece.intCast_ofNat F F_lt
  intCast_negSucc_ofNat := GradedPiece.intCast_negSucc_ofNat F F_lt

open DirectSum in
instance [DecidableEq ι] : Ring (⨁ i, GradedPiece F F_lt i) := DirectSum.ring (GradedPiece F F_lt)

end GradedMul

end HasGMul

end GradedRing
