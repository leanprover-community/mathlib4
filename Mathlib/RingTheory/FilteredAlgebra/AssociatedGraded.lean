/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Wanyi He, Jiedong Jiang
-/
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.RingTheory.FilteredAlgebra.Basic
/-!
# The Associated Graded Ring to a Filtered Ring

In this file we define `GradedPiece` for `IsFiltration F F_lt` on abelian groups with every `F j`
`AddSubgroup`s, and their direct sum `AssociatedGraded`.
We also proved that when the filtration appropriate condition `hasGMul`, the `AssociatedGraded`
over a ring also have a ring structure. i.e. the associated graded ring to a filtered ring.

# Main definitions and results

* `GradedPiece` : `GradedPiece i` of the associated graded abelian group to `IsFiltration F F_lt`
with every `F i` of some `AddSubgroupClass` is defined as `F i` quotient by `F_lt i`

* `AssociatedGraded` : The direct sum of `GradedPiece`s

* `hasGMul` : The class of filtrations that can obtain
  a well defined graded multiplication over `GradedPiece`

* `instGRingGradedPieceOfHasGMul` : `GradedPiece` satisfies `DirectSum.GRing`

* `instRingAssociatedGradedOfHasGMulOfDecidableEq` :
  `AssociatedGraded` have a ring structure when given `hasGMul` and decidable on the index set.

-/

section GeneralGraded

variable {ι : Type*}

variable {A : Type*} [AddCommGroup A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]

variable (F : ι → σ) (F_lt : outParam <| ι → σ)

@[nolint unusedArguments]
instance [Preorder ι] [IsFiltration F F_lt] (i : ι) : Setoid (AddSubgroup.ofClass (F i)) :=
  QuotientAddGroup.leftRel
    ((AddSubgroup.ofClass (F_lt i)).addSubgroupOf (AddSubgroup.ofClass (F i)))

/-- `GradedPiece i` of the associated graded abelian group to `IsFiltration F F_lt`
with every `F j` `AddSubgroup`s is defined as `F i` quotient by `F_lt i`. -/
abbrev GradedPiece (i : ι) :=
  (AddSubgroup.ofClass (F i)) ⧸
    (AddSubgroup.ofClass (F_lt i)).addSubgroupOf (AddSubgroup.ofClass (F i))

/-- Direct sum of `GradedPiece`s.-/
abbrev AssociatedGraded := DirectSum ι (GradedPiece F F_lt)

namespace AssociatedGraded

/-- `AssociatedGraded.mk F F_lt s x` is the element of `AssociatedGraded F F_lt` that is zero
outside `s` and has coefficient `x i` for `i` in `s`. -/
abbrev mk [DecidableEq ι] (s : Finset ι) :
    (∀ i : (s : Set ι), GradedPiece F F_lt i.val) →+ AssociatedGraded F F_lt :=
  DirectSum.mk (GradedPiece F F_lt) s

variable {F F_lt}

/-- The natrual inclusion map from `GradedPiece F F_lt i` to `AssociatedGraded F F_lt`-/
abbrev of [DecidableEq ι] {i : ι} : GradedPiece F F_lt i →+ AssociatedGraded F F_lt :=
  DirectSum.of (GradedPiece F F_lt) i

@[ext]
theorem ext {x y : AssociatedGraded F F_lt} (w : ∀ i, x i = y i) : x = y := by
  exact DirectSum.ext (GradedPiece F F_lt) w

variable [DecidableEq ι]

theorem of_eq_of_ne (i j : ι) (x : GradedPiece F F_lt i) (h : i ≠ j) : (of x) j = 0 :=
  DFinsupp.single_eq_of_ne h

lemma of_apply {i : ι} (j : ι) (x : GradedPiece F F_lt i) :
    of x j = if h : i = j then Eq.recOn h x else 0 :=
  DFinsupp.single_apply

theorem mk_apply_of_mem {s : Finset ι} {f : ∀ i : (s : Set ι), GradedPiece F F_lt i.val}
    {n : ι} (hn : n ∈ s) : mk F F_lt s f n = f ⟨n, hn⟩ := by
  dsimp only [Finset.coe_sort_coe, mk, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    DFinsupp.mk_apply, DirectSum.mk]
  rw [dif_pos hn]

theorem mk_apply_of_not_mem {s : Finset ι} {f : ∀ i : (s : Set ι), GradedPiece F F_lt i.val}
    {n : ι} (hn : n ∉ s) : mk F F_lt s f n = 0 := by
  dsimp only [Finset.coe_sort_coe, mk, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    DFinsupp.mk_apply, DirectSum.mk]
  rw [dif_neg hn]

section support

noncomputable instance : ∀ (i : ι) (x : GradedPiece F F_lt i), Decidable (x ≠ 0) :=
  fun _ x ↦ Classical.propDecidable (x ≠ 0)

@[simp]
theorem support_of (i : ι) (x : GradedPiece F F_lt i) (h : x ≠ 0) : (of x).support = {i} :=
  DFinsupp.support_single_ne_zero h

theorem support_of_subset {i : ι} {b : GradedPiece F F_lt i} : (of b).support ⊆ {i} :=
  DFinsupp.support_single_subset

theorem sum_support_of (x : AssociatedGraded F F_lt) : (∑ i ∈ x.support, of (x i)) = x :=
  DFinsupp.sum_single

end support

theorem sum_univ_of [Fintype ι] (x : AssociatedGraded F F_lt) :
    ∑ i ∈ Finset.univ, of (x i) = x := by
  apply DFinsupp.ext (fun i ↦ ?_)
  rw [DFinsupp.finset_sum_apply]
  simp [of_apply]

theorem mk_injective (s : Finset ι) : Function.Injective (mk F F_lt s) :=
  DFinsupp.mk_injective s

theorem of_injective (i : ι) : Function.Injective (of (i := i) (F := F) (F_lt := F_lt)) :=
  DFinsupp.single_injective

end AssociatedGraded

open AddSubgroup

namespace GradedPiece

/-- Obtaining an element of `GradedPiece i` from an element of `F i`.-/
def mk {i : ι} : (ofClass (F i)) →+ GradedPiece F F_lt i :=
  QuotientAddGroup.mk' ((ofClass (F_lt i)).addSubgroupOf (ofClass (F i)))

section

lemma mk_eq {i : ι} (x : F i) : mk F F_lt x = ⟦x⟧ := rfl

lemma HEq_rfl {i j : ι} {r : A} (h : i = j) (hi : r ∈ ofClass (F i)) (hj : r ∈ ofClass (F j)) :
    HEq (mk F F_lt ⟨r, hi⟩) (mk F F_lt ⟨r, hj⟩) :=
  h ▸ HEq.rfl

lemma HEq_eq_mk_eq {i j : ι} {x : GradedPiece F F_lt i} {y : GradedPiece F F_lt j} {r s : A}
    (h : i = j) (e : r = s) (hi : r ∈ ofClass (F i)) (hj : s ∈ ofClass (F j))
    (hx : x = mk F F_lt ⟨r, hi⟩) (hy : y = mk F F_lt ⟨s, hj⟩) : HEq x y := by
  rw [hx, hy]
  subst e
  exact HEq_rfl F F_lt h hi hj

-- Will be easier to use if HMul intances for F i is added and some other refactor is done.
lemma HEq_eq_mk_coe_eq {i j : ι} {x : GradedPiece F F_lt i} {y : GradedPiece F F_lt j}
    (r : ofClass (F i)) (s : ofClass (F j)) (h : i = j) (e : (r : A) = (s : A))
    (hx : x = mk F F_lt r) (hy : y = mk F F_lt s) : HEq x y :=
  HEq_eq_mk_eq F F_lt h e r.2 (e ▸ s.2) hx hy

end

lemma mk_congr {i : ι} (x y : ofClass (F i)) (h : x = y) : mk F F_lt x = mk F F_lt y :=
  congrArg (mk F F_lt) h

lemma sound [Preorder ι] [IsFiltration F F_lt] {i : ι} (x y : ofClass (F i)) :
    x ≈ y → mk F F_lt x = mk F F_lt y :=
  Quotient.sound

@[simp]
lemma exact [Preorder ι] [IsFiltration F F_lt] {i : ι} (x y : ofClass (F i)) :
    mk F F_lt x = mk F F_lt y → x ≈ y :=
  Quotient.exact

end GradedPiece

end GeneralGraded

section GradedRing

variable {ι : Type*}

variable {R : Type*} [Ring R] {σ : Type*} [SetLike σ R]

instance [OrderedAddCommMonoid ι] [AddSubgroupClass σ R] (F : ι → σ) (F_lt : outParam <| ι → σ)
    [IsRingFiltration F F_lt] : One (GradedPiece F F_lt 0) where
  one := ⟦⟨1, IsRingFiltration.toGradedMonoid.one_mem⟩⟧

variable (F : ι → σ) (F_lt : outParam <| ι → σ)

section HasGMul

/-- The class of ring filtrations that can obtain a well defined `GradedMul`
from the multiplication `F i → F j → F (i + j)`. -/
class hasGMul [OrderedAddCommMonoid ι] extends IsRingFiltration F F_lt : Prop where
  F_lt_mul_mem {i j : ι} {x y} : x ∈ F_lt i → y ∈ F j → x * y ∈ F_lt (i + j)
  mul_F_lt_mem {i j : ι} {x y} : x ∈ F i → y ∈ F_lt j → x * y ∈ F_lt (i + j)

lemma hasGMul.mk_int (F : ℤ → σ) (mono : Monotone F) [SetLike.GradedMonoid F] :
    hasGMul F (fun n ↦ F (n - 1)) where
    __ := IsRingFiltration.mk_int F mono
    F_lt_mul_mem := fun h1 h2 ↦ by
      simpa [sub_add_eq_add_sub] using SetLike.GradedMul.mul_mem h1 h2
    mul_F_lt_mem := fun h1 h2 ↦ by
      simpa [add_sub_assoc'] using SetLike.GradedMul.mul_mem h1 h2

lemma hasGMul_AddSubgroup (F : ι → AddSubgroup R) (F_lt : outParam <| ι → AddSubgroup R)
    [OrderedCancelAddCommMonoid ι] [IsRingFiltration F F_lt] : hasGMul F F_lt where
  F_lt_mul_mem {i j x y} hx hy := by
    let S : AddSubgroup R := {
      carrier := {z | z * y ∈ F_lt (i + j)}
      add_mem' ha hb :=  by simp [add_mul, add_mem ha.out hb.out]
      zero_mem' := by simp [zero_mem]
      neg_mem' := by simp }
    exact IsFiltration.is_sup S i (fun k hk z hz ↦
      IsFiltration.is_le (add_lt_add_right hk j) (IsRingFiltration.toGradedMonoid.mul_mem hz hy)) hx
  mul_F_lt_mem {i j x y} hx hy := by
    let S : AddSubgroup R := {
      carrier := {z | x * z ∈ F_lt (i + j)}
      add_mem' ha hb := by simp [mul_add, add_mem ha.out hb.out]
      zero_mem' := by simp [zero_mem]
      neg_mem' := by simp }
    exact IsFiltration.is_sup S j (fun k hk z hz ↦
      IsFiltration.is_le (add_lt_add_left hk i) (IsRingFiltration.toGradedMonoid.mul_mem hx hz)) hy

variable [OrderedAddCommMonoid ι] [AddSubgroupClass σ R]

open AddSubgroup

/-- The multiplication `F i → F j → F (i + j)` defined as the multiplication of its value. -/
def IsRingFiltration.hMul [isfil : IsRingFiltration F F_lt] (i j : ι)
    (x : AddSubgroup.ofClass (F i)) (y : AddSubgroup.ofClass (F j)) : ofClass (F (i + j)) where
  val := x * y
  property := isfil.toGradedMonoid.mul_mem x.2 y.2

instance [IsRingFiltration F F_lt] {i j : ι} :
    HMul (ofClass (F i)) (ofClass (F j)) (ofClass (F (i + j))) where
  hMul := IsRingFiltration.hMul F F_lt i j

lemma hasGMul.mul_equiv_mul [hasGMul F F_lt] {i j : ι} ⦃x₁ x₂ : ofClass (F i)⦄ (hx : x₁ ≈ x₂)
    ⦃y₁ y₂ : ofClass (F j)⦄ (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ := by
  simp only [HasEquiv.Equiv, QuotientAddGroup.leftRel_apply] at hx hy ⊢
  have eq : - (x₁ * y₁ : R) + (x₂ * y₂ : R) = (- x₁ + x₂ : R) * y₁ + x₂ * (- y₁ + y₂ : R) := by
    noncomm_ring
  have eq : - (x₁ * y₁) + (x₂ * y₂) = (- x₁ + x₂) * y₁ + x₂ * (- y₁ + y₂) :=
    SetLike.coe_eq_coe.mp eq
  rw [eq]
  exact add_mem (hasGMul.F_lt_mul_mem hx y₁.2) (hasGMul.mul_F_lt_mem x₂.2 hy)

/-- The multiplication `GradedPiece F F_lt i → GradedPiece F F_lt j → GradedPiece F F_lt (i + j)`
lifted from the multiplication `F i → F j → F (i + j)`. -/
def hasGMul.gradedMul [hasGMul F F_lt] {i j : ι} (x : GradedPiece F F_lt i)
    (y : GradedPiece F F_lt j) : GradedPiece F F_lt (i + j) :=
  Quotient.map₂ (· * ·) (hasGMul.mul_equiv_mul F F_lt) x y

instance hMul [hasGMul F F_lt] {i j : ι} :
    HMul (GradedPiece F F_lt i) (GradedPiece F F_lt j) (GradedPiece F F_lt (i + j)) where
  hMul := hasGMul.gradedMul F F_lt

namespace GradedPiece

section HEq

lemma mk_mul [hasGMul F F_lt] {i j : ι} (x : ofClass (F i)) (y : ofClass (F j)) :
    mk F F_lt x * mk F F_lt y = mk F F_lt (x * y) := rfl

lemma gradedMul_def [hasGMul F F_lt] {i j : ι} (x : ofClass (F i)) (y : ofClass (F j)) :
    mk F F_lt (IsRingFiltration.hMul F F_lt i j x y) =
    hasGMul.gradedMul F F_lt (mk F F_lt x) (mk F F_lt y) := rfl

end HEq

end GradedPiece

namespace GradedMul

open GradedPiece

instance [hasGMul F F_lt] : GradedMonoid.GMul (GradedPiece F F_lt) where
  mul := hasGMul.gradedMul F F_lt

instance [IsRingFiltration F F_lt] : GradedMonoid.GOne (GradedPiece F F_lt) where
  one := (1 : GradedPiece F F_lt 0)

lemma GradedPiece.HEq_one_mul [hasGMul F F_lt] {i : ι} (x : GradedPiece F F_lt i) :
    HEq ((1 : GradedPiece F F_lt 0) * x) x := by
  let rx := Quotient.out x
  apply HEq_eq_mk_eq F F_lt (zero_add i) (one_mul (rx : R))
  · rw [← Quotient.out_eq' x]
    exact (gradedMul_def F F_lt (1 : F 0) rx).symm
  · exact (Quotient.out_eq' x).symm

lemma GradedPiece.HEq_mul_one [hasGMul F F_lt] {i : ι} (x : GradedPiece F F_lt i) :
    HEq (x * (1 : GradedPiece F F_lt 0)) x := by
  let rx := Quotient.out x
  apply HEq_eq_mk_eq F F_lt (add_zero i) (mul_one (rx : R))
  · rw [← Quotient.out_eq' x]
    exact (gradedMul_def F F_lt rx (1 : F 0)).symm
  · exact (Quotient.out_eq' x).symm

lemma GradedPiece.HEq_mul_assoc [hasGMul F F_lt] {i j k : ι}
    (a : GradedPiece F F_lt i) (b : GradedPiece F F_lt j) (c : GradedPiece F F_lt k) :
    HEq (a * b * c) (a * (b * c)) := by
  let ra := Quotient.out a
  let rb := Quotient.out b
  let rc := Quotient.out c
  apply HEq_eq_mk_eq F F_lt (add_assoc i j k) (mul_assoc (ra : R) rb rc)
  · show a * b * c = ⟦ra * rb * rc⟧
    rw [← Quotient.out_eq' c]
    convert (gradedMul_def F F_lt (ra * rb) rc).symm
    rw [← Quotient.out_eq' a, ← Quotient.out_eq' b]
    exact (gradedMul_def F F_lt ra rb).symm
  · show a * (b * c) = ⟦ra * (rb * rc)⟧
    rw [← Quotient.out_eq' a]
    convert (gradedMul_def F F_lt ra (rb * rc)).symm
    rw [← Quotient.out_eq' b, ← Quotient.out_eq' c]
    exact (gradedMul_def F F_lt rb rc).symm

lemma Filtration.pow_mem [IsRingFiltration F F_lt] (n : ℕ) {i : ι}
    (x : ofClass (F i)) : (x : R) ^ n ∈ ofClass (F (n • i)) := by
  induction' n with d hd
  · simpa using IsRingFiltration.toGradedMonoid.one_mem
  · rw [pow_succ, succ_nsmul i d]
    exact IsRingFiltration.toGradedMonoid.mul_mem hd x.2

lemma Filtration.pow_lift [hasGMul F F_lt] (n : ℕ) {i : ι} (x₁ x₂ : ofClass (F i)) (h : x₁ ≈ x₂) :
    (⟨x₁ ^ n, Filtration.pow_mem F F_lt n x₁⟩ : ofClass (F (n • i))) ≈
    (⟨x₂ ^ n, Filtration.pow_mem F F_lt n x₂⟩ : ofClass (F (n • i))) := by
  induction' n with d hd
  · simp only [pow_zero, mk_eq, exact]
  · simp only [pow_succ, HasEquiv.Equiv, QuotientAddGroup.leftRel_apply] at h hd ⊢
    have mem1 : x₁.1 ^ d * x₂.1 - x₁.1 ^ d * x₁.1 ∈ F_lt ((d + 1) • i) := by
      rw [← mul_sub, sub_eq_neg_add, succ_nsmul i d]
      exact hasGMul.mul_F_lt_mem (Filtration.pow_mem F F_lt d x₁) h
    have mem2 : x₂.1 ^ d * x₂.1 - x₁.1 ^ d * x₂.1 ∈ F_lt ((d + 1) • i) := by
      rw [← sub_mul, sub_eq_neg_add]
      simp only [← sub_mul, sub_eq_neg_add, succ_nsmul i d]
      exact hasGMul.F_lt_mul_mem hd x₂.2
    show -(x₁.1 ^ d * x₁.1) + x₂.1 ^ d * x₂.1 ∈ (F_lt ((d + 1) • i))
    have : -(x₁.1 ^ d * x₁.1) + x₂.1 ^ d * x₂.1 =
      x₁.1 ^ d * x₂.1 - x₁.1 ^ d * x₁.1 + (x₂.1 ^ d * x₂.1 - x₁.1 ^ d * x₂.1) := by abel
    simpa only [this] using add_mem mem1 mem2

/-- The graded nat power between graded pieces. -/
def GradedPiece.gnpow [hasGMul F F_lt] (n : ℕ) {i : ι} :
    GradedPiece F F_lt i → GradedPiece F F_lt (n • i) :=
  Quotient.map (fun x ↦ ⟨x.1 ^ n, Filtration.pow_mem F F_lt n x⟩)
  (fun x₁ x₂ h ↦ Filtration.pow_lift F F_lt n x₁ x₂ h)

lemma gnpow_def [hasGMul F F_lt] (n : ℕ) {i : ι} (x : F i) :
    mk F F_lt ⟨x.1 ^ n, Filtration.pow_mem F F_lt n x⟩ = GradedPiece.gnpow F F_lt n (mk F F_lt x) :=
  rfl

lemma GradedPiece.gnpow_zero' [hasGMul F F_lt] {i : ι} (x : GradedPiece F F_lt i) :
    HEq (gnpow F F_lt 0 x) (1 : GradedPiece F F_lt 0) := by
  let rx := Quotient.out x
  apply HEq_eq_mk_eq F F_lt (zero_nsmul i) (pow_zero rx.1) (Filtration.pow_mem F F_lt 0 rx)
    (1 : F 0).2 _ rfl
  nth_rw 1 [gnpow_def F F_lt 0 rx, mk_eq, ← Quotient.out_eq x]

lemma GradedPiece.gnpow_succ' [hasGMul F F_lt] (n : ℕ) {i : ι} (x : GradedPiece F F_lt i) :
    HEq (gnpow F F_lt n.succ x) (gnpow F F_lt n x * x) := by
  let rx := Quotient.out x
  have mk_rx : mk F F_lt rx = x := QuotientAddGroup.out_eq' x
  have : rx.1 ^ n * rx.1 ∈ (F (n • i + i)) :=
    IsRingFiltration.toGradedMonoid.mul_mem (Filtration.pow_mem F F_lt n rx) rx.2
  apply HEq_eq_mk_eq F F_lt (succ_nsmul i n) (pow_succ rx.1 n)
    (Filtration.pow_mem F F_lt (n + 1) rx) this
  · rw [gnpow_def, mk_rx]
  · rw [← mk_rx, ← gnpow_def]
    rfl

instance [hasGMul F F_lt] : GradedMonoid.GMonoid (GradedPiece F F_lt) where
  one_mul := fun ⟨i, a⟩ => Sigma.ext (by simp) (GradedPiece.HEq_one_mul F F_lt a)
  mul_one := fun ⟨i, a⟩ => Sigma.ext (by simp) (GradedPiece.HEq_mul_one F F_lt a)
  mul_assoc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    Sigma.ext (add_assoc i j k) (GradedPiece.HEq_mul_assoc F F_lt a b c)
  gnpow := GradedPiece.gnpow F F_lt
  gnpow_zero' := fun ⟨i, a⟩ ↦ Sigma.ext (zero_nsmul i) (GradedPiece.gnpow_zero' F F_lt a)
  gnpow_succ' :=  fun n ⟨i, a⟩ ↦ Sigma.ext (succ_nsmul i n) (GradedPiece.gnpow_succ' F F_lt n a)

lemma GradedPiece.mul_zero [hasGMul F F_lt] {i j : ι} (a : GradedPiece F F_lt i) :
    a * (0 : GradedPiece F F_lt j) = 0 := by
  rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
  induction a using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  simp only [Quotient.eq'', ZeroMemClass.coe_zero, mul_zero, QuotientAddGroup.leftRel_apply,
    add_zero, neg_mem_iff]
  show _ * (0 : R) ∈ (F_lt (i + j))
  simpa only [MulZeroClass.mul_zero] using zero_mem (F_lt (i + j))

lemma GradedPiece.zero_mul [hasGMul F F_lt] {i j : ι} (a : GradedPiece F F_lt i) :
    (0 : GradedPiece F F_lt j) * a = 0 := by
  rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
  induction a using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  simp only [Quotient.eq'', ZeroMemClass.coe_zero, zero_mul, QuotientAddGroup.leftRel_apply,
    add_zero, neg_mem_iff]
  show (0 : R) * _ ∈ (F_lt (j + i))
  simpa only [MulZeroClass.zero_mul] using zero_mem (F_lt (j + i))

lemma GradedPiece.mul_add [hasGMul F F_lt] {i j : ι} (a : GradedPiece F F_lt i)
    (b c : GradedPiece F F_lt j) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind'
  induction b using Quotient.ind'
  induction c using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  simp only [Quotient.eq'', QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_add, NegMemClass.coe_neg, AddSubgroup.mem_mk, SetLike.mem_coe]
  rename_i a1 a2 a3
  have : -(a1 * (a2 + a3)).1 + ((a1 * a2).1 + (a1 * a3).1) = 0 := by
    have : -(a1.1 * (a2.1 + a3.1)) + (a1.1 * a2.1 + a1.1 * a3.1) = 0 := by noncomm_ring
    rw [← this]
    rfl
  simpa only [this] using zero_mem (F_lt (i + j))

lemma GradedPiece.add_mul [hasGMul F F_lt] {i j : ι} (a b : GradedPiece F F_lt i)
    (c : GradedPiece F F_lt j) : (a + b) * c = a * c + b * c := by
  induction a using Quotient.ind'
  induction b using Quotient.ind'
  induction c using Quotient.ind'
  rename_i a1 a2 a3
  show Quotient.mk'' _ = Quotient.mk'' _
  simp only [Quotient.eq'', QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_add, NegMemClass.coe_neg, AddSubgroup.mem_mk, SetLike.mem_coe]
  have : -((a1 + a2) * a3).1 + ((a1 * a3).1 + (a2 * a3).1) = 0 := by
    have : -((a1.1 + a2.1) * a3.1) + (a1.1 * a3.1 + a2.1 * a3.1) = 0 := by noncomm_ring
    rw [← this]
    rfl
  simpa only [this] using zero_mem (F_lt (i + j))

/-- The nat scalar multiple in `GradedPiece F F_lt 0`.-/
def GradedPiece.natCast [IsRingFiltration F F_lt] (n : ℕ) : GradedPiece F F_lt 0 :=
  mk F F_lt (n • (1 : F 0))

lemma GradedPiece.natCast_zero [IsRingFiltration F F_lt] :
    (natCast F F_lt 0 : GradedPiece F F_lt 0) = 0 := by
  show mk F F_lt (0 • (1 : F 0)) = 0
  simp only [zero_smul, mk_eq]
  rfl

lemma GradedPiece.natCast_succ [IsRingFiltration F F_lt] (n : ℕ) :
    (natCast F F_lt n.succ : GradedPiece F F_lt 0) =
    (natCast F F_lt n : GradedPiece F F_lt 0) + 1 := by
  show mk F F_lt (n.succ • (1 : F 0)) = mk F F_lt ((n • (1 : F 0)) + (1 : F 0))
  simp [succ_nsmul]

instance [hasGMul F F_lt] : DirectSum.GSemiring (GradedPiece F F_lt) :=
{ GradedMul.instGMonoidGradedPieceOfHasGMul F F_lt with
  mul_zero := GradedPiece.mul_zero F F_lt
  zero_mul := GradedPiece.zero_mul F F_lt
  mul_add := GradedPiece.mul_add F F_lt
  add_mul := GradedPiece.add_mul F F_lt
  natCast := GradedPiece.natCast F F_lt
  natCast_zero := GradedPiece.natCast_zero F F_lt
  natCast_succ := GradedPiece.natCast_succ F F_lt }

/-- The int scalar multiple in `GradedPiece F F_lt 0`.-/
def GradedPiece.intCast [IsRingFiltration F F_lt] (n : ℤ) : GradedPiece F F_lt 0 :=
  mk F F_lt (n • (1 : F 0))

lemma GradedPiece.intCast_ofNat [IsRingFiltration F F_lt] (n : ℕ) :
    intCast F F_lt n = natCast F F_lt n := by
  show mk F F_lt ((n : ℤ) • (1 : F 0)) = mk F F_lt (n • (1 : F 0))
  simp

lemma GradedPiece.intCast_negSucc_ofNat [IsRingFiltration F F_lt] (n : ℕ) :
    intCast F F_lt (Int.negSucc n) = - (natCast F F_lt (n + 1)) := by
  show mk F F_lt ((Int.negSucc n) • (1 : F 0)) = - mk F F_lt ((n + 1) • (1 : F 0))
  simp only [negSucc_zsmul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mk_eq]
  rfl

instance [hasGMul F F_lt] : DirectSum.GRing (GradedPiece F F_lt) where
  intCast := GradedPiece.intCast F F_lt
  intCast_ofNat := GradedPiece.intCast_ofNat F F_lt
  intCast_negSucc_ofNat := GradedPiece.intCast_negSucc_ofNat F F_lt

open DirectSum in
instance [hasGMul F F_lt] [DecidableEq ι] : Ring (AssociatedGraded F F_lt) :=
  DirectSum.ring (GradedPiece F F_lt)

end GradedMul

end HasGMul

end GradedRing
