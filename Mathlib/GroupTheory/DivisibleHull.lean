/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Order.Module.Archimedean
import Mathlib.Algebra.Order.Monoid.PNat
import Mathlib.Data.Sign.Defs
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Divisible Hull of an abelian group

This file constructs the divisible hull of an `AddCommMonoid` as a `ℕ`-module localized at
`ℕ+` (implemented using `nonZeroDivisors ℕ`), which is a `ℚ≥0`-module.

Furthermore, we show that

* when `M` is a group, so is `DivisibleHull M`, which is also a `ℚ`-module
* when `M` is linearly ordered and cancellative, so is `DivisibleHull M`, which is also an
  ordered `ℚ≥0`-module.
* when `M` is a linearly ordered group, `DivisibleHull M` is an ordered `ℚ`-module, and
  `ArchimedeanClass` is preserved.

Despite the name, this file doesn't implement a `DivisibleBy` instance on `DivisibleHull`. This
should be implemented on `LocalizedModule` in a more general setting (TODO: implement this).
This file mainly focuses on the specialization to `ℕ` and the linear order property introduced by
it.

## Main declarations

* `DivisibleHull M` is the divisible hull of an abelian group.
* `DivisibleHull.archimedeanClassOrderIso M` is the equivalence between `ArchimedeanClass M` and
  `ArchimedeanClass (DivisibleHull M)`.

-/

variable {M : Type*} [AddCommMonoid M]

local notation "↑ⁿ" => PNat.equivNonZeroDivisorsNat

variable (M) in
/-- The divisible hull of a `AddCommMonoid` (as a ℕ-module) is the localized module by
`ℕ+` (implemented using `nonZeroDivisors ℕ`), thus a ℕ-divisble group, or a `ℚ≥0`-module. -/
abbrev DivisibleHull := LocalizedModule (nonZeroDivisors ℕ) M

namespace DivisibleHull

/-- Create an element `m / s`. -/
def mk (m : M) (s : ℕ+) : DivisibleHull M := LocalizedModule.mk m (↑ⁿ s)

/-- Define coercion as `m ↦ m / 1`. -/
@[coe]
abbrev coe (m : M) := mk m 1

/-- Coercion from `M` to `DivisibleHull M` defined as `m ↦ m / 1`. -/
instance : Coe M (DivisibleHull M) where
  coe := coe

@[simp]
theorem mk_zero (s : ℕ+) : mk (0 : M) s = 0 := by simp [mk]

@[elab_as_elim, induction_eliminator]
theorem ind {motive : DivisibleHull M → Prop} (mk : ∀ num den, motive (.mk num den)) :
    ∀ x, motive x :=
  LocalizedModule.induction_on fun m s ↦ mk m (↑ⁿ.symm s)

theorem mk_eq_mk {m m' : M} {s s' : ℕ+} :
    mk m s = mk m' s' ↔ ∃ u : ℕ+, u.val • s'.val • m = u.val • s.val • m' := by
  unfold mk
  rw [LocalizedModule.mk_eq, ↑ⁿ.exists_congr_left]
  rfl

/-- If `f : M → ℕ+ → α` respects the equivalence on localization,
lift it to a function `DivisibleHull M → α`. -/
def liftOn {α : Type*} (x : DivisibleHull M)
    (f : M → ℕ+ → α)
    (h : ∀ (m m' : M) (s s' : ℕ+), mk m s = mk m' s' → f m s = f m' s') : α :=
  LocalizedModule.liftOn x (fun p ↦ f p.1 (↑ⁿ.symm p.2)) fun p p' heq ↦
    h p.1 p'.1 (↑ⁿ.symm p.2) (↑ⁿ.symm p'.2) <| by
      obtain ⟨u, hu⟩ := heq
      exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩

@[simp]
theorem liftOn_mk {α : Type*} (m : M) (s : ℕ+)
    (f : M → ℕ+ → α)
    (h : ∀ (m m' : M) (s s' : ℕ+), mk m s = mk m' s' → f m s = f m' s') :
    liftOn (mk m s) f h = f m s := rfl

/-- If `f : M → ℕ+ → M → ℕ+ → α` respects the equivalence on
localization, lift it to a function `DivisibleHull M → DivisibleHull M → α`. -/
def liftOn₂ {α : Type*} (x y : DivisibleHull M)
    (f : M → ℕ+ → M → ℕ+ → α)
    (h : ∀ (m n m' n' : M) (s t s' t' : ℕ+),
      mk m s = mk m' s' → mk n t = mk n' t' → f m s n t = f m' s' n' t') : α :=
  LocalizedModule.liftOn₂ x y (fun p q ↦ f p.1 (↑ⁿ.symm p.2) q.1 (↑ⁿ.symm q.2))
    fun p q p' q' heq heq' ↦
    h p.1 q.1 p'.1 q'.1 (↑ⁿ.symm p.2) (↑ⁿ.symm q.2) (↑ⁿ.symm p'.2) (↑ⁿ.symm q'.2)
      (by
        obtain ⟨u, hu⟩ := heq
        exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩)
      (by
        obtain ⟨u, hu⟩ := heq'
        exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩)

@[simp]
theorem liftOn₂_mk {α : Type*} (m m' : M) (s s' : ℕ+)
    (f : M → ℕ+ → M → ℕ+ → α)
    (h : ∀ (m n m' n' : M) (s t s' t' : ℕ+),
      mk m s = mk m' s' → mk n t = mk n' t' → f m s n t = f m' s' n' t') :
    liftOn₂ (mk m s) (mk m' s') f h = f m s m' s' := rfl

theorem mk_add_mk {m1 m2 : M} {s1 s2 : ℕ+} :
    mk m1 s1 + mk m2 s2 = mk (s2.val • m1 + s1.val • m2) (s1 * s2) := LocalizedModule.mk_add_mk

theorem mk_add_mk_left {m1 m2 : M} {s : ℕ+} :
    mk m1 s + mk m2 s = mk (m1 + m2) s := by
  rw [mk_add_mk, mk_eq_mk]
  exact ⟨1, by simp [smul_smul]⟩

@[simp, norm_cast]
theorem coe_add {m1 m2 : M} : ↑(m1 + m2) = (↑m1 + ↑m2 : DivisibleHull M) := by simp [mk_add_mk_left]

variable (M) in
/-- Coercion from `M` to `DivisibleHull M` as an `AddMonoidHom`. -/
@[simps]
def coeAddMonoidHom : M →+ DivisibleHull M where
  toFun := (↑)
  map_zero' := by simp
  map_add' := by simp

theorem nsmul_mk (a : ℕ) (m : M) (s : ℕ+) : a • mk m s = mk (a • m) s := by
  induction a with
  | zero => simp
  | succ n h => simp [add_nsmul, mk_add_mk_left, h]

theorem nnqsmul_mk (a : ℚ≥0) (m : M) (s : ℕ+) :
    a • mk m s = mk (a.num • m) (⟨a.den, a.den_pos⟩ * s) := by
  convert LocalizedModule.mk'_smul_mk ℚ≥0 a.num m ⟨a.den, by simp⟩ (↑ⁿ s)
  simp [IsLocalization.eq_mk'_iff_mul_eq]

section TorsionFree
variable [IsAddTorsionFree M]

theorem mk_eq_mk_iff_smul_eq_smul {m m' : M} {s s' : ℕ+} :
    mk m s = mk m' s' ↔ s'.val • m = s.val • m' := by
  aesop (add simp [mk_eq_mk, nsmul_right_inj])

theorem mk_left_injective (s : ℕ+) : Function.Injective (fun (m : M) ↦ mk m s) := by
  intro m n h
  simp_rw [mk_eq_mk_iff_smul_eq_smul] at h
  exact nsmul_right_injective (by simp) h

theorem coe_injective : Function.Injective ((↑) : M → DivisibleHull M) :=
  mk_left_injective 1

@[simp, norm_cast]
theorem coe_inj {m m' : M} : (m : DivisibleHull M) = ↑m' ↔ m = m' :=
  coe_injective.eq_iff

end TorsionFree

section Group
variable {M : Type*} [AddCommGroup M]

theorem neg_mk (m : M) (s : ℕ+) : -mk m s = mk (-m) s :=
  (eq_neg_of_add_eq_zero_left (by simp [mk_add_mk_left])).symm

noncomputable
instance : SMul ℚ (DivisibleHull M) where
  smul a x := (SignType.sign a : ℤ) • (show ℚ≥0 from ⟨|a|, abs_nonneg _⟩) • x

theorem qsmul_def (a : ℚ) (x : DivisibleHull M) :
    a • x = (SignType.sign a : ℤ) • (show ℚ≥0 from ⟨|a|, abs_nonneg _⟩) • x :=
  rfl

theorem zero_qsmul (x : DivisibleHull M) : (0 : ℚ) • x = 0 := by
  simp [qsmul_def]

theorem qsmul_of_nonneg {a : ℚ} (h : 0 ≤ a) (x : DivisibleHull M) :
    a • x = (show ℚ≥0 from ⟨a, h⟩) • x := by
  have := h.eq_or_lt
  aesop (add simp [qsmul_def, abs_of_pos])

theorem qsmul_of_nonpos {a : ℚ} (h : a ≤ 0) (x : DivisibleHull M) :
    a • x = -((show ℚ≥0 from ⟨-a, Left.nonneg_neg_iff.mpr h⟩) • x) := by
  have := h.eq_or_lt
  aesop (add simp [qsmul_def, abs_of_neg])

theorem qsmul_mk (a : ℚ) (m : M) (s : ℕ+) :
    a • mk m s = mk (a.num • m) (⟨a.den, a.den_pos⟩ * s) := by
  obtain h | h := le_total 0 a
  · rw [qsmul_of_nonneg h, nnqsmul_mk, ← natCast_zsmul]
    congr
    simpa using h
  · rw [qsmul_of_nonpos h]
    have : a.num.natAbs • m = -a.num • m := by
      rw [← natCast_zsmul]
      congr
      simpa using h
    simp [nnqsmul_mk, this, ← neg_mk]

noncomputable
instance : Module ℚ (DivisibleHull M) where
  one_smul x := by
    induction x with | mk m s
    simp [qsmul_of_nonneg zero_le_one, nnqsmul_mk]
  zero_smul := zero_qsmul
  smul_zero a := by simp [qsmul_def]
  smul_add a x y := by simp [qsmul_def, smul_add]
  add_smul a b x := by
    induction x with | mk m s
    simp_rw [qsmul_mk, mk_add_mk, mk_eq_mk]
    use 1
    suffices ((a + b).num * a.den * b.den * (s * s)) • m =
        ((a.num * b.den + b.num * a.den) * (a + b).den * (s * s)) • m  by
      convert this using 1
      all_goals
      simp [← natCast_zsmul, smul_smul, ← add_smul]
      ring_nf
    rw [Rat.add_num_den']
  mul_smul a b x := by
    induction x with | mk m s
    simp_rw [qsmul_mk, mk_eq_mk]
    use 1
    suffices ((a * b).num * a.den * b.den * s) • m = (a.num * b.num * (a * b).den * s) • m by
      convert this using 1
      all_goals
      simp [← natCast_zsmul, smul_smul]
      ring_nf
    rw [Rat.mul_num_den']

theorem zsmul_mk (a : ℤ) (m : M) (s : ℕ+) : a • mk m s = mk (a • m) s := by
  simp [← Int.cast_smul_eq_zsmul ℚ a, qsmul_mk]

end Group

section LinearOrder
variable {M : Type*} [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]

private theorem lift_aux (m n m' n' : M) (s t s' t' : ℕ+)
    (h : mk m s = mk m' s') (h' : mk n t = mk n' t') :
    (t.val • m ≤ s.val • n) = (t'.val • m' ≤ s'.val • n') := by
  rw [mk_eq_mk_iff_smul_eq_smul] at h h'
  rw [propext_iff, ← nsmul_le_nsmul_iff_right (mul_ne_zero s'.ne_zero t'.ne_zero)]
  convert (nsmul_le_nsmul_iff_right (M := M) (mul_ne_zero s.ne_zero t.ne_zero)) using 2
  · simp_rw [smul_smul, mul_rotate s'.val, ← smul_smul, h, smul_smul]
    ring_nf
  · simp_rw [smul_smul, ← mul_rotate s'.val, ← smul_smul, ← h', smul_smul]
    ring_nf
instance : LE (DivisibleHull M) where
  le x y := liftOn₂ x y (fun m s n t ↦ t.val • m ≤ s.val • n) lift_aux

@[simp]
theorem mk_le_mk {m m' : M} {s s' : ℕ+} :
    mk m s ≤ mk m' s' ↔ s'.val • m ≤ s.val • m' := by rfl

instance : LinearOrder (DivisibleHull M) where
  le_refl a := by
    induction a with | mk m s
    simp
  le_trans a b c hab hbc := by
    induction a with | mk ma sa
    induction b with | mk mb sb
    induction c with | mk mc sc
    rw [mk_le_mk] at ⊢ hab hbc
    rw [← nsmul_le_nsmul_iff_right (show sb.val ≠ 0 by simp), smul_comm _ _ ma, smul_comm _ _ mc]
    rw [← nsmul_le_nsmul_iff_right (show sc.val ≠ 0 by simp), smul_comm _ _ mb] at hab
    rw [← nsmul_le_nsmul_iff_right (show sa.val ≠ 0 by simp)] at hbc
    exact hab.trans hbc
  le_antisymm a b h h' := by
    induction a with | mk ma sa
    induction b with | mk mb sb
    rw [mk_le_mk] at h h'
    rw [mk_eq_mk_iff_smul_eq_smul]
    exact le_antisymm h h'
  le_total a b := by
    induction a with | mk ma sa
    induction b with | mk mb sb
    simp_rw [mk_le_mk]
    exact le_total _ _
  toDecidableLE := by
    unfold DecidableLE LE.le instLE liftOn₂ LocalizedModule.liftOn₂
    infer_instance

@[simp]
theorem mk_lt_mk {m m' : M} {s s' : ℕ+} : mk m s < mk m' s' ↔ s'.val • m < s.val • m' := by
  simp_rw [lt_iff_not_ge, mk_le_mk]

instance : IsOrderedCancelAddMonoid (DivisibleHull M) :=
  .of_add_lt_add_left (fun a b c h ↦ by
    induction a with | mk ma sa
    induction b with | mk mb sb
    induction c with | mk mc sc
    simp_rw [mk_add_mk]
    rw [mk_lt_mk] at ⊢ h
    simp_rw [PNat.mul_coe, mul_smul, smul_add, smul_smul]
    have := add_lt_add_left (nsmul_lt_nsmul_right (sa * sa).ne_zero h) ((sa * sb * sc.val) • ma)
    simp_rw [PNat.mul_coe, smul_smul] at this
    convert this using 3 <;> ring)

instance : IsStrictOrderedModule ℚ≥0 (DivisibleHull M) where
  smul_lt_smul_of_pos_left a ha b c h := by
    induction b with | mk mb sb
    induction c with | mk mc sc
    simp_rw [mk_lt_mk] at h
    simp_rw [nnqsmul_mk, mk_lt_mk, smul_smul, PNat.mul_coe]
    simp_rw [mul_right_comm _ _ a.num, mul_smul _ _ mc, mul_smul _ _ mb]
    exact (nsmul_right_strictMono (by simpa using ha.ne.symm)).lt_iff_lt.mpr h
  smul_lt_smul_of_pos_right a ha b c h := by
    induction a with | mk m s
    simp_rw [nnqsmul_mk, mk_lt_mk, smul_smul, PNat.mul_coe, PNat.mk_coe]
    refine smul_lt_smul_of_pos_right ?_ ?_
    · convert mul_lt_mul_of_pos_right (NNRat.lt_def.mp h) (show 0 < s.val by simp) using 1 <;> ring
    · rw [← mk_zero 1, mk_lt_mk] at ha
      simpa using ha

end LinearOrder

section OrderedGroup
variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

instance : IsStrictOrderedModule ℚ (DivisibleHull M) where
  smul_lt_smul_of_pos_left a ha b c h := by
    simp_rw [qsmul_of_nonneg ha.le]
    apply smul_lt_smul_of_pos_left h (by simpa using ha)
  smul_lt_smul_of_pos_right a ha b c h := by
    apply lt_of_sub_pos
    rw [← sub_smul]
    simp_rw [qsmul_of_nonneg (sub_pos_of_lt h).le]
    apply smul_pos (by simpa [← NNRat.coe_pos] using h) ha

variable (M) in
/-- Coercion from `M` to `DivisibleHull M` as an `OrderAddMonoidHom`. -/
@[simps!]
def coeOrderAddMonoidHom : M →+o DivisibleHull M where
  __ := coeAddMonoidHom M
  monotone' a b h := by simpa using h

/-- `ArchimedeanClass.mk` of an element from `DivisibleHull` only depends on the numerator. -/
theorem archimedeanClassMk_mk_eq (m : M) (s s' : ℕ+) :
    ArchimedeanClass.mk (mk m s) = ArchimedeanClass.mk (mk m s') := by
  suffices (s : ℤ) • mk m s = (s' : ℤ) • mk m s' by
    apply_fun ArchimedeanClass.mk at this
    rw [ArchimedeanClass.mk_smul _ (by simp)] at this
    rw [ArchimedeanClass.mk_smul _ (by simp)] at this
    exact this
  simp_rw [zsmul_mk, mk_eq_mk_iff_smul_eq_smul, natCast_zsmul, smul_smul, mul_comm s'.val]

variable (M) in
/-- Forward direction of `archimedeanClassOrderIso`. -/
private noncomputable
def archimedeanClassOrderHom : ArchimedeanClass M →o ArchimedeanClass (DivisibleHull M) :=
  ArchimedeanClass.orderHom (coeOrderAddMonoidHom M)

/-- See `archimedeanClassOrderIso_symm_apply` for public API. -/
private theorem aux_archimedeanClassMk_mk (m : M) (s : ℕ+) :
    ArchimedeanClass.mk (mk m s) = archimedeanClassOrderHom M (ArchimedeanClass.mk m) := by
  rw [archimedeanClassOrderHom, ArchimedeanClass.orderHom_mk, coeOrderAddMonoidHom_apply]
  apply archimedeanClassMk_mk_eq

/-- Use `Equiv.injective archimedeanClassOrderIso` for public API. -/
private theorem aux_archimedeanClassOrderHom_injective :
    Function.Injective (archimedeanClassOrderHom M) :=
  ArchimedeanClass.orderHom_injective coe_injective

variable (M) in
/-- Backward direction of `archimedeanClassOrderIso`. -/
private noncomputable
def archimedeanClassOrderHomInv : ArchimedeanClass (DivisibleHull M) →o ArchimedeanClass M :=
  ArchimedeanClass.liftOrderHom (fun x ↦ x.liftOn (fun m s ↦ ArchimedeanClass.mk m)
    (fun _ _ _ _ h ↦ by
      apply aux_archimedeanClassOrderHom_injective
      apply_fun ArchimedeanClass.mk at h
      simpa [aux_archimedeanClassMk_mk] using h))
    (fun a b h ↦ by
      induction a with | mk _ _
      induction b with | mk _ _
      simp_rw [aux_archimedeanClassMk_mk] at h
      simpa using ((archimedeanClassOrderHom M).monotone.strictMono_of_injective
        aux_archimedeanClassOrderHom_injective).le_iff_le.mp h)

variable (M) in
/-- The Archimedean classes of `DivisibleHull M` are the same as those of `M`. -/
noncomputable
def archimedeanClassOrderIso : ArchimedeanClass M ≃o ArchimedeanClass (DivisibleHull M) := by
  apply OrderIso.ofHomInv (archimedeanClassOrderHom M) (archimedeanClassOrderHomInv M)
  · ext a
    induction a with | mk a
    induction a with | mk m s
    suffices ArchimedeanClass.mk (mk m 1) = ArchimedeanClass.mk (mk m s) by
      simpa [archimedeanClassOrderHom, archimedeanClassOrderHomInv]
    simp_rw [aux_archimedeanClassMk_mk]
  · ext a
    induction a with | mk _
    simp [archimedeanClassOrderHom, archimedeanClassOrderHomInv]

@[simp]
theorem archimedeanClassOrderIso_apply (a : ArchimedeanClass M) :
    archimedeanClassOrderIso M a = ArchimedeanClass.orderHom (coeOrderAddMonoidHom M) a := rfl

@[simp]
theorem archimedeanClassOrderIso_symm_apply (m : M) (s : ℕ+) :
    (archimedeanClassOrderIso M).symm (ArchimedeanClass.mk (mk m s)) = ArchimedeanClass.mk m := rfl

end OrderedGroup

end DivisibleHull
