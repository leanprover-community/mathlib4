/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Order.Module.Archimedean
import Mathlib.Algebra.Order.Monoid.PNat
import Mathlib.Data.Sign.Defs
import Mathlib.GroupTheory.Divisible
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Divisible Hull of an abelian group

This file constructs the divisible hull of an `AddCommMonoid` as a `ℕ`-module localized at
`ℕ+` (implemented using `nonZeroDivisors ℕ`), which is a ℕ-divisible `AddCommMonoid` and a
`ℚ≥0`-module. Futher more, we show that
* when `M` is a group, so is `DivisibleHull M`, which is also a `ℚ`-module
* when `M` is linearly ordered and cancellative, so is `DivisibleHull M`, which is also an
  ordered `ℚ≥0`-module.
* when `M` is a linearly ordered group, `DivisibleHull M` is an ordered `ℚ`-module, and
  `ArchimedeanClass` are preserved.

## Main declarations

* `DivisibleHull M` is the divisible hull of an abelian group.
* `DivisibleHull.coeAddEquiv` shows the divisible hull of a `ℕ`-divisible torsion-free monoid is
  isomorphic to itself.
* `DivisibleHull.archimedeanClassOrderIso M` is the equivalence between `ArchimedeanClass M` and
  `ArchimedeanClass (DivisibleHull M)`.

-/

variable (M : Type*) [AddCommMonoid M]

local notation "↑ⁿ" => PNat.equivNonZeroDivisorsNat

/-- The divisible hull of a `AddCommMonoid` (as a ℕ-module) is the localized module by
`ℕ+` (implemented using `nonZeroDivisors ℕ`), thus a ℕ-divisble group, or a `ℚ≥0`-module. -/
abbrev DivisibleHull := LocalizedModule (nonZeroDivisors ℕ) M

namespace DivisibleHull
variable {M}

/-- Create an element `m / s`. -/
def mk (m : M) (s : ℕ+) : DivisibleHull M := LocalizedModule.mk m (↑ⁿ s)

/-- Coercion from `M` to `DivisibleHull M` defined as `m ↦ m / 1`. -/
instance : Coe M (DivisibleHull M) where
  coe m := mk m 1

@[simp]
theorem mk_zero (s : ℕ+) : mk (0 : M) s = 0 := by simp [mk]

@[elab_as_elim, induction_eliminator]
theorem ind {motive : DivisibleHull M → Prop} (mk : ∀ num den, motive (.mk num den)) :
    ∀ x, motive x := by
  apply LocalizedModule.induction_on
  intro m s
  apply mk m (↑ⁿ.symm s)

theorem mk_eq_mk {m m' : M} {s s' : ℕ+} :
    mk m s = mk m' s' ↔ ∃ u : ℕ+, u.val • s'.val • m = u.val • s.val • m' := by
  unfold mk
  rw [LocalizedModule.mk_eq]
  simp_rw [Submonoid.smul_def]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨↑ⁿ.symm u, by simpa using hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨↑ⁿ u, by simpa using hu⟩

/-- If `f : M → ℕ+ → α` respects the equivalence on localization,
lift it to a function `DivisibleHull M → α`. -/
def liftOn {α : Type*} (x : DivisibleHull M)
    (f : M → ℕ+ → α)
    (h : ∀ (m m' : M) (s s' : ℕ+), mk m s = mk m' s' → f m s = f m' s') : α :=
  LocalizedModule.liftOn x (fun p ↦ f p.1 (↑ⁿ.symm p.2)) fun p p' heq ↦
    h p.1 p'.1 (↑ⁿ.symm p.2) (↑ⁿ.symm p'.2) ((by
      obtain ⟨u, hu⟩ := heq
      exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, by simpa using hu⟩))

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
      ((by
        obtain ⟨u, hu⟩ := heq
        exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, by simpa using hu⟩
      )) ((by
        obtain ⟨u, hu⟩ := heq'
        exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, by simpa using hu⟩
      ))

@[simp]
theorem liftOn₂_mk {α : Type*} (m m' : M) (s s' : ℕ+)
    (f : M → ℕ+ → M → ℕ+ → α)
    (h : ∀ (m n m' n' : M) (s t s' t' : ℕ+),
      mk m s = mk m' s' → mk n t = mk n' t' → f m s n t = f m' s' n' t') :
    liftOn₂ (mk m s) (mk m' s') f h = f m s m' s' := rfl

instance decidable_liftOn₂ (f : M → ℕ+ → M → ℕ+ → Prop)
    [(m : M) → (s : ℕ+) → (n : M) → (t : ℕ+) → Decidable (f m s n t)]
    (h : ∀ (m n m' n' : M) (s t s' t' : ℕ+),
      mk m s = mk m' s' → mk n t = mk n' t' → f m s n t = f m' s' n' t')
    (x y : DivisibleHull M) :
    Decidable (liftOn₂ x y f h) := by
  change Decidable (Quotient.liftOn₂ _ _ _ ?_)
  · infer_instance
  · intro a1 a2 b1 b2 h1 h2
    refine h a1.1 a2.1 b1.1 b2.1 (↑ⁿ.symm a1.2) (↑ⁿ.symm a2.2) (↑ⁿ.symm b1.2) (↑ⁿ.symm b2.2) ?_ ?_
    · obtain ⟨u, hu⟩ := h1
      exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, by simpa using hu⟩
    · obtain ⟨u, hu⟩ := h2
      exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, by simpa using hu⟩

theorem mk_add_mk {m1 m2 : M} {s1 s2 : ℕ+} :
    mk m1 s1 + mk m2 s2 = mk (s2.val • m1 + s1.val • m2) (s1 * s2) := LocalizedModule.mk_add_mk

theorem mk_add_mk_left {m1 m2 : M} {s : ℕ+} :
    mk m1 s + mk m2 s = mk (m1 + m2) s := by
  rw [mk_add_mk, mk_eq_mk]
  exact ⟨1, by simp [smul_smul]⟩

@[simp]
theorem coe_add {m1 m2 : M} : ↑(m1 + m2) = (↑m1 + ↑m2 : DivisibleHull M) := by simp [mk_add_mk_left]

variable (M) in
/-- Coercion from `M` to `DivisibleHull M` as a `AddMonoidHom`. -/
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
    a • mk m s =
    mk (a.num • m) (⟨a.den, Nat.pos_of_ne_zero (a.den_ne_zero)⟩ * s) := by
  convert LocalizedModule.mk'_smul_mk ℚ≥0 a.num m ⟨a.den, by simp⟩ (↑ⁿ s)
  simp [IsLocalization.eq_mk'_iff_mul_eq]

noncomputable
instance : DivisibleBy (DivisibleHull M) ℕ where
  div m n := (n⁻¹ : ℚ≥0) • m
  div_zero := by simp
  div_cancel n {m} h := by
    rw [← Nat.cast_smul_eq_nsmul ℚ≥0 n, smul_smul, mul_inv_cancel₀ (by simpa using h), one_smul]

section TorsionFree
variable [IsAddTorsionFree M]

theorem mk_eq_mk_iff_smul_eq_smul {m m' : M} {s s' : ℕ+} :
    mk m s = mk m' s' ↔ s'.val • m = s.val • m' := by
  rw [mk_eq_mk]
  constructor
  · intro ⟨u, h⟩
    exact (nsmul_right_inj (by simp)).mp h
  · intro hr
    use 1
    rw [hr]

theorem mk_left_injective (s : ℕ+) :
    Function.Injective (fun (m : M) ↦ mk m s) := by
  intro m n h
  simp_rw [mk_eq_mk_iff_smul_eq_smul] at h
  exact nsmul_right_injective (by simp) h

theorem coe_injective : Function.Injective ((↑) : M → DivisibleHull M) :=
  mk_left_injective 1

theorem coeAddMonoidHom_injective : Function.Injective (coeAddMonoidHom M) := coe_injective

end TorsionFree

section Divisible
variable [DivisibleBy M ℕ]

theorem mk_left_surjective (s : ℕ+) :
    Function.Surjective (fun (m : M) ↦ mk m s) := by
  intro m
  induction m with | mk m t
  use DivisibleBy.div (s.val • m) t.val
  rw [mk_eq_mk]
  use 1
  rw [DivisibleBy.div_cancel _ (by simp)]

theorem coe_surjective : Function.Surjective ((↑) : M → DivisibleHull M) :=
  mk_left_surjective 1

theorem coeAddMonoidHom_surjective : Function.Surjective (coeAddMonoidHom M) := coe_surjective

section TorsionFree
variable [IsAddTorsionFree M]

variable (M) in
/-- A torsion-free divisible monoid is isomorphic to its divisible hull. -/
def coeAddEquiv : M ≃+ DivisibleHull M where
  __ := coeAddMonoidHom M
  invFun m := m.liftOn (fun m s ↦ DivisibleBy.div m s.val) (fun m m' s s' h ↦ by
    simp_rw [mk_eq_mk_iff_smul_eq_smul] at h
    rw [← nsmul_right_inj (show s.val ≠ 0 by simp)]
    rw [← nsmul_right_inj (show s'.val ≠ 0 by simp)]
    rw [DivisibleBy.div_cancel _ (by simp), h, smul_comm, DivisibleBy.div_cancel _ (by simp)])
  left_inv m := by
    rw [← nsmul_right_inj (show 1 ≠ 0 by simp)]
    simp [DivisibleBy.div_cancel]
  right_inv m := by
    induction m with | mk m s
    simp [mk_eq_mk_iff_smul_eq_smul, DivisibleBy.div_cancel]

end TorsionFree

end Divisible

section Group
variable {M : Type*} [AddCommGroup M]

theorem mk_neg (m : M) (s : ℕ+) : mk (-m) s = - mk m s :=
  eq_neg_of_add_eq_zero_left (by simp [mk_add_mk_left])

noncomputable
instance : SMul ℚ (DivisibleHull M) where
  smul a x := (SignType.sign a : ℤ) • (show ℚ≥0 from ⟨|a|, abs_nonneg _⟩) • x

theorem qsmul_def (a : ℚ) (x : DivisibleHull M) :
    a • x = (SignType.sign a : ℤ) • (show ℚ≥0 from ⟨|a|, abs_nonneg _⟩) • x :=
  rfl

theorem qsmul_of_nonneg {a : ℚ} (h : 0 ≤ a) (x : DivisibleHull M) :
    a • x = (show ℚ≥0 from ⟨a, h⟩) • x := by
  obtain rfl | h := eq_or_lt_of_le h
  · have : ⟨0, Left.nonneg_neg_iff.mpr h⟩ = (0 : ℚ≥0) := rfl
    simp [qsmul_def, this]
  · simp [qsmul_def, abs_eq_self.mpr h.le, sign_pos h]

theorem qsmul_of_nonpos {a : ℚ} (h : a ≤ 0) (x : DivisibleHull M) :
    a • x = -((show ℚ≥0 from ⟨-a, Left.nonneg_neg_iff.mpr h⟩) • x) := by
  obtain rfl | h := eq_or_lt_of_le h
  · have : ⟨0, Left.nonneg_neg_iff.mpr h⟩ = (0 : ℚ≥0) := rfl
    simp [qsmul_def, this]
  · simp [qsmul_def, abs_eq_neg_self.mpr h.le, sign_neg h]

theorem qsmul_mk (a : ℚ) (m : M) (s : ℕ+) :
    a • mk m s = mk (a.num • m) (⟨a.den, Nat.pos_of_ne_zero (a.den_ne_zero)⟩ * s) := by
  obtain h | h := le_total 0 a
  · rw [qsmul_of_nonneg h]
    have : a.num.natAbs • m = a.num • m := by
      rw [← natCast_zsmul]
      congr
      simpa using h
    simp [nnqsmul_mk, this]
  · rw [qsmul_of_nonpos h]
    have : a.num.natAbs • m = -a.num • m := by
      rw [← natCast_zsmul]
      congr
      simpa using h
    simp [nnqsmul_mk, this, mk_neg]

noncomputable
instance : Module ℚ (DivisibleHull M) where
  one_smul x := by
    induction x with | mk m s
    simp only [qsmul_mk, Rat.num_ofNat, one_smul, Rat.den_ofNat]
    apply congrArg
    simp
  zero_smul x := by
    induction x with | mk m s
    simp [qsmul_mk]
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
  suffices (a : ℚ) • mk m s = mk (a • m) s by simpa [Int.cast_smul_eq_zsmul]
  rw [qsmul_mk]
  exact congrArg _ <| Subtype.eq (by simp)

end Group

section LinearOrder
variable {M : Type*} [AddCommMonoid M] [LinearOrder M] [AddLeftStrictMono M]

private theorem lift_aux (m n m' n' : M) (s t s' t' : ℕ+)
    (h : mk m s = mk m' s') (h' : mk n t = mk n' t') :
    (fun m s n t ↦ t.val • m ≤ s.val • n) m s n t =
    (fun m s n t ↦ t.val • m ≤ s.val • n) m' s' n' t' := by
  rw [mk_eq_mk_iff_smul_eq_smul] at h h'
  suffices t.val • m ≤ s.val • n ↔ t'.val • m' ≤ s'.val • n' by simpa
  rw [← (nsmul_right_strictMono
    (mul_ne_zero (show s'.val ≠ 0 by simp) (show t'.val ≠ 0 by simp))).le_iff_le]
  rw [show (s'.val * t'.val) • t.val • m = (t.val * t'.val) • s'.val • m by
    simp_rw [smul_smul]
    ring_nf]
  rw [show (s'.val * t'.val) • s.val • n = (s.val * s'.val) • t'.val • n by
    simp_rw [smul_smul]
    ring_nf]
  rw [h, h']
  rw [show (t.val * t'.val) • s.val • m' = (s.val * t.val) • t'.val • m' by
    simp_rw [smul_smul]
    ring_nf]
  rw [show (s.val * s'.val) • t.val • n' = (s.val * t.val) • s'.val • n' by
    simp_rw [smul_smul]
    ring_nf]
  exact (nsmul_right_strictMono
    (mul_ne_zero (show s.val ≠ 0 by simp) (show t.val ≠ 0 by simp))).le_iff_le

instance : LE (DivisibleHull M) where
  le x y := liftOn₂ x y (fun m s n t ↦ t.val • m ≤ s.val • n) lift_aux

theorem mk_le_mk {m m' : M} {s s' : ℕ+} :
    mk m s ≤ mk m' s' ↔ s'.val • m ≤ s.val • m' := by rfl

instance : LinearOrder (DivisibleHull M) where
  le_refl a := by
    induction a with | mk m s
    rw [mk_le_mk]
  le_trans a b c hab hbc := by
    induction a with | mk ma sa
    induction b with | mk mb sb
    induction c with | mk mc sc
    rw [mk_le_mk] at ⊢ hab hbc
    rw [← (nsmul_right_strictMono (show sb.val ≠ 0 by simp)).le_iff_le]
    rw [← (nsmul_right_strictMono (show sc.val ≠ 0 by simp)).le_iff_le] at hab
    rw [← (nsmul_right_strictMono (show sa.val ≠ 0 by simp)).le_iff_le] at hbc
    rw [smul_comm _ _ ma, smul_comm _ _ mc]
    rw [smul_comm _ _ mb] at hab
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
  toDecidableLE := decidable_liftOn₂ _ _

theorem mk_lt_mk {m m' : M} {s s' : ℕ+} : mk m s < mk m' s' ↔ s'.val • m < s.val • m' := by
  simp_rw [lt_iff_not_ge, mk_le_mk]

-- An intermediate lemma for `IsOrderedCancelAddMonoid`.
-- For public API, use `_root_.add_lt_add_left`.
private lemma aux_add_lt_add_left (a : DivisibleHull M) {b c : DivisibleHull M} (h : b < c) :
    a + b < a + c := by
  induction a with | mk ma sa
  induction b with | mk mb sb
  induction c with | mk mc sc
  simp_rw [mk_add_mk]
  rw [mk_lt_mk] at ⊢ h
  simp_rw [PNat.mul_coe, mul_smul, smul_add, smul_smul]
  suffices (sa * sb * sc : ℕ) • ma + (sa * sa : ℕ) • (sc : ℕ) • mb
      < (sa * sb * sc : ℕ) • ma + (sa * sa : ℕ) • (sb : ℕ) • mc by
    simp_rw [smul_smul] at this
    convert this using 3 <;> ring
  apply _root_.add_lt_add_left <| nsmul_lt_nsmul_right (by simp) h

instance : IsOrderedCancelAddMonoid (DivisibleHull M) where
  add_le_add_left a b h c := by
    obtain rfl | h := eq_or_lt_of_le h
    · simp
    exact (aux_add_lt_add_left c h).le
  le_of_add_le_add_left a b c h := by
    contrapose! h
    exact aux_add_lt_add_left a h

instance : PosSMulStrictMono ℚ≥0 (DivisibleHull M) where
  smul_lt_smul_of_pos_left a ha b c h := by
    induction b with | mk mb sb
    induction c with | mk mc sc
    simp_rw [mk_lt_mk] at h
    simp_rw [nnqsmul_mk, mk_lt_mk, smul_smul, PNat.mul_coe]
    simp_rw [mul_right_comm _ _ a.num, mul_smul _ _ mc, mul_smul _ _ mb]
    exact (nsmul_right_strictMono (by simpa using ha.ne.symm)).lt_iff_lt.mpr h

end LinearOrder

section OrderedGroup
variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

instance : PosSMulStrictMono ℚ (DivisibleHull M) where
  smul_lt_smul_of_pos_left a ha b c h := by
    simp_rw [qsmul_of_nonneg ha.le]
    apply smul_lt_smul_of_pos_left h (by simpa using ha)

variable (M) in
/-- Coercion from `M` to `DivisibleHull M` as an `OrderAddMonoidHom`. -/
@[simps!]
def coeOrderAddMonoidHom : M →+o DivisibleHull M where
  __ := coeAddMonoidHom M
  monotone' a b h := by simpa [mk_le_mk] using h

theorem coeOrderAddMonoidHom_injective : Function.Injective (coeOrderAddMonoidHom M) :=
  coeAddMonoidHom_injective

variable (M) in
/-- Forward direction of `archimedeanClassOrderIso`. -/
private noncomputable
def aux_archimedeanClassOrderHom : ArchimedeanClass M →o ArchimedeanClass (DivisibleHull M) :=
  ArchimedeanClass.orderHom (coeOrderAddMonoidHom M)

/-- See `archimedeanClassOrderIso_symm_apply` for public API. -/
private theorem aux_archimedeanClassMk_mk (m : M) (s : ℕ+) :
    ArchimedeanClass.mk (mk m s) = aux_archimedeanClassOrderHom M (ArchimedeanClass.mk m) := by
  trans ArchimedeanClass.mk ((s.val : ℤ) • mk m s)
  · rw [ArchimedeanClass.mk_smul _ (show (s.val : ℤ) ≠ 0 by simp)]
  rw [aux_archimedeanClassOrderHom, ArchimedeanClass.orderHom_mk, coeOrderAddMonoidHom_apply,
    zsmul_mk]
  apply congrArg
  simp [mk_eq_mk_iff_smul_eq_smul]

/-- Use `Equiv.injective archimedeanClassOrderIso` for public API. -/
private theorem aux_archimedeanClassOrderHom_injective :
    Function.Injective (aux_archimedeanClassOrderHom M) :=
  ArchimedeanClass.orderHom_injective coeOrderAddMonoidHom_injective

variable (M) in
/-- Backward direction of `archimedeanClassOrderIso`. -/
private noncomputable
def aux_archimedeanClassOrderHomInv : ArchimedeanClass (DivisibleHull M) →o ArchimedeanClass M :=
  ArchimedeanClass.liftOrderHom (fun x ↦ x.liftOn (fun m s ↦ ArchimedeanClass.mk m)
    (fun _ _ _ _ h ↦ by
      apply aux_archimedeanClassOrderHom_injective
      apply_fun ArchimedeanClass.mk at h
      simpa [aux_archimedeanClassMk_mk] using h))
    (fun a b h ↦ by
      induction a with | mk _ _
      induction b with | mk _ _
      simp_rw [aux_archimedeanClassMk_mk] at h
      simpa using ((aux_archimedeanClassOrderHom M).monotone.strictMono_of_injective
        aux_archimedeanClassOrderHom_injective).le_iff_le.mp h)

variable (M) in
/-- The Archimedean classes of `DivisibleHull M` are the same as those of `M`. -/
noncomputable
def archimedeanClassOrderIso : ArchimedeanClass M ≃o ArchimedeanClass (DivisibleHull M) := by
  apply OrderIso.ofHomInv (aux_archimedeanClassOrderHom M) (aux_archimedeanClassOrderHomInv M)
  · ext a
    induction a using ArchimedeanClass.ind with | mk a
    induction a with | mk m s
    suffices ArchimedeanClass.mk (mk m 1) = ArchimedeanClass.mk (mk m s) by
      simpa [aux_archimedeanClassOrderHom, aux_archimedeanClassOrderHomInv]
    simp_rw [aux_archimedeanClassMk_mk]
  · ext a
    induction a using ArchimedeanClass.ind with | mk _
    simp [aux_archimedeanClassOrderHom, aux_archimedeanClassOrderHomInv]

@[simp]
theorem archimedeanClassOrderIso_apply (a : ArchimedeanClass M) :
    archimedeanClassOrderIso M a = ArchimedeanClass.orderHom (coeOrderAddMonoidHom M) a := rfl

@[simp]
theorem archimedeanClassOrderIso_symm_apply (m : M) (s : ℕ+) :
    (archimedeanClassOrderIso M).symm (ArchimedeanClass.mk (mk m s)) = ArchimedeanClass.mk m := rfl

end OrderedGroup

end DivisibleHull
