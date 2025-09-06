/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Order.GroupWithZero.Submonoid
import Mathlib.Algebra.Order.Module.Archimedean
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.GroupTheory.Divisible
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Divisible Hull of an abelian group

This file constructs the divisible hull of an `AddCommMonoid` as a ℕ-module localized at
`nonZeroDivisors ℕ`, which is a ℕ-divisible `AddCommMonoid` and a `ℚ≥0`-module . Futher more,
we show that
* when `M` is a group, so is `DivisibleHull M`, which is also a `ℚ`-module
* when `M` is linearly ordered and cancellative, so is `DivisibleHull M`, which is also an
  ordered `ℚ≥0`-module.
* when `M` is a linearly ordered group, `DivisibleHull M` is an ordered `ℚ`-module, and
  `ArchimedeanClass` are preserved.

## Main declarations

* `DivisibleHull M` is the divisible hull of an abelian group.
* `DivisibleHull.archimedeanClassOrderIso M` is the equivalence between `ArchimedeanClass M` and
  `ArchimedeanClass (DivisibleHul M)`.

## Implementation notes

This could be equivalently implemented as localization at `nonZeroDivisors ℤ`, but it would
complicate the linear order implementation.
-/

-- TODO: move
instance : IsLocalization (nonZeroDivisors ℕ) ℚ≥0 where
  map_units' y := by simp
  surj' z := ⟨⟨z.num, ⟨z.den, by simp⟩⟩, by simp⟩
  exists_of_eq {x y} h := ⟨1, by simpa using h⟩

-- TODO: move
@[to_additive]
instance {α : Type*} [CommMonoid α] [LinearOrder α] [MulLeftStrictMono α] :
  IsMulTorsionFree α where pow_left_injective _ hn := (pow_left_strictMono hn).injective

namespace DivisibleHull2

variable (M : Type*) [AddCommMonoid M]

/-- The divisible hull of a `AddCommMonoid` (as a ℕ-module) is the localized module by
`nonZeroDivisors ℕ`, thus a ℕ-divisble group, or a `ℚ≥0`-module. -/
abbrev DivisibleHull := LocalizedModule (nonZeroDivisors ℕ) M

namespace DivisibleHull
variable {M}

/-- Create an element `m / s`. -/
def mk (m : M) (s : nonZeroDivisors ℕ) : DivisibleHull M := LocalizedModule.mk m s

@[simp]
theorem mk_zero (s : nonZeroDivisors ℕ) : mk (0 : M) s = 0 := by simp [mk]

theorem ind {motive : DivisibleHull M → Prop} (mk : ∀ num den, motive (.mk num den)) :
    ∀ x, motive x := by
  apply LocalizedModule.induction_on
  intro a
  apply mk

theorem mk_eq_mk {m m' : M} {s s' : nonZeroDivisors ℕ} :
    mk m s = mk m' s' ↔ ∃ u : nonZeroDivisors ℕ, u • s' • m = u • s • m' := by
  unfold mk
  exact LocalizedModule.mk_eq

/-- If `f : M → nonZeroDivisors ℕ → α` respects the equivalence on localization,
lift it to a function `DivisibleHull M → α`. -/
def liftOn {α : Type*} (x : DivisibleHull M)
    (f : M → nonZeroDivisors ℕ → α)
    (h : ∀ (m m' : M) (s s' : nonZeroDivisors ℕ), mk m s = mk m' s' → f m s = f m' s') : α :=
  LocalizedModule.liftOn x (Function.uncurry f) fun p p' heq ↦
    h p.1 p'.1 p.2 p'.2 (mk_eq_mk.mpr heq)

@[simp]
theorem liftOn_mk {α : Type*} (m : M) (s : nonZeroDivisors ℕ)
    (f : M → (nonZeroDivisors ℕ) → α)
    (h : ∀ (m m' : M) (s s' : nonZeroDivisors ℕ), mk m s = mk m' s' → f m s = f m' s') :
    liftOn (mk m s) f h = f m s := rfl

/-- If `f : M → nonZeroDivisors ℕ → M → nonZeroDivisors ℕ → α` respects the equivalence on
localization, lift it to a function `DivisibleHull M → DivisibleHull M → α`. -/
def liftOn₂ {α : Type*} (x y : DivisibleHull M)
    (f : M → nonZeroDivisors ℕ → M → nonZeroDivisors ℕ → α)
    (h : ∀ (m n m' n' : M) (s t s' t' : nonZeroDivisors ℕ),
      mk m s = mk m' s' → mk n t = mk n' t' → f m s n t = f m' s' n' t') : α :=
  LocalizedModule.liftOn₂ x y (fun p q ↦ f p.1 p.2 q.1 q.2) fun p q p' q' heq heq' ↦
    h p.1 q.1 p'.1 q'.1 p.2 q.2 p'.2 q'.2 (mk_eq_mk.mpr heq) (mk_eq_mk.mpr heq')

instance decidable_liftOn₂ (f : M → nonZeroDivisors ℕ → M → nonZeroDivisors ℕ → Prop)
    [(m : M) → (s : nonZeroDivisors ℕ) → (n : M) → (t : nonZeroDivisors ℕ) → Decidable (f m s n t)]
    (h : ∀ (m n m' n' : M) (s t s' t' : nonZeroDivisors ℕ),
      mk m s = mk m' s' → mk n t = mk n' t' → f m s n t = f m' s' n' t')
    (x y : DivisibleHull M) :
    Decidable (liftOn₂ x y f h) := by
  change Decidable (Quotient.liftOn₂ _ _ _ ?_)
  · infer_instance
  · intro a1 a2 b1 b2 h1 h2
    refine h a1.1 a2.1 b1.1 b2.1 a1.2 a2.2 b1.2 b2.2 ?_ ?_
    · rw [mk_eq_mk]
      exact h1
    · rw [mk_eq_mk]
      exact h2

theorem mk_eq_mk_iff_smul_eq_smul [IsAddTorsionFree M] {m m' : M} {s s' : nonZeroDivisors ℕ} :
    mk m s = mk m' s' ↔ s' • m = s • m' := by
  rw [mk_eq_mk]
  constructor
  · intro ⟨u, h⟩
    simp_rw [Submonoid.smul_def] at ⊢ h
    exact (nsmul_right_inj (by simp)).mp h
  · intro hr
    use 1
    rw [hr]

theorem mk_add_mk {m1 m2 : M} {s1 s2 : nonZeroDivisors ℕ} :
    mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2) := LocalizedModule.mk_add_mk

theorem mk_add_mk_left {m1 m2 : M} {s : nonZeroDivisors ℕ} :
    mk m1 s + mk m2 s = mk (m1 + m2) s := by
  rw [mk_add_mk]
  rw [mk_eq_mk]
  exact ⟨1, by simp [smul_smul]⟩

theorem nsmul_mk (a : ℕ) (m : M) (s : nonZeroDivisors ℕ) : a • mk m s = mk (a • m) s := by
  induction a with
  | zero => simp
  | succ n h =>
    simp [add_nsmul, mk_add_mk_left, h]

theorem nnqsmul_mk (a : ℚ≥0) (m : M) (s : nonZeroDivisors ℕ) :
    a • mk m s = mk (a.num • m) (⟨a.den, by simp⟩ * s) := by
  convert LocalizedModule.mk'_smul_mk ℚ≥0 a.num m ⟨a.den, by simp⟩ s
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  simp

instance : DivisibleBy (DivisibleHull M) ℕ where
  div m n :=
    if h : n = 0 then
      0
    else
      liftOn m (fun m s ↦ mk m ⟨s.val * n, by simpa using h⟩)
      (fun m m' s s' ↦ by
        suffices ∀ a : ℕ, a ≠ 0 → a • s' • m = a • s • m' →
            ∃ a : ℕ, a ≠ 0 ∧ a • (s'.val * n) • m = a • (s.val * n) • m' by
          simpa [mk_eq_mk, -Nat.exists_ne_zero]
        refine fun a ha h ↦ ⟨a, ha, ?_⟩
        simp_rw [Submonoid.smul_def] at h
        simp_rw [smul_smul, ← mul_assoc, mul_comm _ (n : ℕ), mul_smul, h])
  div_zero := by simp
  div_cancel n {m} h := by
    induction m using ind with | mk m s
    suffices ∃ a : ℕ, a ≠ 0 ∧ a • s • n • m = a • (s.val * n) • m by
      simpa [h, nsmul_mk, mk_eq_mk]
    use 1
    suffices s • n • m = (s.val * n) • m by simpa
    rw [mul_smul, Submonoid.smul_def]

variable {M : Type*} [AddCommGroup M]

theorem mk_neg (m : M) (s : nonZeroDivisors ℕ) : mk (-m) s = - mk m s :=
  eq_neg_of_add_eq_zero_left (by simp [mk_add_mk_left])

noncomputable
instance : SMul ℚ (DivisibleHull M) where
  smul a x :=
    if h : 0 ≤ a then
      (show ℚ≥0 from ⟨a, h⟩) • x
    else
      -((show ℚ≥0 from ⟨-a, le_of_lt (by simpa using h)⟩) • x)

theorem qsmul_def (a : ℚ) (x : DivisibleHull M) :
    a • x = if h : 0 ≤ a then
      (show ℚ≥0 from ⟨a, h⟩) • x
    else
      -((show ℚ≥0 from ⟨-a, le_of_lt (by simpa using h)⟩) • x) :=
  rfl

theorem qsmul_mk (a : ℚ) (m : M) (s : nonZeroDivisors ℕ) :
    a • mk m s = mk (a.num • m) (⟨a.den, by simp⟩ * s) := by
  rw [qsmul_def]
  split_ifs with h
  · have : a.num.natAbs • m = a.num • m := by
      rw [← natCast_zsmul]
      congr
      simpa using h
    simp [nnqsmul_mk, this]
  · have : a.num.natAbs • m = -a.num • m := by
      rw [← natCast_zsmul]
      congr
      simpa using (le_of_lt (lt_of_not_ge h))
    simp [nnqsmul_mk, this, mk_neg]

noncomputable
instance : Module ℚ (DivisibleHull M) where
  one_smul x := by
    induction x using ind with | mk m s
    simp only [qsmul_mk, Rat.num_ofNat, one_smul, Rat.den_ofNat]
    apply congrArg
    simp
  zero_smul x := by
    induction x using ind with | mk m s
    simp [qsmul_mk]
  smul_zero a := by simp [qsmul_def]
  smul_add a x y := by
    simp_rw [qsmul_def, dite_add_dite]
    simp [smul_add, -neg_add_rev, neg_add]
  add_smul a b x := by
    induction x using ind with | mk m s
    simp_rw [qsmul_mk, mk_add_mk, mk_eq_mk]
    use 1
    suffices ((a + b).num * a.den * b.den * (s * s)) • m =
        ((a.num * b.den + b.num * a.den) * (a + b).den * (s * s)) • m  by
      convert this using 1
      all_goals
      simp [Submonoid.smul_def, ← natCast_zsmul, smul_smul, ← add_smul]
      ring_nf
    rw [Rat.add_num_den']
  mul_smul a b x := by
    induction x using ind with | mk m s
    simp_rw [qsmul_mk, mk_eq_mk]
    use 1
    suffices ((a * b).num * a.den * b.den * s) • m = (a.num * b.num * (a * b).den * s) • m by
      convert this using 1
      all_goals
      simp [Submonoid.smul_def, ← natCast_zsmul, smul_smul,]
      ring_nf
    rw [Rat.mul_num_den']

theorem zsmul_mk (a : ℤ) (m : M) (s : nonZeroDivisors ℕ) : a • mk m s = mk (a • m) s := by
  suffices (a : ℚ) • mk m s = mk (a • m) s by simpa [Int.cast_smul_eq_zsmul] using this
  rw [qsmul_mk]
  exact congrArg _ <| Subtype.eq (by simp)

variable {M : Type*} [AddCommMonoid M] [LinearOrder M] [AddLeftStrictMono M]

private theorem lift_aux (m n m' n' : M) (s t s' t' : nonZeroDivisors ℕ)
    (h : mk m s = mk m' s') (h' : mk n t = mk n' t') :
    (fun m s n t ↦ t • m ≤ s • n) m s n t = (fun m s n t ↦ t • m ≤ s • n) m' s' n' t' := by
  rw [mk_eq_mk_iff_smul_eq_smul] at h h'
  suffices t • m ≤ s • n ↔ t' • m' ≤ s' • n' by simpa
  simp_rw [Submonoid.smul_def] at ⊢ h h'
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
  le x y := liftOn₂ x y (fun m s n t ↦ t • m ≤ s • n) lift_aux

theorem mk_le_mk {m m' : M} {s s' : nonZeroDivisors ℕ} :
    mk m s ≤ mk m' s' ↔ s' • m ≤ s • m' := by rfl

instance : LinearOrder (DivisibleHull M) where
  le_refl a := by
    induction a using ind with | mk m s
    rw [mk_le_mk]
  le_trans a b c hab hbc := by
    induction a using ind with | mk ma sa
    induction b using ind with | mk mb sb
    induction c using ind with | mk mc sc
    rw [mk_le_mk, Submonoid.smul_def] at ⊢ hab hbc
    rw [← (nsmul_right_strictMono (show sb.val ≠ 0 by simp)).le_iff_le]
    rw [← (nsmul_right_strictMono (show sc.val ≠ 0 by simp)).le_iff_le] at hab
    rw [← (nsmul_right_strictMono (show sa.val ≠ 0 by simp)).le_iff_le] at hbc
    rw [smul_comm _ _ ma, smul_comm _ _ mc]
    rw [smul_comm _ _ mb] at hab
    exact hab.trans hbc
  le_antisymm a b h h' := by
    induction a using ind with | mk ma sa
    induction b using ind with | mk mb sb
    rw [mk_le_mk] at h h'
    rw [mk_eq_mk_iff_smul_eq_smul]
    exact le_antisymm h h'
  le_total a b := by
    induction a using ind with | mk ma sa
    induction b using ind with | mk mb sb
    exact le_total _ _
  toDecidableLE := decidable_liftOn₂ _ _

theorem mk_lt_mk {m m' : M} {s s' : nonZeroDivisors ℕ} : mk m s < mk m' s' ↔ s' • m < s • m' := by
  simp_rw [lt_iff_not_ge, mk_le_mk]

theorem add_lt_add_left (a : DivisibleHull M) {b c : DivisibleHull M} (h : b < c) :
    a + b < a + c := by
  induction a using ind with | mk ma sa
  induction b using ind with | mk mb sb
  induction c using ind with | mk mc sc
  simp_rw [mk_add_mk]
  rw [mk_lt_mk] at ⊢ h
  simp_rw [mul_smul]
  simp_rw [Submonoid.smul_def] at ⊢ h
  simp_rw [smul_add, smul_smul]
  suffices (sa * sb * sc : ℕ) • ma + (sa * sa : ℕ) • (sc : ℕ) • mb
      < (sa * sb * sc : ℕ) • ma + (sa * sa : ℕ) • (sb : ℕ) • mc by
    simp_rw [smul_smul] at this
    convert this using 3 <;> ring
  apply _root_.add_lt_add_left <| nsmul_lt_nsmul_right (by simp) h

instance : IsOrderedCancelAddMonoid (DivisibleHull M) where
  add_le_add_left a b h c := by
    obtain rfl | h := eq_or_lt_of_le h
    · simp
    exact (add_lt_add_left c h).le
  le_of_add_le_add_left a b c h := by
    contrapose! h
    exact add_lt_add_left a h

instance : PosSMulStrictMono ℚ≥0 (DivisibleHull M) where
  smul_lt_smul_of_pos_left a ha b c h := by
    induction b using ind with | mk mb sb
    induction c using ind with | mk mc sc
    simp_rw [mk_lt_mk, Submonoid.smul_def] at h
    simp_rw [nnqsmul_mk, mk_lt_mk, Submonoid.smul_def, Submonoid.mul_def, smul_smul]
    simp_rw [mul_right_comm _ _ a.num, mul_smul _ _ mc, mul_smul _ _ mb]
    refine (nsmul_right_strictMono ?_).lt_iff_lt.mpr h
    simpa using ha.ne.symm

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

instance : PosSMulStrictMono ℚ (DivisibleHull M) where
  smul_lt_smul_of_pos_left a ha b c h := by
    simpa only [qsmul_def, ha.le, ↓reduceDIte] using smul_lt_smul_of_pos_left h (by simpa using ha)

variable (M) in
/-- The map `m ↦ m / 1` as an `OrderAddMonoidHom`. -/
@[simps]
def mkOrderAddMonoidHom : M →+o DivisibleHull M where
  toFun a := mk a 1
  map_add' a b := by simp [mk_add_mk]
  map_zero' := by simp [mk]
  monotone' a b h := by simpa [mk_le_mk] using h

theorem mkOrderAddMonoidHom_injective : Function.Injective (mkOrderAddMonoidHom M) := by
  intro a b
  simp [mk_eq_mk_iff_smul_eq_smul]

variable (M) in
private noncomputable
def aux_archimedeanClassOrderHom : ArchimedeanClass M →o ArchimedeanClass (DivisibleHull M) :=
  ArchimedeanClass.orderHom (mkOrderAddMonoidHom M)

private theorem aux_archimedeanClassMk_mk (m : M) (s : nonZeroDivisors ℕ) :
    ArchimedeanClass.mk (mk m s) = aux_archimedeanClassOrderHom M (ArchimedeanClass.mk m) := by
  trans ArchimedeanClass.mk ((s.val : ℤ) • mk m s)
  · rw [ArchimedeanClass.mk_smul _ (show (s.val : ℤ) ≠ 0 by simp)]
  rw [aux_archimedeanClassOrderHom, ArchimedeanClass.orderHom_mk, mkOrderAddMonoidHom_apply,
    zsmul_mk]
  apply congrArg
  simp [mk_eq_mk_iff_smul_eq_smul, Submonoid.smul_def]

private theorem aux_archimedeanClassOrderHom_injective :
    Function.Injective (aux_archimedeanClassOrderHom M) :=
  ArchimedeanClass.orderHom_injective mkOrderAddMonoidHom_injective

variable (M) in
private noncomputable
def aux_archimedeanClassOrderHomInv :
    ArchimedeanClass (DivisibleHull M) →o ArchimedeanClass M :=
  ArchimedeanClass.liftOrderHom (fun x ↦ x.liftOn (fun m s ↦ ArchimedeanClass.mk m)
    (fun _ _ _ _ h ↦ by
      apply aux_archimedeanClassOrderHom_injective
      apply_fun ArchimedeanClass.mk at h
      simpa [aux_archimedeanClassMk_mk] using h))
    (fun a b h ↦ by
      induction a using ind with | mk _ _
      induction b using ind with | mk _ _
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
    induction a using ind with | mk m s
    suffices ArchimedeanClass.mk (mk m 1) = ArchimedeanClass.mk (mk m s) by
      simpa [aux_archimedeanClassOrderHom, aux_archimedeanClassOrderHomInv]
    simp_rw [aux_archimedeanClassMk_mk]
  · ext a
    induction a using ArchimedeanClass.ind with | mk _
    simp [aux_archimedeanClassOrderHom, aux_archimedeanClassOrderHomInv]

@[simp]
theorem archimedeanClassOrderIso_apply (a : ArchimedeanClass M) :
    archimedeanClassOrderIso M a = ArchimedeanClass.orderHom (mkOrderAddMonoidHom M) a := rfl

@[simp]
theorem archimedeanClassOrderIso_symm_apply (m : M) (s : nonZeroDivisors ℕ) :
    (archimedeanClassOrderIso M).symm (ArchimedeanClass.mk (mk m s)) = ArchimedeanClass.mk m := rfl


end DivisibleHull
end DivisibleHull2
