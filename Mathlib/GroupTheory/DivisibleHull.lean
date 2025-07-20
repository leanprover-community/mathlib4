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

This file constructs the divisible hull of an abelian group as a ℤ-module localized at
`Submonoid.pos ℤ`. Further more, when the source group is linearly ordered, we show that
`DivisibleHull` is a linearly ordered ℚ-module and that `ArchimedeanClass` are preserved.

## Main declarations

* `DivisibleHull M` is the divisible hull of an abelian group.
* `DivisibleHull.archimedeanClassOrderIso M` is the equivalence between `ArchimedeanClass M` and
  `ArchimedeanClass (DivisibleHul M)`.

## Implementation notes

This could be equivalently implemented as localization at `nonZeroDivisors ℤ`, but it would
complicate the linear order implementation.
-/

variable (M : Type*) [AddCommGroup M]

/-- The divisible hull of a Abelian group (as a ℤ-module) is the localized module by
`Submonoid.pos ℤ`, thus a ℕ-divisble group, or a ℚ-module. -/
abbrev DivisibleHull := LocalizedModule (Submonoid.pos ℤ) M

namespace DivisibleHull
variable {M}

/-- Create an element `m / s`. -/
def mk (m : M) (s : Submonoid.pos ℤ) : DivisibleHull M := LocalizedModule.mk m s

theorem ind {motive : DivisibleHull M → Prop} (mk : ∀ num den, motive (.mk num den)) :
    ∀ x, motive x := by
  apply LocalizedModule.induction_on
  intro a
  apply mk

theorem mk_eq_mk {m m' : M} {s s' : Submonoid.pos ℤ} :
    mk m s = mk m' s' ↔ ∃ u : Submonoid.pos ℤ, u • s' • m = u • s • m' := by
  unfold mk
  exact LocalizedModule.mk_eq

/-- If `f : M → Submonoid.pos ℤ → α` respects the equivalence on localization,
lift it to a function `DivisibleHull M → α`. -/
def liftOn {α : Type*} (x : DivisibleHull M)
    (f : M → Submonoid.pos ℤ → α)
    (h : ∀ (m m' : M) (s s' : Submonoid.pos ℤ), mk m s = mk m' s' → f m s = f m' s') : α :=
  LocalizedModule.liftOn x (Function.uncurry f) fun p p' heq ↦
    h p.1 p'.1 p.2 p'.2 (mk_eq_mk.mpr heq)

@[simp]
theorem liftOn_mk {α : Type*} (m : M) (s : Submonoid.pos ℤ)
    (f : M → (Submonoid.pos ℤ) → α)
    (h : ∀ (m m' : M) (s s' : Submonoid.pos ℤ), mk m s = mk m' s' → f m s = f m' s') :
    liftOn (mk m s) f h = f m s := rfl

/-- If `f : M → Submonoid.pos ℤ → M → Submonoid.pos ℤ → α` respects the equivalence on
localization, lift it to a function `DivisibleHull M → DivisibleHull M → α`. -/
def liftOn₂ {α : Type*} (x y : DivisibleHull M)
    (f : M → Submonoid.pos ℤ → M → Submonoid.pos ℤ → α)
    (h : ∀ (m n m' n' : M) (s t s' t' : Submonoid.pos ℤ),
      mk m s = mk m' s' → mk n t = mk n' t' → f m s n t = f m' s' n' t') : α :=
  LocalizedModule.liftOn₂ x y (fun p q ↦ f p.1 p.2 q.1 q.2) fun p q p' q' heq heq' ↦
    h p.1 q.1 p'.1 q'.1 p.2 q.2 p'.2 q'.2 (mk_eq_mk.mpr heq) (mk_eq_mk.mpr heq')

instance decidable_liftOn₂ (f : M → Submonoid.pos ℤ → M → Submonoid.pos ℤ → Prop)
    [(m : M) → (s : Submonoid.pos ℤ) → (n : M) → (t : Submonoid.pos ℤ) → Decidable (f m s n t)]
    (h : ∀ (m n m' n' : M) (s t s' t' : Submonoid.pos ℤ),
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

theorem mk_eq_mk_iff_smul_eq_smul [IsAddTorsionFree M] {m m' : M} {s s' : Submonoid.pos ℤ} :
    mk m s = mk m' s' ↔ s' • m = s • m' := by
  rw [mk_eq_mk]
  constructor
  · intro ⟨u, h⟩
    simp_rw [Submonoid.smul_def] at ⊢ h
    exact (smul_right_inj (ne_of_gt u.prop)).mp h
  · intro hr
    use 1
    rw [hr]

theorem mk_add_mk {m1 m2 : M} {s1 s2 : Submonoid.pos ℤ} :
    mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2) := LocalizedModule.mk_add_mk

theorem qsmul_mk (a : ℚ) (m : M) (s : Submonoid.pos ℤ) :
    a • mk m s = mk (a.num • m) (⟨a.den, Int.natCast_pos.mpr a.den_pos⟩ * s) := by
  convert LocalizedModule.mk'_smul_mk ℚ a.num m ⟨a.den, Int.natCast_pos.mpr a.den_pos⟩ s
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  simp

theorem zsmul_mk (a : ℤ) (m : M) (s : Submonoid.pos ℤ) : a • mk m s = mk (a • m) s := by
  suffices (a : ℚ) • mk m s = mk (a • m) s by simpa [Int.cast_smul_eq_zsmul] using this
  rw [qsmul_mk]
  exact congrArg _ <| Subtype.eq (by simp)

theorem nsmul_mk (a : ℕ) (m : M) (s : Submonoid.pos ℤ) : a • mk m s = mk (a • m) s := by
  suffices (a : ℤ) • mk m s = mk ((a : ℤ) • m) s by simpa using this
  exact zsmul_mk _ _ _

instance : DivisibleBy (DivisibleHull M) ℕ where
  div m n :=
    if h : n = 0 then
      0
    else
      liftOn m (fun m s ↦ mk m ⟨s.val * n,
        Submonoid.mem_pos.mpr <| mul_pos s.prop (by simpa using Nat.pos_of_ne_zero h)⟩)
      (fun m m' s s' ↦ by
        suffices ∀ a : ℤ, 0 < a → a • s' • m = a • s • m' →
          ∃ a : ℤ, 0 < a ∧ a • (s'.val * n) • m = a • (s.val * n) • m' by simpa [mk_eq_mk]
        refine fun a ha h ↦ ⟨a, ha, ?_⟩
        simp_rw [Submonoid.smul_def] at h
        simp_rw [smul_smul, ← mul_assoc, mul_comm _ (n : ℤ), mul_smul, h])
  div_zero := by simp
  div_cancel n {m} h := by
    induction m using ind with | mk m s
    suffices ∃ a : ℤ, 0 < a ∧ a • s • n • m = a • (s.val * n) • m by simpa [h, nsmul_mk, mk_eq_mk]
    use 1
    suffices s • n • m = (s.val * n) • m by simpa
    rw [mul_smul, natCast_zsmul, Submonoid.smul_def]

variable [LinearOrder M] [IsOrderedAddMonoid M]

private theorem lift_aux (m n m' n' : M) (s t s' t' : ↥(Submonoid.pos ℤ))
    (h : mk m s = mk m' s') (h' : mk n t = mk n' t') :
    (fun m s n t ↦ t • m ≤ s • n) m s n t = (fun m s n t ↦ t • m ≤ s • n) m' s' n' t' := by

  rw [mk_eq_mk_iff_smul_eq_smul] at h h'
  suffices t • m ≤ s • n ↔ t' • m' ≤ s' • n' by simpa
  simp_rw [Submonoid.smul_def] at ⊢ h h'
  rw [← zsmul_le_zsmul_iff_right (mul_pos s'.prop t'.prop)]
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
  exact zsmul_le_zsmul_iff_right (mul_pos s.prop t.prop)

instance : LE (DivisibleHull M) where
  le x y := liftOn₂ x y (fun m s n t ↦ t • m ≤ s • n) lift_aux

theorem mk_le_mk {m m' : M} {s s' : Submonoid.pos ℤ} : mk m s ≤ mk m' s' ↔ s' • m ≤ s • m' := by rfl

instance : PartialOrder (DivisibleHull M) where
  le_refl a := by
    induction a using ind with | mk m s
    rw [mk_le_mk]
  le_trans a b c hab hbc := by
    induction a using ind with | mk ma sa
    induction b using ind with | mk mb sb
    induction c using ind with | mk mc sc
    rw [mk_le_mk, Submonoid.smul_def] at ⊢ hab hbc
    rw [← zsmul_le_zsmul_iff_right (show 0 < sb.val from sb.prop)]
    rw [← zsmul_le_zsmul_iff_right (show 0 < sc.val from sc.prop)] at hab
    rw [← zsmul_le_zsmul_iff_right (show 0 < sa.val from sa.prop)] at hbc
    rw [smul_comm _ _ ma, smul_comm _ _ mc]
    rw [smul_comm _ _ mb] at hab
    exact hab.trans hbc
  le_antisymm a b h h' := by
    induction a using ind with | mk ma sa
    induction b using ind with | mk mb sb
    rw [mk_le_mk] at h h'
    rw [mk_eq_mk_iff_smul_eq_smul]
    exact le_antisymm h h'

instance : LinearOrder (DivisibleHull M) where
  le_total a b := by
    induction a using ind with | mk ma sa
    induction b using ind with | mk mb sb
    exact le_total _ _
  toDecidableLE := decidable_liftOn₂ _ _

theorem mk_lt_mk {m m' : M} {s s' : Submonoid.pos ℤ} : mk m s < mk m' s' ↔ s' • m < s • m' := by
  simp_rw [lt_iff_not_ge, mk_le_mk]

instance : IsOrderedAddMonoid (DivisibleHull M) where
  add_le_add_left a b h c := by
    induction a using ind with | mk ma sa
    induction b using ind with | mk mb sb
    induction c using ind with | mk mc sc
    rw [mk_le_mk] at h
    simp_rw [mk_add_mk, mk_le_mk, smul_add, smul_smul]
    rw [mul_right_comm sc sa sb, add_le_add_iff_left]
    rw [mul_right_comm sc sa sc, mul_right_comm sc sb sc]
    rw [mul_smul _ _ ma, mul_smul _ _ mb]
    exact zsmul_le_zsmul_right (le_of_lt (sc * sc).prop) h

instance : PosSMulStrictMono ℚ (DivisibleHull M) where
  smul_lt_smul_of_pos_left a ha b c h := by
    induction b using ind with | mk mb sb
    induction c using ind with | mk mc sc
    simp_rw [mk_lt_mk, Submonoid.smul_def] at h
    simp_rw [qsmul_mk, mk_lt_mk, Submonoid.smul_def, Submonoid.mul_def, smul_smul]
    simp_rw [mul_right_comm _ _ a.num, mul_smul _ _ mc, mul_smul _ _ mb]
    refine (zsmul_lt_zsmul_iff_right ?_).mpr h
    exact mul_pos (Int.natCast_pos.mpr a.den_pos) (Rat.num_pos.mpr ha)

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

private theorem aux_archimedeanClassMk_mk (m : M) (s : Submonoid.pos ℤ) :
    ArchimedeanClass.mk (mk m s) = aux_archimedeanClassOrderHom M (ArchimedeanClass.mk m) := by
  trans ArchimedeanClass.mk (s.val • mk m s)
  · rw [ArchimedeanClass.mk_smul _ (ne_of_gt s.prop)]
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
theorem archimedeanClassOrderIso_symm_apply (m : M) (s : Submonoid.pos ℤ) :
    (archimedeanClassOrderIso M).symm (ArchimedeanClass.mk (mk m s)) = ArchimedeanClass.mk m := rfl


end DivisibleHull
