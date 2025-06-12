/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Regular.Basic
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.RingTheory.OreLocalization.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Localizations of commutative monoids with zeroes

-/

open Function

namespace Submonoid.LocalizationMap

@[to_additive]
theorem toMap_injective_iff
    {M N : Type*} [CommMonoid M] {S : Submonoid M} [CommMonoid N] (f : LocalizationMap S N) :
    Injective (LocalizationMap.toMap f) ↔ ∀ ⦃x⦄, x ∈ S → IsLeftRegular x := by
  rw [Injective]
  constructor <;> intro h
  · intro x hx y z hyz
    simp_rw [LocalizationMap.eq_iff_exists] at h
    apply (fun y z _ => h) y z x
    lift x to S using hx
    use x
  · intro a b hab
    rw [LocalizationMap.eq_iff_exists] at hab
    obtain ⟨c,hc⟩ := hab
    apply (fun x a => h a) c (SetLike.coe_mem c) hc

end Submonoid.LocalizationMap

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M] (S : Submonoid M) (N : Type*) [CommMonoidWithZero N]
  {P : Type*} [CommMonoidWithZero P]

namespace Submonoid

variable {S N} in
/-- If `S` contains `0` then the localization at `S` is trivial. -/
theorem LocalizationMap.subsingleton (f : Submonoid.LocalizationMap S N) (h : 0 ∈ S) :
    Subsingleton N := by
  refine ⟨fun a b ↦ ?_⟩
  rw [← LocalizationMap.mk'_sec f a, ← LocalizationMap.mk'_sec f b, LocalizationMap.eq]
  exact ⟨⟨0, h⟩, by simp only [zero_mul]⟩

/-- The type of homomorphisms between monoids with zero satisfying the characteristic predicate:
if `f : M →*₀ N` satisfies this predicate, then `N` is isomorphic to the localization of `M` at
`S`. -/
structure LocalizationWithZeroMap extends LocalizationMap S N where
  map_zero' : toFun 0 = 0

variable {S N}

/-- The monoid with zero hom underlying a `LocalizationMap`. -/
def LocalizationWithZeroMap.toMonoidWithZeroHom (f : LocalizationWithZeroMap S N) : M →*₀ N :=
  { f with }

end Submonoid

namespace Localization

variable {S}

theorem mk_zero (x : S) : mk 0 (x : S) = 0 := OreLocalization.zero_oreDiv' _

instance : CommMonoidWithZero (Localization S) where
  zero_mul := fun x ↦ Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, zero_mul, r_of_eq]
  mul_zero := fun x ↦ Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, zero_mul, r_of_eq]

theorem liftOn_zero {p : Type*} (f : M → S → p) (H) : liftOn 0 f H = f 0 1 := by
  rw [← mk_zero 1, liftOn_mk]

end Localization

variable {S N}

namespace Submonoid

@[simp]
theorem LocalizationMap.sec_zero_fst {f : LocalizationMap S N} : f.toMap (f.sec 0).fst = 0 := by
  rw [LocalizationMap.sec_spec', mul_zero]

namespace LocalizationWithZeroMap

/-- Given a Localization map `f : M →*₀ N` for a Submonoid `S ⊆ M` and a map of
`CommMonoidWithZero`s `g : M →*₀ P` such that `g y` is invertible for all `y : S`, the
homomorphism induced from `N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `(x, y) : M × S`
are such that `z = f x * (f y)⁻¹`. -/
noncomputable def lift (f : LocalizationWithZeroMap S N) (g : M →*₀ P)
    (hg : ∀ y : S, IsUnit (g y)) : N →*₀ P :=
  { @LocalizationMap.lift _ _ _ _ _ _ _ f.toLocalizationMap g.toMonoidHom hg with
    map_zero' := by
      dsimp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      rw [LocalizationMap.lift_spec f.toLocalizationMap hg 0 0, mul_zero, ← map_zero g,
        ← g.toMonoidHom_coe]
      refine f.toLocalizationMap.eq_of_eq hg ?_
      rw [LocalizationMap.sec_zero_fst]
      exact f.toMonoidWithZeroHom.map_zero.symm }

lemma lift_def (f : LocalizationWithZeroMap S N) (g : M →*₀ P) (hg : ∀ y : S, IsUnit (g y)) :
    ⇑(f.lift g hg) = f.toLocalizationMap.lift (g := ↑g) hg := rfl

lemma lift_apply (f : LocalizationWithZeroMap S N) (g : M →*₀ P) (hg : ∀ y : S, IsUnit (g y)) (x) :
    (f.lift g hg) x = g (f.sec x).1 * (IsUnit.liftRight (g.restrict S) hg (f.sec x).2)⁻¹ := rfl

/-- Given a Localization map `f : M →*₀ N` for a Submonoid `S ⊆ M`,
if `M` is left cancellative monoid with zero, and all elements of `S` are
left regular, then N is a left cancellative monoid with zero. -/
theorem leftCancelMulZero_of_le_isLeftRegular
    (f : LocalizationWithZeroMap S N) [IsLeftCancelMulZero M]
    (h : ∀ ⦃x⦄, x ∈ S → IsLeftRegular x) : IsLeftCancelMulZero N := by
  let fl := f.toLocalizationMap
  let g := f.toMap
  constructor
  intro a z w ha hazw
  obtain ⟨b, hb⟩ := LocalizationMap.surj fl a
  obtain ⟨x, hx⟩ := LocalizationMap.surj fl z
  obtain ⟨y, hy⟩ := LocalizationMap.surj fl w
  rw [(LocalizationMap.eq_mk'_iff_mul_eq fl).mpr hx,
    (LocalizationMap.eq_mk'_iff_mul_eq fl).mpr hy, LocalizationMap.eq]
  use 1
  rw [OneMemClass.coe_one, one_mul, one_mul]
  -- The hypothesis `a ≠ 0` in `P` is equivalent to this
  have b1ne0 : b.1 ≠ 0 := by
    intro hb1
    have m0 : (LocalizationMap.toMap fl) 0 = 0 := f.map_zero'
    have a0 : a * (LocalizationMap.toMap fl) b.2 = 0 ↔ a = 0 :=
      (f.toLocalizationMap.map_units' b.2).mul_left_eq_zero
    rw [hb1, m0, a0] at hb
    exact ha hb
  have main : g (b.1 * (x.2 * y.1)) = g (b.1 * (y.2 * x.1)) :=
    calc
      g (b.1 * (x.2 * y.1)) = g b.1 * (g x.2 * g y.1) := by rw [map_mul g,map_mul g]
      _ = a * g b.2 * (g x.2 * (w * g y.2)) := by rw [hb, hy]
      _ = a * w * g b.2 * (g x.2 * g y.2) := by
        rw [← mul_assoc, ← mul_assoc _ w, mul_comm _ w, mul_assoc w, mul_assoc,
          ← mul_assoc w, ← mul_assoc w, mul_comm w]
      _ = a * z * g b.2 * (g x.2 * g y.2) := by rw [hazw]
      _ = a * g b.2 * (z * g x.2 * g y.2) := by
        rw [mul_assoc a, mul_comm z, ← mul_assoc a, mul_assoc, mul_assoc z]
      _ = g b.1 * g (y.2 * x.1) := by rw [hx, hb, mul_comm (g x.1), ← map_mul g]
      _ = g (b.1 * (y.2 * x.1)) := by rw [← map_mul g]
  -- The hypothesis `h` gives that `f` (so, `g`) is injective, and we can cancel out `b.1`.
  exact (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero b1ne0
      ((LocalizationMap.toMap_injective_iff fl).mpr h main)).symm

/-- Given a Localization map `f : M →*₀ N` for a Submonoid `S ⊆ M`,
if `M` is a cancellative monoid with zero, and all elements of `S` are
regular, then N is a cancellative monoid with zero. -/
theorem isLeftRegular_of_le_isCancelMulZero (f : LocalizationWithZeroMap S N)
    [IsCancelMulZero M] (h : ∀ ⦃x⦄, x ∈ S → IsRegular x) : IsCancelMulZero N := by
  have : IsLeftCancelMulZero N :=
    leftCancelMulZero_of_le_isLeftRegular f (fun x h' => (h h').left)
  exact IsLeftCancelMulZero.to_isCancelMulZero

end LocalizationWithZeroMap

end Submonoid

end CommMonoidWithZero
