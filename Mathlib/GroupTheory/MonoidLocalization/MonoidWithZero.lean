/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.RingTheory.OreLocalization.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Localizations of commutative monoids with zeroes

-/

open Function

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M] (S : Submonoid M) (N : Type*) [CommMonoidWithZero N]
  {P : Type*} [CommMonoidWithZero P]

namespace Submonoid

variable {S N} in
/-- If `S` contains `0` then the localization at `S` is trivial. -/
theorem LocalizationMap.subsingleton (f : LocalizationMap S N) (h : 0 ∈ S) :
    Subsingleton N := by
  refine ⟨fun a b ↦ ?_⟩
  rw [← LocalizationMap.mk'_sec f a, ← LocalizationMap.mk'_sec f b, LocalizationMap.eq]
  exact ⟨⟨0, h⟩, by simp only [zero_mul]⟩

protected theorem LocalizationMap.map_zero (f : LocalizationMap S N) : f 0 = 0 := by
  have ⟨ms, eq⟩ := f.surj 0
  rw [← zero_mul, map_mul, ← eq, zero_mul, mul_zero]

variable {S N}

/-- The monoid with zero hom underlying a `LocalizationMap`. -/
def LocalizationMap.toMonoidWithZeroHom (f : LocalizationMap S N) : M →*₀ N :=
  { f with map_zero' := f.map_zero }

@[deprecated (since := "2025-08-01")] alias LocalizationWithZeroMap := LocalizationMap
@[deprecated (since := "2025-08-01")]
alias LocalizationWithZeroMap.toMonoidWithZeroHom := LocalizationMap.toMonoidWithZeroHom

end Submonoid

namespace Localization

variable {S}

theorem mk_zero (x : S) : mk 0 (x : S) = 0 := OreLocalization.zero_oreDiv' _

instance : CommMonoidWithZero (Localization S) where
  zero_mul := fun x ↦ Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, zero_mul, r_of_eq]
  mul_zero := fun x ↦ Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, r_of_eq]

theorem liftOn_zero {p : Type*} (f : M → S → p) (H) : liftOn 0 f H = f 0 1 := by
  rw [← mk_zero 1, liftOn_mk]

end Localization

variable {S N}

namespace Submonoid

@[simp]
theorem LocalizationMap.sec_zero_fst {f : LocalizationMap S N} : f (f.sec 0).fst = 0 := by
  rw [LocalizationMap.sec_spec', mul_zero]

namespace LocalizationMap

/-- Given a Localization map `f : M →*₀ N` for a Submonoid `S ⊆ M` and a map of
`CommMonoidWithZero`s `g : M →*₀ P` such that `g y` is invertible for all `y : S`, the
homomorphism induced from `N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `(x, y) : M × S`
are such that `z = f x * (f y)⁻¹`. -/
noncomputable def lift₀ (f : LocalizationMap S N) (g : M →*₀ P)
    (hg : ∀ y : S, IsUnit (g y)) : N →*₀ P :=
  { @LocalizationMap.lift _ _ _ _ _ _ _ f g.toMonoidHom hg with
    map_zero' := by
      dsimp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      rw [LocalizationMap.lift_spec f hg 0 0, mul_zero, ← map_zero g, ← g.toMonoidHom_coe]
      refine f.eq_of_eq hg ?_
      rw [LocalizationMap.sec_zero_fst]
      exact f.toMonoidWithZeroHom.map_zero.symm }

lemma lift₀_def (f : LocalizationMap S N) (g : M →*₀ P) (hg : ∀ y : S, IsUnit (g y)) :
    ⇑(f.lift₀ g hg) = f.lift (g := g) hg := rfl

lemma lift₀_apply (f : LocalizationMap S N) (g : M →*₀ P) (hg : ∀ y : S, IsUnit (g y)) (x) :
    f.lift₀ g hg x = g (f.sec x).1 * (IsUnit.liftRight (g.restrict S) hg (f.sec x).2)⁻¹ := rfl

/-- Given a Localization map `f : M →*₀ N` for a Submonoid `S ⊆ M`,
if `M` is a cancellative monoid with zero, and all elements of `S` are
regular, then N is a cancellative monoid with zero. -/
theorem isCancelMulZero (f : LocalizationMap S N) [IsCancelMulZero M] : IsCancelMulZero N := by
  simp_rw [isCancelMulZero_iff_forall_isRegular, Commute.isRegular_iff (Commute.all _),
    ← Commute.isRightRegular_iff (Commute.all _)]
  intro n hn
  have ⟨ms, eq⟩ := f.surj n
  refine (eq ▸ f.map_isRegular (isCancelMulZero_iff_forall_isRegular.mp ‹_› ?_)).2.of_mul
  refine fun h ↦ hn ?_
  rwa [h, f.map_zero, (f.map_units _).mul_left_eq_zero] at eq

end LocalizationMap

namespace LocalizationWithZeroMap

@[deprecated (since := "2025-08-01")]
alias isLeftRegular_of_le_isCancelMulZero := LocalizationMap.isCancelMulZero
@[deprecated (since := "2025-08-01")]
alias leftCancelMulZero_of_le_isLeftRegular := LocalizationMap.isCancelMulZero
@[deprecated (since := "2025-08-01")] alias lift := LocalizationMap.lift₀
@[deprecated (since := "2025-08-01")] alias lift_def := LocalizationMap.lift₀_def
@[deprecated (since := "2025-08-01")] alias lift_apply := LocalizationMap.lift₀_apply

end LocalizationWithZeroMap

end Submonoid

end CommMonoidWithZero
