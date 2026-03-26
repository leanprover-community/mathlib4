/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Maps
public import Mathlib.RingTheory.OreLocalization.Basic

/-!
# Localizations of commutative monoids with zeroes

-/

@[expose] public section

open Function

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M] (S : Submonoid M) (N : Type*) [CommMonoidWithZero N]
  {P : Type*} [CommMonoidWithZero P]

namespace Submonoid

variable {S N}

/-- If `S` contains `0` then the localization at `S` is trivial. -/
theorem LocalizationMap.subsingleton (f : LocalizationMap S N) (h : 0 ∈ S) : Subsingleton N where
  allEq a b := by
    rw [← f.mk'_sec a, ← f.mk'_sec b, f.eq]
    exact ⟨⟨0, h⟩, by simp only [zero_mul]⟩

theorem LocalizationMap.subsingleton_iff (f : LocalizationMap S N) : Subsingleton N ↔ 0 ∈ S :=
  ⟨fun _ ↦ have ⟨c, eq⟩ := f.exists_of_eq (Subsingleton.elim (f 0) (f 1))
    by rw [mul_zero, mul_one] at eq; exact eq ▸ c.2, f.subsingleton⟩

theorem LocalizationMap.nontrivial (f : LocalizationMap S N) (h : 0 ∉ S) : Nontrivial N := by
  rwa [← not_subsingleton_iff_nontrivial, f.subsingleton_iff]

protected theorem LocalizationMap.map_zero (f : LocalizationMap S N) : f 0 = 0 := by
  have ⟨ms, eq⟩ := f.surj 0
  rw [← zero_mul, map_mul, ← eq, zero_mul, mul_zero]

protected theorem IsLocalizationMap.map_zero {F} [FunLike F M N] [MulHomClass F M N] {f : F}
    (hf : IsLocalizationMap S f) : f 0 = 0 :=
  LocalizationMap.map_zero ⟨MulHomClass.toMulHom f, hf⟩

instance : MonoidWithZeroHomClass (LocalizationMap S N) M N where
  map_zero f := by
    have ⟨ms, eq⟩ := f.surj 0
    rw [← zero_mul, map_mul, ← eq, zero_mul, mul_zero]

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
      exact (map_zero f).symm }

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
  rwa [h, map_zero, (f.map_units _).mul_left_eq_zero] at eq

theorem map_eq_zero_iff (f : LocalizationMap S N) {m : M} : f m = 0 ↔ ∃ s : S, s * m = 0 := by
  simp_rw [← f.map_zero, eq_iff_exists, mul_zero]

theorem mk'_eq_zero_iff (f : LocalizationMap S N) (m : M) (s : S) :
    f.mk' m s = 0 ↔ ∃ s : S, s * m = 0 := by
  rw [← (f.map_units s).mul_left_inj, mk'_spec, zero_mul, map_eq_zero_iff]

@[simp] theorem mk'_zero (f : LocalizationMap S N) (s : S) : f.mk' 0 s = 0 := by
  rw [eq_comm, eq_mk'_iff_mul_eq, zero_mul, f.map_zero]

theorem associated_mk' (f : LocalizationMap S N) (x : M) (y : S) :
    Associated (f x) (f.mk' x y) := by
  rw [← f.mk'_spec' x y]
  exact associated_unit_mul_left _ _ (f.map_units y)

theorem map_isUnit_iff (f : LocalizationMap S N) (x : M) :
    IsUnit (f x) ↔ ∃ y : S, x ∣ (y : M) := by
  refine ⟨fun h ↦ ?_, fun ⟨y, hxy⟩ ↦ isUnit_of_dvd_unit (map_dvd f.toMonoidHom hxy) (f.map_units y)⟩
  let ⟨z, hz⟩ := isUnit_iff_dvd_one.mp h
  let ⟨⟨r, s⟩, hrs⟩ := f.surj z
  have hmap : f s = f (x * r) := by grind
  let ⟨t, ht⟩ := f.eq_iff_exists.mp hmap
  exact ⟨t * s, ⟨t * r, show (t : S) * (s : S) = x * (t * r) by grind⟩⟩

theorem not_dvd_submonoid_of_not_isUnit (f : LocalizationMap S N) {x : M}
    (hxu : ¬ IsUnit (f x)) (y : S) : ¬ x ∣ (y : M) :=
  fun hxy ↦ hxu <| (f.map_isUnit_iff x).2 ⟨y, hxy⟩

theorem map_dvd_mk'_iff_of_prime (f : LocalizationMap S N) {p x : M} (s : S) (hp : Prime p)
    (hpu : ¬ IsUnit (f p)) : f p ∣ f.mk' x s ↔ p ∣ x := by
  constructor
  · rintro ⟨c, hc⟩
    let ⟨⟨r, t⟩, ht⟩ := f.surj c
    have hmk := calc
      f.mk' x s = f p * c := hc
      _ = f p * f.mk' r t := by simp [(f.eq_mk'_iff_mul_eq).2 ht]
      _ = f.mk' (p * r) t := by rw [f.mul_mk'_eq_mk'_of_mul]
    have hmap : f (t * x) = f (s * (p * r)) := (f.mk'_eq_iff_eq).mp hmk
    let ⟨u, hu⟩ := f.eq_iff_exists.mp hmap
    have hdiv : p ∣ u * (t * x) := ⟨u * (s * r), by grind⟩
    exact (hp.dvd_or_dvd <| (hp.dvd_or_dvd hdiv).resolve_left <|
      f.not_dvd_submonoid_of_not_isUnit hpu u).resolve_left <|
        f.not_dvd_submonoid_of_not_isUnit hpu t
  · rintro ⟨r, rfl⟩
    exact ⟨f.mk' r s, by rw [f.mul_mk'_eq_mk'_of_mul]⟩

theorem map_dvd_map_iff_of_prime (f : LocalizationMap S N) {p q : M} (hp : Prime p)
    (hpu : ¬ IsUnit (f p)) : f p ∣ f q ↔ p ∣ q := by
  simpa [f.mk'_one] using f.map_dvd_mk'_iff_of_prime 1 hp hpu

theorem map_prime_of_ne_zero (f : LocalizationMap S N) {p : M} (hp : Prime p)
    (hp0 : f p ≠ 0) (hpu : ¬ IsUnit (f p)) : Prime (f p) := by
  refine ⟨hp0, hpu, ?_⟩
  intro a b hab
  obtain ⟨a', s, rfl⟩ := f.mk'_surjective a
  obtain ⟨b', t, rfl⟩ := f.mk'_surjective b
  have hdiv : p ∣ a' * b' := by
    have hmk : f p ∣ f.mk' (a' * b') (s * t) := by
      simpa [f.mk'_mul] using hab
    exact (f.map_dvd_mk'_iff_of_prime (s * t) hp hpu).mp hmk
  rcases hp.dvd_or_dvd hdiv with hdiv | hdiv
  · left
    exact (f.associated_mk' a' s).dvd_iff_dvd_right.mp (map_dvd f.toMonoidHom hdiv)
  · right
    exact (f.associated_mk' b' t).dvd_iff_dvd_right.mp (map_dvd f.toMonoidHom hdiv)

theorem nonZeroDivisors_le_comap (f : LocalizationMap S N) :
    nonZeroDivisors M ≤ (nonZeroDivisors N).comap f := by
  refine fun m hm ↦ nonZeroDivisorsRight_eq_nonZeroDivisors (M₀ := N) ▸ fun n h0 ↦ ?_
  have ⟨ms, eq⟩ := f.surj n
  rw [← (f.map_units ms.2).mul_left_eq_zero, mul_right_comm, eq, ← map_mul, map_eq_zero_iff] at h0
  simp_rw [← mul_assoc, mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hm.2] at h0
  rwa [← (f.map_units ms.2).mul_left_eq_zero, eq, map_eq_zero_iff]

theorem map_nonZeroDivisors_le (f : LocalizationMap S N) :
    (nonZeroDivisors M).map f ≤ nonZeroDivisors N :=
  map_le_iff_le_comap.mpr f.nonZeroDivisors_le_comap

theorem noZeroDivisors (f : LocalizationMap S N) [NoZeroDivisors M] : NoZeroDivisors N := by
  refine noZeroDivisors_iff_forall_mem_nonZeroDivisors.mpr fun n hn ↦ ?_
  have ⟨ms, eq⟩ := f.surj n
  have hs : ms.1 ≠ 0 := fun h ↦ hn (by rwa [h, f.map_zero, (f.map_units _).mul_left_eq_zero] at eq)
  exact And.left <| mul_mem_nonZeroDivisors.mp
    (eq ▸ f.map_nonZeroDivisors_le ⟨_, mem_nonZeroDivisors_of_ne_zero hs, rfl⟩)

end LocalizationMap

end Submonoid

end CommMonoidWithZero
