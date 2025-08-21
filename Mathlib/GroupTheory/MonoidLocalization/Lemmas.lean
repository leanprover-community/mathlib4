/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero

/-!
# Lemmas about localizations of commutative monoids

that requires additional imports.
-/

namespace Submonoid.IsLocalizationMap

open Finset in
@[to_additive] theorem Submonoid.IsLocalizationMap.surj_of_finite {M N F ι : Type*} [Finite ι]
    [CommMonoid M] [CommMonoid N] [FunLike F M N] [MulHomClass F M N] {f : F}
    {S : Submonoid M} (hf : IsLocalizationMap S f) (n : ι → N) :
    ∃ (s : S) (x : ι → M), ∀ i, n i * f s = f (x i) := by
  choose x hx using hf.surj'
  have := Fintype.ofFinite ι
  classical
  refine ⟨∏ i : ι, (x (n i)).2, fun i ↦ (x (n i)).1 * ∏ j ∈ univ.erase i, (x (n j)).2, fun i ↦ ?_⟩
  rw [← univ.mul_prod_erase _ (mem_univ i), S.coe_mul, map_mul, ← mul_assoc, hx, map_mul]

@[to_additive] protected theorem Submonoid.IsLocalizationMap.pi {ι : Type*} {M N : ι → Type*}
    [∀ i, CommMonoid (M i)] [∀ i, CommMonoid (N i)] (S : Π i, Submonoid (M i))
    {f : Π i, M i → N i} (hf : ∀ i, IsLocalizationMap (S i) (f i)) :
    IsLocalizationMap (Submonoid.pi .univ S) (Pi.map f) where
  map_units' m := Pi.isUnit_iff.mpr fun i ↦ (hf i).map_units' ⟨_, m.2 i ⟨⟩⟩
  surj' z := by
    choose x hx using fun i ↦ (hf i).surj'
    exact ⟨⟨fun i ↦ (x i (z i)).1, ⟨_, fun i _ ↦ (x i (z i)).2.2⟩⟩, funext fun i ↦ hx i (z i)⟩
  exists_of_eq {x y} eq := by
    choose c hc using fun i ↦ (hf i).exists_of_eq congr($eq i)
    exact ⟨⟨_, fun i _ ↦ (c i).2⟩, funext hc⟩

end IsLocalizationMap

namespace LocalizationMap

variable {M N : Type*} [CommMonoidWithZero M] {S : Submonoid M} [CommMonoidWithZero N]

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

end Submonoid.LocalizationMap
