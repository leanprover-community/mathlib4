/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Data.Fintype.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Lemmas about localizations of commutative monoids

that requires additional imports.
-/

public section

namespace Submonoid.IsLocalizationMap

open Finset in
/-- See also the analogous `IsLocalization.map_integerMultiple`. -/
@[to_additive] theorem surj_pi_of_finite {M N F ι : Type*} [Finite ι]
    [CommMonoid M] [CommMonoid N] [FunLike F M N] [MulHomClass F M N] {f : F}
    {S : Submonoid M} (hf : IsLocalizationMap S f) (n : ι → N) :
    ∃ (s : S) (x : ι → M), ∀ i, n i * f s = f (x i) := by
  choose x hx using hf.surj
  have ⟨_⟩ := nonempty_fintype ι
  classical
  refine ⟨∏ i : ι, (x (n i)).2, fun i ↦ (x (n i)).1 * ∏ j ∈ univ.erase i, (x (n j)).2, fun i ↦ ?_⟩
  rw [← univ.mul_prod_erase _ (mem_univ i), S.coe_mul, map_mul, ← mul_assoc, hx, map_mul]

@[to_additive] protected theorem pi {ι : Type*} {M N : ι → Type*}
    [∀ i, CommMonoid (M i)] [∀ i, CommMonoid (N i)] (S : Π i, Submonoid (M i))
    {f : Π i, M i → N i} (hf : ∀ i, IsLocalizationMap (S i) (f i)) :
    IsLocalizationMap (Submonoid.pi .univ S) (Pi.map f) where
  map_units m := Pi.isUnit_iff.mpr fun i ↦ (hf i).map_units ⟨_, m.2 i ⟨⟩⟩
  surj z := by
    choose x hx using fun i ↦ (hf i).surj
    exact ⟨⟨fun i ↦ (x i (z i)).1, ⟨_, fun i _ ↦ (x i (z i)).2.2⟩⟩, funext fun i ↦ hx i (z i)⟩
  exists_of_eq {x y} eq := by
    choose c hc using fun i ↦ (hf i).exists_of_eq congr($eq i)
    exact ⟨⟨_, fun i _ ↦ (c i).2⟩, funext hc⟩

end Submonoid.IsLocalizationMap
