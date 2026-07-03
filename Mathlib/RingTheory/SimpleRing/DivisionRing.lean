/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.RingTheory.SimpleModule.Basic

/-!

## Simple modules over division rings
This file contains some results about simple modules over division rings.

# Main results

* `DivisionRing.nonempty_linearEquiv_of_isSimpleModule` : There is an unique simple module over
  a division ring, up to isomorphism.
* `isSimpleModule_iff_eq_zero_or_injective` : A module is simple if and only if it is nontrivial
  and every linear map from it is either zero or injective, this is the module analogue of
  `RingHom.injective`
* `IsSimpleModule.obj_of_isEquivalence` : If `M` is a simple module over a ring `R`, and
  `e : ModuleCat R ⥤ ModuleCat S` is an equivalence of categories,
  then `e(M)` is a simple module over `S`.

## Tags
Noncommutative algebra, simple module, division ring

-/

@[expose] public section

universe u v

open CategoryTheory

variable (R S : Type*) [DivisionRing R] [DivisionRing S] (e : ModuleCat R ≌ ModuleCat S)

lemma DivisionRing.nonempty_linearEquiv_of_isSimpleModule (N : Type*) [AddCommGroup N]
    [Module S N] [IsSimpleModule S N] : Nonempty (N ≃ₗ[S] S) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹_›
  exact ⟨e ≪≫ₗ I.quotEquivOfEqBot ((eq_bot_or_eq_top I).resolve_right hI.ne_top)⟩

lemma isSimpleModule_iff_eq_zero_or_injective (R : Type u) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] : IsSimpleModule R M ↔ (Nontrivial M ∧ ∀ (N : Type v) [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N), f = 0 ∨ Function.Injective f) :=
  ⟨fun hM ↦ ⟨Submodule.nontrivial_iff _|>.1 hM.1.1, fun N _ _ f ↦ hM.1.2 (LinearMap.ker f)|>.elim
    (fun h ↦ Or.inr <| by rwa [LinearMap.ker_eq_bot] at h) (fun h ↦ Or.inl <|by simp_all)⟩,
  fun ⟨hM1, hM2⟩ ↦ isSimpleModule_iff R M|>.2 ⟨fun p ↦ (hM2 (M ⧸ p) p.mkQ).elim
  (fun h ↦ Or.inr <| by simpa [Submodule.ext_iff, LinearMap.ext_iff] using h)
  (fun h ↦ Or.inl <| eq_bot_iff.2 fun x hx ↦ h (by simp [hx]))⟩⟩

lemma IsSimpleModule.obj_of_isEquivalence
    {R S : Type*} [Ring R] [Ring S] (e : ModuleCat R ⥤ ModuleCat S)
    [e.IsEquivalence] (M : ModuleCat R) [IsSimpleModule R M] :
    IsSimpleModule S (e.obj M) := by
  rw [← simple_iff_isSimpleModule'] at *
  exact simple_obj e M
