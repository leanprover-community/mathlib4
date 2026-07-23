/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.FiniteFreeResolution.Exact
public import Mathlib.Algebra.Module.StablyFree.Basic

/-!
# A finite projective module has a finite free resolution if and only if it is stably free
-/

public section

universe u v

namespace Module

variable {R : Type u} [CommRing R]

theorem HasFiniteFreeResolutionOfLength.isStablyFree_of_projective {P : Type v} [AddCommGroup P]
    [Module R P] {n : ℕ} (hn : HasFiniteFreeResolutionOfLength R P n) :
    [Projective R P] → Module.IsStablyFree R P := by
  induction hn using induction_on with
  | zero P =>
      intro
      infer_instance
  | succ K F P _ f g hf hg he hK ih =>
      intro
      have : Module.Finite R K := hK.module_finite
      obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
      let e : F ≃ₗ[R] K × P := ((Function.Exact.splitSurjectiveEquiv he hf) ⟨l, hl⟩).1
      have : Projective R (K × P) := Projective.of_equiv e
      have hprojK : Projective R K := Projective.of_split
        (LinearMap.inl R K P) (LinearMap.fst R K P) (LinearMap.ext fun _ ↦ by simp)
      rcases ih with ⟨N, _, _, _, _, _⟩
      have : Module.Free R (K × P) := Module.Free.of_equiv e
      have : Module.Free R (P × (K × N)) := Module.Free.of_equiv <|
        (LinearEquiv.prodComm R K P).prodCongr (LinearEquiv.refl R N) ≪≫ₗ
          LinearEquiv.prodAssoc R P K N
      exact Module.IsStablyFree.of_free_prod R P (K × N)

variable (R)

/-- Let `P` be a finite projective module. Then `P` is stably free if `P` admits a
  finite free resolution. -/
instance HasFiniteFreeResolution.isStablyFree (P : Type v) [AddCommGroup P] [Module R P]
    [Projective R P] [HasFiniteFreeResolution R P] : IsStablyFree R P := by
  obtain ⟨_, hn⟩ := HasFiniteFreeResolution.out R P
  exact hn.isStablyFree_of_projective

theorem HasFiniteFreeResolution.iff_isStablyFree [Small.{v} R] (P : Type v) [AddCommGroup P]
    [Module R P] [Module.Finite R P] [Projective R P] :
    HasFiniteFreeResolution R P ↔ IsStablyFree R P := by
  refine ⟨fun _ ↦ HasFiniteFreeResolution.isStablyFree R P, fun _ ↦ ?_⟩
  obtain ⟨N, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R P
  have : Small.{v} N := Module.Finite.small.{v} R N
  let +nondep eN : N ≃ₗ[R] Shrink.{v} N := (Shrink.linearEquiv R N).symm
  have : Module.Free R (P × Shrink.{v} N) :=
    Module.Free.of_equiv ((LinearEquiv.refl R P).prodCongr eN)
  exact of_shortExact_of_left_of_middle (LinearMap.inr R P (Shrink.{v} N))
    (LinearMap.fst R P (Shrink.{v} N)) LinearMap.inr_injective LinearMap.fst_surjective
      Function.Exact.inr_fst

end Module
