/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!

# Existence of Flat extension

-/

@[expose] public section

universe w u v

open IsLocalRing CategoryTheory

variable (R : Type u) [CommRing R] [IsLocalRing R] (K : Type v) [Field K]
  [Algebra (ResidueField R) K]

structure FlatExtension where
  Ring : Type w
  [commRing : CommRing Ring]
  [isLocalRing : IsLocalRing Ring]
  [algebra : Algebra R Ring]
  [isLocalHom : IsLocalHom (algebraMap R Ring)]
  flat : Module.Flat R Ring
  eqmap : maximalIdeal Ring = (maximalIdeal R).map (algebraMap R Ring)
  resembd : ResidueField Ring →ₐ[ResidueField R] K

open FlatExtension

attribute [instance] commRing algebra isLocalRing isLocalHom

variable {R K} in
structure FlatExtension.Hom (S₁ S₂ : FlatExtension.{w} R K) where
  hom : S₁.Ring →ₐ[R] S₂.Ring
  [isLocalHom : IsLocalHom hom]
  comm : S₂.resembd.toRingHom.comp (ResidueField.map hom) = S₁.resembd.toRingHom

attribute [instance] Hom.isLocalHom

instance {S : Type*} [Ring S] [Algebra R S] : IsLocalHom (AlgHom.id R S) := ⟨fun _ h ↦ h⟩

instance {S₁ S₂ S₃ : Type*} [Ring S₁] [Ring S₂] [Ring S₃] [Algebra R S₁] [Algebra R S₂]
    [Algebra R S₃] (f : S₁ →ₐ[R] S₂) (g : S₂ →ₐ[R] S₃) [locf : IsLocalHom f] [locg : IsLocalHom g] :
    IsLocalHom (g.comp f) :=
  ⟨fun a ha ↦ locf.map_nonunit a (locg.map_nonunit (f a) ha)⟩

omit [IsLocalRing R] in
lemma AlgHom.comp_toRingHom' {S₁ S₂ S₃ : Type*} [Ring S₁] [Ring S₂] [Ring S₃] [Algebra R S₁]
    [Algebra R S₂] [Algebra R S₃] (f : S₁ →ₐ[R] S₂) (g : S₂ →ₐ[R] S₃) :
    (g.comp f) = (RingHomClass.toRingHom g).comp (RingHomClass.toRingHom f) := rfl

instance : Category (FlatExtension R K) where
  Hom S₁ S₂ := FlatExtension.Hom S₁ S₂
  id S := ⟨AlgHom.id R S.Ring, by simp⟩
  comp f g := ⟨g.hom.comp f.hom, by
    rw [← f.comm, ← g.comm]
    simp [AlgHom.comp_toRingHom', ResidueField.map_comp, ← RingHom.comp_assoc]⟩

lemma exists_isLocalHom_flat : ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R')
    (_ : Algebra R R') (_ : IsLocalHom (algebraMap R R')), Module.Flat R R' ∧
    maximalIdeal R' = (maximalIdeal R).map (algebraMap R R') ∧
    Nonempty (K ≃ₐ[ResidueField R] (ResidueField R')) := by
  sorry
