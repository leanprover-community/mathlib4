/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Topology.Category.ExtrDisc.Basic
/-!
# Explicit (co)limits in Extremally disconnected sets

This file describes some explicit (co)limits in `ExtrDisc`

## Overview

We define explicit finite coproducts in `ExtrDisc` as sigma types (disjoint unions).

TODO: Define pullbacks of open embeddings.

-/

open CategoryTheory

-- This section contains helper lemmas about the sigma-type `Σ i, π i`.
section Sigma

@[simp]
theorem mem_sigma_iff {π : ι → Type _} [∀ i, TopologicalSpace (π i)]
  {i : ι} {x : π i} {s : Set (Σ i, π i)}
    : x ∈ Sigma.mk i ⁻¹' s ↔ ⟨i, x⟩ ∈ s :=
  Iff.rfl

lemma sigma_mk_preimage_image' (h : i ≠ j) : Sigma.mk j ⁻¹' (Sigma.mk i '' U) = ∅ := by
  change Sigma.mk j ⁻¹' {⟨i, u⟩ | u ∈ U} = ∅
  -- change { x | (Sigma.mk j) x ∈ {⟨i, u⟩ | u ∈ U}} = ∅
  simp [h]

lemma sigma_mk_preimage_image_eq_self : Sigma.mk i ⁻¹' (Sigma.mk i '' U) = U := by
  change Sigma.mk i ⁻¹' {⟨i, u⟩ | u ∈ U} = U
  simp

-- Note: It might be possible to use Gleason for this instead
/-- The sigma-type of extremally disconneted spaces is extremally disconnected -/
instance instExtremallyDisconnected
    {π : ι → Type _} [∀ i, TopologicalSpace (π i)] [h₀ : ∀ i, ExtremallyDisconnected (π i)] :
    ExtremallyDisconnected (Σi, π i) := by
  constructor
  intro s hs
  rw [isOpen_sigma_iff] at hs ⊢
  intro i
  rcases h₀ i with ⟨h₀⟩
  have h₁ : IsOpen (closure (Sigma.mk i ⁻¹' s))
  · apply h₀
    exact hs i
  suffices h₂ : Sigma.mk i ⁻¹' closure s = closure (Sigma.mk i ⁻¹' s)
  · rwa [h₂]
  apply IsOpenMap.preimage_closure_eq_closure_preimage
  intro U _
  · rw [isOpen_sigma_iff]
    intro j
    by_cases ij : i = j
    · rw [← ij]
      rw [sigma_mk_preimage_image_eq_self]
      assumption
    · rw [sigma_mk_preimage_image' ij]
      apply isOpen_empty
  · continuity

end Sigma

namespace ExtrDisc

/-!
This section defines the finite Coproduct of a finite family
of profinite spaces `X : α → ExtrDisc.{u}`

Notes: The content is mainly copied from
`Mathlib/Topology/Category/CompHaus/ExplicitLimits.lean`
-/
section FiniteCoproducts

open Limits

-- Assume we have `X a → B` which are jointly surjective.
variable {α : Type} [Fintype α] {B : ExtrDisc.{u}}
  (X : α → ExtrDisc.{u}) (π : (a : α) → (X a ⟶ B))
  (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b)

/--
The coproduct of a finite family of objects in `ExtrDisc`, constructed as the disjoint
union with its usual topology.
-/
def finiteCoproduct : ExtrDisc := ExtrDisc.of <| Σ (a : α), X a

/-- The inclusion of one of the factors into the explicit finite coproduct. -/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X where
  toFun := fun x => ⟨a,x⟩
  continuous_toFun := continuous_sigmaMk (σ := fun a => X a)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : ExtrDisc.{u}} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a,x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a; exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : ExtrDisc.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
  finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : ExtrDisc.{u}} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a,x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

/-- The coproduct cocone associated to the explicit finite coproduct. -/
@[simps]
def finiteCoproduct.cocone : Cocone (Discrete.functor X) where
  pt := finiteCoproduct X
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι X a

/-- The explicit finite coproduct cocone is a colimit cocone. -/
@[simps]
def finiteCoproduct.isColimit : IsColimit (finiteCoproduct.cocone X) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

/-- The category of extremally disconnected spaces has finite coproducts.
-/
instance hasFiniteCoproducts : HasFiniteCoproducts ExtrDisc.{u} where
  out n := {
    has_colimit := fun F => {
      exists_colimit := ⟨{
        cocone := {
          pt := finiteCoproduct (F.obj ⟨·⟩)
          ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι (F.obj ⟨·⟩) a }
        isColimit := {
          desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
          fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
          uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
            specialize hm ⟨a⟩
            ext t
            apply_fun (fun q => q t) at hm
            exact hm }}⟩}}

end FiniteCoproducts

end ExtrDisc
