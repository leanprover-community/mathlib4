/-
Copyright (c) 2024 Andrew Yang, Qi Ge, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Qi Ge, Christian Merten
-/
module

public import Mathlib.RingTheory.RingHomProperties

/-! # Meta properties of injective ring homomorphisms -/

public section

lemma _root_.RingHom.injective_stableUnderComposition :
    RingHom.StableUnderComposition (fun f ↦ Function.Injective f) := by
  intro R S T _ _ _ f g hf hg
  simp only [RingHom.coe_comp]
  exact Function.Injective.comp hg hf

lemma _root_.RingHom.injective_respectsIso :
    RingHom.RespectsIso (fun f ↦ Function.Injective f) := by
  apply RingHom.injective_stableUnderComposition.respectsIso
  intro R S _ _ e
  exact e.bijective.injective
