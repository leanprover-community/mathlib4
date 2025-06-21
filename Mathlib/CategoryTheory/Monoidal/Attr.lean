/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Init
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

/-!
# Simp attribute for monoid objects

This file declares the `mon_tauto` simp set, which in `Mathlib/CategoryTheory/Monoidal/Mon_.lean`
gets equipped to prove all tautologies involving (commutative) monoid objects in a (braided)
monoidal category. See below for full details.
-/

/-- `mon_tauto` is a simp set to prove all tautologies involving (commutative) monoid objects in a
(braided) monoidal category.

THIS SIMP SET IS INCOMPATIBLE WITH THE STANDARD SIMP SET.
If you want to use it, make sure to add the following to your simp call to disable the problematic
default simp lemmas:
```
-MonoidalCategory.whiskerLeft_id, -MonoidalCategory.id_whiskerRight,
-MonoidalCategory.tensor_comp, -MonoidalCategory.tensor_comp_assoc,
-Mon_Class.mul_assoc, -Mon_Class.mul_assoc_assoc
```

The general algorithm it follows is to push the associators `α_` and commutators `β_` inwards until
they cancel against the right sequence of multiplications.

This approach is justified by the fact that a tautology in the language of (commutative) monoid
objects "remembers" how it was proved: Every use of a (commutative) monoid object axiom inserts a
unitor, associator or commutator, and proving a tautology simply amounts to undoing those moves as
prescribed by the presence of unitors, associators and commutators in its expression.

This simp set is opiniated about its normal form, which is why it be used concurrently to some of
the simp lemmas in the standard simp set:
* It eliminates all mentions of whiskers by rewriting them to tensored homs,
  which goes against `whiskerLeft_id` and `id_whiskerRight`:
  `X ◁ f = 𝟙 X ⊗ₘ f`, `f ▷ X = 𝟙 X ⊗ₘ f`.
  This goes against `whiskerLeft_id` and `id_whiskerRight` in the standard simp set.
* It collapses compositions of tensored homs to the tensored hom of the compositions,
  which goes against `tensor_comp`:
  `(f₁ ⊗ₘ g₁) ≫ (f₂ ⊗ₘ g₂) = (f₁ ≫ f₂) ⊗ₘ (g₁ ≫ g₂)`. TODO: Isn't this direction Just Better?
* It cancels the associators against multiplications,
  which goes against `mul_assoc`:
  `(α_ M M M).hom ≫ (𝟙 M ⊗ₘ μ) ≫ μ = (μ ⊗ₘ 𝟙 M) ≫ μ`,
  `(α_ M M M).inv ≫ (μ ⊗ₘ 𝟙 M) ≫ μ = (𝟙 M ⊗ₘ μ) ≫ μ`
* It unfolds non-primitive coherence isomorphisms, like the tensor strengths `tensorμ`, `tensorδ`.
-/
register_simp_attr mon_tauto
