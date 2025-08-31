/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Algebra.Homology.CommSq

/-!
# The exact sequence attached to a pushout square

Consider a pushout square in an abelian category:

```
X₁ ⟶ X₂
|    |
v    v
X₃ ⟶ X₄
```

We study the associated exact sequence `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0`.

-/

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {X₁ X₂ X₃ X₄ : C}
  {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

namespace IsPushout

lemma exact_shortComplex (h : IsPushout t l r b) : h.shortComplex.Exact :=
  h.shortComplex.exact_of_g_is_cokernel
    h.isColimitCokernelCofork

/-- Given a pushout square in an abelian category
```
X₁ ⟶ X₂
|    |
v    v
X₃ ⟶ X₄
```
the morphism `X₂ ⊞ X₃ ⟶ X₄` is an epimorphism. This lemma translates this
as the existence of liftings up to refinements: a morphism `z : T ⟶ X₄`
can be written as a sum of a morphism to `X₂` and a morphism to `X₃`,
at least if we allow a precomposition with an epimorphism `π : T' ⟶ T`. -/
lemma hom_eq_add_up_to_refinements (h : IsPushout t l r b) {T : C} (x₄ : T ⟶ X₄) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (x₂ : T' ⟶ X₂) (x₃ : T' ⟶ X₃),
      π ≫ x₄ = x₂ ≫ r + x₃ ≫ b := by
  have := h.epi_shortComplex_g
  obtain ⟨T', π, _, u, hu⟩ := surjective_up_to_refinements_of_epi h.shortComplex.g x₄
  refine ⟨T', π, inferInstance, u ≫ biprod.fst, u ≫ biprod.snd, ?_⟩
  simp only [hu, assoc, ← Preadditive.comp_add]
  congr
  aesop_cat

/--
Given a commutative diagram in an abelian category
```
X₁ ⟶ X₂
|    |  \
v    v   \
X₃ ⟶ X₄   \
 \     \   v
  \     \> X₅
   \_____>
```
where the top/left square is a pushout square,
the outer square involving `X₁`, `X₂`, `X₃` and `X₅`
is a pullback square, and `X₂ ⟶ X₅` is mono,
then `X₄ ⟶ X₅` is a mono.
-/
lemma mono_of_isPullback_of_mono
    (h₁ : IsPushout t l r b) {X₅ : C} {r' : X₂ ⟶ X₅} {b' : X₃ ⟶ X₅}
    (h₂ : IsPullback t l r' b') (k : X₄ ⟶ X₅)
    (fac₁ : r ≫ k = r') (fac₂ : b ≫ k = b') [Mono r'] : Mono k :=
  Preadditive.mono_of_cancel_zero _ (fun {T₀} x₄ hx₄ ↦ by
    obtain ⟨T₁, π, _, x₂, x₃, eq⟩ := hom_eq_add_up_to_refinements h₁ x₄
    have fac₃ : (-x₂) ≫ r' = x₃ ≫ b' := by
      rw [Preadditive.neg_comp, neg_eq_iff_add_eq_zero, ← fac₂, ← fac₁,
        ← assoc, ← assoc, ← Preadditive.add_comp, ← eq, assoc, hx₄, comp_zero]
    obtain ⟨x₂', hx₂'⟩ : ∃ x₂', π ≫ x₄ = x₂' ≫ r := by
      refine ⟨x₂ + h₂.lift (-x₂) x₃ fac₃ ≫ t, ?_⟩
      rw [eq, Preadditive.add_comp, assoc, h₁.w, IsPullback.lift_snd_assoc, add_comm]
    rw [← cancel_epi π, comp_zero, reassoc_of% hx₂', fac₁] at hx₄
    obtain rfl := zero_of_comp_mono _ hx₄
    rw [zero_comp] at hx₂'
    rw [← cancel_epi π, hx₂', comp_zero])

end IsPushout

namespace IsPullback

lemma exact_shortComplex' (h : IsPullback t l r b) : h.shortComplex'.Exact :=
  h.shortComplex'.exact_of_f_is_kernel
    h.isLimitKernelFork

/-!
Note: if `h : IsPullback t l r b`, then `X₁ ⟶ X₂ ⊞ X₃` is a monomorphism,
which can be translated in concrete terms thanks to the lemma `IsPullback.hom_ext`:
if a morphism `f : Z ⟶ X₁` becomes zero after composing with `X₁ ⟶ X₂` and
`X₁ ⟶ X₃`, then `f = 0`. This is the reason why we do not state the dual
statement to `IsPushout.hom_eq_add_up_to_refinements`.
-/

end IsPullback


end CategoryTheory
