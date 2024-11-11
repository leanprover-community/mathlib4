/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, David Loeffler
-/
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Vertical line test for group homs

This file proves the vertical line test for monoid homomorphisms/isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some monoid homomorphism `f' : H → I`.

Furthermore, if `f` is also surjective on the second factor and its image intersects every
"horizontal line" `{(h, i) | h : H}` at most once, then `f'` is actually an isomorphism
`f' : H ≃ I`.

We also prove specialised versions when `f` is the inclusion of a subgroup of the direct product.
(The version for general homomorphisms can easily be reduced to this special case, but the
homomorphism version is more flexible in applications.)
-/

open Function Set

variable {G H I : Type*} [Monoid G] [Monoid H] [Monoid I]

/-- **Vertical line test** for monoid homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some monoid homomorphism `f' : H → I`. -/
@[to_additive "**Vertical line test** for monoid homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every \"vertical line\" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some monoid homomorphism `f' : H → I`."]
lemma MonoidHom.exists_range_eq_graph {f : G →* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
    ∃ f' : H →* I, .range f = univ.graphOn f' := by
  use
  { toFun := fun h ↦ (f (hf₁ h).choose).snd
    map_one' := by simpa using hf (hf₁ 1).choose 1 (by simpa using (hf₁ 1).choose_spec)
    map_mul' := fun h₁ h₂ ↦ by
      have := calc (f (hf₁ (h₁ * h₂)).choose).fst
        _ = h₁ * h₂ := (hf₁ (h₁ * h₂)).choose_spec
        _ = (f (hf₁ h₁).choose).fst * (f (hf₁ h₂).choose).fst := by
          congr 1; exacts [(hf₁ h₁).choose_spec.symm, (hf₁ h₂).choose_spec.symm]
        _ = (f ((hf₁ h₁).choose * (hf₁ h₂).choose)).fst := by simp
      simpa using hf _ _ this }
  ext x
  simp only [Set.mem_range, Function.comp_apply, coe_mk, OneHom.coe_mk, mem_graphOn, mem_univ,
    true_and]
  refine ⟨?_, fun hi ↦ ⟨(hf₁ x.1).choose, Prod.ext (hf₁ x.1).choose_spec hi⟩⟩
  rintro ⟨g, rfl⟩
  exact hf _ _ (hf₁ (f g).1).choose_spec

/-- **Vertical line test** for monoid homomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that `G` maps bijectively to the
first factor. Then `G` is the graph of some monoid homomorphism `f : H → I`. -/
@[to_additive "**Vertical line test** for additive monoid homomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that `G` surjects onto the first
factor and `G` intersects every \"vertical line\" `{(h, i) | i : I}` at most once. Then `G` is the
graph of some monoid homomorphism `f : H → I`."]
lemma Submonoid.exists_eq_graph {G : Submonoid (H × I)} (hf₁ : Bijective (Prod.fst ∘ G.subtype)) :
    ∃ f : H →* I, G = univ.graphOn f := by
  simpa only [coe_subtype, Subtype.range_coe_subtype, SetLike.setOf_mem_eq]
    using MonoidHom.exists_range_eq_graph hf₁.surjective
      (fun a b h ↦ congr_arg (Prod.snd ∘ G.subtype) (hf₁.injective h))

/-- **Line test** for monoid isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some monoid
isomorphism `f' : H ≃ I`. -/
@[to_additive "**Line test** for monoid isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on both
factors and that the image of `f` intersects every \"vertical line\" `{(h, i) | i : I}` and every
\"horizontal line\" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some
monoid isomorphism `f' : H ≃ I`."]
lemma MonoidHom.exists_mulEquiv_range_eq_graph {f : G →* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf₂ : Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    ∃ e : H ≃* I, .range f = univ.graphOn e := by
  obtain ⟨e₁, he₁⟩ := f.exists_range_eq_graph hf₁ fun _ _ ↦ (hf _ _).1
  obtain ⟨e₂, he₂⟩ := (MulEquiv.prodComm.toMonoidHom.comp f).exists_range_eq_graph (by simpa) <|
    by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    rw [Set.ext_iff] at he₁ he₂
    aesop (add simp [Prod.swap_eq_iff_eq_swap])
  exact ⟨
  { toFun := e₁
    map_mul' := e₁.map_mul'
    invFun := e₂
    left_inv := fun h ↦ by rw [← he₁₂]
    right_inv := fun i ↦ by rw [he₁₂] }, he₁⟩

/-- **Goursat's lemma** for monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that the natural maps from `G` to
both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃* I`. -/
@[to_additive "**Goursat's lemma** for additive monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of additive monoids. Assume that the natural maps from
`G` to both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃+ I`."]
lemma Submonoid.exists_mulEquiv_eq_graph {G : Submonoid (H × I)}
    (hf₁ : Bijective (Prod.fst ∘ G.subtype)) (hf₂ : Bijective (Prod.snd ∘ G.subtype)) :
    ∃ e : H ≃* I, G = univ.graphOn e := by
  simpa only [coe_subtype, Subtype.range_coe_subtype, SetLike.setOf_mem_eq]
    using MonoidHom.exists_mulEquiv_range_eq_graph hf₁.surjective hf₂.surjective
      (fun _ _ ↦ (hf₁.injective.eq_iff).trans hf₂.injective.eq_iff.symm)
