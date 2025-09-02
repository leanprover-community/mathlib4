/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, David Loeffler
-/
import Mathlib.Algebra.Group.Subgroup.Ker

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

variable {G H I : Type*}

section Monoid
variable [Monoid G] [Monoid H] [Monoid I]

namespace MonoidHom

/-- The graph of a monoid homomorphism as a submonoid.

See also `MonoidHom.graph` for the graph as a subgroup. -/
@[to_additive
/-- The graph of a monoid homomorphism as a submonoid.

See also `AddMonoidHom.graph` for the graph as a subgroup. -/]
def mgraph (f : G →* H) : Submonoid (G × H) where
  carrier := {x | f x.1 = x.2}
  one_mem' := map_one f
  mul_mem' {x y} := by simp +contextual

-- TODO: Can `to_additive` be smarter about `simps`?
attribute [simps! coe] mgraph
attribute [simps! coe] AddMonoidHom.mgraph
set_option linter.existingAttributeWarning false in
attribute [to_additive existing] coe_mgraph

@[to_additive (attr := simp)]
lemma mem_mgraph {f : G →* H} {x : G × H} : x ∈ f.mgraph ↔ f x.1 = x.2 := .rfl

@[to_additive mgraph_eq_mrange_prod]
lemma mgraph_eq_mrange_prod (f : G →* H) : f.mgraph = mrange ((id _).prod f) := by aesop

@[deprecated (since := "2025-03-11")]
alias _root_.AddMonoidHom.mgraph_eq_mrange_sum := AddMonoidHom.mgraph_eq_mrange_prod

/-- **Vertical line test** for monoid homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some monoid homomorphism `f' : H → I`. -/
@[to_additive /-- **Vertical line test** for monoid homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some monoid homomorphism `f' : H → I`. -/]
lemma exists_mrange_eq_mgraph {f : G →* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
    ∃ f' : H →* I, mrange f = f'.mgraph := by
  obtain ⟨f', hf'⟩ := exists_range_eq_graphOn_univ hf₁ hf
  simp only [Set.ext_iff, Set.mem_range, mem_graphOn, mem_univ, true_and, Prod.forall] at hf'
  use
  { toFun := f'
    map_one' := (hf' _ _).1 ⟨1, map_one _⟩
    map_mul' := by
      simp_rw [hf₁.forall]
      rintro g₁ g₂
      exact (hf' _ _).1 ⟨g₁ * g₂, by simp [Prod.ext_iff, (hf' (f _).1 _).1 ⟨_, rfl⟩]⟩ }
  simpa [SetLike.ext_iff] using hf'

/-- **Line test** for monoid isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some monoid
isomorphism `f' : H ≃ I`. -/
@[to_additive /-- **Line test** for monoid isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some
monoid isomorphism `f' : H ≃ I`. -/]
lemma exists_mulEquiv_mrange_eq_mgraph {f : G →* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf₂ : Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    ∃ e : H ≃* I, mrange f = e.toMonoidHom.mgraph := by
  obtain ⟨e₁, he₁⟩ := f.exists_mrange_eq_mgraph hf₁ fun _ _ ↦ (hf _ _).1
  obtain ⟨e₂, he₂⟩ := (MulEquiv.prodComm.toMonoidHom.comp f).exists_mrange_eq_mgraph (by simpa) <|
    by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    rw [SetLike.ext_iff] at he₁ he₂
    aesop (add simp [Prod.swap_eq_iff_eq_swap])
  exact ⟨
  { toFun := e₁
    map_mul' := e₁.map_mul'
    invFun := e₂
    left_inv := fun h ↦ by rw [← he₁₂]
    right_inv := fun i ↦ by rw [he₁₂] }, he₁⟩

end MonoidHom

/-- **Vertical line test** for monoid homomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that `G` maps bijectively to the
first factor. Then `G` is the graph of some monoid homomorphism `f : H → I`. -/
@[to_additive /-- **Vertical line test** for additive monoid homomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that `G` surjects onto the first
factor and `G` intersects every "vertical line" `{(h, i) | i : I}` at most once. Then `G` is the
graph of some monoid homomorphism `f : H → I`. -/]
lemma Submonoid.exists_eq_mgraph {G : Submonoid (H × I)} (hG₁ : Bijective (Prod.fst ∘ G.subtype)) :
    ∃ f : H →* I, G = f.mgraph := by
  simpa using MonoidHom.exists_mrange_eq_mgraph hG₁.surjective
    fun a b h ↦ congr_arg (Prod.snd ∘ G.subtype) (hG₁.injective h)

/-- **Goursat's lemma** for monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that the natural maps from `G` to
both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃* I`. -/
@[to_additive /-- **Goursat's lemma** for additive monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of additive monoids. Assume that the natural maps from
`G` to both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃+ I`. -/]
lemma Submonoid.exists_mulEquiv_eq_mgraph {G : Submonoid (H × I)}
    (hG₁ : Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) :
    ∃ e : H ≃* I, G = e.toMonoidHom.mgraph := by
  simpa using MonoidHom.exists_mulEquiv_mrange_eq_mgraph hG₁.surjective hG₂.surjective
    fun _ _ ↦ hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

end Monoid

section Group
variable [Group G] [Group H] [Group I]

namespace MonoidHom

/-- The graph of a group homomorphism as a subgroup.

See also `MonoidHom.mgraph` for the graph as a submonoid. -/
@[to_additive
/-- The graph of a group homomorphism as a subgroup.

See also `AddMonoidHom.mgraph` for the graph as a submonoid. -/]
def graph (f : G →* H) : Subgroup (G × H) where
  toSubmonoid := f.mgraph
  inv_mem' {x} := by simp +contextual

-- TODO: Can `to_additive` be smarter about `simps`?
attribute [simps! coe toSubmonoid] graph
attribute [simps! coe toAddSubmonoid] AddMonoidHom.graph
set_option linter.existingAttributeWarning false in
attribute [to_additive existing] coe_graph graph_toSubmonoid

@[to_additive]
lemma mem_graph {f : G →* H} {x : G × H} : x ∈ f.graph ↔ f x.1 = x.2 := .rfl

@[to_additive graph_eq_range_prod]
lemma graph_eq_range_prod (f : G →* H) : f.graph = range ((id _).prod f) := by aesop

@[deprecated (since := "2025-03-11")]
alias AddMonoidHom.graph_eq_range_sum := graph_eq_range_prod

/-- **Vertical line test** for group homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of groups. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some group homomorphism `f' : H → I`. -/
@[to_additive /-- **Vertical line test** for group homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of groups. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some group homomorphism `f' : H → I`. -/]
lemma exists_range_eq_graph {f : G →* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
    ∃ f' : H →* I, range f = f'.graph := by
  simpa [SetLike.ext_iff] using exists_mrange_eq_mgraph hf₁ hf

/-- **Line test** for group isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of groups. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some group
isomorphism `f' : H ≃ I`. -/
@[to_additive /-- **Line test** for monoid isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of groups. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some
group isomorphism `f' : H ≃ I`. -/]
lemma exists_mulEquiv_range_eq_graph {f : G →* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf₂ : Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    ∃ e : H ≃* I, range f = e.toMonoidHom.graph := by
  simpa [SetLike.ext_iff] using exists_mulEquiv_mrange_eq_mgraph hf₁ hf₂ hf

end MonoidHom

/-- **Vertical line test** for group homomorphisms.

Let `G ≤ H × I` be a subgroup of a product of monoids. Assume that `G` maps bijectively to the
first factor. Then `G` is the graph of some monoid homomorphism `f : H → I`. -/
@[to_additive /-- **Vertical line test** for additive monoid homomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that `G` surjects onto the first
factor and `G` intersects every "vertical line" `{(h, i) | i : I}` at most once. Then `G` is the
graph of some monoid homomorphism `f : H → I`. -/]
lemma Subgroup.exists_eq_graph {G : Subgroup (H × I)} (hG₁ : Bijective (Prod.fst ∘ G.subtype)) :
    ∃ f : H →* I, G = f.graph := by
  simpa [SetLike.ext_iff] using Submonoid.exists_eq_mgraph hG₁

/-- **Goursat's lemma** for monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that the natural maps from `G` to
both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃* I`. -/
@[to_additive /-- **Goursat's lemma** for additive monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of additive monoids. Assume that the natural maps from
`G` to both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃+ I`. -/]
lemma Subgroup.exists_mulEquiv_eq_graph {G : Subgroup (H × I)}
    (hG₁ : Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) :
    ∃ e : H ≃* I, G = e.toMonoidHom.graph := by
  simpa [SetLike.ext_iff] using Submonoid.exists_mulEquiv_eq_mgraph hG₁ hG₂

end Group
