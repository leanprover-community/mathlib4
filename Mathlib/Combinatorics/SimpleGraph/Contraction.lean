/-
Copyright (c) 2026 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walks.Operations

/-!
# Simple graph contractions

This file defines the contraction of a simple graph as its image under a map with connected fibers.

## Main definitions

* `SimpleGraph.Adapted G f` : a function `f : V → V'` is adapted to a graph `G` if its fibers are
  connected via graph walks. This is equivalent to saying that `G.induce (f ⁻¹' {v})` is
  `Preconnected` but is easier to work with in practice.
* `SimpleGraph.IsContraction G G'`, `G ≼c G'` : a graph `G` is a contraction of a graph `G'` if it
  is the image of `G'` via `SimpleGraph.map` through a function that is surjective and `Adapted` to
  `G'`.

-/

@[expose] public section

open Function

namespace SimpleGraph

variable {V V' V'' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {G'' : SimpleGraph V''}
  {f : V → V'} {g : V' → V''} {x y z : V} {u v w : V'}

/-! A function is adapted to a graph if it has connected fibers. -/
def Adapted (G : SimpleGraph V) (f : V → V') : Prop :=
  ∀ ⦃x y : V⦄, f x = f y → ∃ p : G.Walk x y, ∀ z ∈ p.support, f z = f x

namespace Adapted

lemma of_injective (h : Injective f) : Adapted G f := by
  rintro x y hxy
  exact ⟨Walk.nil' x |>.copy rfl (h hxy), by simp⟩

lemma id : Adapted G id :=
  of_injective injective_id

/-! Lift a walk from a contraction to the original graph. -/
noncomputable def lift_walk (hf : Adapted G f) (p : Walk (G.map f) u v) :
    ∀ x y, f x = u → f y = v → { q : Walk G x y // ∀ z ∈ q.support, f z ∈ p.support } := by
  induction p with
  | nil =>
    rintro x y hxy rfl
    choose q hq using hf hxy
    refine ⟨q, by simpa [← hxy]⟩
  | cons h p ih =>
    rintro x y rfl rfl
    obtain ⟨h1, h2⟩ := h
    have := h2
    choose a b h3 h4 h5 using this
    subst h5
    obtain ⟨q₂, hq₂⟩ := ih b y rfl rfl
    choose q₁ hq₁ using hf h4.symm
    refine ⟨q₁.append (q₂.cons h3), ?_⟩
    intro z hz
    simp only [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons] at hz
    obtain h | h | h := hz <;> simp_all

/-! Variant of `lift_walk` where the endpoints are explicit images by the function. -/
noncomputable def lift_walk' (hf : Adapted G f) (p : Walk (G.map f) (f x) (f y)) :
    { q : Walk G x y // ∀ z ∈ q.support, f z ∈ p.support } :=
  lift_walk hf p x y rfl rfl

theorem comp (hf : Adapted G f) (hg : Adapted (G.map f) g) : Adapted G (g ∘ f) := by
  intro x y hxy
  obtain ⟨p, hp⟩ := hg hxy
  exact ⟨lift_walk' hf p, by grind⟩

end Adapted

/-! A graph `G` is a contraction of a graph `G'` if it is the image of `G'` via `SimpleGraph.map`
  through a function `f` that is surjective and has connected fibers. This can in particular be used
  when `f` is a quotient map with connected cosets.
  -/
def IsContraction (G : SimpleGraph V) (G' : SimpleGraph V') : Prop :=
  ∃ φ : V' → V, Surjective φ ∧ Adapted G' φ ∧ G = G'.map φ

infix:50 " ≼c " => IsContraction

namespace IsContraction

@[refl] theorem refl : G ≼c G :=
  ⟨id, surjective_id, Adapted.id, by simp⟩

@[trans] theorem trans : G ≼c G' → G' ≼c G'' → G ≼c G'' := by
  rintro ⟨φ1, h1s, h1a, rfl⟩ ⟨φ2, h2s, h2a, rfl⟩
  exact ⟨φ1 ∘ φ2, h1s.comp h2s, h2a.comp h1a, by simp⟩

theorem ofIso (φ : G ≃g G') : G ≼c G' := by
  refine ⟨φ.symm, φ.symm.surjective, .of_injective φ.symm.injective, ?_⟩
  ext x y
  refine ⟨fun h => ⟨h.ne, φ x, φ y, by simp [φ.map_rel_iff, h]⟩, ?_⟩
  rintro ⟨-, u, v, h2, rfl, rfl⟩
  simp only [← φ.map_rel_iff, RelIso.apply_symm_apply, h2]

lemma iso_left (h1 : G ≃g G') (h2 : G' ≼c G'') : G ≼c G'' := trans (ofIso h1) h2

lemma iso_right (h1 : G ≼c G') (h2 : G' ≃g G'') : G ≼c G'' := trans h1 (ofIso h2)

end IsContraction

end SimpleGraph
