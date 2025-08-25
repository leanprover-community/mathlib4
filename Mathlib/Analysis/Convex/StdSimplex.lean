/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Functoriality of the standard simplex

When `f : X → Y` is a map between finite types, and `S` is an ordered semiring,
we define the map `stdSimplex.map f : stdSimplex S X → stdSimplex S Y`.
In the case `S := ℝ`, we show that these maps are continuous.

-/

namespace stdSimplex

variable {S : Type*} [Semiring S] [PartialOrder S]
  {R : Type*} [Ring R] [PartialOrder R]
  {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

instance : FunLike (stdSimplex S X) X S where
  coe s := s.val
  coe_injective' := by aesop

@[ext high]
lemma ext {s t : stdSimplex S X} (h : (s : X → S) = t) : s = t := by
  ext : 1
  assumption

@[simp]
lemma zero_le (s : stdSimplex S X) (x : X) : 0 ≤ s x := s.2.1 x

@[simp]
lemma sum_eq_one (s : stdSimplex S X) : ∑ x, s x = 1 := s.2.2

@[simp]
lemma le_one (s : stdSimplex R X) [IsOrderedRing R] (x : X) : s x ≤ 1 := by
  classical
  rw [← sum_eq_one s, ← Finset.sum_compl_add_sum {x}, Finset.sum_singleton,
    le_add_iff_nonneg_left]
  exact Finset.sum_nonneg (by simp)

lemma add_eq_one (s : stdSimplex S (Fin 2)) :
    s 0 + s 1 = 1 := by
  simpa only [Fin.sum_univ_two] using sum_eq_one s

section

variable [IsOrderedRing S]

/-- The vertex corresponding to `x : X` in `stdSimplex S X`. -/
abbrev vertex [DecidableEq X] (x : X) : stdSimplex S X :=
  ⟨Pi.single x 1, single_mem_stdSimplex S x⟩

@[simp]
lemma vertex_coe [DecidableEq X] (x : X) :
    ⇑(vertex (S := S) x) = Pi.single x 1 := rfl

lemma vertex_injective [Nontrivial S] [DecidableEq X] :
    Function.Injective (vertex (S := S) (X := X)) := by
  intro x y h
  replace h := DFunLike.congr_fun h x
  by_contra!
  simp [Pi.single_eq_of_ne this] at h

instance [Nonempty X] : Nonempty (stdSimplex S X) := by
  classical
  exact ⟨vertex (Classical.arbitrary _)⟩

instance [Nontrivial S] [Nontrivial X] : Nontrivial (stdSimplex S X) where
  exists_pair_ne := by
    classical
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    exact ⟨vertex x, vertex y, fun h ↦ hxy (vertex_injective h)⟩

instance [Subsingleton X] : Subsingleton (stdSimplex S X) where
  allEq s t := by
    ext i
    have (u : stdSimplex S X) : u i = 1 := by
      rw [← sum_eq_one u, Finset.sum_eq_single i _ (by simp)]
      intro j _ hj
      exact (hj (Subsingleton.elim j i)).elim
    simp [this]

instance [Unique X] : Unique (stdSimplex S X) where
  default := ⟨1, by simp, by simp⟩
  uniq := by subsingleton

@[simp]
lemma eq_one_of_unique [Unique X] (s : stdSimplex S X) (x : X) :
    s x = 1 := by
  obtain rfl : s = default := by subsingleton
  rfl

lemma image_linearMap (f : X → Y) :
    Set.image (FunOnFinite.linearMap S S f) (stdSimplex S X) ⊆ stdSimplex S Y := by
  classical
  rintro _ ⟨s, ⟨hs₀, hs₁⟩, rfl⟩
  refine ⟨fun y ↦ ?_, ?_⟩
  · rw [FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_nonneg (by aesop)
  · simp only [FunOnFinite.linearMap_apply_apply, ← hs₁]
    exact Finset.sum_fiberwise Finset.univ f s

/-- The map `stdSimplex S X → stdSimplex S Y` that is induced by a map `f : X → Y`. -/
noncomputable def map (f : X → Y) (s : stdSimplex S X) : stdSimplex S Y :=
  ⟨FunOnFinite.linearMap S S f s, image_linearMap f (by aesop)⟩

@[simp]
lemma map_coe (f : X → Y) (s : stdSimplex S X) :
    ⇑(map f s) = FunOnFinite.linearMap S S f s := rfl

@[simp]
lemma map_id_apply (x : stdSimplex S X) : map id x = x := by
  aesop

lemma map_comp_apply (f : X → Y) (g : Y → Z) (x : stdSimplex S X) :
    map g (map f x) = map (g.comp f) x := by
  ext
  simp [FunOnFinite.linearMap_comp]

@[simp]
lemma map_vertex [DecidableEq X] [DecidableEq Y] (f : X → Y) (x : X) :
    map (S := S) f (vertex x) = vertex (f x) := by
  aesop

end

lemma _root_.FunOnFinite.continuous_linearMap (f : X → Y) :
    Continuous (FunOnFinite.linearMap ℝ ℝ f) := by
  classical
  refine continuous_pi (fun y ↦ ?_)
  simp only [FunOnFinite.linearMap_apply_apply]
  apply continuous_finset_sum
  continuity

@[continuity]
lemma continuous_map (f : X → Y) : Continuous (map (S := ℝ) f) :=
  Continuous.subtype_mk ((FunOnFinite.continuous_linearMap f).comp continuous_induced_dom) _

end stdSimplex
