/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Data.Set.BooleanAlgebra

/-!
# Entourages

Many definitions in metric spaces rely solely on the set `{(x, y) | dist x y ≤ ε}`. This is
called an entourage and this file provides basic definitions around entourages.
-/

assert_not_exists Filter

open Set

/-!
### Relations, seen as `Set (α × α)`
-/

variable {ι : Sort*} {α β : Type*} {U V W : Set (α × α)} {x y z : α}

/-- The identity relation, or the graph of the identity function -/
def idRel := {(x, y) : α × α | x = y}

@[simp] lemma mem_idRel : (x, y) ∈ @idRel α ↔ x = y := .rfl

@[simp] lemma idRel_subset : idRel ⊆ U ↔ ∀ x, (x, x) ∈ U := by simp [subset_def]

lemma eq_singleton_left_of_prod_subset_idRel {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty)
    (h_diag : s ×ˢ t ⊆ idRel) : ∃ x, s = {x} := by
  rcases hs, ht with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  refine ⟨s, eq_singleton_iff_nonempty_unique_mem.mpr ⟨⟨s, hs⟩, fun x hx ↦ ?_⟩⟩
  rw [prod_subset_iff] at h_diag
  obtain rfl := h_diag s hs t ht
  exact h_diag x hx _ ht

lemma eq_singleton_right_prod_subset_idRel {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty)
    (h_diag : s ×ˢ t ⊆ idRel) : ∃ x, t = {x} := by
  rw [Set.prod_subset_iff] at h_diag
  replace h_diag := fun x hx y hy => (h_diag y hy x hx).symm
  exact eq_singleton_left_of_prod_subset_idRel ht hs (prod_subset_iff.mpr h_diag)

lemma eq_singleton_prod_subset_idRel {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty)
    (h_diag : s ×ˢ t ⊆ idRel) : ∃ x, s = {x} ∧ t = {x} := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := eq_singleton_left_of_prod_subset_idRel hs ht h_diag,
    eq_singleton_right_prod_subset_idRel hs ht h_diag
  refine ⟨x, hx, ?_⟩
  rw [hy, Set.singleton_eq_singleton_iff]
  exact (Set.prod_subset_iff.mp h_diag x (by simp only [hx, Set.mem_singleton]) y
    (by simp only [hy, Set.mem_singleton])).symm

/-- The composition of relations -/
def compRel (U V : Set (α × α)) := {(x, z) : α × α | ∃ y, (x, y) ∈ U ∧ (y, z) ∈ V}

@[inherit_doc]
scoped[Uniformity] infixl:62 " ○ " => compRel
open Uniformity

@[simp] lemma mem_compRel : (x, z) ∈ U ○ V ↔ ∃ y, (x, y) ∈ U ∧ (y, z) ∈ V := .rfl

@[simp]
lemma swap_idRel : Prod.swap '' idRel = @idRel α :=
  Set.ext fun ⟨a, b⟩ => by simpa [image_swap_eq_preimage_swap] using eq_comm

lemma Monotone.compRel [Preorder β] {f g : β → Set (α × α)} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ○ g x := fun _ _ h _ ⟨z, h₁, h₂⟩ => ⟨z, hf h h₁, hg h h₂⟩

@[mono, gcongr]
lemma compRel_mono {f g h k : Set (α × α)} (h₁ : f ⊆ h) (h₂ : g ⊆ k) : f ○ g ⊆ h ○ k :=
  fun _ ⟨z, h, h'⟩ => ⟨z, h₁ h, h₂ h'⟩

lemma prodMk_mem_compRel (hxy : (x, y) ∈ U) (hyz : (y, z) ∈ V) : (x, z) ∈ U ○ V := ⟨y, hxy, hyz⟩

@[deprecated (since := "2025-03-10")] alias prod_mk_mem_compRel := prodMk_mem_compRel

@[simp] lemma id_compRel : idRel ○ U = U := Set.ext fun ⟨a, b⟩ => by simp

lemma compRel_assoc : U ○ V ○ W  = U ○ (V ○ W) := by ext ⟨a, b⟩; simp only [mem_compRel]; tauto

lemma left_subset_compRel (h : idRel ⊆ V) : U ⊆ U ○ V := fun ⟨_x, y⟩ xy_in ↦ ⟨y, xy_in, h <| rfl⟩

lemma right_subset_compRel (h : idRel ⊆ U) : V ⊆ U ○ V := fun ⟨x, _y⟩ xy_in ↦ ⟨x, h <| rfl, xy_in⟩

lemma subset_comp_self (h : idRel ⊆ U) : U ⊆ U ○ U := left_subset_compRel h

lemma subset_iterate_compRel (h : idRel ⊆ U) : ∀ {V} n, V ⊆ (U ○ ·)^[n] V
  | _V, 0 => .rfl
  | _V, n + 1 => (right_subset_compRel h).trans <| subset_iterate_compRel h n

/-- The relation is invariant under swapping factors. -/
def IsSymmetricRel (U : Set (α × α)) : Prop := ∀ ⦃a b⦄, (a, b) ∈ U → (b, a) ∈ U

@[deprecated (since := "2025-03-05")] alias SymmetricRel := IsSymmetricRel

/-- The maximal symmetric relation contained in a given relation. -/
def symmetrizeRel (U : Set (α × α)) : Set (α × α) := U ∩ Prod.swap ⁻¹' U

lemma symmetric_symmetrizeRel (U : Set (α × α)) : IsSymmetricRel (symmetrizeRel U) := by
  simp +contextual [IsSymmetricRel, symmetrizeRel]

lemma symmetrizeRel_subset_self (U : Set (α × α)) : symmetrizeRel U ⊆ U := sep_subset _ _

@[mono] lemma symmetrize_mono (h : U ⊆ V) : symmetrizeRel U ⊆ symmetrizeRel V :=
  inter_subset_inter h <| preimage_mono h

lemma IsSymmetricRel.mk_mem_comm (hU : IsSymmetricRel U) : (x, y) ∈ U ↔ (y, x) ∈ U :=
  ⟨@hU _ _, @hU _ _⟩

@[deprecated (since := "2025-03-05")] alias SymmetricRel.mk_mem_comm := IsSymmetricRel.mk_mem_comm

lemma IsSymmetricRel.eq (hU : IsSymmetricRel U) : Prod.swap ⁻¹' U = U := ext fun _ ↦ hU.mk_mem_comm

@[deprecated (since := "2025-03-05")] alias SymmetricRel.eq := IsSymmetricRel.eq

lemma IsSymmetricRel.inter (hU : IsSymmetricRel U) (hV : IsSymmetricRel V) :
    IsSymmetricRel (U ∩ V) := fun _ _ ⟨h₁, h₂⟩ ↦ ⟨hU h₁, hV h₂⟩

@[deprecated (since := "2025-03-05")] alias SymmetricRel.inter := IsSymmetricRel.inter

lemma IsSymmetricRel.iInter {U : (i : ι) → Set (α × α)} (hU : ∀ i, IsSymmetricRel (U i)) :
    IsSymmetricRel (⋂ i, U i) := by
  simp only [IsSymmetricRel, mem_iInter]; exact fun a b h i ↦ hU i <| h i

lemma IsSymmetricRel.preimage_prodMap (hU : IsSymmetricRel U) (f : β → α) :
    IsSymmetricRel (Prod.map f f ⁻¹' U) := fun _ _ ↦ @hU _ _

lemma IsSymmetricRel.comp_self (hU : IsSymmetricRel U) : IsSymmetricRel (U ○ U) :=
  fun _x _z ↦ .imp fun _y ⟨hxy, hyz⟩ ↦ ⟨hU hyz, hU hxy⟩

/-!
### Balls
-/

namespace UniformSpace

/-- The ball around `(x : α)` with respect to `(V : Set (α × α))`. Intended to be
used for `V ∈ 𝓤 α`, but this is not needed for the definition. Recovers the
notions of metric space ball when `V = {p | dist p.1 p.2 < r }`. -/
def ball (x : α) (V : Set (α × α)) : Set α := Prod.mk x ⁻¹' V

open UniformSpace (ball)

/-- The triangle inequality for `UniformSpace.ball`. -/
lemma mem_ball_comp (hxy : y ∈ ball x U) (hyz : z ∈ ball y V) : z ∈ ball x (U ○ V) :=
  prodMk_mem_compRel hxy hyz

lemma ball_subset_of_comp_subset (h : x ∈ ball y V) (hVU : V ○ V ⊆ U) : ball x V ⊆ ball y U :=
  fun _z hz => hVU (mem_ball_comp h hz)

lemma ball_mono (h : U ⊆ V) (x : α) : ball x U ⊆ ball x V := preimage_mono h

lemma ball_inter (x : α) (U V : Set (α × α)) : ball x (U ∩ V) = ball x U ∩ ball x V :=
  preimage_inter

lemma ball_inter_left (x : α) (U W : Set (α × α)) : ball x (U ∩ W) ⊆ ball x U :=
  ball_mono inter_subset_left x

lemma ball_inter_right (x : α) (U W : Set (α × α)) : ball x (U ∩ W) ⊆ ball x W :=
  ball_mono inter_subset_right x

lemma mem_ball_symmetry (hU : IsSymmetricRel U) : x ∈ ball y U ↔ y ∈ ball x U := hU.mk_mem_comm

lemma ball_eq_of_symmetry (hU : IsSymmetricRel U) : ball x U = {y | (y, x) ∈ U} := by
  ext y; exact mem_ball_symmetry hU

lemma mem_comp_of_mem_ball (hU : IsSymmetricRel U) (hx : x ∈ ball z U) (hy : y ∈ ball z V) :
    (x, y) ∈ U ○ V := by rw [mem_ball_symmetry hU] at hx; exact ⟨z, hx, hy⟩

lemma mem_comp_comp (hV : IsSymmetricRel V) {p : α × α} :
    p ∈ U ○ W ○ V ↔ (ball p.1 U ×ˢ ball p.2 V ∩ W).Nonempty := by
  simp [compRel, Set.Nonempty, ball, ← exists_and_right, ← and_assoc, and_right_comm (b := _ ∈ W),
    hV.mk_mem_comm]
  rw [exists_comm]

end UniformSpace
