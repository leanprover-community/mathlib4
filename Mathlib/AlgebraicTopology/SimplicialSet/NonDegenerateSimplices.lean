/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import Mathlib.AlgebraicTopology.SimplicialSet.Simplices

/-!
# The partially ordered type of non degenerate simplices of a simplicial set

In this file, we introduce the partially ordered type `X.N` of
non degenerate simplices of a simplicial set `X`. We obtain
an embedding `X.orderEmbeddingN : X.N ↪o X.Subcomplex` which sends
a non degenerate simplex to the subcomplex of `X` it generates.

Given an arbitrary simplex `x : X.S`, we show that there is a unique
non degenerate `x.toN : X.N` such that `x.toN.subcomplex = x.subcomplex`.

-/

universe u

open CategoryTheory Simplicial

namespace SSet

variable (X : SSet.{u})

/-- The type of non degenerate simplices of a simplicial set. -/
structure N extends X.S where mk' ::
  nonDegenerate : simplex ∈ X.nonDegenerate _

namespace N

variable {X}

lemma mk'_surjective (s : X.N) :
    ∃ (t : X.S) (ht : t.simplex ∈ X.nonDegenerate _), s = mk' t ht :=
  ⟨s.toS, s.nonDegenerate, rfl⟩

/-- Constructor for the type of non degenerate simplices of a simplicial set. -/
@[simps]
def mk {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) : X.N where
  simplex := x
  nonDegenerate := hx

lemma mk_surjective (x : X.N) :
    ∃ (n : ℕ) (y : X.nonDegenerate n), x = N.mk _ y.prop :=
  ⟨x.dim, ⟨_, x.nonDegenerate⟩, rfl⟩

lemma ext_iff (x y : X.N) :
    x = y ↔ x.toS = y.toS := by
  grind [cases SSet.N]

instance : Preorder X.N := Preorder.lift toS

lemma le_iff {x y : X.N} : x ≤ y ↔ x.subcomplex ≤ y.subcomplex :=
  Iff.rfl

lemma le_iff_exists_mono {x y : X.N} :
    x ≤ y ↔ ∃ (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) (_ : Mono f), X.map f.op y.simplex = x.simplex := by
  simp only [le_iff, CategoryTheory.Subpresheaf.ofSection_le_iff,
    Subcomplex.mem_ofSimplex_obj_iff]
  exact ⟨fun ⟨f, hf⟩ ↦ ⟨f, X.mono_of_nonDegenerate ⟨_, x.nonDegenerate⟩ f _ hf, hf⟩, by tauto⟩

lemma dim_le_of_le {x y : X.N} (h : x ≤ y) : x.dim ≤ y.dim := by
  rw [le_iff_exists_mono] at h
  obtain ⟨f, hf, _⟩ := h
  exact SimplexCategory.len_le_of_mono f

lemma dim_lt_of_lt {x y : X.N} (h : x < y) : x.dim < y.dim := by
  obtain h' | h' := (dim_le_of_le h.le).lt_or_eq
  · exact h'
  · obtain ⟨f, _, hf⟩ := le_iff_exists_mono.1 h.le
    obtain ⟨d, ⟨x, hx⟩, rfl⟩ := x.mk_surjective
    obtain ⟨d', ⟨y, hy⟩, rfl⟩ := y.mk_surjective
    obtain rfl : d = d' := h'
    obtain rfl := SimplexCategory.eq_id_of_mono f
    obtain rfl : y = x := by simpa using hf
    simp at h

instance : PartialOrder X.N where
  le_antisymm x₁ x₂ h h' := by
    obtain ⟨n₁, ⟨x₁, hx₁⟩, rfl⟩ := x₁.mk_surjective
    obtain ⟨n₂, ⟨x₂, hx₂⟩, rfl⟩ := x₂.mk_surjective
    obtain rfl : n₁ = n₂ := le_antisymm (dim_le_of_le h) (dim_le_of_le h')
    rw [le_iff_exists_mono] at h
    obtain ⟨f, hf, h⟩ := h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    aesop

lemma subcomplex_injective {x y : X.N} (h : x.subcomplex = y.subcomplex) :
    x = y := by
  apply le_antisymm
  all_goals
  · rw [le_iff, h]

lemma subcomplex_injective_iff {x y : X.N} :
    x.subcomplex = y.subcomplex ↔ x = y :=
  ⟨subcomplex_injective, by rintro rfl; rfl⟩

lemma eq_iff {x y : X.N} :
    x = y ↔ x.subcomplex = y.subcomplex :=
  ⟨by rintro rfl; rfl, fun h ↦ by simp [le_antisymm_iff, le_iff, h]⟩

section

variable (s : X.N) {d : ℕ} (hd : s.dim = d)

/-- When `s : X.N` is such that `s.dim = d`, this is a term
that is equal to `s`, but whose dimension if definitionally equal to `d`. -/
abbrev cast : X.N where
  toS := s.toS.cast hd
  nonDegenerate := by
    subst hd
    exact s.nonDegenerate

lemma cast_eq_self : s.cast hd = s := by
  subst hd
  rfl

end

end N

/-- The map which sends a non degenerate simplex of a simplicial set to
the subcomplex it generates is an order embedding. -/
@[simps]
def orderEmbeddingN : X.N ↪o X.Subcomplex where
  toFun x := x.subcomplex
  inj' _ _ h := by
    dsimp at h
    apply le_antisymm <;> rw [N.le_iff, h]
  map_rel_iff' := Iff.rfl

namespace S

variable {X}

lemma existsUnique_n (x : X.S) : ∃! (y : X.N), y.subcomplex = x.subcomplex :=
  existsUnique_of_exists_of_unique (by
    obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
    obtain ⟨m, f, _, y, rfl⟩ := X.exists_nonDegenerate x
    refine ⟨N.mk _ y.prop, le_antisymm ?_ ?_⟩
    · simp only [Subcomplex.ofSimplex_le_iff]
      have := isSplitEpi_of_epi f
      have : Function.Injective (X.map f.op) := by
        rw [← mono_iff_injective]
        infer_instance
      refine ⟨(section_ f).op, this ?_⟩
      dsimp
      rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
        ← op_comp, ← op_comp, Category.assoc, IsSplitEpi.id, Category.comp_id]
    · simp only [Subcomplex.ofSimplex_le_iff]
      exact ⟨f.op, rfl⟩)
    (fun y₁ y₂ h₁ h₂ ↦ N.subcomplex_injective (by rw [h₁, h₂]))

/-- This is the non degenerate simplex of a simplicial set which
generates the same subcomplex as a given simplex. -/
noncomputable def toN (x : X.S) : X.N := x.existsUnique_n.exists.choose

@[simp]
lemma subcomplex_toN (x : X.S) : x.toN.subcomplex = x.subcomplex :=
  x.existsUnique_n.exists.choose_spec

lemma toN_eq_iff {x : X.S} {y : X.N} :
    x.toN = y ↔ y.subcomplex = x.subcomplex :=
  ⟨by rintro rfl; simp, fun h ↦ x.existsUnique_n.unique (by simp) h⟩

end S

end SSet
