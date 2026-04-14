/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Simplices

/-!
# The partially ordered type of non degenerate simplices of a simplicial set

In this file, we introduce the partially ordered type `X.N` of
non degenerate simplices of a simplicial set `X`. We obtain
an embedding `X.orderEmbeddingN : X.N ↪o X.Subcomplex` which sends
a non degenerate simplex to the subcomplex of `X` it generates.

Given an arbitrary simplex `x : X.S`, we show that there is a unique
non degenerate `x.toN : X.N` such that `x.toN.subcomplex = x.subcomplex`.

-/

@[expose] public section

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

/-- Induction principle for the type `X.N` of nondegenerate simplices of
a simplicial set `X`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def induction {motive : X.N → Sort*}
    (mk : ∀ (n : ℕ) (x : X.nonDegenerate n), motive (mk x.val x.property)) (s : X.N) :
    motive s :=
  mk s.dim ⟨_, s.nonDegenerate⟩

@[simp]
lemma induction_mk {motive : X.N → Sort*}
    (mk : ∀ (n : ℕ) (x : X.nonDegenerate n), motive (mk x.1 x.2)) {n : ℕ} (s : X.nonDegenerate n) :
  induction (motive := motive) mk (N.mk s.val s.property) = mk n s := rfl

lemma ext_iff (x y : X.N) :
    x = y ↔ x.toS = y.toS := by
  grind [cases SSet.N]

instance : Preorder X.N := Preorder.lift toS

lemma le_iff {x y : X.N} : x ≤ y ↔ x.subcomplex ≤ y.subcomplex :=
  Iff.rfl

lemma lt_iff {x y : X.N} : x < y ↔ x.subcomplex < y.subcomplex :=
  Iff.rfl

lemma le_iff_exists_mono {x y : X.N} :
    x ≤ y ↔ ∃ (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) (_ : Mono f), X.map f.op y.simplex = x.simplex := by
  simp only [le_iff, CategoryTheory.Subfunctor.ofSection_le_iff,
    Subcomplex.mem_ofSimplex_obj_iff]
  exact ⟨fun ⟨f, hf⟩ ↦ ⟨f, X.mono_of_nonDegenerate ⟨_, x.nonDegenerate⟩ f _ hf, hf⟩, by tauto⟩

lemma dim_le_of_le {x y : X.N} (h : x ≤ y) : x.dim ≤ y.dim := by
  rw [le_iff_exists_mono] at h
  obtain ⟨f, hf, _⟩ := h
  exact SimplexCategory.len_le_of_mono f

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

variable (X) in
lemma iSup_subcomplex_eq_top :
    ⨆ (s : X.N), s.subcomplex = ⊤ :=
  le_antisymm (by simp) (by
    rw [← Subcomplex.iSup_ofSimplex_nonDegenerate_eq_top X, iSup_le_iff]
    rintro ⟨d, s, hs⟩
    exact le_trans (by rfl) (le_iSup _ (N.mk _ hs)))

lemma subcomplex_le_iff {A B : X.Subcomplex} :
    A ≤ B ↔ ∀ (s : X.N), s.subcomplex ≤ A → s.subcomplex ≤ B := by
  rw [Subcomplex.le_iff_contains_nonDegenerate]
  refine ⟨fun h s ↦ ?_, fun h n x hx ↦ ?_⟩
  · induction s using N.induction with
    | mk n x =>
      intro hx
      simp only [Subfunctor.ofSection_le_iff, mk_dim, mk_simplex] at hx ⊢
      exact h _ _ hx
  · simpa using h (N.mk _ x.prop) (by simpa)

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

lemma eq_iff_ofSimplex_eq {X : SSet.{u}} {n m : ℕ} (x : X _⦋n⦌) (y : X _⦋m⦌)
    (hx : x ∈ X.nonDegenerate _) (hy : y ∈ X.nonDegenerate _) :
    S.mk x = S.mk y ↔ Subcomplex.ofSimplex x = Subcomplex.ofSimplex y := by
  trans N.mk x hx = N.mk y hy
  · exact (N.ext_iff (N.mk x hx) (N.mk y hy)).symm
  · simp only [le_antisymm_iff]
    rfl

lemma subcomplex_map_le (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌)
    (hf : X.map f.op y.simplex = x.simplex) :
    x.subcomplex ≤ y.subcomplex := by
  simp only [Subcomplex.ofSimplex_le_iff]
  exact ⟨_, hf⟩

lemma subcomplex_eq_of_epi (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Epi f]
    (hf : X.map f.op y.simplex = x.simplex) :
    x.subcomplex = y.subcomplex := by
  refine le_antisymm (subcomplex_map_le x y f hf) ?_
  simp only [Subcomplex.ofSimplex_le_iff]
  have := isSplitEpi_of_epi f
  exact ⟨(section_ f).op, by simp [← hf, ← Functor.map_comp_apply, ← op_comp]⟩

set_option backward.isDefEq.respectTransparency false in
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
      rw [← comp_apply, ← Functor.map_comp, ← comp_apply, ← Functor.map_comp,
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

set_option backward.isDefEq.respectTransparency false in
lemma existsUnique_toNπ {x : X.S} {y : X.N} (hy : x.toN = y) :
    ∃! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Epi f ∧ X.map f.op y.simplex = x.simplex := by
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
  obtain ⟨m, f, _, z, rfl⟩ := X.exists_nonDegenerate x
  obtain rfl : y = N.mk _ z.2 := by
    rw [toN_eq_iff] at hy
    rw [← N.subcomplex_injective_iff, hy]
    exact subcomplex_eq_of_epi _ _ f rfl
  refine existsUnique_of_exists_of_unique ⟨f, inferInstance, rfl⟩
    (fun f₁ f₂ ⟨_, hf₁⟩ ⟨_, hf₂⟩ ↦ unique_nonDegenerate_map _ _ _ _ hf₁.symm _ _ hf₂.symm)

/-- Given a simplex `x : X.S` of a simplicial set `X`, this is the unique
(epi)morphism `f : ⦋x.dim⦌ ⟶ ⦋x.toN.dim⦌` such that `x.simplex` is
`X.map f.op x.toN.simplex` where `x.toN : X.N` is the unique nondegenerate
simplex of `X` which generates the same subcomplex as `x`. -/
@[no_expose] noncomputable def toNπ (x : X.S) : ⦋x.dim⦌ ⟶ ⦋x.toN.dim⦌ :=
  (existsUnique_toNπ rfl).exists.choose

instance (x : X.S) : Epi x.toNπ := (existsUnique_toNπ rfl).exists.choose_spec.1

@[simp]
lemma map_toNπ_op_apply (x : X.S) :
    X.map x.toNπ.op x.toN.simplex = x.simplex := (existsUnique_toNπ rfl).exists.choose_spec.2

lemma dim_toN_le (x : X.S) :
    x.toN.dim ≤ x.dim :=
  SimplexCategory.le_of_epi x.toNπ

end S

end SSet
