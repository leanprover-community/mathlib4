/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Dimension of a simplicial set

For a simplicial set `X` and `d : ℕ`, we introduce a typeclass
`X.HasDimensionLT d` saying that the dimension of `X` is `< d`,
i.e. all nondegenerate simplices of `X` are of dimension `< d`.

-/

@[expose] public section

universe u

open CategoryTheory Opposite Simplicial

namespace SSet

/-- A simplicial set `X` has dimension `< d` iff for any `n : ℕ`
such that `d ≤ n`, all `n`-simplices are degenerate. -/
@[mk_iff]
class HasDimensionLT (X : SSet.{u}) (d : ℕ) : Prop where
  degenerate_eq_top (n : ℕ) (hn : d ≤ n) : X.degenerate n = ⊤

/-- A simplicial set has dimension `≤ d` if it has dimension `< d + 1`. -/
abbrev HasDimensionLE (X : SSet.{u}) (d : ℕ) := X.HasDimensionLT (d + 1)

section

variable (X : SSet.{u}) (d : ℕ) [X.HasDimensionLT d] (n : ℕ)

lemma degenerate_eq_top_of_hasDimensionLT (hn : d ≤ n) : X.degenerate n = ⊤ :=
  HasDimensionLT.degenerate_eq_top n hn

lemma nonDegenerate_eq_bot_of_hasDimensionLT (hn : d ≤ n) : X.nonDegenerate n = ⊥ := by
  simp [nonDegenerate, X.degenerate_eq_top_of_hasDimensionLT d n hn]

lemma dim_lt_of_nonDegenerate {n : ℕ} (x : X.nonDegenerate n) (d : ℕ)
    [X.HasDimensionLT d] : n < d := by
  by_contra!
  obtain ⟨x, hx⟩ := x
  simp [X.nonDegenerate_eq_bot_of_hasDimensionLT d n this] at hx

lemma dim_le_of_nonDegenerate {n : ℕ} (x : X.nonDegenerate n) (d : ℕ)
    [X.HasDimensionLE d] : n ≤ d :=
  Nat.le_of_lt_succ (X.dim_lt_of_nonDegenerate x (d + 1))

lemma hasDimensionLT_of_le (hn : d ≤ n := by lia) : HasDimensionLT X n where
  degenerate_eq_top i hi :=
    X.degenerate_eq_top_of_hasDimensionLT d i (hn.trans hi)

instance [HasDimensionLT X n] (k : ℕ) : HasDimensionLT X (n + k) :=
  X.hasDimensionLT_of_le n _

end

namespace Subcomplex

variable {X : SSet.{u}}

instance (d : ℕ) [X.HasDimensionLT d] (A : X.Subcomplex) : HasDimensionLT A d where
  degenerate_eq_top (n : ℕ) (hd : d ≤ n) := by
    ext x
    simp [A.mem_degenerate_iff, X.degenerate_eq_top_of_hasDimensionLT d n hd]

lemma le_iff_of_hasDimensionLT (A B : X.Subcomplex) (d : ℕ) [X.HasDimensionLT d] :
    A ≤ B ↔ ∀ i < d, A.obj _ ∩ X.nonDegenerate i ⊆ B.obj (op ⦋i⦌) := by
  refine ⟨fun h i hi a ⟨ha, _⟩ ↦ h _ ha, fun h ↦ ?_⟩
  rw [le_iff_contains_nonDegenerate]
  rintro n x hx
  exact h _ (X.dim_lt_of_nonDegenerate x d) ⟨hx, x.prop⟩

lemma eq_top_iff_of_hasDimensionLT (A : X.Subcomplex) (d : ℕ) [X.HasDimensionLT d] :
    A = ⊤ ↔ ∀ i < d, X.nonDegenerate i ⊆ A.obj _ := by
  simp [← top_le_iff, le_iff_of_hasDimensionLT ⊤ A d]

end Subcomplex

lemma hasDimensionLT_of_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (d : ℕ)
    [Y.HasDimensionLT d] : X.HasDimensionLT d where
  degenerate_eq_top n hn := by
    ext x
    rw [← degenerate_iff_of_isIso (Subcomplex.toRange f),
      Subcomplex.mem_degenerate_iff, Y.degenerate_eq_top_of_hasDimensionLT d n hn]
    simp

lemma Subcomplex.hasDimensionLT_of_le
    {X : SSet.{u}} {A B : X.Subcomplex} (h : A ≤ B) (d : ℕ) [HasDimensionLT B d] :
    HasDimensionLT A d :=
  hasDimensionLT_of_mono (Subcomplex.homOfLE h) d

lemma hasDimensionLT_of_epi {X Y : SSet.{u}} (f : X ⟶ Y) [Epi f] (d : ℕ)
    [X.HasDimensionLT d] : Y.HasDimensionLT d where
  degenerate_eq_top n hn := by
    ext y
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    obtain ⟨x, rfl⟩ := epi_iff_surjective (f := (f.app (op ⦋n⦌))).1 inferInstance y
    apply degenerate_app_apply
    simp [X.degenerate_eq_top_of_hasDimensionLT d n hn]

lemma hasDimensionLT_iff_of_iso {X Y : SSet.{u}} (e : X ≅ Y) (d : ℕ) :
    X.HasDimensionLT d ↔ Y.HasDimensionLT d :=
  ⟨fun _ ↦ hasDimensionLT_of_epi e.hom d, fun _ ↦ hasDimensionLT_of_epi e.inv d⟩

instance {X Y : SSet.{u}} (f : X ⟶ Y) (d : ℕ) [X.HasDimensionLT d] :
    HasDimensionLT (Subcomplex.range f) d :=
  hasDimensionLT_of_epi (Subcomplex.toRange f) d

lemma hasDimensionLT_iSup_iff {X : SSet.{u}} {ι : Type*} (A : ι → X.Subcomplex) (d : ℕ) :
    HasDimensionLT (⨆ i, A i :) d ↔ ∀ i, HasDimensionLT (A i) d := by
  simp only [hasDimensionLT_iff, Subcomplex.degenerate_eq_top_iff]
  aesop

lemma hasDimensionLT_subcomplex_top_iff (X : SSet.{u}) (d : ℕ) :
    HasDimensionLT (⊤ : X.Subcomplex) d ↔ X.HasDimensionLT d :=
  hasDimensionLT_iff_of_iso (Subcomplex.topIso X) _

instance {X : SSet.{u}} (n : ℕ) : HasDimensionLT (⊥ : X.Subcomplex) n where
  degenerate_eq_top k hk := by
    ext ⟨x, hx⟩
    simp at hx

end SSet
