/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# The relative cell complex attached to a rank function for a pairing

-/

universe v u

open CategoryTheory HomotopicalAlgebra Simplicial Limits

namespace SSet.Subcomplex.Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} {P : A.Pairing}

namespace RankFunction

variable [P.IsProper] {ι : Type v} [LinearOrder ι] (f : P.RankFunction ι)

def Cells (i : ι) : Type u := { s : P.II // f.rank s = i }

namespace Cells

variable {f} {i : ι} (c : f.Cells i)

abbrev dim : ℕ := c.1.1.dim

noncomputable def index : Fin (c.dim + 2) :=
  (P.isUniquelyCodimOneFace c.1).index rfl

protected noncomputable def horn :
    (Δ[c.dim + 1] : SSet.{u}).Subcomplex :=
  SSet.horn _ c.index

abbrev cast : A.N := (P.p c.1).1.cast (P.isUniquelyCodimOneFace c.1).dim_eq

abbrev simplex : X _⦋c.dim + 1⦌ := c.cast.simplex

abbrev map {j : ι} (c : f.Cells j) :
    Δ[c.dim + 1] ⟶ X :=
  yonedaEquiv.symm c.simplex

end Cells

noncomputable abbrev basicCell (i : ι) (c : f.Cells i) := c.horn.ι

def filtration (i : ι) : X.Subcomplex :=
  A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cells j), .ofSimplex c.simplex

lemma simplex_le_filtration {j : ι} (c : f.Cells j) {i : ι} (h : j < i) :
    Subcomplex.ofSimplex c.simplex ≤ f.filtration i := by
  refine le_trans ?_ le_sup_right
  refine le_trans ?_ (le_iSup _ j)
  refine le_trans ?_ (le_iSup _ h)
  exact le_trans (by rfl) (le_iSup _ c)

@[simp]
lemma le_filtration (i : ι) : A ≤ f.filtration i := le_sup_left

lemma filtration_bot [OrderBot ι] : f.filtration ⊥ = A := by
  simp [filtration]

lemma monotone_filtration : Monotone f.filtration := by
  intro i₁ i₂ h
  rw [filtration]
  simp only [sup_le_iff, iSup_le_iff, le_filtration, true_and]
  intro j hj c
  exact f.simplex_le_filtration c (lt_of_lt_of_le hj h)

lemma filtration_succ [SuccOrder ι] (i : ι) (hi : ¬ IsMax i) :
    f.filtration (Order.succ i) =
      f.filtration i ⊔ ⨆ (c : f.Cells i), .ofSimplex c.simplex := by
  apply le_antisymm
  · rw [filtration]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨(f.le_filtration _).trans le_sup_left, fun j hj c ↦ ?_⟩
    rw [Order.lt_succ_iff_of_not_isMax hi] at hj
    obtain hj | rfl := hj.lt_or_eq
    · exact (f.simplex_le_filtration _ hj).trans le_sup_left
    · exact le_trans (le_trans (by rfl) (le_iSup _ c)) le_sup_right
  · simp only [sup_le_iff, iSup_le_iff]
    exact ⟨f.monotone_filtration (Order.le_succ i),
      fun c ↦ f.simplex_le_filtration _ (Order.lt_succ_of_not_isMax hi)⟩

lemma filtration_of_isSuccLimit [OrderBot ι] [SuccOrder ι]
    (i : ι) (hi : Order.IsSuccLimit i) :
    f.filtration i = ⨆ (j : ι) (_ : j < i), f.filtration j := by
  apply le_antisymm
  · rw [filtration]
    simp only [sup_le_iff, iSup_le_iff]
    constructor
    · refine le_trans ?_ (le_iSup _ ⊥)
      exact le_trans (by simp) (le_iSup _ hi.bot_lt)
    · intro j hj c
      refine le_trans ?_ (le_iSup _ (Order.succ j))
      refine le_trans ?_ (le_iSup _
        (by rwa [← Order.IsSuccLimit.succ_lt_iff hi] at hj))
      exact f.simplex_le_filtration _ (Order.lt_succ_of_not_isMax hj.not_isMax)
  · simp only [iSup_le_iff]
    intro j hj
    exact f.monotone_filtration hj.le

lemma filtration_le_iSup (i : ι) :
    f.filtration i ≤ ⨆ (i : ι), f.filtration i :=
  le_iSup _ i

lemma iSup_filtration [OrderBot ι] :
    ⨆ (i : ι), f.filtration i = ⊤ := by
  let B := ⨆ (i : ι), f.filtration i
  suffices ∀ (s : A.N), s.simplex ∈ B.obj _ by
    rw [eq_top_iff_contains_nonDegenerate]
    intro n s hs
    by_cases hs₀ : s ∈ A.obj _
    · exact f.filtration_le_iSup ⊥ _ (by rwa [filtration_bot])
    · exact this (N.mk _ hs hs₀)
  intro s
  obtain ⟨y, (rfl | rfl)⟩ := P.exists_or s
  · sorry
  · sorry

def Cells.mapToSucc {j : ι} [SuccOrder ι] (c : f.Cells j) :
    Δ[c.dim + 1] ⟶ f.filtration (Order.succ j) :=
  Subcomplex.lift c.map (by
    sorry)

@[reassoc (attr := simp)]
lemma Cells.mapToSucc_ι {j : ι} [SuccOrder ι] (c : f.Cells j) :
    c.mapToSucc ≫ (f.filtration (Order.succ j)).ι = c.map :=
  rfl

section

noncomputable abbrev sigmaHorn (j : ι) := ∐ (fun (c : f.Cells j) ↦ (c.horn : SSet))

noncomputable abbrev Cells.ιSigmaHorn {j : ι} (c : f.Cells j) :
    (c.horn : SSet) ⟶ f.sigmaHorn j :=
  Sigma.ι (fun (c : f.Cells j) ↦ (c.horn : SSet)) c

noncomputable abbrev sigmaStdSimplex (j : ι) := ∐ (fun (i : f.Cells j) ↦ Δ[i.dim + 1])

noncomputable abbrev Cells.ιSigmaStdSimplex {j : ι} (c : f.Cells j) :
    Δ[c.dim + 1] ⟶ f.sigmaStdSimplex j :=
  Sigma.ι (fun (c : f.Cells j) ↦ Δ[c.dim + 1]) c

noncomputable def m (j : ι) : f.sigmaHorn j ⟶ f.sigmaStdSimplex j :=
  Limits.Sigma.map (basicCell _ _)

@[reassoc (attr := simp)]
lemma Cells.ιSigmaHorn_m {j : ι} (c : f.Cells j) :
    c.ιSigmaHorn ≫ f.m j = c.horn.ι ≫ c.ιSigmaStdSimplex:= by
  simp [m]

noncomputable def t (j : ι) : f.sigmaHorn j ⟶ f.filtration j :=
  sorry

variable [SuccOrder ι]

noncomputable def b (j : ι) :
    f.sigmaStdSimplex j ⟶ f.filtration (Order.succ j) :=
  Sigma.desc (fun c ↦ c.mapToSucc)

lemma isPushout (j : ι) (hj : ¬ IsMax j) :
    IsPushout (f.t j) (f.m j)
      (homOfLE (f.monotone_filtration (Order.le_succ j))) (f.b j) := by
  sorry

end

variable [SuccOrder ι] [OrderBot ι] [WellFoundedLT ι]

noncomputable def relativeCellComplex : RelativeCellComplex f.basicCell A.ι where
  F := f.monotone_filtration.functor ⋙ Subcomplex.toSSetFunctor
  isoBot := Subcomplex.isoOfEq (filtration_bot _)
  isColimit := sorry
  isWellOrderContinuous := sorry
  incl.app i := (f.filtration i).ι
  attachCells j hj :=
    { ι := f.Cells j
      π := id
      cofan₁ := _
      cofan₂ := _
      isColimit₁ := colimit.isColimit _
      isColimit₂ := colimit.isColimit _
      m := f.m j
      hm c := c.ιSigmaHorn_m
      g₁ := f.t j
      g₂ := f.b j
      isPushout := f.isPushout j hj }

end RankFunction

end SSet.Subcomplex.Pairing
