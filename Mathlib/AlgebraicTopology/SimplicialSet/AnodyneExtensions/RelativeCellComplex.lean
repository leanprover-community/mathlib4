/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The relative cell complex attached to a rank function for a pairing

-/

@[expose] public section

universe v u

open CategoryTheory HomotopicalAlgebra Simplicial Limits Opposite

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

lemma filtration_monotone : Monotone f.filtration := by
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
    exact ⟨f.filtration_monotone (Order.le_succ i),
      fun c ↦ f.simplex_le_filtration _ (Order.lt_succ_of_not_isMax hi)⟩

lemma filtration_of_isSuccLimit [OrderBot ι] [SuccOrder ι]
    (i : ι) (hi : Order.IsSuccLimit i) :
    f.filtration i = ⨆ (j : ι) (_ : j < i), f.filtration j := by
  apply le_antisymm
  · rw [filtration]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨?_, fun j hj c ↦ ?_⟩
    · refine le_trans ?_ (le_iSup _ ⊥)
      exact le_trans (by simp) (le_iSup _ hi.bot_lt)
    · refine le_trans ?_ (le_iSup _ (Order.succ j))
      refine le_trans ?_ (le_iSup _
        (by rwa [← Order.IsSuccLimit.succ_lt_iff hi] at hj))
      exact f.simplex_le_filtration _ (Order.lt_succ_of_not_isMax hj.not_isMax)
  · simp only [iSup_le_iff]
    intro j hj
    exact f.filtration_monotone hj.le

lemma iSup_filtration [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι] :
    ⨆ (i : ι), f.filtration i = ⊤ := by
  let B := ⨆ (i : ι), f.filtration i
  suffices ∀ (s : A.N), s.simplex ∈ B.obj _ by
    rw [eq_top_iff_contains_nonDegenerate]
    intro n s hs
    by_cases hs₀ : s ∈ A.obj _
    · exact le_iSup f.filtration ⊥ _ (by rwa [filtration_bot])
    · exact this (N.mk _ hs hs₀)
  suffices ∀ (y : P.II), ofSimplex (P.p y).1.simplex ≤ B by
    intro s
    obtain ⟨y, (rfl | rfl)⟩ := P.exists_or s
    · rw [← Subcomplex.ofSimplex_le_iff]
      refine ((S.le_def ..).1 (P.isUniquelyCodimOneFace y).le).trans (this y)
    · rw [← Subcomplex.ofSimplex_le_iff]
      exact this y
  intro y
  exact le_trans (by simp [Cells.simplex])
    ((f.simplex_le_filtration ⟨y, rfl⟩ (Order.lt_succ (f.rank y))).trans
      (le_iSup f.filtration _))

lemma iSup_filtration_iio [OrderBot ι] [SuccOrder ι] (m : ι) (hm : Order.IsSuccLimit m) :
    ⨆ (i : Set.Iio m), f.filtration i = f.filtration m :=
  le_antisymm (by
    simp only [iSup_le_iff, Subtype.forall, Set.mem_Iio]
    intro j hj
    exact f.filtration_monotone hj.le) (by
    rw [filtration]
    simp only [sup_le_iff, iSup_le_iff, ← f.filtration_bot]
    exact ⟨le_trans (by rfl) (le_iSup _ ⟨⊥, hm.bot_lt⟩), fun j hj c ↦
      (f.simplex_le_filtration c (Order.lt_succ_of_not_isMax (not_isMax_of_lt hj))).trans
        (le_trans (by rfl) (le_iSup _ ⟨Order.succ j, hm.succ_lt_iff.2 hj⟩))⟩)

def Cells.mapToSucc {j : ι} [SuccOrder ι] [NoMaxOrder ι] (c : f.Cells j) :
    Δ[c.dim + 1] ⟶ f.filtration (Order.succ j) :=
  Subcomplex.lift c.map (by
    rw [range_eq_ofSimplex, Cells.map, Equiv.apply_symm_apply]
    exact f.simplex_le_filtration c (Order.lt_succ _))

@[reassoc (attr := simp)]
lemma Cells.mapToSucc_ι {j : ι} [SuccOrder ι] [NoMaxOrder ι] (c : f.Cells j) :
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

instance (j : ι) : Mono (f.m j) :=
  have : (MorphismProperty.monomorphisms
    SSet.{u}).IsStableUnderCoproductsOfShape (f.Cells j) := sorry
  MorphismProperty.colimitsOfShape_le (W := .monomorphisms _) _
    (MorphismProperty.colimitsOfShape_colimMap _ (fun ⟨c⟩ ↦ by
      dsimp only [Discrete.functor_obj_eq_as, Discrete.natTrans_app]
      simp only [MorphismProperty.monomorphisms.iff]
      infer_instance))

@[reassoc (attr := simp)]
lemma Cells.ιSigmaHorn_m {j : ι} (c : f.Cells j) :
    c.ιSigmaHorn ≫ f.m j = c.horn.ι ≫ c.ιSigmaStdSimplex := by
  simp [m]

@[simp]
lemma Cells.preimage_filtration_map {j : ι} (c : f.Cells j) :
    (f.filtration j).preimage c.map = c.horn := sorry

def Cells.mapHorn {j : ι} (c : f.Cells j) : (c.horn : SSet) ⟶ f.filtration j :=
  Subcomplex.lift (c.horn.ι ≫ c.map) (by
    simp [← image_top, image_le_iff, preimage_comp, c.preimage_filtration_map])

@[reassoc (attr := simp)]
lemma Cells.mapHorn_ι {j : ι} (c : f.Cells j) :
    c.mapHorn ≫ (f.filtration j).ι = c.horn.ι ≫ c.map := rfl

noncomputable def t (j : ι) : f.sigmaHorn j ⟶ f.filtration j :=
  Limits.Sigma.desc (fun c ↦ c.mapHorn)

@[reassoc (attr := simp)]
lemma Cells.ιSigmaHorn_t {j : ι} (c : f.Cells j) :
    c.ιSigmaHorn ≫ f.t j = c.mapHorn:= by
  simp [t]

variable [SuccOrder ι] [NoMaxOrder ι]

noncomputable def b (j : ι) :
    f.sigmaStdSimplex j ⟶ f.filtration (Order.succ j) :=
  Sigma.desc (fun c ↦ c.mapToSucc)

@[reassoc (attr := simp)]
lemma ι_b {j : ι} (c : f.Cells j) :
    c.ιSigmaStdSimplex ≫ f.b j = c.mapToSucc := by simp [b]

@[reassoc]
lemma w (j : ι) :
    f.t j ≫ homOfLE (f.filtration_monotone (Order.le_succ j)) = f.m j ≫ f.b j := by
  ext c : 1
  simp [← cancel_mono (Subcomplex.ι _)]

lemma isPullback (j : ι) (hj : ¬ IsMax j) :
    IsPullback (f.t j) (f.m j)
      (homOfLE (f.filtration_monotone (Order.le_succ j))) (f.b j) where
  w := f.w j
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun ⟨d⟩ ↦ by
    refine (isLimitMapConePullbackConeEquiv _ _).2
      (IsPullback.isLimit ?_)
    induction d using SimplexCategory.rec with | _ d
    rw [Types.isPullback_iff]
    dsimp
    refine ⟨congr_app (f.w j) (op ⦋d⦌), ?_, ?_⟩
    · intro a₁ a₂ ⟨ht, hm⟩
      have : Mono (f.m j) := inferInstance
      rw [NatTrans.mono_iff_mono_app] at this
      exact (mono_iff_injective _).1 (this _) hm
    · sorry
    )⟩

#exit
lemma isPushout (j : ι) (hj : ¬ IsMax j) :
    IsPushout (f.t j) (f.m j)
      (homOfLE (f.filtration_monotone (Order.le_succ j))) (f.b j) where
  w := f.w j
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨d⟩ ↦ by
    induction d using SimplexCategory.rec with | _ d
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).2
      (IsPushout.isColimit ?_)
    dsimp
    refine Limits.Types.isPushout_of_isPullback_of_mono'
      ((f.isPullback j hj).map ((CategoryTheory.evaluation _ _).obj (op ⦋d⦌)))
      sorry sorry
    )⟩

end

variable [SuccOrder ι] [OrderBot ι] [NoMaxOrder ι] [WellFoundedLT ι]

instance : f.filtration_monotone.functor.IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨Preorder.isColimitOfIsLUB _ _ (by
    dsimp
    rw [← f.iSup_filtration_iio m hm]
    apply isLUB_iSup)⟩

noncomputable def relativeCellComplex : RelativeCellComplex f.basicCell A.ι where
  F := f.filtration_monotone.functor ⋙ Subcomplex.toSSetFunctor
  isoBot := Subcomplex.eqToIso (filtration_bot _)
  isColimit :=
    IsColimit.ofIsoColimit (isColimitOfPreserves Subcomplex.toSSetFunctor
      (Preorder.colimitCoconeOfIsLUB f.filtration_monotone.functor (pt := ⊤)
        (by rw [← f.iSup_filtration]; apply isLUB_iSup)).isColimit)
        (Cocones.ext (Subcomplex.topIso _))
  isWellOrderContinuous :=
    ⟨fun m hm ↦ ⟨isColimitOfPreserves Subcomplex.toSSetFunctor
      (Functor.isColimitOfIsWellOrderContinuous f.filtration_monotone.functor m hm)⟩⟩
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
