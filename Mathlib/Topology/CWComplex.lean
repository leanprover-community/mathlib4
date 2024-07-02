/-
Copyright (c) 2024 Elliot Dean Young and Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia, Elliot Dean Young
-/

import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# CW-complexes

In this file we define a relative CW-complex as the colimit of an expanding sequence of subspaces
`sk i` (called the `i`-skeleta) for `i ≥ -1`, where `sk (-1)` is an arbitrary topological space
and each `sk (n+1)` is obtained from `sk n` by attaching (n+1)-disks.

## References
The definition of CW complexes follows David Wärn's suggestion at
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Do.20we.20have.20CW.20complexes.3F/near/231769080
-/

open CategoryTheory

namespace CWComplex

/-- The n-dimensional sphere is the set of points in ℝ^(n+1) whose norm equals 1, endowed with the
subspace topology. -/
noncomputable def sphere (n : ℤ) : TopCat :=
  TopCat.of <| Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| Int.toNat <| n + 1) 1

/-- The n-dimensional closed disk is the set of points in ℝ^n whose norm is at most 1, endowed with
the subspace topology. -/
noncomputable def disk (n : ℤ) : TopCat :=
  TopCat.of <| Metric.closedBall (0 : EuclideanSpace ℝ <| Fin <| Int.toNat n) 1

/-- `𝕊 n` denotes the n-dimensional sphere. -/
notation "𝕊 "n => sphere n

/-- `𝔻 n` denotes the n-dimensional closed disk. -/
notation "𝔻 "n => disk n

/-- The inclusion map from the n-sphere to the (n+1)-disk -/
def sphereInclusion (n : ℤ) : (𝕊 n) ⟶ (𝔻 n + 1) where
  toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
  continuous_toFun := ⟨fun t ⟨s, hso, hst⟩ ↦ by
    rw [isOpen_induced_iff, ← hst]
    tauto⟩

/-- The inclusion map from the disjoint union of n-spheres to the disjoint union of (n+1)-disks,
where both of the disjoint unions are indexed by `cells` -/
def sigmaSphereInclusion (n : ℤ) (cells : Type) :
    TopCat.of (Σ (_ : cells), 𝕊 n) ⟶ TopCat.of (Σ (_ : cells), 𝔻 n + 1) where
  toFun := Sigma.map id fun _ x ↦ (sphereInclusion n).toFun x
  continuous_toFun := Continuous.sigma_map fun _ ↦ (sphereInclusion n).continuous_toFun

/-- Given an attaching map for each n-sphere, we construct the attaching map for the disjoint
union of the n-spheres. -/
def sigmaAttachMap (X : TopCat) (n : ℤ) (cells : Type) (attach_maps : cells → C(𝕊 n, X)) :
    TopCat.of (Σ (_ : cells), 𝕊 n) ⟶ X where
  toFun := fun ⟨i, x⟩ ↦ attach_maps i x
  continuous_toFun := continuous_sigma fun i ↦ (attach_maps i).continuous_toFun

/-- A type witnessing that X' is obtained from X by attaching (n+1)-disks -/
structure AttachCells (X X' : TopCat) (n : ℤ) where
  /-- The index type over the (n+1)-disks -/
  cells : Type
  /-- For each (n+1)-disk, we have an attaching map from its boundary, namely an n-sphere,
  to `X`. -/
  attach_maps : cells → C(𝕊 n, X)
  /-- X' is the pushout obtained from X along `sigmaAttachMap`. -/
  iso_pushout : X' ≅ Limits.pushout
    (sigmaSphereInclusion n cells) (sigmaAttachMap X n cells attach_maps)

end CWComplex

/-- A relative CW-complex contains an expanding sequence of subspaces `sk i`
(called the `i`-skeleta) for `i ≥ -1`, where `sk (-1)` is an arbitrary topological space,
isomorphic to `A`, and each `sk (n+1)` is obtained from `sk n` by attaching (n+1)-disks. -/
structure RelativeCWComplex (A : TopCat) where
  /-- Skeleta -/
  sk : ℤ → TopCat
  /-- A is isomorphic to the (-1)-skeleton. -/
  iso_sk_neg_one : A ≅ sk (-1)
  /-- The (n+1)-skeleton is obtained from the n-skeleton by attaching (n+1)-disks. -/
  attach_cells : (n : ℤ) → CWComplex.AttachCells (sk n) (sk (n + 1)) n

/-- A CW-complex is a relative CW-complex whose (-1)-skeleton is empty. -/
abbrev CWComplex := RelativeCWComplex (TopCat.of Empty)

namespace CWComplex

noncomputable section Topology

/-- The inclusion map from `X` to `X'`, given that `X'` is obtained from X by attaching
(n+1)-disks -/
def attachCellsInclusion (X X' : TopCat) (n : ℤ) (att : AttachCells X X' n) : X ⟶ X' :=
  @Limits.pushout.inr TopCat _ _ _ X
    (sigmaSphereInclusion n att.cells)
    (sigmaAttachMap X n att.cells att.attach_maps) _ ≫ att.iso_pushout.inv

/-- The inclusion map from the n-skeleton to the (n+1)-skeleton of a relative CW-complex -/
def skeletaInclusion {A : TopCat} (X : RelativeCWComplex A) (n : ℤ) : X.sk n ⟶ X.sk (n + 1) :=
  attachCellsInclusion (X.sk n) (X.sk (n + 1)) n (X.attach_cells n)

/-- The inclusion map from the n-skeleton to the m-skeleton of a relative CW-complex -/
def skeletaInclusion' {A : TopCat} (X : RelativeCWComplex A)
    (n : ℤ) (m : ℤ) (n_le_m : n ≤ m) : X.sk n ⟶ X.sk m :=
  if h : n = m then by
    subst m
    exact 𝟙 (X.sk n)
  else by
    have h' : n < m := Int.lt_iff_le_and_ne.mpr ⟨n_le_m, h⟩
    exact skeletaInclusion X n ≫ skeletaInclusion' X (n + 1) m h'
  termination_by Int.toNat (m - n)
  decreasing_by
    simp_wf
    rw [Int.toNat_of_nonneg (Int.sub_nonneg_of_le h')]
    linarith

/-- The colimit diagram in the definition of a relative CW-complex -/
def colimitDiagram {A : TopCat} (X : RelativeCWComplex A) : ℤ ⥤ TopCat where
  obj := X.sk
  map := @fun n m n_le_m => skeletaInclusion' X n m <| Quiver.Hom.le n_le_m
  map_id := by simp [skeletaInclusion']
  map_comp := by
    let rec p (n m l : ℤ) (n_le_m : n ≤ m) (m_le_l : m ≤ l) (n_le_l : n ≤ l) :
        skeletaInclusion' X n l n_le_l =
        skeletaInclusion' X n m n_le_m ≫
        skeletaInclusion' X m l m_le_l :=
      if hnm : n = m then by
        unfold skeletaInclusion'
        subst hnm
        simp only [eq_mpr_eq_cast, ↓reduceDite, cast_eq, Category.id_comp]
      else by
        have h1 : n < m := Int.lt_iff_le_and_ne.mpr ⟨n_le_m, hnm⟩
        have h2 : n < l := by linarith
        unfold skeletaInclusion'
        simp [hnm, Int.ne_of_lt h2]
        by_cases hml : m = l
        · subst hml
          simp only [↓reduceDite, Category.comp_id]
        congr
        rw [p (n + 1) m l h1 m_le_l h2]
        congr
        simp only [hml, ↓reduceDite]
        conv => lhs; unfold skeletaInclusion'
        simp only [hml, ↓reduceDite]
      termination_by Int.toNat (l - n)
      decreasing_by
        simp_wf
        rw [Int.toNat_of_nonneg (Int.sub_nonneg_of_le h2)]
        linarith
    intro n m l n_le_m m_le_l
    have n_le_m := Quiver.Hom.le n_le_m
    have m_le_l := Quiver.Hom.le m_le_l
    exact p n m l n_le_m m_le_l (Int.le_trans n_le_m m_le_l)

/-- The topology on a relative CW-complex -/
def toTopCat {A : TopCat} (X : RelativeCWComplex A) : TopCat :=
  Limits.colimit (colimitDiagram X)

instance : Coe CWComplex TopCat where coe X := toTopCat X

end Topology
