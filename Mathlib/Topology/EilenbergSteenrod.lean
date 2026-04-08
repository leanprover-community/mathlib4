/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/

module

public import Mathlib
public import Mathlib.Topology.Category.TopPair

@[expose] public section

open CategoryTheory

universe u v

variable (Hₚ : ℕ → TopPair ⥤ Ab) (H : ℕ → TopCat ⥤ Ab) (H_incl_Hₚ : ∀ n : ℕ, H n ≅ TopPair.incl ⋙ Hₚ n)
  (δ : (Π m n, (Hₚ m) ⟶ TopPair.proj₂ ⋙ H n))

def pairSeq (X : TopPair) (n : ℕ) := ComposableArrows.mk₄ ((Hₚ (n + 1)).map X.j)
    ((δ (n + 1) n).app X) ((H n).map X.map) (((H_incl_Hₚ n).app X.fst).hom ≫ (Hₚ n).map X.j)

-- TODO: define complements in a toppair, make U toppair
-- def excisionIncl (U : Set X.fst) : (TopPair.mk ⟨↑Uᶜ⟩ ⟨↑(X.map ⁻¹' U)ᶜ⟩
--     ⟨X.map.hom.restrictPreimage Uᶜ⟩ (Set.restrictPreimage_isInducing Uᶜ X.isInducing_map)) ⟶ X where
--   fst := ⟨ContinuousMap.mk Subtype.val⟩
--   snd := ⟨ContinuousMap.mk Subtype.val⟩

structure IsExtraordinaryEilenbergSteenrod : Prop where
  hδ : ∀ n m : ℕ, m ≠ n + 1 → δ m n = 0
  homotopy {X Y : TopPair} (f g : X ⟶ Y) (hfg : TopPair.Homotopic f g): ∀ (n : ℕ), (Hₚ n).map f = (Hₚ n).map g
  -- excision {X : TopPair} (U : Set X.fst) (hU : closure U ⊆ interior (Set.range X.map)) :
  --     ∀ n : ℕ, IsIso ((Hₚ n).map sorry)
  additivity (J : Type u) : ∀ (n : ℕ), Limits.PreservesColimitsOfShape (Discrete J) (H n)
  exact (X : TopPair) : ∀ (n : ℕ), ComposableArrows.Exact (pairSeq Hₚ H H_incl_Hₚ δ X n)

structure IsEilenbergSteenrod extends IsExtraordinaryEilenbergSteenrod Hₚ H H_incl_Hₚ δ where
  dimension : ∀ (n : ℕ) (hn : n ≠ 0), Limits.IsZero ((H n).obj (TopCat.of PUnit))

def IsExtraordinaryEilenbergSteenrod' := IsExtraordinaryEilenbergSteenrod Hₚ (fun n ↦ TopPair.incl ⋙ (Hₚ n)) (fun n ↦ Iso.refl _) sorry --(fun m n ↦ δ m n ≫ ((H_incl_Hₚ n).app X.fst).hom)

def IsEilenbergSteenrod' := @IsEilenbergSteenrod Hₚ (fun n ↦ TopPair.incl ⋙ (Hₚ n)) (fun n ↦ Iso.refl _) sorry --(fun m n ↦ δ m n ≫ ((H_incl_Hₚ n).app X.fst).hom)

-- TODO: HP ≅ HP' → E-S HP ↔ E-S HP'
