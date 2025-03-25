/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Yaël Dillies
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.OrdContinuous
import Mathlib.Topology.Order.Basic

/-!
# Order-continuity of left and right adjoints in Galois connections

This file contains the results that left/right adjoints in Galois connections are
left/right-continuous.

## Main results

 * `GaloisConnection.leftOrdContinuous`: A left adjoint is left-order-continuous.
 * `GaloisConnection.rightOrdContinuous`: A right adjoint is right-order-continuous.
 * `LeftOrdContinuous.continuousWithinAt_Iic`: A left-order-continuous function between
   conditionally complete linear orders is topologically left-continuous.
 * `RightOrdContinuous.continuousWithinAt_Ici`: A right-order-continuous function between
   conditionally complete linear orders is topologically right-continuous.
-/

open scoped CategoryTheory

open CategoryTheory Set Filter

section Preorder

variable {X Y : Type*} [Preorder X] [Preorder Y]

/-- An adjunction between preorder categories is a Galois connection. -/
lemma CategoryTheory.Adjunction.galoisConnection {F : X ⥤ Y} {G : Y ⥤ X} (adj : F ⊣ G):
    GaloisConnection F.obj G.obj :=
  fun x y ↦ ⟨fun Fx_le_y ↦ leOfHom <| adj.homEquiv x y Fx_le_y.hom,
             fun x_le_Gy ↦ leOfHom <| (adj.homEquiv x y).symm x_le_Gy.hom⟩

/-- A left adjoint in a Galois connection is left-continuous in the order-theoretic sense. -/
lemma GaloisConnection.leftOrdContinuous {f : X → Y} {g : Y → X} (gc : GaloisConnection f g) :
    LeftOrdContinuous f := by
  intro s a ⟨a_ub_s, a_le_ub_s⟩
  refine ⟨?_, ?_⟩
  · intro y ⟨x, x_in_s, fx_eq_y⟩
    simpa [← fx_eq_y] using monotone_l gc <| a_ub_s x_in_s
  · intro b b_ub_s
    rw [gc]
    exact a_le_ub_s fun z z_in_s ↦ by simpa [← gc _ _] using b_ub_s <| mem_image_of_mem f z_in_s

/-- A right adjoint in a Galois connection is right-continuous in the order-theoretic sense. -/
lemma GaloisConnection.rightOrdContinuous {f : X → Y} {g : Y → X} (gc : GaloisConnection f g) :
    RightOrdContinuous g := by
  apply leftOrdContinuous (X := Yᵒᵈ) (Y := Xᵒᵈ) (f := g) (g := f)
  · exact fun _ _ ↦ (le_iff_le gc).symm

end Preorder

section ConditionallyCompleteLinearOrder

variable {X : Type*} [ConditionallyCompleteLinearOrder X] [DenselyOrdered X]
variable [TopologicalSpace X] [OrderTopology X]
variable {Y : Type*} [ConditionallyCompleteLinearOrder Y] [TopologicalSpace Y] [OrderTopology Y]
variable {f : X → Y}

/-- An order-theoretically left-continuous function is topologically left-continuous, assuming
the function is between conditionally complete linear orders with order topologies, and the domain
is densely ordered. -/
lemma LeftOrdContinuous.continuousWithinAt_Iic (f_loc : LeftOrdContinuous f) (x : X) :
    ContinuousWithinAt f (Iic x) x := by
  rw [ContinuousWithinAt, OrderTopology.topology_eq_generate_intervals (α := Y)]
  simp_rw [TopologicalSpace.tendsto_nhds_generateFrom_iff, mem_nhdsWithin]
  intro V ⟨z, hV⟩ x_in_V
  rcases hV with V_eq | V_eq
  · -- The case `V = Ioi z`.
    rw [V_eq] at x_in_V ⊢
    by_cases Iio_empty : Iio x = ∅
    · refine ⟨univ, isOpen_univ, mem_univ x, ?_⟩
      intro a ha
      simp only [univ_inter, mem_Iic, mem_preimage, mem_Iio, mem_Ioi] at ha ⊢
      have a_eq_x : a = x :=
        le_antisymm ha (le_of_not_lt <| fun con ↦ by simp [← mem_Iio, Iio_empty] at con)
      simpa [a_eq_x] using x_in_V
    have Iio_nonempty : (Iio x).Nonempty := nonempty_iff_ne_empty.mpr Iio_empty
    have Iio_bdd_above : BddAbove (Iio x) := ⟨x, fun _ h ↦ h.le⟩
    obtain ⟨f_sup_ub, f_sup_lub⟩ := f_loc <| isLUB_csSup (s := Iio x) Iio_nonempty Iio_bdd_above
    have x_eq : x = sSup (Iio x) := by
      apply le_antisymm _ (csSup_le Iio_nonempty fun _ h ↦ le_of_lt h)
      apply (le_csSup_iff ⟨x, fun _ h ↦ h.le⟩ Iio_nonempty).mpr fun b hb ↦ ?_
      by_contra con
      obtain ⟨a, b_lt_a, a_lt_x⟩ := exists_between (not_le.mp con)
      simpa using lt_of_lt_of_le b_lt_a (mem_upperBounds.mp hb a a_lt_x)
    rw [← x_eq] at f_sup_ub f_sup_lub
    have key : sSup (f '' Iio x) > z := by
      apply lt_of_lt_of_le x_in_V (f_sup_lub fun y hy ↦ ?_)
      obtain ⟨c, c_lt_x, fc_eq_y⟩ := (mem_image ..).mp hy
      simpa [← fc_eq_y] using le_csSup (by use f x) <| mem_image_of_mem f c_lt_x
    obtain ⟨b, hb, z_lt_b⟩ :=
      (lt_csSup_iff (Monotone.map_bddAbove f_loc.mono Iio_bdd_above)
      (Nonempty.image f Iio_nonempty)).mp key
    obtain ⟨a, a_lt_x, fa_eq_b⟩ := (mem_image ..).mp hb
    refine ⟨Ioi a, isOpen_Ioi, a_lt_x, ?_⟩
    intro c ⟨a_lt_c, c_le_x⟩
    simp only [mem_preimage, mem_Ioi, gt_iff_lt, mem_Ioi, mem_Iic, mem_Iio] at *
    apply lt_of_lt_of_le z_lt_b (by simpa [← fa_eq_b] using f_loc.mono a_lt_c.le)
  · -- The case `V = Iio z`.
    rw [V_eq] at x_in_V ⊢
    refine ⟨univ, isOpen_univ, by trivial, ?_⟩
    intro a ha
    exact lt_of_le_of_lt (f_loc.mono (show a ≤ x by simpa using ha)) x_in_V

/-- An order-theoretically right-continuous function is topologically right-continuous, assuming
the function is between conditionally complete linear orders with order topologies, and the domain
is densely ordered. -/
lemma RightOrdContinuous.continuousWithinAt_Ici (f_roc : RightOrdContinuous f) (x : X) :
    ContinuousWithinAt f (Ici x) x :=
  LeftOrdContinuous.continuousWithinAt_Iic (X := Xᵒᵈ) (Y := Yᵒᵈ) f_roc x

end ConditionallyCompleteLinearOrder
