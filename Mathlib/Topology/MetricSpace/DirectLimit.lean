/-
Copyright (c) 2026 Matthew Corbelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Corbelli
-/
module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Topology.MetricSpace.Isometry

@[expose] public section

/-!
Gives an instance of `MetricSpace` on the `DirectLimit` of a directed system of metric spaces,
where all the maps in the directed system are from types satisfying the class `IsometryClass`.
-/

namespace DirectLimit

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
variable [IsDirectedOrder ι]

namespace MetricSpace

variable [∀ i, MetricSpace (G i)]
variable [∀ i j h, IsometryClass (T h) (G i) (G j)]

noncomputable instance : MetricSpace (DirectLimit G f) where
  dist := DirectLimit.lift₂ f f (fun i ↦ dist (α := G i))
    (fun i j h x y ↦ (IsometryClass.dist_eq (f i j h) x y).symm)
  dist_self := by
    apply DirectLimit.induction
    intro i x
    rw [← dist_self x]
    apply DirectLimit.lift₂_def f f (fun i ↦ dist (α := G i) )
      (fun i j h x y ↦ (IsometryClass.dist_eq (f i j h) x y).symm) i x x
  dist_comm := by
    apply DirectLimit.induction₂
    intro i x y
    simp_rw [lift₂_def, dist_comm x y]
  dist_triangle := by
    apply DirectLimit.induction₃
    intro i x y z
    simp_rw [lift₂_def, dist_triangle]
  eq_of_dist_eq_zero := by
    apply DirectLimit.induction₂
    intro i x y
    rw [DirectLimit.lift₂_def]
    intro h
    simp [eq_of_dist_eq_zero h]

lemma dist_def (i : ι) (x y : G i) :
    dist (α := DirectLimit G f) ⟦⟨i,x⟩⟧ ⟦⟨i,y⟩⟧ = dist x y := by
  change DirectLimit.lift₂ f f _
    (fun i j h x y ↦ (IsometryClass.dist_eq (f i j h) x y).symm)
    ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ = dist x y
  rw [lift₂_def]

end MetricSpace

end DirectLimit
