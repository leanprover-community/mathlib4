/-
Copyright (c) 2026 Matthew Corbelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Corbelli
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Topology.MetricSpace.DirectLimit

@[expose] public section

/-!
# Direct Limit of normed additive groups

We introduct instances of `NormedAddGroup` and `NormedAddCommGroup` on `DirectLimit`,
under the assumption that the types `T h` that the maps in the directed system come from,
all have instances of `IsometryClass`.
-/

namespace DirectLimit

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
variable [IsDirectedOrder ι]
variable [Nonempty ι]

namespace NormedAddGroup

variable [∀ i, NormedAddGroup (G i)]
variable [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]
variable [∀ i j h, IsometryClass (T h) (G i) (G j)]

noncomputable instance instNormedAddGroup : NormedAddGroup (DirectLimit G f) where
  norm := DirectLimit.lift f (ih := fun i x ↦ ‖x‖) (fun i j h x ↦ by
    simpa [NormedAddGroup.dist_eq] using (IsometryClass.dist_eq (f i j h) 0 x).symm)
  dist_eq := DirectLimit.induction₂ f (fun i x y ↦ by
    rw [MetricSpace.dist_def, NormedAddGroup.dist_eq, neg_def, add_def, DirectLimit.lift_def])

lemma norm_def (i : ι) (x : G i) : ‖(⟦⟨i, x⟩⟧ : DirectLimit G f)‖ = ‖x‖ := by
  change DirectLimit.lift f (ih := fun i x ↦ ‖x‖) _ ⟦⟨i, x⟩⟧ = ‖x‖
  apply DirectLimit.lift_def

end NormedAddGroup

namespace NormedAddCommGroup

variable [∀ i, NormedAddCommGroup (G i)]
variable [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]
variable [∀ i j h, IsometryClass (T h) (G i) (G j)]

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (DirectLimit G f) where
  __ := NormedAddGroup.instNormedAddGroup
  __ := (inferInstance : AddCommGroup (DirectLimit G f))

end NormedAddCommGroup

end DirectLimit
