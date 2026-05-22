/-
Copyright (c) 2026 Matthew Corbelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Corbelli
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Topology.MetricSpace.DirectLimit

/-!
# Direct Limit of normed additive groups

We introduct instances of `NormedAddGroup` and `NormedAddCommGroup` on `DirectLimit`,
under the assumption that the types `T h` that the maps in the directed system come from,
all have instances of `IsometryClass`.
-/

@[expose] public section

namespace DirectLimit

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
variable [IsDirectedOrder ι]
variable [Nonempty ι]

section SeminormedGroup

variable [∀ i, SeminormedGroup (G i)]
variable [∀ i j h, MonoidHomClass (T h) (G i) (G j)]
variable [∀ i j h, IsometryClass (T h) (G i) (G j)]

@[to_additive]
noncomputable instance : SeminormedGroup (DirectLimit G f) where
  norm := DirectLimit.lift f (ih := fun i x ↦ ‖x‖) (fun i j h x ↦ by
    simpa [SeminormedGroup.dist_eq] using (IsometryClass.dist_eq (f i j h) 1 x).symm)
  dist_eq := DirectLimit.induction₂ f (fun i x y ↦ by
    rw [dist_def, SeminormedGroup.dist_eq, inv_def, mul_def, DirectLimit.lift_def])

@[to_additive norm_def]
lemma mul_norm_def (i : ι) (x : G i) : ‖(⟦⟨i, x⟩⟧ : DirectLimit G f)‖ = ‖x‖ := by
  change DirectLimit.lift f (ih := fun i x ↦ ‖x‖) _ ⟦⟨i, x⟩⟧ = ‖x‖
  apply DirectLimit.lift_def

@[to_additive nnnorm_def]
lemma mul_nnnorm_def (i : ι) (x : G i) : ‖(⟦⟨i, x⟩⟧ : DirectLimit G f)‖₊ = ‖x‖₊ := by
  simp_rw [← @norm_toNNReal', mul_norm_def]

@[to_additive enorm_def]
lemma mul_enorm_def (i : ι) (x : G i) : ‖(⟦⟨i, x⟩⟧ : DirectLimit G f)‖ₑ = ‖x‖ₑ := by
  rw [@enorm'_eq_iff_norm_eq,  mul_norm_def]

end SeminormedGroup

section NormedGroup

variable [∀ i, NormedGroup (G i)]
variable [∀ i j h, MonoidHomClass (T h) (G i) (G j)]
variable [∀ i j h, IsometryClass (T h) (G i) (G j)]

@[to_additive]
noncomputable instance : NormedGroup (DirectLimit G f) where
  __ := (inferInstance : SeminormedGroup (DirectLimit G f))
  __ := (inferInstance : MetricSpace (DirectLimit G f))

end NormedGroup

section NormedCommGroup

variable [∀ i, NormedCommGroup (G i)]
variable [∀ i j h, MonoidHomClass (T h) (G i) (G j)]
variable [∀ i j h, IsometryClass (T h) (G i) (G j)]

@[to_additive]
noncomputable instance : NormedCommGroup (DirectLimit G f) where
  __ := (inferInstance : NormedGroup (DirectLimit G f))
  __ := (inferInstance : CommGroup (DirectLimit G f))

end NormedCommGroup

end DirectLimit
