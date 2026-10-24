/-
Copyright (c) 2026 Matthew Corbelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Corbelli
-/
module

public import Mathlib.Analysis.Normed.Group.DirectLimit
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Direct Limit of normed rings

We introduct instances of `NormedRing` and `NonUnitalNormedRing` on `DirectLimit`,
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

section NonUnitalNormedRing

variable [∀ i, NonUnitalNormedRing (G i)]
variable [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable [∀ i j h, IsometryClass (T h) (G i) (G j)]

noncomputable instance : NonUnitalNormedRing (DirectLimit G f) where
  __ := (inferInstance : NormedAddCommGroup (DirectLimit G f))
  __ := (inferInstance : NonUnitalRing (DirectLimit G f))
  norm_mul_le := DirectLimit.induction₂ f
    fun i x y ↦ by simp_rw [mul_def, norm_def]; exact norm_mul_le x y

end NonUnitalNormedRing

section NormedRing

variable [∀ i, NormedRing (G i)]
variable [∀ i j h, RingHomClass (T h) (G i) (G j)]
variable [∀ i j h, IsometryClass (T h) (G i) (G j)]

noncomputable instance : NormedRing (DirectLimit G f) where
  __ := (inferInstance : Ring (DirectLimit G f))
  __ := (inferInstance : NonUnitalNormedRing (DirectLimit G f))

end NormedRing


end DirectLimit
