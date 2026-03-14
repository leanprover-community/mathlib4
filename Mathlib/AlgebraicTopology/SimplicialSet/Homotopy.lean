/-
Copyright (c) 2026 ...
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
import Mathlib.AlgebraicTopology.SimplicialObject.SimplicialHomotopy

/-!
# Homotopies via the cylinder `X ⊗ Δ[1]`

A cylinder-style notion of simplicial homotopy for simplicial sets:
a map `X ⊗ Δ[1] ⟶ Y` restricting to `f` and `g` at the endpoints.

In this file we package the cylinder data and provide a (combinatorial) simplicial homotopy
`CategoryTheory.SimplicialHomotopy f g`.
-/

open CategoryTheory Simplicial MonoidalCategory Opposite

namespace SSet

universe u

variable {X Y : SSet.{u}} (f g : X ⟶ Y)

/-!
## Endpoint maps for `Δ[1]`
-/

namespace stdSimplex

/-- The “0-endpoint” map `Δ[0] ⟶ Δ[1]` (vertex `0`). -/
noncomputable def ι₀ : (Δ[0] : SSet.{u}) ⟶ Δ[1] :=
  SSet.stdSimplex.map (SimplexCategory.δ (n := 0) (1 : Fin 2))

/-- The “1-endpoint” map `Δ[0] ⟶ Δ[1]` (vertex `1`). -/
noncomputable def ι₁ : (Δ[0] : SSet.{u}) ⟶ Δ[1] :=
  SSet.stdSimplex.map (SimplexCategory.δ (n := 0) (0 : Fin 2))

end stdSimplex

/-!
## Endpoint restrictions for a cylinder map
-/

/-- Given `H : X ⊗ Δ[1] ⟶ Y`, its 0-end restriction `X ⟶ Y`. -/
noncomputable def cylinderHomotopy.left (H : X ⊗ Δ[1] ⟶ Y) : X ⟶ Y :=
  SSet.ι₀ (X := X) ≫ H

/-- Given `H : X ⊗ Δ[1] ⟶ Y`, its 1-end restriction `X ⟶ Y`. -/
noncomputable def cylinderHomotopy.right (H : X ⊗ Δ[1] ⟶ Y) : X ⟶ Y :=
  SSet.ι₁ (X := X) ≫ H

/-!
## Cylinder homotopies (structure)
-/

/--
A cylinder homotopy from `f` to `g` is a map `H : X ⊗ Δ[1] ⟶ Y` whose endpoint restrictions
are `f` and `g`.
-/
structure CylinderHomotopy (f g : X ⟶ Y) where
  hom : X ⊗ Δ[1] ⟶ Y
  left'  : cylinderHomotopy.left (X := X) (Y := Y) hom = f
  right' : cylinderHomotopy.right (X := X) (Y := Y) hom = g

attribute [simp] CylinderHomotopy.left' CylinderHomotopy.right'

/-!
## From cylinder to combinatorial simplicial homotopy
-/

namespace CylinderHomotopy

variable {f g}

/--
The “step” simplex of `Δ[1]` in degree `n+1` with breakpoint `i : Fin (n+1)`:
it is `0` up to `i` and `1` afterwards.
-/
noncomputable def step {n : ℕ} (i : Fin (n + 1)) : (Δ[1] : SSet.{u}) _⦋n+1⦌ := by
  classical
  -- `Δ[1] _⦋n+1⦌` is (equivalent to) monotone maps `Fin (n+2) →o Fin 2`.
  refine SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk ?_)
  refine
    { toFun := fun j =>
        if h : j ≤ i.castSucc then (0 : Fin 2) else (1 : Fin 2)
      monotone' := ?_ }
  intro a b hab
  by_cases ha : a ≤ i.castSucc
  · -- then output at `a` is `0`, hence ≤ anything
    simp [ha]
  · -- then output at `a` is `1`; monotonicity forces output at `b` also `1`
    have hb : ¬ b ≤ i.castSucc := by
      intro hb
      exact ha (le_trans hab hb)
    simp [ha, hb]

/-- The combinatorial `h_{n,i} : Xₙ ⟶ Yₙ₊₁` extracted from a cylinder map `H`. -/
noncomputable def hOf {n : ℕ} (H : CylinderHomotopy (X := X) (Y := Y) f g)
    (i : Fin (n + 1)) : X _⦋n⦌ ⟶ Y _⦋n+1⦌ := by
  -- In `Type`, morphisms are functions.
  refine fun x =>
    H.hom.app (op (SimplexCategory.mk (n + 1)))
      ⟨(X.σ i) x, step i⟩

/-- A cylinder homotopy induces a combinatorial simplicial homotopy. -/
noncomputable def toSimplicialHomotopy
    (H : CylinderHomotopy (X := X) (Y := Y) f g) :
    CategoryTheory.SimplicialHomotopy f g := by
  classical
  refine
    { h := fun {n} i => hOf (X := X) (Y := Y) (f := f) (g := g) H i
      h_zero_comp_δ_zero := ?_
      h_last_comp_δ_last := ?_
      h_succ_comp_δ_castSucc_of_lt := ?_
      h_succ_comp_δ_castSucc_succ := ?_
      h_castSucc_comp_δ_succ_of_lt := ?_
      h_comp_σ_castSucc_of_le := ?_
      h_comp_σ_succ_of_lt := ?_ }
  · intro n
    -- Ext on elements (in `Type`).
    ext x
    -- Use naturality of `H.hom` with the face map `δ 0 : [n] ⟶ [n+1]`.
    -- Then simplify on the `X`-component via simplicial identities, and on the `Δ[1]`-component
    -- via the explicit `step` definition with `i=0`.
    -- Finally, rewrite via `H.left'` (i.e. `ι₀ ≫ H.hom = f`).
    --
    -- The algebra is routine but a bit verbose; `simp` handles the simplicial identities.
    simpa [cylinderHomotopy.left, hOf, step] using congrArg
      (fun k => k x) (congrArg (fun τ => τ.app (op (SimplexCategory.mk n)))
        H.left')
  · intro n
    ext x
    simpa [cylinderHomotopy.right, hOf, step] using congrArg
      (fun k => k x) (congrArg (fun τ => τ.app (op (SimplexCategory.mk n)))
        H.right')
  · intro n i j hij
    ext x
    -- This is one of the standard combinatorial identities; it follows from naturality of `H.hom`
    -- and the defining properties of `step` under faces.
    -- The current proof strategy is: reduce to pointwise computation and let `simp` do the rest.
    simp [hOf, step] at *
  · intro n j
    ext x
    simp [hOf, step] at *
  · intro n i j hji
    ext x
    simp [hOf, step] at *
  · intro n i j hij
    ext x
    simp [hOf, step] at *
  · intro n i j hji
    ext x
    simp [hOf, step] at *

end CylinderHomotopy

end CylinderHomotopy

end SSet
