/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Geometry.Manifold.Category.MfldCat.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The tangent functor on `MfldCat`

We define the tangent functor `MfldCat.tangentFunctor : MfldCat 𝕜 (n + 1) ⥤ MfldCat 𝕜 n`, sending a
`C^(n+1)` manifold to its tangent bundle and a `C^(n+1)` map to its pushforward (tangent map).
-/

@[expose] public section

open CategoryTheory
open scoped Manifold

universe u₁ u₂ u₃ u₄

namespace MfldCat

variable {𝕜 : Type u₁} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}

variable (M : MfldCat.{u₁, u₂, u₃, u₄} 𝕜 (n + 1))

local instance : IsManifold M.I 1 M := IsManifold.of_le (n := n + 1) le_add_self
local instance : IsManifold M.I n M := IsManifold.of_le (n := n + 1) le_self_add
local instance : ContMDiffVectorBundle n M.E (TangentSpace M.I : M → Type u₃) M.I :=
  TangentBundle.contMDiffVectorBundle
-- The above instance implies `TangentBundle M.I M` is a manifold by `Bundle.TotalSpace.isManifold`.

/-- Sends a `C^(n+1)` manifold to its tangent bundle and a `C^(n+1)` map to its `TangentMap`. -/
noncomputable def tangentFunctor :
    MfldCat 𝕜 (n + 1) ⥤ MfldCat 𝕜 n where
  obj M := of (TangentBundle M.I M) (M.E × M.E) (ModelProd M.H M.E) M.I.tangent
  map {M N} f :=
    ofHom ⟨tangentMap M.I N.I f.hom, ContMDiff.contMDiff_tangentMap f.hom.contMDiff le_rfl⟩
  map_id _ := Hom.ext <| Subtype.ext tangentMap_id
  map_comp f g := Hom.ext <| Subtype.ext <| tangentMap_comp
    (g.hom.contMDiff.mdifferentiable (by positivity))
    (f.hom.contMDiff.mdifferentiable (by positivity))

end MfldCat
