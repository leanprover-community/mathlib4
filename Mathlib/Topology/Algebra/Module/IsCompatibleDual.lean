/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! # Compatible duals

Given a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, we say that these (that is, `B`, `E` and `F`) form a
*compatible dual system* (`LinearMap.IsCompatibleDual`) if `B.flip` is a linear equivalence between
`F` and the strong dual of `E` (`StrongDual 𝕜 E`). In other words, `B.flip` is injective, for every
`y : F`, `B.flip y : E →ₗ[𝕜] 𝕜` is continuous, and moreover every element of `StrongDual 𝕜 E` can be
realized as `B.flip y` for some choice of `y`.

Compatible dual systems are prevalent throughout functional analysis, and are the primary subject of
the Mackey–Arens theorem: given a dual system `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, a locally convex topology
on `E` makes this a compatible dual system if and only if that topology lies between the weak
topology on `E` induced by `B` and the Mackey topology on `E` relative to `B`.

## Implementation notes

We choose to implement `IsCompatibleDual` as a `Prop`-valued class instead of carrying the data of
the inverse (i.e., the map `StrongDual 𝕜 E →ₗ[𝕜] F`). This avoids entirely any potential instance
diamonds (e.g., `B.IsCompatibleDual` and `B.flip.flip.IsCompatibleDual`).
-/

@[expose] public section

namespace LinearMap

variable {𝕜 E F : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommMonoid F] [Module 𝕜 F]

/-- A topology on `E` is compatible with the bilinear form `B` if every
continuous linear functional on `E` has the form `B.flip f` for exactly one `f : F`. -/
class IsCompatibleDual (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Prop where
  range_flip : range B.flip = range (topDualPairing 𝕜 E)
  flip_injective : Function.Injective B.flip

namespace IsCompatibleDual

/-- A linear equivalence between `F` and the strong dual of `E` which is implemented by `B`
constitutes a compatible dual system. The converse also holds, see
`LinearMap.IsCompatibleDual.equiv` and `isCompatibleDual_iff_exists_linearEquiv`. -/
lemma of_linearEquiv (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (e : F ≃ₗ[𝕜] StrongDual 𝕜 E)
    (he : ∀ x y, e y x = B x y) : B.IsCompatibleDual where
  range_flip := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e y, LinearMap.ext fun x ↦ he x y⟩
    · rintro ⟨f, rfl⟩
      refine ⟨e.symm f, LinearMap.ext fun x ↦ ?_⟩
      simp [← he]
  flip_injective y₁ y₂ h := e.injective <| ContinuousLinearMap.ext fun x ↦ by
    simpa [he] using congr($h x)

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsCompatibleDual]

lemma continuous_eval (y : F) : Continuous (B · y) := by
  obtain ⟨f, hf⟩ : B.flip y ∈ range (topDualPairing 𝕜 E) := hB.range_flip ▸ mem_range_self _ y
  convert f.continuous using 1
  ext x
  simpa using congr($hf.symm x)

/-- Linear equivalence of `F` with `StrongDual 𝕜 E` obtained from `B.IsCompatibleDual`
This has a non-computable inverse via `LinearEquiv.ofBijective`. In type-specific cases, it
is preferred to use an existing equivalence. -/
noncomputable def equiv : F ≃ₗ[𝕜] StrongDual 𝕜 E :=
  .ofBijective
    { toFun y := ⟨B.flip y, continuous_eval B y⟩
      map_add' _ _ := ContinuousLinearMap.ext fun x ↦ map_add (B x) _ _
      map_smul' _ _ := ContinuousLinearMap.ext fun x ↦ map_smul (B x) _ _ }
    ⟨fun _ _ h ↦ hB.flip_injective <| LinearMap.ext fun x ↦ congr($h x), fun f ↦
      have ⟨y, hy⟩ := hB.range_flip ▸ mem_range_self (topDualPairing 𝕜 E) f
      ⟨y, ContinuousLinearMap.ext fun x ↦ congr($hy x)⟩⟩

@[simp]
lemma equiv_apply_apply (y : F) (x : E) : equiv B y x = B x y :=
  rfl

@[simp]
lemma apply_equiv_symm_apply (f : StrongDual 𝕜 E) (x : E) : B x ((equiv B).symm f) = f x := by
  rw [← equiv_apply_apply, LinearEquiv.apply_symm_apply]

protected lemma separatingRight : B.SeparatingRight := fun y hy ↦
  hB.flip_injective <| by ext x; simpa using hy x

lemma equiv_eq (e : F ≃ₗ[𝕜] StrongDual 𝕜 E) (he : ∀ x y, e y x = B x y) : equiv B = e :=
  LinearEquiv.ext fun y ↦ ContinuousLinearMap.ext fun x ↦ (he x y).symm

end IsCompatibleDual

lemma isCompatibleDual_iff_exists_linearEquiv (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    B.IsCompatibleDual ↔ ∃ e : F ≃ₗ[𝕜] StrongDual 𝕜 E, ∀ x y, e y x = B x y :=
  ⟨fun _ ↦ ⟨IsCompatibleDual.equiv B, fun _ _ ↦ rfl⟩,
    fun ⟨e, he⟩ ↦ .of_linearEquiv B e he⟩

instance : (topDualPairing 𝕜 E).flip.IsCompatibleDual :=
  .of_linearEquiv _ (.refl 𝕜 _) fun _ _ ↦ rfl

@[simp]
lemma IsCompatibleDual.equiv_topDualPairing_flip :
    equiv (topDualPairing 𝕜 E).flip = .refl 𝕜 _ :=
  equiv_eq _ _ fun _ _ ↦ rfl

end LinearMap
