/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Interactions of exterior powers and tensor powers.
-/

@[expose] public section

open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ) {M N N' : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N']

namespace exteriorPower

/-! Map to the tensor power. -/

variable (M)

/-- The linear map from the `n`th exterior power to the `n`th tensor power induced by
`MultilinearMap.alternarization`. -/
noncomputable def toTensorPower : ⋀[R]^n M →ₗ[R] (⨂[R]^n) M :=
    alternatingMapLinearEquiv <|
    MultilinearMap.alternatization (PiTensorProduct.tprod R (s := fun (_ : Fin n) => M))

variable {M}

open Equiv in
@[simp]
lemma toTensorPower_apply_ιMulti (v : Fin n → M) :
    toTensorPower R n M (ιMulti R n v) =
      ∑ σ : Perm (Fin n), Perm.sign σ • PiTensorProduct.tprod R (fun i => v (σ i)) := by
  simp [toTensorPower, MultilinearMap.alternatization_apply]

/-! Linear form on the exterior power induced by a family of linear forms on the module. This
is used to prove the linear independence of some families in the exterior power, cf.
`exteriorPower.linearFormOfBasis` and `exteriorPower.ιMulti_family_linearIndependent_ofBasis`. -/

/-- A family `f` indexed by `Fin n` of linear forms on `M` defines a linear form on the `n`th
exterior power of `M`, by composing the map `exteriorPower.toTensorPower` to the `n`th tensor
power and then applying `TensorPower.linearFormOfFamily` (which takes the product of the
components of `f`). -/
noncomputable def linearFormOfFamily (f : (_ : Fin n) → (M →ₗ[R] R)) :
    ⋀[R]^n M →ₗ[R] R :=
  TensorPower.dprod f ∘ₗ toTensorPower R n M

@[simp]
lemma linearFormOfFamily_apply (f : (_ : Fin n) → (M →ₗ[R] R)) (x : ⋀[R]^n M) :
    linearFormOfFamily R n f x = TensorPower.dprod f (toTensorPower R n M x) :=
  rfl

lemma linearFormOfFamily_apply_ιMulti (f : (_ : Fin n) → (M →ₗ[R] R)) (m : Fin n → M) :
    linearFormOfFamily R n f (ιMulti R n m) =
    ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, f i (m (σ i)) := by
  simp only [linearFormOfFamily_apply, toTensorPower_apply_ιMulti, map_sum,
    LinearMap.map_smul_of_tower, TensorPower.dprod_apply]

/-- If `f` is a family of linear forms on `M` (index by `Fin n`) and `p` is a linear map
from `N` to `M`, then the composition of `exteriorPower.linearFormOfFamily R n f` and
of `exteriorPower.map p` is equal to the linear form induced by the family
`fun i ↦ (f i).comp p`.. -/
lemma linearFormOfFamily_comp_map (f : (_ : Fin n) → (M →ₗ[R] R)) (p : N →ₗ[R] M) :
    (linearFormOfFamily R n f).comp (map n p) =
    linearFormOfFamily R n (fun (i : Fin n) => (f i).comp p) := by
  apply LinearMap.ext_on (ιMulti_span R n (M := N))
  intro x hx
  obtain ⟨y, h⟩ := Set.mem_range.mp hx
  simp only [← h, LinearMap.coe_comp, Function.comp_apply, map_apply_ιMulti,
    linearFormOfFamily_apply, toTensorPower_apply_ιMulti, map_sum, LinearMap.map_smul_of_tower,
    TensorPower.dprod_apply]

lemma linearFormOfFamily_comp_map_apply (f : (_ : Fin n) → (M →ₗ[R] R))
    (p : N →ₗ[R] M) (x : ⋀[R]^n N) :
    (linearFormOfFamily R n f) (map n p x) =
    linearFormOfFamily R n (fun (i : Fin n) => (f i).comp p) x := by
  rw [← LinearMap.comp_apply, linearFormOfFamily_comp_map]

/-- A family `f` of linear forms on `M` indexed by `Fin n` defines an `n`-fold alternating form
on `M`, by composing the linear form on `⋀[R]^n M` indeuced by `f` (defined in
`exteriorPower.linearFormOfFamily`) with the canonical `n`-fold alternating map from `M` to its
`n`th exterior power. -/
noncomputable def alternatingFormOfFamily (f : (_ : Fin n) → (M →ₗ[R] R)) :
    M [⋀^Fin n]→ₗ[R] R :=
  (linearFormOfFamily R n f).compAlternatingMap (ιMulti R n)

@[simp]
lemma alternatingFormOfFamily_apply (f : (_ : Fin n) → (M →ₗ[R] R)) (m : Fin n → M) :
    alternatingFormOfFamily R n f m = linearFormOfFamily R n f (ιMulti R n m) :=
  rfl

variable {R}
variable {N'' : Type*} [AddCommGroup N''] [Module R N'']

lemma sum_range_map (f : N →ₗ[R] M) (f' : N' →ₗ[R] M) (f'' : N'' →ₗ[R] M)
    (hf : ∃ (g : N →ₗ[R] N''), f''.comp g = f) (hf' : ∃ (g' : N' →ₗ[R] N''), f''.comp g' = f') :
    LinearMap.range (map n f) ⊔ LinearMap.range (map n f') ≤ LinearMap.range (map n f'') := by
  let ⟨g, hg⟩ := hf
  let ⟨g', hg'⟩ := hf'
  intro x
  simp only [Submodule.mem_sup, LinearMap.mem_range]
  intro ⟨x₁, ⟨⟨y, hy⟩, ⟨x₂, ⟨⟨y', hy'⟩, hx⟩⟩⟩⟩
  existsi map n g y + map n g' y'
  rw [← hx, ← hy, ← hy', ← hg, ← hg', map_comp, ← map_comp, map_add]
  simp

/-- Every element of `⋀[R]^n M` is in the image of `⋀[R]^n P` for some finitely generated
submodule `P` of `M`. -/
lemma mem_exteriorPower_is_mem_finite (x : ⋀[R]^n M) :
    ∃ (P : Submodule R M), Submodule.FG P ∧ x ∈ LinearMap.range (map n (Submodule.subtype P)) := by
  have hx : x ∈ (⊤ : Submodule R (⋀[R]^n M)) := by simp only [Submodule.mem_top]
  rw [← ιMulti_span] at hx
  refine Submodule.span_induction (R := R) (p := fun x _ => ∃ (P : Submodule R M),
    P.FG ∧ x ∈ LinearMap.range (map n P.subtype)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨z, hz⟩ := hy
    use Submodule.span R (Set.range z)
    constructor
    · apply Submodule.fg_span
      exact Set.finite_range z
    · use ιMulti R n (fun i => ⟨z i, by simp [Submodule.mem_span_of_mem]⟩)
      simp only [map_apply_ιMulti, Submodule.coe_subtype, ← hz]
      congr
  · use ⊥
    simp [Submodule.fg_bot]
  · rintro y z _ _ ⟨Py, PyFG, y_mem⟩ ⟨Pz, PzFG, z_mem⟩
    use Py ⊔ Pz
    refine ⟨Submodule.FG.sup PyFG PzFG, ?_⟩
    apply sum_range_map n Py.subtype Pz.subtype
    · use Submodule.inclusion le_sup_left
      exact Submodule.subtype_comp_inclusion Py _ le_sup_left
    · use Submodule.inclusion le_sup_right
      exact Submodule.subtype_comp_inclusion Pz _ le_sup_right
    · exact Submodule.add_mem_sup y_mem z_mem
  · intro c y _ ⟨Py, PyFG, y_mem⟩
    use Py
    refine ⟨PyFG, ?_⟩
    obtain ⟨y₁, hy₁⟩ := y_mem
    use c • y₁
    rw [map_smul, hy₁]

end exteriorPower
