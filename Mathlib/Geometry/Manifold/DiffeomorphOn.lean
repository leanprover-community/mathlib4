/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# "Local" diffeomorphisms
This file implements "local" diffeomorphisms: `C^n` maps between open subsets of two manifolds.

Junk value pattern, extended to the whole manifold.

Model case: charts of a smooth manifold.

Naming is hard: "LocalDiffeomorph" would parallel `LocalHomeomorph` (which is the continuous
analogue of this notion); however, in mathematics, "local diffeomorphisms" are already a fixed term
and something different (a `C^n` map `f: M → N` such that every point `p ∈ M` has a neighbourhood
on which `f` is a diffeomorphism).

TODO: define the real local diffeomorphisms; show more relations to diffeomorphisms
-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
set_option autoImplicit false

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 F G}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞}

variable (I I' J M M' N n)

/-- A diffeomorphism is a local diffeomorphism on the entire space. -/
def Diffeomorph.toDiffeomorphOn (h : Diffeomorph I J M N n) : DiffeomorphOn I J M N n :=
  {
    contMDiffOn_toFun := h.contMDiff.contMDiffOn
    contMDiffOn_invFun := h.contMDiff_invFun.contMDiffOn
    toLocalHomeomorph := h.toHomeomorph.toLocalHomeomorph
  }

-- aux statements for DiffeomorphOn, which might be useful simple lemmas there
namespace DiffeomorphOn
-- simple properties: TODO compare with Diffeomorph and fill out API!
-- XXX: is `Diffeomorph` missing the simple theorems for inverse, or are the further below?

-- @[simp]
-- theorem coe_refl : ⇑(DiffeomorphOn.refl I M n) = id :=
--   rfl

-- TODO: these statements don't compile yet
/-
@[simp]
theorem trans_refl (h : DiffeomorphOn I I' M M' n) : h.trans (Diffeomorph.refl I' M' n) = h :=
  ext fun _ => rfl

-- TODO: from here on, even the notation is shamelessly copied from `Diffeomorph.lean`
@[simp]
theorem refl_trans (h : M ≃ₘ^n⟮I, I'⟯ M') : (Diffeomorph.refl I M n).trans h = h :=
  ext fun _ => rfl

@[simp]
theorem coe_trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) : ⇑(h₁.trans h₂) = h₂ ∘ h₁ :=
  rfl
-/

/- TODO: fix these statements, then the proofs will be easy
@[simp]
theorem apply_symm_apply (h : DiffeomorphOn I I' M M' n) {x : N} (hx : x ∈ h.target) :
    h.toFun (h.symm.toFun x) = x :=
  h.toLocalHomeomorph.apply_symm_apply hx

@[simp]
theorem symm_apply_apply (h : DiffeomorphOn I I' M M' n) (x : M) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x


-- TODO: fix these proofs, once the right ext lemma has been added!
@[simp]
theorem symm_refl : (DiffeomorphOn.refl I M n).symm = DiffeomorphOn.refl I M n := by
  sorry -- ext fun _ => rfl

-- TODO: statements don't compile yet...
@[simp]
theorem self_trans_symm (h : DiffeomorphOn I J M N n) : h.trans h.symm = DiffeomorphOn.refl I M n :=
  sorry -- ext h.symm_apply_apply

@[simp]
theorem symm_trans_self (h : DiffeomorphOn I J M N n) : h.symm.trans h = DiffeomorphOn.refl J N n :=
  sorry -- ext h.apply_symm_apply

@[simp]
theorem symm_trans' (h₁ : DiffeomorphOn I I' M M' n) (h₂ : DiffeomorphOn I' J M' N n) :
    (h₁.trans h₂).symm = h₂.symm.trans h₁.symm :=
  rfl
-/

-- TODO: audit these, and adapt the ones which fit to DiffeomorphOn
@[simp, mfld_simps]
theorem toEquiv_coe_symm (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toEquiv.symm = h.symm :=
  rfl

theorem image_eq_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) : h '' s = h.symm ⁻¹' s :=
  h.toEquiv.image_eq_preimage s

theorem symm_image_eq_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N) : h.symm '' s = h ⁻¹' s :=
  h.symm.image_eq_preimage s

@[simp, mfld_simps]
nonrec theorem range_comp {α} (h : M ≃ₘ^n⟮I, J⟯ N) (f : α → M) :
    range (h ∘ f) = h.symm ⁻¹' range f := by
  rw [range_comp, image_eq_preimage]

@[simp]
theorem image_symm_image (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N) : h '' (h.symm '' s) = s :=
  h.toEquiv.image_symm_image s

@[simp]
theorem symm_image_image (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) : h.symm '' (h '' s) = s :=
  h.toEquiv.symm_image_image s

/-- A diffeomorphism is a homeomorphism. -/
def toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : M ≃ₜ N :=
  ⟨h.toEquiv, h.continuous, h.symm.continuous⟩

@[simp]
theorem toHomeomorph_toEquiv (h : M ≃ₘ^n⟮I, J⟯ N) : h.toHomeomorph.toEquiv = h.toEquiv :=
  rfl

@[simp]
theorem symm_toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.toHomeomorph = h.toHomeomorph.symm :=
  rfl

@[simp]
theorem coe_toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toHomeomorph = h :=
  rfl

@[simp]
theorem coe_toHomeomorph_symm (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toHomeomorph.symm = h.symm :=
  rfl
end DiffeomorphOn
