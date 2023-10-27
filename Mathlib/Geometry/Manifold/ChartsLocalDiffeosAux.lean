/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# Charts are local diffeomorphism

TODO: prove what I want to, then add a real docstring
-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
set_option autoImplicit false

variable
  -- Let `M` be a smooth manifold over the pair `(E, H)`. xxx: remove smoothness
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- Let `N` be a smooth manifold over the pair `(F, G)`.
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N] {n : ℕ∞}

section Future
-- On any topological manifold (charted space on a normed space),
-- charts and inverse charts are structomorphisms.
-- ACTUALLY, that is not quite true! Charts are only local homeomorphisms,
-- hence they should be structomorphisms on e.source resp. e.target.
-- Mathlib doesn't fully have that "open subsets of manifolds are manifolds" yet
-- (the ChartedSpace instance is missing).

/-- Charts are structomorphisms. -/
lemma LocalHomeomorphism.toStructomorph {e : LocalHomeomorph M H} (he : e ∈ atlas H M)
    {G : StructureGroupoid H} : Structomorph G M H := sorry

/-- Each chart inverse is a structomorphism. -/
-- do the same with symm... probably cannot reflect this in the types...
lemma LocalHomeomorphism.symm_toStructomorph {e : LocalHomeomorph M H} (he : e ∈ atlas H M)
    {G : StructureGroupoid H} : Structomorph G M H := sorry

-- Generalise this to all extended charts, if I is boundaryless.

-- On a C^n manifolds, all charts and inverse charts are C^m.
-- TODO: generalise this to structomorphisms, once the above gap has been filled
end Future

section Present
-- If M is a C^m manifold, charts are DiffeomorphOn (easy).
-- In particular: each chart and inverse chart is a local diffeomorphism at each point of its source.

-- Corollary. differentials of (inverse) charts are linear isomorphisms.

-- Cor: differentials of charts are bijective.
end Present

-- auxiliary results, not needed for my proof, but perhaps still useful
section aux
-- TODO: PRed to Data.Set.Image, drop once that is merged
/-- Variant of `image_congr`, for one function being the identity. -/
theorem image_congr'' {α β : Type*} {f : α → β} {g : β → α} {s : Set α}
    (h : ∀ x : α, x ∈ s → (g ∘ f) x = x) : g ∘ f '' s = s := by
  rw [image_congr h, image_id']

-- TODO: I feel this should be in mathlib already, but exact? cannot find it...
lemma LocalHomeomorph.image_symm_target_eq_source {e : LocalHomeomorph M H} :
    e.invFun '' e.target = e.source := by
  rw [← e.toLocalEquiv.image_source_eq_target, ← image_comp]
  exact image_congr'' (fun x hx ↦ e.left_inv' hx)

-- is this worth being a separate lemma?
lemma LocalHomeomorph.isBLA {e : LocalHomeomorph M H} : IsOpen (e.invFun '' e.target) := by
  rw [e.image_symm_target_eq_source]
  exact e.open_source

-- is this worth being a separate lemma in mathlib?
lemma LocalHomeomorph.source_nhd {e : LocalHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    e.source ∈ 𝓝 x := e.open_source.mem_nhds hx
end aux

-- auxiliary statements for `DiffeomorphOn`, which might be useful simple lemmas, eventually
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
/-
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
-/
end DiffeomorphOn
