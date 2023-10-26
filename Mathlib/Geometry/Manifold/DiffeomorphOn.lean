import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv

/-!
# "Local" diffeomorphisms
This file implements "local" diffeomorphisms: C^n maps between open subsets of two manifolds.

Junk value pattern, extended to the whole manifold.

Model case: charts of a smooth manifold.

Naming is hard: "LocalDiffeomorph" would parallel `LocalHomeomorph` (which is the continuous
analogue of this notion); however, in mathematics, "local diffeomorphisms" are already a fixed term
and something different (a C^n map, so every point has a neighbourhood on which `f` is a diffeomorphism).
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

/-- Like `Diffeomorph`, but on an open set only.
  Maps `M → M` which are `n`-times continuous differentiable diffeomorphisms with respect to `I` and `I'`
  between two open subsets of `M` resp. `M'`.
  Not called LocalDiffeomorph as that's something else...  -/
structure DiffeomorphOn extends LocalHomeomorph M N where
  contMDiffOn_toFun : ContMDiffOn I J n toFun source
  contMDiffOn_invFun : ContMDiffOn J I n invFun target

/-- A diffeomorphism is a local diffeomorphism. -/
theorem Diffeomorph.toDiffeomorphOn (h : Diffeomorph I J M N n) : DiffeomorphOn I J M N n :=
  {
    contMDiffOn_toFun := h.contMDiff.contMDiffOn
    contMDiffOn_invFun := h.contMDiff_invFun.contMDiffOn
    toLocalHomeomorph := h.toHomeomorph.toLocalHomeomorph
  }

-- TODO: add a coe instance instance? injectivity, ext lemma, etc.

namespace DiffeomorphOn
-- simple properties: TODO compare with Diffeomorph and fill out API!
-- XXX: Diffeomorph is missing theorems for inverse? or further below??
@[continuity]
protected theorem continuousOn (h : DiffeomorphOn I J M N n) : ContinuousOn h.toFun h.source :=
  h.contMDiffOn_toFun.continuousOn

@[continuity]
protected theorem continuousOn_symm (h : DiffeomorphOn I J M N n) : ContinuousOn h.invFun h.target :=
  h.contMDiffOn_invFun.continuousOn

protected theorem contMDiffOn (h : DiffeomorphOn I J M N n) : ContMDiffOn I J n h.toFun h.source :=
  h.contMDiffOn_toFun

protected theorem contMDiffOn_symm (h : DiffeomorphOn I J M N n) : ContMDiffOn J I n h.invFun h.target :=
  h.contMDiffOn_invFun

protected theorem contMDiffAt (h : DiffeomorphOn I J M N n) {x : M} (hx : x ∈ h.source) :
    ContMDiffAt I J n h.toFun x :=
  h.contMDiffOn_toFun.contMDiffAt (h.open_source.mem_nhds hx)

protected theorem contMDiffAt_symm (h : DiffeomorphOn I J M N n) {x : N} (hx : x ∈ h.target) :
    ContMDiffAt J I n h.invFun x :=
  h.contMDiffOn_invFun.contMDiffAt (h.open_target.mem_nhds hx)

protected theorem contMDiffWithinAt (h : DiffeomorphOn I J M N n)
      {s : Set M} {x : M} (hx : x ∈ h.source) : ContMDiffWithinAt I J n h.toFun s x :=
  (h.contMDiffAt hx).contMDiffWithinAt

protected theorem contMDiffWithinAt_symm (h : DiffeomorphOn I J M N n)
      {s : Set N} {x : N} (hx : x ∈ h.target) : ContMDiffWithinAt J I n h.invFun s x :=
  (h.contMDiffAt_symm hx).contMDiffWithinAt

protected theorem mdifferentiableOn (h :  DiffeomorphOn I J M N n) (hn : 1 ≤ n) :
    MDifferentiableOn I J h.toFun h.source :=
  (h.contMDiffOn).mdifferentiableOn hn

protected theorem mdifferentiableOn_symm (h :  DiffeomorphOn I J M N n) (hn : 1 ≤ n) :
    MDifferentiableOn J I h.invFun h.target :=
  (h.contMDiffOn_symm).mdifferentiableOn hn

/-- Identity map as a diffeomorphism. -/
protected def refl : DiffeomorphOn I I M M n where
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn
  toLocalHomeomorph := LocalHomeomorph.refl M

@[simp]
theorem refl_toEquiv : (DiffeomorphOn.refl I M n).toEquiv = Equiv.refl _ :=
  rfl

-- @[simp]
-- theorem coe_refl : ⇑(DiffeomorphOn.refl I M n) = id :=
--   rfl

/-- Composition of two diffeomorphisms. -/
-- skipped so far; this is more subtle than I like (compare LocalHomeomorph, which has trans' and trans)
protected def trans (h₁ : DiffeomorphOn I I' M M' n) (h₂ : DiffeomorphOn I' J M' N n)
    (h : h₁.target ⊆ h₂.source) : DiffeomorphOn I J M N n where
  contMDiffOn_toFun := sorry -- (h₂.contMDiffOn).comp h₁.contMDiffOn h
  contMDiffOn_invFun := sorry --h₁.contMDiffOn_invFun.comp h₂.contMDiffOn_invFun h
  toLocalHomeomorph := h₁.toLocalHomeomorph.trans h₂.toLocalHomeomorph

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

/-- Inverse of a diffeomorphism. -/
@[pp_dot]
protected def symm (h : DiffeomorphOn I I' M M' n) : DiffeomorphOn I' I M' M n where
  contMDiffOn_toFun := h.contMDiffOn_invFun
  contMDiffOn_invFun := h.contMDiffOn_toFun
  toLocalHomeomorph := h.toLocalHomeomorph.symm

/- TODO: fix these statements, then the proofs will be easy
@[simp]
theorem apply_symm_apply (h : DiffeomorphOn I I' M M' n) {x : N} (hx : x ∈ h.target) : h.toFun (h.symm.toFun x) = x :=
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

@[simp]
theorem symm_toLocalHomeomorph (h : DiffeomorphOn I J M N n) :
    (h.symm).toLocalHomeomorph = h.toLocalHomeomorph.symm :=
  rfl

#exit
-- TODO: audit these, and adapt to DiffeoMorphOn as fit
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
