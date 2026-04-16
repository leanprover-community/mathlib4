/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Yury Kudryashov
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential

/-!
# Diffeomorphisms
This file implements diffeomorphisms.

## Definitions

* `Diffeomorph I I' M M' n`: `n`-times continuously differentiable diffeomorphism between
  `M` and `M'` with respect to I and I'; we do not introduce a separate definition for the case
  `n = ∞` or `n = ω`; we use notation instead.
* `Diffeomorph.toHomeomorph`: reinterpret a diffeomorphism as a homeomorphism.
* `ContinuousLinearEquiv.toDiffeomorph`: reinterpret a continuous equivalence as
  a diffeomorphism.
* `ModelWithCorners.transContinuousLinearEquiv`: compose a given `ModelWithCorners` with a
  continuous linear equiv between the old and the new target spaces. Useful, e.g, to turn any
  finite-dimensional manifold into a manifold modelled on a Euclidean space.
* `Diffeomorph.toTransContinuousLinearEquiv`: the identity diffeomorphism between `M` with
  model `I` and `M` with model `I.transContinuousLinearEquiv e`.

This file also provides diffeomorphisms related to products and disjoint unions.
* `Diffeomorph.prodCongr`: the product of two diffeomorphisms
* `Diffeomorph.prodComm`: `M × N` is diffeomorphic to `N × M`
* `Diffeomorph.prodAssoc`: `(M × N) × N'` is diffeomorphic to `M × (N × N')`
* `Diffeomorph.sumCongr`: the disjoint union of two diffeomorphisms
* `Diffeomorph.sumComm`: `M ⊕ M'` is diffeomorphic to `M' × M`
* `Diffeomorph.sumAssoc`: `(M ⊕ N) ⊕ P` is diffeomorphic to `M ⊕ (N ⊕ P)`
* `Diffeomorph.sumEmpty`: `M ⊕ ∅` is diffeomorphic to `M`

## Notation

* `M ≃ₘ^n⟮I, I'⟯ M'`  := `Diffeomorph I J M N n`
* `M ≃ₘ⟮I, I'⟯ M'`    := `Diffeomorph I J M N ∞`
* `E ≃ₘ^n[𝕜] E'`     := `E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`
* `E ≃ₘ[𝕜] E'`       := `E ≃ₘ⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Keywords

diffeomorphism, manifold
-/

@[expose] public section


open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*} [TopologicalSpace H] {H' : Type*}
  [TopologicalSpace H'] {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 F G}
  {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*} [TopologicalSpace M']
  [ChartedSpace H' M'] {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {N' : Type*}
  [TopologicalSpace N'] [ChartedSpace G' N'] {n : WithTop ℕ∞}

section Defs

variable (I I' M M' n)

/-- `n`-times continuously differentiable diffeomorphism between `M` and `M'` with respect to `I`
and `I'`, denoted as `M ≃ₘ^n⟮I, I'⟯ M'` (in the `Manifold` namespace). -/
structure Diffeomorph extends M ≃ M' where
  protected contMDiff_toFun : CMDiff n toEquiv
  protected contMDiff_invFun : CMDiff n toEquiv.symm


end Defs

@[inherit_doc]
scoped[Manifold] notation M " ≃ₘ^" n:1000 "⟮" I ", " J "⟯ " N => Diffeomorph I J M N n

/-- Infinitely differentiable diffeomorphism between `M` and `M'` with respect to `I` and `I'`. -/
scoped[Manifold] notation M " ≃ₘ⟮" I ", " J "⟯ " N => Diffeomorph I J M N ∞

-- Porting note: this notation is broken because `n[𝕜]` gets parsed as `getElem`
/-- `n`-times continuously differentiable diffeomorphism between `E` and `E'`. -/
scoped[Manifold] notation E " ≃ₘ^" n:1000 "[" 𝕜 "] " E' => Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') E E' n

/-- Infinitely differentiable diffeomorphism between `E` and `E'`. -/
scoped[Manifold] notation3 E " ≃ₘ[" 𝕜 "] " E' => Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') E E' ∞

namespace Diffeomorph

theorem toEquiv_injective : Injective (Diffeomorph.toEquiv : (M ≃ₘ^n⟮I, I'⟯ M') → M ≃ M')
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

instance : EquivLike (M ≃ₘ^n⟮I, I'⟯ M') M M' where
  coe Φ := Φ.toEquiv
  inv Φ := Φ.toEquiv.symm
  left_inv Φ := Φ.left_inv
  right_inv Φ := Φ.right_inv
  coe_injective' _ _ h _ := toEquiv_injective <| DFunLike.ext' h

/-- Interpret a diffeomorphism as a `ContMDiffMap`. -/
@[coe]
def toContMDiffMap (Φ : M ≃ₘ^n⟮I, I'⟯ M') : C^n⟮I, M; I', M'⟯ :=
  ⟨Φ, Φ.contMDiff_toFun⟩

instance : Coe (M ≃ₘ^n⟮I, I'⟯ M') C^n⟮I, M; I', M'⟯ :=
  ⟨toContMDiffMap⟩

@[continuity]
protected theorem continuous (h : M ≃ₘ^n⟮I, I'⟯ M') : Continuous h :=
  h.contMDiff_toFun.continuous

protected theorem contMDiff (h : M ≃ₘ^n⟮I, I'⟯ M') : CMDiff n h :=
  h.contMDiff_toFun

protected theorem contMDiffAt (h : M ≃ₘ^n⟮I, I'⟯ M') {x} : CMDiffAt n h x :=
  h.contMDiff.contMDiffAt

protected theorem contMDiffWithinAt (h : M ≃ₘ^n⟮I, I'⟯ M') {s x} : CMDiffAt[s] n h x :=
  h.contMDiffAt.contMDiffWithinAt

protected theorem contDiff (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E') : ContDiff 𝕜 n h :=
  h.contMDiff.contDiff

protected theorem mdifferentiable (h : M ≃ₘ^n⟮I, I'⟯ M') (hn : n ≠ 0) : MDiff h :=
  h.contMDiff.mdifferentiable hn

protected theorem mdifferentiableOn (h : M ≃ₘ^n⟮I, I'⟯ M') (s : Set M) (hn : n ≠ 0) : MDiff[s] h :=
  (h.mdifferentiable hn).mdifferentiableOn

@[simp]
theorem coe_toEquiv (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑h.toEquiv = h :=
  rfl

@[simp, norm_cast]
theorem coe_coe (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑(h : C^n⟮I, M; I', M'⟯) = h :=
  rfl

@[simp]
theorem toEquiv_inj {h h' : M ≃ₘ^n⟮I, I'⟯ M'} : h.toEquiv = h'.toEquiv ↔ h = h' :=
  toEquiv_injective.eq_iff

/-- Coercion to function `fun h : M ≃ₘ^n⟮I, I'⟯ M' ↦ (h : M → M')` is injective. -/
theorem coeFn_injective : Injective ((↑) : (M ≃ₘ^n⟮I, I'⟯ M') → (M → M')) :=
  DFunLike.coe_injective

@[ext]
theorem ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : ∀ x, h x = h' x) : h = h' :=
  coeFn_injective <| funext Heq

instance : ContinuousMapClass (M ≃ₘ⟮I, J⟯ N) M N where
  map_continuous f := f.continuous

section

variable (M I n)

/-- Identity map as a diffeomorphism. -/
protected def refl : M ≃ₘ^n⟮I, I⟯ M where
  contMDiff_toFun := contMDiff_id
  contMDiff_invFun := contMDiff_id
  toEquiv := Equiv.refl M

@[simp]
theorem refl_toEquiv : (Diffeomorph.refl I M n).toEquiv = Equiv.refl _ :=
  rfl

@[simp]
theorem coe_refl : ⇑(Diffeomorph.refl I M n) = id :=
  rfl

end

/-- Composition of two diffeomorphisms. -/
@[trans]
protected def trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) : M ≃ₘ^n⟮I, J⟯ N where
  contMDiff_toFun := h₂.contMDiff.comp h₁.contMDiff
  contMDiff_invFun := h₁.contMDiff_invFun.comp h₂.contMDiff_invFun
  toEquiv := h₁.toEquiv.trans h₂.toEquiv

@[simp]
theorem trans_refl (h : M ≃ₘ^n⟮I, I'⟯ M') : h.trans (Diffeomorph.refl I' M' n) = h :=
  ext fun _ => rfl

@[simp]
theorem refl_trans (h : M ≃ₘ^n⟮I, I'⟯ M') : (Diffeomorph.refl I M n).trans h = h :=
  ext fun _ => rfl

@[simp]
theorem coe_trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) : ⇑(h₁.trans h₂) = h₂ ∘ h₁ :=
  rfl

/-- Inverse of a diffeomorphism. -/
@[symm]
protected def symm (h : M ≃ₘ^n⟮I, J⟯ N) : N ≃ₘ^n⟮J, I⟯ M where
  contMDiff_toFun := h.contMDiff_invFun
  contMDiff_invFun := h.contMDiff_toFun
  toEquiv := h.toEquiv.symm

@[simp]
theorem apply_symm_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x : N) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x : M) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

@[simp]
theorem symm_refl : (Diffeomorph.refl I M n).symm = Diffeomorph.refl I M n :=
  ext fun _ => rfl

@[simp]
theorem self_trans_symm (h : M ≃ₘ^n⟮I, J⟯ N) : h.trans h.symm = Diffeomorph.refl I M n :=
  ext h.symm_apply_apply

@[simp]
theorem symm_trans_self (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.trans h = Diffeomorph.refl J N n :=
  ext h.apply_symm_apply

@[simp]
theorem symm_trans' (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) :
    (h₁.trans h₂).symm = h₂.symm.trans h₁.symm :=
  rfl

@[simp]
theorem symm_toEquiv (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.toEquiv = h.toEquiv.symm :=
  rfl

@[simp, mfld_simps]
theorem toEquiv_coe_symm (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toEquiv.symm = h.symm :=
  rfl

theorem image_eq_preimage_symm (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) : h '' s = h.symm ⁻¹' s :=
  h.toEquiv.image_eq_preimage_symm s

theorem symm_image_eq_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N) : h.symm '' s = h ⁻¹' s :=
  h.symm.image_eq_preimage_symm s

@[simp, mfld_simps]
nonrec theorem range_comp {α} (h : M ≃ₘ^n⟮I, J⟯ N) (f : α → M) :
    range (h ∘ f) = h.symm ⁻¹' range f := by
  rw [range_comp, image_eq_preimage_symm]

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

@[simp]
theorem contMDiffWithinAt_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {s x}
    (hm : m ≤ n) :
    CMDiffAt[s] m (f ∘ h) x ↔ CMDiffAt[h.symm ⁻¹' s] m f (h x) := by
  constructor
  · intro Hfh
    rw [← h.symm_apply_apply x] at Hfh
    simpa only [Function.comp_def, h.apply_symm_apply] using
      Hfh.comp (h x) (h.symm.contMDiffWithinAt.of_le hm) (mapsTo_preimage _ _)
  · rw [← h.image_eq_preimage_symm]
    exact fun hf => hf.comp x (h.contMDiffWithinAt.of_le hm) (mapsTo_image _ _)

@[simp]
theorem contMDiffOn_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {s} (hm : m ≤ n) :
    CMDiff[s] m (f ∘ h) ↔ CMDiff[h.symm ⁻¹' s] m f :=
  h.toEquiv.forall_congr fun {_} => by
    simp only [hm, coe_toEquiv, h.symm_apply_apply, contMDiffWithinAt_comp_diffeomorph_iff,
      mem_preimage]

@[simp]
theorem contMDiffAt_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {x} (hm : m ≤ n) :
    CMDiffAt m (f ∘ h) x ↔ CMDiffAt m f (h x) :=
  h.contMDiffWithinAt_comp_diffeomorph_iff hm

@[simp]
theorem contMDiff_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} (hm : m ≤ n) :
    CMDiff m (f ∘ h) ↔ CMDiff m f :=
  h.toEquiv.forall_congr fun _ ↦ h.contMDiffAt_comp_diffeomorph_iff hm

@[simp]
theorem contMDiffWithinAt_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n)
    {s x} : CMDiffAt[s] m (h ∘ f) x ↔ CMDiffAt[s] m f x :=
  ⟨fun Hhf => by
    simpa only [Function.comp_def, h.symm_apply_apply] using
      (h.symm.contMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hhf,
    fun Hf => (h.contMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hf⟩

@[simp]
theorem contMDiffAt_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n) {x} :
    CMDiffAt m (h ∘ f) x ↔ CMDiffAt m f x :=
  h.contMDiffWithinAt_diffeomorph_comp_iff hm

@[simp]
theorem contMDiffOn_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n) {s} :
    CMDiff[s] m (h ∘ f) ↔ CMDiff[s] m f :=
  forall₂_congr fun _ _ => h.contMDiffWithinAt_diffeomorph_comp_iff hm

@[simp]
theorem contMDiff_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n) :
    CMDiff m (h ∘ f) ↔ CMDiff m f :=
  forall_congr' fun _ => h.contMDiffWithinAt_diffeomorph_comp_iff hm

theorem toOpenPartialHomeomorph_mdifferentiable (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) :
    h.toHomeomorph.toOpenPartialHomeomorph.MDifferentiable I J :=
  ⟨h.mdifferentiableOn _ hn, h.symm.mdifferentiableOn _ hn⟩

theorem uniqueMDiffOn_image_aux (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {s : Set M}
    (hs : UniqueMDiffOn I s) : UniqueMDiffOn J (h '' s) := by
  convert hs.uniqueMDiffOn_preimage (h.toOpenPartialHomeomorph_mdifferentiable hn)
  simp [h.image_eq_preimage_symm]

@[simp]
theorem uniqueMDiffOn_image (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {s : Set M} :
    UniqueMDiffOn J (h '' s) ↔ UniqueMDiffOn I s :=
  ⟨fun hs => h.symm_image_image s ▸ h.symm.uniqueMDiffOn_image_aux hn hs,
    h.uniqueMDiffOn_image_aux hn⟩

@[simp]
theorem uniqueMDiffOn_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {s : Set N} :
    UniqueMDiffOn I (h ⁻¹' s) ↔ UniqueMDiffOn J s :=
  h.symm_image_eq_preimage s ▸ h.symm.uniqueMDiffOn_image hn

@[simp]
theorem uniqueDiffOn_image (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : n ≠ 0) {s : Set E} :
    UniqueDiffOn 𝕜 (h '' s) ↔ UniqueDiffOn 𝕜 s := by
  simp only [← uniqueMDiffOn_iff_uniqueDiffOn, uniqueMDiffOn_image _ hn]

@[simp]
theorem uniqueDiffOn_preimage (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : n ≠ 0) {s : Set F} :
    UniqueDiffOn 𝕜 (h ⁻¹' s) ↔ UniqueDiffOn 𝕜 s :=
  h.symm_image_eq_preimage s ▸ h.symm.uniqueDiffOn_image hn

end Diffeomorph

namespace ContinuousLinearEquiv

variable (e : E ≃L[𝕜] E')

/-- A continuous linear equivalence between normed spaces is a diffeomorphism. -/
def toDiffeomorph : E ≃ₘ[𝕜] E' where
  contMDiff_toFun := e.contDiff.contMDiff
  contMDiff_invFun := e.symm.contDiff.contMDiff
  toEquiv := e.toLinearEquiv.toEquiv

@[simp]
theorem coe_toDiffeomorph : ⇑e.toDiffeomorph = e :=
  rfl

@[simp]
theorem symm_toDiffeomorph : e.symm.toDiffeomorph = e.toDiffeomorph.symm :=
  rfl

@[simp]
theorem coe_toDiffeomorph_symm : ⇑e.toDiffeomorph.symm = e.symm :=
  rfl

end ContinuousLinearEquiv

namespace ModelWithCorners

variable (I) (e : E ≃L[𝕜] E')

/-- Apply a continuous linear equivalence to the model vector space. -/
def transContinuousLinearEquiv : ModelWithCorners 𝕜 E' H where
  toPartialEquiv := I.toPartialEquiv.trans e.toEquiv.toPartialEquiv
  source_eq := by simp
  convex_range' := by
    split_ifs with h
    · simp only [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply, LinearEquiv.coe_toEquiv,
      ContinuousLinearEquiv.coe_toLinearEquiv, toPartialEquiv_coe]
      rw [range_comp]
      letI := h.rclike
      letI := NormedSpace.restrictScalars ℝ 𝕜 E
      letI := NormedSpace.restrictScalars ℝ 𝕜 E'
      let eR : E →L[ℝ] E' := ContinuousLinearMap.restrictScalars ℝ (e : E →L[𝕜] E')
      change Convex ℝ (⇑eR '' range ↑I)
      apply I.convex_range.linear_image
    · simp [range_eq_univ_of_not_isRCLikeNormedField I h, range_comp]
  nonempty_interior' := by
    simp only [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply, LinearEquiv.coe_toEquiv,
      ContinuousLinearEquiv.coe_toLinearEquiv, toPartialEquiv_coe, range_comp,
      ContinuousLinearEquiv.image_eq_preimage_symm]
    apply Nonempty.mono (preimage_interior_subset_interior_preimage e.symm.continuous)
    rw [← ContinuousLinearEquiv.image_eq_preimage_symm]
    simpa using I.nonempty_interior
  continuous_toFun := e.continuous.comp I.continuous
  continuous_invFun := I.continuous_symm.comp e.symm.continuous

@[simp, mfld_simps]
theorem coe_transContinuousLinearEquiv : ⇑(I.transContinuousLinearEquiv e) = e ∘ I :=
  rfl

@[simp, mfld_simps]
theorem coe_transContinuousLinearEquiv_symm :
    ⇑(I.transContinuousLinearEquiv e).symm = I.symm ∘ e.symm := rfl

theorem transContinuousLinearEquiv_range : range (I.transContinuousLinearEquiv e) = e '' range I :=
  range_comp e I

theorem coe_extChartAt_transContinuousLinearEquiv (x : M) :
    ⇑(extChartAt (I.transContinuousLinearEquiv e) x) = e ∘ extChartAt I x :=
  rfl

theorem coe_extChartAt_transContinuousLinearEquiv_symm (x : M) :
    ⇑(extChartAt (I.transContinuousLinearEquiv e) x).symm = (extChartAt I x).symm ∘ e.symm :=
  rfl

theorem extChartAt_transContinuousLinearEquiv_target (x : M) :
    (extChartAt (I.transContinuousLinearEquiv e) x).target
      = e.symm ⁻¹' (extChartAt I x).target := by
  simp only [range_comp, preimage_preimage, ContinuousLinearEquiv.image_eq_preimage_symm,
    mfld_simps, ← comp_def]

end ModelWithCorners

namespace ContinuousLinearEquiv

variable (e : E ≃L[𝕜] F)

instance instIsManifoldtransContinuousLinearEquiv [IsManifold I n M] :
    IsManifold (I.transContinuousLinearEquiv e) n M := by
  refine isManifold_of_contDiffOn (I.transContinuousLinearEquiv e) n M fun e₁ e₂ h₁ h₂ => ?_
  refine e.contDiff.comp_contDiffOn
      (((contDiffGroupoid n I).compatible h₁ h₂).1.comp e.symm.contDiff.contDiffOn ?_)
  simp [preimage_comp, range_comp, mapsTo_iff_subset_preimage,
    ContinuousLinearEquiv.image_eq_preimage_symm]

variable (I M)

/-- The identity diffeomorphism between a manifold with model `I` and the same manifold
with model `I.trans_diffeomorph e`. -/
def toTransContinuousLinearEquiv (e : E ≃L[𝕜] F) : M ≃ₘ^n⟮I, I.transContinuousLinearEquiv e⟯ M where
  toEquiv := Equiv.refl M
  contMDiff_toFun x := by
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine e.contDiff.contDiffWithinAt.congr_of_mem (fun y hy ↦ ?_) ?_
    · simp only [Equiv.coe_refl, id, (· ∘ ·), I.coe_extChartAt_transContinuousLinearEquiv,
        (extChartAt I x).right_inv hy.1]
    · exact
      ⟨(extChartAt I x).map_source (mem_extChartAt_source x), trivial, by simp only [mfld_simps]⟩
  contMDiff_invFun x := by
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine e.symm.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [mem_inter_iff, I.extChartAt_transContinuousLinearEquiv_target] at hy
      simp only [Equiv.coe_refl, Equiv.refl_symm, id, (· ∘ ·),
        I.coe_extChartAt_transContinuousLinearEquiv_symm, (extChartAt I x).right_inv hy.1]
    exact ⟨(extChartAt _ x).map_source (mem_extChartAt_source x), trivial, by
      simp only [e.symm_apply_apply, Equiv.refl_symm, Equiv.coe_refl, mfld_simps]⟩

variable {I M}

@[simp]
theorem contMDiffWithinAt_transContinuousLinearEquiv_right {f : M' → M} {x s} :
    ContMDiffWithinAt I' (I.transContinuousLinearEquiv e) n f s x
      ↔ CMDiffAt[s] n f x :=
  (toTransContinuousLinearEquiv I M e).contMDiffWithinAt_diffeomorph_comp_iff le_rfl

@[simp]
theorem contMDiffAt_transContinuousLinearEquiv_right {f : M' → M} {x} :
    ContMDiffAt I' (I.transContinuousLinearEquiv e) n f x ↔ CMDiffAt n f x :=
  (toTransContinuousLinearEquiv I M e).contMDiffAt_diffeomorph_comp_iff le_rfl

@[simp]
theorem contMDiffOn_transContinuousLinearEquiv_right {f : M' → M} {s} :
    ContMDiffOn I' (I.transContinuousLinearEquiv e) n f s ↔ CMDiff[s] n f :=
  (toTransContinuousLinearEquiv I M e).contMDiffOn_diffeomorph_comp_iff le_rfl

@[simp]
theorem contMDiff_transContinuousLinearEquiv_right {f : M' → M} :
    ContMDiff I' (I.transContinuousLinearEquiv e) n f ↔ CMDiff n f :=
  (toTransContinuousLinearEquiv I M e).contMDiff_diffeomorph_comp_iff le_rfl

@[simp]
theorem contMDiffWithinAt_transContinuousLinearEquiv_left {f : M → M'} {x s} :
    ContMDiffWithinAt (I.transContinuousLinearEquiv e) I' n f s x ↔ CMDiffAt[s] n f x :=
  ((toTransContinuousLinearEquiv I M e).contMDiffWithinAt_comp_diffeomorph_iff le_rfl).symm

@[simp]
theorem contMDiffAt_transContinuousLinearEquiv_left {f : M → M'} {x} :
    ContMDiffAt (I.transContinuousLinearEquiv e) I' n f x ↔ CMDiffAt n f x :=
  ((toTransContinuousLinearEquiv I M e).contMDiffAt_comp_diffeomorph_iff le_rfl).symm

@[simp]
theorem contMDiffOn_transContinuousLinearEquiv_left {f : M → M'} {s} :
    ContMDiffOn (I.transContinuousLinearEquiv e) I' n f s ↔ CMDiff[s] n f :=
  ((toTransContinuousLinearEquiv I M e).contMDiffOn_comp_diffeomorph_iff le_rfl).symm

@[simp]
theorem contMDiff_transContinuousLinearEquiv_left {f : M → M'} :
    ContMDiff (I.transContinuousLinearEquiv e) I' n f ↔ CMDiff n f :=
  ((toTransContinuousLinearEquiv I M e).contMDiff_comp_diffeomorph_iff le_rfl).symm

end ContinuousLinearEquiv

namespace Diffeomorph

section Constructions

section Product

/-- Product of two diffeomorphisms. -/
def prodCongr (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    (M × N) ≃ₘ^n⟮I.prod J, I'.prod J'⟯ M' × N' where
  contMDiff_toFun := (h₁.contMDiff.comp contMDiff_fst).prodMk (h₂.contMDiff.comp contMDiff_snd)
  contMDiff_invFun :=
    (h₁.symm.contMDiff.comp contMDiff_fst).prodMk (h₂.symm.contMDiff.comp contMDiff_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]
theorem prodCongr_symm (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
theorem coe_prodCongr (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

section

variable (I J J' M N N' n)

/-- `M × N` is diffeomorphic to `N × M`. -/
def prodComm : (M × N) ≃ₘ^n⟮I.prod J, J.prod I⟯ N × M where
  contMDiff_toFun := contMDiff_snd.prodMk contMDiff_fst
  contMDiff_invFun := contMDiff_snd.prodMk contMDiff_fst
  toEquiv := Equiv.prodComm M N

@[simp]
theorem prodComm_symm : (prodComm I J M N n).symm = prodComm J I N M n :=
  rfl

@[simp]
theorem coe_prodComm : ⇑(prodComm I J M N n) = Prod.swap :=
  rfl

/-- `(M × N) × N'` is diffeomorphic to `M × (N × N')`. -/
def prodAssoc : ((M × N) × N') ≃ₘ^n⟮(I.prod J).prod J', I.prod (J.prod J')⟯ M × N × N' where
  contMDiff_toFun :=
    (contMDiff_fst.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd)
  contMDiff_invFun :=
    (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).prodMk
      (contMDiff_snd.comp contMDiff_snd)
  toEquiv := Equiv.prodAssoc M N N'

end

end Product

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  {N J : Type*} [TopologicalSpace N] [ChartedSpace H N] {J : ModelWithCorners 𝕜 E' H}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace H N']

/-- The sum of two diffeomorphisms: this is `Sum.map` as a diffeomorphism. -/
def sumCongr (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    Diffeomorph I J (M ⊕ M') (N ⊕ N') n where
  toEquiv := Equiv.sumCongr φ.toEquiv ψ.toEquiv
  contMDiff_toFun := ContMDiff.sumMap φ.contMDiff_toFun ψ.contMDiff_toFun
  contMDiff_invFun := ContMDiff.sumMap φ.contMDiff_invFun ψ.contMDiff_invFun

lemma sumCongr_symm_symm (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    sumCongr φ.symm ψ.symm = (sumCongr φ ψ).symm := rfl

@[simp, mfld_simps]
lemma sumCongr_coe (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    sumCongr φ ψ = Sum.map φ ψ := rfl

lemma sumCongr_inl (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    (sumCongr φ ψ) ∘ Sum.inl = Sum.inl ∘ φ := rfl

lemma sumCongr_inr (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    (sumCongr φ ψ) ∘ Sum.inr = Sum.inr ∘ ψ := rfl

variable (I M M' n) in
/-- The canonical diffeomorphism `M ⊕ M' → M' ⊕ M`: this is `Sum.swap` as a diffeomorphism -/
def sumComm : Diffeomorph I I (M ⊕ M') (M' ⊕ M) n where
  toEquiv := Equiv.sumComm M M'
  contMDiff_toFun := ContMDiff.swap
  contMDiff_invFun := ContMDiff.swap

@[simp, mfld_simps]
theorem sumComm_coe : (Diffeomorph.sumComm I M n M' : (M ⊕ M') → (M' ⊕ M)) = Sum.swap := rfl

@[simp, mfld_simps]
theorem sumComm_symm : (Diffeomorph.sumComm I M n M').symm = Diffeomorph.sumComm I M' n M := rfl

variable (I M M' n) in
lemma sumComm_inl : (Diffeomorph.sumComm I M n M') ∘ Sum.inl = Sum.inr := by
  ext
  exact Sum.swap_inl

variable (I M M' n) in
lemma sumComm_inr : (Diffeomorph.sumComm I M n M') ∘ Sum.inr = Sum.inl := by
  ext
  exact Sum.swap_inr

variable (I M M' M'' n) in
/-- The canonical diffeomorphism `(M ⊕ N) ⊕ P → M ⊕ (N ⊕ P)` -/
def sumAssoc : Diffeomorph I I ((M ⊕ M') ⊕ M'') (M ⊕ (M' ⊕ M'')) n where
  toEquiv := Equiv.sumAssoc M M' M''
  contMDiff_toFun := by
    apply ContMDiff.sumElim
    · exact contMDiff_id.sumMap ContMDiff.inl
    · exact ContMDiff.inr.comp ContMDiff.inr
  contMDiff_invFun := by
    apply ContMDiff.sumElim
    · exact ContMDiff.inl.comp ContMDiff.inl
    · exact ContMDiff.inr.sumMap contMDiff_id

@[simp]
theorem sumAssoc_coe :
    (sumAssoc I M n M' M'' : (M ⊕ M') ⊕ M'' → M ⊕ (M' ⊕ M'')) = Equiv.sumAssoc M M' M'' := rfl

variable (I M n) in
/-- The canonical diffeomorphism `M ⊕ ∅ → M` -/
def sumEmpty [IsEmpty M'] : Diffeomorph I I (M ⊕ M') M n where
  toEquiv := Equiv.sumEmpty M M'
  contMDiff_toFun := contMDiff_id.sumElim fun x ↦ (IsEmpty.false x).elim
  contMDiff_invFun := ContMDiff.inl

@[simp, mfld_simps]
theorem sumEmpty_toEquiv [IsEmpty M'] : (sumEmpty I M n).toEquiv = Equiv.sumEmpty M M' := rfl

@[simp, mfld_simps]
lemma sumEmpty_apply_inl [IsEmpty M'] (x : M) : (sumEmpty I M (M' := M') n) (Sum.inl x) = x := rfl

/-- The unique diffeomorphism between two empty types -/
protected def empty [IsEmpty M] [IsEmpty M'] : Diffeomorph I I M M' n where
  __ := Equiv.equivOfIsEmpty M M'
  contMDiff_toFun x := (IsEmpty.false x).elim
  contMDiff_invFun x := (IsEmpty.false x).elim

end disjointUnion

end Constructions

end Diffeomorph
