/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Yury Kudryashov
-/
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential

/-!
# Diffeomorphisms
This file implements diffeomorphisms.

## Definitions

* `Diffeomorph I I' M M' n`: `n`-times continuously differentiable diffeomorphism between
  `M` and `M'` with respect to I and I'; we do not introduce a separate definition for the case
  `n = ∞`; we use notation instead.
* `Diffeomorph.toHomeomorph`: reinterpret a diffeomorphism as a homeomorphism.
* `ContinuousLinearEquiv.toDiffeomorph`: reinterpret a continuous equivalence as
  a diffeomorphism.
* `ModelWithCorners.transDiffeomorph`: compose a given `ModelWithCorners` with a diffeomorphism
  between the old and the new target spaces. Useful, e.g, to turn any finite dimensional manifold
  into a manifold modelled on a Euclidean space.
* `Diffeomorph.toTransDiffeomorph`: the identity diffeomorphism between `M` with model `I` and `M`
  with model `I.trans_diffeomorph e`.

## Notations

* `M ≃ₘ^n⟮I, I'⟯ M'`  := `Diffeomorph I J M N n`
* `M ≃ₘ⟮I, I'⟯ M'`    := `Diffeomorph I J M N ⊤`
* `E ≃ₘ^n[𝕜] E'`      := `E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`
* `E ≃ₘ[𝕜] E'`        := `E ≃ₘ⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Keywords

diffeomorphism, manifold
-/


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
  [TopologicalSpace N'] [ChartedSpace G' N'] {n : ℕ∞}

section Defs

variable (I I' M M' n)

/-- `n`-times continuously differentiable diffeomorphism between `M` and `M'` with respect to `I`
and `I'`. -/
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/5171): was @[nolint has_nonempty_instance]
structure Diffeomorph extends M ≃ M' where
  protected contMDiff_toFun : ContMDiff I I' n toEquiv
  protected contMDiff_invFun : ContMDiff I' I n toEquiv.symm

end Defs

@[inherit_doc]
scoped[Manifold] notation M " ≃ₘ^" n:1000 "⟮" I ", " J "⟯ " N => Diffeomorph I J M N n

/-- Infinitely differentiable diffeomorphism between `M` and `M'` with respect to `I` and `I'`. -/
scoped[Manifold] notation M " ≃ₘ⟮" I ", " J "⟯ " N => Diffeomorph I J M N ⊤

/-- `n`-times continuously differentiable diffeomorphism between `E` and `E'`. -/
scoped[Manifold] notation E " ≃ₘ^" n:1000 "[" 𝕜 "] " E' => Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') E E' n

/-- Infinitely differentiable diffeomorphism between `E` and `E'`. -/
scoped[Manifold]
  notation3 E " ≃ₘ[" 𝕜 "] " E' =>
    Diffeomorph (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') E E' ⊤

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

protected theorem contMDiff (h : M ≃ₘ^n⟮I, I'⟯ M') : ContMDiff I I' n h :=
  h.contMDiff_toFun

protected theorem contMDiffAt (h : M ≃ₘ^n⟮I, I'⟯ M') {x} : ContMDiffAt I I' n h x :=
  h.contMDiff.contMDiffAt

protected theorem contMDiffWithinAt (h : M ≃ₘ^n⟮I, I'⟯ M') {s x} : ContMDiffWithinAt I I' n h s x :=
  h.contMDiffAt.contMDiffWithinAt

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: should use `E ≃ₘ^n[𝕜] F` notation
protected theorem contDiff (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E') : ContDiff 𝕜 n h :=
  h.contMDiff.contDiff

@[deprecated (since := "2024-11-21")] alias smooth := Diffeomorph.contDiff

protected theorem mdifferentiable (h : M ≃ₘ^n⟮I, I'⟯ M') (hn : 1 ≤ n) : MDifferentiable I I' h :=
  h.contMDiff.mdifferentiable hn

protected theorem mdifferentiableOn (h : M ≃ₘ^n⟮I, I'⟯ M') (s : Set M) (hn : 1 ≤ n) :
    MDifferentiableOn I I' h s :=
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

@[simp]
theorem contMDiffWithinAt_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {s x}
    (hm : m ≤ n) :
    ContMDiffWithinAt I I' m (f ∘ h) s x ↔ ContMDiffWithinAt J I' m f (h.symm ⁻¹' s) (h x) := by
  constructor
  · intro Hfh
    rw [← h.symm_apply_apply x] at Hfh
    simpa only [Function.comp_def, h.apply_symm_apply] using
      Hfh.comp (h x) (h.symm.contMDiffWithinAt.of_le hm) (mapsTo_preimage _ _)
  · rw [← h.image_eq_preimage]
    exact fun hf => hf.comp x (h.contMDiffWithinAt.of_le hm) (mapsTo_image _ _)

@[simp]
theorem contMDiffOn_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {s} (hm : m ≤ n) :
    ContMDiffOn I I' m (f ∘ h) s ↔ ContMDiffOn J I' m f (h.symm ⁻¹' s) :=
  h.toEquiv.forall_congr fun {_} => by
    simp only [hm, coe_toEquiv, h.symm_apply_apply, contMDiffWithinAt_comp_diffeomorph_iff,
      mem_preimage]

@[simp]
theorem contMDiffAt_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {x} (hm : m ≤ n) :
    ContMDiffAt I I' m (f ∘ h) x ↔ ContMDiffAt J I' m f (h x) :=
  h.contMDiffWithinAt_comp_diffeomorph_iff hm

@[simp]
theorem contMDiff_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} (hm : m ≤ n) :
    ContMDiff I I' m (f ∘ h) ↔ ContMDiff J I' m f :=
  h.toEquiv.forall_congr fun _ ↦ h.contMDiffAt_comp_diffeomorph_iff hm

@[simp]
theorem contMDiffWithinAt_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n)
    {s x} : ContMDiffWithinAt I' J m (h ∘ f) s x ↔ ContMDiffWithinAt I' I m f s x :=
  ⟨fun Hhf => by
    simpa only [Function.comp_def, h.symm_apply_apply] using
      (h.symm.contMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hhf,
    fun Hf => (h.contMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hf⟩

@[simp]
theorem contMDiffAt_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n) {x} :
    ContMDiffAt I' J m (h ∘ f) x ↔ ContMDiffAt I' I m f x :=
  h.contMDiffWithinAt_diffeomorph_comp_iff hm

@[simp]
theorem contMDiffOn_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n) {s} :
    ContMDiffOn I' J m (h ∘ f) s ↔ ContMDiffOn I' I m f s :=
  forall₂_congr fun _ _ => h.contMDiffWithinAt_diffeomorph_comp_iff hm

@[simp]
theorem contMDiff_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n) :
    ContMDiff I' J m (h ∘ f) ↔ ContMDiff I' I m f :=
  forall_congr' fun _ => h.contMDiffWithinAt_diffeomorph_comp_iff hm

theorem toPartialHomeomorph_mdifferentiable (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) :
    h.toHomeomorph.toPartialHomeomorph.MDifferentiable I J :=
  ⟨h.mdifferentiableOn _ hn, h.symm.mdifferentiableOn _ hn⟩

section Constructions

/-- Product of two diffeomorphisms. -/
def prodCongr (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    (M × N) ≃ₘ^n⟮I.prod J, I'.prod J'⟯ M' × N' where
  contMDiff_toFun := (h₁.contMDiff.comp contMDiff_fst).prod_mk (h₂.contMDiff.comp contMDiff_snd)
  contMDiff_invFun :=
    (h₁.symm.contMDiff.comp contMDiff_fst).prod_mk (h₂.symm.contMDiff.comp contMDiff_snd)
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
  contMDiff_toFun := contMDiff_snd.prod_mk contMDiff_fst
  contMDiff_invFun := contMDiff_snd.prod_mk contMDiff_fst
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
    (contMDiff_fst.comp contMDiff_fst).prod_mk
      ((contMDiff_snd.comp contMDiff_fst).prod_mk contMDiff_snd)
  contMDiff_invFun :=
    (contMDiff_fst.prod_mk (contMDiff_fst.comp contMDiff_snd)).prod_mk
      (contMDiff_snd.comp contMDiff_snd)
  toEquiv := Equiv.prodAssoc M N N'

end

end Constructions

theorem uniqueMDiffOn_image_aux (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) {s : Set M}
    (hs : UniqueMDiffOn I s) : UniqueMDiffOn J (h '' s) := by
  convert hs.uniqueMDiffOn_preimage (h.toPartialHomeomorph_mdifferentiable hn)
  simp [h.image_eq_preimage]

@[simp]
theorem uniqueMDiffOn_image (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) {s : Set M} :
    UniqueMDiffOn J (h '' s) ↔ UniqueMDiffOn I s :=
  ⟨fun hs => h.symm_image_image s ▸ h.symm.uniqueMDiffOn_image_aux hn hs,
    h.uniqueMDiffOn_image_aux hn⟩

@[simp]
theorem uniqueMDiffOn_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) {s : Set N} :
    UniqueMDiffOn I (h ⁻¹' s) ↔ UniqueMDiffOn J s :=
  h.symm_image_eq_preimage s ▸ h.symm.uniqueMDiffOn_image hn

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: should use `E ≃ₘ^n[𝕜] F` notation
@[simp]
theorem uniqueDiffOn_image (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : 1 ≤ n) {s : Set E} :
    UniqueDiffOn 𝕜 (h '' s) ↔ UniqueDiffOn 𝕜 s := by
  simp only [← uniqueMDiffOn_iff_uniqueDiffOn, uniqueMDiffOn_image, hn]

@[simp]
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: should use `E ≃ₘ^n[𝕜] F` notation
theorem uniqueDiffOn_preimage (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : 1 ≤ n) {s : Set F} :
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

variable (I) (e : E ≃ₘ[𝕜] E')

/-- Apply a diffeomorphism (e.g., a continuous linear equivalence) to the model vector space. -/
def transDiffeomorph (I : ModelWithCorners 𝕜 E H) (e : E ≃ₘ[𝕜] E') : ModelWithCorners 𝕜 E' H where
  toPartialEquiv := I.toPartialEquiv.trans e.toEquiv.toPartialEquiv
  source_eq := by simp
  uniqueDiffOn' := by simp [range_comp e, I.uniqueDiffOn]
  target_subset_closure_interior := by
    simp only [PartialEquiv.trans_target, Equiv.toPartialEquiv_target,
      Equiv.toPartialEquiv_symm_apply, Diffeomorph.toEquiv_coe_symm, target_eq, univ_inter]
    change e.toHomeomorph.symm ⁻¹' _ ⊆ closure (interior (e.toHomeomorph.symm ⁻¹' (range I)))
    rw [← e.toHomeomorph.symm.isOpenMap.preimage_interior_eq_interior_preimage
      e.toHomeomorph.continuous_symm,
      ← e.toHomeomorph.symm.isOpenMap.preimage_closure_eq_closure_preimage
      e.toHomeomorph.continuous_symm]
    exact preimage_mono I.range_subset_closure_interior
  continuous_toFun := e.continuous.comp I.continuous
  continuous_invFun := I.continuous_symm.comp e.symm.continuous

@[simp, mfld_simps]
theorem coe_transDiffeomorph : ⇑(I.transDiffeomorph e) = e ∘ I :=
  rfl

@[simp, mfld_simps]
theorem coe_transDiffeomorph_symm : ⇑(I.transDiffeomorph e).symm = I.symm ∘ e.symm :=
  rfl

theorem transDiffeomorph_range : range (I.transDiffeomorph e) = e '' range I :=
  range_comp e I

theorem coe_extChartAt_transDiffeomorph (x : M) :
    ⇑(extChartAt (I.transDiffeomorph e) x) = e ∘ extChartAt I x :=
  rfl

theorem coe_extChartAt_transDiffeomorph_symm (x : M) :
    ⇑(extChartAt (I.transDiffeomorph e) x).symm = (extChartAt I x).symm ∘ e.symm :=
  rfl

theorem extChartAt_transDiffeomorph_target (x : M) :
    (extChartAt (I.transDiffeomorph e) x).target = e.symm ⁻¹' (extChartAt I x).target := by
  simp only [e.range_comp, preimage_preimage, mfld_simps]; rfl

end ModelWithCorners

namespace Diffeomorph

variable (e : E ≃ₘ[𝕜] F)

instance smoothManifoldWithCorners_transDiffeomorph [SmoothManifoldWithCorners I M] :
    SmoothManifoldWithCorners (I.transDiffeomorph e) M := by
  refine smoothManifoldWithCorners_of_contDiffOn (I.transDiffeomorph e) M fun e₁ e₂ h₁ h₂ => ?_
  refine e.contDiff.comp_contDiffOn
      (((contDiffGroupoid ∞ I).compatible h₁ h₂).1.comp e.symm.contDiff.contDiffOn ?_)
  simp only [mapsTo_iff_subset_preimage]
  mfld_set_tac

variable (I M)

/-- The identity diffeomorphism between a manifold with model `I` and the same manifold
with model `I.trans_diffeomorph e`. -/
def toTransDiffeomorph (e : E ≃ₘ[𝕜] F) : M ≃ₘ⟮I, I.transDiffeomorph e⟯ M where
  toEquiv := Equiv.refl M
  contMDiff_toFun x := by
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine e.contDiff.contDiffWithinAt.congr_of_mem (fun y hy ↦ ?_) ?_
    · simp only [Equiv.coe_refl, id, (· ∘ ·), I.coe_extChartAt_transDiffeomorph,
        (extChartAt I x).right_inv hy.1]
    · exact
      ⟨(extChartAt I x).map_source (mem_extChartAt_source x), trivial, by simp only [mfld_simps]⟩
  contMDiff_invFun x := by
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine e.symm.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [mem_inter_iff, I.extChartAt_transDiffeomorph_target] at hy
      simp only [Equiv.coe_refl, Equiv.refl_symm, id, (· ∘ ·),
        I.coe_extChartAt_transDiffeomorph_symm, (extChartAt I x).right_inv hy.1]
    exact ⟨(extChartAt _ x).map_source (mem_extChartAt_source x), trivial, by
      simp only [e.symm_apply_apply, Equiv.refl_symm, Equiv.coe_refl, mfld_simps]⟩

variable {I M}

@[simp]
theorem contMDiffWithinAt_transDiffeomorph_right {f : M' → M} {x s} :
    ContMDiffWithinAt I' (I.transDiffeomorph e) n f s x ↔ ContMDiffWithinAt I' I n f s x :=
  (toTransDiffeomorph I M e).contMDiffWithinAt_diffeomorph_comp_iff le_top

@[simp]
theorem contMDiffAt_transDiffeomorph_right {f : M' → M} {x} :
    ContMDiffAt I' (I.transDiffeomorph e) n f x ↔ ContMDiffAt I' I n f x :=
  (toTransDiffeomorph I M e).contMDiffAt_diffeomorph_comp_iff le_top

@[simp]
theorem contMDiffOn_transDiffeomorph_right {f : M' → M} {s} :
    ContMDiffOn I' (I.transDiffeomorph e) n f s ↔ ContMDiffOn I' I n f s :=
  (toTransDiffeomorph I M e).contMDiffOn_diffeomorph_comp_iff le_top

@[simp]
theorem contMDiff_transDiffeomorph_right {f : M' → M} :
    ContMDiff I' (I.transDiffeomorph e) n f ↔ ContMDiff I' I n f :=
  (toTransDiffeomorph I M e).contMDiff_diffeomorph_comp_iff le_top

@[deprecated (since := "2024-11-21")]
alias smooth_transDiffeomorph_right := contMDiff_transDiffeomorph_right

@[simp]
theorem contMDiffWithinAt_transDiffeomorph_left {f : M → M'} {x s} :
    ContMDiffWithinAt (I.transDiffeomorph e) I' n f s x ↔ ContMDiffWithinAt I I' n f s x :=
  ((toTransDiffeomorph I M e).contMDiffWithinAt_comp_diffeomorph_iff le_top).symm

@[simp]
theorem contMDiffAt_transDiffeomorph_left {f : M → M'} {x} :
    ContMDiffAt (I.transDiffeomorph e) I' n f x ↔ ContMDiffAt I I' n f x :=
  ((toTransDiffeomorph I M e).contMDiffAt_comp_diffeomorph_iff le_top).symm

@[simp]
theorem contMDiffOn_transDiffeomorph_left {f : M → M'} {s} :
    ContMDiffOn (I.transDiffeomorph e) I' n f s ↔ ContMDiffOn I I' n f s :=
  ((toTransDiffeomorph I M e).contMDiffOn_comp_diffeomorph_iff le_top).symm

@[simp]
theorem contMDiff_transDiffeomorph_left {f : M → M'} :
    ContMDiff (I.transDiffeomorph e) I' n f ↔ ContMDiff I I' n f :=
  ((toTransDiffeomorph I M e).contMDiff_comp_diffeomorph_iff le_top).symm

@[deprecated (since := "2024-11-21")]
alias smooth_transDiffeomorph_left := contMDiff_transDiffeomorph_left

end Diffeomorph
