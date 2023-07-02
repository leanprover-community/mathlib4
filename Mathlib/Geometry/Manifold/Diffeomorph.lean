/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Yury Kudryashov

! This file was ported from Lean 3 source module geometry.manifold.diffeomorph
! leanprover-community/mathlib commit e354e865255654389cc46e6032160238df2e0f40
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Manifold.ContMdiffMap
import Mathbin.Geometry.Manifold.ContMdiffMfderiv

/-!
# Diffeomorphisms
This file implements diffeomorphisms.

## Definitions

* `diffeomorph I I' M M' n`:  `n`-times continuously differentiable diffeomorphism between
  `M` and `M'` with respect to I and I'; we do not introduce a separate definition for the case
  `n = ∞`; we use notation instead.
* `diffeomorph.to_homeomorph`: reinterpret a diffeomorphism as a homeomorphism.
* `continuous_linear_equiv.to_diffeomorph`: reinterpret a continuous equivalence as
  a diffeomorphism.
* `model_with_corners.trans_diffeomorph`: compose a given `model_with_corners` with a diffeomorphism
  between the old and the new target spaces. Useful, e.g, to turn any finite dimensional manifold
  into a manifold modelled on a Euclidean space.
* `diffeomorph.to_trans_diffeomorph`: the identity diffeomorphism between `M` with model `I` and `M`
  with model `I.trans_diffeomorph e`.

## Notations

* `M ≃ₘ^n⟮I, I'⟯ M'`  := `diffeomorph I J M N n`
* `M ≃ₘ⟮I, I'⟯ M'`    := `diffeomorph I J M N ⊤`
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


open scoped Manifold Topology

open Function Set

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type _}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type _} [TopologicalSpace H] {H' : Type _}
  [TopologicalSpace H'] {G : Type _} [TopologicalSpace G] {G' : Type _} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 F G}
  {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] {M' : Type _} [TopologicalSpace M']
  [ChartedSpace H' M'] {N : Type _} [TopologicalSpace N] [ChartedSpace G N] {N' : Type _}
  [TopologicalSpace N'] [ChartedSpace G' N'] {n : ℕ∞}

section Defs

variable (I I' M M' n)

/--
`n`-times continuously differentiable diffeomorphism between `M` and `M'` with respect to I and I'
-/
@[protect_proj, nolint has_nonempty_instance]
structure Diffeomorph extends M ≃ M' where
  contMDiff_to_fun : ContMDiff I I' n to_equiv
  contMDiff_inv_fun : ContMDiff I' I n to_equiv.symm
#align diffeomorph Diffeomorph

end Defs

scoped[Manifold] notation M " ≃ₘ^" n:1000 "⟮" I ", " J "⟯ " N => Diffeomorph I J M N n

scoped[Manifold] notation M " ≃ₘ⟮" I ", " J "⟯ " N => Diffeomorph I J M N ⊤

scoped[Manifold]
  notation E " ≃ₘ^" n:1000 "[" 𝕜 "] " E' =>
    Diffeomorph (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') E E' n

scoped[Manifold]
  notation E " ≃ₘ[" 𝕜 "] " E' =>
    Diffeomorph (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') E E' ⊤

namespace Diffeomorph

instance : CoeFun (M ≃ₘ^n⟮I, I'⟯ M') fun _ => M → M' :=
  ⟨fun e => e.toEquiv⟩

instance : Coe (M ≃ₘ^n⟮I, I'⟯ M') C^n⟮I, M; I', M'⟯ :=
  ⟨fun Φ => ⟨Φ, Φ.contMDiff_to_fun⟩⟩

@[continuity]
protected theorem continuous (h : M ≃ₘ^n⟮I, I'⟯ M') : Continuous h :=
  h.contMDiff_to_fun.Continuous
#align diffeomorph.continuous Diffeomorph.continuous

protected theorem contMDiff (h : M ≃ₘ^n⟮I, I'⟯ M') : ContMDiff I I' n h :=
  h.contMDiff_to_fun
#align diffeomorph.cont_mdiff Diffeomorph.contMDiff

protected theorem contMDiffAt (h : M ≃ₘ^n⟮I, I'⟯ M') {x} : ContMDiffAt I I' n h x :=
  h.ContMDiff.ContMDiffAt
#align diffeomorph.cont_mdiff_at Diffeomorph.contMDiffAt

protected theorem contMDiffWithinAt (h : M ≃ₘ^n⟮I, I'⟯ M') {s x} : ContMDiffWithinAt I I' n h s x :=
  h.ContMDiffAt.ContMDiffWithinAt
#align diffeomorph.cont_mdiff_within_at Diffeomorph.contMDiffWithinAt

protected theorem contDiff (h : E ≃ₘ^n[𝕜] E') : ContDiff 𝕜 n h :=
  h.ContMDiff.ContDiff
#align diffeomorph.cont_diff Diffeomorph.contDiff

protected theorem smooth (h : M ≃ₘ⟮I, I'⟯ M') : Smooth I I' h :=
  h.contMDiff_to_fun
#align diffeomorph.smooth Diffeomorph.smooth

protected theorem mDifferentiable (h : M ≃ₘ^n⟮I, I'⟯ M') (hn : 1 ≤ n) : MDifferentiable I I' h :=
  h.ContMDiff.MDifferentiable hn
#align diffeomorph.mdifferentiable Diffeomorph.mDifferentiable

protected theorem mDifferentiableOn (h : M ≃ₘ^n⟮I, I'⟯ M') (s : Set M) (hn : 1 ≤ n) :
    MDifferentiableOn I I' h s :=
  (h.MDifferentiable hn).MDifferentiableOn
#align diffeomorph.mdifferentiable_on Diffeomorph.mDifferentiableOn

@[simp]
theorem coe_toEquiv (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑h.toEquiv = h :=
  rfl
#align diffeomorph.coe_to_equiv Diffeomorph.coe_toEquiv

@[simp, norm_cast]
theorem coe_coe (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑(h : C^n⟮I, M; I', M'⟯) = h :=
  rfl
#align diffeomorph.coe_coe Diffeomorph.coe_coe

theorem toEquiv_injective : Injective (Diffeomorph.toEquiv : (M ≃ₘ^n⟮I, I'⟯ M') → M ≃ M')
  | ⟨e, _, _⟩, ⟨e', _, _⟩, rfl => rfl
#align diffeomorph.to_equiv_injective Diffeomorph.toEquiv_injective

@[simp]
theorem toEquiv_inj {h h' : M ≃ₘ^n⟮I, I'⟯ M'} : h.toEquiv = h'.toEquiv ↔ h = h' :=
  toEquiv_injective.eq_iff
#align diffeomorph.to_equiv_inj Diffeomorph.toEquiv_inj

/-- Coercion to function `λ h : M ≃ₘ^n⟮I, I'⟯ M', (h : M → M')` is injective. -/
theorem coeFn_injective : Injective fun (h : M ≃ₘ^n⟮I, I'⟯ M') (x : M) => h x :=
  Equiv.coe_fn_injective.comp toEquiv_injective
#align diffeomorph.coe_fn_injective Diffeomorph.coeFn_injective

@[ext]
theorem ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : ∀ x, h x = h' x) : h = h' :=
  coeFn_injective <| funext Heq
#align diffeomorph.ext Diffeomorph.ext

instance : ContinuousMapClass (M ≃ₘ⟮I, J⟯ N) M N
    where
  coe := coeFn
  coe_injective' := coeFn_injective
  map_continuous f := f.Continuous

section

variable (M I n)

/-- Identity map as a diffeomorphism. -/
protected def refl : M ≃ₘ^n⟮I, I⟯ M
    where
  contMDiff_to_fun := contMDiff_id
  contMDiff_inv_fun := contMDiff_id
  toEquiv := Equiv.refl M
#align diffeomorph.refl Diffeomorph.refl

@[simp]
theorem refl_toEquiv : (Diffeomorph.refl I M n).toEquiv = Equiv.refl _ :=
  rfl
#align diffeomorph.refl_to_equiv Diffeomorph.refl_toEquiv

@[simp]
theorem coe_refl : ⇑(Diffeomorph.refl I M n) = id :=
  rfl
#align diffeomorph.coe_refl Diffeomorph.coe_refl

end

/-- Composition of two diffeomorphisms. -/
protected def trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) : M ≃ₘ^n⟮I, J⟯ N
    where
  contMDiff_to_fun := h₂.contMDiff_to_fun.comp h₁.contMDiff_to_fun
  contMDiff_inv_fun := h₁.contMDiff_inv_fun.comp h₂.contMDiff_inv_fun
  toEquiv := h₁.toEquiv.trans h₂.toEquiv
#align diffeomorph.trans Diffeomorph.trans

@[simp]
theorem trans_refl (h : M ≃ₘ^n⟮I, I'⟯ M') : h.trans (Diffeomorph.refl I' M' n) = h :=
  ext fun _ => rfl
#align diffeomorph.trans_refl Diffeomorph.trans_refl

@[simp]
theorem refl_trans (h : M ≃ₘ^n⟮I, I'⟯ M') : (Diffeomorph.refl I M n).trans h = h :=
  ext fun _ => rfl
#align diffeomorph.refl_trans Diffeomorph.refl_trans

@[simp]
theorem coe_trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) : ⇑(h₁.trans h₂) = h₂ ∘ h₁ :=
  rfl
#align diffeomorph.coe_trans Diffeomorph.coe_trans

/-- Inverse of a diffeomorphism. -/
protected def symm (h : M ≃ₘ^n⟮I, J⟯ N) : N ≃ₘ^n⟮J, I⟯ M
    where
  contMDiff_to_fun := h.contMDiff_inv_fun
  contMDiff_inv_fun := h.contMDiff_to_fun
  toEquiv := h.toEquiv.symm
#align diffeomorph.symm Diffeomorph.symm

@[simp]
theorem apply_symm_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x : N) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x
#align diffeomorph.apply_symm_apply Diffeomorph.apply_symm_apply

@[simp]
theorem symm_apply_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x : M) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x
#align diffeomorph.symm_apply_apply Diffeomorph.symm_apply_apply

@[simp]
theorem symm_refl : (Diffeomorph.refl I M n).symm = Diffeomorph.refl I M n :=
  ext fun _ => rfl
#align diffeomorph.symm_refl Diffeomorph.symm_refl

@[simp]
theorem self_trans_symm (h : M ≃ₘ^n⟮I, J⟯ N) : h.trans h.symm = Diffeomorph.refl I M n :=
  ext h.symm_apply_apply
#align diffeomorph.self_trans_symm Diffeomorph.self_trans_symm

@[simp]
theorem symm_trans_self (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.trans h = Diffeomorph.refl J N n :=
  ext h.apply_symm_apply
#align diffeomorph.symm_trans_self Diffeomorph.symm_trans_self

@[simp]
theorem symm_trans' (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) :
    (h₁.trans h₂).symm = h₂.symm.trans h₁.symm :=
  rfl
#align diffeomorph.symm_trans' Diffeomorph.symm_trans'

@[simp]
theorem symm_toEquiv (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.toEquiv = h.toEquiv.symm :=
  rfl
#align diffeomorph.symm_to_equiv Diffeomorph.symm_toEquiv

@[simp, mfld_simps]
theorem toEquiv_coe_symm (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toEquiv.symm = h.symm :=
  rfl
#align diffeomorph.to_equiv_coe_symm Diffeomorph.toEquiv_coe_symm

theorem image_eq_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) : h '' s = h.symm ⁻¹' s :=
  h.toEquiv.image_eq_preimage s
#align diffeomorph.image_eq_preimage Diffeomorph.image_eq_preimage

theorem symm_image_eq_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N) : h.symm '' s = h ⁻¹' s :=
  h.symm.image_eq_preimage s
#align diffeomorph.symm_image_eq_preimage Diffeomorph.symm_image_eq_preimage

@[simp, mfld_simps]
theorem range_comp {α} (h : M ≃ₘ^n⟮I, J⟯ N) (f : α → M) : range (h ∘ f) = h.symm ⁻¹' range f := by
  rw [range_comp, image_eq_preimage]
#align diffeomorph.range_comp Diffeomorph.range_comp

@[simp]
theorem image_symm_image (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N) : h '' (h.symm '' s) = s :=
  h.toEquiv.image_symm_image s
#align diffeomorph.image_symm_image Diffeomorph.image_symm_image

@[simp]
theorem symm_image_image (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) : h.symm '' (h '' s) = s :=
  h.toEquiv.symm_image_image s
#align diffeomorph.symm_image_image Diffeomorph.symm_image_image

/-- A diffeomorphism is a homeomorphism. -/
def toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : M ≃ₜ N :=
  ⟨h.toEquiv, h.Continuous, h.symm.Continuous⟩
#align diffeomorph.to_homeomorph Diffeomorph.toHomeomorph

@[simp]
theorem toHomeomorph_toEquiv (h : M ≃ₘ^n⟮I, J⟯ N) : h.toHomeomorph.toEquiv = h.toEquiv :=
  rfl
#align diffeomorph.to_homeomorph_to_equiv Diffeomorph.toHomeomorph_toEquiv

@[simp]
theorem symm_toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.toHomeomorph = h.toHomeomorph.symm :=
  rfl
#align diffeomorph.symm_to_homeomorph Diffeomorph.symm_toHomeomorph

@[simp]
theorem coe_toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toHomeomorph = h :=
  rfl
#align diffeomorph.coe_to_homeomorph Diffeomorph.coe_toHomeomorph

@[simp]
theorem coe_toHomeomorph_symm (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toHomeomorph.symm = h.symm :=
  rfl
#align diffeomorph.coe_to_homeomorph_symm Diffeomorph.coe_toHomeomorph_symm

@[simp]
theorem contMDiffWithinAt_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {s x}
    (hm : m ≤ n) :
    ContMDiffWithinAt I I' m (f ∘ h) s x ↔ ContMDiffWithinAt J I' m f (h.symm ⁻¹' s) (h x) :=
  by
  constructor
  · intro Hfh
    rw [← h.symm_apply_apply x] at Hfh 
    simpa only [(· ∘ ·), h.apply_symm_apply] using
      Hfh.comp (h x) (h.symm.cont_mdiff_within_at.of_le hm) (maps_to_preimage _ _)
  · rw [← h.image_eq_preimage]
    exact fun hf => hf.comp x (h.cont_mdiff_within_at.of_le hm) (maps_to_image _ _)
#align diffeomorph.cont_mdiff_within_at_comp_diffeomorph_iff Diffeomorph.contMDiffWithinAt_comp_diffeomorph_iff

@[simp]
theorem contMDiffOn_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {s} (hm : m ≤ n) :
    ContMDiffOn I I' m (f ∘ h) s ↔ ContMDiffOn J I' m f (h.symm ⁻¹' s) :=
  h.toEquiv.forall_congr' fun x => by
    simp only [hm, coe_to_equiv, symm_apply_apply, cont_mdiff_within_at_comp_diffeomorph_iff,
      mem_preimage]
#align diffeomorph.cont_mdiff_on_comp_diffeomorph_iff Diffeomorph.contMDiffOn_comp_diffeomorph_iff

@[simp]
theorem contMDiffAt_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {x} (hm : m ≤ n) :
    ContMDiffAt I I' m (f ∘ h) x ↔ ContMDiffAt J I' m f (h x) :=
  h.contMDiffWithinAt_comp_diffeomorph_iff hm
#align diffeomorph.cont_mdiff_at_comp_diffeomorph_iff Diffeomorph.contMDiffAt_comp_diffeomorph_iff

@[simp]
theorem contMDiff_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} (hm : m ≤ n) :
    ContMDiff I I' m (f ∘ h) ↔ ContMDiff J I' m f :=
  h.toEquiv.forall_congr' fun x => h.contMDiffAt_comp_diffeomorph_iff hm
#align diffeomorph.cont_mdiff_comp_diffeomorph_iff Diffeomorph.contMDiff_comp_diffeomorph_iff

@[simp]
theorem contMDiffWithinAt_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n)
    {s x} : ContMDiffWithinAt I' J m (h ∘ f) s x ↔ ContMDiffWithinAt I' I m f s x :=
  ⟨fun Hhf => by
    simpa only [(· ∘ ·), h.symm_apply_apply] using
      (h.symm.cont_mdiff_at.of_le hm).comp_contMDiffWithinAt _ Hhf,
    fun Hf => (h.ContMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hf⟩
#align diffeomorph.cont_mdiff_within_at_diffeomorph_comp_iff Diffeomorph.contMDiffWithinAt_diffeomorph_comp_iff

@[simp]
theorem contMDiffAt_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n) {x} :
    ContMDiffAt I' J m (h ∘ f) x ↔ ContMDiffAt I' I m f x :=
  h.contMDiffWithinAt_diffeomorph_comp_iff hm
#align diffeomorph.cont_mdiff_at_diffeomorph_comp_iff Diffeomorph.contMDiffAt_diffeomorph_comp_iff

@[simp]
theorem contMDiffOn_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n) {s} :
    ContMDiffOn I' J m (h ∘ f) s ↔ ContMDiffOn I' I m f s :=
  forall₂_congr fun x hx => h.contMDiffWithinAt_diffeomorph_comp_iff hm
#align diffeomorph.cont_mdiff_on_diffeomorph_comp_iff Diffeomorph.contMDiffOn_diffeomorph_comp_iff

@[simp]
theorem contMDiff_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n) :
    ContMDiff I' J m (h ∘ f) ↔ ContMDiff I' I m f :=
  forall_congr' fun x => h.contMDiffWithinAt_diffeomorph_comp_iff hm
#align diffeomorph.cont_mdiff_diffeomorph_comp_iff Diffeomorph.contMDiff_diffeomorph_comp_iff

theorem toLocalHomeomorph_mDifferentiable (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) :
    h.toHomeomorph.toLocalHomeomorph.MDifferentiable I J :=
  ⟨h.MDifferentiableOn _ hn, h.symm.MDifferentiableOn _ hn⟩
#align diffeomorph.to_local_homeomorph_mdifferentiable Diffeomorph.toLocalHomeomorph_mDifferentiable

section Constructions

/-- Product of two diffeomorphisms. -/
def prodCongr (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    (M × N) ≃ₘ^n⟮I.Prod J, I'.Prod J'⟯ M' × N'
    where
  contMDiff_to_fun := (h₁.ContMDiff.comp contMDiff_fst).prod_mk (h₂.ContMDiff.comp contMDiff_snd)
  contMDiff_inv_fun :=
    (h₁.symm.ContMDiff.comp contMDiff_fst).prod_mk (h₂.symm.ContMDiff.comp contMDiff_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv
#align diffeomorph.prod_congr Diffeomorph.prodCongr

@[simp]
theorem prodCongr_symm (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl
#align diffeomorph.prod_congr_symm Diffeomorph.prodCongr_symm

@[simp]
theorem coe_prodCongr (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl
#align diffeomorph.coe_prod_congr Diffeomorph.coe_prodCongr

section

variable (I J J' M N N' n)

/-- `M × N` is diffeomorphic to `N × M`. -/
def prodComm : (M × N) ≃ₘ^n⟮I.Prod J, J.Prod I⟯ N × M
    where
  contMDiff_to_fun := contMDiff_snd.prod_mk contMDiff_fst
  contMDiff_inv_fun := contMDiff_snd.prod_mk contMDiff_fst
  toEquiv := Equiv.prodComm M N
#align diffeomorph.prod_comm Diffeomorph.prodComm

@[simp]
theorem prodComm_symm : (prodComm I J M N n).symm = prodComm J I N M n :=
  rfl
#align diffeomorph.prod_comm_symm Diffeomorph.prodComm_symm

@[simp]
theorem coe_prodComm : ⇑(prodComm I J M N n) = Prod.swap :=
  rfl
#align diffeomorph.coe_prod_comm Diffeomorph.coe_prodComm

/-- `(M × N) × N'` is diffeomorphic to `M × (N × N')`. -/
def prodAssoc : ((M × N) × N') ≃ₘ^n⟮(I.Prod J).Prod J', I.Prod (J.Prod J')⟯ M × N × N'
    where
  contMDiff_to_fun :=
    (contMDiff_fst.comp contMDiff_fst).prod_mk
      ((contMDiff_snd.comp contMDiff_fst).prod_mk contMDiff_snd)
  contMDiff_inv_fun :=
    (contMDiff_fst.prod_mk (contMDiff_fst.comp contMDiff_snd)).prod_mk
      (contMDiff_snd.comp contMDiff_snd)
  toEquiv := Equiv.prodAssoc M N N'
#align diffeomorph.prod_assoc Diffeomorph.prodAssoc

end

end Constructions

variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N]

theorem uniqueMDiffOn_image_aux (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) {s : Set M}
    (hs : UniqueMDiffOn I s) : UniqueMDiffOn J (h '' s) :=
  by
  convert hs.unique_mdiff_on_preimage (h.to_local_homeomorph_mdifferentiable hn)
  simp [h.image_eq_preimage]
#align diffeomorph.unique_mdiff_on_image_aux Diffeomorph.uniqueMDiffOn_image_aux

@[simp]
theorem uniqueMDiffOn_image (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) {s : Set M} :
    UniqueMDiffOn J (h '' s) ↔ UniqueMDiffOn I s :=
  ⟨fun hs => h.symm_image_image s ▸ h.symm.uniqueMDiffOn_image_aux hn hs,
    h.uniqueMDiffOn_image_aux hn⟩
#align diffeomorph.unique_mdiff_on_image Diffeomorph.uniqueMDiffOn_image

@[simp]
theorem uniqueMDiffOn_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) {s : Set N} :
    UniqueMDiffOn I (h ⁻¹' s) ↔ UniqueMDiffOn J s :=
  h.symm_image_eq_preimage s ▸ h.symm.uniqueMDiffOn_image hn
#align diffeomorph.unique_mdiff_on_preimage Diffeomorph.uniqueMDiffOn_preimage

@[simp]
theorem uniqueDiffOn_image (h : E ≃ₘ^n[𝕜] F) (hn : 1 ≤ n) {s : Set E} :
    UniqueDiffOn 𝕜 (h '' s) ↔ UniqueDiffOn 𝕜 s := by
  simp only [← uniqueMDiffOn_iff_uniqueDiffOn, unique_mdiff_on_image, hn]
#align diffeomorph.unique_diff_on_image Diffeomorph.uniqueDiffOn_image

@[simp]
theorem uniqueDiffOn_preimage (h : E ≃ₘ^n[𝕜] F) (hn : 1 ≤ n) {s : Set F} :
    UniqueDiffOn 𝕜 (h ⁻¹' s) ↔ UniqueDiffOn 𝕜 s :=
  h.symm_image_eq_preimage s ▸ h.symm.uniqueDiffOn_image hn
#align diffeomorph.unique_diff_on_preimage Diffeomorph.uniqueDiffOn_preimage

end Diffeomorph

namespace ContinuousLinearEquiv

variable (e : E ≃L[𝕜] E')

/-- A continuous linear equivalence between normed spaces is a diffeomorphism. -/
def toDiffeomorph : E ≃ₘ[𝕜] E'
    where
  contMDiff_to_fun := e.ContDiff.ContMDiff
  contMDiff_inv_fun := e.symm.ContDiff.ContMDiff
  toEquiv := e.toLinearEquiv.toEquiv
#align continuous_linear_equiv.to_diffeomorph ContinuousLinearEquiv.toDiffeomorph

@[simp]
theorem coe_toDiffeomorph : ⇑e.toDiffeomorph = e :=
  rfl
#align continuous_linear_equiv.coe_to_diffeomorph ContinuousLinearEquiv.coe_toDiffeomorph

@[simp]
theorem symm_toDiffeomorph : e.symm.toDiffeomorph = e.toDiffeomorph.symm :=
  rfl
#align continuous_linear_equiv.symm_to_diffeomorph ContinuousLinearEquiv.symm_toDiffeomorph

@[simp]
theorem coe_toDiffeomorph_symm : ⇑e.toDiffeomorph.symm = e.symm :=
  rfl
#align continuous_linear_equiv.coe_to_diffeomorph_symm ContinuousLinearEquiv.coe_toDiffeomorph_symm

end ContinuousLinearEquiv

namespace ModelWithCorners

variable (I) (e : E ≃ₘ[𝕜] E')

/-- Apply a diffeomorphism (e.g., a continuous linear equivalence) to the model vector space. -/
def transDiffeomorph (I : ModelWithCorners 𝕜 E H) (e : E ≃ₘ[𝕜] E') : ModelWithCorners 𝕜 E' H
    where
  toLocalEquiv := I.toLocalEquiv.trans e.toEquiv.toLocalEquiv
  source_eq := by simp
  unique_diff' := by simp [range_comp e, I.unique_diff]
  continuous_toFun := e.Continuous.comp I.Continuous
  continuous_invFun := I.continuous_symm.comp e.symm.Continuous
#align model_with_corners.trans_diffeomorph ModelWithCorners.transDiffeomorph

@[simp, mfld_simps]
theorem coe_transDiffeomorph : ⇑(I.transDiffeomorph e) = e ∘ I :=
  rfl
#align model_with_corners.coe_trans_diffeomorph ModelWithCorners.coe_transDiffeomorph

@[simp, mfld_simps]
theorem coe_transDiffeomorph_symm : ⇑(I.transDiffeomorph e).symm = I.symm ∘ e.symm :=
  rfl
#align model_with_corners.coe_trans_diffeomorph_symm ModelWithCorners.coe_transDiffeomorph_symm

theorem transDiffeomorph_range : range (I.transDiffeomorph e) = e '' range I :=
  range_comp e I
#align model_with_corners.trans_diffeomorph_range ModelWithCorners.transDiffeomorph_range

theorem coe_extChartAt_transDiffeomorph (x : M) :
    ⇑(extChartAt (I.transDiffeomorph e) x) = e ∘ extChartAt I x :=
  rfl
#align model_with_corners.coe_ext_chart_at_trans_diffeomorph ModelWithCorners.coe_extChartAt_transDiffeomorph

theorem coe_extChartAt_transDiffeomorph_symm (x : M) :
    ⇑(extChartAt (I.transDiffeomorph e) x).symm = (extChartAt I x).symm ∘ e.symm :=
  rfl
#align model_with_corners.coe_ext_chart_at_trans_diffeomorph_symm ModelWithCorners.coe_extChartAt_transDiffeomorph_symm

theorem extChartAt_transDiffeomorph_target (x : M) :
    (extChartAt (I.transDiffeomorph e) x).target = e.symm ⁻¹' (extChartAt I x).target := by
  simp only [range_comp e, e.image_eq_preimage, preimage_preimage, mfld_simps]
#align model_with_corners.ext_chart_at_trans_diffeomorph_target ModelWithCorners.extChartAt_transDiffeomorph_target

end ModelWithCorners

namespace Diffeomorph

variable (e : E ≃ₘ[𝕜] F)

instance smoothManifoldWithCorners_transDiffeomorph [SmoothManifoldWithCorners I M] :
    SmoothManifoldWithCorners (I.transDiffeomorph e) M :=
  by
  refine' smoothManifoldWithCorners_of_contDiffOn _ _ fun e₁ e₂ h₁ h₂ => _
  refine'
    e.cont_diff.comp_cont_diff_on
      (((contDiffGroupoid ⊤ I).compatible h₁ h₂).1.comp e.symm.cont_diff.cont_diff_on _)
  mfld_set_tac
#align diffeomorph.smooth_manifold_with_corners_trans_diffeomorph Diffeomorph.smoothManifoldWithCorners_transDiffeomorph

variable (I M)

/-- The identity diffeomorphism between a manifold with model `I` and the same manifold
with model `I.trans_diffeomorph e`. -/
def toTransDiffeomorph (e : E ≃ₘ[𝕜] F) : M ≃ₘ⟮I, I.transDiffeomorph e⟯ M
    where
  toEquiv := Equiv.refl M
  contMDiff_to_fun x :=
    by
    refine' contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, _⟩
    refine' e.cont_diff.cont_diff_within_at.congr' (fun y hy => _) _
    ·
      simp only [Equiv.coe_refl, id, (· ∘ ·), I.coe_ext_chart_at_trans_diffeomorph,
        (extChartAt I x).right_inv hy.1]
    exact
      ⟨(extChartAt I x).map_source (mem_extChartAt_source I x), trivial, by simp only [mfld_simps]⟩
  contMDiff_inv_fun x :=
    by
    refine' contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, _⟩
    refine' e.symm.cont_diff.cont_diff_within_at.congr' (fun y hy => _) _
    · simp only [mem_inter_iff, I.ext_chart_at_trans_diffeomorph_target] at hy 
      simp only [Equiv.coe_refl, Equiv.refl_symm, id, (· ∘ ·),
        I.coe_ext_chart_at_trans_diffeomorph_symm, (extChartAt I x).right_inv hy.1]
    exact
      ⟨(extChartAt _ x).map_source (mem_extChartAt_source _ x), trivial, by
        simp only [e.symm_apply_apply, Equiv.refl_symm, Equiv.coe_refl, mfld_simps]⟩
#align diffeomorph.to_trans_diffeomorph Diffeomorph.toTransDiffeomorph

variable {I M}

@[simp]
theorem contMDiffWithinAt_transDiffeomorph_right {f : M' → M} {x s} :
    ContMDiffWithinAt I' (I.transDiffeomorph e) n f s x ↔ ContMDiffWithinAt I' I n f s x :=
  (toTransDiffeomorph I M e).contMDiffWithinAt_diffeomorph_comp_iff le_top
#align diffeomorph.cont_mdiff_within_at_trans_diffeomorph_right Diffeomorph.contMDiffWithinAt_transDiffeomorph_right

@[simp]
theorem contMDiffAt_transDiffeomorph_right {f : M' → M} {x} :
    ContMDiffAt I' (I.transDiffeomorph e) n f x ↔ ContMDiffAt I' I n f x :=
  (toTransDiffeomorph I M e).contMDiffAt_diffeomorph_comp_iff le_top
#align diffeomorph.cont_mdiff_at_trans_diffeomorph_right Diffeomorph.contMDiffAt_transDiffeomorph_right

@[simp]
theorem contMDiffOn_transDiffeomorph_right {f : M' → M} {s} :
    ContMDiffOn I' (I.transDiffeomorph e) n f s ↔ ContMDiffOn I' I n f s :=
  (toTransDiffeomorph I M e).contMDiffOn_diffeomorph_comp_iff le_top
#align diffeomorph.cont_mdiff_on_trans_diffeomorph_right Diffeomorph.contMDiffOn_transDiffeomorph_right

@[simp]
theorem contMDiff_transDiffeomorph_right {f : M' → M} :
    ContMDiff I' (I.transDiffeomorph e) n f ↔ ContMDiff I' I n f :=
  (toTransDiffeomorph I M e).contMDiff_diffeomorph_comp_iff le_top
#align diffeomorph.cont_mdiff_trans_diffeomorph_right Diffeomorph.contMDiff_transDiffeomorph_right

@[simp]
theorem smooth_transDiffeomorph_right {f : M' → M} :
    Smooth I' (I.transDiffeomorph e) f ↔ Smooth I' I f :=
  contMDiff_transDiffeomorph_right e
#align diffeomorph.smooth_trans_diffeomorph_right Diffeomorph.smooth_transDiffeomorph_right

@[simp]
theorem contMDiffWithinAt_transDiffeomorph_left {f : M → M'} {x s} :
    ContMDiffWithinAt (I.transDiffeomorph e) I' n f s x ↔ ContMDiffWithinAt I I' n f s x :=
  ((toTransDiffeomorph I M e).contMDiffWithinAt_comp_diffeomorph_iff le_top).symm
#align diffeomorph.cont_mdiff_within_at_trans_diffeomorph_left Diffeomorph.contMDiffWithinAt_transDiffeomorph_left

@[simp]
theorem contMDiffAt_transDiffeomorph_left {f : M → M'} {x} :
    ContMDiffAt (I.transDiffeomorph e) I' n f x ↔ ContMDiffAt I I' n f x :=
  ((toTransDiffeomorph I M e).contMDiffAt_comp_diffeomorph_iff le_top).symm
#align diffeomorph.cont_mdiff_at_trans_diffeomorph_left Diffeomorph.contMDiffAt_transDiffeomorph_left

@[simp]
theorem contMDiffOn_transDiffeomorph_left {f : M → M'} {s} :
    ContMDiffOn (I.transDiffeomorph e) I' n f s ↔ ContMDiffOn I I' n f s :=
  ((toTransDiffeomorph I M e).contMDiffOn_comp_diffeomorph_iff le_top).symm
#align diffeomorph.cont_mdiff_on_trans_diffeomorph_left Diffeomorph.contMDiffOn_transDiffeomorph_left

@[simp]
theorem contMDiff_transDiffeomorph_left {f : M → M'} :
    ContMDiff (I.transDiffeomorph e) I' n f ↔ ContMDiff I I' n f :=
  ((toTransDiffeomorph I M e).contMDiff_comp_diffeomorph_iff le_top).symm
#align diffeomorph.cont_mdiff_trans_diffeomorph_left Diffeomorph.contMDiff_transDiffeomorph_left

@[simp]
theorem smooth_transDiffeomorph_left {f : M → M'} :
    Smooth (I.transDiffeomorph e) I' f ↔ Smooth I I' f :=
  e.contMDiff_transDiffeomorph_left
#align diffeomorph.smooth_trans_diffeomorph_left Diffeomorph.smooth_transDiffeomorph_left

end Diffeomorph

