/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.IsImmersionEmbedding

/-!
# Embedded submanifolds

TODO: write doc-string when things are clearer

-/

open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H'] {H'' : Type*} [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' H''}
  {M M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] {n : WithTop ℕ∞}

variable (I I' F) in
/-- Two models with corners `I` and `I'` form a **slice model** if "I includes into I'".
More precisely, there are an embedding `H → H'` and a continuous linear map `E → E'` so the diagram
  H  -I  → E'
  |        |
  |        |
  H' -I' → E'
commutes. More precisely, we prescribe a linear equivalence `E × F → E`, for some normed space `F`,
which induces the map `E → E'` in the obvious way.
-/
class SliceModel where
  equiv: (E × F) ≃L[𝕜] E'
  map: H → H'
  hmap : Topology.IsEmbedding map
  compatible : I' ∘ map = equiv ∘ ((·, 0) : E → E × F) ∘ I

/-- A choice of inverse of `map`: its value outside of `range map` is unspecified. -/
noncomputable def SliceModel.inverse [Nonempty H] [h : SliceModel F I I']: H' → H :=
  (Function.extend h.map id (fun _ ↦ (Classical.arbitrary H)))

-- warm-up: I' ∘ map ⊆ im equiv ∘ I: that's basically obvious, nothing to prove

lemma SliceModel.inverse_left_inv [Nonempty H] [h : SliceModel F I I'] (x : H) :
    h.inverse (h.map x) = x :=
  Injective.extend_apply h.hmap.injective ..

section

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Unique G]

variable (𝕜 E) in
def LinearEquiv.prodUnique : (E × G) ≃ₗ[𝕜] E where
  toEquiv := Equiv.prodUnique E G
  map_add' := sorry
  map_smul' := sorry

@[simp]
lemma LinearEquiv.prodUnique_toEquiv : (LinearEquiv.prodUnique 𝕜 E).toEquiv = Equiv.prodUnique E G := rfl

variable (𝕜 E) in
def ContinuousLinearEquiv.prodUnique : (E × G) ≃L[𝕜] E where
  toLinearEquiv := LinearEquiv.prodUnique 𝕜 E
  continuous_toFun := by
    show Continuous (Equiv.prodUnique E G)
    dsimp; fun_prop
  continuous_invFun := by
    dsimp
    show Continuous (Equiv.prodUnique E G).symm
    sorry -- dsimp; continuity--fun_prop

@[simp]
lemma ContinuousLinearEquiv.prodUnique_toEquiv :
    (ContinuousLinearEquiv.prodUnique 𝕜 E).toEquiv = Equiv.prodUnique E G := rfl

@[simp]
lemma ContinuousLinearEquiv.prodUnique_apply (x : E × G) :
    (ContinuousLinearEquiv.prodUnique 𝕜 E) x = x.1 := rfl

@[simp]
lemma ContinuousLinearEquiv.prodUnique_symm_apply (x : E) :
    (ContinuousLinearEquiv.prodUnique 𝕜 E (G := G)).symm x = (x, (sorry : G)) := sorry -- rfl

/- do I want all/any of these lemma?
@[simp]
lemma LinearEquiv.prodSingle_coe {y : G} :
    (LinearEquiv.prodSingleton 𝕜 E (y := y)) = ((·, y) : E → E × G) := rfl
-/

/-- Every model with corners is a slice model over itself. -/
instance : SliceModel (⊥ : Subspace 𝕜 E) I I where
  equiv := ContinuousLinearEquiv.prodUnique 𝕜 E
  map := id
  hmap := Topology.IsEmbedding.id
  compatible := by ext x; dsimp

-- apparently all missing: LinearEquiv.prodCongr, ContinuousLinearEquiv.prodCongr

open Topology

instance [h : SliceModel F I I'] : SliceModel F (J.prod I) (J.prod I') where
  equiv := by
    let sdf := h.equiv
    -- want h.equiv.prodCongr (.id), and probably re-associating...
    sorry
  map := Prod.map id h.map
  hmap := IsEmbedding.id.prodMap h.hmap
  compatible := sorry

-- a bit more cumbersom, as equiv needs some reordering
instance [h : SliceModel F I I'] : SliceModel F (I.prod J) (I'.prod J) where
  equiv := sorry
  map := Prod.map h.map id
  hmap := h.hmap.prodMap IsEmbedding.id
  compatible := sorry

end

namespace PartialHomeomorph

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

noncomputable def _root_.PartialEquiv.pullback (φ : PartialEquiv Y Z) {f : X → Y} (hf : Injective f) [Nonempty X] :
    PartialEquiv X Z where
  toFun := φ ∘ f
  invFun := (Function.extend f id (fun _ ↦ (Classical.arbitrary X))) ∘ φ.invFun
  left_inv' x hx := by
    have : φ.symm (φ (f x)) = f x := φ.left_inv' hx
    simp only [PartialEquiv.invFun_as_coe, comp_apply, this]
    exact hf.extend_apply _ _ _
  right_inv' x hx := by
    simp only [comp_apply]
    set y := φ.invFun x with hy
    have : y ∈ φ.source := φ.map_target' hx
    -- trouble: this is true if y ∈ im f, and maybe VERY false otherwise!!
    have : f (Function.extend f id (fun x ↦ Classical.arbitrary X) y) = y := by
      unfold Function.extend
      by_cases h : ∃ a, f a = y
      · obtain ⟨a, ha⟩ := h
        rw [← ha]
        simp
        sorry -- seems true, but lean is stuck somewhere
      · simp [h]
        sorry -- this is clearly false
    rw [this, hy]
    exact φ.right_inv' hx
  -- trouble: I *could* restrict the target (e.g. by intersecting with im f), but then the target
  -- would generally not be open any more! for pulling back, I really need a better way.
  source := f ⁻¹' φ.source
  target := φ.target
  map_source' := fun x hx ↦ φ.map_source hx
  map_target' x hx := by
    rw [mem_preimage]
    simp only [comp_apply]
    set y := φ.invFun x with hy
    convert φ.map_target' hx
    rw [← hy]
    -- now, we're just at the interesting part of right_inv'
    sorry

/-- Pulling back a partial homeomorphism by an injective continuous map.
XXX: what's the inverse map? not sure! -/
noncomputable  def pullback (φ : PartialHomeomorph Y Z) {f : X → Y}
    (hf : Injective f) (hf' : Continuous f) [Nonempty X] : PartialHomeomorph X Z where
  toPartialEquiv := φ.toPartialEquiv.pullback hf
  continuousOn_toFun := φ.continuousOn_toFun.comp hf'.continuousOn (fun ⦃x⦄ a ↦ a)
  continuousOn_invFun := by
    let finv := Function.extend f id (fun _ ↦ (Classical.arbitrary X))
    sorry
  open_source := IsOpen.preimage hf' φ.open_source
  open_target := φ.open_target

variable [TopologicalSpace M] [IsManifold I' n M']

open Topology

section

variable [Nonempty M] [Nonempty H] (φ : PartialHomeomorph M' H') {f : M → M'}

-- auxiliary definition; will become the invFun of pullback_sliceModel
variable (f) in
noncomputable def aux_invFun (h : SliceModel F I I') : H → M :=
  (Function.extend f id (fun _ ↦ (Classical.arbitrary M))) ∘ φ.symm ∘ h.map

omit [Nonempty M] [ChartedSpace H' M'] [TopologicalSpace M] in
lemma aux (h : SliceModel F I I') (hyp : range (φ ∘ f) = range h.map)
    {y : H'} (hy : y ∈ range (φ ∘ f)) : h.map (h.inverse y) = y := by
  have : y ∈ range h.map := by
    simp_rw [← hyp]; exact hy
  choose x hx using hy
  choose x' hx' using this
  rw [← hx', SliceModel.inverse_left_inv x']

/-- Pull back a partial homeomorphism using a slice model.
The slice model conditions should guarantee the necessary condition for continuity and inverses. -/
noncomputable def pullback_sliceModel [Nonempty M] [Nonempty H] (φ : PartialHomeomorph M' H')
    {f : M → M'} (hf : IsEmbedding f) (h : SliceModel F I I') (hyp : range (φ ∘ f) = range h.map) :
    PartialHomeomorph M H where
  toFun := h.inverse ∘ φ ∘ f
  invFun :=
    letI finv := Function.extend f id (fun _ ↦ (Classical.arbitrary M))
    (finv ∘ φ.symm ∘ h.map)
  source := f ⁻¹' φ.source
  open_source := IsOpen.preimage hf.continuous φ.open_source
  target := h.map ⁻¹' φ.target
  open_target := IsOpen.preimage h.hmap.continuous φ.open_target
  map_source' x hx := by
    rw [← φ.image_source_eq_target, mem_preimage]
    convert mem_image_of_mem φ hx
    exact aux φ h hyp (mem_range_self x)
  map_target' x hx := by
    rw [mem_preimage] at hx ⊢
    -- f and f.extend cancel
    -- φ.symm '' target ∈ φ.source
    -- use
    sorry
  left_inv' x hx := calc
      _ = ((Function.extend f id fun x ↦ Classical.arbitrary M) ∘ φ.symm ∘
          (SliceModel.map F I I' ∘ SliceModel.inverse) ∘ φ ∘ f) x := rfl
      _ = ((Function.extend f id fun x ↦ Classical.arbitrary M) ∘ φ.symm ∘ φ ∘ f) x := by
        simp_rw [comp_apply]
        congr
        exact aux φ h hyp (mem_range_self x)
      _ = (Function.extend f id fun x ↦ Classical.arbitrary M) (f x) := by
        simp only [comp_apply]
        congr
        apply φ.left_inv' hx
      _ = x := hf.injective.extend_apply _ _ x
  right_inv' x hx := by
    -- key: image (φ.symm ∘ map) ⊆ image f
    have : range (φ.symm ∘ h.map) ⊆ range f := sorry
    have : (φ.symm ∘ SliceModel.map F I I') x ∈ range f := sorry
    choose x' hx' using this
    have (x') : (Function.extend f id (fun x ↦ Classical.arbitrary M)) (f x') = x' := by
      simp [hf.injective.extend_apply]
    specialize this x'
    calc
      _ = (SliceModel.inverse ∘ φ ∘ f) ((Function.extend f id fun x ↦ Classical.arbitrary M) ((φ.symm ∘ SliceModel.map F I I') x)) := rfl
      _ = (SliceModel.inverse (h := h) ∘ φ) ((φ.symm ∘ SliceModel.map F I I') x) := by
        rw [← hx']
        apply congrArg
        apply this
      _ = SliceModel.inverse (h := h) ((φ ∘ φ.symm) (SliceModel.map F I I' x)) := by simp [Function.comp_apply]
      _ = SliceModel.inverse (h := h) (SliceModel.map F I I' x) := by
        apply congrArg
        apply φ.right_inv' hx
      _ = x := SliceModel.inverse_left_inv x

  -- tricky question: why is all that continuous? need to use the slice model!
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry


#exit
-- next: pull back a partial homeo by a slice model
-- the slice condition guarantees the condition below is what I want
-- target should be inverse '' φ.target, and that lies in the image :-)

end PartialHomeomorph

variable (I I' M M' n) in
class IsImmersedSubmanifold [TopologicalSpace M] [IsManifold I' n M'] [SliceModel F I I'] where
  emb: M → M'

namespace IsImmersedSubmanifold

variable [TopologicalSpace M] [IsManifold I' n M']

--instance instChartedSpace [IsImmersedSubmanifold I' M M' n] : ChartedSpace H M := sorry
-- IsManifold I n M
-- IsImmersion ...emb

-- conversely, if f: M → M' is an immersion (embedding), we can define the image model I₀ on M',
-- prove that this is a slice model and deduce IsImmersedSubmanifold via f! (same for embedded)
end IsImmersedSubmanifold

#exit



-- XXX: does NontriviallyNormedField also work? Splits seems to require more...
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}
