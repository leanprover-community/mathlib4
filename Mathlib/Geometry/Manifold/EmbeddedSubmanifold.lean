/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.IsImmersionEmbedding
import Mathlib.Geometry.Manifold.Instances.Real -- XXX: disentangle these later
/-!
# Embedded submanifolds

TODO: write doc-string when things are clearer

-/

open scoped Manifold ContDiff
open Topology Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' E''' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E''']
    [NormedSpace 𝕜 E''']
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H H' H'' H''' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace H''] [TopologicalSpace H''']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {I'' : ModelWithCorners 𝕜 E'' H''}
  {J : ModelWithCorners 𝕜 E''' H'''}
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

namespace SliceModel

/-- A choice of inverse of `map`: its value outside of `range map` is unspecified. -/
noncomputable def inverse [Nonempty H] (h : SliceModel F I I') : H' → H :=
  (Function.extend h.map id (fun _ ↦ (Classical.arbitrary H)))

-- warm-up: I' ∘ map ⊆ im equiv ∘ I: that's basically obvious, nothing to prove

lemma inverse_left_inv [Nonempty H] (h : SliceModel F I I') (x : H) :
    h.inverse (h.map x) = x :=
  Injective.extend_apply h.hmap.injective ..

lemma inverse_right_inv [Nonempty H] (h : SliceModel F I I') (z : H') (hz : z ∈ range h.map) :
    h.map (h.inverse z) = z := by
  choose x hx using hz
  rw [← hx, h.inverse_left_inv]

end SliceModel

section

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Unique G]

namespace LinearEquiv

variable (𝕜 E) in
/-- The natural equivalence `E × G ≃ₗ[𝕜] E` for any `Unique` type `G`.
This is `Equiv.prodUnique` as a linear equivalence. -/
def prodUnique : (E × G) ≃ₗ[𝕜] E where
  toEquiv := Equiv.prodUnique E G
  map_add' x y := by simp
  map_smul' r x := by simp

@[simp]
lemma prodUnique_toEquiv : (prodUnique 𝕜 E).toEquiv = Equiv.prodUnique E G := rfl

end LinearEquiv

namespace ContinuousLinearEquiv

variable (𝕜 E) in
/-- The natural equivalence `E × G ≃L[𝕜] E` for any `Unique` type `G`.
This is `Equiv.prodUnique` as a continuous linear equivalence. -/
def prodUnique : (E × G) ≃L[𝕜] E where
  toLinearEquiv := LinearEquiv.prodUnique 𝕜 E
  continuous_toFun := by
    show Continuous (Equiv.prodUnique E G)
    dsimp; fun_prop
  continuous_invFun := by
    show Continuous fun x ↦ (x, default)
    fun_prop

@[simp]
lemma prodUnique_toEquiv : (prodUnique 𝕜 E).toEquiv = Equiv.prodUnique E G := rfl

@[simp]
lemma prodUnique_apply (x : E × G) : prodUnique 𝕜 E x = x.1 := rfl

@[simp]
lemma prodUnique_symm_apply (x : E) : (prodUnique 𝕜 E (G := G)).symm x = (x, default) := rfl

/- do I want all/any of these lemma?
@[simp]
lemma prodSingle_coe {y : G} :
    (prodSingleton 𝕜 E (y := y)) = ((·, y) : E → E × G) := rfl
-/

section

variable (R M₁ M₂ M₃ : Type*) [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]

/-- The product of topological modules is associative up to continuous linear isomorphism.
This is `LinearEquiv.prodAssoc` prodAssoc as a continuous linear equivalence. -/
def prodAssoc : ((M₁ × M₂) × M₃) ≃L[R] M₁ × M₂ × M₃ where
  toLinearEquiv := LinearEquiv.prodAssoc R M₁ M₂ M₃
  continuous_toFun := (continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)

@[simp]
lemma prodAssoc_toLinearEquiv :
  (prodAssoc 𝕜 E E' E'').toLinearEquiv = LinearEquiv.prodAssoc 𝕜 E E' E'' := rfl

-- not simp as the combination of existing lemmas. TODO: should this one still be added?
lemma prodAssoc_toEquiv :
  (prodAssoc 𝕜 E E' E'').toEquiv = Equiv.prodAssoc E E' E'' := rfl

end

end ContinuousLinearEquiv

end

section instances

/-- Every model with corners is a slice model over itself. -/
instance : SliceModel (⊥ : Subspace 𝕜 E) I I where
  equiv := ContinuousLinearEquiv.prodUnique 𝕜 E
  map := id
  hmap := Topology.IsEmbedding.id
  compatible := by ext x; dsimp

-- apparently all missing: LinearEquiv.prodCongr, ContinuousLinearEquiv.prodCongr

instance [h : SliceModel F I I'] : SliceModel F (J.prod I) (J.prod I') where
  equiv := by
    let sdf := h.equiv
    -- want h.equiv.prodCongr (.id), and probably re-associating...
    sorry
  map := Prod.map id h.map
  hmap := IsEmbedding.id.prodMap h.hmap
  compatible := sorry

-- a bit more cumbersome, as equiv needs some reordering
instance [h : SliceModel F I I'] : SliceModel F (I.prod J) (I'.prod J) where
  equiv := sorry
  map := Prod.map h.map id
  hmap := h.hmap.prodMap IsEmbedding.id
  compatible := sorry

instance (h : (E × F) ≃L[𝕜] E') : SliceModel F (𝓘(𝕜, E)) (𝓘(𝕜, E')) where
  equiv := h
  map := h ∘ (·, (0 : F))
  hmap := by
    apply IsEmbedding.comp
    · sorry -- apply ContinuousLinearEquiv.isEmbedding
    have : IsEmbedding (@Prod.swap E F) := sorry -- missing, it seems
    rw [← IsEmbedding.of_comp_iff this]
    have : ((·, (0 : F)) : E → E × F) = Prod.swap ∘ Prod.mk 0 := by
      ext x
      simp_all; sorry
    convert isEmbedding_prodMk (0 : F)
  compatible := by simp

/-- *Any* model with corners on `E` which is an embedding is a slice model with the trivial model
on `E`. (The embedding condition excludes strange cases of submanifolds with boundary).
For boundaryless models, that is always true. -/
instance {I : ModelWithCorners 𝕜 E H} (hI : IsEmbedding I) :
    SliceModel (⊥ : Subspace 𝕜 E) I 𝓘(𝕜, E) where
  equiv := ContinuousLinearEquiv.prodUnique 𝕜 E
  map := I
  hmap := hI
  compatible := by ext; simp

-- TODO: prove that I is an embedding if I is boundaryless, then add the corresponding instance
-- TODO: think about the boundary case, and which particular version of submanifolds this enforces...

open scoped Manifold

-- XXX: can this be golfed using the previous instance?
noncomputable instance {n : ℕ} [NeZero n] :
    SliceModel (⊥ : Subspace ℝ ((Fin n → ℝ))) (𝓡∂ n) (𝓡 n) where
  equiv := ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin n))
  map := Subtype.val
  hmap := Topology.IsEmbedding.subtypeVal
  compatible := by
    ext x'
    simp only [modelWithCornersSelf_coe, comp_apply, id_eq, ContinuousLinearEquiv.prodUnique_apply]
    rfl

-- should be a not-too-hard exercise
noncomputable instance {n m : ℕ} [NeZero n] :
    SliceModel (⊥ : Subspace ℝ ((Fin m → ℝ))) (𝓡 n) (𝓡 (n + m)) where
  equiv := sorry -- see zulip! ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin n))
  map := sorry -- easy from `equiv`
  hmap := sorry -- should be easy: `equiv` is an embedding, and prodMk{Left,Right} also are
  compatible := by -- should be obvious then
    ext x'
    sorry

noncomputable instance {n : ℕ} [NeZero n] :
    SliceModel (⊥ : Subspace ℝ ((Fin n → ℝ))) (modelWithCornersEuclideanQuadrant n) (𝓡∂ n) where
  equiv := ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin n))
  map := fun ⟨x, hx⟩ ↦ ⟨x, hx 0⟩
  hmap :=
    -- general result: two subtypes, one contained in the other: is Subtype.val always an
    -- embedding? can one prove this?
    sorry
  compatible := by
    ext x
    simp_all only [comp_apply, ContinuousLinearEquiv.prodUnique_apply]
    rfl

-- TODO: make an instance/ figure out why Lean complains about synthesisation order!
def instTrans (h : SliceModel F I I') (h' : SliceModel F' I' I'') : SliceModel (F × F') I I'' where
  equiv := (ContinuousLinearEquiv.prodAssoc 𝕜 E F F').symm.trans
    ((h.equiv.prod (ContinuousLinearEquiv.refl 𝕜 F')).trans h'.equiv)
  map := h'.map ∘ h.map
  hmap := h'.hmap.comp h.hmap
  compatible := by -- paste the two commutative diagrams together
    ext x
    simp [h.compatible, h'.compatible]
    sorry

end instances

namespace PartialHomeomorph

variable [TopologicalSpace M] [IsManifold I' n M']

variable [Nonempty H] {φ : PartialHomeomorph M' H'} {f : M → M'}
omit [ChartedSpace H' M']

-- continuity of `toFun`
lemma continuousOn_source (h : SliceModel F I I') (hf : Continuous f) :
    ContinuousOn (h.inverse ∘ φ ∘ f) (f ⁻¹' (φ.source ∩ (φ ⁻¹' range h.map))) := by
  rw [h.hmap.continuousOn_iff]
  have : ContinuousOn (↑φ ∘ f) (f ⁻¹' φ.source) :=
    φ.continuousOn_toFun.comp hf.continuousOn (fun ⦃x⦄ a ↦ a)
  have : ContinuousOn (φ ∘ f) (f ⁻¹' (φ.source ∩ (φ ⁻¹' range h.map))) := by
    apply this.mono
    gcongr
    exact inter_subset_left
  apply this.congr
  intro x hx
  apply h.inverse_right_inv
  apply hx.2

-- auxiliary definition; will become the invFun of pullback_sliceModel
variable (f φ) in
noncomputable def aux_invFun [Nonempty M] (h : SliceModel F I I') : H → M :=
  (Function.extend f id (fun _ ↦ (Classical.arbitrary M))) ∘ φ.symm ∘ h.map

-- continuity of the inverse function
lemma continuousOn_aux_invFun [Nonempty M] (h : SliceModel F I I') (hf : IsEmbedding f)
    (hyp : φ.source ⊆ range f) :
    ContinuousOn (aux_invFun φ f h) (h.map ⁻¹' φ.target) := by
  have : ContinuousOn ((Function.extend f id fun x ↦ Classical.arbitrary M) ∘ φ.symm) φ.target := by
    refine ContinuousOn.comp ?_ φ.continuousOn_symm φ.symm_mapsTo
    -- This holds for any embedding, but seems to be missing.
    have missing : ContinuousOn (Function.extend f id fun x ↦ Classical.arbitrary M) (range f) := by
      -- does this help? refine IsOpenMap.continuousOn_range_of_leftInverse ?_ ?_
      sorry
    exact missing.mono hyp
  exact this.comp h.hmap.continuous.continuousOn (fun ⦃x⦄ a ↦ a)

omit [TopologicalSpace M] in
lemma aux' (h : SliceModel F I I') {y : H'} (hy : y ∈ range (φ ∘ f)) (hy' : y ∈ range h.map) :
    h.map (h.inverse y) = y := by
  choose x hx using hy
  choose x' hx' using hy'
  rw [← hx', h.inverse_left_inv x']

omit [TopologicalSpace M] [Nonempty H] in
theorem missing (h : SliceModel F I I') (hsource : φ.source ⊆ range f)
    {x : H} (hx : h.map x ∈ φ.target) : (φ.symm ∘ h.map) x ∈ range f := by
  rw [← φ.image_source_eq_target] at hx
  choose s hs hsx using hx
  rw [comp_apply, ← hsx, φ.left_inv hs]
  exact hsource hs

variable [Nonempty M]

-- TODO: `hsource` is much too restrictive:
-- if M has smaller dimension that M', then range f is never open, while φ.source is
-- similarly for htarget

variable (φ) in
/-- Pull back a partial homeomorphism using a slice model. -/
-- XXX: does this hold for merely inducing maps? depends on the missing sorry for the inverse
noncomputable def pullback_sliceModel (h : SliceModel F I I') (hf : IsEmbedding f) :
    PartialHomeomorph M H where
  toFun := h.inverse ∘ φ ∘ f
  invFun :=
    letI finv := Function.extend f id (fun _ ↦ (Classical.arbitrary M))
    (finv ∘ φ.symm ∘ h.map)
  source := f ⁻¹' (φ.source ∩ (φ ⁻¹' range h.map))
  open_source := by
    apply IsOpen.preimage hf.continuous --φ.open_source
    apply φ.open_source.inter
    sorry -- IsOpen (φ ⁻¹' range (SliceModel.map F I I'))
  target := h.map ⁻¹' φ.target
  open_target := sorry -- IsOpen.preimage h.hmap.continuous φ.open_target
  map_source' := by
    rintro x ⟨hx₁, hx₂⟩
    rw [← φ.image_source_eq_target, mem_preimage]
    convert mem_image_of_mem φ hx₁
    exact aux' h (mem_range_self x) hx₂
  map_target' x hx := by
    sorry /- rw [mem_preimage] at hx ⊢
    constructor
    · convert map_target φ hx.2
      sorry
    · rw [mem_preimage]
      sorry -/
    -- choose x' hx' using missing h hsource hx
    -- calc
    --   _ = f (Function.extend f id (fun x ↦ Classical.arbitrary M) ((φ.symm ∘ h.map) x)) := rfl
    --   _ = (φ.symm ∘ h.map) x := by
    --     rw [← hx']
    --     congr
    --     apply hf.injective.extend_apply
  left_inv' x hx := calc
      _ = ((Function.extend f id fun x ↦ Classical.arbitrary M) ∘ φ.symm ∘
          (h.map ∘ h.inverse) ∘ φ ∘ f) x := rfl
      _ = ((Function.extend f id fun x ↦ Classical.arbitrary M) ∘ φ.symm ∘ φ ∘ f) x := by
        sorry /- simp_rw [comp_apply]
        congr
        apply aux' h (mem_range_self x) (htarget ?_)
        exact φ.image_source_eq_target ▸ mem_image_of_mem φ hx -/
      _ = (Function.extend f id fun x ↦ Classical.arbitrary M) (f x) := by
        simp only [comp_apply]
        congr
        sorry -- apply φ.left_inv' hx
      _ = x := hf.injective.extend_apply _ _ x
  right_inv' x hx := by
    sorry
    /- choose x' hx' using missing h hsource hx
    have (x') : (Function.extend f id (fun x ↦ Classical.arbitrary M)) (f x') = x' := by
      simp [hf.injective.extend_apply]
    specialize this x'
    calc
      _ = (h.inverse ∘ φ ∘ f) ((Function.extend f id fun x ↦ Classical.arbitrary M)
          ((φ.symm ∘ h.map) x)) := rfl
      _ = (h.inverse ∘ φ) ((φ.symm ∘ h.map) x) := by
        rw [← hx', this]
        simp_rw [comp_apply]
      _ = h.inverse ((φ ∘ φ.symm) (h.map x)) := by simp [Function.comp_apply]
      _ = h.inverse (h.map x) := by congr; exact φ.right_inv' hx
      _ = x := h.inverse_left_inv x -/
  continuousOn_toFun := continuousOn_source h hf.continuous
  continuousOn_invFun := sorry -- continuousOn_aux_invFun h hf hsource

#exit

@[simp, mfld_simps]
lemma pullback_sliceModel_coe (h : SliceModel F I I') (hf : IsEmbedding f)
    (hsource : φ.source ⊆ range f) (htarget : φ.target ⊆ range h.map) :
      φ.pullback_sliceModel h hf hsource htarget = h.inverse ∘ φ ∘ f := by
  rfl

@[simp, mfld_simps]
lemma pullback_sliceModel_source (h : SliceModel F I I') (hf : IsEmbedding f)
    (hsource : φ.source ⊆ range f) (htarget : φ.target ⊆ range h.map) :
      (φ.pullback_sliceModel h hf hsource htarget).source = f ⁻¹' φ.source := by
  rfl

@[simp, mfld_simps]
lemma pullback_sliceModel_target (h : SliceModel F I I') (hf : IsEmbedding f)
    (hsource : φ.source ⊆ range f) (htarget : φ.target ⊆ range h.map) :
      (φ.pullback_sliceModel h hf hsource htarget).target = h.map ⁻¹' φ.target := by
  rfl

@[simp, mfld_simps]
lemma pullback_sliceModel_symm_coe (h : SliceModel F I I') (hf : IsEmbedding f)
    (hsource : φ.source ⊆ range f) (htarget : φ.target ⊆ range h.map) :
    (φ.pullback_sliceModel h hf hsource htarget).symm =
      (Function.extend f id (fun _ ↦ (Classical.arbitrary M))) ∘ φ.symm ∘ h.map := by
  rfl

lemma pullback_sliceModel_trans_eqOn_source (h : SliceModel F I I')
    (hf : IsEmbedding f) {ψ : PartialHomeomorph M' H'}
    (hsource : φ.source ⊆ range f) (htarget : φ.target ⊆ range h.map)
    (hsource' : ψ.source ⊆ range f) (htarget' : ψ.target ⊆ range h.map) :
    EqOn ((φ.pullback_sliceModel h hf hsource htarget).symm.trans
        (ψ.pullback_sliceModel h hf hsource' htarget'))
      (h.inverse ∘ ψ ∘ φ.symm ∘ h.map) (φ.pullback_sliceModel h hf hsource htarget).target := by
  dsimp only [coe_trans, pullback_sliceModel_coe, pullback_sliceModel_symm_coe]
  intro x hx
  calc
    _ = ((h.inverse ∘ ψ) ∘ (f ∘ (Function.extend f id (fun x'' ↦ Classical.arbitrary M))))
        ((φ.symm ∘ h.map) x) := rfl
    _ = (h.inverse ∘ ψ) (φ.symm (SliceModel.map F I I' x)) := by
      choose x' hx' using missing h hsource hx
      simp only [← hx', comp_apply, hf.injective.extend_apply]
      congr

end PartialHomeomorph

variable (F M M' n) in
class IsImmersedSubmanifold [TopologicalSpace M] [IsManifold I' n M'] (h: SliceModel F I I') where
  emb: M → M'
  hemb: IsEmbedding emb
  hcharts_source : ∀ ⦃y⦄, y ∈ range emb → (chartAt H' y).source ⊆ range emb
  hcharts_target : ∀ ⦃y⦄, (hy : y ∈ range emb) →
    (chartAt H' y).target ⊆ range (SliceModel.map F I I')

namespace IsImmersedSubmanifold

variable [TopologicalSpace M] [IsManifold I' n M'] [h: SliceModel F I I'] [Nonempty H] [Nonempty M]

noncomputable def myChart (inst : IsImmersedSubmanifold F M M' n h) (x : M) :
    PartialHomeomorph M H :=
  (chartAt H' (inst.emb x)).pullback_sliceModel h inst.hemb (hcharts_source (mem_range_self x))
    (hcharts_target (mem_range_self x))

-- XXX: making this an instance makes Lean complain about synthesization order
noncomputable def chartedSpace (inst : IsImmersedSubmanifold F M M' n h) :
    ChartedSpace H M where
  atlas := { inst.myChart x | x : M }
  chartAt x := inst.myChart x
  mem_chart_source x := by simp [myChart]
  chart_mem_atlas x := by rw [mem_setOf]; use x

-- cannot state this yet because of the synthesisation order issue
-- TODO fix, and make an instance
/- noncomputable def isManifold (inst : IsImmersedSubmanifold F I I' M M' n h) :
    haveI : ChartedSpace H M := inst.chartedSpace; IsManifold I n M where
  compatible := sorry -/

-- XXX: turn this proof into the isManifold instance, once the above is solved
lemma compatible (inst : IsImmersedSubmanifold F M M' n h)
    -- {e e' : PartialHomeomorph M H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) :
    -- e.symm ≫ₕ e' ∈ (contDiffGroupoid n I)
    {x x' : M} : (inst.myChart x).symm ≫ₕ (inst.myChart x') ∈ (contDiffGroupoid n I) := by
  rw [contDiffGroupoid, contDiffPregroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · dsimp
    simp [myChart]
    show ContDiffOn 𝕜 n
      (I ∘ ((h.inverse ∘ (chartAt H' (emb n h x')) ∘ emb n h) ∘
        (extend (emb n h) id fun x ↦ Classical.arbitrary M) ∘ (chartAt H' (emb n h x)).symm ∘ h.map) ∘
      ↑I.symm)
      (↑I.symm ⁻¹' (h.map ⁻¹' (chartAt H' (emb n h x)).target) ∩
      ↑I.symm ⁻¹'
        ((extend (emb n h) id fun x ↦ Classical.arbitrary M) ∘
            ↑(chartAt H' (emb n h x)).symm ∘ h.map ⁻¹' (emb n h ⁻¹' (chartAt H' (emb n h x')).source)) ∩ range ↑I)
    -- this can help, but not sufficient yet
    -- rw [pullback_sliceModel_trans_eqOn_source]
    sorry
  set X := emb (M' := M') n h x
  set X' := emb (M' := M') n h x'
  sorry

/- lemma isImmersion_emb (inst : IsImmersedSubmanifold F I I' M M' n h) :
    IsImmersion F I I' n inst.emb := sorry -/

-- TODO: define embedded submanifolds, deduce that `emb` is an embedding

-- TODO: conversely, if f: M → M' is an immersion (embedding), we can define the image model
-- I₀ on M', prove that this is a slice model and deduce IsImmersedSubmanifold via f
-- (same for embedded)

end IsImmersedSubmanifold
