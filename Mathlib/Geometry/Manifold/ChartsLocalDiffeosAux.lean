/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# Charts are local diffeomorphisms

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
-- each chart is a structomorphism (from its source to its target).
variable {e : LocalHomeomorph M H} (he : e ∈ atlas H M)

example {f : M → N} (hf : ContMDiff I J n f) (s : Opens M) : True := by
  let f' := (s.1).restrict f
  have : ContMDiff I J n f' := sorry -- type-checks!
  sorry

-- TODO: prove this! it's the main load-bearing part of the lemma below!
lemma obvious (s : Opens M) [Nonempty s] : e.subtypeRestr s ∈ atlas H s := by
  -- can we argue that e = chartAt H x for some x,
  -- hence e.subtypeRestr s is the chart in s at x?
  -- then, would use  simp only [mem_iUnion, mem_singleton_iff]; rfl
  sorry

/-- Charts are structomorphisms. -/
-- xxx: do I need [ClosedUnderRestriction G]? in practice, is not an issue
lemma LocalHomeomorphism.toStructomorph {G : StructureGroupoid H} [ClosedUnderRestriction G]
    (h: HasGroupoid M G) : Structomorph G M H := by
  let s : Opens M := { carrier := e.source, is_open' := e.open_source }
  let t : Opens H := { carrier := e.target, is_open' := e.open_target }

  have : Nonempty s := sorry -- otherwise, trivial
  have : Nonempty t := sorry -- otherwise, trivial
  -- helper lemma: cannot pull out easily, but is conceptually independent
  have helper : ∀ c' : LocalHomeomorph t H, c' ∈ atlas H t →
      e.toHomeomorphSourceTarget.toLocalHomeomorph.trans c' ∈ atlas H s := by
    set e' := e.toHomeomorphSourceTarget.toLocalHomeomorph with eq -- source s, target t
    intro c'
    -- Choose `x ∈ t` so c' is the restriction of `chartAt H x`.
    intro ⟨xset, ⟨x, hx⟩, hc'⟩
    have : xset = {LocalHomeomorph.subtypeRestr (chartAt H ↑x) t} := hx.symm
    have : c' = LocalHomeomorph.subtypeRestr (chartAt H ↑x) t := mem_singleton_iff.mp (this ▸ hc')
    rw [this]
    -- As H has only one chart, this chart is the identity: i.e., c' is the inclusion.
    rw [(chartAt_self_eq)]
    -- simplify: perhaps not needed, but definitely ok
    rw [LocalHomeomorph.subtypeRestr_def, LocalHomeomorph.trans_refl]

    -- now: argue that our expression equals this chart above
    let r := LocalHomeomorph.subtypeRestr e s
    set goal := (e' ≫ₕ Opens.localHomeomorphSubtypeCoe t)
    -- TODO: this should be reasonably obvious... means some missing simp lemma somewhere
    have congr_inv : ∀ y, goal.symm y = r.symm y := by
      intro y
      rw [LocalHomeomorph.coe_trans_symm]
      have aux : ∀ y' : t, e'.symm y' = e.symm ↑y' := by intro; rfl
      let aux := aux (t.localHomeomorphSubtypeCoe.symm y)
      -- also fails: rw [aux]
      calc (e'.symm ∘ t.localHomeomorphSubtypeCoe.symm) y
        _ = e'.symm (t.localHomeomorphSubtypeCoe.symm y) := rfl
        -- doesn't work, for some reason! _ = (e.symm) ↑(t.localHomeomorphSubtypeCoe.symm y) := by rw [aux] -- rfl
        _ = (e.toHomeomorphSourceTarget.toLocalHomeomorph).symm (t.localHomeomorphSubtypeCoe.symm y) := rfl
        _ = (e.toHomeomorphSourceTarget.symm.toLocalHomeomorph) (t.localHomeomorphSubtypeCoe.symm y) := by rw [← Homeomorph.symm_toLocalHomeomorph]
        _ = (e.symm.toHomeomorphSourceTarget.toLocalHomeomorph) (t.localHomeomorphSubtypeCoe.symm y) := rfl

        _ = (e.symm.toHomeomorphSourceTarget.toLocalHomeomorph) (t.localHomeomorphSubtypeCoe.symm y) := sorry--rfl
        --_ = (e'.trans (t.localHomeomorphSubtypeCoe)).symm y := rfl
        --_ = (e.toHomeomorphSourceTarget.toLocalHomeomorph.trans (t.localHomeomorphSubtypeCoe)).symm y := rfl

        _ = (e.symm.trans s.localHomeomorphSubtypeCoe.symm) y := sorry
        _ = (s.localHomeomorphSubtypeCoe.trans e).symm y := rfl
        _ = r.symm y := rfl
    have congr_to : ∀ y, goal y = r ↑y := by intro; rfl
    have h2 : goal = r := LocalHomeomorph.ext goal r congr_to congr_inv (by simp)
    exact mem_of_eq_of_mem h2 (obvious s)
  -- singleton_hasGroupoid should also show this, by the way
  -- have : HasGroupoid t G := t.instHasGroupoid G -- as G is closed under restrictions
  let ehom := e.toHomeomorphSourceTarget -- temporarily given a name, to make the goal readable
  have : Structomorph G s t := {
    ehom with
    mem_groupoid := by
      intro c c' hc hc'
      show (c.symm).trans (ehom.toLocalHomeomorph.trans c') ∈ G -- just our pretty-printed goal

      -- Setting: have s ⊆ M and t ⊆ H, e maps s to t.
      -- c : s → H is a chart of M; c': t → M is essentially the inclusion.

      -- The atlas on H on itself has only one chart (by `chartedSpaceSelf_atlas H`),
      -- hence c' (as a restriction of that) is the inclusion.
      have : ∀ x, c' x = x := sorry -- unsure how to formally prove this...
      -- This *almost* gives our claim: except that `e` is a chart on M and c is one on s,
      -- so they don't fit together nicely. (Composing with the inclusion makes that nice...)
      -- let r := G.compatible hc he
      -- This version is rigorous... except the sorry (i.e. helper above) might be too optimistic.
      -- let e' : LocalHomeomorph s H := (ehom.toLocalHomeomorph.trans c')
      exact G.compatible hc (helper c' hc')
  }
  sorry
#exit

/-- Each chart inverse is a structomorphism. -/
-- do the same with symm... probably cannot reflect this in the types...
lemma LocalHomeomorphism.symm_toStructomorph {e : LocalHomeomorph M H} (he : e ∈ atlas H M)
    {G : StructureGroupoid H} : Structomorph G M H := sorry

-- Generalise this to all extended charts, if I is boundaryless.
end Future

section PresentHelpers
-- belongs in `SmoothManifoldWithCorners.lean`
/-- An identity local homeomorphism belongs to the maximal atlas on `E`. -/
lemma ofSet_in_maximal_atlas {s : Set E} (hs : IsOpen s) :
    LocalHomeomorph.ofSet s hs ∈ maximalAtlas 𝓘(ℝ, E) E := by
  set e := LocalHomeomorph.ofSet s hs
  set gr := (contDiffGroupoid ∞ I)
  rw [maximalAtlas, mem_maximalAtlas_iff]
  intro e' he'
  rw [he']
  simp only [comp_apply, LocalHomeomorph.ofSet_symm, LocalHomeomorph.trans_refl,
    LocalHomeomorph.refl_symm, LocalHomeomorph.refl_trans, and_self]
  apply ofSet_mem_contDiffGroupoid

lemma LocalHomeomorph.mapsTo_extend_symm {e : LocalHomeomorph M H} :
    MapsTo (e.extend I).symm (e.extend I '' e.source) e.source := by
  rintro x ⟨s, hs, rfl⟩
  have : (e.extend I).symm (e.extend I s) = s := e.extend_left_inv _ hs
  rw [this]
  exact hs

-- xxx: I could inline this
lemma ModelWithCorners.right_inv'' [I.Boundaryless] (x : E) : (I ∘ I.invFun) x = x := by
  have : x ∈ range I := by rw [I.range_eq_univ]; exact trivial
  exact I.right_inv this

-- XXX: can this proof by golfed?
lemma LocalHomeomorph.extend_right_inv [I.Boundaryless] {e : LocalHomeomorph M H}
    {x : E} (hx: x ∈ (e.extend I) '' e.source) : ((e.extend I) ∘ (e.extend I).symm) x = x := by
  have : I.invFun x ∈ e.target := by aesop
  have aux : ∀ y : H, y ∈ e.target → (e ∘ e.invFun) y = y := by intros; aesop
  calc ((e.extend I) ∘ (e.extend I).symm) x
    _ = I ((e ∘ e.invFun) (I.invFun x)) := rfl
    _ = I (I.invFun x) := by simp_rw [aux (I.invFun x) this]
    _ = x := I.right_inv'' x

-- all of these are on the "manifolds are locally path-connected" branch

-- these two lemmas should go into LocalHomeomorph.lean
lemma LocalHomeomorph.isOpenMapOn_source {e : LocalHomeomorph M H} {s : Set M}
    (hopen : IsOpen s) (hs : s ⊆ e.source) : IsOpen (e '' s) := by
  rw [(image_eq_target_inter_inv_preimage (e := e) hs)]
  exact e.continuous_invFun.preimage_open_of_open e.open_target hopen

lemma LocalHomeomorph.symm_isOpenMapOn_target {e : LocalHomeomorph M H} {t : Set H}
    (hopen : IsOpen t) (ht : t ⊆ e.target) : IsOpen (e.invFun '' t) := by
  have r : e.invFun '' t = e.source ∩ ↑e ⁻¹' t := symm_image_eq_source_inter_preimage (e := e) ht
  exact r ▸ e.continuous_toFun.preimage_open_of_open e.open_source hopen

-- all these results should go into SmoothManifoldWithCorners.lean
/-- If `I` is boundaryless, it is an open embedding. -/
theorem ModelWithCorners.toOpenEmbedding [I.Boundaryless] : OpenEmbedding I :=
  I.toHomeomorph.openEmbedding

/-- If `I` is boundaryless, `I.symm` is an open embedding. -/
theorem ModelWithCorners.toOpenEmbedding_symm [I.Boundaryless] : OpenEmbedding I.symm :=
  I.toHomeomorph.symm.openEmbedding

/-- If I has no boundary, `e.extend I` is an open map on its source. -/
lemma LocalHomeomorph.extend_isOpenMapOn_source [I.Boundaryless] {e : LocalHomeomorph M H}
    {s : Set M} (hopen : IsOpen s) (hs : s ⊆ e.source) : IsOpen ((e.extend I) '' s) := by
  simp only [extend_coe, image_comp I e]
  -- As I has no boundary, it is a homeomorphism, hence an open embedding.
  apply (I.toOpenEmbedding.open_iff_image_open).mp (e.isOpenMapOn_source hopen hs)

/-- If I has no boundary, `(e.extend I).symm` is an open map on its source. -/
lemma LocalHomeomorph.extend_symm_isOpenMapOn_target [I.Boundaryless] {e : LocalHomeomorph M H}
    {t : Set E} (hopen : IsOpen t) (ht : t ⊆ (e.extend I).target) : IsOpen ((e.extend I).symm '' t) := by
  have h : IsOpen (I.invFun '' t) := I.toOpenEmbedding_symm.open_iff_image_open.mp hopen
  have : (e.extend I).target = I.symm ⁻¹' e.target := by
    let r := e.extend_target I
    rw [I.range_eq_univ, inter_univ] at r
    exact r
  have : I.symm '' t ⊆ e.target := calc I.symm '' t
    _ ⊆ I.symm '' ((e.extend I).target) := image_subset _ ht
    _ = I.symm '' (I.symm ⁻¹' e.target) := by rw [this]
    _ ⊆ e.target := image_preimage_subset I.symm e.target
  rw [extend_coe_symm, image_comp]
  exact e.symm_isOpenMapOn_target h this

end PresentHelpers

section Present
-- On C^n manifolds without boundary, all charts and inverse charts are C^m.
-- TODO: generalise this to structomorphisms, once the above gap has been filled
-- FUTURE: add version of `e` and `e.symm`: that's basically `contMDiffOn_of_mem_maximalAtlas`
variable {e : LocalHomeomorph M H} (he : e ∈ atlas H M) [I.Boundaryless]

/-- An extended chart $e.extend I : M → E$ on a smooth manifold is smooth on `e.source`. -/
lemma extendedChart_smooth : ContMDiffOn I 𝓘(ℝ, E) ∞ (e.extend I) e.source := by
  let e' : LocalHomeomorph E E := LocalHomeomorph.refl E
  have h₁ : e ∈ maximalAtlas I M := subset_maximalAtlas _ he
  have h₂ : e' ∈ maximalAtlas 𝓘(ℝ, E) E := subset_maximalAtlas _ (by rfl)
  -- Looking closely, we want to show smoothness of f.
  set f := e.extend I ∘ (e.extend I).symm
  -- Since f=id on e.extend I '' e.source, we're done.
  have h : ∀ x ∈ (e.extend I) '' e.source, f x = x := fun _ hx ↦ e.extend_right_inv I hx
  apply (contMDiffOn_iff_of_mem_maximalAtlas' h₁ h₂ (Eq.subset rfl) (mapsTo_univ _ _)).mpr
  exact ContMDiffOn.contDiffOn (fun x hx ↦ ContMDiffWithinAt.congr smoothWithinAt_id h (h x hx))

/-- The inverse of an extended chart `e.extend I : M → E` on a smooth manifold without boundary
  is smooth on its source. -/
-- TODO: deduce this from a more general result about these being `Structomorph`
-- FIXME: does this hold for manifolds with boundary?
lemma extendedChart_symm_smooth :
    ContMDiffOn 𝓘(ℝ, E) I ∞ (e.extend I).symm (e.extend I '' e.source) := by
  have : IsOpen ((e.extend I) '' e.source) := e.extend_isOpenMapOn_source I e.open_source (Eq.subset rfl)
  let e' : LocalHomeomorph E E := LocalHomeomorph.ofSet (e.extend I '' e.source) this
  have h1 : e ∈ maximalAtlas I M := subset_maximalAtlas _ he
  have h2 : e' ∈ maximalAtlas 𝓘(ℝ, E) E := ofSet_in_maximal_atlas I this
  apply (contMDiffOn_iff_of_mem_maximalAtlas' h2 h1 (Eq.subset rfl) (e.mapsTo_extend_symm I)).mpr

  apply ContMDiffOn.contDiffOn
  -- We want to show smoothness of this function: locally, that's just the identity.
  set f := e.extend I ∘ (e.extend I).symm ∘ (LocalEquiv.symm (LocalHomeomorph.extend e' 𝓘(ℝ, E)))
  simp? says simp only [LocalHomeomorph.extend, LocalEquiv.coe_trans,
    ModelWithCorners.toLocalEquiv_coe, LocalHomeomorph.toFun_eq_coe, LocalEquiv.coe_trans_symm,
    LocalHomeomorph.coe_coe_symm, ModelWithCorners.toLocalEquiv_coe_symm, comp_apply,
    LocalHomeomorph.ofSet_toLocalEquiv, modelWithCornersSelf_localEquiv, LocalEquiv.trans_refl,
    LocalEquiv.ofSet_symm, LocalEquiv.ofSet_coe, comp.right_id, id_eq, image_id',
    LocalEquiv.ofSet_source]
  intro x hx
  exact smoothWithinAt_id.congr (fun _ hx ↦ e.extend_right_inv I hx) (e.extend_right_inv I hx)

/-- If `M` is a `C^m` manifold, extended charts are smooth local diffeomorphisms. -/
lemma extendedChart_toDiffeomorphOn : DiffeomorphOn I 𝓘(ℝ, E) M E ∞ :=
  {
    toLocalEquiv := (e.extend I)
    open_source := by rw [e.extend_source]; apply e.open_source
    open_target := by
      -- make a small lemma: e.extend_open_target or so. or an alternative proof of open_on_target
      rw [e.extend_target, I.range_eq_univ, inter_univ]
      exact I.continuous_symm.isOpen_preimage e.target e.open_target
      -- XXX: compare with old proof, which used
      --exact e.extend_isOpenMapOn_source I e.open_source (Eq.subset rfl)
    continuous_toFun := e.continuousOn_extend I
    continuous_invFun := e.continuousOn_extend_symm I
    contMDiffOn_toFun := by
      show ContMDiffOn I 𝓘(ℝ, E) ∞ (e.extend I) (e.extend I).source
      exact (e.extend_source I) ▸ (extendedChart_smooth I he)
    contMDiffOn_invFun := by
      show ContMDiffOn 𝓘(ℝ, E) I ∞ (e.extend I).symm (e.extend I).target
      have : (LocalHomeomorph.extend e I).target = (LocalHomeomorph.extend e I) '' e.source := by
        rw [e.extend_target, I.range_eq_univ, inter_univ]
        --rw [← @LocalHomeomorph.symm_image_target_eq_source]
        -- use a calc block and right inverse of I, or so
        rw [← e.image_source_eq_target]
        sorry
      exact this ▸ extendedChart_symm_smooth I he
  }

/-- If `M` is a `C^m` manifold, inverses of extended charts are smooth local diffeomorphisms. -/
-- By construction, `symm` of the previous local diffeo uses the inverse extended chart
-- `(e.extend I).symm`; so this is fine.
lemma extendedChart_symm_toDiffeomorphOn : DiffeomorphOn 𝓘(ℝ, E) I E M ∞ :=
  (extendedChart_toDiffeomorphOn I he).symm

-- Sanity check: we didn't silently change the map.
-- XXX: we're missing basic API to show this, the example below also fails.
example : (extendedChart_symm_toDiffeomorphOn I he).toFun = (e.extend I).invFun := by
  simp; sorry

-- FIXME: these should be most of the necessary API?
lemma asdf (h : DiffeomorphOn I J M N n) : (h.symm).toLocalHomeomorph = h.toLocalHomeomorph.symm := rfl
lemma asdf2 (h : DiffeomorphOn I J M N n) : (h.symm).toFun = h.invFun := rfl

-- also missing basic API; with or without the ext
example : (extendedChart_toDiffeomorphOn I he).toFun = (e.extend I).toFun := by
  simp; sorry

-- In particular: each chart and inverse chart is a local diffeomorphism at each point of its source.

-- Corollary. differentials of (inverse) charts are linear isomorphisms.

-- Corollary: differentials of charts are bijective.
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
