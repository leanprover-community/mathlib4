/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.IsLocalHomeomorph

/-! # The inverse function theorem for manifolds

In this file, we prove the inverse function theorem for functions between differentiable manifolds.
This theorem holds in different versions, for instance for `C^r` (for `r≥1`) and analytic maps.
Hence, we prove a general version first --- and will deduce the C^r and analytic cases from this.

The conclusion of the abstract inverse function theorem is that `f` is a local structomorphism.
The hypotheses are stated as a condition on the pregroupoid of the given atlas.

## Main definitions
* An **IFTPregroupoid** is a pregroupoid which is monotone and stable under local inverses
(in a precise sense). These are the setting for the abstract inverse function theorem.

## Main results
* The groupoid induced by an `IFTPregroupoid` is closed under restriction.
* `xxx`: the conceptual version of the inverse function theorem.

## TODO
- show that `contDiffPregroupoid` and `analyticPregroupoid` are `IFTPregroupoid`s
- deduce the standard phrasing of the inverse function theorem

## Tags
inverse function theorem, manifold, groupoid
-/

open Function Manifold Set TopologicalSpace Topology

-- Let M and N be manifolds over (E,H) and (E',H), respectively (on the same model space!).
-- We don't assume smoothness, but allow any structure groupoid.
variable {E E' H H' M N : Type*} {𝕂 : Type*} [NontriviallyNormedField 𝕂]
  [NormedAddCommGroup E] [NormedSpace 𝕂 E] [NormedAddCommGroup E'] [NormedSpace 𝕂 E']
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H N]
  (I : ModelWithCorners 𝕂 E H) (J : ModelWithCorners 𝕂 E' H)

/-! Re-phrasing the implicit function theorem over normed spaces in categorical language,
  using (pre-)groupoids and local structomorphisms.
  This unifies e.g. the smooth and analytic categories. -/
section IFTBasic
variable {n : ℕ∞} {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]

variable (𝕂) in
/-- A pregroupoid which satisfies the necessary conditions for the inverse function theorem.
Over the real or complex numbers, this includes the `C^n` and analytic pre-groupoids.
There's a design choice when defining this: one can either
  - assume that `P` contains only continuously differentiable functions on `s`
  (excluding e.g. the category PDiff of piece-wise differentiable functions), or
  - assume in the IFT hypothesis that `f` is cont. differentiable on some open set `s ∋ x`.
  With this definition, even the trivial and the continuous pregroupoid (over ℝ or ℂ) is an
  IFT groupoid, as the inverse `g` needs to satisfy fewer conditions.

We have chosen the latter, for slightly greater generality.In practice, one would only apply the
inverse function theorem in contexts where the differentiability follows anyway. -/
structure IFTPregroupoid (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕂 E] extends Pregroupoid E
where
  /-- Our property is **monotone** on open sets: if `s` is open and `s ⊆ t`, then
    `f ∈ P` on `t` implies `f ∈ P` on `s`. -/
  -- xxx: does this follow from the locality property of pregroupoids? think!
  monotonicity : ∀ {f s t}, IsOpen s → s ⊆ t → property f t → property f s
  /-- If `f ∈ P` on `s` and `f` is strictly differentiable at `x` with invertible differential,
    a local inverse `g` of `f` at `f x` also lies in `P` on some open neighbourhood `t` of `f x`.
    It is sufficient to consider the case of `s` open.
    We assume the existence of `g`; this holds automatically over ℝ or ℂ. -/
  inverse : ∀ {f g s t x}, ∀ {f' : E ≃L[𝕂] E}, IsOpen s → x ∈ s → property f s →
  -- We need t' to be open to deduce that `f` is a local structomorphism:
  -- that definition requires a partial homeomorphism in the (pre-)groupoid,
  -- which our setting only yields around x; that source is *open*.
    HasStrictFDerivAt (𝕜 := 𝕂) f f' x → InvOn g f s t →
    ∃ t' ⊆ t, f x ∈ t' ∧ IsOpen t' ∧ property g t'

/-- The groupoid associated to an IFT pre-groupoid. -/
def IFTPregroupoid.groupoid (P : IFTPregroupoid 𝕂 E) : StructureGroupoid E :=
  (P.toPregroupoid).groupoid

@[simp]
lemma IFTPregroupoid.groupoid_coe (P : IFTPregroupoid 𝕂 E) :
    P.groupoid = P.toPregroupoid.groupoid :=
  rfl

/-- If `P` is an `IFTPregroupoid`, its induced groupoid is `ClosedUnderRestriction`. -/
-- Note: this proof only uses monotonicity, hence could be generalised to
-- "a monotone pregroupoid induces a groupoid closed under restriction".
-- Is it worth refactoring existing proofs of `ClosedUnderRestriction` this way?
lemma IFTPregroupoid.isClosedUnderRestriction_groupoid (P : IFTPregroupoid 𝕂 E) :
    ClosedUnderRestriction (P.groupoid) := by
  refine { closedUnderRestriction := ?_ }
  intro e he s hs
  obtain ⟨l, r ⟩ := mem_groupoid_of_pregroupoid.mp he
  apply mem_groupoid_of_pregroupoid.mpr
  constructor
  · rw [e.restr_source' s hs]
    exact P.monotonicity (e.open_source.inter hs) (inter_subset_left _ _) l
  · show P.property (e.restr s).symm (e.restr s).symm.source
    rw [(e.restr s).symm_source]
    exact P.monotonicity (e.restr s).open_target (by simp) r

/-- Categorical statement of the Inverse Function Theorem on a Banach space.
  Suppose `f` has invertible differential at `x` and lies in an IFTPregroupoid `P` on `s ∋ x`.
  Then `f` is a local structomorphism at `x` (within some open set `s' ∋ x`).
  For `P=contDiffPregroupoid n`, this recovers the standard statement. -/
lemma HasStrictFDerivAt.isLocalStructomorphWithinAt_of_IFTPregroupoid [CompleteSpace E] {f : E → E}
    {s : Set E} {x : E} {f' : E ≃L[𝕂] E} (hf' : HasStrictFDerivAt (𝕜 := 𝕂) f f' x)
    (hf : ContDiffOn 𝕂 n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n)
    {P : IFTPregroupoid 𝕂 E} (hfP : P.property f s) :
    ∃ s', x ∈ s' ∧ IsOpen s' ∧ P.groupoid.IsLocalStructomorphWithinAt f s' x := by
  set G := P.groupoid
  -- Apply the local lemma to find a local inverse `g` of `f` at `f x`.
  let f_loc := hf'.toPartialHomeomorph
  have hx' : x ∈ f_loc.source := hf'.mem_toPartialHomeomorph_source

  -- Since `f` is `P` on `s`, we get a local inverse `f_loc` on `f_loc.source`.
  -- Our IFT groupoid property applies on the intersection, hence we need monotonity of `P`.
  let s' := (f_loc.source ∩ s)
  have hs' : IsOpen s' := f_loc.open_source.inter hs
  have hfP' : P.property f s' := P.monotonicity hs' (inter_subset_right _ _) hfP
  -- Since `P` is an IFTPregroupoid, `P.property g t'` for some open set
  -- `t' ⊆ t := f_loc.target` containing `x`.
  have hinv' : InvOn f_loc.symm f_loc s' (f_loc '' s') :=
    f_loc.invOn.mono (inter_subset_left _ _) (image_subset _ (inter_subset_left _ _))
  let p := P.inverse hs' (mem_inter hx' hx) hfP' hf' hinv'

  rcases p with ⟨t', htt', hxt', ht', hP⟩
  let s'' := s' ∩ f ⁻¹' t'
  have : ContinuousOn f s' := hf.continuousOn.mono (inter_subset_right _ _)
  have hs'' : IsOpen s'' := this.isOpen_inter_preimage hs' ht'
  have hG : P.groupoid.IsLocalStructomorphWithinAt f s'' x := by
    intro hx
    refine ⟨f_loc.restrOpen s'' hs'', ?_, eqOn_refl f _, ?_⟩
    · apply mem_groupoid_of_pregroupoid.mpr
      have aux : f_loc.source ∩ s' = s' := by simp
      rw [f_loc.restrOpen_source]--, aux]
      constructor
      · apply P.monotonicity (t := s') (f_loc.open_source.inter hs'') ?_ hfP'
        rw [← aux]
        exact inter_subset_inter_right _ (inter_subset_left _ _)
      · have : (f_loc.restrOpen s' hs').target = f_loc '' s' := by
          rw [f_loc.restrOpen_target s' hs', aux]
        -- TODO: complete proof, using things with t and t'!
        show P.property (f_loc.restrOpen s'' hs'').symm (f_loc.restrOpen s'' hs'').target
        have : P.property f_loc.symm t' := hP
        --have : t' ⊆ f_loc '' s' := htt', hence t' ⊆ f_loc '' s'' follows
        rw [f_loc.restrOpen_target]
        -- final step: argue with the congr property; restrOpen equals f_loc on s'',
        -- which is an open set (by `hs''`)
        sorry
    · rw [f_loc.restrOpen_source]
      apply (mem_inter hx' hx)
  refine ⟨s'', by apply mem_inter (mem_inter hx' hx); exact hxt', hs'', hG⟩
  -- -- Thus, f and g define a local homeomorphism.
  -- have : P.groupoid.IsLocalStructomorphWithinAt f s' x := by
  --   intro hx
  --   refine ⟨f_loc.restrOpen s' hs', ?_, eqOn_refl f _, ?_⟩
  --   · apply mem_groupoid_of_pregroupoid.mpr
  --     rw [f_loc.restrOpen_source, aux]
  --     sorry -- TODO: fix proof!
  --     --exact ⟨hfP', this ▸ p⟩

#exit

/-- The pregroupoid of `C^n` functions on `E`. -/
def contDiffPregroupoidBasic : Pregroupoid E := {
  property := fun f s ↦ ContDiffOn 𝕂 n f s
  comp := fun {f g} {u v} hf hg _ _ _ ↦ hg.comp' hf
  id_mem := contDiffOn_id
  locality := fun _ h ↦ contDiffOn_of_locally_contDiffOn h
  congr := by intro f g u _ congr hf; exact (contDiffOn_congr congr).mpr hf
}

-- xxx: generalise this argument to ℂ also
variable [NormedSpace ℝ E] [NormedSpace ℝ E']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H)

-- This is the key lemma I need to showing that C^n maps define an `IFTPregroupoid`.
-- we need to work over ℝ or ℂ, otherwise `toLocalInverse` doesn't apply
lemma contDiffPregroupoindIsIFT_aux [CompleteSpace E] {f g : E → E} {s t : Set E} {x : E}
    {f' : E ≃L[ℝ] E} (hf : ContDiffAt ℝ n f x) (hf' : HasFDerivAt (𝕜 := ℝ) f f' x)
    (hinv : InvOn g f s t) (hm : MapsTo g t s) (hn : 1 ≤ n) : ContDiffAt ℝ n g (f x) := by
  let h := hf.toPartialHomeomorph f hf' hn
  have h2 : ContDiffAt ℝ n h.symm (f x) := hf.to_localInverse (f' := f') hf' hn
  have hinv : h.symm (f x) = x := by
    show h.symm (h x) = x
    apply h.left_inv (hf.mem_toPartialHomeomorph_source hf' hn)
  let r := h.contDiffAt_symm (hf.image_mem_toPartialHomeomorph_target hf' hn)
    (hinv.symm ▸ hf') (hinv.symm ▸ hf)
  -- shrinking s and t (and restricting h), we may assume s = h.source and t = h.target
  -- then both of these are immediate
  have h1' : InvOn h.symm h s t := sorry -- is then h.invOn
  have h2' : InvOn g f s t := sorry -- rewrite h=f in hinv
  have : EqOn h.symm g t := eqOn_of_leftInvOn_of_rightInvOn h1'.1 h2'.2 hm
  have : ContDiffAt ℝ n h.symm (f x) := h2
  -- last step: apply ContDiffAt.congr, seems to be missing; have e.g. fderiv_congr
  -- slightly different route: add ContDiffOn assumption, then it exists?
  sorry

/-- If `E` is complete and `n ≥ 1`, the pregroupoid of `C^n` functions
  is an IFT pregroupoid.
  The proof relies on the mean value theorem, which is why ℝ or ℂ is required. -/
def contDiffBasicIsIFTPregroupoid [CompleteSpace E] (hn : 1 ≤ n) : IFTPregroupoid ℝ E where
  toPregroupoid := contDiffPregroupoidBasic (n := n)
  monotonicity := fun {f} _ _ _ hst hf ↦ hf.mono hst
  inverse := by
    intro f g s t x f' hs hx hf hf' hinv
    -- Since f is continuously differentiable on s, there's a neighbourhood `U` of `x` s.t.
    -- `df_x'` is an isomorphism for all `x' ∈ U`.
    rcases mem_nhds_iff.mp f'.nhds with ⟨t', ht', ht'open, hft⟩
    let U := s ∩ (fun x ↦ fderiv ℝ f x) ⁻¹' t'
    have : IsOpen U := (hf.continuousOn_fderiv_of_isOpen hs hn).isOpen_inter_preimage hs ht'open
    have hxU : x ∈ U := by
      refine ⟨hx, ?_⟩
      show fderiv ℝ f x ∈ t'
      exact mem_of_eq_of_mem hf'.hasFDerivAt.fderiv hft

    let fhom := ContDiffAt.toPartialHomeomorph f (hf.contDiffAt (hs.mem_nhds hx)) hf'.hasFDerivAt hn
    have : f = fhom := by rw [ContDiffAt.toPartialHomeomorph_coe]
    have h3 : IsLocalHomeomorphOn f fhom.source :=
      IsLocalHomeomorphOn.mk f fhom.source (fun x hx ↦ ⟨fhom, hx, fun y hy ↦ by rw [this]⟩)
    -- now: U ⊆ fhom.source and h3 imply f(U) is open
    -- this is a missing lemma about local homeomorphisms
    have scifi : IsOpen (f '' U) := sorry
    -- shrinking s and t, we may assume s = fhom.source, t = fhom.target
    -- use filters to formalise this?
    have shrink1 : s = fhom.source := sorry
    have shrink2 : t = fhom.target := sorry

    have : MapsTo f s t := by
      rw [shrink1, shrink2]
      exact fhom.mapsTo
    have hm : MapsTo g t s := by
      rw [shrink1, shrink2]
      have : EqOn fhom.symm g fhom.target := sorry -- proven in aux lemma above
      rw [← this.mapsTo_iff (t := fhom.source)]
      exact fhom.symm_mapsTo
    have hu₁ : f '' U ⊆ t :=
      Subset.trans (image_subset _ (inter_subset_left _ _)) (mapsTo'.mp this)
    refine ⟨f '' U , hu₁, mem_image_of_mem f hxU, scifi, ?_⟩
    suffices ∀ y : f '' U, ContDiffAt ℝ n g y from fun y hy ↦ (this ⟨y, hy⟩).contDiffWithinAt
    -- Show g is continuously differentiable at each y ∈ f(U).
    intro ⟨y, x', hx'U, hx'y⟩
    have : x' ∈ (fun x ↦ fderiv ℝ f x) ⁻¹' t' := mem_of_mem_inter_right hx'U
    -- Last step: upgrade `fderiv ℝ f x'` to an isomorphism, using `x' ∈ U`.
    rcases ht' this with ⟨f'', hf''eq⟩
    have hs : s ∈ 𝓝 x' := hs.mem_nhds (mem_of_mem_inter_left hx'U)
    have : HasFDerivAt f f''.toContinuousLinearMap x' := by
      rw [hf''eq]
      exact ((hf.contDiffAt hs).differentiableAt hn).hasFDerivAt
    exact hx'y ▸ (contDiffPregroupoindIsIFT_aux (hf.contDiffAt hs) this hinv hm hn)

end IFTBasic

-- FUTURE: show that the analytic pregroupoid is also IFT

/-! General version of the IFT on manifolds. -/
section IFTFull
-- define IFTPregroupoids on H, via (E, I)
-- define contDiffPregroupoid: copy-paste from standard def (later: deduplicate)

-- theorem: contDiffPregroupoid is an IFT pregroupoid
-- local inverse of IFT (mostly already done)

-- categorical IFT: using LiftProp and G.IsLocalStructomorphWithinAt

-- finally: (try to) prove that LiftProp (G.isLocalStructomorphWithinAt) iff f and f.symm ∈ P
-- this would generalise isLocalStructomorphOn_contDiffGroupoid_iff
section IFTFull
