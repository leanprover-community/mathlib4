/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.Diffeomorph

/-! # The inverse function theorem for manifolds
TODO: complete docstring
-/

open Function Manifold Set TopologicalSpace Topology

-- Let M and N be manifolds over (E,H) and (E',H'), respectively.
-- We don't assume smoothness, but allow any structure groupoid (which contains C¹ maps).
variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
   [TopologicalSpace N] [ChartedSpace H N]
  -- TODO: relax these conditions!!
  (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M]
  (J : ModelWithCorners ℝ E' H) [SmoothManifoldWithCorners J N]

/-! Re-phrasing the implicit function theorem over normed spaces in categorical language,
  using (pre-)groupoids and local structomorphisms.
  This unifies e.g. the smooth and analytic categories. -/
section IFTBasic
variable {n : ℕ∞} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
-- XXX: generalise to any field 𝕜 which is ℝ or ℂ

/-- A pregroupoid which satisfies the necessary conditions for the implicit function theorem.
Over the real or complex numbers, this includes the `C^n` and analytic pre-groupoids.
There's a design choice when defining this: one can either
  - assume that `P` contains only continuously differentiable functions on `s` or
  - assume in the IFT hypothesis that `f` is continuously differentiable on some open set `s ∋ x`.

The first definition is more restrictive, excluding e.g. the category PDiff;
on the other hand, with the latter definition, even the trivial and the continuous pregroupoid
(over ℝ or ℂ) is an IFT groupoid, as the inverse `g` needs to satisfy fewer conditions.

We have chosen the latter, for slightly greater generality. In practice, one would only apply the
IFT in contexts where the differentiability follows anyway. -/
structure IFTPregroupoid (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] extends Pregroupoid E
where
  /-- Our property is **monotone** on open sets: if `s` is open and `s ⊆ t`, then
    `f ∈ P` on `t` implies `f ∈ P` on `s`. -/
  monotonicity : ∀ {f s t}, IsOpen s → s ⊆ t → property f t → property f s
  /-- If `f ∈ P` on `s` and `f` is differentiable at `x` with invertible differential `df_x`,
    a local inverse `g` of `f` at `f x` also lies in `P` on some open neighbourhood `t` of `f x`.
    It is sufficient to consider the case of `s` open.
    We assume the existence of `g`; this holds automatically over ℝ or ℂ. -/
  inverse : ∀ {f g s t x}, ∀ {f' : E ≃L[ℝ] E}, IsOpen s → x ∈ s → property f s →
  -- We need t' to be open to deduce that `f` is a local structomorphism:
  -- that definition requires a partial homeomorphism in the (pre-)groupoid,
  -- which our setting only yields around x; that source is *open*.
    HasFDerivAt (𝕜 := ℝ) f f' x → InvOn g f s t → ∃ t' ⊆ t, f x ∈ t' ∧ IsOpen t' ∧ property g t'

/-- The groupoid associated to an IFT pre-groupoid. -/
def IFTPregroupoid.groupoid (P : IFTPregroupoid E) : StructureGroupoid E :=
  (P.toPregroupoid).groupoid

@[simp]
lemma IFTPregroupoid.groupoid_coe {P : IFTPregroupoid E} : P.groupoid = P.toPregroupoid.groupoid :=
  rfl

/-- If `P` is an `IFTPregroupoid`, its induced groupoid is `ClosedUnderRestriction`. -/
-- FUTURE: this proof only uses monotonicity, hence could be generalised to
-- "a monotone pregroupoid induces a groupoid closed under restriction".
-- Is it worth refactoring existing proofs of ClosedUnderRestriction this way?
lemma IFTPregroupoid.isClosedUnderRestriction_groupoid (P : IFTPregroupoid E) :
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
lemma IFT_categorical [CompleteSpace E] {f : E → E} {s : Set E} {x : E}
    (hf : ContDiffOn ℝ n f s) {f' : E ≃L[ℝ] E} (hf' : HasFDerivAt (𝕜 := ℝ) f f' x) (hs : IsOpen s)
    (hx : x ∈ s) (hn : 1 ≤ n) {P : IFTPregroupoid E} (hfP : P.property f s) :
    ∃ s', x ∈ s' ∧ IsOpen s' ∧ P.groupoid.IsLocalStructomorphWithinAt f s' x := by
  set G := P.groupoid
  -- Apply the local lemma to find a local inverse `g` of `f` at `f x`.
  let diff := hf.contDiffAt (hs.mem_nhds hx)
  let f_loc := diff.toPartialHomeomorph f hf' hn
  have hx' : x ∈ f_loc.source := diff.mem_toPartialHomeomorph_source  hf' hn

  -- Two sets in play here: `f` is `P` on `s`; we get a local inverse `f_loc` on `f_loc.source`.
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
      -- show property on s' (copy from below), then use monotonicity!
      · have : P.property f_loc s' := sorry
        show P.property f_loc (f_loc.source ∩ s'')
        apply P.monotonicity (t := s') (f_loc.open_source.inter hs'')
        rw [← aux]
        exact inter_subset_inter_right f_loc.source (inter_subset_left _ _)
        exact this
      · have : (f_loc.restrOpen s' hs').target = f_loc '' s' := by rw [f_loc.restrOpen_target s' hs', aux]
        -- complete proof, with the below things!
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

/-- The pregroupoid of `C^n` functions on `E`. -/
def contDiffPregroupoidBasic : Pregroupoid E := {
  property := fun f s ↦ ContDiffOn ℝ n f s
  comp := fun {f g} {u v} hf hg _ _ _ ↦ hg.comp' hf
  id_mem := contDiffOn_id
  locality := fun _ h ↦ contDiffOn_of_locally_contDiffOn h
  congr := by intro f g u _ congr hf; exact (contDiffOn_congr congr).mpr hf
}

-- this is the key lemma I need to showing that C^n maps define a better pregroupoid
-- we need to work over ℝ or ℂ, otherwise `toLocalInverse` doesn't apply
lemma contDiffPregroupoindIsIFT_aux [CompleteSpace E] {f g : E → E} {s t : Set E} {x : E}
    {f' : E ≃L[ℝ] E} (hf : ContDiffAt ℝ n f x) (hf' : HasFDerivAt (𝕜 := ℝ) f f' x)
    (hinv : InvOn g f s t) (hm : MapsTo g t s) (hn : 1 ≤ n) : ContDiffAt ℝ n g (f x) := by
  let r := hf.to_localInverse (f' := f') hf' hn -- ContDiffAt ℝ n (hf.localInverse hf' hn) (f x)
  set g' := ContDiffAt.localInverse hf hf' hn with eq
  let h := hf.toPartialHomeomorph f hf' hn
  -- XXX: not true! s, t are subsets --> should replace t by the source of the local homeo
  have : EqOn g g' h.target := by
    have hinv' : InvOn g' f h.source h.target := by
      apply (hf.localInverse_eq_toLocalHomeomorph_symm hf' hn) ▸ h.invOn
    -- xxx: extract into lemma: if MapsTo g t s, and if g and g' are inverses of f on s, g=g' on s.
    intro y hy
    let x := g y
    have hm' : MapsTo g h.target h.source := by
      -- show MapsTo g' h.target h.source -- rewrite by EqOn...
      have : MapsTo g' h.target h.source := by
        have : g' = h.symm := (hf.localInverse_eq_toLocalHomeomorph_symm hf' hn)
        rw [this]
        exact h.symm_mapsTo
      sorry -- rewrite by EqOn from the previous have
    have hx : x ∈ h.source := hm' hy
    -- these should both be routine
    have : h.target ⊆ t := sorry
    have hy : y ∈ t := this hy
    have : h.source ⊆ s := sorry
    calc g y
      _ = g (f x) := by rw [hinv.2 hy]
      _ = x := by rw [hinv.1 (this hx)]
      _ = g' (f x) := by rw [hinv'.1 hx]
      _ = g' y := by rw [hinv.2 hy]
  -- apply fderiv_congr to rewrite g' with g
  sorry

-- also want a version of the IFT with HasStrictFDerivAt; uses the below under the hood

/-- If `E` is complete and `n ≥ 1`, the pregroupoid of `C^n` functions
  is an IFT pregroupoid.
  The proof relies on the mean value theorem, which is why ℝ or ℂ is required. -/
def contDiffBasicIsIFTPregroupoid [CompleteSpace E] (hn : 1 ≤ n) : IFTPregroupoid E where
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
      exact mem_of_eq_of_mem hf'.fderiv hft
    -- TODO: argue f is a local homeomorphism, then the next three sorries are immediate
    have : MapsTo f s t := sorry
    have hm : MapsTo g t s := sorry
    have scifi : IsOpen (f '' U) := sorry -- need to argue harder: f is a local homeo or so
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

-- FIXME: show that the analytic pregroupoid is also IFT

end IFTBasic

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
