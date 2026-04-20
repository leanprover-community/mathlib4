/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # The groupoid of `C^n`, fiberwise-linear maps

This file contains preliminaries for the definition of a `C^n` vector bundle: an associated
`StructureGroupoid`, the groupoid of `contMDiffFiberwiseLinear` functions.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace

open scoped Manifold Topology

/-! ### The groupoid of `C^n`, fiberwise-linear maps -/


variable {𝕜 B F : Type*} [TopologicalSpace B]
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace FiberwiseLinear

variable {φ φ' : B → F ≃L[𝕜] F} {U U' : Set B}

/-- For `B` a topological space and `F` a `𝕜`-normed space, a map from `U : Set B` to `F ≃L[𝕜] F`
determines an open partial homeomorphism from `B × F` to itself by its action fiberwise. -/
def openPartialHomeomorph (φ : B → F ≃L[𝕜] F) (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B → F →L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B → F →L[𝕜] F) U) :
    OpenPartialHomeomorph (B × F) (B × F) where
  toFun x := (x.1, φ x.1 x.2)
  invFun x := (x.1, (φ x.1).symm x.2)
  source := U ×ˢ univ
  target := U ×ˢ univ
  map_source' _x hx := mk_mem_prod hx.1 (mem_univ _)
  map_target' _x hx := mk_mem_prod hx.1 (mem_univ _)
  left_inv' _ _ := Prod.ext rfl (ContinuousLinearEquiv.symm_apply_apply _ _)
  right_inv' _ _ := Prod.ext rfl (ContinuousLinearEquiv.apply_symm_apply _ _)
  open_source := hU.prod isOpen_univ
  open_target := hU.prod isOpen_univ
  continuousOn_toFun :=
    have : ContinuousOn (fun p : B × F => ((φ p.1 : F →L[𝕜] F), p.2)) (U ×ˢ univ) :=
      hφ.prodMap continuousOn_id
    continuousOn_fst.prodMk (isBoundedBilinearMap_apply.continuous.comp_continuousOn this)
  continuousOn_invFun :=
    have : ContinuousOn (fun p : B × F => (((φ p.1).symm : F →L[𝕜] F), p.2)) (U ×ˢ univ) :=
      h2φ.prodMap continuousOn_id
    continuousOn_fst.prodMk (isBoundedBilinearMap_apply.continuous.comp_continuousOn this)

/-- Compute the composition of two open partial homeomorphisms induced by fiberwise linear
equivalences. -/
theorem trans_openPartialHomeomorph_apply (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B → F →L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B → F →L[𝕜] F) U) (hU' : IsOpen U')
    (hφ' : ContinuousOn (fun x => φ' x : B → F →L[𝕜] F) U')
    (h2φ' : ContinuousOn (fun x => (φ' x).symm : B → F →L[𝕜] F) U') (b : B) (v : F) :
    (FiberwiseLinear.openPartialHomeomorph φ hU hφ h2φ ≫ₕ
      FiberwiseLinear.openPartialHomeomorph φ' hU' hφ' h2φ')
        ⟨b, v⟩ =
      ⟨b, φ' b (φ b v)⟩ :=
  rfl

/-- Compute the source of the composition of two open partial homeomorphisms induced by fiberwise
linear equivalences. -/
theorem source_trans_openPartialHomeomorph (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B → F →L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B → F →L[𝕜] F) U) (hU' : IsOpen U')
    (hφ' : ContinuousOn (fun x => φ' x : B → F →L[𝕜] F) U')
    (h2φ' : ContinuousOn (fun x => (φ' x).symm : B → F →L[𝕜] F) U') :
    (FiberwiseLinear.openPartialHomeomorph φ hU hφ h2φ ≫ₕ
          FiberwiseLinear.openPartialHomeomorph φ' hU' hφ' h2φ').source =
      (U ∩ U') ×ˢ univ := by
  dsimp only [FiberwiseLinear.openPartialHomeomorph]; mfld_set_tac

/-- Compute the target of the composition of two open partial homeomorphisms induced by fiberwise
linear equivalences. -/
theorem target_trans_openPartialHomeomorph (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B → F →L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B → F →L[𝕜] F) U) (hU' : IsOpen U')
    (hφ' : ContinuousOn (fun x => φ' x : B → F →L[𝕜] F) U')
    (h2φ' : ContinuousOn (fun x => (φ' x).symm : B → F →L[𝕜] F) U') :
    (FiberwiseLinear.openPartialHomeomorph φ hU hφ h2φ ≫ₕ
          FiberwiseLinear.openPartialHomeomorph φ' hU' hφ' h2φ').target =
      (U ∩ U') ×ˢ univ := by
  dsimp only [FiberwiseLinear.openPartialHomeomorph]; mfld_set_tac

end FiberwiseLinear

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*}
  [TopologicalSpace HB] [ChartedSpace HB B] {IB : ModelWithCorners 𝕜 EB HB}

/-- Let `e` be an open partial homeomorphism of `B × F`.  Suppose that at every point `p` in the
source of `e`, there is some neighbourhood `s` of `p` on which `e` is equal to a bi-`C^n` fiberwise
linear open partial homeomorphism.
Then the source of `e` is of the form `U ×ˢ univ`, for some set `U` in `B`, and, at any point `x` in
`U`, admits a neighbourhood `u` of `x` such that `e` is equal on `u ×ˢ univ` to some bi-`C^n`
fiberwise linear open partial homeomorphism. -/
theorem ContMDiffFiberwiseLinear.locality_aux₁
    (n : WithTop ℕ∞) (e : OpenPartialHomeomorph (B × F) (B × F))
    (h : ∀ p ∈ e.source, ∃ s : Set (B × F), IsOpen s ∧ p ∈ s ∧
      ∃ (φ : B → F ≃L[𝕜] F) (u : Set B) (hu : IsOpen u)
        (hφ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => (φ x : F →L[𝕜] F)) u)
        (h2φ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => ((φ x).symm : F →L[𝕜] F)) u),
          (e.restr s).EqOnSource
            (FiberwiseLinear.openPartialHomeomorph φ hu hφ.continuousOn h2φ.continuousOn)) :
    ∃ U : Set B, e.source = U ×ˢ univ ∧ ∀ x ∈ U,
        ∃ (φ : B → F ≃L[𝕜] F) (u : Set B) (hu : IsOpen u) (_huU : u ⊆ U) (_hux : x ∈ u),
          ∃ (hφ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => (φ x : F →L[𝕜] F)) u)
            (h2φ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => ((φ x).symm : F →L[𝕜] F)) u),
            (e.restr (u ×ˢ univ)).EqOnSource
              (FiberwiseLinear.openPartialHomeomorph φ hu hφ.continuousOn h2φ.continuousOn) := by
  rw [SetCoe.forall'] at h
  choose s hs hsp φ u hu hφ h2φ heφ using h
  have hesu : ∀ p : e.source, e.source ∩ s p = u p ×ˢ univ := by
    intro p
    rw [← e.restr_source' (s _) (hs _)]
    exact (heφ p).1
  have hu' : ∀ p : e.source, (p : B × F).fst ∈ u p := by
    intro p
    have : (p : B × F) ∈ e.source ∩ s p := ⟨p.prop, hsp p⟩
    simpa only [hesu, mem_prod, mem_univ, and_true] using this
  have heu : ∀ p : e.source, ∀ q : B × F, q.fst ∈ u p → q ∈ e.source := by
    intro p q hq
    have : q ∈ u p ×ˢ (univ : Set F) := ⟨hq, trivial⟩
    rw [← hesu p] at this
    exact this.1
  have he : e.source = (Prod.fst '' e.source) ×ˢ (univ : Set F) := by
    apply HasSubset.Subset.antisymm
    · intro p hp
      exact ⟨⟨p, hp, rfl⟩, trivial⟩
    · rintro ⟨x, v⟩ ⟨⟨p, hp, rfl : p.fst = x⟩, -⟩
      exact heu ⟨p, hp⟩ (p.fst, v) (hu' ⟨p, hp⟩)
  refine ⟨Prod.fst '' e.source, he, ?_⟩
  rintro x ⟨p, hp, rfl⟩
  refine ⟨φ ⟨p, hp⟩, u ⟨p, hp⟩, hu ⟨p, hp⟩, ?_, hu' _, hφ ⟨p, hp⟩, h2φ ⟨p, hp⟩, ?_⟩
  · intro y hy; exact ⟨(y, 0), heu ⟨p, hp⟩ ⟨_, _⟩ hy, rfl⟩
  · rw [← hesu, e.restr_source_inter]; exact heφ ⟨p, hp⟩

/-- Let `e` be an open partial homeomorphism of `B × F` whose source is `U ×ˢ univ`, for some set
`U` in `B`, and which, at any point `x` in `U`, admits a neighbourhood `u` of `x` such that `e` is
equal on `u ×ˢ univ` to some bi-`C^n` fiberwise linear open partial homeomorphism.  Then `e` itself
is equal to some bi-`C^n` fiberwise linear open partial homeomorphism.

This is the key mathematical point of the `locality` condition in the construction of the
`StructureGroupoid` of bi-`C^n` fiberwise linear open partial homeomorphisms.  The proof is by
gluing together the various bi-`C^n` fiberwise linear open partial homeomorphism which exist
locally.

The `U` in the conclusion is the same `U` as in the hypothesis. We state it like this, because this
is exactly what we need for `contMDiffFiberwiseLinear`. -/
theorem ContMDiffFiberwiseLinear.locality_aux₂
    (n : WithTop ℕ∞) (e : OpenPartialHomeomorph (B × F) (B × F)) (U : Set B)
    (hU : e.source = U ×ˢ univ)
    (h : ∀ x ∈ U,
      ∃ (φ : B → F ≃L[𝕜] F) (u : Set B) (hu : IsOpen u) (_hUu : u ⊆ U) (_hux : x ∈ u)
        (hφ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => (φ x : F →L[𝕜] F)) u)
        (h2φ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => ((φ x).symm : F →L[𝕜] F)) u),
          (e.restr (u ×ˢ univ)).EqOnSource
            (FiberwiseLinear.openPartialHomeomorph φ hu hφ.continuousOn h2φ.continuousOn)) :
    ∃ (Φ : B → F ≃L[𝕜] F) (U : Set B) (hU₀ : IsOpen U) (hΦ :
      ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => (Φ x : F →L[𝕜] F)) U) (h2Φ :
      ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => ((Φ x).symm : F →L[𝕜] F)) U),
      e.EqOnSource
      (FiberwiseLinear.openPartialHomeomorph Φ hU₀ hΦ.continuousOn h2Φ.continuousOn) := by
  classical
  rw [SetCoe.forall'] at h
  choose! φ u hu hUu hux hφ h2φ heφ using h
  have heuφ : ∀ x : U, EqOn e (fun q => (q.1, φ x q.1 q.2)) (u x ×ˢ univ) := fun x p hp ↦ by
    refine (heφ x).2 ?_
    rw [(heφ x).1]
    exact hp
  have huφ : ∀ (x x' : U) (y : B), y ∈ u x → y ∈ u x' → φ x y = φ x' y := fun p p' y hyp hyp' ↦ by
    ext v
    have h1 : e (y, v) = (y, φ p y v) := heuφ _ ⟨(id hyp : (y, v).fst ∈ u p), trivial⟩
    have h2 : e (y, v) = (y, φ p' y v) := heuφ _ ⟨(id hyp' : (y, v).fst ∈ u p'), trivial⟩
    exact congr_arg Prod.snd (h1.symm.trans h2)
  have hUu' : U = ⋃ i, u i := by
    ext x
    rw [mem_iUnion]
    refine ⟨fun h => ⟨⟨x, h⟩, hux _⟩, ?_⟩
    rintro ⟨x, hx⟩
    exact hUu x hx
  have hU' : IsOpen U := by
    rw [hUu']
    apply isOpen_iUnion hu
  let Φ₀ : U → F ≃L[𝕜] F := iUnionLift u (fun x => φ x ∘ (↑)) huφ U hUu'.le
  let Φ : B → F ≃L[𝕜] F := fun y =>
    if hy : y ∈ U then Φ₀ ⟨y, hy⟩ else ContinuousLinearEquiv.refl 𝕜 F
  have hΦ : ∀ (y) (hy : y ∈ U), Φ y = Φ₀ ⟨y, hy⟩ := fun y hy => dif_pos hy
  have hΦφ : ∀ x : U, ∀ y ∈ u x, Φ y = φ x y := by
    intro x y hyu
    refine (hΦ y (hUu x hyu)).trans ?_
    exact iUnionLift_mk ⟨y, hyu⟩ _
  have hΦ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun y => (Φ y : F →L[𝕜] F)) U := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro x hx
    refine ⟨u ⟨x, hx⟩, hu ⟨x, hx⟩, hux _, ?_⟩
    refine (ContMDiffOn.congr (hφ ⟨x, hx⟩) ?_).mono inter_subset_right
    intro y hy
    rw [hΦφ ⟨x, hx⟩ y hy]
  have h2Φ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun y => ((Φ y).symm : F →L[𝕜] F)) U := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro x hx
    refine ⟨u ⟨x, hx⟩, hu ⟨x, hx⟩, hux _, ?_⟩
    refine (ContMDiffOn.congr (h2φ ⟨x, hx⟩) ?_).mono inter_subset_right
    intro y hy
    rw [hΦφ ⟨x, hx⟩ y hy]
  refine ⟨Φ, U, hU', hΦ, h2Φ, hU, fun p hp => ?_⟩
  rw [hU] at hp
  rw [heuφ ⟨p.fst, hp.1⟩ ⟨hux _, hp.2⟩]
  congrm (_, ?_)
  rw [hΦφ]
  apply hux

-- Having this private lemma speeds up `simp` calls below a lot.
-- TODO: understand why and fix the underlying issue (relatedly, the `simp` calls
-- in `contMDiffFiberwiseLinear` are quite slow, even with this change)
private theorem mem_aux {e : OpenPartialHomeomorph (B × F) (B × F)} {n : WithTop ℕ∞} :
    (e ∈ ⋃ (φ : B → F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U)
      (hφ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => φ x : B → F →L[𝕜] F) U)
      (h2φ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => (φ x).symm : B → F →L[𝕜] F) U),
        {e | e.EqOnSource (FiberwiseLinear.openPartialHomeomorph φ hU hφ.continuousOn
          h2φ.continuousOn)}) ↔
      ∃ (φ : B → F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U)
        (hφ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => φ x : B → F →L[𝕜] F) U)
        (h2φ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => (φ x).symm : B → F →L[𝕜] F) U),
          e.EqOnSource
            (FiberwiseLinear.openPartialHomeomorph φ hU hφ.continuousOn h2φ.continuousOn) := by
  simp only [mem_iUnion, mem_setOf_eq]

variable (F B IB)

/-- For `B` a manifold and `F` a normed space, the groupoid on `B × F` consisting of local
homeomorphisms which are bi-`C^n` and fiberwise linear, and induce the identity on `B`.
When a (topological) vector bundle is `C^n`, then the composition of charts associated
to the vector bundle belong to this groupoid. -/
def contMDiffFiberwiseLinear (n : WithTop ℕ∞) : StructureGroupoid (B × F) where
  members :=
    ⋃ (φ : B → F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U)
      (hφ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => φ x : B → F →L[𝕜] F) U)
      (h2φ : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => (φ x).symm : B → F →L[𝕜] F) U),
        {e | e.EqOnSource
          (FiberwiseLinear.openPartialHomeomorph φ hU hφ.continuousOn h2φ.continuousOn)}
  trans' := by
    simp only [mem_aux]
    rintro e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ ⟨φ', U', hU', hφ', h2φ', heφ'⟩
    refine ⟨fun b => (φ b).trans (φ' b), _, hU.inter hU', ?_, ?_,
      Setoid.trans (OpenPartialHomeomorph.EqOnSource.trans' heφ heφ') ⟨?_, ?_⟩⟩
    · change
        ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n
          (fun x : B => (φ' x).toContinuousLinearMap ∘L (φ x).toContinuousLinearMap) (U ∩ U')
      exact (hφ'.mono inter_subset_right).clm_comp (hφ.mono inter_subset_left)
    · change
        ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n
          (fun x : B => (φ x).symm.toContinuousLinearMap ∘L (φ' x).symm.toContinuousLinearMap)
          (U ∩ U')
      exact (h2φ.mono inter_subset_left).clm_comp (h2φ'.mono inter_subset_right)
    · apply FiberwiseLinear.source_trans_openPartialHomeomorph
    · rintro ⟨b, v⟩ -; apply FiberwiseLinear.trans_openPartialHomeomorph_apply
  symm' e := by
    simp only [mem_aux]
    rintro ⟨φ, U, hU, hφ, h2φ, heφ⟩
    refine ⟨fun b => (φ b).symm, U, hU, h2φ, ?_, OpenPartialHomeomorph.EqOnSource.symm' heφ⟩
    simp_rw [ContinuousLinearEquiv.symm_symm]
    exact hφ
  id_mem' := by
    simp_rw [mem_aux]
    refine ⟨fun _ ↦ ContinuousLinearEquiv.refl 𝕜 F, univ, isOpen_univ, contMDiffOn_const,
      contMDiffOn_const, ⟨?_, fun b _hb ↦ rfl⟩⟩
    simp only [FiberwiseLinear.openPartialHomeomorph, OpenPartialHomeomorph.refl_partialEquiv,
      PartialEquiv.refl_source, univ_prod_univ]
  locality' := by
    -- the hard work has been extracted to `locality_aux₁` and `locality_aux₂`
    simp only [mem_aux]
    intro e he
    obtain ⟨U, hU, h⟩ := ContMDiffFiberwiseLinear.locality_aux₁ n e he
    exact ContMDiffFiberwiseLinear.locality_aux₂ n e U hU h
  mem_of_eqOnSource' := by
    simp only [mem_aux]
    rintro e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ hee'
    exact ⟨φ, U, hU, hφ, h2φ, Setoid.trans hee' heφ⟩

@[simp]
theorem mem_contMDiffFiberwiseLinear_iff {n : WithTop ℕ∞}
    (e : OpenPartialHomeomorph (B × F) (B × F)) :
    e ∈ contMDiffFiberwiseLinear B F IB n ↔
      ∃ (φ : B → F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U) (hφ :
        ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => φ x : B → F →L[𝕜] F) U) (h2φ :
        ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x => (φ x).symm : B → F →L[𝕜] F) U),
        e.EqOnSource
        (FiberwiseLinear.openPartialHomeomorph φ hU hφ.continuousOn h2φ.continuousOn) :=
  mem_aux
