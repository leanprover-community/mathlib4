/-
Copyright (c) 2025 Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz,
Juan José Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz, Juan José Madrigal
-/
module

public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# Quotients of manifolds

This file contains results about quotients of manifolds by group actions.

## Main results

* `MulAction.instChartedSpaceQuotient`: a choice of charted space structure on the quotient of a
  charted space by a free, properly-discontinuous group action.

## TODO

* if `G` acts smoothly, the quotient is an `IsManifold I n` for a suitable `ModelWithCorners I`.
* if `G` acts smoothly, the projection map is smooth

## tags
smooth manifold, smooth action, quotient manifold
-/

public noncomputable section

namespace MulAction

variable {M : Type*} [TopologicalSpace M]
  {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H M]

/-!
## Charted space structure on quotient by a group
-/

/-- The induced charted space structure on the quotient of a charted space by a free, properly
discontinuous group action. -/
@[expose, to_additive]
instance instChartedSpaceQuotient : ChartedSpace H (orbitRel.Quotient G M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    |>.isLocalHomeomorph.chartedSpace Quotient.mk_surjective

-- maybe we should change the ChartedSpace instance to this
--(so we can use x.out and delete the right inverse choice)
instance instChartedSpaceQuotient' : ChartedSpace H (orbitRel.Quotient G M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    |>.isLocalHomeomorph.chartedSpaceOfRightInverse Quotient.out_eq






variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (I : ModelWithCorners 𝕜 E H)
  {n : ℕ∞} [IsManifold I n M]

omit [T2Space M] [LocallyCompactSpace M] in
lemma mem_contDiffGroupoid_of_contMDiff_chartAt {x y : M} {h : OpenPartialHomeomorph M M}
    (hh : ContMDiff I I n h) (hhsymm : ContMDiff I I n h.symm) :
    (chartAt H x).symm.trans (h.trans (chartAt H y)) ∈ (contDiffGroupoid (↑n) I) := by
  refine mem_groupoid_of_pregroupoid.mpr ⟨?_, ?_⟩
  · refine ((contMDiff_iff.mp hh).2 x y).mono (fun v hv ↦ ?_)
    simpa using ⟨⟨hv.2, hv.1.1⟩, hv.1.2.2⟩
  · refine ((contMDiff_iff.mp hhsymm).2 y x).mono (fun v hv ↦ ?_)
    simpa using ⟨⟨hv.2, hv.1.1.1⟩, hv.1.2⟩

open Set

lemma quotient_IsLocalHomeomorph : IsLocalHomeomorph (Quotient.mk (orbitRel G M)) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap.isLocalHomeomorph

variable (x y : orbitRel.Quotient G M)

abbrev φ : OpenPartialHomeomorph M H := chartAt H x.out

abbrev πinv : OpenPartialHomeomorph (orbitRel.Quotient G M) M :=
  quotient_IsLocalHomeomorph.localInverseAt (Y := orbitRel.Quotient G M) x.out

section

variable {x} in
/-- If `g • m` is in the target of `πinv x`, then `πinv x ⟦m⟧` is just `g • m`. -/
lemma πinv_mk_eq_smul {g : G} {m : M} (hm : g • m ∈ (πinv x).target) :
    πinv x ⟦m⟧ = g • m := by
  rw [← orbitRel.Quotient.quotient_smul_eq (g := g),
    ← quotient_IsLocalHomeomorph.localInverseAt_symm, (πinv x).right_inv hm]

/-- On the open set `(g • ·) ⁻¹' (πinv y).target`, the section comparison
`(πinv x).symm.trans (πinv y)` is the action of `g`. -/
lemma smul_eqOn (g : G) :
    ((g • ·) ⁻¹' (πinv y).target).EqOn ((πinv x).symm.trans (πinv y)) (g • ·) := by
  intro m hm
  simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    quotient_IsLocalHomeomorph.localInverseAt_symm] using πinv_mk_eq_smul hm

variable {x} in
/-- If `⟦m⟧` is in the target of `πinv x`, then there is some `g ∈ G` such that
`g • m` is also in the target of `πinv x`.
-/
lemma exists_smul_mem_πinv_target (m : M) (hm : (⟦m⟧ : orbitRel.Quotient G M) ∈ (πinv x).source) :
    ∃ g : G, g • m ∈ (πinv x).target := by
  obtain ⟨g, hg⟩ := orbitRel_apply.mp
    (Quotient.exact (quotient_IsLocalHomeomorph.apply_localInverseAt_of_mem hm))
  exact ⟨g, by simpa [hg] using (πinv x).map_source hm⟩

/-- Locally, the comparison of two local sections is the action of a single group element. -/
lemma locally_smul (m : M) (hm : m ∈ ((πinv x).symm.trans (πinv y)).source) :
    ∃ g : G, m ∈ (g • ·) ⁻¹' (πinv y).target ∧
      ((g • ·) ⁻¹' (πinv y).target).EqOn ((πinv x).symm.trans (πinv y)) (g • ·)  := by
  rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    quotient_IsLocalHomeomorph.localInverseAt_symm] at hm
  obtain ⟨g, hg⟩ := exists_smul_mem_πinv_target m hm.2
  exact ⟨g, hg, smul_eqOn x y g⟩


end

variable (e e' : OpenPartialHomeomorph M H)

def generalTransitionMap : OpenPartialHomeomorph H H :=
  e.symm.trans (((πinv x).symm.trans (πinv y)).trans e')

variable {x y : orbitRel.Quotient G M}

/-
locally the change of charts on the quotient is the same as the action of a single group element g
on M. -/
omit [ChartedSpace H M] in
lemma general_f_eq_φρφ
    {g : G} {u : M} (hu : u ∈ e.source)
    (hu' : g • u ∈ (πinv y).target) :
    generalTransitionMap x y e e' (e u) = e' (g • ((e.symm (e u)))) := by
  simp only [generalTransitionMap, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  rw [e.left_inv hu, quotient_IsLocalHomeomorph.localInverseAt_symm,
    ← orbitRel.Quotient.quotient_smul_eq (g:=g),
    ← quotient_IsLocalHomeomorph.localInverseAt_symm, (πinv y).right_inv hu']

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : OpenPartialHomeomorph X Y}

example (y : Y) (hy : y ∈ f.target) :
  f (f.symm y) = y := by exact OpenPartialHomeomorph.right_inv f hy

lemma aux (y : Y) (hy : y ∈ f.target) :
  ∃ x ∈ f.source, f x = y := by
  use f.symm y
  sorry

example (m : M) (g : G) :
    (πinv x).symm.trans (πinv y) m = g • m := by
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  rw [quotient_IsLocalHomeomorph.localInverseAt_symm,
  ← orbitRel.Quotient.quotient_smul_eq (g:=g),
  ← quotient_IsLocalHomeomorph.localInverseAt_symm m]

  sorry

omit [ChartedSpace H M] in
lemma general_f_eq_φρφ' {g : G} (h : H)
    (hh : h ∈ e.target) (hh' : g • e.symm h ∈ (πinv y).target) :
    generalTransitionMap x y e e' h = e' (g • ((e.symm h))) := by
  simp only [generalTransitionMap, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  rw [← e.right_inv hh, e.left_inv (e.map_target hh),
    quotient_IsLocalHomeomorph.localInverseAt_symm, ← orbitRel.Quotient.quotient_smul_eq (g:=g),
    ← quotient_IsLocalHomeomorph.localInverseAt_symm, (πinv y).right_inv hh']

example (h : H) (g : G) :
  (h ∈ e '' ((Homeomorph.smul g⁻¹) '' (πinv y).target))→ (g • e.symm h ∈ (πinv y).target) := by sorry

lemma general_eqOn {g : G} (t : Set H) :
    (e.target ∩ e '' ((Homeomorph.smul g⁻¹) '' (πinv y).target)).EqOn
    (generalTransitionMap x y e e')
    (e.symm.trans ((Homeomorph.smul g).toOpenPartialHomeomorph.trans e')) := by
  intro h ⟨hh, hh'⟩
  refine general_f_eq_φρφ' e e' h hh ?_
  simp at hh'
  obtain ⟨a, ha⟩ := hh'
  rw [← ha.2]
  rw [e.left_inv]
  simpa using ha.1
  rw [← ha.2] at hh
  apply e.map_target' at hh
  sorry



variable (s : OpenPartialHomeomorph (orbitRel.Quotient G M) M)


omit [ChartedSpace H M] in
lemma general_f_eqOn {g : G} :
    (e.source ∩ Homeomorph.smul g⁻¹ '' (πinv y).target).EqOn
    (e.trans (generalTransitionMap x y e e'))
    (e.trans (e.symm.trans ((Homeomorph.smul g).toOpenPartialHomeomorph.trans e'))) := by
  intro _ ⟨hu, ⟨_, hv⟩⟩
  simpa using general_f_eq_φρφ _ _ hu (by simpa [← hv.2] using hv.1)

omit [ChartedSpace H M] in
example {g : G} :
    (e.target ∩ e '' (Homeomorph.smul g⁻¹ '' (πinv y).target)).EqOn
    (generalTransitionMap x y e e')
    (e.symm.trans ((Homeomorph.smul g).toOpenPartialHomeomorph.trans e')) := by
  intro eu ⟨hu, hu'⟩
  --simp only [generalTransitionMap, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  have ⟨v, hv⟩ : ∃ u ∈ e.source, e u = eu := by
    use e.symm eu
    exact ⟨e.map_target' hu, e.right_inv' hu⟩
  rw [← hv.2]
  apply general_f_eq_φρφ _ _ hv.1

  rw [← hv.2] at hu'
  --simp at hu'
  obtain ⟨a, ha⟩ := hu'
  obtain ⟨⟨b, hb⟩, ha⟩ := ha

  sorry



omit [ChartedSpace H M] in
lemma general_hfg_t
    (t : Set M) (g : G)
    (ht : t ⊆ e.source)
    (is_open_t : IsOpen t)
    (ht' : Homeomorph.smul g '' t ⊆ e'.source)
    (ht'' : Homeomorph.smul g '' t ⊆ (πinv y).target) :
    ((e.symm.trans (((Homeomorph.smul g).toOpenPartialHomeomorph).trans e')).restr
      ((e '' t) ∩ (generalTransitionMap x y e e').source)).EqOnSource
      ((generalTransitionMap x y e e').restr (e '' t))
    := by
  have is_open_at := (e.isOpen_image_iff_of_subset_source ht).mpr is_open_t
  refine ⟨?_, ?_⟩
  · ext z
    refine ⟨?_, ?_⟩
    · intro ⟨_, hzt⟩
      rw [(generalTransitionMap x y e e').restr_source, is_open_at.interior_eq, inter_comm]
      simpa [(is_open_at.inter (generalTransitionMap x y e e').open_source).interior_eq] using hzt
    · intro ⟨hzf, hzt⟩
      rw [is_open_at.interior_eq] at hzt
      obtain ⟨u, hu, hz⟩ := hzt
      refine ⟨?_, ?_⟩
      · rw [← hz]
        refine ⟨e.map_source' (ht hu), ?_⟩
        suffices h : g • e.symm (e u) ∈ e'.source by simpa using h
        rw [e.left_inv (ht hu)]
        apply ht'
        simp [hu]
      · rw [(is_open_at.inter (generalTransitionMap x y e e').open_source).interior_eq]
        refine ⟨by use u;, by exact hzf⟩
  · intro z ⟨_, hz⟩
    rw [(is_open_at.inter (generalTransitionMap x y e e').open_source).interior_eq] at hz
    obtain ⟨⟨_, hut, hu⟩, _⟩ := hz
    simpa [hu] using (general_f_eq_φρφ e e' (ht hut) (ht'' (mem_image_of_mem _ hut))).symm


instance : IsManifold I n (orbitRel.Quotient G M) where
  compatible := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩

    change ((πinv x).trans (φ x)).symm.trans ((πinv y).trans (φ y)) ∈ contDiffGroupoid (↑n) I

    rw [(πinv x).trans_symm_eq_symm_trans_symm, (φ x).symm.trans_assoc, ← (πinv x).symm.trans_assoc]

    apply StructureGroupoid.locality

    intro h ⟨hh1, ⟨hh2, hh3⟩, hh4⟩

    have heq : (⟦(φ x).symm h⟧ : orbitRel.Quotient G M) =
      ⟦(πinv y) ((πinv x).symm ((φ x).symm h))⟧ := by
      rw [← quotient_IsLocalHomeomorph.localInverseAt_symm y.out,
        OpenPartialHomeomorph.left_inv _ hh3, quotient_IsLocalHomeomorph.localInverseAt_symm,
        quotient_IsLocalHomeomorph.localInverseAt_symm]

    /-
    the second rw could be
    (πinv y).left_inv (x := (πinv x).symm ((φ x).symm h)) hh3
    or
    (πinv y).left_inv (by simpa using hh3)
    neither of them feel a lot better.
    -/

    obtain ⟨g0, hg0⟩ := MulAction.orbitRel_apply.mp (Quotient.exact heq.symm)

    let Up := (πinv x).target ∩ (φ (H := H) x).source -- U H x
    let Uq := (πinv y).target ∩ (φ (H := H) y).source -- U H y
    let Up' := Up ∩ Homeomorph.smul g0⁻¹ '' Uq
    let t := φ (H:=H) x '' Up'

    have is_open_Up' : IsOpen Up' := ((πinv x).open_target.inter (φ x).open_source).inter
      ((Homeomorph.isOpen_image _).mpr ((πinv y).open_target.inter (φ y).open_source))

    have is_open_t : IsOpen t := (φ x).isOpen_image_of_subset_source is_open_Up'
      (inter_subset_left.trans inter_subset_right)

    have h_in_t : h ∈ t := by
      refine ⟨(φ x).symm h, ?_, (φ x).right_inv hh1⟩
      refine ⟨⟨hh2, (φ x).map_target hh1⟩, ?_⟩
      refine ⟨(πinv y) ((πinv x).symm ((φ x).symm h)), ?_⟩
      exact ⟨⟨(πinv y).map_source hh3, hh4⟩, (Homeomorph.smul g0).injective (by simp [hg0])⟩

    refine ⟨t, is_open_t, h_in_t, ?_⟩

    have hfg_t := general_hfg_t (x:=x) (y:=y) (φ x) (φ y) Up' g0 (fun x hx => hx.1.2) is_open_Up'
      (fun m ⟨_, ⟨_, _, hw⟩, hu2⟩ ↦ by simpa [← hu2, ← hw.2] using hw.1.2)
      (fun m ⟨_, ⟨_, _, hw⟩, hu2⟩ ↦ by simpa [← hu2, ← hw.2] using hw.1.1)

    refine (StructureGroupoid.mem_iff_of_eqOnSource hfg_t).mp ?_

    refine closedUnderRestriction' ?_ ?_
    · refine mem_contDiffGroupoid_of_contMDiff_chartAt I ?_ ?_
      · sorry
      · sorry
    · exact is_open_t.inter (generalTransitionMap x y _ _).open_source

end MulAction

end
