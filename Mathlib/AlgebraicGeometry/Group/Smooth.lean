/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.EtaleDescent
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Smoothness of group schemes

## Main results
- `AlgebraicGeometry.smooth_of_grpObj`:
  If `G` is a group scheme over a field `k` that is geometrically reduced and locally
  of finite type, then `G` is smooth over `k`.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {G : Scheme} (f : G ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [GrpObj (Over.mk f)]

set_option backward.isDefEq.respectTransparency false in
open MonObj MonoidalCategory CartesianMonoidalCategory in
/--
If `G` is a group scheme over an algebraically closed field `k` that is reduced and locally
of finite type, then `G` is smooth over `k`.
-/
private lemma smooth_of_grpObj_of_isAlgClosed [IsReduced G] [IsAlgClosed K] : Smooth f := by
  have := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty G := ⟨η[Over.mk f].1 (IsLocalRing.closedPoint _)⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints H f.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy : y ∈ f.smoothLocus, hyc⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.2.isLocallyClosed
  let x' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨x, hxc⟩).2
  let y' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨y, hyc⟩).2
  let α := (GrpObj.mulRight (A := Over.mk f) x').symm ≪≫
    (GrpObj.mulRight (A := Over.mk f) y')
  have hα : x' ≫ α.hom = y' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have hα' : α.hom.left x = y := by
    simpa [x', y', pointEquivClosedPoint] using congr(($hα).left (IsLocalRing.closedPoint K))
  rw! [← hα', ← α.hom.left.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    show α.hom.left ≫ f = f from α.hom.w] at hy
  exact hx hy

lemma smooth_of_grpObj [GeometricallyReduced f] : Smooth f := by
  let Ω : Type u := AlgebraicClosure K
  let g : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom <| algebraMap K Ω)
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := g)
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · let : GrpObj (Over.mk (Limits.pullback.snd f g)) := Over.grpObjMkPullbackSnd
    exact smooth_of_grpObj_of_isAlgClosed _

end AlgebraicGeometry
