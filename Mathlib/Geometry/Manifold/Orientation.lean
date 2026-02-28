/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finite.Card
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Manifold orientation helpers

This file defines orientation structures for manifolds.

## Main definitions

* `Manifold.Orientable`: manifold-level orientability predicate.
* `Manifold.ManifoldOrientation`: chart-sign cocycle data for a chosen orientation.
* `Manifold.OrientedManifold`: typeclass choosing a specific manifold orientation.

## Implementation note

This is a chart-sign-cocycle model of manifold orientation. An intrinsic model via sections of
an orientation bundle attached to the top exterior power of the tangent bundle is deferred until
that bundle infrastructure is available.
-/

@[expose] public section

noncomputable section

open scoped Manifold
open Set

namespace Manifold

section Orientable

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- A fixed reference orientation on the model space. -/
noncomputable def baseOrientation : Orientation ℝ E (Fin (Module.finrank ℝ E)) :=
  (Module.finBasis ℝ E).orientation

/-- Apply a chart-sign bit to an orientation value: `0` keeps it, `1` flips it. -/
noncomputable def signedOrientation (s : ZMod 2)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    Orientation ℝ E (Fin (Module.finrank ℝ E)) :=
  if s = 0 then o else -o

omit [FiniteDimensional ℝ E] in
theorem signedOrientation_add (a b : ZMod 2)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    signedOrientation (a + b) o =
      signedOrientation a (signedOrientation b o) := by
  by_cases ha : a = 0
  · subst ha
    simp [signedOrientation]
  · have ha1 : a = 1 := by
      fin_cases a
      · contradiction
      · rfl
    subst ha1
    by_cases hb : b = 0
    · subst hb
      simp [signedOrientation]
    · have hb1 : b = 1 := by
        fin_cases b
        · contradiction
        · rfl
      subst hb1
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      simp [signedOrientation, h11]

omit [FiniteDimensional ℝ E] in
theorem signedOrientation_injective
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    Function.Injective (fun s : ZMod 2 => signedOrientation s o) := by
  intro a b h
  fin_cases a <;> fin_cases b
  · rfl
  · exfalso
    exact (Module.Ray.ne_neg_self o) (by simpa [signedOrientation] using h)
  · exfalso
    exact (Module.Ray.ne_neg_self o) (by simpa [signedOrientation] using h.symm)
  · rfl

namespace Orientation

omit [FiniteDimensional ℝ E] in
theorem map_signedOrientation (f : E ≃ₗ[ℝ] E) (s : ZMod 2)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    Orientation.map (Fin (Module.finrank ℝ E)) f (signedOrientation s o) =
      signedOrientation s (Orientation.map (Fin (Module.finrank ℝ E)) f o) := by
  fin_cases s <;> simp [signedOrientation, Orientation.map_neg]

end Orientation

/-- Data of a chosen orientation on a manifold, encoded by a chart-sign cocycle. -/
structure ManifoldOrientation (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] where
  /-- Locally constant sign data on each tangent trivialization domain. -/
  chartSign :
    ∀ x : M,
      LocallyConstant
        {z // z ∈ (trivializationAt E (TangentSpace I) x).baseSet} (ZMod 2)
  /-- Compatibility with tangent-bundle chart transitions. -/
  compatible :
    ∀ x y z
      (hz : z ∈ (trivializationAt E (TangentSpace I) x).baseSet ∩
        (trivializationAt E (TangentSpace I) y).baseSet),
      Orientation.map (Fin (Module.finrank ℝ E))
        (((trivializationAt E (TangentSpace I) x).coordChangeL ℝ
            (trivializationAt E (TangentSpace I) y) z).toLinearEquiv)
        (signedOrientation (chartSign x ⟨z, hz.1⟩) baseOrientation) =
      signedOrientation (chartSign y ⟨z, hz.2⟩) baseOrientation

@[ext]
theorem ManifoldOrientation.ext_chartSign {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] {o1 o2 : ManifoldOrientation I M}
    (h : o1.chartSign = o2.chartSign) : o1 = o2 := by
  cases o1
  cases o2
  cases h
  simp

/-- A manifold is orientable if it admits a manifold orientation. -/
abbrev Orientable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] : Prop :=
  Nonempty (ManifoldOrientation I M)

/-- Typeclass choosing a specific orientation on a manifold. -/
class OrientedManifold (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    where manifoldOrientation : ManifoldOrientation I M

/-- An oriented manifold is orientable. -/
instance (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [o : OrientedManifold I M] : Orientable I M := ⟨o.manifoldOrientation⟩

private theorem mo_eq_of_chartSign_eq
    (o1 o2 : ManifoldOrientation (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (EuclideanSpace ℝ (Fin 0)))
    (h : o1.chartSign = o2.chartSign) : o1 = o2 := by
  cases o1
  cases o2
  cases h
  simp

private theorem compatible_const_chartSign
    (s : ZMod 2) (x y z : EuclideanSpace ℝ (Fin 0)) :
    Orientation.map (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 0))))
      (((trivializationAt (EuclideanSpace ℝ (Fin 0))
        (TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))) x).coordChangeL ℝ
        (trivializationAt (EuclideanSpace ℝ (Fin 0))
        (TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))) y) z).toLinearEquiv)
      (signedOrientation s
        (baseOrientation)) =
    signedOrientation s
      (baseOrientation) := by
  have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)) = 0 := by
    exact finrank_euclideanSpace
  letI : IsEmpty (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)))) := by
    simpa [hfinrank] using (inferInstance : IsEmpty (Fin 0))
  exact Orientation.map_of_isEmpty (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 0))))
    (signedOrientation s
      (baseOrientation))
    (((trivializationAt (EuclideanSpace ℝ (Fin 0))
      (TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))) x).coordChangeL ℝ
      (trivializationAt (EuclideanSpace ℝ (Fin 0))
      (TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))) y) z).toLinearEquiv)

theorem point_has_two_manifoldOrientations :
    ∃ oPos oNeg : ManifoldOrientation (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (EuclideanSpace ℝ (Fin 0)),
      oPos ≠ oNeg ∧
      ∀ o : ManifoldOrientation (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
        (EuclideanSpace ℝ (Fin 0)), o = oPos ∨ o = oNeg := by
  let oPos : ManifoldOrientation (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (EuclideanSpace ℝ (Fin 0)) :=
    { chartSign := fun _ => LocallyConstant.const _ (0 : ZMod 2)
      compatible := by
        intro x y z hz
        simpa using compatible_const_chartSign 0 x y z }
  let oNeg : ManifoldOrientation (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (EuclideanSpace ℝ (Fin 0)) :=
    { chartSign := fun _ => LocallyConstant.const _ (1 : ZMod 2)
      compatible := by
        intro x y z hz
        simpa using compatible_const_chartSign 1 x y z }
  let x0 : EuclideanSpace ℝ (Fin 0) := default
  let z0 :
      {z // z ∈ (trivializationAt (EuclideanSpace ℝ (Fin 0))
        (TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))) x0).baseSet} :=
    ⟨x0, mem_baseSet_trivializationAt (EuclideanSpace ℝ (Fin 0))
      (TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))) x0⟩
  refine ⟨oPos, oNeg, ?_, ?_⟩
  · intro h
    have hchart : oPos.chartSign = oNeg.chartSign := congrArg ManifoldOrientation.chartSign h
    have hpt : (0 : ZMod 2) = 1 := by
      simpa [oPos, oNeg, x0, z0] using congrArg (fun f => f x0 z0) hchart
    exact Fin.zero_ne_one hpt
  · intro o
    have hval : o.chartSign x0 z0 = (0 : ZMod 2) ∨ o.chartSign x0 z0 = (1 : ZMod 2) := by
      refine Fin.cases ?_ ?_ (o.chartSign x0 z0)
      · exact Or.inl rfl
      · intro i
        fin_cases i
        exact Or.inr rfl
    rcases hval with h0 | h1
    · left
      apply mo_eq_of_chartSign_eq
      funext x
      cases Subsingleton.elim x x0
      ext z
      have hz : z = z0 := Subsingleton.elim z z0
      subst hz
      have hPos : (oPos.chartSign x0) z0 = 0 := by
        simp [oPos]
      exact h0.trans hPos.symm
    · right
      apply mo_eq_of_chartSign_eq
      funext x
      cases Subsingleton.elim x x0
      ext z
      have hz : z = z0 := Subsingleton.elim z z0
      subst hz
      have hNeg : (oNeg.chartSign x0) z0 = 1 := by
        simp [oNeg]
      exact h1.trans hNeg.symm

section Cardinality

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

def chartDelta (o₀ o : ManifoldOrientation I M) (x : M) :
    LocallyConstant {z // z ∈ (trivializationAt E (TangentSpace I) x).baseSet} (ZMod 2) :=
  o.chartSign x - o₀.chartSign x

omit [FiniteDimensional ℝ E] in
theorem sub_eq_of_signedOrientation_map_eq
    (L : E ≃ₗ[ℝ] E) (sx sy s0x s0y : ZMod 2)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (h : Orientation.map (Fin (Module.finrank ℝ E)) L (signedOrientation sx o) =
      signedOrientation sy o)
    (h0 : Orientation.map (Fin (Module.finrank ℝ E)) L (signedOrientation s0x o) =
      signedOrientation s0y o) :
    sx - s0x = sy - s0y := by
  have hsx : signedOrientation sx o =
      signedOrientation (sx - s0x) (signedOrientation s0x o) := by
    fin_cases sx <;> fin_cases s0x <;>
      (simp [signedOrientation]; try exact (neg_neg o).symm)
  have hsy : signedOrientation sy o =
      signedOrientation (sy - s0y) (signedOrientation s0y o) := by
    fin_cases sy <;> fin_cases s0y <;>
      (simp [signedOrientation]; try exact (neg_neg o).symm)
  have h1 : Orientation.map (Fin (Module.finrank ℝ E)) L
      (signedOrientation (sx - s0x) (signedOrientation s0x o)) =
      signedOrientation sy o := by
    simpa [hsx] using h
  have h2 : Orientation.map (Fin (Module.finrank ℝ E)) L
      (signedOrientation (sx - s0x) (signedOrientation s0x o)) =
      signedOrientation (sx - s0x) (signedOrientation s0y o) := by
    calc
      Orientation.map (Fin (Module.finrank ℝ E)) L
          (signedOrientation (sx - s0x) (signedOrientation s0x o))
          = signedOrientation (sx - s0x)
              (Orientation.map (Fin (Module.finrank ℝ E)) L
                (signedOrientation s0x o)) := by
            simpa using Orientation.map_signedOrientation L (sx - s0x)
              (signedOrientation s0x o)
      _ = signedOrientation (sx - s0x) (signedOrientation s0y o) := by
            simp [h0]
  have h3 : signedOrientation (sx - s0x) (signedOrientation s0y o) =
      signedOrientation (sy - s0y) (signedOrientation s0y o) := by
    exact (h2.symm.trans h1).trans (by simp [hsy])
  exact (signedOrientation_injective
    (signedOrientation s0y o)) h3

theorem chartDelta_eq_on_overlap (o₀ o : ManifoldOrientation I M)
    {x y z : M}
    (hz : z ∈ (trivializationAt E (TangentSpace I) x).baseSet ∩
      (trivializationAt E (TangentSpace I) y).baseSet) :
    chartDelta I o₀ o x ⟨z, hz.1⟩ =
      chartDelta I o₀ o y ⟨z, hz.2⟩ := by
  let L : E ≃ₗ[ℝ] E :=
    ((trivializationAt E (TangentSpace I) x).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) y) z).toLinearEquiv
  let sx : ZMod 2 := o.chartSign x ⟨z, hz.1⟩
  let sy : ZMod 2 := o.chartSign y ⟨z, hz.2⟩
  let s0x : ZMod 2 := o₀.chartSign x ⟨z, hz.1⟩
  let s0y : ZMod 2 := o₀.chartSign y ⟨z, hz.2⟩
  have h : Orientation.map (Fin (Module.finrank ℝ E)) L
      (signedOrientation sx (baseOrientation)) =
      signedOrientation sy (baseOrientation) := by
    simpa [L, sx, sy] using o.compatible x y z hz
  have h0 : Orientation.map (Fin (Module.finrank ℝ E)) L
      (signedOrientation s0x (baseOrientation)) =
      signedOrientation s0y (baseOrientation) := by
    simpa [L, s0x, s0y] using o₀.compatible x y z hz
  exact sub_eq_of_signedOrientation_map_eq L sx sy s0x s0y (baseOrientation)
    h h0

def deltaFn (o₀ o : ManifoldOrientation I M) (z : M) : ZMod 2 :=
  chartDelta I o₀ o z ⟨z, mem_baseSet_trivializationAt E (TangentSpace I) z⟩

theorem deltaFn_eq_chartDelta (o₀ o : ManifoldOrientation I M)
    {x z : M} (hz : z ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    deltaFn I o₀ o z = chartDelta I o₀ o x ⟨z, hz⟩ := by
  simpa [deltaFn] using
    (show chartDelta I o₀ o z ⟨z, mem_baseSet_trivializationAt E (TangentSpace I) z⟩ =
        chartDelta I o₀ o x ⟨z, hz⟩ from
      chartDelta_eq_on_overlap I o₀ o
        ⟨mem_baseSet_trivializationAt E (TangentSpace I) z, hz⟩)

theorem deltaFn_isLocallyConstant (o₀ o : ManifoldOrientation I M) :
    IsLocallyConstant (deltaFn I o₀ o) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  let xSub : {z // z ∈ (trivializationAt E (TangentSpace I) x).baseSet} :=
    ⟨x, mem_baseSet_trivializationAt E (TangentSpace I) x⟩
  obtain ⟨Vsub, hVopen, hxV, hVconst⟩ :=
    (chartDelta I o₀ o x).isLocallyConstant.exists_open xSub
  let V : Set M := ((↑) : {z // z ∈ (trivializationAt E (TangentSpace I) x).baseSet} → M) '' Vsub
  refine ⟨V, ?_, ?_, ?_⟩
  · exact
      ((trivializationAt E (TangentSpace I) x).open_baseSet.isOpenMap_subtype_val _ hVopen)
  · exact ⟨xSub, hxV, rfl⟩
  · intro z hzV
    rcases hzV with ⟨zSub, hzSubV, rfl⟩
    have hzBase : (zSub : M) ∈ (trivializationAt E (TangentSpace I) x).baseSet := zSub.2
    calc
      deltaFn I o₀ o zSub
          = chartDelta I o₀ o x ⟨zSub, hzBase⟩ :=
              deltaFn_eq_chartDelta I o₀ o hzBase
      _ = chartDelta I o₀ o x xSub := hVconst zSub hzSubV
      _ = deltaFn I o₀ o x := by
            symm
            simpa [xSub] using
              deltaFn_eq_chartDelta I o₀ o
                (mem_baseSet_trivializationAt E (TangentSpace I) x)

def deltaLC (o₀ o : ManifoldOrientation I M) : LocallyConstant M (ZMod 2) :=
  ⟨deltaFn I o₀ o, deltaFn_isLocallyConstant I o₀ o⟩

def twist (o₀ : ManifoldOrientation I M) (δ : LocallyConstant M (ZMod 2)) :
    ManifoldOrientation I M where
  chartSign x :=
    δ.comap ⟨((↑) : {z // z ∈ (trivializationAt E (TangentSpace I) x).baseSet} → M),
      continuous_subtype_val⟩ + o₀.chartSign x
  compatible := by
    intro x y z hz
    let L : E ≃ₗ[ℝ] E :=
      ((trivializationAt E (TangentSpace I) x).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) y) z).toLinearEquiv
    have hcompat0 : Orientation.map (Fin (Module.finrank ℝ E)) L
        (signedOrientation (o₀.chartSign x ⟨z, hz.1⟩) (baseOrientation)) =
        signedOrientation (o₀.chartSign y ⟨z, hz.2⟩) (baseOrientation) := by
      simpa [L] using o₀.compatible x y z hz
    calc
      Orientation.map (Fin (Module.finrank ℝ E)) L
          (signedOrientation
            (((δ.comap ⟨((↑) : {z // z ∈ (trivializationAt E (TangentSpace I) x).baseSet} → M),
              continuous_subtype_val⟩) ⟨z, hz.1⟩) + o₀.chartSign x ⟨z, hz.1⟩)
            (baseOrientation))
          =
        Orientation.map (Fin (Module.finrank ℝ E)) L
          (signedOrientation ((δ.comap ⟨((↑) : {z // z ∈
            (trivializationAt E (TangentSpace I) x).baseSet} → M),
            continuous_subtype_val⟩) ⟨z, hz.1⟩)
            (signedOrientation (o₀.chartSign x ⟨z, hz.1⟩) (baseOrientation))) := by
            simp [signedOrientation_add]
      _ =
        signedOrientation ((δ.comap ⟨((↑) : {z // z ∈
          (trivializationAt E (TangentSpace I) x).baseSet} → M),
          continuous_subtype_val⟩) ⟨z, hz.1⟩)
          (Orientation.map (Fin (Module.finrank ℝ E)) L
            (signedOrientation (o₀.chartSign x ⟨z, hz.1⟩) (baseOrientation))) := by
          simpa using Orientation.map_signedOrientation L
            ((δ.comap ⟨((↑) : {z // z ∈ (trivializationAt E (TangentSpace I) x).baseSet} → M),
              continuous_subtype_val⟩) ⟨z, hz.1⟩)
            (signedOrientation (o₀.chartSign x ⟨z, hz.1⟩) (baseOrientation))
      _ =
        signedOrientation ((δ.comap ⟨((↑) : {z // z ∈
          (trivializationAt E (TangentSpace I) x).baseSet} → M),
          continuous_subtype_val⟩) ⟨z, hz.1⟩)
          (signedOrientation (o₀.chartSign y ⟨z, hz.2⟩) (baseOrientation)) := by
          exact congrArg (signedOrientation (δ z)) hcompat0
      _ = signedOrientation
          (((δ.comap ⟨((↑) : {z // z ∈ (trivializationAt E (TangentSpace I) y).baseSet} → M),
              continuous_subtype_val⟩) ⟨z, hz.2⟩) + o₀.chartSign y ⟨z, hz.2⟩)
          (baseOrientation) := by
          simp [signedOrientation_add]

noncomputable def manifoldOrientationEquivLocallyConstant (o₀ : ManifoldOrientation I M) :
    ManifoldOrientation I M ≃ LocallyConstant M (ZMod 2) where
  toFun o := deltaLC I o₀ o
  invFun δ := twist I o₀ δ
  left_inv o := by
    ext x z
    change
      (deltaLC I o₀ o) z.1 + o₀.chartSign x z = o.chartSign x z
    change deltaFn I o₀ o z.1 + o₀.chartSign x z = o.chartSign x z
    rw [deltaFn_eq_chartDelta I o₀ o z.2]
    change (o.chartSign x z - o₀.chartSign x z) + o₀.chartSign x z = o.chartSign x z
    calc
      (o.chartSign x z - o₀.chartSign x z) + o₀.chartSign x z
          = (-(o₀.chartSign x z)) + ((o₀.chartSign x z) + o.chartSign x z) := by
              simp [sub_eq_add_neg, add_comm]
      _ = o.chartSign x z := by
            simpa [ZMod.neg_eq_self_mod_two, add_assoc] using
              (neg_add_cancel_left (o₀.chartSign x z) (o.chartSign x z))
  right_inv δ := by
    ext z
    simp [deltaLC, deltaFn, chartDelta, twist]

noncomputable def locallyConstantEquivConnectedComponents [LocallyConnectedSpace M] :
    LocallyConstant M (ZMod 2) ≃ (ConnectedComponents M → ZMod 2) where
  toFun f := Quotient.lift (fun x : M => f x) (by
    intro x y hxy
    have hyx : y ∈ connectedComponent x := by
      simpa [hxy.symm] using (mem_connectedComponent : y ∈ connectedComponent y)
    exact f.apply_eq_of_isPreconnected isConnected_connectedComponent.isPreconnected
      mem_connectedComponent hyx)
  invFun g :=
    ⟨fun x => g x,
      IsLocallyConstant.of_constant_on_connected_components (fun x y hy => by
        exact congrArg g (ConnectedComponents.coe_eq_coe'.2 hy))⟩
  left_inv f := by
    ext x
    rfl
  right_inv g := by
    funext c
    rcases ConnectedComponents.surjective_coe c with ⟨x, rfl⟩
    rfl

theorem natCard_manifoldOrientation_eq_two_pow_of_natCard_connectedComponents_eq
    [LocallyConnectedSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [Orientable I M]
    [Finite (ConnectedComponents M)] {n : ℕ}
    (hn : Nat.card (ConnectedComponents M) = n) :
    Nat.card (ManifoldOrientation I M) = 2 ^ n := by
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  classical
  let o₀ : ManifoldOrientation I M :=
    Classical.choice (show Nonempty (ManifoldOrientation I M) from ‹Orientable I M›)
  calc
    Nat.card (ManifoldOrientation I M)
        = Nat.card (LocallyConstant M (ZMod 2)) :=
          Nat.card_congr (manifoldOrientationEquivLocallyConstant I o₀)
    _ = Nat.card (ConnectedComponents M → ZMod 2) :=
          Nat.card_congr (locallyConstantEquivConnectedComponents)
    _ = Nat.card (ZMod 2) ^ Nat.card (ConnectedComponents M) := by
          simpa using (Nat.card_fun (α := ConnectedComponents M) (β := ZMod 2))
    _ = 2 ^ n := by simp [hn]

end Cardinality

end Orientable

end Manifold
