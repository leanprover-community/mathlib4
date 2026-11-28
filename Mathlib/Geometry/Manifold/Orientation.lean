/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Orientations of manifolds

This file defines orientation structures for manifolds.

## Main definitions

* `Manifold.Orientable`: manifold-level orientability predicate.
* `Manifold.OrientationLift`: orientation data relative to an orientation of the model space.
* `Manifold.Orientation`: the quotient of orientation lifts by simultaneous reversal of the model
  orientation and every chart sign.
* `Manifold.OrientedManifold`: typeclass choosing a specific manifold orientation.

## Implementation note

An orientation lift consists of an orientation of the model vector space and a locally constant
`ℤˣ`-valued sign for each preferred chart. On chart overlaps, the tangent coordinate change must
carry the signed model orientation in the first chart to the signed model orientation in the
second. The determinant criterion is a consequence of this transport condition.

Changing the model orientation and every chart sign by the same element of `ℤˣ` does not change
the induced tangent-space orientations. A manifold orientation is therefore the orbit quotient of
orientation lifts by this diagonal action.
-/

@[expose] public section

noncomputable section

namespace Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- The homomorphism which regards a unit of `ℤ` as a unit of `ℝ`. -/
def intUnitsToRealUnits : ℤˣ →* ℝˣ :=
  Units.map (Int.castRingHom ℝ).toMonoidHom

/-- Multiply a linear orientation by a sign. -/
def signedOrientation {ι : Type*} (ε : ℤˣ) (ω : _root_.Orientation ℝ E ι) :
    _root_.Orientation ℝ E ι :=
  intUnitsToRealUnits ε • ω

@[simp]
theorem signedOrientation_one {ι : Type*} (ω : _root_.Orientation ℝ E ι) :
    signedOrientation 1 ω = ω := by
  simp [signedOrientation, intUnitsToRealUnits]

@[simp]
theorem signedOrientation_neg_one {ι : Type*} (ω : _root_.Orientation ℝ E ι) :
    signedOrientation (-1) ω = -ω := by
  simp [signedOrientation, intUnitsToRealUnits]

theorem signedOrientation_mul {ι : Type*} (ε η : ℤˣ) (ω : _root_.Orientation ℝ E ι) :
    signedOrientation ε (signedOrientation η ω) = signedOrientation (ε * η) ω := by
  simp [signedOrientation, intUnitsToRealUnits, mul_smul]

/-- Multiplying both a model orientation and its sign by the same integer unit leaves the signed
orientation unchanged. -/
theorem signedOrientation_diagonal {ι : Type*} (ε η : ℤˣ)
    (ω : _root_.Orientation ℝ E ι) :
    signedOrientation (ε * η) (signedOrientation ε ω) = signedOrientation η ω := by
  rw [signedOrientation_mul]
  congr 1
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [mul_comm]

/-- Distinct integer units give distinct signed orientations. -/
theorem signedOrientation_injective {ι : Type*} (ω : _root_.Orientation ℝ E ι) :
    Function.Injective (fun ε : ℤˣ ↦ signedOrientation ε ω) := by
  intro ε η h
  rcases Int.units_eq_one_or ε with rfl | rfl <;>
    rcases Int.units_eq_one_or η with rfl | rfl
  all_goals simp only [signedOrientation_one, signedOrientation_neg_one] at h ⊢
  all_goals first
    | rfl
    | exact (Module.Ray.ne_neg_self ω h).elim
    | exact (Module.Ray.ne_neg_self ω h.symm).elim

theorem map_signedOrientation {ι : Type*} (ε : ℤˣ) (e : E ≃ₗ[ℝ] E)
    (ω : _root_.Orientation ℝ E ι) :
    _root_.Orientation.map ι e (signedOrientation ε ω) =
      signedOrientation ε (_root_.Orientation.map ι e ω) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp
  · simp only [signedOrientation_neg_one]
    exact _root_.Orientation.map_neg e ω

/-- A lift of a manifold orientation relative to an orientation of the model vector space. -/
@[ext]
structure OrientationLift (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [FiniteDimensional ℝ E] (ι : Type*) [Fintype ι]
    [Fact (Fintype.card ι = Module.finrank ℝ E)] where
  /-- The chosen orientation of the model vector space. -/
  modelOrientation : _root_.Orientation ℝ E ι
  /-- The sign of the chart at `x`, evaluated at each point; only meaningful on
  `(chartAt H x).source`. -/
  chartSign : M → M → ℤˣ
  /-- Each chart sign is continuous on its chart domain. -/
  continuousOn_chartSign : ∀ x, ContinuousOn (chartSign x) (chartAt H x).source
  /-- The chart sign is normalized to `1` outside the chart domain. -/
  chartSign_eq_one_of_notMem : ∀ x z, z ∉ (chartAt H x).source → chartSign x z = 1
  /-- Coordinate changes transport the signed model orientation in one chart to that in the
  other chart. -/
  compatible : ∀ x y z, z ∈ (chartAt H x).source → z ∈ (chartAt H y).source →
    _root_.Orientation.map ι (tangentCoordChangeEquiv I x y z)
        (signedOrientation (chartSign x z) modelOrientation) =
      signedOrientation (chartSign y z) modelOrientation

variable {I} {ι : Type*} [Fintype ι] [FiniteDimensional ℝ E]
  [Fact (Fintype.card ι = Module.finrank ℝ E)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The sign taking one linear orientation to another. -/
noncomputable def orientationSign (ω₀ ω : _root_.Orientation ℝ E ι) : ℤˣ := by
  classical
  exact if ω = ω₀ then 1 else -1

omit [Fintype ι] [FiniteDimensional ℝ E]
  [Fact (Fintype.card ι = Module.finrank ℝ E)] in
@[simp]
theorem orientationSign_self (ω : _root_.Orientation ℝ E ι) : orientationSign ω ω = 1 := by
  simp [orientationSign]

/-- Applying the relative sign to the first orientation gives the second orientation. -/
theorem signedOrientation_orientationSign (ω₀ ω : _root_.Orientation ℝ E ι) :
    signedOrientation (orientationSign ω₀ ω) ω₀ = ω := by
  classical
  by_cases h : ω = ω₀
  · simp [orientationSign, h]
  · have hneg : ω = -ω₀ :=
      (_root_.Orientation.ne_iff_eq_neg ω ω₀ Fact.out).mp h
    rw [hneg, orientationSign, if_neg (Module.Ray.ne_neg_self ω₀).symm]
    simp

/-- The relative sign after independently changing the signs of its two arguments. -/
theorem orientationSign_signed (ε η : ℤˣ) (ω₀ ω : _root_.Orientation ℝ E ι) :
    orientationSign (signedOrientation ε ω₀) (signedOrientation η ω) =
      η * ε * orientationSign ω₀ ω := by
  apply signedOrientation_injective (signedOrientation ε ω₀)
  change signedOrientation
      (orientationSign (signedOrientation ε ω₀) (signedOrientation η ω))
      (signedOrientation ε ω₀) =
    signedOrientation (η * ε * orientationSign ω₀ ω) (signedOrientation ε ω₀)
  rw [signedOrientation_orientationSign, signedOrientation_mul]
  let r := orientationSign ω₀ ω
  have hr : signedOrientation r ω₀ = ω := signedOrientation_orientationSign ω₀ ω
  calc
    signedOrientation η ω = signedOrientation η (signedOrientation r ω₀) :=
      congrArg (signedOrientation η) hr.symm
    _ = signedOrientation (η * r) ω₀ := signedOrientation_mul η r ω₀
    _ = signedOrientation ((η * ε * r) * ε) ω₀ := by
      congr 1
      rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [mul_comm]

namespace OrientationLift

/-- The orientation represented by a lift in the coordinates of the chart at `x`. -/
def orientationInChart (o : OrientationLift I M ι) (x z : M) : _root_.Orientation ℝ E ι :=
  signedOrientation (o.chartSign x z) o.modelOrientation

/-- The old determinant/sign compatibility condition follows from transport of orientations. -/
theorem compatible_det (o : OrientationLift I M ι) {x y z : M}
    (hx : z ∈ (chartAt H x).source) (hy : z ∈ (chartAt H y).source) :
    0 < LinearMap.det (tangentCoordChange I x y z).toLinearMap ↔
      o.chartSign x z = o.chartSign y z := by
  rw [← tangentCoordChangeEquiv_toLinearMap hx hy,
    ← _root_.Orientation.map_eq_iff_det_pos
      (signedOrientation (o.chartSign x z) o.modelOrientation)
      (tangentCoordChangeEquiv I x y z) Fact.out,
    o.compatible x y z hx hy]
  constructor
  · exact fun h ↦ (signedOrientation_injective o.modelOrientation h).symm
  · intro h
    rw [h]

/-- Build orientation transport from the determinant/sign criterion. This is useful for migrating
constructions expressed using the former definition of manifold orientation. -/
theorem compatible_of_det (ω : _root_.Orientation ℝ E ι) (ε η : ℤˣ) (e : E ≃ₗ[ℝ] E)
    (h : 0 < LinearMap.det (e : E →ₗ[ℝ] E) ↔ ε = η) :
    _root_.Orientation.map ι e (signedOrientation ε ω) = signedOrientation η ω := by
  by_cases hεη : ε = η
  · subst η
    exact (_root_.Orientation.map_eq_iff_det_pos
      (signedOrientation ε ω) e Fact.out).2 (h.mpr rfl)
  · rw [show signedOrientation η ω = -signedOrientation ε ω by
      rcases Int.units_eq_one_or ε with rfl | rfl <;>
        rcases Int.units_eq_one_or η with rfl | rfl
      all_goals simp only [signedOrientation_one, signedOrientation_neg_one] at hεη ⊢
      all_goals first | contradiction | rfl | exact (neg_neg ω).symm,
      _root_.Orientation.map_eq_neg_iff_det_neg _ _ Fact.out]
    exact lt_of_le_of_ne (not_lt.mp fun hp ↦ hεη (h.mp hp)) <| by
      rw [← LinearEquiv.coe_det]
      exact Units.ne_zero _

private theorem chartSign_mul_chartSign_eq (o₀ o : OrientationLift I M ι) {x z : M}
    (hz : z ∈ (chartAt H x).source) :
    o.chartSign z z * o₀.chartSign z z = o.chartSign x z * o₀.chartSign x z :=
  (by decide : ∀ a b c d : ℤˣ, (a = b ↔ c = d) → a * c = b * d) _ _ _ _
    ((o.compatible_det (mem_chart_source H z) hz).symm.trans
      (o₀.compatible_det (mem_chart_source H z) hz))

/-- The orientation represented by a lift at a point. -/
def orientationAt (o : OrientationLift I M ι) (z : M) : _root_.Orientation ℝ E ι :=
  o.orientationInChart z z

/-- Simultaneously change the model orientation and all chart signs. -/
def diagonalSMul (ε : ℤˣ) (o : OrientationLift I M ι) : OrientationLift I M ι where
  modelOrientation := signedOrientation ε o.modelOrientation
  chartSign x z := open scoped Classical in
    if z ∈ (chartAt H x).source then ε * o.chartSign x z else 1
  continuousOn_chartSign x :=
    ((continuousOn_const (c := ε)).mul (o.continuousOn_chartSign x)).congr
      fun z hz ↦ by simp [hz]
  chartSign_eq_one_of_notMem x z hz := if_neg hz
  compatible x y z hx hy := by
    simp only [if_pos hx, if_pos hy]
    rw [signedOrientation_diagonal, signedOrientation_diagonal]
    exact o.compatible x y z hx hy

instance instSMul : SMul ℤˣ (OrientationLift I M ι) := ⟨diagonalSMul⟩

@[simp]
theorem smul_modelOrientation (ε : ℤˣ) (o : OrientationLift I M ι) :
    (ε • o).modelOrientation = signedOrientation ε o.modelOrientation := rfl

open scoped Classical in
/-- The chart sign of a diagonally rescaled orientation lift. -/
theorem smul_chartSign (ε : ℤˣ) (o : OrientationLift I M ι) (x z : M) :
    (ε • o).chartSign x z =
      if z ∈ (chartAt H x).source then ε * o.chartSign x z else 1 := rfl

@[simp]
theorem smul_chartSign_of_mem (ε : ℤˣ) (o : OrientationLift I M ι) {x z : M}
    (hz : z ∈ (chartAt H x).source) :
    (ε • o).chartSign x z = ε * o.chartSign x z := by
  rw [smul_chartSign, if_pos hz]

instance : MulAction ℤˣ (OrientationLift I M ι) where
  one_smul o := by
    apply OrientationLift.ext
    · rw [smul_modelOrientation, signedOrientation_one]
    · funext x z
      by_cases hz : z ∈ (chartAt H x).source
      · rw [smul_chartSign_of_mem 1 o hz, one_mul]
      · rw [(1 • o).chartSign_eq_one_of_notMem x z hz,
          o.chartSign_eq_one_of_notMem x z hz]
  mul_smul ε η o := by
    apply OrientationLift.ext
    · rw [smul_modelOrientation, smul_modelOrientation, smul_modelOrientation,
        signedOrientation_mul]
    · funext x z
      by_cases hz : z ∈ (chartAt H x).source
      · rw [smul_chartSign_of_mem (ε * η) o hz,
          smul_chartSign_of_mem ε (η • o) hz, smul_chartSign_of_mem η o hz, mul_assoc]
      · rw [((ε * η) • o).chartSign_eq_one_of_notMem x z hz,
          (ε • η • o).chartSign_eq_one_of_notMem x z hz]

@[simp]
theorem orientationAt_smul (ε : ℤˣ) (o : OrientationLift I M ι) (z : M) :
    (ε • o).orientationAt z = o.orientationAt z := by
  rw [orientationAt, orientationInChart, smul_modelOrientation,
    smul_chartSign_of_mem ε o (mem_chart_source H z)]
  exact signedOrientation_diagonal ε (o.chartSign z z) o.modelOrientation

/-- The sign difference between two orientation lifts. -/
def deltaLC (o₀ o : OrientationLift I M ι) : LocallyConstant M ℤˣ :=
  ⟨fun z ↦ orientationSign o₀.modelOrientation o.modelOrientation *
      (o.chartSign z z * o₀.chartSign z z), by
    rw [IsLocallyConstant.iff_continuous, continuous_iff_continuousAt]
    intro p
    refine ContinuousOn.continuousAt ?_
      ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
    exact ((continuousOn_const (c := orientationSign o₀.modelOrientation o.modelOrientation)).mul
      ((o.continuousOn_chartSign p).mul (o₀.continuousOn_chartSign p))).congr
        (fun z hz ↦ congrArg _ (chartSign_mul_chartSign_eq o₀ o hz))⟩

@[simp]
theorem deltaLC_apply (o₀ o : OrientationLift I M ι) (z : M) :
    deltaLC o₀ o z = orientationSign o₀.modelOrientation o.modelOrientation *
      (o.chartSign z z * o₀.chartSign z z) := rfl

/-- The sign difference can be computed in any chart containing the point. -/
theorem deltaLC_eq (o₀ o : OrientationLift I M ι) {x z : M}
    (hz : z ∈ (chartAt H x).source) :
    deltaLC o₀ o z = orientationSign o₀.modelOrientation o.modelOrientation *
      (o.chartSign x z * o₀.chartSign x z) := by
  rw [deltaLC_apply, chartSign_mul_chartSign_eq o₀ o hz]

@[simp]
theorem deltaLC_smul (ε η : ℤˣ) (o₀ o : OrientationLift I M ι) :
    deltaLC (ε • o₀) (η • o) = deltaLC o₀ o := by
  ext z
  rw [deltaLC_apply, deltaLC_apply, smul_modelOrientation, smul_modelOrientation,
    smul_chartSign_of_mem η o (mem_chart_source H z),
    smul_chartSign_of_mem ε o₀ (mem_chart_source H z), orientationSign_signed]
  rcases Int.units_eq_one_or ε with rfl | rfl <;>
    rcases Int.units_eq_one_or η with rfl | rfl <;>
      simp [mul_comm]

/-- Twist an orientation lift by a locally constant sign. -/
def twist (o : OrientationLift I M ι) (δ : LocallyConstant M ℤˣ) : OrientationLift I M ι where
  modelOrientation := o.modelOrientation
  chartSign x z := open scoped Classical in
    if z ∈ (chartAt H x).source then δ z * o.chartSign x z else 1
  continuousOn_chartSign x :=
    (δ.continuous.continuousOn.mul (o.continuousOn_chartSign x)).congr
      (fun z hz ↦ by simp [hz])
  chartSign_eq_one_of_notMem x z hz := if_neg hz
  compatible x y z hx hy := by
    simp only [if_pos hx, if_pos hy]
    rw [← signedOrientation_mul, ← signedOrientation_mul, map_signedOrientation,
      o.compatible x y z hx hy]

@[simp]
theorem twist_chartSign (o : OrientationLift I M ι) (δ : LocallyConstant M ℤˣ) {x z : M}
    (hz : z ∈ (chartAt H x).source) :
    (o.twist δ).chartSign x z = δ z * o.chartSign x z := by
  simp [twist, hz]

@[simp]
theorem orientationAt_twist (o : OrientationLift I M ι) (δ : LocallyConstant M ℤˣ) (z : M) :
    (o.twist δ).orientationAt z = signedOrientation (δ z) (o.orientationAt z) := by
  rw [orientationAt, orientationInChart, twist_chartSign _ _ (mem_chart_source H z),
    orientationAt, orientationInChart]
  exact (signedOrientation_mul (δ z) (o.chartSign z z) o.modelOrientation).symm

theorem twist_smul (ε : ℤˣ) (o : OrientationLift I M ι) (δ : LocallyConstant M ℤˣ) :
    (ε • o).twist δ = ε • o.twist δ := by
  classical
  apply OrientationLift.ext
  · rfl
  · funext x z
    by_cases hz : z ∈ (chartAt H x).source
    · rw [twist_chartSign _ _ hz, smul_chartSign_of_mem ε (o.twist δ) hz,
        smul_chartSign_of_mem _ _ hz, twist_chartSign _ _ hz]
      simp [mul_assoc, mul_comm]
    · rw [((ε • o).twist δ).chartSign_eq_one_of_notMem x z hz,
        (ε • o.twist δ).chartSign_eq_one_of_notMem x z hz]

/-- Lift-level `deltaLC` agrees with the intrinsic relative sign at a point. -/
theorem deltaLC_eq_orientationSign (o₀ o : OrientationLift I M ι) (z : M) :
    deltaLC o₀ o z = orientationSign (o₀.orientationAt z) (o.orientationAt z) := by
  rw [deltaLC_apply, orientationAt, orientationAt, orientationInChart, orientationInChart,
    orientationSign_signed]
  rcases Int.units_eq_one_or (o.chartSign z z) with h | h <;>
    rw [h] <;> simp [mul_comm]

end OrientationLift

/-- A manifold orientation is an orientation lift modulo simultaneous reversal of its model
orientation and all chart signs. -/
abbrev Orientation (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] (ι : Type*) [Fintype ι]
    [Fact (Fintype.card ι = Module.finrank ℝ E)] :=
  MulAction.orbitRel.Quotient ℤˣ (OrientationLift I M ι)

namespace Orientation

/-- The manifold orientation represented by an orientation lift. -/
def mk (o : OrientationLift I M ι) : Orientation I M ι := Quotient.mk'' o

/-- The orientation induced on the tangent space at a point, expressed in model coordinates. -/
def orientationAt (o : Orientation I M ι) (z : M) : _root_.Orientation ℝ E ι :=
  Quotient.liftOn' o (fun l ↦ l.orientationAt z) fun a b h ↦ by
    rcases h with ⟨ε, rfl⟩
    exact OrientationLift.orientationAt_smul ε b z

@[simp]
theorem orientationAt_mk (o : OrientationLift I M ι) (z : M) :
    orientationAt (mk o) z = o.orientationAt z := rfl

@[simp]
theorem mk_smul (ε : ℤˣ) (o : OrientationLift I M ι) : mk (ε • o) = mk o :=
  Quotient.sound ⟨ε, rfl⟩

/-- The sign difference between two manifold orientations. -/
noncomputable def deltaLC (o₀ o : Orientation I M ι) : LocallyConstant M ℤˣ :=
  Quotient.liftOn₂' o₀ o OrientationLift.deltaLC fun a₀ a b₀ b h₀ h ↦ by
    rcases h₀ with ⟨ε, rfl⟩
    rcases h with ⟨η, rfl⟩
    exact OrientationLift.deltaLC_smul ε η b₀ b

@[simp]
theorem deltaLC_mk (o₀ o : OrientationLift I M ι) :
    deltaLC (mk o₀) (mk o) = OrientationLift.deltaLC o₀ o := rfl

/-- The pointwise value of `deltaLC` is the intrinsic relative sign of the two induced
orientations. -/
@[simp]
theorem deltaLC_apply (o₀ o : Orientation I M ι) (z : M) :
    deltaLC o₀ o z = orientationSign (o₀.orientationAt z) (o.orientationAt z) := by
  refine Quotient.inductionOn₂' o₀ o ?_
  intro l₀ l
  exact OrientationLift.deltaLC_eq_orientationSign l₀ l z

@[simp]
theorem deltaLC_self (o : Orientation I M ι) :
    deltaLC o o = LocallyConstant.const M 1 := by
  ext z
  simp

/-- Modify a manifold orientation by a locally constant sign. -/
def twist (o : Orientation I M ι) (δ : LocallyConstant M ℤˣ) : Orientation I M ι :=
  Quotient.map' (fun l ↦ l.twist δ) (fun a b h ↦ by
    rcases h with ⟨ε, rfl⟩
    exact ⟨ε, (OrientationLift.twist_smul ε b δ).symm⟩) o

@[simp]
theorem twist_mk (o : OrientationLift I M ι) (δ : LocallyConstant M ℤˣ) :
    twist (mk o) δ = mk (o.twist δ) := rfl

@[simp]
theorem orientationAt_twist (o : Orientation I M ι) (δ : LocallyConstant M ℤˣ) (z : M) :
    (o.twist δ).orientationAt z = signedOrientation (δ z) (o.orientationAt z) := by
  refine Quotient.inductionOn' o ?_
  intro l
  exact OrientationLift.orientationAt_twist l δ z

@[simp]
theorem deltaLC_twist (o : Orientation I M ι) (δ : LocallyConstant M ℤˣ) :
    deltaLC o (o.twist δ) = δ := by
  ext z : 1
  rw [deltaLC_apply, orientationAt_twist]
  simpa using orientationSign_signed (1 : ℤˣ) (δ z) (o.orientationAt z) (o.orientationAt z)

private theorem twist_deltaLC_mk (o₀ o : OrientationLift I M ι) :
    twist (mk o₀) (deltaLC (mk o₀) (mk o)) = mk o := by
  let ε := orientationSign o₀.modelOrientation o.modelOrientation
  have hLift : ε • o₀.twist (OrientationLift.deltaLC o₀ o) = o := by
    apply OrientationLift.ext
    · rw [OrientationLift.smul_modelOrientation]
      exact signedOrientation_orientationSign o₀.modelOrientation o.modelOrientation
    · funext x z
      by_cases hz : z ∈ (chartAt H x).source
      · rw [OrientationLift.smul_chartSign_of_mem ε _ hz,
          OrientationLift.twist_chartSign _ _ hz, OrientationLift.deltaLC_eq o₀ o hz]
        exact (by decide : ∀ a b c : ℤˣ, a * (a * (b * c) * c) = b) _ _ _
      · rw [(ε • o₀.twist (OrientationLift.deltaLC o₀ o)).chartSign_eq_one_of_notMem x z hz,
          o.chartSign_eq_one_of_notMem x z hz]
  rw [deltaLC_mk, twist_mk]
  calc
    mk (o₀.twist (OrientationLift.deltaLC o₀ o)) =
        mk (ε • o₀.twist (OrientationLift.deltaLC o₀ o)) := (mk_smul _ _).symm
    _ = mk o := congrArg mk hLift

@[simp]
theorem twist_deltaLC (o₀ o : Orientation I M ι) : o₀.twist (deltaLC o₀ o) = o := by
  refine Quotient.inductionOn₂' o₀ o ?_
  exact twist_deltaLC_mk

/-- Relative to a fixed base orientation, manifold orientations are equivalent to locally
constant sign functions. -/
noncomputable def equivLocallyConstant (o₀ : Orientation I M ι) :
    Orientation I M ι ≃ LocallyConstant M ℤˣ where
  toFun := deltaLC o₀
  invFun := twist o₀
  left_inv := twist_deltaLC o₀
  right_inv := deltaLC_twist o₀

/-- Negating an orientation twists it by the constant sign `-1`. -/
instance : InvolutiveNeg (Orientation I M ι) where
  neg o := o.twist (LocallyConstant.const M (-1))
  neg_neg o := by
    refine Quotient.inductionOn' o ?_
    intro l
    change twist (twist (mk l) (LocallyConstant.const M (-1)))
      (LocallyConstant.const M (-1)) = mk l
    rw [twist_mk, twist_mk]
    apply congrArg mk
    apply OrientationLift.ext
    · rfl
    · funext x z
      by_cases hz : z ∈ (chartAt H x).source
      · rw [OrientationLift.twist_chartSign _ _ hz,
          OrientationLift.twist_chartSign _ _ hz]
        simp
      · rw [((l.twist (LocallyConstant.const M (-1))).twist
            (LocallyConstant.const M (-1))).chartSign_eq_one_of_notMem x z hz,
          l.chartSign_eq_one_of_notMem x z hz]

@[simp]
theorem neg_orientationAt (o : Orientation I M ι) (z : M) :
    (-o).orientationAt z = -o.orientationAt z := by
  rw [show -o = o.twist (LocallyConstant.const M (-1)) from rfl, orientationAt_twist]
  simp

@[simp]
theorem deltaLC_neg (o : Orientation I M ι) :
    deltaLC o (-o) = LocallyConstant.const M (-1) :=
  deltaLC_twist o (LocallyConstant.const M (-1))

/-- An orientation on a nonempty manifold differs from its negation. -/
theorem ne_neg [Nonempty M] (o : Orientation I M ι) : o ≠ -o := by
  intro h
  obtain ⟨z⟩ := ‹Nonempty M›
  exact Module.Ray.ne_neg_self (o.orientationAt z) <| by
    simpa using congrArg (fun o : Orientation I M ι ↦ o.orientationAt z) h

/-- Two orientations of a preconnected manifold are equal or negatives of each other. -/
theorem eq_or_eq_neg [PreconnectedSpace M] (o o₀ : Orientation I M ι) :
    o = o₀ ∨ o = -o₀ := by
  let e := equivLocallyConstant o₀
  rw [← e.injective.eq_iff, ← e.injective.eq_iff]
  obtain ⟨δ, hδ⟩ := (deltaLC o₀ o).exists_eq_const
  rcases Int.units_eq_one_or δ with rfl | rfl <;>
    simp_all [e, equivLocallyConstant]

end Orientation

/-- A manifold is orientable if it admits a manifold orientation. -/
class Orientable (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] (ι : Type*) [Fintype ι]
    [Fact (Fintype.card ι = Module.finrank ℝ E)] : Prop where
  /-- An orientation witnessing orientability. -/
  nonemptyOrientation : Nonempty (Orientation I M ι)

/-- Typeclass choosing a specific orientation on a manifold. -/
class OrientedManifold (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] (ι : Type*) [Fintype ι]
    [Fact (Fintype.card ι = Module.finrank ℝ E)] where
  /-- The chosen orientation of the manifold. -/
  manifoldOrientation : Orientation I M ι

/-- An oriented manifold is orientable. -/
instance [o : OrientedManifold I M ι] : Orientable I M ι := ⟨⟨o.manifoldOrientation⟩⟩

namespace Orientation

variable (I) in
theorem natCard_eq_two_pow_of_natCard_connectedComponents_eq [Orientable I M ι]
    [Finite (ConnectedComponents M)] {n : ℕ}
    (hn : Nat.card (ConnectedComponents M) = n) :
    Nat.card (Orientation I M ι) = 2 ^ n := by
  letI : LocallyConnectedSpace M := I.locallyConnectedSpace M
  let o₀ : Orientation I M ι :=
    Classical.choice (Orientable.nonemptyOrientation (I := I) (M := M) (ι := ι))
  calc
    Nat.card (Orientation I M ι)
    _ = Nat.card (LocallyConstant M ℤˣ) := Nat.card_congr (equivLocallyConstant o₀)
    _ = Nat.card (ConnectedComponents M → ℤˣ) :=
      Nat.card_congr LocallyConstant.equivConnectedComponents
    _ = Nat.card ℤˣ ^ Nat.card (ConnectedComponents M) := by
      simpa using (Nat.card_fun (α := ConnectedComponents M) (β := ℤˣ))
    _ = 2 ^ n := by
      rw [show Nat.card ℤˣ = 2 from by simp [Nat.card_eq_fintype_card], hn]

end Orientation

end Manifold
