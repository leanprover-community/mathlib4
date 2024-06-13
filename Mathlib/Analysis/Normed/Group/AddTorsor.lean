/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.LinearAlgebra.AffineSpace.Midpoint

#align_import analysis.normed.group.add_torsor from "leanprover-community/mathlib"@"837f72de63ad6cd96519cde5f1ffd5ed8d280ad0"

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.
-/


noncomputable section

open NNReal Topology

open Filter

/-- A `NormedAddTorsor V P` is a torsor of an additive seminormed group
action by a `SeminormedAddCommGroup V` on points `P`. We bundle the pseudometric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a pseudometric space, but
bundling just the distance and using an instance for the pseudometric space
results in type class problems). -/
class NormedAddTorsor (V : outParam Type*) (P : Type*) [SeminormedAddCommGroup V]
  [PseudoMetricSpace P] extends AddTorsor V P where
  dist_eq_norm' : ∀ x y : P, dist x y = ‖(x -ᵥ y : V)‖
#align normed_add_torsor NormedAddTorsor

/-- Shortcut instance to help typeclass inference out. -/
instance (priority := 100) NormedAddTorsor.toAddTorsor' {V P : Type*} [NormedAddCommGroup V]
    [MetricSpace P] [NormedAddTorsor V P] : AddTorsor V P :=
  NormedAddTorsor.toAddTorsor
#align normed_add_torsor.to_add_torsor' NormedAddTorsor.toAddTorsor'

variable {α V P W Q : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [NormedAddCommGroup W] [MetricSpace Q] [NormedAddTorsor W Q]

instance (priority := 100) NormedAddTorsor.to_isometricVAdd : IsometricVAdd V P :=
  ⟨fun c => Isometry.of_dist_eq fun x y => by
    -- porting note (#10745): was `simp [NormedAddTorsor.dist_eq_norm']`
    rw [NormedAddTorsor.dist_eq_norm', NormedAddTorsor.dist_eq_norm', vadd_vsub_vadd_cancel_left]⟩
#align normed_add_torsor.to_has_isometric_vadd NormedAddTorsor.to_isometricVAdd

/-- A `SeminormedAddCommGroup` is a `NormedAddTorsor` over itself. -/
instance (priority := 100) SeminormedAddCommGroup.toNormedAddTorsor : NormedAddTorsor V V where
  dist_eq_norm' := dist_eq_norm
#align seminormed_add_comm_group.to_normed_add_torsor SeminormedAddCommGroup.toNormedAddTorsor

-- Because of the AddTorsor.nonempty instance.
/-- A nonempty affine subspace of a `NormedAddTorsor` is itself a `NormedAddTorsor`. -/
instance AffineSubspace.toNormedAddTorsor {R : Type*} [Ring R] [Module R V]
    (s : AffineSubspace R P) [Nonempty s] : NormedAddTorsor s.direction s :=
  { AffineSubspace.toAddTorsor s with
    dist_eq_norm' := fun x y => NormedAddTorsor.dist_eq_norm' x.val y.val }
#align affine_subspace.to_normed_add_torsor AffineSubspace.toNormedAddTorsor

section

variable (V W)

/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub` sometimes doesn't work. -/
theorem dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖ :=
  NormedAddTorsor.dist_eq_norm' x y
#align dist_eq_norm_vsub dist_eq_norm_vsub

theorem nndist_eq_nnnorm_vsub (x y : P) : nndist x y = ‖x -ᵥ y‖₊ :=
  NNReal.eq <| dist_eq_norm_vsub V x y
#align nndist_eq_nnnorm_vsub nndist_eq_nnnorm_vsub


/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub'` sometimes doesn't work. -/
theorem dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖ :=
  (dist_comm _ _).trans (dist_eq_norm_vsub _ _ _)
#align dist_eq_norm_vsub' dist_eq_norm_vsub'

theorem nndist_eq_nnnorm_vsub' (x y : P) : nndist x y = ‖y -ᵥ x‖₊ :=
  NNReal.eq <| dist_eq_norm_vsub' V x y
#align nndist_eq_nnnorm_vsub' nndist_eq_nnnorm_vsub'

end

theorem dist_vadd_cancel_left (v : V) (x y : P) : dist (v +ᵥ x) (v +ᵥ y) = dist x y :=
  dist_vadd _ _ _
#align dist_vadd_cancel_left dist_vadd_cancel_left

theorem nndist_vadd_cancel_left (v : V) (x y : P) : nndist (v +ᵥ x) (v +ᵥ y) = nndist x y :=
  NNReal.eq <| dist_vadd_cancel_left _ _ _

@[simp]
theorem dist_vadd_cancel_right (v₁ v₂ : V) (x : P) : dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm, vadd_vsub_vadd_cancel_right]
#align dist_vadd_cancel_right dist_vadd_cancel_right

@[simp]
theorem nndist_vadd_cancel_right (v₁ v₂ : V) (x : P) : nndist (v₁ +ᵥ x) (v₂ +ᵥ x) = nndist v₁ v₂ :=
  NNReal.eq <| dist_vadd_cancel_right _ _ _
#align nndist_vadd_cancel_right nndist_vadd_cancel_right

@[simp]
theorem dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖ := by
  -- porting note (#10745): was `simp [dist_eq_norm_vsub V _ x]`
  rw [dist_eq_norm_vsub V _ x, vadd_vsub]
#align dist_vadd_left dist_vadd_left

@[simp]
theorem nndist_vadd_left (v : V) (x : P) : nndist (v +ᵥ x) x = ‖v‖₊ :=
  NNReal.eq <| dist_vadd_left _ _
#align nndist_vadd_left nndist_vadd_left

@[simp]
theorem dist_vadd_right (v : V) (x : P) : dist x (v +ᵥ x) = ‖v‖ := by rw [dist_comm, dist_vadd_left]
#align dist_vadd_right dist_vadd_right

@[simp]
theorem nndist_vadd_right (v : V) (x : P) : nndist x (v +ᵥ x) = ‖v‖₊ :=
  NNReal.eq <| dist_vadd_right _ _
#align nndist_vadd_right nndist_vadd_right

/-- Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` given by
addition/subtraction of `x : P`. -/
@[simps!]
def IsometryEquiv.vaddConst (x : P) : V ≃ᵢ P where
  toEquiv := Equiv.vaddConst x
  isometry_toFun := Isometry.of_dist_eq fun _ _ => dist_vadd_cancel_right _ _ _
#align isometry_equiv.vadd_const IsometryEquiv.vaddConst

@[simp]
theorem dist_vsub_cancel_left (x y z : P) : dist (x -ᵥ y) (x -ᵥ z) = dist y z := by
  rw [dist_eq_norm, vsub_sub_vsub_cancel_left, dist_comm, dist_eq_norm_vsub V]
#align dist_vsub_cancel_left dist_vsub_cancel_left

@[simp]
theorem nndist_vsub_cancel_left (x y z : P) : nndist (x -ᵥ y) (x -ᵥ z) = nndist y z :=
  NNReal.eq <| dist_vsub_cancel_left _ _ _

/-- Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` given by
subtraction from `x : P`. -/
@[simps!]
def IsometryEquiv.constVSub (x : P) : P ≃ᵢ V where
  toEquiv := Equiv.constVSub x
  isometry_toFun := Isometry.of_dist_eq fun _ _ => dist_vsub_cancel_left _ _ _
#align isometry_equiv.const_vsub IsometryEquiv.constVSub

@[simp]
theorem dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ z) (y -ᵥ z) = dist x y :=
  (IsometryEquiv.vaddConst z).symm.dist_eq x y
#align dist_vsub_cancel_right dist_vsub_cancel_right

@[simp]
theorem nndist_vsub_cancel_right (x y z : P) : nndist (x -ᵥ z) (y -ᵥ z) = nndist x y :=
  NNReal.eq <| dist_vsub_cancel_right _ _ _
#align nndist_vsub_cancel_right nndist_vsub_cancel_right

theorem dist_vadd_vadd_le (v v' : V) (p p' : P) :
    dist (v +ᵥ p) (v' +ᵥ p') ≤ dist v v' + dist p p' := by
  simpa using dist_triangle (v +ᵥ p) (v' +ᵥ p) (v' +ᵥ p')
#align dist_vadd_vadd_le dist_vadd_vadd_le

theorem nndist_vadd_vadd_le (v v' : V) (p p' : P) :
    nndist (v +ᵥ p) (v' +ᵥ p') ≤ nndist v v' + nndist p p' :=
  dist_vadd_vadd_le _ _ _ _
#align nndist_vadd_vadd_le nndist_vadd_vadd_le

theorem dist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
    dist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ dist p₁ p₃ + dist p₂ p₄ := by
  rw [dist_eq_norm, vsub_sub_vsub_comm, dist_eq_norm_vsub V, dist_eq_norm_vsub V]
  exact norm_sub_le _ _
#align dist_vsub_vsub_le dist_vsub_vsub_le

theorem nndist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
    nndist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ nndist p₁ p₃ + nndist p₂ p₄ := by
  simp only [← NNReal.coe_le_coe, NNReal.coe_add, ← dist_nndist, dist_vsub_vsub_le]
#align nndist_vsub_vsub_le nndist_vsub_vsub_le

theorem edist_vadd_vadd_le (v v' : V) (p p' : P) :
    edist (v +ᵥ p) (v' +ᵥ p') ≤ edist v v' + edist p p' := by
  simp only [edist_nndist]
  norm_cast  -- Porting note: was apply_mod_cast
  apply dist_vadd_vadd_le
#align edist_vadd_vadd_le edist_vadd_vadd_le

theorem edist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
    edist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ edist p₁ p₃ + edist p₂ p₄ := by
  simp only [edist_nndist]
  norm_cast  -- Porting note: was apply_mod_cast
  apply dist_vsub_vsub_le
#align edist_vsub_vsub_le edist_vsub_vsub_le

/-- The pseudodistance defines a pseudometric space structure on the torsor. This
is not an instance because it depends on `V` to define a `MetricSpace P`. -/
def pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor (V P : Type*) [SeminormedAddCommGroup V]
    [AddTorsor V P] : PseudoMetricSpace P where
  dist x y := ‖(x -ᵥ y : V)‖
  -- Porting note: `edist_dist` is no longer an `autoParam`
  edist_dist _ _ := by simp only [← ENNReal.ofReal_eq_coe_nnreal]
  dist_self x := by simp
  dist_comm x y := by simp only [← neg_vsub_eq_vsub_rev y x, norm_neg]
  dist_triangle x y z := by
    change ‖x -ᵥ z‖ ≤ ‖x -ᵥ y‖ + ‖y -ᵥ z‖
    rw [← vsub_add_vsub_cancel]
    apply norm_add_le
#align pseudo_metric_space_of_normed_add_comm_group_of_add_torsor pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor

/-- The distance defines a metric space structure on the torsor. This
is not an instance because it depends on `V` to define a `MetricSpace P`. -/
def metricSpaceOfNormedAddCommGroupOfAddTorsor (V P : Type*) [NormedAddCommGroup V]
    [AddTorsor V P] : MetricSpace P where
  dist x y := ‖(x -ᵥ y : V)‖
  edist_dist _ _ := by simp only; rw [ENNReal.ofReal_eq_coe_nnreal]
  dist_self x := by simp
  eq_of_dist_eq_zero h := by simpa using h
  dist_comm x y := by simp only [← neg_vsub_eq_vsub_rev y x, norm_neg]
  dist_triangle x y z := by
    change ‖x -ᵥ z‖ ≤ ‖x -ᵥ y‖ + ‖y -ᵥ z‖
    rw [← vsub_add_vsub_cancel]
    apply norm_add_le
#align metric_space_of_normed_add_comm_group_of_add_torsor metricSpaceOfNormedAddCommGroupOfAddTorsor

theorem LipschitzWith.vadd [PseudoEMetricSpace α] {f : α → V} {g : α → P} {Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) (f +ᵥ g) :=
  fun x y =>
  calc
    edist (f x +ᵥ g x) (f y +ᵥ g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
      edist_vadd_vadd_le _ _ _ _
    _ ≤ Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm
#align lipschitz_with.vadd LipschitzWith.vadd

theorem LipschitzWith.vsub [PseudoEMetricSpace α] {f g : α → P} {Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) (f -ᵥ g) :=
  fun x y =>
  calc
    edist (f x -ᵥ g x) (f y -ᵥ g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
      edist_vsub_vsub_le _ _ _ _
    _ ≤ Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm
#align lipschitz_with.vsub LipschitzWith.vsub

theorem uniformContinuous_vadd : UniformContinuous fun x : V × P => x.1 +ᵥ x.2 :=
  (LipschitzWith.prod_fst.vadd LipschitzWith.prod_snd).uniformContinuous
#align uniform_continuous_vadd uniformContinuous_vadd

theorem uniformContinuous_vsub : UniformContinuous fun x : P × P => x.1 -ᵥ x.2 :=
  (LipschitzWith.prod_fst.vsub LipschitzWith.prod_snd).uniformContinuous
#align uniform_continuous_vsub uniformContinuous_vsub

instance (priority := 100) NormedAddTorsor.to_continuousVAdd : ContinuousVAdd V P where
  continuous_vadd := uniformContinuous_vadd.continuous
#align normed_add_torsor.to_has_continuous_vadd NormedAddTorsor.to_continuousVAdd

theorem continuous_vsub : Continuous fun x : P × P => x.1 -ᵥ x.2 :=
  uniformContinuous_vsub.continuous
#align continuous_vsub continuous_vsub

theorem Filter.Tendsto.vsub {l : Filter α} {f g : α → P} {x y : P} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (f -ᵥ g) l (𝓝 (x -ᵥ y)) :=
  (continuous_vsub.tendsto (x, y)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.vsub Filter.Tendsto.vsub

section

variable [TopologicalSpace α]

theorem Continuous.vsub {f g : α → P} (hf : Continuous f) (hg : Continuous g) :
    Continuous (f -ᵥ g) :=
  continuous_vsub.comp (hf.prod_mk hg : _)
#align continuous.vsub Continuous.vsub

nonrec theorem ContinuousAt.vsub {f g : α → P} {x : α} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) :
    ContinuousAt (f -ᵥ g) x :=
  hf.vsub hg
#align continuous_at.vsub ContinuousAt.vsub

nonrec theorem ContinuousWithinAt.vsub {f g : α → P} {x : α} {s : Set α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (f -ᵥ g) s x :=
  hf.vsub hg
#align continuous_within_at.vsub ContinuousWithinAt.vsub

theorem ContinuousOn.vsub {f g : α → P} {s : Set α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (f -ᵥ g) s := fun x hx ↦
  (hf x hx).vsub (hg x hx)

end

section

variable {R : Type*} [Ring R] [TopologicalSpace R] [Module R V] [ContinuousSMul R V]

theorem Filter.Tendsto.lineMap {l : Filter α} {f₁ f₂ : α → P} {g : α → R} {p₁ p₂ : P} {c : R}
    (h₁ : Tendsto f₁ l (𝓝 p₁)) (h₂ : Tendsto f₂ l (𝓝 p₂)) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => AffineMap.lineMap (f₁ x) (f₂ x) (g x)) l (𝓝 <| AffineMap.lineMap p₁ p₂ c) :=
  (hg.smul (h₂.vsub h₁)).vadd h₁
#align filter.tendsto.line_map Filter.Tendsto.lineMap

theorem Filter.Tendsto.midpoint [Invertible (2 : R)] {l : Filter α} {f₁ f₂ : α → P} {p₁ p₂ : P}
    (h₁ : Tendsto f₁ l (𝓝 p₁)) (h₂ : Tendsto f₂ l (𝓝 p₂)) :
    Tendsto (fun x => midpoint R (f₁ x) (f₂ x)) l (𝓝 <| midpoint R p₁ p₂) :=
  h₁.lineMap h₂ tendsto_const_nhds
#align filter.tendsto.midpoint Filter.Tendsto.midpoint

end

section Pointwise

open Pointwise

theorem IsClosed.vadd_right_of_isCompact {s : Set V} {t : Set P} (hs : IsClosed s)
    (ht : IsCompact t) : IsClosed (s +ᵥ t) := by
  -- This result is still true for any `AddTorsor` where `-ᵥ` is continuous,
  -- but we don't yet have a nice way to state it.
  refine IsSeqClosed.isClosed (fun u p husv hup ↦ ?_)
  choose! a ha v hv hav using husv
  rcases ht.isSeqCompact hv with ⟨q, hqt, φ, φ_mono, hφq⟩
  refine ⟨p -ᵥ q, hs.mem_of_tendsto ((hup.comp φ_mono.tendsto_atTop).vsub hφq)
    (eventually_of_forall fun n ↦ ?_), q, hqt, vsub_vadd _ _⟩
  convert ha (φ n) using 1
  exact (eq_vadd_iff_vsub_eq _ _ _).mp (hav (φ n)).symm

end Pointwise
