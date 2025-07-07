/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# The Levi-Civita connection

This file will define the Levi-Civita connection on any Riemannian manifold.
Details to be written!




TODO: more generally, define a notion of metric connections (e.g., those whose parallel transport
is an isometry) and prove the Levi-Civita connection is a metric connection

-/

open Bundle Filter Function Topology

open scoped Bundle Manifold ContDiff

-- Let M be a C^k real manifold modeled on (E, H), endowed with a Riemannian metric.
variable {n : WithTop ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  -- comes in a future PR by sgouezel; don't need this part yet
  -- [IsRiemannianManifold I M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-! Compatible connections: a connection on TM is compatible with the metric on M iff
`∇ X ⟨Y, Z⟩ = ⟨∇ X Y, Z⟩ + ⟨Y, ∇ X Z⟩` holds for all vector fields X, Y and Z on `M`.
The left hand side is the pushforward of the function `⟨Y, Z⟩` along the vector field `X`:
the left hand side at `X` is `df(X x)`, where `f := ⟨Y, Z⟩`. -/

variable {X X' Y Y' Z Z' : Π x : M, TangentSpace I x}

/-- The scalar product of two vector fields -/
noncomputable abbrev product (X Y : Π x : M, TangentSpace I x) : M → ℝ := fun x ↦ inner ℝ (X x) (Y x)
-- Riemannian.lean shows that `product` is C^k if X and Y are

local notation "⟪" X ", " Y "⟫" => product I X Y

variable (X) in
@[simp]
lemma product_zero_right : ⟪X, 0⟫ = 0 := sorry

@[simp]
lemma product_zero_left : ⟪0, X⟫ = 0 := sorry

lemma product_sub_right : ⟪X, Y - Z⟫ = ⟪X, Y⟫ - ⟪X, Z⟫ := sorry

namespace CovariantDerivative

-- Let `cov` be a covariant derivative on `TM`.
-- TODO: include in cheat sheet!
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

-- TODO: make g part of the notation!
def IsCompatible : Prop :=
  ∀ X Y Z : Π x : M, TangentSpace I x, -- XXX: missing differentiability hypotheses!
  ∀ x : M,
  mfderiv I 𝓘(ℝ) ⟪Y, Z⟫ x (X x) = ⟪cov X Y, Z⟫ x + ⟪Y, cov X Z⟫ x

-- TODO: make g part of the notation!
/-- A covariant derivative on `TM` is called the **Levi-Civita connection** for a Riemannian metric
`g` on `M` iff it is torsion-free and compatible with `g`. -/
def IsLeviCivitaConnection : Prop := cov.IsCompatible ∧ cov.IsTorsionFree

-- This is mild defeq abuse, right?
variable (X Y Z) in
noncomputable abbrev rhs_aux : M → ℝ := fun x ↦ (mfderiv I 𝓘(ℝ) ⟪Y, Z⟫ x (X x))

-- XXX: inlining rhs_aux makes things not typecheck any more!

variable (X Y Z) in
/-- Auxiliary quantity used in the uniqueness proof of the Levi-Civita connection:
If ∇ is a Levi-Civita connection on `TM`, then
`⟨∇ X Y, Z⟩ = leviCivita_rhs I X Y Z` for all vector fields `Z`. -/
noncomputable def leviCivita_rhs : M → ℝ := 1 / 2 * (
  rhs_aux I X Y Z + rhs_aux I Y Z X + rhs_aux I Z X Y
  - ⟪Y ,(VectorField.mlieBracket I X Z)⟫
  - ⟪Z, (VectorField.mlieBracket I X Y)⟫
  + ⟪X, (VectorField.mlieBracket I Z Y)⟫
  )

variable (X Y Z) in
lemma aux (h : cov.IsLeviCivitaConnection) : rhs_aux I X Y Z =
    ⟪cov X Y, Z⟫ + ⟪Y, cov Z X⟫ + ⟪Y, VectorField.mlieBracket I X Z⟫ := by
  have : ⟪Y, cov X Z - cov Z X⟫ = ⟪Y, VectorField.mlieBracket I X Z⟫ := by
    simp [isTorsionFree_iff.mp h.2 X Z]
  trans ⟪cov X Y, Z⟫ + ⟪Y, cov X Z⟫
  · ext x
    exact h.1 X Y Z x
  · simp [← this, product_sub_right]

-- XXX: are there useful intermediate lemmas to deduce just for metric or torsion-free connections?
variable (X Y Z) in
/-- Auxiliary lemma towards the uniquness of the Levi-Civita connection: expressing the term
⟨∇ X Y, Z⟩ for all differentiable vector fields X, Y and Z, without reference to ∇. -/
lemma isLeviCivitaConnection_uniqueness_aux (h : cov.IsLeviCivitaConnection) :
    ⟪cov X Y, Z⟫ = leviCivita_rhs I X Y Z := by
  have eq1 := aux I X Y Z cov h
  have eq2 := aux I Y Z X cov h
  have eq3 := aux I Z X Y cov h
  -- add (I) + (II) and subtract (III)

  -- solve for ⟪cov X Y, Z⟫
  sorry

variable (X Y Y') in
lemma product_add : product I X (Y + Y') = product I X Y + product I X Y' := sorry

variable (X Y) in
lemma product_smul_left (f : M → ℝ) : product I (f • X) Y = f • product I X Y := by
  ext x
  simp [product, real_inner_smul_left]

variable (X Y) in
lemma product_smul_right (f : M → ℝ) : product I X (f • Y) = f • product I X Y := by
  ext x
  simp [product, real_inner_smul_right]

@[simp]
lemma product_add_left_apply (x : M) : product I (X + X') Y x = product I X Y x + product I X' Y x := sorry

@[simp]
lemma product_add_right_apply (x : M) : product I X (Y + Y') x = product I X Y x + product I X Y' x := sorry

variable (X Y Z Z') in
lemma rhs_aux_addZ : rhs_aux I X Y (Z + Z') = rhs_aux I X Y Z + rhs_aux I X Y Z' := by
  ext x
  simp only [rhs_aux]
  -- only holds given enough smoothness!
  sorry

variable (X X' Y Z) in
lemma rhs_aux_addX : rhs_aux I (X + X') Y Z = rhs_aux I X Y Z + rhs_aux I X' Y Z := by
  sorry

variable (X Y Y' Z) in
lemma rhs_aux_addY : rhs_aux I X (Y + Y') Z = rhs_aux I X Y Z + rhs_aux I X Y' Z := by
  sorry

variable (X Y Z) in
lemma rhs_aux_smulZ (f : M → ℝ) : rhs_aux I X Y (f • Z) = f • rhs_aux I X Y Z := by
  ext x
  simp only [rhs_aux]
  -- only holds given enough smoothness!
  sorry

variable (X Y Z) in
lemma rhs_aux_smulX (f : M → ℝ) : rhs_aux I (f • X) Y Z = f • rhs_aux I X Y Z := by
  sorry

variable (X Y Z Z') in
lemma rhs_aux_smulY (f : M → ℝ) : rhs_aux I X (f • Y) Z = f • rhs_aux I X Y Z := by
  sorry

lemma leviCivita_rhs_add (Z Z' : Π x : M, TangentSpace I x) [CompleteSpace E]
    (hZ : MDifferentiable% (T% Z)) (hZ' : MDifferentiable% (T% Z')) :
    leviCivita_rhs I X Y (Z + Z') = leviCivita_rhs I X Y Z + leviCivita_rhs I X Y Z' := by
  -- A bit too painful, and have missing differentiability assumptions.
  simp only [leviCivita_rhs]
  set A : M → ℝ := (1 : M → ℝ) / 2
  rw [← left_distrib]
  apply congrArg
  ext x
  have h1 : VectorField.mlieBracket I X (Z + Z') =
    VectorField.mlieBracket I X Z + VectorField.mlieBracket I X Z' := by
    ext x
    simp [VectorField.mlieBracket_add_right (V := X) (hZ x) (hZ' x)]
  have h2 : VectorField.mlieBracket I (Z + Z') Y =
    VectorField.mlieBracket I Z Y + VectorField.mlieBracket I Z' Y := by
    ext x
    simp [VectorField.mlieBracket_add_left (W := Y) (hZ x) (hZ' x)]
  simp [h1, h2, rhs_aux_addX, rhs_aux_addY, rhs_aux_addZ]
  module

lemma leviCivita_rhs_smul [CompleteSpace E] {f : M → ℝ} {Z' : Π x : M, TangentSpace I x}
    (hf : MDifferentiable% f) (hZ : MDifferentiable% (T% Z)) :
    leviCivita_rhs I X Y (f • Z) = f • leviCivita_rhs I X Y Z := by
  simp only [leviCivita_rhs]
  simp [rhs_aux_smulX, rhs_aux_smulY, rhs_aux_smulZ]
  ext x
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.ofNat_apply, Pi.add_apply, Pi.sub_apply]
  -- Only kind of true: get extra mfderiv's, which will cancel in the end...
  have h1 : VectorField.mlieBracket I X (f • Z) =
      f • VectorField.mlieBracket I X Z := by
    ext x
    rw [VectorField.mlieBracket_smul_right (hf x) (hZ x)]; simp; sorry
  have h2 : VectorField.mlieBracket I (f • Z) Y =
      f • VectorField.mlieBracket I Z Y := by
    ext x
    rw [VectorField.mlieBracket_smul_left (hf x) (hZ x)]; simp; sorry
  simp [h1, h2]
  rw [product_smul_left, product_smul_right]
  simp; abel_nf
  sorry -- easy computation

variable {I} in
/-- If two vector fields `X` and `X'` on `M` satisfy the relation `⟨X, Z⟩ = ⟨X', Z⟩` for all
vector fields `Z`, then `X = X'`. XXX up to differentiability? -/
lemma congr_of_forall_product {X X' : Π x : M, TangentSpace I x}
    (h : ∀ Z : Π x : M, TangentSpace I x, ⟪X, Z⟫ = ⟪X', Z⟫) : X = X' := by
  -- any vector bundle with a bundle metric has local orthonormal frames (not just a local frame)
  --  -> apply Gram-Schmidt to a local frame; prove orthonormality w.r.t. bundle metric
  -- prove: local orthonormal frame is C^k when the bundle metric is
  -- use this to prove this lemma
  sorry

/-- The Levi-Civita connection on `(M, g)` is uniquely determined,
at least on differentiable vector fields. -/
-- (probably not everywhere, as addition rules apply only for differentiable vector fields?)
theorem isLeviCivita_uniqueness {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection) :
    -- almost, only agree on smooth functions
    cov = cov' := by
  ext X σ x
  apply congrFun
  apply congr_of_forall_product fun Z ↦ ?_
  trans leviCivita_rhs I X σ Z
  · exact cov.isLeviCivitaConnection_uniqueness_aux I X σ Z hcov
  · exact (cov'.isLeviCivitaConnection_uniqueness_aux I X σ Z hcov').symm

variable (X Y) in
noncomputable def existence_candidate_aux [FiniteDimensional ℝ E]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e] :
    (x : M) → TangentSpace I x := fun x ↦
  -- Choose a trivialisation of TM near x.
  letI b := Basis.ofVectorSpace ℝ E
  --letI t := trivializationAt E (TangentSpace I : M → Type _) x
  -- choose an orthonormal frame (s i) near x w.r.t. to this trivialisation, and the metric g
  -- TODO: this is only a local frame; not orthonormal yet! placeholder definition!
  letI frame := b.localFrame e
  -- The coefficient of the desired tangent vector ∇ X Y x w.r.t. s i
  -- is given by leviCivita_rhs X Y s i.
  ∑ i, ((leviCivita_rhs I X Y (frame i)) x) • (frame i x)

variable (M) in
-- TODO: make g part of the notation!
/-- Given two vector fields X and Y on TM, compute
the candidate definition for the Levi-Civita connection on `TM`. -/
noncomputable def existence_candidate [FiniteDimensional ℝ E] :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  fun X Y x ↦
  -- -- Choose a trivialisation of TM near x.
  -- letI b := Basis.ofVectorSpace ℝ E
  letI t := trivializationAt E (TangentSpace I : M → Type _) x
  -- -- choose an orthonormal frame (s i) near x w.r.t. to this trivialisation, and the metric g
  -- -- TODO: this is only a local frame; not orthonormal yet! placeholder definition!
  -- letI frame := b.localFrame t
  -- -- The coefficient of the desired tangent vector ∇ X Y x w.r.t. s i
  -- -- is given by leviCivita_rhs X Y s i.
  -- ∑ i, ((leviCivita_rhs I X Y (frame i)) x) • (frame i x)
  existence_candidate_aux I X Y t x

variable (X Y) in
-- The above definition behaves well: for each compatible trivialisation e,
-- using e on e.baseSet yields the same result as above.
lemma foo [FiniteDimensional ℝ E] (e : Trivialization E (TotalSpace.proj: TangentBundle I M → M))
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet) :
  existence_candidate I M X Y x = existence_candidate_aux I X Y e x := sorry

-- The candidate definition is a covariant derivative on each local frame's domain.
lemma isCovariantDerivativeOn_existence_candidate [FiniteDimensional ℝ E]
    (e : Trivialization E (TotalSpace.proj: TangentBundle I M → M)) [MemTrivializationAtlas e] :
    IsCovariantDerivativeOn E (TangentSpace I) (existence_candidate I M) e.baseSet := by
  sorry

-- deduce: this defines a covariant derivative

-- TODO: make g part of the notation!
variable (M) in
/-- A choice of Levi-Civita connection on the tangent bundle `TM` of a Riemannian manifold `(M, g)`:
this is unique up to the value on non-differentiable vector fields.
If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead. -/
def LeviCivitaConnection : CovariantDerivative I E (TangentSpace I : M → Type _) :=
  -- This is the existence part of the proof: take the formula derived above
  -- and prove it satisfies all the conditions.

  -- use isCovariantDerivativeOn_existence_candidate plus (future) API lemmas about
  -- IsCovariantDerivativeOn
  sorry

lemma bar : (LeviCivitaConnection I M).IsLeviCivitaConnection  := sorry

end CovariantDerivative
