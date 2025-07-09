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
  -- comes in a future PR by sgouezel; don't need this part yet
  -- [IsRiemannianManifold I M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-! Compatible connections: a connection on TM is compatible with the metric on M iff
`∇ X ⟨Y, Z⟩ = ⟨∇ X Y, Z⟩ + ⟨Y, ∇ X Z⟩` holds for all vector fields X, Y and Z on `M`.
The left hand side is the pushforward of the function `⟨Y, Z⟩` along the vector field `X`:
the left hand side at `X` is `df(X x)`, where `f := ⟨Y, Z⟩`. -/

variable {X X' Y Y' Z Z' : Π x : M, TangentSpace I x}

/-- The scalar product of two vector fields -/
noncomputable abbrev product (X Y : Π x : M, TangentSpace I x) : M → ℝ :=
  fun x ↦ inner ℝ (X x) (Y x)
-- Riemannian.lean shows that `product` is C^k if X and Y are

local notation "⟪" X ", " Y "⟫" => product I X Y

section product

omit [IsManifold I ∞ M]

variable (X Y) in
lemma product_swap : ⟪Y, X⟫ = ⟪X, Y⟫ := by
  ext x
  apply real_inner_comm

variable (X) in
@[simp]
lemma product_zero_left : ⟪0, X⟫ = 0 := by
  ext x
  simp [product]

@[simp]
lemma product_zero_right : ⟪X, 0⟫ = 0 := by rw [product_swap, product_zero_left]

variable (X X' Y) in
lemma product_add_left : ⟪X + X', Y⟫ = ⟪X, Y⟫ + ⟪X', Y⟫ := by
  ext x
  simp [product, InnerProductSpace.add_left]

variable (X Y Y') in
lemma product_add_right : ⟪X, Y + Y'⟫ = ⟪X, Y⟫ + ⟪X, Y'⟫ := by
  rw [product_swap, product_swap _ Y, product_swap _ Y', product_add_left]

variable (X Y) in
@[simp] lemma product_neg_left : ⟪-X, Y⟫ = -⟪X, Y⟫ := by ext x; simp [product]

variable (X Y) in
@[simp] lemma product_neg_right : ⟪X, -Y⟫ = -⟪X, Y⟫ := by ext x; simp [product]

variable (X X' Y) in
lemma product_sub_left : ⟪X - X', Y⟫ = ⟪X, Y⟫ - ⟪X', Y⟫ := by
  ext x
  simp [product, inner_sub_left]

variable (X Y Y') in
lemma product_sub_right : ⟪X, Y - Y'⟫ = ⟪X, Y⟫ - ⟪X, Y'⟫ := by
  ext x
  simp [product, inner_sub_right]

variable (X Y) in
lemma product_smul_left (f : M → ℝ) : product I (f • X) Y = f • product I X Y := by
  ext x
  simp [product, real_inner_smul_left]

variable (X Y) in
lemma product_smul_right (f : M → ℝ) : product I X (f • Y) = f • product I X Y := by
  ext x
  simp [product, real_inner_smul_right]

end product

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
noncomputable def leviCivita_rhs : M → ℝ := (1 / 2 : ℝ) • (
  rhs_aux I X Y Z + rhs_aux I Y Z X - rhs_aux I Z X Y
  - ⟪Y ,(VectorField.mlieBracket I X Z)⟫
  - ⟪Z, (VectorField.mlieBracket I X Y)⟫
  + ⟪X, (VectorField.mlieBracket I Z Y)⟫
  )

variable (X Y Z) in
lemma aux (h : cov.IsLeviCivitaConnection) : rhs_aux I X Y Z =
    ⟪cov X Y, Z⟫ + ⟪Y, cov Z X⟫ + ⟪Y, VectorField.mlieBracket I X Z⟫ := by
  trans ⟪cov X Y, Z⟫ + ⟪Y, cov X Z⟫
  · ext x
    exact h.1 X Y Z x
  · simp [← isTorsionFree_iff.mp h.2 X Z, product_sub_right]

lemma isolate_aux {α : Type*} [AddCommGroup α]
    (X Y Z A D E F : α) (h : X + Y - Z = 2 * A + D + E - F) :
    2 * A = X + Y - Z - D - E + F := by
  trans (X + Y - Z) - D - E + F
  · rw [h]; abel
  · abel

variable (X Y Z) in
/-- Auxiliary lemma towards the uniquness of the Levi-Civita connection: expressing the term
⟨∇ X Y, Z⟩ for all differentiable vector fields X, Y and Z, without reference to ∇. -/
lemma isLeviCivitaConnection_uniqueness_aux (h : cov.IsLeviCivitaConnection) :
    ⟪cov X Y, Z⟫ = leviCivita_rhs I X Y Z := by
  set A := ⟪cov X Y, Z⟫
  set B := ⟪cov Z X, Y⟫
  set C := ⟪cov Y Z, X⟫
  set D := ⟪Y, VectorField.mlieBracket I X Z⟫ with D_eq
  set E := ⟪Z, VectorField.mlieBracket I Y X⟫ with E_eq
  set F := ⟪X, VectorField.mlieBracket I Z Y⟫ with F_eq
  have eq1 : rhs_aux I X Y Z = A + B + D := by
    simp only [aux I X Y Z cov h, A, B, D, product_swap _ Y (cov Z X)]
  have eq2 : rhs_aux I Y Z X = C + A + E := by
    simp only [aux I Y Z X cov h, A, C, E, product_swap _ (cov X Y) Z]
  have eq3 : rhs_aux I Z X Y = B + C + F := by
    simp only [aux I Z X Y cov h, B, C, F, product_swap _ X (cov Y Z)]
  -- add (I) and (II), subtract (III)
  have : rhs_aux I X Y Z + rhs_aux I Y Z X - rhs_aux I Z X Y = 2 * A + D + E - F := by
    rw [eq1, eq2, eq3]
    abel_nf
    grind [zsmul_eq_mul, Int.cast_ofNat, Int.reduceNeg, neg_smul, one_smul]

  -- solve for ⟪cov X Y, Z⟫ and obtain the claim
  simp only [leviCivita_rhs] -- - D - E + F
  ext x
  have almost := isolate_aux (X := rhs_aux I X Y Z) (Y := rhs_aux I Y Z X) (Z := rhs_aux I Z X Y)
    (A := A) (D := D) (E := E) (F := F) (h := by simp [this]; sorry)
  sorry -- obvious: if 2 • A = stuff, A = 1/2 stuff

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

/- XXX: writing `hY.inner_bundle hZ` or writing `by apply MDifferentiable.inner_bundle hY hZ`
yields an error
synthesized type class instance is not definitionally equal to expression inferred by typing rules,
synthesized
  fun x ↦ instNormedAddCommGroupOfRiemannianBundle x
inferred
  fun b ↦ inst✝⁷ -/
variable {I} in
lemma foo (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) : MDiff ⟪Y, Z⟫ :=
  MDifferentiable.inner_bundle hY hZ

variable (X Y Z Z') in
lemma rhs_aux_addZ (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
  rhs_aux I X Y (Z + Z') = rhs_aux I X Y Z + rhs_aux I X Y Z' := by
  unfold rhs_aux
  ext x
  rw [product_add_right, mfderiv_add ((foo hY hZ) x) ((foo hY hZ') x)]; simp; congr

omit [IsManifold I ∞ M] in
variable (X X' Y Z) in
lemma rhs_aux_addX : rhs_aux I (X + X') Y Z = rhs_aux I X Y Z + rhs_aux I X' Y Z := by
  ext x
  simp [rhs_aux]

variable (X Y Y' Z) in
lemma rhs_aux_addY (hY : MDiff (T% Y)) (hY' : MDiff (T% Y')) (hZ : MDiff (T% Z)) :
    rhs_aux I X (Y + Y') Z = rhs_aux I X Y Z + rhs_aux I X Y' Z := by
  ext x
  simp only [rhs_aux]
  rw [product_add_left, mfderiv_add ((foo hY hZ) x) ((foo hY' hZ) x)]
  simp; congr

variable (X Y Z) in
lemma rhs_aux_smulZ (f : M → ℝ) : rhs_aux I X Y (f • Z) = f • rhs_aux I X Y Z := by
  ext x
  simp only [rhs_aux]
  rw [product_smul_right]
  -- XXX: not true, the product rule gives us two terms
  -- and there is missing API in mathlib!
  -- only holds given enough smoothness!
  sorry

variable (X Y Z) in
lemma rhs_aux_smulX (f : M → ℝ) : rhs_aux I (f • X) Y Z = f • rhs_aux I X Y Z := by
  ext x
  simp [rhs_aux]

variable (X Y Z Z') in
lemma rhs_aux_smulY (f : M → ℝ) : rhs_aux I X (f • Y) Z = f • rhs_aux I X Y Z := by
  ext x
  simp [rhs_aux]
  rw [product_smul_left]
  -- TODO: get a second term from the product rule!
  sorry

lemma leviCivita_rhs_add (Z Z' : Π x : M, TangentSpace I x) [CompleteSpace E]
    (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
    leviCivita_rhs I X Y (Z + Z') = leviCivita_rhs I X Y Z + leviCivita_rhs I X Y Z' := by
  -- A bit too painful, and have missing differentiability assumptions.
  simp only [leviCivita_rhs]
  set A : M → ℝ := (1 : M → ℝ) / 2
  --rw [← left_distrib]
  --apply congrArg
  ext x
  have h1 : VectorField.mlieBracket I X (Z + Z') =
    VectorField.mlieBracket I X Z + VectorField.mlieBracket I X Z' := by
    ext x
    simp [VectorField.mlieBracket_add_right (V := X) (hZ x) (hZ' x)]
  have h2 : VectorField.mlieBracket I (Z + Z') Y =
    VectorField.mlieBracket I Z Y + VectorField.mlieBracket I Z' Y := by
    ext x
    simp [VectorField.mlieBracket_add_left (W := Y) (hZ x) (hZ' x)]
  simp [h1, h2, rhs_aux_addX] -- rhs_aux_addY, rhs_aux_addZ
  sorry -- module

lemma leviCivita_rhs_smul [CompleteSpace E] {f : M → ℝ} {Z' : Π x : M, TangentSpace I x}
    (hf : MDiff f) (hZ : MDiff (T% Z)) :
    leviCivita_rhs I X Y (f • Z) = f • leviCivita_rhs I X Y Z := by
  simp only [leviCivita_rhs]
  simp [rhs_aux_smulX, rhs_aux_smulY, rhs_aux_smulZ]
  ext x
  simp only [Pi.mul_apply, /-Pi.inv_apply, Pi.ofNat_apply,-/ Pi.add_apply /-, Pi.sub_apply-/]
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
  simp only [Pi.smul_apply', smul_eq_mul]; abel_nf
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
lemma bar [FiniteDimensional ℝ E] (e : Trivialization E (TotalSpace.proj: TangentBundle I M → M))
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

lemma baz : (LeviCivitaConnection I M).IsLeviCivitaConnection := sorry

end CovariantDerivative
