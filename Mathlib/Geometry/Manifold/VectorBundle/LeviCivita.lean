/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative
import Mathlib.Geometry.Manifold.VectorBundle.OrthonormalFrame
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

set_option linter.style.commandStart false -- custom elaborators not handled well yet

/- XXX: writing `hY.inner_bundle hZ` or writing `by apply MDifferentiable.inner_bundle hY hZ`
yields an error
synthesized type class instance is not definitionally equal to expression inferred by typing rules,
synthesized
  fun x ↦ instNormedAddCommGroupOfRiemannianBundle x
inferred
  fun b ↦ inst✝⁷ -/
variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] {I} in
lemma foo (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) : MDiff ⟪Y, Z⟫ :=
  MDifferentiable.inner_bundle hY hZ

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

section rhs_aux

omit [IsManifold I ∞ M] in
lemma rhs_aux_swap : rhs_aux I X Y Z = rhs_aux I X Z Y := by
  ext x
  simp only [rhs_aux]
  congr
  exact product_swap I Z Y

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

omit [IsManifold I ∞ M] in
variable (X X' Y Z) in
lemma rhs_aux_addX : rhs_aux I (X + X') Y Z = rhs_aux I X Y Z + rhs_aux I X' Y Z := by
  ext x
  simp [rhs_aux]

variable (X) in
lemma rhs_aux_addY (hY : MDiff (T% Y)) (hY' : MDiff (T% Y')) (hZ : MDiff (T% Z)) :
    rhs_aux I X (Y + Y') Z = rhs_aux I X Y Z + rhs_aux I X Y' Z := by
  ext x
  simp only [rhs_aux]
  rw [product_add_left, mfderiv_add ((foo hY hZ) x) ((foo hY' hZ) x)]
  simp; congr

variable (X) in
lemma rhs_aux_addZ (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
  rhs_aux I X Y (Z + Z') = rhs_aux I X Y Z + rhs_aux I X Y Z' := by
  unfold rhs_aux
  ext x
  rw [product_add_right, mfderiv_add ((foo hY hZ) x) ((foo hY hZ') x)]; simp; congr

omit [IsManifold I ∞ M] in
variable (X Y Z) in
lemma rhs_aux_smulX (f : M → ℝ) : rhs_aux I (f • X) Y Z = f • rhs_aux I X Y Z := by
  ext x
  simp [rhs_aux]

variable (X) in
lemma rhs_aux_smulY {f : M → ℝ} (hf : MDiff f) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    letI A (x) : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (X x)
    rhs_aux I X (f • Y) Z = f • rhs_aux I X Y Z + A • ⟪Y, Z⟫ := by
  ext x
  rw [rhs_aux, product_smul_left, mfderiv_smul (foo hY hZ x) (hf x)]
  congr

variable (X) in
lemma rhs_aux_smulZ {f : M → ℝ} (hf : MDiff f) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    letI A (x) : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (X x)
    rhs_aux I X Y (f • Z) = f • rhs_aux I X Y Z + A • ⟪Y, Z⟫ := by
  rw [rhs_aux_swap, rhs_aux_smulY, rhs_aux_swap, product_swap]
  exacts [hf, hZ, hY]

end rhs_aux

variable {x : M}

-- XXX: inlining rhs_aux here makes things not typecheck any more!
variable (X Y Z) in
/-- Auxiliary quantity used in the uniqueness proof of the Levi-Civita connection:
If ∇ is a Levi-Civita connection on `TM`, then
`⟨∇ X Y, Z⟩ = leviCivita_rhs I X Y Z` for all vector fields `Z`. -/
noncomputable def leviCivita_rhs' : M → ℝ :=
  rhs_aux I X Y Z + rhs_aux I Y Z X - rhs_aux I Z X Y
  - ⟪Y ,(VectorField.mlieBracket I X Z)⟫
  - ⟪Z, (VectorField.mlieBracket I X Y)⟫
  + ⟪X, (VectorField.mlieBracket I Z Y)⟫

variable (X Y Z) in
/-- Auxiliary quantity used in the uniqueness proof of the Levi-Civita connection:
If ∇ is a Levi-Civita connection on `TM`, then
`⟨∇ X Y, Z⟩ = leviCivita_rhs I X Y Z` for all vector fields `Z`. -/
noncomputable def leviCivita_rhs : M → ℝ := (1 / 2 : ℝ) • leviCivita_rhs' I X Y Z

omit [IsManifold I ∞ M] in
lemma leviCivita_rhs_apply : leviCivita_rhs I X Y Z x = (1 / 2 : ℝ) • leviCivita_rhs' I X Y Z x :=
  rfl

section leviCivita_rhs

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

-- TODO: relax assumptions; I only need differentiability at x!
@[simp]
lemma leviCivita_rhs'_addX_apply [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivita_rhs' I (X + X') Y Z x =
      leviCivita_rhs' I X Y Z x + leviCivita_rhs' I X' Y Z x := by
  simp only [leviCivita_rhs']
  have h : VectorField.mlieBracket I (X + X') Y =
    VectorField.mlieBracket I X Y + VectorField.mlieBracket I X' Y := by
    ext x
    simp [VectorField.mlieBracket_add_left (W := Y) (hX x) (hX' x)]
  have h' : VectorField.mlieBracket I (X + X') Z =
    VectorField.mlieBracket I X Z + VectorField.mlieBracket I X' Z := by
    ext x
    simp [VectorField.mlieBracket_add_left (W := Z) (hX x) (hX' x)]
  simp only [rhs_aux_addX, h, h', Pi.add_apply, Pi.sub_apply]
  rw [rhs_aux_addY, rhs_aux_addZ] <;> try assumption
  rw [product_add_left, product_add_right, product_add_right]
  simp only [Pi.add_apply]
  abel

lemma leviCivita_rhs'_addX [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivita_rhs' I (X + X') Y Z =
      leviCivita_rhs' I X Y Z + leviCivita_rhs' I X' Y Z := by
  ext x
  simp [leviCivita_rhs'_addX_apply _ hX hX' hY hZ]

lemma leviCivita_rhs_addX [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivita_rhs I (X + X') Y Z = leviCivita_rhs I X Y Z + leviCivita_rhs I X' Y Z := by
  sorry -- divide the previous equation by 2

variable (X Y Z) in
lemma leviCivita_rhs_smulX {f : M → ℝ} (hf : MDiff f) (hX : MDiff (T% X)) :
    leviCivita_rhs I (f • X) Y Z = f • leviCivita_rhs I X Y Z := by
  -- TODO: do I need to assume X is differentiable?
  sorry

variable (X Z) in
lemma leviCivita_rhs_addY [CompleteSpace E]
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hY' : MDiff (T% Y')) (hZ : MDiff (T% Z)) :
    leviCivita_rhs I X (Y + Y') Z = leviCivita_rhs I X Y Z + leviCivita_rhs I X Y' Z := by
  sorry -- divide the previous equation by 2

lemma leviCivita_rhs'_addZ [CompleteSpace E]
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
    leviCivita_rhs' I X Y (Z + Z') =
      leviCivita_rhs' I X Y Z + leviCivita_rhs' I X Y Z' := by
  simp only [leviCivita_rhs']
  ext x
  have h : VectorField.mlieBracket I X (Z + Z') =
    VectorField.mlieBracket I X Z + VectorField.mlieBracket I X Z' := by
    ext x
    simp [VectorField.mlieBracket_add_right (V := X) (hZ x) (hZ' x)]
  have h' : VectorField.mlieBracket I (Z + Z') Y =
    VectorField.mlieBracket I Z Y + VectorField.mlieBracket I Z' Y := by
    ext x
    simp [VectorField.mlieBracket_add_left (W := Y) (hZ x) (hZ' x)]
  simp only [rhs_aux_addX, h, h', Pi.add_apply, Pi.sub_apply]
  rw [rhs_aux_addY, rhs_aux_addZ] <;> try assumption
  rw [product_add_left, product_add_right, product_add_right]
  simp only [Pi.add_apply]
  abel

lemma leviCivita_rhs_addZ [CompleteSpace E]
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
    leviCivita_rhs I X Y (Z + Z') = leviCivita_rhs I X Y Z + leviCivita_rhs I X Y Z' := by
  sorry -- divide previous equation by two

lemma leviCivita_rhs_smulZ [CompleteSpace E] {f : M → ℝ} (hf : MDiff f) (hZ : MDiff (T% Z)) :
    leviCivita_rhs I X Y (f • Z) = f • leviCivita_rhs I X Y Z := by
  simp only [leviCivita_rhs, leviCivita_rhs']
  simp [rhs_aux_smulX]--, rhs_aux_smulY, rhs_aux_smulZ]
  ext x
  simp only [Pi.mul_apply, Pi.add_apply]
  have h1 : VectorField.mlieBracket I X (f • Z) =
      f • VectorField.mlieBracket I X Z + (fun x ↦ mfderiv I 𝓘(ℝ, ℝ) f x (X x)) • Z := by
    ext x
    rw [VectorField.mlieBracket_smul_right (hf x) (hZ x), add_comm]
    simp
  have h2 : VectorField.mlieBracket I (f • Z) Y =
      -(fun x ↦ mfderiv I 𝓘(ℝ, ℝ) f x (Y x)) • Z + f • VectorField.mlieBracket I Z Y := by
    ext x
    rw [VectorField.mlieBracket_smul_left (hf x) (hZ x)]
    simp
  simp only [h1, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul, h2]
  set A := rhs_aux I X Y Z x
  set B := rhs_aux I Y Z X x
  set C := rhs_aux I Z X Y x
  set D := (fun x ↦ (mfderiv I 𝓘(ℝ, ℝ) f x) (X x)) • Z

  rw [product_add_right, product_add_right]
  -- These are all science fiction, and not fully true!
  rw [product_smul_left, product_smul_right, product_smul_right]
  set E := ⟪Z, VectorField.mlieBracket I X Y⟫
  set F := ⟪Y, VectorField.mlieBracket I X Z⟫
  set G := ⟪X, VectorField.mlieBracket I Z Y⟫
  -- apart from science fiction mistakes, this is "an easy computation"
  simp; abel_nf
  sorry

end leviCivita_rhs

variable (X Y Z) in
lemma aux (h : cov.IsLeviCivitaConnection) : rhs_aux I X Y Z =
    ⟪cov X Y, Z⟫ + ⟪Y, cov Z X⟫ + ⟪Y, VectorField.mlieBracket I X Z⟫ := by
  trans ⟪cov X Y, Z⟫ + ⟪Y, cov X Z⟫
  · ext x
    exact h.1 X Y Z x
  · simp [← isTorsionFree_iff.mp h.2 X Z, product_sub_right]

lemma isolate_aux {α : Type*} [AddCommGroup α]
    (A D E F X Y Z : α) (h : X + Y - Z = A + A + D + E - F) :
    A + A = X + Y - Z - D - E + F := by
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
  have : rhs_aux I X Y Z + rhs_aux I Y Z X - rhs_aux I Z X Y = A + A + D + E - F := by
    rw [eq1, eq2, eq3]; abel

  -- solve for ⟪cov X Y, Z⟫ and obtain the claim
  simp only [leviCivita_rhs] -- - D - E + F
  ext x
  have almost := isolate_aux A D E F (rhs_aux I X Y Z) (rhs_aux I Y Z X) (rhs_aux I Z X Y)
    (by simp [this])
  sorry -- obvious: if A + A = stuff, A = 1/2 stuff

-- TODO: move to Data.Fintype.EquivFin
/-- Choose an arbitrary linear order on a `Fintype`: this is not an instance because in most
situations, choosing a linear order extending a given preorder, or a particular linear order
is preferred over choosing *any* linear order. -/
noncomputable def Fintype.instLinearOrder {α : Type*} [Fintype α] : LinearOrder α :=
  LinearOrder.lift' _ (Fintype.equivFin α).injective

section

attribute [local instance] Fintype.toOrderBot Fintype.toLocallyFiniteOrder Fintype.instLinearOrder

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

variable {I} in
/-- If two vector fields `X` and `X'` on `M` satisfy the relation `⟨X, Z⟩ = ⟨X', Z⟩` for all
vector fields `Z`, then `X = X'`. XXX up to differentiability? -/
-- TODO: is this true if E is infinite-dimensional? trace the origin of the `Fintype` assumptions!
lemma congr_of_forall_product [FiniteDimensional ℝ E]
    (h : ∀ Z : Π x : M, TangentSpace I x, ⟪X, Z⟫ = ⟪X', Z⟫) : X = X' := by
  by_cases hE : Subsingleton E
  · sorry
  ext x
  letI b := Basis.ofVectorSpace ℝ E
  letI t := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := by
    by_contra!
    have : IsEmpty ↑(Basis.ofVectorSpaceIndex ℝ E) := not_nonempty_iff.mp this
    have : Subsingleton E := by
      sorry
    apply hE this
  haveI : LocallyFiniteOrderBot ↑(Basis.ofVectorSpaceIndex ℝ E) := inferInstance

  -- Choose an orthonormal frame (s i) near x w.r.t. to this trivialisation, and the metric g
  let real := b.orthonormalFrame t
  have hframe := b.orthonormalFrame_isOrthonormalFrameOn t (F := E) (IB := I) (n := 1)
  rw [hframe.eq_iff_repr hx]
  intro i
  have h₁ : ⟪X, real i⟫ x = (hframe.repr i) X x := by
    rw [hframe.repr_eq_inner' _ hx]
    simp [real, real_inner_comm]
  have h₂ : ⟪X', real i⟫ x = (hframe.repr i) X' x := by
    rw [hframe.repr_eq_inner' _ hx]
    simp [real, real_inner_comm]
  -- this would work, except that h is unapplied, but my results are applied...
  --simp_rw [hframe'.repr_eq_inner' _ hx]
  --specialize h (real i)
  --simp [real_inner_comm]
  rw [← h₁, ← h₂, h (real i)]

/-- The Levi-Civita connection on `(M, g)` is uniquely determined,
at least on differentiable vector fields. -/
-- (probably not everywhere, as addition rules apply only for differentiable vector fields?)
theorem isLeviCivita_uniqueness [FiniteDimensional ℝ E]
    {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection) :
    -- almost, only agree on smooth functions
    cov = cov' := by
  ext X σ x
  apply congrFun
  apply congr_of_forall_product fun Z ↦ ?_
  trans leviCivita_rhs I X σ Z
  · exact cov.isLeviCivitaConnection_uniqueness_aux I X σ Z hcov
  · exact (cov'.isLeviCivitaConnection_uniqueness_aux I X σ Z hcov').symm

noncomputable def lcCandidate_aux [FiniteDimensional ℝ E]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e] :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) → (x : M) → TangentSpace I x :=
  fun X Y x ↦
  -- Choose a trivialisation of TM near x.
  letI b := Basis.ofVectorSpace ℝ E
  -- Case distinction: if E is trivial, there is only one choice anyway;
  -- otherwise, b must be non-trivial.
  have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := sorry
  have : Fintype ↑(Basis.ofVectorSpaceIndex ℝ E) := by infer_instance
  haveI : LocallyFiniteOrderBot ↑(Basis.ofVectorSpaceIndex ℝ E) := inferInstance
  letI frame := b.orthonormalFrame e
  -- The coefficient of the desired tangent vector ∇ X Y x w.r.t. s i
  -- is given by leviCivita_rhs X Y s i.
  ∑ i, ((leviCivita_rhs I X Y (frame i)) x) • (frame i x)

variable (M) in
-- TODO: make g part of the notation!
/-- Given two vector fields X and Y on TM, compute
the candidate definition for the Levi-Civita connection on `TM`. -/
noncomputable def lcCandidate [FiniteDimensional ℝ E] :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  -- Use the preferred trivialisation at x to write down a candidate for the existence.
  -- to write down a candidate for the existence.
  fun X Y x ↦ lcCandidate_aux I (trivializationAt E (TangentSpace I : M → Type _) x) X Y x

variable (X Y) in
-- The above definition behaves well: for each compatible trivialisation e,
-- using e on e.baseSet yields the same result as above.
lemma bar [FiniteDimensional ℝ E] (e : Trivialization E (TotalSpace.proj: TangentBundle I M → M))
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet) :
  lcCandidate I M X Y x = lcCandidate_aux I e X Y x := sorry

-- The candidate definition is a covariant derivative on each local frame's domain.
lemma isCovariantDerivativeOn_lcCandidate_aux [FiniteDimensional ℝ E]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e] :
    IsCovariantDerivativeOn E (lcCandidate_aux I (M := M) e) e.baseSet where
  addX X X' σ x := by
    -- these three sorries seem to be necessary!
    have hX : MDiff (T% X) := sorry
    have hX' : MDiff (T% X') := sorry
    have hσ : MDiff (T% σ) := sorry
    intro hx
    unfold lcCandidate_aux
    simp only [← Finset.sum_add_distrib, ← add_smul]
    congr; ext i
    rw [leviCivita_rhs_addX] <;> try assumption
    · abel
    · have : LocallyFiniteOrderBot ↑(Basis.ofVectorSpaceIndex ℝ E) := sorry
      set f := ((Basis.ofVectorSpace ℝ E).orthonormalFrame e i)
      have : MDiffAt (T% f) x := -- missing API lemma!
        (contMDiffAt_orthonormalFrame_of_mem (Basis.ofVectorSpace ℝ E) e i hx)
          |>.mdifferentiableAt le_rfl
      -- TODO: need a local version of leviCivita_rhs_addX!
      sorry
  smulX X σ g x hx := by
    unfold lcCandidate_aux
    dsimp
    have hX : MDiff (T% X) := sorry -- might need this (hopefully not!)
    have hg : MDiff g := sorry -- might need this (hopefully not!)
    rw [Finset.smul_sum]
    congr; ext i
    rw [leviCivita_rhs_smulX _ _ _ _ hg hX]
    simp [← smul_assoc]
  smul_const_σ X σ a x hx := by
    unfold lcCandidate_aux
    dsimp
    rw [Finset.smul_sum]; congr; ext i
    -- want leviCivita_rhs_smulY (with a constant)
    sorry
  addσ X σ σ' x hσ hσ' hx := by
    have hX : MDiff (T% X) := sorry -- missing assumption!
    -- TODO: these should not be necessary with a local version of addY!
    have hσ2 : MDiff (T% σ) := sorry
    have hσ'2 : MDiff (T% σ') := sorry
    unfold lcCandidate_aux
    dsimp
    simp [← Finset.sum_add_distrib, ← add_smul]
    congr; ext i
    rw [leviCivita_rhs_addY] <;> try assumption
    · abel
    · have : LocallyFiniteOrderBot ↑(Basis.ofVectorSpaceIndex ℝ E) := sorry
      set f := ((Basis.ofVectorSpace ℝ E).orthonormalFrame e i)
      have : MDiffAt (T% f) x := -- missing API lemma!
        (contMDiffAt_orthonormalFrame_of_mem (Basis.ofVectorSpace ℝ E) e i hx)
          |>.mdifferentiableAt le_rfl
      -- TODO: need a local version of leviCivita_rhs_addX!
      sorry
  leibniz := by
    sorry

-- The candidate definition is a covariant derivative on each local frame's domain.
lemma isCovariantDerivativeOn_existence_candidate [FiniteDimensional ℝ E]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e] :
    IsCovariantDerivativeOn E (lcCandidate I M) e.baseSet := by
  sorry -- need some IsCovariantDerivativeOn_congr + lemma bar

end

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

-- TODO: make g part of the notation!
variable (M) in
/-- A choice of Levi-Civita connection on the tangent bundle `TM` of a Riemannian manifold `(M, g)`:
this is unique up to the value on non-differentiable vector fields.
If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead. -/
noncomputable def LeviCivitaConnection [FiniteDimensional ℝ E] :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  -- This is the existence part of the proof: take the formula derived above
  -- and prove it satisfies all the conditions.
  toFun := lcCandidate I M
  isCovariantDerivativeOn := by
    rw [← iUnion_source_chartAt H M]
    let t := fun x ↦ trivializationAt E (TangentSpace I : M → Type _) x
    apply IsCovariantDerivativeOn.iUnion (s := fun i ↦ (t i).baseSet) fun i ↦ ?_
    apply isCovariantDerivativeOn_existence_candidate I _

lemma baz [FiniteDimensional ℝ E] : (LeviCivitaConnection I M).IsLeviCivitaConnection := by
  refine ⟨?_, ?_⟩
  · sorry -- compatible
  · sorry -- torsion-free

end CovariantDerivative
