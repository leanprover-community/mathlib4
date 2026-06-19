/-
# Graded differential Lie algebras and the Bianchi identity (ℝ-coefficients)

The purely algebraic content of the Cartan structure equations and Bianchi, with no
manifolds. We assume the laws that genuine 𝔤-valued forms satisfy (exterior derivative `d`,
bracket-wedge `wb`, their compatibility) as a class, and prove Bianchi against it. The
eventual concrete construction -- 𝔤-valued forms as `Ω* ⊗ 𝔤` for a real `LieAlgebra 𝔤` --
becomes an *instance*, at which point everything below specialises with no edits.

Design choices, both learned the hard way:

* **Coefficients are ℝ.** The objects (connections on the real frame bundle, gravity) are
  real; carrying an abstract field buys generality we never spend. Over ℝ the `½` in the
  curvature is free and there is no characteristic side-condition.

* **No abstract graded Jacobi axiom.** Bianchi needs exactly one Jacobi consequence,
  `[[ω∧ω]∧ω] = 0` for a degree-1 form. Axiomatising *full* graded Jacobi and specialising it
  to three equal arguments forces `-3X = 0`, hence a `3 ≠ 0` hypothesis -- an artefact of the
  abstract route. The honest fact lives one level down: in `Ω* ⊗ 𝔤` the cancellation comes
  pointwise from the ordinary Jacobi identity of 𝔤 (the factor of 2 from `[ω∧ω] = 2[ω,ω]`
  multiplies a quantity that is identically zero), division-free, in any characteristic. So we
  take that single identity, `wb_wb_self`, as the interface field; the concrete instance
  discharges it as a theorem.

Degrees live in the type (`A n` = forms of degree `n`). To avoid dependent-type transport,
`wb` is a smart constructor `wb (h : p + q = n) : A p →ₗ A q →ₗ A n` taking a proof of its
output degree, so every law states both sides in one `A n` with no `cast`.

WARNING: uncompiled. The class design and the mathematics I am confident in; the dependent
degree-proof bookkeeping in `bianchi` (proof irrelevance between `wb` terms carrying
different `omega`-generated proofs of the same degree equation) is the likely friction.
Flagged inline.
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic

/-- A graded differential Lie algebra with ℝ-coefficients: an ℕ-graded ℝ-module `A` with an
exterior derivative `d` (degree `+1`, `d² = 0`) and a graded-antisymmetric bracket-wedge `wb`
satisfying a graded Leibniz rule, together with the single Jacobi consequence Bianchi needs. -/
class GradedDiffLieAlg (A : ℕ → Type*)
    [∀ n, AddCommGroup (A n)] [∀ n, Module ℝ (A n)] where
  /-- Exterior derivative, raising degree by one. -/
  d : ∀ {n : ℕ}, A n →ₗ[ℝ] A (n + 1)
  /-- `d² = 0`. (Tu, Prop. 21.6 underlies this; standard `d ∘ d = 0` for forms.) -/
  d_comp_d : ∀ {n : ℕ} (x : A n), d (d x) = 0
  /-- Bracket-wedge `[·∧·]`, landing in the degree named by the proof. -/
  wb : ∀ {p q n : ℕ}, p + q = n → A p →ₗ[ℝ] A q →ₗ[ℝ] A n
  /-- Graded Leibniz: `d[α∧β] = [dα∧β] + (-1)^|α| [α∧dβ]`. (Tu, **Prop. 21.6**.) -/
  d_wb : ∀ {p q n : ℕ} (h : p + q = n) (α : A p) (β : A q),
    d (wb h α β)
      = wb (by omega : p + 1 + q = n + 1) (d α) β
        + (-1 : ℝ) ^ p • wb (by omega : p + (q + 1) = n + 1) α (d β)
  /-- Graded antisymmetry: `[α∧β] = -(-1)^{|α||β|} [β∧α]`. (Tu, **Prop. 21.5**.) -/
  wb_antisymm : ∀ {p q n : ℕ} (h : p + q = n) (α : A p) (β : A q),
    wb h α β = - ((-1 : ℝ) ^ (p * q) • wb (by omega : q + p = n) β α)
  /-- `[[ω∧ω]∧ω] = 0` for a degree-1 form. (Tu, **Problem 21.5**.) In the concrete `Ω* ⊗ 𝔤`
  instance this is a *theorem*, derived division-free from the ordinary Jacobi identity of 𝔤;
  here it is the one Jacobi fact the Bianchi identity consumes. -/
  wb_wb_self : ∀ (ω : A 1),
    wb (by omega : 2 + 1 = 3) (wb (by omega : 1 + 1 = 2) ω ω) ω = 0

namespace GradedDiffLieAlg

variable {A : ℕ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module ℝ (A n)]
  [GradedDiffLieAlg A]

/-- The curvature 2-form `Ω = dω + ½[ω∧ω]` of a connection 1-form `ω`. (Tu, **second
structure equation**, §21/§30 "definition of curvature".) -/
noncomputable def curvature (ω : A 1) : A 2 :=
  d ω + (2 : ℝ)⁻¹ • wb (by omega : 1 + 1 = 2) ω ω

/-- **Bianchi identity** `dΩ = [Ω∧ω]`. (Tu, **(30.2)/§30 part (iii)**; general-Lie-algebra
form. The frame-bundle specialization is Tu **(30.3)**, see `bianchi_matrix`.) Over ℝ, with no
characteristic hypothesis. The proof:
`dΩ = ½ d[ω∧ω] = ½ · 2 [dω∧ω] = [dω∧ω]` (using `d² = 0`, Leibniz, antisymmetry), while
`[Ω∧ω] = [dω∧ω] + ½[[ω∧ω]∧ω] = [dω∧ω]` (using `wb_wb_self`); both sides are `[dω∧ω]`. -/
theorem bianchi (ω : A 1) :
    d (curvature ω) = wb (by omega : 2 + 1 = 3) (curvature ω) ω := by
  -- (1) d[ω∧ω] = 2 • [dω∧ω].
  have hdW : d (wb (by omega : 1 + 1 = 2) ω ω)
      = (2 : ℝ) • wb (by omega : 2 + 1 = 3) (d ω) ω := by
    rw [d_wb (by omega : 1 + 1 = 2) ω ω,
        wb_antisymm (by omega : 1 + 2 = 3) ω (d ω)]
    -- (-1)^1 = -1 ; (-1)^(1*2) = 1, so the second summand is (-1)•(-(1•[dω∧ω])) = [dω∧ω].
    simp only [pow_one, show (1 * 2) = 2 from rfl,
      show ((-1 : ℝ) ^ 2) = 1 from by norm_num, one_smul]
    -- UNTESTED: the two `wb _ (d ω) ω` atoms carry different omega-proofs of `2+1=3`;
    -- they are defeq by proof irrelevance. If `module` does not unify them, replace with
    -- `show _ = _; congr 1` or `convert ... using 2` then `rfl` on the degree goals.
    module
  -- (2) LHS: d(curvature ω) = [dω∧ω].
  have hLHS : d (curvature ω) = wb (by omega : 2 + 1 = 3) (d ω) ω := by
    rw [curvature, map_add, map_smul, d_comp_d, zero_add, hdW, smul_smul]
    norm_num
  -- (3) RHS: [Ω∧ω] = [dω∧ω] + ½[[ω∧ω]∧ω] = [dω∧ω], since [[ω∧ω]∧ω] = 0.
  have hRHS : wb (by omega : 2 + 1 = 3) (curvature ω) ω
      = wb (by omega : 2 + 1 = 3) (d ω) ω := by
    rw [curvature, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        wb_wb_self, smul_zero, add_zero]
  rw [hLHS, hRHS]

end GradedDiffLieAlg

/-- A graded differential Lie algebra whose bracket-wedge is the graded commutator of an
associative graded product `mw` ("matrix-wedge": wedge the form parts, *multiply* the matrix
/ operator coefficients). This models the frame-bundle case: the structure group is
`(E →L[ℝ] E)ˣ`, whose Lie algebra `E →L[ℝ] E` is an *associative* matrix algebra. Writing the
matrix-wedge as `∧` (Bleecker's convention, where the coefficients are multiplied, not
bracketed), the bracket-wedge is its graded commutator: `[α∧β] = α ∧ β - (-1)^{|α||β|} β ∧ α`
(Bleecker 2.2.12; Tu Prop. 21.7). -/
class GradedDiffAssocAlg (A : ℕ → Type*)
    [∀ n, AddCommGroup (A n)] [∀ n, Module ℝ (A n)] extends GradedDiffLieAlg A where
  /-- Associative graded product (matrix multiplication on the algebra factor, wedge on the
  form factor), landing in the degree named by the proof. -/
  mw : ∀ {p q n : ℕ}, p + q = n → A p →ₗ[ℝ] A q →ₗ[ℝ] A n
  /-- The bracket-wedge is the graded commutator of `mw`. (Bleecker 2.2.12; Tu Prop. 21.7:
  for matrix-valued forms, `[α∧β] = α ∧ β - (-1)^{|α||β|} β ∧ α`, where `∧` wedges the forms
  and multiplies the matrix coefficients.) -/
  wb_eq_graded_comm : ∀ {p q n : ℕ} (h : p + q = n) (α : A p) (β : A q),
    wb h α β
      = mw h α β - (-1 : ℝ) ^ (p * q) • mw (by omega : q + p = n) β α

namespace GradedDiffAssocAlg

variable {A : ℕ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module ℝ (A n)]
  [GradedDiffAssocAlg A]

open GradedDiffLieAlg

/-- **Bianchi in matrix-commutator form** (Tu (30.3)): for the frame bundle with associative
(matrix) structure algebra, `dΩ = Ω ∧ ω - ω ∧ Ω` (Bleecker 2.2.13, where `∧` multiplies the
matrix coefficients). Obtained from `bianchi` by unfolding the bracket-wedge `[Ω∧ω]` into the
graded commutator of the matrix-wedge `mw`. With `|Ω| = 2`, `|ω| = 1`, the sign
`(-1)^{2·1} = 1`, so the commutator is `Ω ∧ ω - ω ∧ Ω`. -/
theorem bianchi_matrix (ω : A 1) :
    d (curvature ω)
      = mw (by omega : 2 + 1 = 3) (curvature ω) ω
        - mw (by omega : 1 + 2 = 3) ω (curvature ω) := by
  rw [bianchi ω, wb_eq_graded_comm (by omega : 2 + 1 = 3) (curvature ω) ω]
  -- (-1)^(2*1) = 1, so the second term loses its sign.
  simp only [show (2 * 1) = 2 from rfl, show ((-1 : ℝ) ^ 2) = 1 from by norm_num, one_smul]

end GradedDiffAssocAlg
