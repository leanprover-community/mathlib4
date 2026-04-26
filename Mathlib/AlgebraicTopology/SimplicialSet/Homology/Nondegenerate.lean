/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
public import Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Computing homology using nondegenerate simplices

In this file, we introduce the normalized chain complex `X.normalizedChainComplex R`
of a simplicial set `X` with coefficients in `R` (where `R` is an object of a
preadditive category `C` with coproducts). The `n`-chains of this complex
identifies to the coproduct of copies of `R` indexed by the nondegenerate
`n`-simplices of `X`. In particular, we deduce that the homology is zero in degree `≥ d`
when `X` has dimension `< d`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomologicalComplex Simplicial
  AlgebraicTopology.DoldKan

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  (X : SSet.{w}) (R : C)

/-- The normalized chain complex of a simplicial set `X` with coefficients in `R`.
In degree `n`, it consists of a coproduct of copies of `R` indexed by the
nondegenerate `n`-simplices of `X`. -/
noncomputable def normalizedChainComplex : ChainComplex C ℕ :=
  (X.splitting.map (sigmaConst.obj R)).nondegComplex

/-- The split epi `X.chainComplex R ⟶ X.normalizedChainComplex R`. -/
noncomputable def toNormalizedChainComplex : X.chainComplex R ⟶ X.normalizedChainComplex R :=
  (X.splitting.map (sigmaConst.obj R)).toNondegComplex

/-- The split mono `X.normalizedChainComplex R ⟶ X.chainComplex R`. -/
noncomputable def fromNormalizedChainComplex : X.normalizedChainComplex R ⟶ X.chainComplex R :=
  (X.splitting.map (sigmaConst.obj R)).fromNondegComplex

instance : IsSplitEpi (X.toNormalizedChainComplex R) :=
  SimplicialObject.Splitting.isSplitEpi_toNondegComplex _

instance : IsSplitMono (X.fromNormalizedChainComplex R) :=
  SimplicialObject.Splitting.isSplitMono_fromNondegComplex _

@[reassoc (attr := simp)]
lemma fromNormalizedChainComplex_toNormalizedChainComplex :
    X.fromNormalizedChainComplex R ≫ X.toNormalizedChainComplex R = 𝟙 _ :=
  SimplicialObject.Splitting.fromNondegComplex_toNondegComplex _

@[reassoc (attr := simp)]
lemma fromNormalizedChainComplex_f_toNormalizedChainComplex_f (n : ℕ) :
    (X.fromNormalizedChainComplex R).f n ≫ (X.toNormalizedChainComplex R).f n = 𝟙 _ := by
  simp [← HomologicalComplex.comp_f]

@[reassoc (attr := simp)]
lemma toNormalizedChainComplex_fromNormalizedChainComplex :
    X.toNormalizedChainComplex R ≫ X.fromNormalizedChainComplex R = PInfty :=
  SimplicialObject.Splitting.toNondegComplex_fromNondegComplex _

@[reassoc (attr := simp)]
lemma toNormalizedChainComplex_f_fromNormalizedChainComplex_f (n : ℕ) :
    (X.toNormalizedChainComplex R).f n ≫ (X.fromNormalizedChainComplex R).f n = PInfty.f n := by
  simp [← HomologicalComplex.comp_f]

/-- The homotopy equivalence from `X.chainComplex R` to `X.normalizedChainComplex R`. -/
noncomputable def homotopyEquivNormalizedChainComplex :
    HomotopyEquiv (X.chainComplex R) (X.normalizedChainComplex R) :=
  SimplicialObject.Splitting.homotopyEquivNondegComplex _

@[simp]
lemma homotopyEquivNormalizedChainComplex_hom :
    (X.homotopyEquivNormalizedChainComplex R).hom = X.toNormalizedChainComplex R := rfl

@[simp]
lemma homotopyEquivNormalizedChainComplex_inv :
    (X.homotopyEquivNormalizedChainComplex R).inv = X.fromNormalizedChainComplex R := rfl

section

variable {R} {n : ℕ}

/-- The map `R ⟶ (X.normalizedChainComplex R).X n` for any `x : X _⦋n⦌`. Note that
this is zero is `x` is a degenerate simplex, see `ιNormalizedChainComplex_eq_zero`. -/
@[no_expose]
noncomputable def ιNormalizedChainComplex (x : X _⦋n⦌) :
    R ⟶ (X.normalizedChainComplex R).X n :=
  X.ιChainComplex x ≫ (X.toNormalizedChainComplex R).f n

@[reassoc (attr := simp)]
lemma ιChainComplex_toNormalizedChainComplex_f (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (X.toNormalizedChainComplex R).f n =
    X.ιNormalizedChainComplex x := by
  rfl

@[reassoc (attr := simp)]
lemma ιNormalizedChainComplex_d {n : ℕ} (x : X _⦋n + 1⦌) :
    X.ιNormalizedChainComplex x ≫ (X.normalizedChainComplex R).d (n + 1) n =
      ∑ (i : Fin (n + 2)), (-1) ^ i.val • X.ιNormalizedChainComplex (X.δ i x) := by
  simp [ιNormalizedChainComplex, Preadditive.sum_comp,
    -ιChainComplex_toNormalizedChainComplex_f]

@[reassoc]
lemma ιNormalizedChainComplex_fromNondegComplex_f (x : X _⦋n⦌) :
    X.ιNormalizedChainComplex x ≫ (X.fromNormalizedChainComplex R).f n =
      X.ιChainComplex x ≫ (PInfty).f n := by
  dsimp [ιNormalizedChainComplex]
  rw [Category.assoc, toNormalizedChainComplex_f_fromNormalizedChainComplex_f]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma ιNormalizedChainComplex_eq_zero (x : X _⦋n⦌) (hx : x ∈ X.degenerate n) :
    X.ιNormalizedChainComplex (R := R) x = 0 := by
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n), zero_comp,
    ιNormalizedChainComplex_fromNondegComplex_f]
  obtain _ | n := n
  · simp at hx
  · simp only [degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hx
    let X' := ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).obj X
    obtain ⟨i, y, rfl⟩ := hx
    trans X.ιChainComplex y ≫ X'.σ i ≫ (PInfty (X := X')).f _
    · simp [ιChainComplex, X']
    · simp [σ_comp_PInfty X' i]

variable (R n) in
/-- The cofan given by the inclusions
`X.ιNormalizedChainComplex x : R ⟶ (X.normalizedChainComplex R).X n` for all
nondegenerate `n`-simplices `x` of a simplicial set `X`. -/
noncomputable abbrev cofanNormalizedChainComplex : Cofan (fun (_ : X.nonDegenerate n) ↦ R) :=
  Cofan.mk _ (fun x ↦ X.ιNormalizedChainComplex x.val)

set_option backward.isDefEq.respectTransparency false in
variable (R n) in
private lemma ιNormalizedChainComplex_eq_ι (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    X.ιNormalizedChainComplex (R := R) x =
      Sigma.ι (fun (_ : X.nonDegenerate n) ↦ R) ⟨x, hx⟩ := by
  dsimp [ιNormalizedChainComplex, ιChainComplex]
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n), Category.assoc,
    toNormalizedChainComplex_f_fromNormalizedChainComplex_f]
  simp [fromNormalizedChainComplex, SimplicialObject.Splitting.fromNondegComplex_f]

set_option backward.isDefEq.respectTransparency false in
variable (R n) in
/-- `(X.normalizedChainComplex R).X n` identifies to the coproduct of copies
of `R` indexed by the nondegenerate `n`-simplices of the simplicial set `X`. -/
@[no_expose]
noncomputable def isColimitCofanNormalizedChainComplex :
    IsColimit (X.cofanNormalizedChainComplex R n) :=
  IsColimit.ofIsoColimit (coproductIsCoproduct _)
    (Cofan.ext (Iso.refl _) (fun ⟨x, hx⟩ ↦ by
      simpa using (X.ιNormalizedChainComplex_eq_ι R n x hx).symm))

@[ext]
lemma normalizedChainComplex_hom_ext {T : C} {f g : (X.normalizedChainComplex R).X n ⟶ T}
    (h : ∀ (x : X _⦋n⦌) (_ : x ∈ X.nonDegenerate n),
      X.ιNormalizedChainComplex x ≫ f = X.ιNormalizedChainComplex x ≫ g) :
    f = g :=
  (X.isColimitCofanNormalizedChainComplex R n).hom_ext (fun ⟨x, hx⟩ ↦ h x hx)

end

lemma isZero_normalizedChainComplex_X_of_hasDimensionLT (n d : ℕ) [X.HasDimensionLT d]
    (h : d ≤ n := by lia) :
    IsZero ((X.normalizedChainComplex R).X n) := by
  rw [IsZero.iff_id_eq_zero]
  ext x hx
  exact (h.not_gt (X.dim_lt_of_nonDegenerate ⟨x, hx⟩ d)).elim

section

variable [CategoryWithHomology C]

instance : QuasiIso (X.toNormalizedChainComplex R) :=
  (X.homotopyEquivNormalizedChainComplex R).quasiIso_hom

instance : QuasiIso (X.fromNormalizedChainComplex R) :=
  (X.homotopyEquivNormalizedChainComplex R).quasiIso_inv

lemma exactAt_chainComplex_of_hasDimensionLT (n d : ℕ) [X.HasDimensionLT d]
    (h : d ≤ n := by lia) :
    (X.chainComplex R).ExactAt n := by
  rw [exactAt_iff_of_quasiIsoAt (X.toNormalizedChainComplex R)]
  exact .of_isZero (X.isZero_normalizedChainComplex_X_of_hasDimensionLT R n d)

lemma isZero_homology_of_hasDimensionLT (n d : ℕ) [X.HasDimensionLT d]
    (h : d ≤ n := by lia) :
    IsZero (X.homology R n) := by
  rw [← exactAt_iff_isZero_homology]
  exact X.exactAt_chainComplex_of_hasDimensionLT R n d

end

end SSet
