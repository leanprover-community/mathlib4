/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Multiset.Fintype
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Algebraic Closure

In this file we construct the algebraic closure of a field

## Main Definitions

- `AlgebraicClosure k` is an algebraic closure of `k` (in the same universe).
  It is constructed by taking the polynomial ring generated by indeterminates
  $X_{f,1}, \dots, X_{f,\deg f}$ corresponding to roots of monic irreducible
  polynomials `f` with coefficients in `k`, and quotienting out by a maximal
  ideal containing every $f - \prod_i (X - X_{f,i})$. The proof follows
  https://kconrad.math.uconn.edu/blurbs/galoistheory/algclosureshorter.pdf.

## Tags

algebraic closure, algebraically closed
-/

universe u v w

noncomputable section

open Polynomial

variable (k : Type u) [Field k]

namespace AlgebraicClosure

/-- The subtype of monic polynomials. -/
def Monics : Type u := {f : k[X] // f.Monic}

/-- `Vars k` provides `n` variables $X_{f,1}, \dots, X_{f,n}$ for each monic polynomial
`f : k[X]` of degree `n`. -/
def Vars : Type u := Σ f : Monics k, Fin f.1.natDegree

variable {k} in
/-- Given a monic polynomial `f : k[X]`,
`subProdXSubC f` is the polynomial $f - \prod_i (X - X_{f,i})$. -/
def subProdXSubC (f : Monics k) : (MvPolynomial (Vars k) k)[X] :=
  f.1.map (algebraMap _ _) - ∏ i : Fin f.1.natDegree, (X - C (MvPolynomial.X ⟨f, i⟩))

/-- The span of all coefficients of `subProdXSubC f` as `f` ranges all polynomials in `k[X]`. -/
def spanCoeffs : Ideal (MvPolynomial (Vars k) k) :=
  Ideal.span <| Set.range fun fn : Monics k × ℕ ↦ (subProdXSubC fn.1).coeff fn.2

variable {k}

/-- If a monic polynomial `f : k[X]` splits in `K`,
then it has as many roots (counting multiplicity) as its degree. -/
def finEquivRoots {K} [Field K] [DecidableEq K] {i : k →+* K} {f : Monics k} (hf : f.1.Splits i) :
    Fin f.1.natDegree ≃ (f.1.map i).roots.toEnumFinset :=
  .symm <| Finset.equivFinOfCardEq <| by
    rwa [← splits_id_iff_splits, splits_iff_card_roots,
      ← Multiset.card_toEnumFinset, f.2.natDegree_map] at hf

lemma Monics.splits_finsetProd {s : Finset (Monics k)} {f : Monics k} (hf : f ∈ s) :
    f.1.Splits (algebraMap k (SplittingField (∏ f ∈ s, f.1))) :=
  (splits_prod_iff _ fun j _ ↦ j.2.ne_zero).1 (SplittingField.splits _) _ hf

open Classical in
/-- Given a finite set of monic polynomials, construct an algebra homomorphism
to the splitting field of the product of the polynomials
sending indeterminates $X_{f_i}$ to the distinct roots of `f`. -/
def toSplittingField (s : Finset (Monics k)) :
    MvPolynomial (Vars k) k →ₐ[k] SplittingField (∏ f ∈ s, f.1) :=
  MvPolynomial.aeval fun fi ↦
    if hf : fi.1 ∈ s then (finEquivRoots (Monics.splits_finsetProd hf) fi.2).1.1 else 37

theorem toSplittingField_coeff {s : Finset (Monics k)} {f} (h : f ∈ s) (n) :
    toSplittingField s ((subProdXSubC f).coeff n) = 0 := by
  classical
  simp_rw [← AlgHom.coe_toRingHom, ← coeff_map, subProdXSubC, Polynomial.map_sub,
    Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, toSplittingField,
    AlgHom.coe_toRingHom, MvPolynomial.aeval_X, dif_pos h,
    ← (finEquivRoots (Monics.splits_finsetProd h)).symm.prod_comp, Equiv.apply_symm_apply]
  rw [Finset.prod_coe_sort (f := fun x : _ × ℕ ↦ X - C x.1), (Multiset.toEnumFinset _)
    |>.prod_eq_multiset_prod, ← Function.comp_def (X - C ·) Prod.fst, ← Multiset.map_map,
    Multiset.map_toEnumFinset_fst, map_map, AlgHom.comp_algebraMap]
  conv in map _ _ => rw [eq_prod_roots_of_splits (Monics.splits_finsetProd h)]
  rw [f.2, map_one, C_1, one_mul, sub_self, coeff_zero]

variable (k)

theorem spanCoeffs_ne_top : spanCoeffs k ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one, spanCoeffs, Ideal.span, ← Set.image_univ,
    Finsupp.mem_span_image_iff_linearCombination]
  rintro ⟨v, _, hv⟩
  classical
  replace hv := congr_arg (toSplittingField <| v.support.image Prod.fst) hv
  rw [map_one, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finset.sum_eq_zero] at hv
  · exact zero_ne_one hv
  intro j hj
  rw [smul_eq_mul, map_mul, toSplittingField_coeff (Finset.mem_image_of_mem _ hj), mul_zero]

/-- A random maximal ideal that contains `spanEval k` -/
def maxIdeal : Ideal (MvPolynomial (Vars k) k) :=
  Classical.choose <| Ideal.exists_le_maximal _ <| spanCoeffs_ne_top k

instance maxIdeal.isMaximal : (maxIdeal k).IsMaximal :=
  (Classical.choose_spec <| Ideal.exists_le_maximal _ <| spanCoeffs_ne_top k).1

theorem le_maxIdeal : spanCoeffs k ≤ maxIdeal k :=
  (Classical.choose_spec <| Ideal.exists_le_maximal _ <| spanCoeffs_ne_top k).2

end AlgebraicClosure

open AlgebraicClosure in
/-- The canonical algebraic closure of a field, the direct limit of adding roots to the field for
each polynomial over the field. -/
@[stacks 09GT]
def AlgebraicClosure : Type u :=
  MvPolynomial (Vars k) k ⧸ maxIdeal k

namespace AlgebraicClosure

instance instCommRing : CommRing (AlgebraicClosure k) := Ideal.Quotient.commRing _
instance instInhabited : Inhabited (AlgebraicClosure k) := ⟨37⟩

instance {S : Type*} [DistribSMul S k] [IsScalarTower S k k] : SMul S (AlgebraicClosure k) :=
  Submodule.Quotient.instSMul' _

instance instAlgebra {R : Type*} [CommSemiring R] [Algebra R k] : Algebra R (AlgebraicClosure k) :=
  Ideal.Quotient.algebra _

instance {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [Algebra S k] [Algebra R k]
    [IsScalarTower R S k] : IsScalarTower R S (AlgebraicClosure k) :=
  Ideal.Quotient.isScalarTower _ _ _

instance instGroupWithZero : GroupWithZero (AlgebraicClosure k) where
  __ := Ideal.Quotient.field _

instance instField : Field (AlgebraicClosure k) where
  __ := instCommRing _
  __ := instGroupWithZero _
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast q := algebraMap k _ q
  ratCast q := algebraMap k _ q
  nnratCast_def q := by change algebraMap k _ _ = _; simp_rw [NNRat.cast_def, map_div₀, map_natCast]
  ratCast_def q := by
    change algebraMap k _ _ = _; rw [Rat.cast_def, map_div₀, map_intCast, map_natCast]
  nnqsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' <| by
    ext; simp [MvPolynomial.algebraMap_eq, NNRat.smul_def]
  qsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' <| by
    ext; simp [MvPolynomial.algebraMap_eq, Rat.smul_def]

theorem Monics.map_eq_prod {f : Monics k} :
    f.1.map (algebraMap k (AlgebraicClosure k)) =
      ∏ i, map (Ideal.Quotient.mk <| maxIdeal k) (X - C (MvPolynomial.X ⟨f, i⟩)) := by
  ext
  dsimp [AlgebraicClosure]
  rw [← Ideal.Quotient.mk_comp_algebraMap, ← map_map, ← Polynomial.map_prod, ← sub_eq_zero,
    ← coeff_sub, ← Polynomial.map_sub, ← subProdXSubC, coeff_map, Ideal.Quotient.eq_zero_iff_mem]
  refine le_maxIdeal _ (Ideal.subset_span ⟨⟨f, _⟩, rfl⟩)

instance isAlgebraic : Algebra.IsAlgebraic k (AlgebraicClosure k) :=
  ⟨fun z =>
    IsIntegral.isAlgebraic <| by
      let ⟨p, hp⟩ := Ideal.Quotient.mk_surjective z
      rw [← hp]
      induction p using MvPolynomial.induction_on generalizing z with
        | h_C => exact isIntegral_algebraMap
        | h_add _ _ ha hb => exact (ha _ rfl).add (hb _ rfl)
        | h_X p fi ih =>
          rw [map_mul]
          refine (ih _ rfl).mul ⟨_, fi.1.2, ?_⟩
          simp_rw [← eval_map, Monics.map_eq_prod, eval_prod, Polynomial.map_sub, eval_sub]
          apply Finset.prod_eq_zero (Finset.mem_univ fi.2)
          erw [map_C, eval_C]
          simp⟩

instance : IsAlgClosure k (AlgebraicClosure k) := .of_splits fun f hf _ ↦ by
  rw [show f = (⟨f, hf⟩ : Monics k) from rfl, ← splits_id_iff_splits, Monics.map_eq_prod]
  exact splits_prod _ fun _ _ ↦ (splits_id_iff_splits _).mpr (splits_X_sub_C _)

instance isAlgClosed : IsAlgClosed (AlgebraicClosure k) := IsAlgClosure.isAlgClosed k

instance [CharZero k] : CharZero (AlgebraicClosure k) :=
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap k (AlgebraicClosure k)))

instance {p : ℕ} [CharP k p] : CharP (AlgebraicClosure k) p :=
  charP_of_injective_algebraMap (RingHom.injective (algebraMap k (AlgebraicClosure k))) p

instance {L : Type*} [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] :
    IsAlgClosure k (AlgebraicClosure L) where
  isAlgebraic := .trans k L _
  isAlgClosed := inferInstance

end AlgebraicClosure
