/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module field_theory.is_alg_closed.algebraic_closure
! leanprover-community/mathlib commit df76f43357840485b9d04ed5dee5ab115d420e87
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.DirectLimit
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Algebraic Closure

In this file we construct the algebraic closure of a field

## Main Definitions

- `algebraic_closure k` is an algebraic closure of `k` (in the same universe).
  It is constructed by taking the polynomial ring generated by indeterminates `x_f`
  corresponding to monic irreducible polynomials `f` with coefficients in `k`, and quotienting
  out by a maximal ideal containing every `f(x_f)`, and then repeating this step countably
  many times. See Exercise 1.13 in Atiyah--Macdonald.

## Tags

algebraic closure, algebraically closed
-/


universe u v w

noncomputable section

open scoped Classical BigOperators Polynomial

open Polynomial

variable (k : Type u) [Field k]

namespace AlgebraicClosure

open MvPolynomial

/-- The subtype of monic irreducible polynomials -/
@[reducible]
def MonicIrreducible : Type u :=
  { f : k[X] // Monic f ∧ Irreducible f }
#align algebraic_closure.monic_irreducible AlgebraicClosure.MonicIrreducible

/-- Sends a monic irreducible polynomial `f` to `f(x_f)` where `x_f` is a formal indeterminate. -/
def evalXSelf (f : MonicIrreducible k) : MvPolynomial (MonicIrreducible k) k :=
  Polynomial.eval₂ MvPolynomial.C (X f) f
set_option linter.uppercaseLean3 false in
#align algebraic_closure.eval_X_self AlgebraicClosure.evalXSelf

/-- The span of `f(x_f)` across monic irreducible polynomials `f` where `x_f` is an
indeterminate. -/
def spanEval : Ideal (MvPolynomial (MonicIrreducible k) k) :=
  Ideal.span <| Set.range <| evalXSelf k
#align algebraic_closure.span_eval AlgebraicClosure.spanEval

/-- Given a finset of monic irreducible polynomials, construct an algebra homomorphism to the
splitting field of the product of the polynomials sending each indeterminate `x_f` represented by
the polynomial `f` in the finset to a root of `f`. -/
def toSplittingField (s : Finset (MonicIrreducible k)) :
    MvPolynomial (MonicIrreducible k) k →ₐ[k] SplittingField (∏ x in s, x : k[X]) :=
  MvPolynomial.aeval fun f =>
    if hf : f ∈ s then
      rootOfSplits _
        ((splits_prod_iff _ fun (j : MonicIrreducible k) _ => j.2.2.ne_zero).1
          (SplittingField.splits _) f hf)
        (mt isUnit_iff_degree_eq_zero.2 f.2.2.not_unit)
    else 37
#align algebraic_closure.to_splitting_field AlgebraicClosure.toSplittingField

theorem toSplittingField_evalXSelf {s : Finset (MonicIrreducible k)} {f} (hf : f ∈ s) :
    toSplittingField k s (evalXSelf k f) = 0 := by
  rw [toSplittingField, evalXSelf, ← AlgHom.coe_toRingHom, hom_eval₂, AlgHom.coe_toRingHom,
    MvPolynomial.aeval_X, dif_pos hf, ← algebraMap_eq, AlgHom.comp_algebraMap]
  exact map_rootOfSplits _ _ _
set_option linter.uppercaseLean3 false in
#align algebraic_closure.to_splitting_field_eval_X_self AlgebraicClosure.toSplittingField_evalXSelf

theorem spanEval_ne_top : spanEval k ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one, spanEval, Ideal.span, ← Set.image_univ,
    Finsupp.mem_span_image_iff_total]
  rintro ⟨v, _, hv⟩
  replace hv := congr_arg (toSplittingField k v.support) hv
  rw [AlgHom.map_one, Finsupp.total_apply, Finsupp.sum, AlgHom.map_sum, Finset.sum_eq_zero] at hv
  · exact zero_ne_one hv
  intro j hj
  rw [smul_eq_mul, AlgHom.map_mul, toSplittingField_evalXSelf (s := v.support) hj,
    MulZeroClass.mul_zero]
#align algebraic_closure.span_eval_ne_top AlgebraicClosure.spanEval_ne_top

/-- A random maximal ideal that contains `span_eval k` -/
def maxIdeal : Ideal (MvPolynomial (MonicIrreducible k) k) :=
  Classical.choose <| Ideal.exists_le_maximal _ <| spanEval_ne_top k
#align algebraic_closure.max_ideal AlgebraicClosure.maxIdeal

instance maxIdeal.isMaximal : (maxIdeal k).IsMaximal :=
  (Classical.choose_spec <| Ideal.exists_le_maximal _ <| spanEval_ne_top k).1
#align algebraic_closure.max_ideal.is_maximal AlgebraicClosure.maxIdeal.isMaximal

theorem le_maxIdeal : spanEval k ≤ maxIdeal k :=
  (Classical.choose_spec <| Ideal.exists_le_maximal _ <| spanEval_ne_top k).2
#align algebraic_closure.le_max_ideal AlgebraicClosure.le_maxIdeal

/-- The first step of constructing `algebraic_closure`: adjoin a root of all monic polynomials -/
def AdjoinMonic : Type u :=
  MvPolynomial (MonicIrreducible k) k ⧸ maxIdeal k
#align algebraic_closure.adjoin_monic AlgebraicClosure.AdjoinMonic

instance AdjoinMonic.field : Field (AdjoinMonic k) :=
  Ideal.Quotient.field _
#align algebraic_closure.adjoin_monic.field AlgebraicClosure.AdjoinMonic.field

instance AdjoinMonic.inhabited : Inhabited (AdjoinMonic k) :=
  ⟨37⟩
#align algebraic_closure.adjoin_monic.inhabited AlgebraicClosure.AdjoinMonic.inhabited

/-- The canonical ring homomorphism to `adjoin_monic k`. -/
def toAdjoinMonic : k →+* AdjoinMonic k :=
  (Ideal.Quotient.mk _).comp C
#align algebraic_closure.to_adjoin_monic AlgebraicClosure.toAdjoinMonic

instance AdjoinMonic.algebra : Algebra k (AdjoinMonic k) :=
  (toAdjoinMonic k).toAlgebra
#align algebraic_closure.adjoin_monic.algebra AlgebraicClosure.AdjoinMonic.algebra

theorem AdjoinMonic.algebraMap : algebraMap k (AdjoinMonic k) = (Ideal.Quotient.mk _).comp
  (C : k →+* MvPolynomial (MonicIrreducible k) k) := rfl
#align algebraic_closure.adjoin_monic.algebra_map AlgebraicClosure.AdjoinMonic.algebraMap

theorem AdjoinMonic.isIntegral (z : AdjoinMonic k) : IsIntegral k z := by
  let ⟨p, hp⟩ := Ideal.Quotient.mk_surjective z
  rw [← hp]
  induction p using MvPolynomial.induction_on generalizing z with
    | h_C => exact isIntegral_algebraMap
    | h_add _ _ ha hb => exact isIntegral_add (ha _ rfl) (hb _ rfl)
    | h_X p f ih =>
      · refine @isIntegral_mul k _ _ _ _ _ (Ideal.Quotient.mk (maxIdeal k) _) (ih _ rfl) ?_
        refine ⟨f, f.2.1, ?_⟩
        erw [AdjoinMonic.algebraMap, ← hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
        exact le_maxIdeal k (Ideal.subset_span ⟨f, rfl⟩)
#align algebraic_closure.adjoin_monic.is_integral AlgebraicClosure.AdjoinMonic.isIntegral

theorem AdjoinMonic.exists_root {f : k[X]} (hfm : f.Monic) (hfi : Irreducible f) :
    ∃ x : AdjoinMonic k, f.eval₂ (toAdjoinMonic k) x = 0 :=
  ⟨Ideal.Quotient.mk _ <| X (⟨f, hfm, hfi⟩ : MonicIrreducible k), by
    rw [toAdjoinMonic, ← hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact le_maxIdeal k (Ideal.subset_span <| ⟨_, rfl⟩)⟩
#align algebraic_closure.adjoin_monic.exists_root AlgebraicClosure.AdjoinMonic.exists_root

/-- The `n`th step of constructing `algebraic_closure`, together with its `field` instance. -/
def stepAux (n : ℕ) : Σ α : Type u, Field α :=
  Nat.recOn n ⟨k, inferInstance⟩ fun _ ih => ⟨@AdjoinMonic ih.1 ih.2, @AdjoinMonic.field ih.1 ih.2⟩
#align algebraic_closure.step_aux AlgebraicClosure.stepAux

/-- The `n`th step of constructing `algebraic_closure`. -/
def Step (n : ℕ) : Type u :=
  (stepAux k n).1
#align algebraic_closure.step AlgebraicClosure.Step

-- Porting note: added during the port to help in the proof of `Step.isIntegral` below.
theorem Step.zero : Step k 0 = k := rfl

instance Step.field (n : ℕ) : Field (Step k n) :=
  (stepAux k n).2
#align algebraic_closure.step.field AlgebraicClosure.Step.field

-- Porting note: added during the port to help in the proof of `Step.isIntegral` below.
theorem Step.succ (n : ℕ) : Step k (n + 1) = AdjoinMonic (Step k n) := rfl

instance Step.inhabited (n) : Inhabited (Step k n) :=
  ⟨37⟩
#align algebraic_closure.step.inhabited AlgebraicClosure.Step.inhabited

/-- The canonical inclusion to the `0`th step. -/
def toStepZero : k →+* Step k 0 :=
  RingHom.id k
#align algebraic_closure.to_step_zero AlgebraicClosure.toStepZero

set_option maxHeartbeats 210000 in
/-- The canonical ring homomorphism to the next step. -/
def toStepSucc (n : ℕ) : Step k n →+* (Step k (n + 1)) :=
  @toAdjoinMonic (Step k n) (Step.field k n)
#align algebraic_closure.to_step_succ AlgebraicClosure.toStepSucc

instance Step.algebraSucc (n) : Algebra (Step k n) (Step k (n + 1)) :=
  (toStepSucc k n).toAlgebra
#align algebraic_closure.step.algebra_succ AlgebraicClosure.Step.algebraSucc

theorem toStepSucc.exists_root {n} {f : Polynomial (Step k n)} (hfm : f.Monic)
    (hfi : Irreducible f) : ∃ x : Step k (n + 1), f.eval₂ (toStepSucc k n) x = 0 := by
-- Porting note: original proof was `@AdjoinMonic.exists_root _ (Step.field k n) _ hfm hfi`,
-- but it timeouts.
  obtain ⟨x, hx⟩ := @AdjoinMonic.exists_root _ (Step.field k n) _ hfm hfi
-- Porting note: using `hx` instead of `by apply hx` timeouts.
  exact ⟨x, by apply hx⟩
#align algebraic_closure.to_step_succ.exists_root AlgebraicClosure.toStepSucc.exists_root

-- Porting note: the following two declarations were added during the port to be used in the
-- definition of toStepOfLE
private def toStepOfLE' (m n : ℕ) (h : m ≤ n) : Step k m → Step k n :=
Nat.leRecOn h @fun a => toStepSucc k a

private theorem toStepOfLE'.succ (m n : ℕ) (h : m ≤ n) :
    toStepOfLE' k m (Nat.succ n) (h.trans n.le_succ) =
    (toStepSucc k n) ∘ toStepOfLE' k m n h := by
  ext x
  convert Nat.leRecOn_succ h x
  exact h.trans n.le_succ

/-- The canonical ring homomorphism to a step with a greater index. -/
def toStepOfLE (m n : ℕ) (h : m ≤ n) : Step k m →+* Step k n where
  toFun := toStepOfLE' k m n h
  map_one' := by
-- Porting note: original proof was `induction' h with n h ih; · exact Nat.leRecOn_self 1`
--                                   `rw [Nat.leRecOn_succ h, ih, RingHom.map_one]`
    induction' h with a h ih
    · exact Nat.leRecOn_self 1
    · rw [toStepOfLE'.succ k m a h]; simp [ih]
  map_mul' x y := by
-- Porting note: original proof was `induction' h with n h ih; · simp_rw [Nat.leRecOn_self]`
--                                   `simp_rw [Nat.leRecOn_succ h, ih, RingHom.map_mul]`
    induction' h with a h ih
    · dsimp [toStepOfLE']; simp_rw [Nat.leRecOn_self]
    · simp_rw [toStepOfLE'.succ k m a h]; simp only at ih; simp [ih]
-- Porting note: original proof was `induction' h with n h ih; · exact Nat.leRecOn_self 0`
--                                   `rw [Nat.leRecOn_succ h, ih, RingHom.map_zero]`
  map_zero' := by
    induction' h with a h ih
    · exact Nat.leRecOn_self 0
    · simp_rw [toStepOfLE'.succ k m a h]; simp only at ih; simp [ih]
  map_add' x y := by
-- Porting note: original proof was `induction' h with n h ih; · simp_rw [Nat.leRecOn_self]`
--                                   `simp_rw [Nat.leRecOn_succ h, ih, RingHom.map_add]`
    induction' h with a h ih
    · dsimp [toStepOfLE']; simp_rw [Nat.leRecOn_self]
    · simp_rw [toStepOfLE'.succ k m a h]; simp only at ih; simp [ih]
#align algebraic_closure.to_step_of_le AlgebraicClosure.toStepOfLE

@[simp]
theorem coe_toStepOfLE (m n : ℕ) (h : m ≤ n) :
    (toStepOfLE k m n h : Step k m → Step k n) = Nat.leRecOn h @fun n => toStepSucc k n :=
  rfl
#align algebraic_closure.coe_to_step_of_le AlgebraicClosure.coe_toStepOfLE

instance Step.algebra (n) : Algebra k (Step k n) :=
  (toStepOfLE k 0 n n.zero_le).toAlgebra
#align algebraic_closure.step.algebra AlgebraicClosure.Step.algebra

instance Step.scalar_tower (n) : IsScalarTower k (Step k n) (Step k (n + 1)) :=
  IsScalarTower.of_algebraMap_eq fun z =>
    @Nat.leRecOn_succ (Step k) 0 n n.zero_le (n + 1).zero_le (@fun n => toStepSucc k n) z
#align algebraic_closure.step.scalar_tower AlgebraicClosure.Step.scalar_tower

theorem Step.isIntegral (n) : ∀ z : Step k n, IsIntegral k z := by
  induction' n with a h
  · intro z
    exact isIntegral_algebraMap
  · change RingHom.IsIntegral _
    rw [IsScalarTower.algebraMap_eq k (Step k a) (Step k (a + 1))]
    have H1 := RingHom.algebraMap_toAlgebra (toStepOfLE k 0 a a.zero_le)
    have H2 := RingHom.algebraMap_toAlgebra (toStepSucc k a)
    simp_rw [Step.zero] at H1
    have H3 : (toStepOfLE k 0 a a.zero_le).IsIntegral := fun z => h z
    have H4 : (toStepSucc k a).IsIntegral := by
      intro z
      have := AdjoinMonic.isIntegral (Step k a) (z : Step k (a + 1))
      rw [IsIntegral] at this
      simp_rw [← Step.succ] at this
      sorry-- `convert this` works with `2000000` heartbeats
    sorry -- `convert RingHom.isIntegral_trans _ _ H3 H4` works with `2000000` heartbeats

#align algebraic_closure.step.is_integral AlgebraicClosure.Step.isIntegral


instance toStepOfLE.directedSystem : DirectedSystem (Step k) fun i j h => toStepOfLE k i j h :=
  ⟨fun _ x _ => Nat.leRecOn_self x, fun h₁₂ h₂₃ x => (Nat.leRecOn_trans h₁₂ h₂₃ x).symm⟩
#align algebraic_closure.to_step_of_le.directed_system AlgebraicClosure.toStepOfLE.directedSystem

end AlgebraicClosure

/-- The canonical algebraic closure of a field, the direct limit of adding roots to the field for
each polynomial over the field. -/
def AlgebraicClosure : Type u :=
  Ring.DirectLimit (AlgebraicClosure.Step k) fun i j h => AlgebraicClosure.toStepOfLE k i j h
#align algebraic_closure AlgebraicClosure

namespace AlgebraicClosure

instance : Field (AlgebraicClosure k) :=
  Field.DirectLimit.field _ _

instance : Inhabited (AlgebraicClosure k) :=
  ⟨37⟩

/-- The canonical ring embedding from the `n`th step to the algebraic closure. -/
def ofStep (n : ℕ) : Step k n →+* AlgebraicClosure k :=
  Ring.DirectLimit.of _ _ _
#align algebraic_closure.of_step AlgebraicClosure.ofStep

instance algebraOfStep (n) : Algebra (Step k n) (AlgebraicClosure k) :=
  (ofStep k n).toAlgebra
#align algebraic_closure.algebra_of_step AlgebraicClosure.algebraOfStep

theorem ofStep_succ (n : ℕ) : (ofStep k (n + 1)).comp (toStepSucc k n) = ofStep k n :=
  RingHom.ext fun x =>
    show Ring.DirectLimit.of (Step k) (fun i j h => toStepOfLE k i j h) _ _ = _ by
      convert Ring.DirectLimit.of_f n.le_succ x; ext x; exact (Nat.leRecOn_succ' x).symm
#align algebraic_closure.of_step_succ AlgebraicClosure.ofStep_succ

theorem exists_ofStep (z : AlgebraicClosure k) : ∃ n x, ofStep k n x = z :=
  Ring.DirectLimit.exists_of z
#align algebraic_closure.exists_of_step AlgebraicClosure.exists_ofStep

-- slow
theorem exists_root {f : Polynomial (AlgebraicClosure k)} (hfm : f.Monic) (hfi : Irreducible f) :
    ∃ x : AlgebraicClosure k, f.eval x = 0 := by
  have : ∃ n p, Polynomial.map (ofStep k n) p = f := by
    convert Ring.DirectLimit.Polynomial.exists_of f
  obtain ⟨n, p, rfl⟩ := this
  rw [monic_map_iff] at hfm
  have := hfm.irreducible_of_irreducible_map (ofStep k n) p hfi
  obtain ⟨x, hx⟩ := to_step_succ.exists_root k hfm this
  refine' ⟨ofStep k (n + 1) x, _⟩
  rw [← ofStep_succ k n, eval_map, ← hom_eval₂, hx, RingHom.map_zero]
#align algebraic_closure.exists_root AlgebraicClosure.exists_root

instance instIsAlgClosed : IsAlgClosed (AlgebraicClosure k) :=
  IsAlgClosed.of_exists_root _ fun f => exists_root k
#align algebraic_closure.is_alg_closed AlgebraicClosure.instIsAlgClosed

instance {R : Type _} [CommSemiring R] [alg : Algebra R k] : Algebra R (AlgebraicClosure k) :=
  ((ofStep k 0).comp (@algebraMap _ _ _ _ alg)).toAlgebra

theorem algebraMap_def {R : Type _} [CommSemiring R] [alg : Algebra R k] :
    algebraMap R (AlgebraicClosure k) = (ofStep k 0 : k →+* _).comp (@algebraMap _ _ _ _ alg) :=
  rfl
#align algebraic_closure.algebra_map_def AlgebraicClosure.algebraMap_def

instance {R S : Type _} [CommSemiring R] [CommSemiring S] [Algebra R S] [Algebra S k] [Algebra R k]
    [IsScalarTower R S k] : IsScalarTower R S (AlgebraicClosure k) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    RingHom.congr_arg _ (IsScalarTower.algebraMap_apply R S k x : _)

/-- Canonical algebra embedding from the `n`th step to the algebraic closure. -/
def ofStepHom (n) : Step k n →ₐ[k] AlgebraicClosure k :=
  { ofStep k n with commutes' := fun x => Ring.DirectLimit.of_f n.zero_le x }
#align algebraic_closure.of_step_hom AlgebraicClosure.ofStepHom

theorem isAlgebraic : Algebra.IsAlgebraic k (AlgebraicClosure k) := fun z =>
  isAlgebraic_iff_isIntegral.2 <|
    let ⟨n, x, hx⟩ := exists_ofStep k z
    hx ▸ map_isIntegral (ofStepHom k n) (Step.isIntegral k n x)
#align algebraic_closure.is_algebraic AlgebraicClosure.isAlgebraic

instance : IsAlgClosure k (AlgebraicClosure k) :=
  ⟨AlgebraicClosure.instIsAlgClosed k, isAlgebraic k⟩

end AlgebraicClosure
