/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module field_theory.splitting_field.construction
! leanprover-community/mathlib commit df76f43357840485b9d04ed5dee5ab115d420e87
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.FieldTheory.Normal
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.QuotientOperations

/-!
# Splitting fields

In this file we prove the existence and uniqueness of splitting fields.

## Main definitions

* `polynomial.splitting_field f`: A fixed splitting field of the polynomial `f`.

## Main statements

* `polynomial.is_splitting_field.alg_equiv`: Every splitting field of a polynomial `f` is isomorphic
  to `splitting_field f` and thus, being a splitting field is unique up to isomorphism.

-/


noncomputable section

open scoped Classical BigOperators Polynomial

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}

namespace Polynomial

variable [Field K] [Field L] [Field F]

open Polynomial

section SplittingField

/-- Non-computably choose an irreducible factor from a polynomial. -/
def factor (f : K[X]) : K[X] :=
  if H : ∃ g, Irreducible g ∧ g ∣ f then Classical.choose H else X
#align polynomial.factor Polynomial.factor

theorem irreducible_factor (f : K[X]) : Irreducible (factor f) := by
  rw [factor]
  split_ifs with H
  · exact (Classical.choose_spec H).1
  · exact irreducible_X
#align polynomial.irreducible_factor Polynomial.irreducible_factor

/-- See note [fact non-instances]. -/
theorem fact_irreducible_factor (f : K[X]) : Fact (Irreducible (factor f)) :=
  ⟨irreducible_factor f⟩
#align polynomial.fact_irreducible_factor Polynomial.fact_irreducible_factor

attribute [local instance] fact_irreducible_factor

theorem factor_dvd_of_not_isUnit {f : K[X]} (hf1 : ¬IsUnit f) : factor f ∣ f := by
  by_cases hf2 : f = 0; · rw [hf2]; exact dvd_zero _
  rw [factor, dif_pos (WfDvdMonoid.exists_irreducible_factor hf1 hf2)]
  exact (Classical.choose_spec <| WfDvdMonoid.exists_irreducible_factor hf1 hf2).2
#align polynomial.factor_dvd_of_not_is_unit Polynomial.factor_dvd_of_not_isUnit

theorem factor_dvd_of_degree_ne_zero {f : K[X]} (hf : f.degree ≠ 0) : factor f ∣ f :=
  factor_dvd_of_not_isUnit (mt degree_eq_zero_of_isUnit hf)
#align polynomial.factor_dvd_of_degree_ne_zero Polynomial.factor_dvd_of_degree_ne_zero

theorem factor_dvd_of_natDegree_ne_zero {f : K[X]} (hf : f.natDegree ≠ 0) : factor f ∣ f :=
  factor_dvd_of_degree_ne_zero (mt natDegree_eq_of_degree_eq_some hf)
#align polynomial.factor_dvd_of_nat_degree_ne_zero Polynomial.factor_dvd_of_natDegree_ne_zero

/-- Divide a polynomial f by X - C r where r is a root of f in a bigger field extension. -/
def removeFactor (f : K[X]) : Polynomial (AdjoinRoot <| factor f) :=
  map (AdjoinRoot.of f.factor) f /ₘ (X - C (AdjoinRoot.root f.factor))
#align polynomial.remove_factor Polynomial.removeFactor

set_option maxHeartbeats 300000 in
theorem X_sub_C_mul_removeFactor (f : K[X]) (hf : f.natDegree ≠ 0) :
    (X - C (AdjoinRoot.root f.factor)) * f.removeFactor = map (AdjoinRoot.of f.factor) f := by
  let ⟨g, hg⟩ := factor_dvd_of_natDegree_ne_zero hf
  apply (mul_divByMonic_eq_iff_isRoot
    (R := AdjoinRoot f.factor) (a := AdjoinRoot.root f.factor)).mpr
  rw [IsRoot.def, eval_map, hg, eval₂_mul, ← hg, AdjoinRoot.eval₂_root, MulZeroClass.zero_mul]
set_option linter.uppercaseLean3 false in
#align polynomial.X_sub_C_mul_remove_factor Polynomial.X_sub_C_mul_removeFactor

theorem natDegree_removeFactor (f : K[X]) : f.removeFactor.natDegree = f.natDegree - 1 := by
-- Porting note: `(map (AdjoinRoot.of f.factor) f)` was `_`
  rw [removeFactor, natDegree_divByMonic (map (AdjoinRoot.of f.factor) f) (monic_X_sub_C _),
    natDegree_map, natDegree_X_sub_C]
#align polynomial.nat_degree_remove_factor Polynomial.natDegree_removeFactor

theorem natDegree_removeFactor' {f : K[X]} {n : ℕ} (hfn : f.natDegree = n + 1) :
    f.removeFactor.natDegree = n := by rw [natDegree_removeFactor, hfn, n.add_sub_cancel]
#align polynomial.nat_degree_remove_factor' Polynomial.natDegree_removeFactor'

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors.

Uses recursion on the degree. For better definitional behaviour, structures
including `splitting_field_aux` (such as instances) should be defined using
this recursion in each field, rather than defining the whole tuple through
recursion.
-/
def SplittingFieldAuxAux (n : ℕ) : ∀ {K : Type u} [Field K], ∀ _ : K[X],
    Σ (L : Type u) (_ : Field L), Algebra K L :=
  -- Porting note: added motive
  Nat.recOn (motive := fun (_x : ℕ) => ∀ {K : Type u} [_inst_4 : Field K], K[X] →
      Σ (L : Type u) (_ : Field L), Algebra K L) n
    (fun {K} _ _ => ⟨K, inferInstance, inferInstance⟩)
    fun _ ih _ _ f =>
      let ⟨L, fL, _⟩ := ih f.removeFactor
      ⟨L, fL, (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor)).toAlgebra⟩

def SplittingFieldAux (n : ℕ) {K : Type u} [Field K] (f : K[X]) : Type u :=
  (SplittingFieldAuxAux n f).1
#align polynomial.splitting_field_aux Polynomial.SplittingFieldAux

instance SplittingFieldAux.field (n : ℕ) {K : Type u} [Field K] (f : K[X]) :
    Field (SplittingFieldAux n f) :=
  (SplittingFieldAuxAux n f).2.1

instance SplittingFieldAux.algebra (n : ℕ) {K : Type u} [Field K] (f : K[X]) :
    Algebra K (SplittingFieldAux n f) :=
  (SplittingFieldAuxAux n f).2.2

namespace SplittingFieldAux

theorem succ (n : ℕ) (f : K[X]) :
    SplittingFieldAux (n + 1) f = SplittingFieldAux n f.removeFactor :=
  rfl
#align polynomial.splitting_field_aux.succ Polynomial.SplittingFieldAux.succ

section LiftInstances

#noalign polynomial.splitting_field_aux.zero
#noalign polynomial.splitting_field_aux.add
#noalign polynomial.splitting_field_aux.smul
#noalign polynomial.splitting_field_aux.is_scalar_tower
#noalign polynomial.splitting_field_aux.neg
#noalign polynomial.splitting_field_aux.sub
#noalign polynomial.splitting_field_aux.one
#noalign polynomial.splitting_field_aux.mul
#noalign polynomial.splitting_field_aux.npow
#noalign polynomial.splitting_field_aux.mk
#noalign polynomial.splitting_field_aux.Inv
#noalign polynomial.splitting_field_aux.div
#noalign polynomial.splitting_field_aux.zpow
#noalign polynomial.splitting_field_aux.Field
#noalign polynomial.splitting_field_aux.inhabited
#noalign polynomial.splitting_field_aux.mk_hom
#noalign polynomial.splitting_field_aux.algebra

end LiftInstances

instance algebra''' {n : ℕ} {f : K[X]} :
    Algebra (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor) :=
  SplittingFieldAux.algebra n _
#align polynomial.splitting_field_aux.algebra''' Polynomial.SplittingFieldAux.algebra'''

instance algebra' {n : ℕ} {f : K[X]} : Algebra (AdjoinRoot f.factor) (SplittingFieldAux n.succ f) :=
  SplittingFieldAux.algebra'''
#align polynomial.splitting_field_aux.algebra' Polynomial.SplittingFieldAux.algebra'

instance algebra'' {n : ℕ} {f : K[X]} : Algebra K (SplittingFieldAux n f.removeFactor) :=
  RingHom.toAlgebra (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor))
#align polynomial.splitting_field_aux.algebra'' Polynomial.SplittingFieldAux.algebra''

instance scalar_tower' {n : ℕ} {f : K[X]} :
    IsScalarTower K (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
#align polynomial.splitting_field_aux.scalar_tower' Polynomial.SplittingFieldAux.scalar_tower'

#noalign polynomial.splitting_field_aux.scalar_tower

theorem algebraMap_succ (n : ℕ) (f : K[X]) :
    algebraMap K (SplittingFieldAux (n + 1) f) =
      (algebraMap (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor)).comp
        (AdjoinRoot.of f.factor) :=
  rfl
#align polynomial.splitting_field_aux.algebra_map_succ Polynomial.SplittingFieldAux.algebraMap_succ

protected theorem splits (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (_hfn : f.natDegree = n), Splits (algebraMap K <| SplittingFieldAux n f) f :=
  Nat.recOn (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (_hfn : f.natDegree = n), Splits (algebraMap K <| SplittingFieldAux n f) f) n
    (fun {K} _ _ hf =>
      splits_of_degree_le_one _
        (le_trans degree_le_natDegree <| hf.symm ▸ WithBot.coe_le_coe.2 zero_le_one))
    fun n ih {K} _ f hf => by
    skip;
    rw [← splits_id_iff_splits, algebraMap_succ, ← map_map, splits_id_iff_splits, ←
      X_sub_C_mul_removeFactor f fun h => by rw [h] at hf ; cases hf]
    exact splits_mul _ (splits_X_sub_C _) (ih _ (natDegree_removeFactor' hf))
#align polynomial.splitting_field_aux.splits Polynomial.SplittingFieldAux.splits

#noalign polynomial.splitting_field_aux.exists_lift

set_option maxHeartbeats 400000 in
theorem adjoin_roots (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤ :=
  Nat.recOn (motive := fun n =>
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n),
        Algebra.adjoin K
            (↑(f.map <| algebraMap K <| SplittingFieldAux n f).roots.toFinset :
              Set (SplittingFieldAux n f)) = ⊤)
    n (fun {K} _ f hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩)
    fun n ih {K} _ f hfn => by
    have hndf : f.natDegree ≠ 0 := by intro h; rw [h] at hfn ; cases hfn
    have hfn0 : f ≠ 0 := by intro h; rw [h] at hndf ; exact hndf rfl
    have hmf0 : map (algebraMap K (SplittingFieldAux n.succ f)) f ≠ 0 := map_ne_zero hfn0
    rw [algebraMap_succ, ← map_map, ← X_sub_C_mul_removeFactor _ hndf, Polynomial.map_mul] at hmf0
      ⊢
    rw [roots_mul hmf0, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.toFinset_add,
      Finset.coe_union, Multiset.toFinset_singleton, Finset.coe_singleton,
      Algebra.adjoin_union_eq_adjoin_adjoin, ← Set.image_singleton,
      Algebra.adjoin_algebraMap K (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor),
      AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top]
    /- Porting note: was a `rw [IsScalarTower.adjoin_range_toAlgHom K (AdjoinRoot f.factor)
        (SplittingFieldAux n f.removeFactor)]-/
    have := IsScalarTower.adjoin_range_toAlgHom K (AdjoinRoot f.factor)
        (SplittingFieldAux n f.removeFactor)
        (↑(f.removeFactor.map <| algebraMap (AdjoinRoot f.factor) <|
          SplittingFieldAux n f.removeFactor).roots.toFinset :
              Set (SplittingFieldAux n f.removeFactor))
    refine this.trans ?_
    rw [ih _ (natDegree_removeFactor' hfn), Subalgebra.restrictScalars_top]
#align polynomial.splitting_field_aux.adjoin_roots Polynomial.SplittingFieldAux.adjoin_roots

instance : IsSplittingField K (SplittingFieldAux f.natDegree f) f :=
  ⟨SplittingFieldAux.splits _ _ rfl, SplittingFieldAux.adjoin_roots _ _ rfl⟩

def ofMvPolynomial (f : K[X]) :
    MvPolynomial (f.rootSet (SplittingFieldAux f.natDegree f)) K →ₐ[K]
    SplittingFieldAux f.natDegree f :=
  MvPolynomial.aeval (fun i => i.1)

theorem ofMvPolynomial_surjective (f : K[X]) : Function.Surjective (ofMvPolynomial f) :=
  sorry

def AlgEquivQuotientMvPolynomial (f : K[X]) :
    (MvPolynomial (f.rootSet (SplittingFieldAux f.natDegree f)) K ⧸
      RingHom.ker (ofMvPolynomial f)) ≃ₐ[K]
    SplittingFieldAux f.natDegree f :=
  (Ideal.quotientKerAlgEquivOfSurjective (ofMvPolynomial_surjective f) : _)

end SplittingFieldAux

/-- A splitting field of a polynomial. -/
def SplittingField (f : K[X]) : Type v :=
  MvPolynomial (f.rootSet (SplittingFieldAux f.natDegree f)) K ⧸
    RingHom.ker (SplittingFieldAux.ofMvPolynomial f).toRingHom
#align polynomial.splitting_field Polynomial.SplittingField

namespace SplittingField

variable (f : K[X])

instance commRing : CommRing (SplittingField f) := by
  delta SplittingField; infer_instance

instance inhabited : Inhabited (SplittingField f) :=
  ⟨37⟩
#align polynomial.splitting_field.inhabited Polynomial.SplittingField.inhabited

--Porting note: new instance
instance [CommSemiring S] [DistribSMul S K] [IsScalarTower S K K] : SMul S (SplittingField f) :=
  Submodule.Quotient.hasSmul' _

--Porting note: new instance
instance [DistribSMul S K] [IsScalarTower S K K] : DistribSMul S (AdjoinRoot f) :=
  Submodule.Quotient.distribSmul' _

instance algebra' {R} [CommSemiring R] [Algebra R K] : Algebra R (SplittingField f) := by
  delta SplittingField; infer_instance
#align polynomial.splitting_field.algebra' Polynomial.SplittingField.algebra'

instance : Field (SplittingField f) :=
  { toCommRing := SplittingField.commRing f
    ratCast := fun a => algebraMap K (SplittingField f) (a : K)
    ratCast_mk := sorry
    qsmul := (. • .)
    qsmul_eq_mul' := sorry
    inv := sorry
    exists_pair_ne := sorry
    mul_inv_cancel := sorry
    inv_zero := sorry }

instance [CharZero K] : CharZero (SplittingField f) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective

-- The algebra instance deriving from `K` should be definitionally equal to that
-- deriving from the field structure on `SplittingField f`.
example :
    (AddCommMonoid.natModule : Module ℕ (SplittingField f)) =
      @Algebra.toModule _ _ _ _ (SplittingField.algebra' f) :=
  rfl

example :
    (AddCommGroup.intModule _ : Module ℤ (SplittingField f)) =
      @Algebra.toModule _ _ _ _ (SplittingField.algebra' f) :=
  rfl

example [CharZero K] : SplittingField.algebra' f = algebraRat :=
  rfl

example [CharZero K] : SplittingField.algebra' f = algebraRat :=
  rfl

example {q : ℚ[X]} : algebraInt (SplittingField q) = SplittingField.algebra' q :=
  rfl

instance _root_.Polynomial.IsSplittingField.splittingField (f : K[X]) :
    IsSplittingField K (SplittingField f) f :=
  IsSplittingField.of_algEquiv _ f (SplittingFieldAux.AlgEquivQuotientMvPolynomial f).symm
#align polynomial.is_splitting_field.splitting_field Polynomial.IsSplittingField.splittingField

protected theorem splits : Splits (algebraMap K (SplittingField f)) f :=
  IsSplittingField.splits f.SplittingField f
#align polynomial.splitting_field.splits Polynomial.SplittingField.splits

variable [Algebra K L] (hb : Splits (algebraMap K L) f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : SplittingField f →ₐ[K] L :=
  IsSplittingField.lift f.SplittingField f hb
#align polynomial.splitting_field.lift Polynomial.SplittingField.lift

theorem adjoin_roots : Algebra.adjoin K
    (↑(f.map (algebraMap K <| SplittingField f)).roots.toFinset : Set (SplittingField f)) = ⊤ :=
  IsSplittingField.adjoin_roots f.SplittingField f
#align polynomial.splitting_field.adjoin_roots Polynomial.SplittingField.adjoin_roots

theorem adjoin_rootSet : Algebra.adjoin K (f.rootSet f.SplittingField) = ⊤ :=
  adjoin_roots f
#align polynomial.splitting_field.adjoin_root_set Polynomial.SplittingField.adjoin_rootSet

end SplittingField

end SplittingField

namespace IsSplittingField

variable (K L)
variable [Algebra K L]

variable {K}

instance (f : K[X]) : FiniteDimensional K f.SplittingField :=
  finiteDimensional f.SplittingField f

/-- Any splitting field is isomorphic to `splitting_field f`. -/
def algEquiv (f : K[X]) [IsSplittingField K L f] : L ≃ₐ[K] SplittingField f := by
  refine'
    AlgEquiv.ofBijective (lift L f <| splits (SplittingField f) f)
      ⟨RingHom.injective (lift L f <| splits (SplittingField f) f).toRingHom, _⟩
  haveI := finiteDimensional (SplittingField f) f
  haveI := finiteDimensional L f
  have : FiniteDimensional.finrank K L = FiniteDimensional.finrank K (SplittingField f) :=
    le_antisymm
      (LinearMap.finrank_le_finrank_of_injective
        (show Function.Injective (lift L f <| splits (SplittingField f) f).toLinearMap from
          RingHom.injective (lift L f <| splits (SplittingField f) f : L →+* f.SplittingField)))
      (LinearMap.finrank_le_finrank_of_injective
        (show Function.Injective (lift (SplittingField f) f <| splits L f).toLinearMap from
          RingHom.injective (lift (SplittingField f) f <| splits L f : f.SplittingField →+* L)))
  change Function.Surjective (lift L f <| splits (SplittingField f) f).toLinearMap
  refine' (LinearMap.injective_iff_surjective_of_finrank_eq_finrank this).1 _
  exact RingHom.injective (lift L f <| splits (SplittingField f) f : L →+* f.SplittingField)
#align polynomial.is_splitting_field.alg_equiv Polynomial.IsSplittingField.algEquiv

end IsSplittingField

end Polynomial

section Normal

instance [Field F] (p : F[X]) : Normal F p.SplittingField :=
  Normal.of_isSplittingField p

end Normal
