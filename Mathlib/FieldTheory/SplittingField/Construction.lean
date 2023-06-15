/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module field_theory.splitting_field.construction
! leanprover-community/mathlib commit e3f4be1fcb5376c4948d7f095bec45350bfb9d1a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.FieldTheory.Normal

/-!
# Splitting fields

In this file we prove the existence and uniqueness of splitting fields.

## Main definitions

* `polynomial.splitting_field f`: A fixed splitting field of the polynomial `f`.

## Main statements

* `polynomial.is_splitting_field.alg_equiv`: Every splitting field of a polynomial `f` is isomorphic
  to `splitting_field f` and thus, being a splitting field is unique up to isomorphism.

## Implementation details
We construct a `splitting_field_aux` without worrying about whether the instances satisfy nice
definitional equalities. Then the actual `splitting_field` is defined to be a quotient of a
`mv_polynomial` ring by the kernel of the obvious map into `splitting_field_aux`. Because the
actual `splitting_field` will be a quotient of a `mv_polynomial`, it has nice instances on it.

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

theorem irreducible_factor (f : K[X]) : Irreducible (factor f) := by rw [factor]; split_ifs with H;
  · exact (Classical.choose_spec H).1; · exact irreducible_X
#align polynomial.irreducible_factor Polynomial.irreducible_factor

/-- See note [fact non-instances]. -/
theorem fact_irreducible_factor (f : K[X]) : Fact (Irreducible (factor f)) :=
  ⟨irreducible_factor f⟩
#align polynomial.fact_irreducible_factor Polynomial.fact_irreducible_factor

attribute [local instance] fact_irreducible_factor

theorem factor_dvd_of_not_isUnit {f : K[X]} (hf1 : ¬IsUnit f) : factor f ∣ f :=
  by
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

theorem x_sub_c_mul_removeFactor (f : K[X]) (hf : f.natDegree ≠ 0) :
    (X - C (AdjoinRoot.root f.factor)) * f.removeFactor = map (AdjoinRoot.of f.factor) f :=
  let ⟨g, hg⟩ := factor_dvd_of_natDegree_ne_zero hf
  mul_divByMonic_eq_iff_isRoot.2 <| by
    rw [is_root.def, eval_map, hg, eval₂_mul, ← hg, AdjoinRoot.eval₂_root, MulZeroClass.zero_mul]
#align polynomial.X_sub_C_mul_remove_factor Polynomial.x_sub_c_mul_removeFactor

theorem natDegree_removeFactor (f : K[X]) : f.removeFactor.natDegree = f.natDegree - 1 := by
  rw [remove_factor, nat_degree_div_by_monic _ (monic_X_sub_C _), nat_degree_map,
    nat_degree_X_sub_C]
#align polynomial.nat_degree_remove_factor Polynomial.natDegree_removeFactor

theorem natDegree_remove_factor' {f : K[X]} {n : ℕ} (hfn : f.natDegree = n + 1) :
    f.removeFactor.natDegree = n := by rw [nat_degree_remove_factor, hfn, n.add_sub_cancel]
#align polynomial.nat_degree_remove_factor' Polynomial.natDegree_remove_factor'

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors.

It constructs the type, proves that is a field and algebra over the base field.

Uses recursion on the degree.
-/
def splittingFieldAuxAux (n : ℕ) :
    ∀ {K : Type u} [Field K], ∀ f : K[X], Σ (L : Type u) (inst : Field L), Algebra K L :=
  Nat.recOn n (fun K inst f => ⟨K, inst, inferInstance⟩) fun m ih K inst f =>
    let L := ih (@removeFactor K inst f)
    let h₁ := L.2.1
    let h₂ := L.2.2
    ⟨L.1, L.2.1, (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor)).toAlgebra⟩
#align polynomial.splitting_field_aux_aux Polynomial.splittingFieldAuxAux

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors. It is the type constructed in `splitting_field_aux_aux`.
-/
def SplittingFieldAux (n : ℕ) {K : Type u} [Field K] (f : K[X]) : Type u :=
  (splittingFieldAuxAux n f).1
#align polynomial.splitting_field_aux Polynomial.SplittingFieldAux

instance SplittingFieldAux.field (n : ℕ) {K : Type u} [Field K] (f : K[X]) :
    Field (SplittingFieldAux n f) :=
  (splittingFieldAuxAux n f).2.1
#align polynomial.splitting_field_aux.field Polynomial.SplittingFieldAux.field

instance (n : ℕ) {K : Type u} [Field K] (f : K[X]) : Inhabited (SplittingFieldAux n f) :=
  ⟨0⟩

instance SplittingFieldAux.algebra (n : ℕ) {K : Type u} [Field K] (f : K[X]) :
    Algebra K (SplittingFieldAux n f) :=
  (splittingFieldAuxAux n f).2.2
#align polynomial.splitting_field_aux.algebra Polynomial.SplittingFieldAux.algebra

namespace SplittingFieldAux

theorem succ (n : ℕ) (f : K[X]) :
    SplittingFieldAux (n + 1) f = SplittingFieldAux n f.removeFactor :=
  rfl
#align polynomial.splitting_field_aux.succ Polynomial.SplittingFieldAux.succ

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
  IsScalarTower.of_algebraMap_eq fun x => rfl
#align polynomial.splitting_field_aux.scalar_tower' Polynomial.SplittingFieldAux.scalar_tower'

theorem algebraMap_succ (n : ℕ) (f : K[X]) :
    algebraMap K (splitting_field_aux (n + 1) f) =
      (algebraMap (AdjoinRoot f.factor) (splitting_field_aux n f.remove_factor)).comp
        (AdjoinRoot.of f.factor) :=
  rfl
#align polynomial.splitting_field_aux.algebra_map_succ Polynomial.SplittingFieldAux.algebraMap_succ

protected theorem splits (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n), splits (algebraMap K <| splitting_field_aux n f) f :=
  Nat.recOn n
    (fun K _ _ hf =>
      splits_of_degree_le_one _
        (le_trans degree_le_nat_degree <| hf.symm ▸ WithBot.coe_le_coe.2 zero_le_one))
    fun n ih K _ f hf => by
    skip;
    rw [← splits_id_iff_splits, algebra_map_succ, ← map_map, splits_id_iff_splits, ←
      X_sub_C_mul_remove_factor f fun h => by rw [h] at hf ; cases hf]
    exact splits_mul _ (splits_X_sub_C _) (ih _ (nat_degree_remove_factor' hf))
#align polynomial.splitting_field_aux.splits Polynomial.SplittingFieldAux.splits

theorem adjoin_rootSet (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (splitting_field_aux n f)) = ⊤ :=
  Nat.recOn n (fun K _ f hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩)
    fun n ih K _ f hfn =>
    by
    have hndf : f.nat_degree ≠ 0 := by intro h; rw [h] at hfn ; cases hfn
    have hfn0 : f ≠ 0 := by intro h; rw [h] at hndf ; exact hndf rfl
    have hmf0 : map (algebraMap K (splitting_field_aux n.succ f)) f ≠ 0 := map_ne_zero hfn0
    simp_rw [root_set] at ih ⊢
    rw [algebra_map_succ, ← map_map, ← X_sub_C_mul_remove_factor _ hndf, Polynomial.map_mul] at hmf0
      ⊢
    rw [roots_mul hmf0, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.toFinset_add,
      Finset.coe_union, Multiset.toFinset_singleton, Finset.coe_singleton,
      Algebra.adjoin_union_eq_adjoin_adjoin, ← Set.image_singleton,
      Algebra.adjoin_algebraMap K (AdjoinRoot f.factor) (splitting_field_aux n f.remove_factor),
      AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top,
      IsScalarTower.adjoin_range_toAlgHom K (AdjoinRoot f.factor)
        (splitting_field_aux n f.remove_factor),
      ih _ (nat_degree_remove_factor' hfn), Subalgebra.restrictScalars_top]
#align polynomial.splitting_field_aux.adjoin_root_set Polynomial.SplittingFieldAux.adjoin_rootSet

instance (f : K[X]) : IsSplittingField K (SplittingFieldAux f.natDegree f) f :=
  ⟨SplittingFieldAux.splits _ _ rfl, SplittingFieldAux.adjoin_rootSet _ _ rfl⟩

/-- The natural map from `mv_polynomial (f.root_set (splitting_field_aux f.nat_degree f))`
to `splitting_field_aux f.nat_degree f` sendind a variable to the corresponding root. -/
def ofMvPolynomial (f : K[X]) :
    MvPolynomial (f.rootSet (SplittingFieldAux f.natDegree f)) K →ₐ[K]
      SplittingFieldAux f.natDegree f :=
  MvPolynomial.aeval fun i => i.1
#align polynomial.splitting_field_aux.of_mv_polynomial Polynomial.SplittingFieldAux.ofMvPolynomial

theorem ofMvPolynomial_surjective (f : K[X]) : Function.Surjective (ofMvPolynomial f) :=
  by
  suffices AlgHom.range (of_mv_polynomial f) = ⊤ by
    rw [← Set.range_iff_surjective] <;> rwa [SetLike.ext'_iff] at this
  rw [of_mv_polynomial, ← Algebra.adjoin_range_eq_range_aeval K, eq_top_iff, ←
    adjoin_root_set _ _ rfl]
  exact Algebra.adjoin_le fun α hα => Algebra.subset_adjoin ⟨⟨α, hα⟩, rfl⟩
#align polynomial.splitting_field_aux.of_mv_polynomial_surjective Polynomial.SplittingFieldAux.ofMvPolynomial_surjective

/-- The algebra isomorphism between the quotient of
`mv_polynomial (f.root_set (splitting_field_aux f.nat_degree f)) K` by the kernel of
`of_mv_polynomial f` and `splitting_field_aux f.nat_degree f`. It is used to transport all the
algebraic structures from the latter to `f.splitting_field`, that is defined as the former. -/
def algEquivQuotientMvPolynomial (f : K[X]) :
    (MvPolynomial (f.rootSet (SplittingFieldAux f.natDegree f)) K ⧸
        RingHom.ker (ofMvPolynomial f).toRingHom) ≃ₐ[K]
      SplittingFieldAux f.natDegree f :=
  (Ideal.quotientKerAlgEquivOfSurjective (ofMvPolynomial_surjective f) : _)
#align polynomial.splitting_field_aux.alg_equiv_quotient_mv_polynomial Polynomial.SplittingFieldAux.algEquivQuotientMvPolynomial

end SplittingFieldAux

/-- A splitting field of a polynomial. -/
def SplittingField (f : K[X]) :=
  MvPolynomial (f.rootSet (SplittingFieldAux f.natDegree f)) K ⧸
    RingHom.ker (SplittingFieldAux.ofMvPolynomial f).toRingHom
#align polynomial.splitting_field Polynomial.SplittingField

namespace SplittingField

variable (f : K[X])

instance commRing : CommRing (SplittingField f) :=
  Ideal.Quotient.commRing _
#align polynomial.splitting_field.comm_ring Polynomial.SplittingField.commRing

instance inhabited : Inhabited (SplittingField f) :=
  ⟨37⟩
#align polynomial.splitting_field.inhabited Polynomial.SplittingField.inhabited

instance {S : Type _} [DistribSMul S K] [IsScalarTower S K K] : SMul S (SplittingField f) :=
  Submodule.Quotient.hasSmul' _

instance algebra : Algebra K (SplittingField f) :=
  Ideal.Quotient.algebra _
#align polynomial.splitting_field.algebra Polynomial.SplittingField.algebra

instance algebra' {R : Type _} [CommSemiring R] [Algebra R K] : Algebra R (SplittingField f) :=
  Ideal.Quotient.algebra _
#align polynomial.splitting_field.algebra' Polynomial.SplittingField.algebra'

instance isScalarTower {R : Type _} [CommSemiring R] [Algebra R K] :
    IsScalarTower R K (SplittingField f) :=
  Ideal.Quotient.isScalarTower _ _ _
#align polynomial.splitting_field.is_scalar_tower Polynomial.SplittingField.isScalarTower

/-- The algebra equivalence with `splitting_field_aux`,
which we will use to construct the field structure. -/
def algEquivSplittingFieldAux (f : K[X]) : SplittingField f ≃ₐ[K] SplittingFieldAux f.natDegree f :=
  SplittingFieldAux.algEquivQuotientMvPolynomial f
#align polynomial.splitting_field.alg_equiv_splitting_field_aux Polynomial.SplittingField.algEquivSplittingFieldAux

instance : Field (SplittingField f) :=
  let e := algEquivSplittingFieldAux f
  {
    SplittingField.commRing
      f with
    ratCast := fun a => algebraMap K _ (a : K)
    inv := fun a => e.symm (e a)⁻¹
    qsmul := (· • ·)
    qsmul_eq_mul' := fun a x =>
      Quotient.inductionOn' x fun p =>
        congr_arg Quotient.mk''
          (by
            ext
            simp only [MvPolynomial.algebraMap_eq, Rat.smul_def, MvPolynomial.coeff_smul,
              MvPolynomial.coeff_C_mul])
    ratCast_mk := fun a b h1 h2 => by
      apply e.injective
      change e (algebraMap K _ _) = _
      simp only [map_ratCast, map_natCast, map_mul, map_intCast, AlgEquiv.commutes]
      change _ = e ↑a * e (e.symm (e b)⁻¹)
      rw [AlgEquiv.apply_symm_apply]
      convert Field.ratCast_mk a b h1 h2
      all_goals simp
    exists_pair_ne := ⟨e.symm 0, e.symm 1, fun w => zero_ne_one (e.symm.Injective w)⟩
    mul_inv_cancel := fun a w => by
      apply e.injective
      rw [map_mul, map_one]
      change e a * e (e.symm (e a)⁻¹) = 1
      rw [AlgEquiv.apply_symm_apply, mul_inv_cancel]
      exact fun w' => w (by simpa only [AddEquivClass.map_eq_zero_iff] using w')
    inv_zero := by
      change e.symm (e 0)⁻¹ = 0
      simp }

instance [CharZero K] : CharZero (SplittingField f) :=
  charZero_of_injective_algebraMap (algebraMap K _).Injective

-- The algebra instance deriving from `K` should be definitionally equal to that
-- deriving from the field structure on `splitting_field f`.
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

example {q : ℚ[X]} : algebraInt (SplittingField q) = SplittingField.algebra' q :=
  rfl

instance Polynomial.IsSplittingField.splittingField (f : K[X]) :
    IsSplittingField K (SplittingField f) f :=
  IsSplittingField.of_algEquiv _ f (SplittingFieldAux.algEquivQuotientMvPolynomial f).symm
#align polynomial.is_splitting_field.splitting_field Polynomial.IsSplittingField.splittingField

protected theorem splits : Splits (algebraMap K (SplittingField f)) f :=
  IsSplittingField.splits f.SplittingField f
#align polynomial.splitting_field.splits Polynomial.SplittingField.splits

variable [Algebra K L] (hb : Splits (algebraMap K L) f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : SplittingField f →ₐ[K] L :=
  IsSplittingField.lift f.SplittingField f hb
#align polynomial.splitting_field.lift Polynomial.SplittingField.lift

theorem adjoin_rootSet : Algebra.adjoin K (f.rootSet (SplittingField f)) = ⊤ :=
  Polynomial.IsSplittingField.adjoin_rootSet _ f
#align polynomial.splitting_field.adjoin_root_set Polynomial.SplittingField.adjoin_rootSet

end SplittingField

end SplittingField

namespace IsSplittingField

variable (K L) [Algebra K L]

variable {K}

instance (f : K[X]) : FiniteDimensional K f.SplittingField :=
  finiteDimensional f.SplittingField f

instance [Fintype K] (f : K[X]) : Fintype f.SplittingField :=
  FiniteDimensional.fintypeOfFintype K _

instance (f : K[X]) : NoZeroSMulDivisors K f.SplittingField :=
  inferInstance

/-- Any splitting field is isomorphic to `splitting_field f`. -/
def algEquiv (f : K[X]) [IsSplittingField K L f] : L ≃ₐ[K] SplittingField f :=
  by
  refine'
    AlgEquiv.ofBijective (lift L f <| splits (splitting_field f) f)
      ⟨RingHom.injective (lift L f <| splits (splitting_field f) f).toRingHom, _⟩
  haveI := FiniteDimensional (splitting_field f) f
  haveI := FiniteDimensional L f
  have : FiniteDimensional.finrank K L = FiniteDimensional.finrank K (splitting_field f) :=
    le_antisymm
      (LinearMap.finrank_le_finrank_of_injective
        (show Function.Injective (lift L f <| splits (splitting_field f) f).toLinearMap from
          RingHom.injective (lift L f <| splits (splitting_field f) f : L →+* f.splitting_field)))
      (LinearMap.finrank_le_finrank_of_injective
        (show Function.Injective (lift (splitting_field f) f <| splits L f).toLinearMap from
          RingHom.injective (lift (splitting_field f) f <| splits L f : f.splitting_field →+* L)))
  change Function.Surjective (lift L f <| splits (splitting_field f) f).toLinearMap
  refine' (LinearMap.injective_iff_surjective_of_finrank_eq_finrank this).1 _
  exact RingHom.injective (lift L f <| splits (splitting_field f) f : L →+* f.splitting_field)
#align polynomial.is_splitting_field.alg_equiv Polynomial.IsSplittingField.algEquiv

end IsSplittingField

end Polynomial

section Normal

instance [Field F] (p : F[X]) : Normal F p.SplittingField :=
  Normal.of_isSplittingField p

end Normal
