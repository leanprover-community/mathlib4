/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.Algebra.CharP.Algebra

#align_import field_theory.splitting_field.construction from "leanprover-community/mathlib"@"e3f4be1fcb5376c4948d7f095bec45350bfb9d1a"

/-!
# Splitting fields

In this file we prove the existence and uniqueness of splitting fields.

## Main definitions

* `Polynomial.SplittingField f`: A fixed splitting field of the polynomial `f`.

## Main statements

* `Polynomial.IsSplittingField.algEquiv`: Every splitting field of a polynomial `f` is isomorphic
  to `SplittingField f` and thus, being a splitting field is unique up to isomorphism.

## Implementation details
We construct a `SplittingFieldAux` without worrying about whether the instances satisfy nice
definitional equalities. Then the actual `SplittingField` is defined to be a quotient of a
`MvPolynomial` ring by the kernel of the obvious map into `SplittingFieldAux`. Because the
actual `SplittingField` will be a quotient of a `MvPolynomial`, it has nice instances on it.

-/


noncomputable section

open scoped Classical Polynomial

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

/-- Divide a polynomial f by `X - C r` where `r` is a root of `f` in a bigger field extension. -/
def removeFactor (f : K[X]) : Polynomial (AdjoinRoot <| factor f) :=
  map (AdjoinRoot.of f.factor) f /ₘ (X - C (AdjoinRoot.root f.factor))
#align polynomial.remove_factor Polynomial.removeFactor

theorem X_sub_C_mul_removeFactor (f : K[X]) (hf : f.natDegree ≠ 0) :
    (X - C (AdjoinRoot.root f.factor)) * f.removeFactor = map (AdjoinRoot.of f.factor) f := by
  let ⟨g, hg⟩ := factor_dvd_of_natDegree_ne_zero hf
  apply (mul_divByMonic_eq_iff_isRoot
    (R := AdjoinRoot f.factor) (a := AdjoinRoot.root f.factor)).mpr
  rw [IsRoot.def, eval_map, hg, eval₂_mul, ← hg, AdjoinRoot.eval₂_root, zero_mul]
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

It constructs the type, proves that is a field and algebra over the base field.

Uses recursion on the degree.
-/
def SplittingFieldAuxAux (n : ℕ) : ∀ {K : Type u} [Field K], K[X] →
    Σ (L : Type u) (_ : Field L), Algebra K L :=
  -- Porting note: added motive
  Nat.recOn (motive := fun (_x : ℕ) => ∀ {K : Type u} [_inst_4 : Field K], K[X] →
      Σ (L : Type u) (_ : Field L), Algebra K L) n
    (fun {K} _ _ => ⟨K, inferInstance, inferInstance⟩)
    fun _ ih _ _ f =>
      let ⟨L, fL, _⟩ := ih f.removeFactor
      ⟨L, fL, (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor)).toAlgebra⟩
#align polynomial.splitting_field_aux_aux Polynomial.SplittingFieldAuxAux

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors. It is the type constructed in `SplittingFieldAuxAux`.
-/
def SplittingFieldAux (n : ℕ) {K : Type u} [Field K] (f : K[X]) : Type u :=
  (SplittingFieldAuxAux n f).1
#align polynomial.splitting_field_aux Polynomial.SplittingFieldAux

instance SplittingFieldAux.field (n : ℕ) {K : Type u} [Field K] (f : K[X]) :
    Field (SplittingFieldAux n f) :=
  (SplittingFieldAuxAux n f).2.1
#align polynomial.splitting_field_aux.field Polynomial.SplittingFieldAux.field

instance (n : ℕ) {K : Type u} [Field K] (f : K[X]) : Inhabited (SplittingFieldAux n f) :=
  ⟨0⟩

instance SplittingFieldAux.algebra (n : ℕ) {K : Type u} [Field K] (f : K[X]) :
    Algebra K (SplittingFieldAux n f) :=
  (SplittingFieldAuxAux n f).2.2
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
  IsScalarTower.of_algebraMap_eq fun _ => rfl
#align polynomial.splitting_field_aux.scalar_tower' Polynomial.SplittingFieldAux.scalar_tower'

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
    rw [← splits_id_iff_splits, algebraMap_succ, ← map_map, splits_id_iff_splits,
      ← X_sub_C_mul_removeFactor f fun h => by rw [h] at hf; cases hf]
    exact splits_mul _ (splits_X_sub_C _) (ih _ (natDegree_removeFactor' hf))
#align polynomial.splitting_field_aux.splits Polynomial.SplittingFieldAux.splits

theorem adjoin_rootSet (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (_hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤ :=
  Nat.recOn (motive := fun n =>
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (_hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤)
    n (fun {K} _ f _hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩)
    fun n ih {K} _ f hfn => by
    have hndf : f.natDegree ≠ 0 := by intro h; rw [h] at hfn; cases hfn
    have hfn0 : f ≠ 0 := by intro h; rw [h] at hndf; exact hndf rfl
    have hmf0 : map (algebraMap K (SplittingFieldAux n.succ f)) f ≠ 0 := map_ne_zero hfn0
    rw [rootSet_def, aroots_def]
    rw [algebraMap_succ, ← map_map, ← X_sub_C_mul_removeFactor _ hndf, Polynomial.map_mul] at hmf0 ⊢
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [roots_mul hmf0, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.toFinset_add,
      Finset.coe_union, Multiset.toFinset_singleton, Finset.coe_singleton,
      Algebra.adjoin_union_eq_adjoin_adjoin, ← Set.image_singleton,
      Algebra.adjoin_algebraMap K (SplittingFieldAux n f.removeFactor),
      AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top]
    /- Porting note: was `rw [IsScalarTower.adjoin_range_toAlgHom K (AdjoinRoot f.factor)
        (SplittingFieldAux n f.removeFactor)]` -/
    have := IsScalarTower.adjoin_range_toAlgHom K (AdjoinRoot f.factor)
        (SplittingFieldAux n f.removeFactor)
        (f.removeFactor.rootSet (SplittingFieldAux n f.removeFactor))
    refine this.trans ?_
    rw [ih _ (natDegree_removeFactor' hfn), Subalgebra.restrictScalars_top]
#align polynomial.splitting_field_aux.adjoin_root_set Polynomial.SplittingFieldAux.adjoin_rootSet

instance (f : K[X]) : IsSplittingField K (SplittingFieldAux f.natDegree f) f :=
  ⟨SplittingFieldAux.splits _ _ rfl, SplittingFieldAux.adjoin_rootSet _ _ rfl⟩

#noalign polynomial.splitting_field_aux.of_mv_polynomial
#noalign polynomial.splitting_field_aux.of_mv_polynomial_surjective
#noalign polynomial.splitting_field_aux.alg_equiv_quotient_mv_polynomial

end SplittingFieldAux

/-- A splitting field of a polynomial. -/
def SplittingField (f : K[X]) :=
  MvPolynomial (SplittingFieldAux f.natDegree f) K ⧸
    RingHom.ker (MvPolynomial.aeval (R := K) id).toRingHom
#align polynomial.splitting_field Polynomial.SplittingField

namespace SplittingField

variable (f : K[X])

instance commRing : CommRing (SplittingField f) :=
  Ideal.Quotient.commRing _
#align polynomial.splitting_field.comm_ring Polynomial.SplittingField.commRing

instance inhabited : Inhabited (SplittingField f) :=
  ⟨37⟩
#align polynomial.splitting_field.inhabited Polynomial.SplittingField.inhabited

instance {S : Type*} [DistribSMul S K] [IsScalarTower S K K] : SMul S (SplittingField f) :=
  Submodule.Quotient.instSMul' _

instance algebra : Algebra K (SplittingField f) :=
  Ideal.Quotient.algebra _
#align polynomial.splitting_field.algebra Polynomial.SplittingField.algebra

instance algebra' {R : Type*} [CommSemiring R] [Algebra R K] : Algebra R (SplittingField f) :=
  Ideal.Quotient.algebra _
#align polynomial.splitting_field.algebra' Polynomial.SplittingField.algebra'

instance isScalarTower {R : Type*} [CommSemiring R] [Algebra R K] :
    IsScalarTower R K (SplittingField f) :=
  Ideal.Quotient.isScalarTower _ _ _
#align polynomial.splitting_field.is_scalar_tower Polynomial.SplittingField.isScalarTower

/-- The algebra equivalence with `SplittingFieldAux`,
which we will use to construct the field structure. -/
def algEquivSplittingFieldAux (f : K[X]) : SplittingField f ≃ₐ[K] SplittingFieldAux f.natDegree f :=
  Ideal.quotientKerAlgEquivOfSurjective fun x => ⟨MvPolynomial.X x, by simp⟩
#align polynomial.splitting_field.alg_equiv_splitting_field_aux Polynomial.SplittingField.algEquivSplittingFieldAux

instance instGroupWithZero : GroupWithZero (SplittingField f) :=
  let e := algEquivSplittingFieldAux f
  { inv := fun a ↦ e.symm (e a)⁻¹
    inv_zero := by simp
    mul_inv_cancel := fun a ha ↦ e.injective $ by simp [(AddEquivClass.map_ne_zero_iff _).2 ha]
    __ := e.surjective.nontrivial }

instance instField : Field (SplittingField f) where
  __ := commRing _
  __ := instGroupWithZero _
  nnratCast q := algebraMap K _ q
  ratCast q := algebraMap K _ q
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by change algebraMap K _ _ = _; simp_rw [NNRat.cast_def, map_div₀, map_natCast]
  ratCast_def q := by
    change algebraMap K _ _ = _; rw [Rat.cast_def, map_div₀, map_intCast, map_natCast]
  nnqsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' $ by
    ext; simp [MvPolynomial.algebraMap_eq, NNRat.smul_def]
  qsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' $ by
    ext; simp [MvPolynomial.algebraMap_eq, Rat.smul_def]

instance instCharZero [CharZero K] : CharZero (SplittingField f) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective

instance instCharP (p : ℕ) [CharP K p] : CharP (SplittingField f) p :=
  charP_of_injective_algebraMap (algebraMap K _).injective p

instance instExpChar (p : ℕ) [ExpChar K p] : ExpChar (SplittingField f) p :=
  expChar_of_injective_algebraMap (algebraMap K _).injective p

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

example {q : ℚ[X]} : algebraInt (SplittingField q) = SplittingField.algebra' q :=
  rfl

instance _root_.Polynomial.IsSplittingField.splittingField (f : K[X]) :
    IsSplittingField K (SplittingField f) f :=
  IsSplittingField.of_algEquiv _ f (algEquivSplittingFieldAux f).symm
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

variable (K L)
variable [Algebra K L]
variable {K}

instance (f : K[X]) : FiniteDimensional K f.SplittingField :=
  finiteDimensional f.SplittingField f

instance [Fintype K] (f : K[X]) : Fintype f.SplittingField :=
  FiniteDimensional.fintypeOfFintype K _

instance (f : K[X]) : NoZeroSMulDivisors K f.SplittingField :=
  inferInstance

/-- Any splitting field is isomorphic to `SplittingFieldAux f`. -/
def algEquiv (f : K[X]) [h : IsSplittingField K L f] : L ≃ₐ[K] SplittingField f :=
  AlgEquiv.ofBijective (lift L f <| splits (SplittingField f) f) <|
    have := finiteDimensional L f
    ((Algebra.IsAlgebraic.of_finite K L).algHom_bijective₂ _ <| lift _ f h.1).1
#align polynomial.is_splitting_field.alg_equiv Polynomial.IsSplittingField.algEquiv

end IsSplittingField

end Polynomial
