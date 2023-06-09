/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module field_theory.splitting_field.construction
! leanprover-community/mathlib commit df76f43357840485b9d04ed5dee5ab115d420e87
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

Uses recursion on the degree. For better definitional behaviour, structures
including `splitting_field_aux` (such as instances) should be defined using
this recursion in each field, rather than defining the whole tuple through
recursion.
-/
def SplittingFieldAux (n : ℕ) : ∀ {K : Type u} [Field K], ∀ f : K[X], Type u :=
  Nat.recOn n (fun K _ _ => K) fun n ih K _ f => ih f.remove_factor
#align polynomial.splitting_field_aux Polynomial.SplittingFieldAux

namespace SplittingFieldAux

theorem succ (n : ℕ) (f : K[X]) :
    SplittingFieldAux (n + 1) f = SplittingFieldAux n f.removeFactor :=
  rfl
#align polynomial.splitting_field_aux.succ Polynomial.SplittingFieldAux.succ

section LiftInstances

/-! ### Instances on `splitting_field_aux`

In order to avoid diamond issues, we have to be careful to define each data field of algebraic
instances on `splitting_field_aux` by recursion, rather than defining the whole structure by
recursion at once.

The important detail is that the `smul` instances can be lifted _before_ we create the algebraic
instances; if we do not do this, this creates a mutual dependence on both on each other, and it
is impossible to untangle this mess. In order to do this, we need that these `smul` instances
are distributive in the sense of `distrib_smul`, which is weak enough to be guaranteed at this
stage. This is sufficient to lift an action to `adjoin_root f` (remember that this is a quotient,
so these conditions are equivalent to well-definedness), which is all we need.
-/


/-- Splitting fields have a zero. -/
protected def zero (n : ℕ) : ∀ {K : Type u} [Field K], ∀ {f : K[X]}, splitting_field_aux n f :=
  Nat.recOn n (fun K fK f => @Zero.zero K _) fun n ih K fK f => ih
#align polynomial.splitting_field_aux.zero Polynomial.SplittingFieldAux.zero

/-- Splitting fields have an addition. -/
protected def add (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, splitting_field_aux n f → splitting_field_aux n f → splitting_field_aux n f :=
  Nat.recOn n (fun K fK f => @Add.add K _) fun n ih K fK f => ih
#align polynomial.splitting_field_aux.add Polynomial.SplittingFieldAux.add

/-- Splitting fields inherit scalar multiplication. -/
protected def smul (n : ℕ) :
    ∀ (α : Type _) {K : Type u} [Field K],
      ∀ [DistribSMul α K],
        ∀ [IsScalarTower α K K] {f : K[X]}, α → splitting_field_aux n f → splitting_field_aux n f :=
  Nat.recOn n (fun α K fK ds ist f => @SMul.smul _ K _) fun n ih α K fK ds ist f => ih α
#align polynomial.splitting_field_aux.smul Polynomial.SplittingFieldAux.smul

instance hasSmul (α : Type _) (n : ℕ) {K : Type u} [Field K] [DistribSMul α K] [IsScalarTower α K K]
    {f : K[X]} : SMul α (SplittingFieldAux n f) :=
  ⟨SplittingFieldAux.smul n α⟩
#align polynomial.splitting_field_aux.has_smul Polynomial.SplittingFieldAux.hasSmul

instance isScalarTower (n : ℕ) :
    ∀ (R₁ R₂ : Type _) {K : Type u} [SMul R₁ R₂] [Field K],
      ∀ [DistribSMul R₂ K] [DistribSMul R₁ K],
        ∀ [IsScalarTower R₁ K K] [IsScalarTower R₂ K K] [IsScalarTower R₁ R₂ K] {f : K[X]},
          IsScalarTower R₁ R₂ (splitting_field_aux n f) :=
  Nat.recOn n
    (fun R₁ R₂ K _ _ hs₂ hs₁ _ _ h f =>
      by
      rcases hs₁ with @⟨@⟨⟨hs₁⟩, _⟩, _⟩
      rcases hs₂ with @⟨@⟨⟨hs₂⟩, _⟩, _⟩
      exact h)
    fun n ih R₁ R₂ K _ _ _ _ _ _ _ f => ih R₁ R₂
#align polynomial.splitting_field_aux.is_scalar_tower Polynomial.SplittingFieldAux.isScalarTower

/-- Splitting fields have a negation. -/
protected def neg (n : ℕ) :
    ∀ {K : Type u} [Field K], ∀ {f : K[X]}, splitting_field_aux n f → splitting_field_aux n f :=
  Nat.recOn n (fun K fK f => @Neg.neg K _) fun n ih K fK f => ih
#align polynomial.splitting_field_aux.neg Polynomial.SplittingFieldAux.neg

/-- Splitting fields have subtraction. -/
protected def sub (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, splitting_field_aux n f → splitting_field_aux n f → splitting_field_aux n f :=
  Nat.recOn n (fun K fK f => @Sub.sub K _) fun n ih K fK f => ih
#align polynomial.splitting_field_aux.sub Polynomial.SplittingFieldAux.sub

/-- Splitting fields have a one. -/
protected def one (n : ℕ) : ∀ {K : Type u} [Field K], ∀ {f : K[X]}, splitting_field_aux n f :=
  Nat.recOn n (fun K fK f => @One.one K _) fun n ih K fK f => ih
#align polynomial.splitting_field_aux.one Polynomial.SplittingFieldAux.one

/-- Splitting fields have a multiplication. -/
protected def mul (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, splitting_field_aux n f → splitting_field_aux n f → splitting_field_aux n f :=
  Nat.recOn n (fun K fK f => @Mul.mul K _) fun n ih K fK f => ih
#align polynomial.splitting_field_aux.mul Polynomial.SplittingFieldAux.mul

/-- Splitting fields have a power operation. -/
protected def npow (n : ℕ) :
    ∀ {K : Type u} [Field K], ∀ {f : K[X]}, ℕ → splitting_field_aux n f → splitting_field_aux n f :=
  Nat.recOn n (fun K fK f n x => @Pow.pow K _ _ x n) fun n ih K fK f => ih
#align polynomial.splitting_field_aux.npow Polynomial.SplittingFieldAux.npow

/-- Splitting fields have an injection from the base field. -/
protected def mk (n : ℕ) : ∀ {K : Type u} [Field K], ∀ {f : K[X]}, K → splitting_field_aux n f :=
  Nat.recOn n (fun K fK f => id) fun n ih K fK f => ih ∘ coe
#align polynomial.splitting_field_aux.mk Polynomial.SplittingFieldAux.mk

-- note that `coe` goes from `K → adjoin_root f`, and then `ih` lifts to the full splitting field
-- (as we generalise over all fields in this recursion!)
/-- Splitting fields have an inverse. -/
protected def inv (n : ℕ) :
    ∀ {K : Type u} [Field K], ∀ {f : K[X]}, splitting_field_aux n f → splitting_field_aux n f :=
  Nat.recOn n (fun K fK f => @Inv.inv K _) fun n ih K fK f => ih
#align polynomial.splitting_field_aux.inv Polynomial.SplittingFieldAux.inv

/-- Splitting fields have a division. -/
protected def div (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, splitting_field_aux n f → splitting_field_aux n f → splitting_field_aux n f :=
  Nat.recOn n (fun K fK f => @Div.div K _) fun n ih K fK f => ih
#align polynomial.splitting_field_aux.div Polynomial.SplittingFieldAux.div

/-- Splitting fields have powers by integers. -/
protected def zpow (n : ℕ) :
    ∀ {K : Type u} [Field K], ∀ {f : K[X]}, ℤ → splitting_field_aux n f → splitting_field_aux n f :=
  Nat.recOn n (fun K fK f n x => @Pow.pow K _ _ x n) fun n ih K fK f => ih
#align polynomial.splitting_field_aux.zpow Polynomial.SplittingFieldAux.zpow

-- I'm not sure why these two lemmas break, but inlining them seems to not work.
private theorem nsmul_zero (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ {f : K[X]} (x : splitting_field_aux n f), (0 : ℕ) • x = splitting_field_aux.zero n :=
  Nat.recOn n (fun K fK f => zero_nsmul) fun n ih K fK f => ih

private theorem nsmul_succ (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ {f : K[X]} (k : ℕ) (x : splitting_field_aux n f),
        (k + 1) • x = splitting_field_aux.add n x (k • x) :=
  Nat.recOn n (fun K fK f n x => succ_nsmul x n) fun n ih K fK f => ih

instance field (n : ℕ) {K : Type u} [Field K] {f : K[X]} : Field (SplittingFieldAux n f) :=
  by
  refine'
    { zero := splitting_field_aux.zero n
      one := splitting_field_aux.one n
      add := splitting_field_aux.add n
      zero_add :=
        have h := @zero_add
        _
      add_zero :=
        have h := @add_zero
        _
      add_assoc :=
        have h := @add_assoc
        _
      add_comm :=
        have h := @add_comm
        _
      neg := splitting_field_aux.neg n
      add_left_neg :=
        have h := @add_left_neg
        _
      sub := splitting_field_aux.sub n
      sub_eq_add_neg :=
        have h := @sub_eq_add_neg
        _
      mul := splitting_field_aux.mul n
      one_mul :=
        have h := @one_mul
        _
      mul_one :=
        have h := @mul_one
        _
      mul_assoc :=
        have h := @mul_assoc
        _
      left_distrib :=
        have h := @left_distrib
        _
      right_distrib :=
        have h := @right_distrib
        _
      mul_comm :=
        have h := @mul_comm
        _
      inv := splitting_field_aux.inv n
      inv_zero :=
        have h := @inv_zero
        _
      div := splitting_field_aux.div n
      div_eq_mul_inv :=
        have h := @div_eq_mul_inv
        _
      mul_inv_cancel :=
        have h := @mul_inv_cancel
        _
      exists_pair_ne :=
        have h := @exists_pair_ne
        _
      natCast := splitting_field_aux.mk n ∘ (coe : ℕ → K)
      natCast_zero :=
        have h := @CommRing.natCast_zero
        _
      natCast_succ :=
        have h := @CommRing.natCast_succ
        _
      nsmul := (· • ·)
      nsmul_zero := nsmul_zero n
      nsmul_succ := nsmul_succ n
      intCast := splitting_field_aux.mk n ∘ (coe : ℤ → K)
      intCast_ofNat :=
        have h := @CommRing.intCast_ofNat
        _
      intCast_negSucc :=
        have h := @CommRing.intCast_neg_succ_ofNat
        _
      zsmul := (· • ·)
      zsmul_zero' :=
        have h := @SubtractionCommMonoid.zsmul_zero'
        _
      zsmul_succ' :=
        have h := @SubtractionCommMonoid.zsmul_succ'
        _
      zsmul_neg' :=
        have h := @SubtractionCommMonoid.zsmul_neg'
        _
      ratCast := splitting_field_aux.mk n ∘ (coe : ℚ → K)
      ratCast_mk :=
        have h := @Field.ratCast_mk
        _
      qsmul := (· • ·)
      qsmul_eq_mul' :=
        have h := @Field.qsmul_eq_mul'
        _
      npow := splitting_field_aux.npow n
      npow_zero :=
        have h := @CommRing.npow_zero'
        _
      npow_succ :=
        have h := @CommRing.npow_succ'
        _
      zpow := splitting_field_aux.zpow n
      zpow_zero' :=
        have h := @Field.zpow_zero'
        _
      zpow_succ' :=
        have h := @Field.zpow_succ'
        _
      zpow_neg' :=
        have h := @Field.zpow_neg'
        _ }
  all_goals
    induction' n with n ih generalizing K
    · apply @h K
    · exact @ih _ _ _
#align polynomial.splitting_field_aux.field Polynomial.SplittingFieldAux.field

instance inhabited {n : ℕ} {f : K[X]} : Inhabited (SplittingFieldAux n f) :=
  ⟨37⟩
#align polynomial.splitting_field_aux.inhabited Polynomial.SplittingFieldAux.inhabited

/-- The injection from the base field as a ring homomorphism. -/
@[simps]
protected def mkHom (n : ℕ) {K : Type u} [Field K] {f : K[X]} : K →+* SplittingFieldAux n f
    where
  toFun := SplittingFieldAux.mk n
  map_one' := by
    induction' n with k hk generalizing K
    · simp [splitting_field_aux.mk]
    exact hk
  map_mul' := by
    induction' n with k hk generalizing K
    · simp [splitting_field_aux.mk]
    intro x y
    change (splitting_field_aux.mk k) ((AdjoinRoot.of f.factor) _) = _
    rw [map_mul]
    exact hk _ _
  map_zero' := by
    induction' n with k hk generalizing K
    · simp [splitting_field_aux.mk]
    change (splitting_field_aux.mk k) ((AdjoinRoot.of f.factor) 0) = _
    rw [map_zero, hk]
  map_add' := by
    induction' n with k hk generalizing K
    · simp [splitting_field_aux.mk]
    intro x y
    change (splitting_field_aux.mk k) ((AdjoinRoot.of f.factor) _) = _
    rw [map_add]
    exact hk _ _
#align polynomial.splitting_field_aux.mk_hom Polynomial.SplittingFieldAux.mkHom

instance algebra (n : ℕ) (R : Type _) {K : Type u} [CommSemiring R] [Field K] [Algebra R K]
    {f : K[X]} : Algebra R (SplittingFieldAux n f) :=
  {
    (SplittingFieldAux.mkHom n).comp
      (algebraMap R
        K) with
    toFun := (SplittingFieldAux.mkHom n).comp (algebraMap R K)
    smul := (· • ·)
    smul_def' := by
      induction' n with k hk generalizing K
      · exact Algebra.smul_def
      exact hk
    commutes' := fun a b => mul_comm _ _ }
#align polynomial.splitting_field_aux.algebra Polynomial.SplittingFieldAux.algebra

/-- Because `splitting_field_aux` is defined by recursion, we have to make sure all instances
on `splitting_field_aux` are defined by recursion within the fields. Otherwise, there will be
instance diamonds such as the following: -/
example (n : ℕ) {K : Type u} [Field K] {f : K[X]} :
    (AddCommMonoid.natModule : Module ℕ (SplittingFieldAux n f)) =
      @Algebra.toModule _ _ _ _ (SplittingFieldAux.algebra n _) :=
  rfl

end LiftInstances

instance algebra''' {n : ℕ} {f : K[X]} :
    Algebra (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor) :=
  SplittingFieldAux.algebra n _
#align polynomial.splitting_field_aux.algebra''' Polynomial.SplittingFieldAux.algebra'''

instance algebra' {n : ℕ} {f : K[X]} : Algebra (AdjoinRoot f.factor) (SplittingFieldAux n.succ f) :=
  SplittingFieldAux.algebra'''
#align polynomial.splitting_field_aux.algebra' Polynomial.SplittingFieldAux.algebra'

instance algebra'' {n : ℕ} {f : K[X]} : Algebra K (SplittingFieldAux n f.removeFactor) :=
  SplittingFieldAux.algebra n K
#align polynomial.splitting_field_aux.algebra'' Polynomial.SplittingFieldAux.algebra''

instance scalar_tower' {n : ℕ} {f : K[X]} :
    IsScalarTower K (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor) :=
  haveI : IsScalarTower K (AdjoinRoot f.factor) (AdjoinRoot f.factor) := IsScalarTower.right
  splitting_field_aux.is_scalar_tower n K (AdjoinRoot f.factor)
#align polynomial.splitting_field_aux.scalar_tower' Polynomial.SplittingFieldAux.scalar_tower'

instance scalar_tower {n : ℕ} {f : K[X]} :
    IsScalarTower K (AdjoinRoot f.factor) (SplittingFieldAux (n + 1) f) :=
  SplittingFieldAux.scalar_tower'
#align polynomial.splitting_field_aux.scalar_tower Polynomial.SplittingFieldAux.scalar_tower

theorem algebraMap_succ (n : ℕ) (f : K[X]) :
    algebraMap K (splitting_field_aux (n + 1) f) =
      (algebraMap (AdjoinRoot f.factor) (splitting_field_aux n f.remove_factor)).comp
        (AdjoinRoot.of f.factor) :=
  IsScalarTower.algebraMap_eq _ _ _
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

theorem exists_lift (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n) {L : Type _} [Field L],
        ∀ (j : K →+* L) (hf : splits j f),
          ∃ k : splitting_field_aux n f →+* L, k.comp (algebraMap _ _) = j :=
  Nat.recOn n (fun K _ _ _ L _ j _ => ⟨j, j.comp_id⟩) fun n ih K _ f hf L _ j hj =>
    have hndf : f.nat_degree ≠ 0 := by intro h; rw [h] at hf ; cases hf
    have hfn0 : f ≠ 0 := by intro h; rw [h] at hndf ; exact hndf rfl
    let ⟨r, hr⟩ :=
      exists_root_of_splits _
        (splits_of_splits_of_dvd j hfn0 hj (factor_dvd_of_nat_degree_ne_zero hndf))
        (mt is_unit_iff_degree_eq_zero.2 f.irreducible_factor.1)
    have hmf0 : map (AdjoinRoot.of f.factor) f ≠ 0 := map_ne_zero hfn0
    have hsf : splits (AdjoinRoot.lift j r hr) f.remove_factor :=
      by
      rw [← X_sub_C_mul_remove_factor _ hndf] at hmf0 ; refine' (splits_of_splits_mul _ hmf0 _).2
      rwa [X_sub_C_mul_remove_factor _ hndf, ← splits_id_iff_splits, map_map,
        AdjoinRoot.lift_comp_of, splits_id_iff_splits]
    let ⟨k, hk⟩ := ih f.remove_factor (nat_degree_remove_factor' hf) (AdjoinRoot.lift j r hr) hsf
    ⟨k, by rw [algebra_map_succ, ← RingHom.comp_assoc, hk, AdjoinRoot.lift_comp_of]⟩
#align polynomial.splitting_field_aux.exists_lift Polynomial.SplittingFieldAux.exists_lift

theorem adjoin_roots (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n),
        Algebra.adjoin K
            (↑(f.map <| algebraMap K <| splitting_field_aux n f).roots.toFinset :
              Set (splitting_field_aux n f)) =
          ⊤ :=
  Nat.recOn n (fun K _ f hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩)
    fun n ih K _ f hfn =>
    by
    have hndf : f.nat_degree ≠ 0 := by intro h; rw [h] at hfn ; cases hfn
    have hfn0 : f ≠ 0 := by intro h; rw [h] at hndf ; exact hndf rfl
    have hmf0 : map (algebraMap K (splitting_field_aux n.succ f)) f ≠ 0 := map_ne_zero hfn0
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
#align polynomial.splitting_field_aux.adjoin_roots Polynomial.SplittingFieldAux.adjoin_roots

end SplittingFieldAux

/-- A splitting field of a polynomial. -/
def SplittingField (f : K[X]) :=
  SplittingFieldAux f.natDegree f
#align polynomial.splitting_field Polynomial.SplittingField

namespace SplittingField

variable (f : K[X])

instance : Field (SplittingField f) :=
  SplittingFieldAux.field _

instance inhabited : Inhabited (SplittingField f) :=
  ⟨37⟩
#align polynomial.splitting_field.inhabited Polynomial.SplittingField.inhabited

instance algebra' {R} [CommSemiring R] [Algebra R K] : Algebra R (SplittingField f) :=
  SplittingFieldAux.algebra _ _
#align polynomial.splitting_field.algebra' Polynomial.SplittingField.algebra'

instance : Algebra K (SplittingField f) :=
  SplittingFieldAux.algebra _ _

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

example [CharZero K] : SplittingField.algebra' f = algebraRat :=
  rfl

example {q : ℚ[X]} : algebraInt (SplittingField q) = SplittingField.algebra' q :=
  rfl

protected theorem splits : Splits (algebraMap K (SplittingField f)) f :=
  SplittingFieldAux.splits _ _ rfl
#align polynomial.splitting_field.splits Polynomial.SplittingField.splits

variable [Algebra K L] (hb : Splits (algebraMap K L) f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : SplittingField f →ₐ[K] L :=
  { Classical.choose (SplittingFieldAux.exists_lift _ _ _ _ hb) with
    commutes' := fun r =>
      haveI := Classical.choose_spec (splitting_field_aux.exists_lift _ _ rfl _ hb)
      RingHom.ext_iff.1 this r }
#align polynomial.splitting_field.lift Polynomial.SplittingField.lift

theorem adjoin_roots :
    Algebra.adjoin K
        (↑(f.map (algebraMap K <| SplittingField f)).roots.toFinset : Set (SplittingField f)) =
      ⊤ :=
  SplittingFieldAux.adjoin_roots _ _ rfl
#align polynomial.splitting_field.adjoin_roots Polynomial.SplittingField.adjoin_roots

theorem adjoin_rootSet : Algebra.adjoin K (f.rootSet f.SplittingField) = ⊤ :=
  adjoin_roots f
#align polynomial.splitting_field.adjoin_root_set Polynomial.SplittingField.adjoin_rootSet

end SplittingField

end SplittingField

namespace IsSplittingField

variable (K L) [Algebra K L]

variable {K}

instance splittingField (f : K[X]) : IsSplittingField K (SplittingField f) f :=
  ⟨SplittingField.splits f, SplittingField.adjoin_roots f⟩
#align polynomial.is_splitting_field.splitting_field Polynomial.IsSplittingField.splittingField

instance (f : K[X]) : FiniteDimensional K f.SplittingField :=
  finiteDimensional f.SplittingField f

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

