/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module field_theory.splitting_field
! leanprover-community/mathlib commit b353176c24d96c23f0ce1cc63efc3f55019702d9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IntermediateField
import Mathlib.RingTheory.Adjoin.Field

/-!
# Splitting fields

This file introduces the notion of a splitting field of a polynomial and provides an embedding from
a splitting field to any field that splits the polynomial. A polynomial `f : K[X]` splits
over a field extension `L` of `K` if it is zero or all of its irreducible factors over `L` have
degree `1`. A field extension of `K` of a polynomial `f : K[X]` is called a splitting field
if it is the smallest field extension of `K` such that `f` splits.

## Main definitions

* `polynomial.splitting_field f`: A fixed splitting field of the polynomial `f`.
* `polynomial.is_splitting_field`: A predicate on a field to be a splitting field of a polynomial
  `f`.

## Main statements

* `polynomial.is_splitting_field.lift`: An embedding of a splitting field of the polynomial `f` into
  another field such that `f` splits.
* `polynomial.is_splitting_field.alg_equiv`: Every splitting field of a polynomial `f` is isomorphic
  to `splitting_field f` and thus, being a splitting field is unique up to isomorphism.

-/


noncomputable section

open Classical BigOperators Polynomial

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
  by_cases hf2 : f = 0;
  · rw [hf2]
    exact dvd_zero _
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
def SplittingFieldAux (n : ℕ) : ∀ {K : Type u} [Field K], ∀ _ : K[X], Type u :=
  -- Porting note: added motive
  Nat.recOn (motive := fun (_x : ℕ) => ∀ {K : Type u} [_inst_4 : Field K], K[X] → Type u)
    n (fun {K} _ _ => K) fun _ ih _ _ f => ih f.removeFactor
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
protected def zero (n : ℕ) : ∀ {K : Type u} [Field K], ∀ {f : K[X]}, SplittingFieldAux n f :=
  Nat.recOn (motive := (fun (n : ℕ) => ∀ {K : Type u} [Field K] {f : K[X]}, SplittingFieldAux n f))
    n (fun {K} _ _ => @Zero.zero K _) fun _ ih _ _ _ => ih
#align polynomial.splitting_field_aux.zero Polynomial.SplittingFieldAux.zero

/-- Splitting fields have an addition. -/
protected def add (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, SplittingFieldAux n f → SplittingFieldAux n f → SplittingFieldAux n f :=
  Nat.recOn
    (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, SplittingFieldAux n f → SplittingFieldAux n f → SplittingFieldAux n f)
    n (fun {K} _ _ => @Add.add K _) fun _ ih _ _ _ => ih
#align polynomial.splitting_field_aux.add Polynomial.SplittingFieldAux.add

set_option synthInstance.maxHeartbeats 30000 in
/-- Splitting fields inherit scalar multiplication. -/
protected def smul (n : ℕ) :
    ∀ (α : Type _) {K : Type u} [Field K],
      ∀ [DistribSMul α K],
        ∀ [IsScalarTower α K K] {f : K[X]}, α → SplittingFieldAux n f → SplittingFieldAux n f :=
  Nat.recOn
    (motive := fun n => ∀ (α : Type _) {K : Type u} [Field K],
      ∀ [DistribSMul α K],
        ∀ [IsScalarTower α K K] {f : K[X]}, α → SplittingFieldAux n f → SplittingFieldAux n f)
    n (fun α {K} fK ds _ _ => @SMul.smul _ K _) fun n ih α K fK ds ist f => by exact ih α
#align polynomial.splitting_field_aux.smul Polynomial.SplittingFieldAux.smul

instance hasSmul (α : Type _) (n : ℕ) {K : Type u} [Field K] [DistribSMul α K] [IsScalarTower α K K]
    {f : K[X]} : SMul α (SplittingFieldAux n f) :=
  ⟨SplittingFieldAux.smul n α⟩
#align polynomial.splitting_field_aux.has_smul Polynomial.SplittingFieldAux.hasSmul

set_option synthInstance.maxHeartbeats 30000 in
instance isScalarTower (n : ℕ) :
    ∀ (R₁ R₂ : Type _) {K : Type u} [SMul R₁ R₂] [Field K],
      ∀ [DistribSMul R₂ K] [DistribSMul R₁ K],
        ∀ [IsScalarTower R₁ K K] [IsScalarTower R₂ K K] [IsScalarTower R₁ R₂ K] {f : K[X]},
          IsScalarTower R₁ R₂ (SplittingFieldAux n f) :=
  Nat.recOn
    (motive := fun (n : ℕ) =>
    ∀ (R₁ R₂ : Type _) {K : Type u} [SMul R₁ R₂] [Field K],
      ∀ [DistribSMul R₂ K] [DistribSMul R₁ K],
        ∀ [IsScalarTower R₁ K K] [IsScalarTower R₂ K K] [IsScalarTower R₁ R₂ K] {f : K[X]},
          IsScalarTower R₁ R₂ (SplittingFieldAux n f))
    n
    (fun R₁ R₂ {K} _ _ hs₂ hs₁ _ _ h f => by
      rcases hs₁ with @⟨@⟨⟨hs₁⟩, _⟩, _⟩
      rcases hs₂ with @⟨@⟨⟨hs₂⟩, _⟩, _⟩
      exact h)
    fun n ih R₁ R₂ K _ _ _ _ _ _ _ f => ih R₁ R₂
#align polynomial.splitting_field_aux.is_scalar_tower Polynomial.SplittingFieldAux.isScalarTower

/-- Splitting fields have a negation. -/
protected def neg (n : ℕ) :
    ∀ {K : Type u} [Field K], ∀ {f : K[X]}, SplittingFieldAux n f → SplittingFieldAux n f :=
  Nat.recOn
    (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, SplittingFieldAux n f → SplittingFieldAux n f)
    n (fun {K} _ _ => @Neg.neg K _) fun _ ih _ _ _ => ih
#align polynomial.splitting_field_aux.neg Polynomial.SplittingFieldAux.neg

/-- Splitting fields have subtraction. -/
protected def sub (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, SplittingFieldAux n f → SplittingFieldAux n f → SplittingFieldAux n f :=
  Nat.recOn
    (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, SplittingFieldAux n f → SplittingFieldAux n f → SplittingFieldAux n f)
    n (fun {K} _ _ => @Sub.sub K _) fun _ ih _ _ _ => ih
#align polynomial.splitting_field_aux.sub Polynomial.SplittingFieldAux.sub

/-- Splitting fields have a one. -/
protected def one (n : ℕ) : ∀ {K : Type u} [Field K], ∀ {f : K[X]}, SplittingFieldAux n f :=
  Nat.recOn
    (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, SplittingFieldAux n f)
    n (fun {K} _ _ => @One.one K _) fun _ ih _ _ _ => ih
#align polynomial.splitting_field_aux.one Polynomial.SplittingFieldAux.one

/-- Splitting fields have a multiplication. -/
protected def mul (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, SplittingFieldAux n f → SplittingFieldAux n f → SplittingFieldAux n f :=
  Nat.recOn
    (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, SplittingFieldAux n f → SplittingFieldAux n f → SplittingFieldAux n f)
    n (fun {K} _ _ => @Mul.mul K _) fun _ ih _ _ _ => ih
#align polynomial.splitting_field_aux.mul Polynomial.SplittingFieldAux.mul

/-- Splitting fields have a power operation. -/
protected def npow (n : ℕ) :
    ∀ {K : Type u} [Field K], ∀ {f : K[X]}, ℕ → SplittingFieldAux n f → SplittingFieldAux n f :=
  Nat.recOn
    (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, ℕ → SplittingFieldAux n f → SplittingFieldAux n f)
    n (fun {K} _ _ n x => @Pow.pow K _ _ x n) fun _ ih _ _ _ => ih
#align polynomial.splitting_field_aux.npow Polynomial.SplittingFieldAux.npow

/-- Splitting fields have an injection from the base field. -/
protected def mk (n : ℕ) : ∀ {K : Type u} [Field K], ∀ {f : K[X]}, K → SplittingFieldAux n f :=
  Nat.recOn
    (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, K → SplittingFieldAux n f)
    n (fun {_} _ _ => id) fun _ ih _ _ _ => ih ∘ (↑)
#align polynomial.splitting_field_aux.mk Polynomial.SplittingFieldAux.mk

-- note that `coe` goes from `K → adjoin_root f`, and then `ih` lifts to the full splitting field
-- (as we generalise over all fields in this recursion!)
/-- Splitting fields have an inverse. -/
protected def inv (n : ℕ) :
    ∀ {K : Type u} [Field K], ∀ {f : K[X]}, SplittingFieldAux n f → SplittingFieldAux n f :=
  Nat.recOn
    (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, SplittingFieldAux n f → SplittingFieldAux n f)
    n (fun {K} _ _ => @Inv.inv K _) fun _ ih _ _ _ => ih
#align polynomial.splitting_field_aux.inv Polynomial.SplittingFieldAux.inv

/-- Splitting fields have a division. -/
protected def div (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, SplittingFieldAux n f → SplittingFieldAux n f → SplittingFieldAux n f :=
  Nat.recOn
    (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, SplittingFieldAux n f → SplittingFieldAux n f → SplittingFieldAux n f)
    n (fun {K} _ _ => @Div.div K _) fun _ ih _ _ _ => ih
#align polynomial.splitting_field_aux.div Polynomial.SplittingFieldAux.div

/-- Splitting fields have powers by integers. -/
protected def zpow (n : ℕ) :
    ∀ {K : Type u} [Field K], ∀ {f : K[X]}, ℤ → SplittingFieldAux n f → SplittingFieldAux n f :=
  Nat.recOn
    (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ {f : K[X]}, ℤ → SplittingFieldAux n f → SplittingFieldAux n f)
    n (fun {K} _ _ n x => @Pow.pow K _ _ x n) fun _ ih _ _ _ => ih
#align polynomial.splitting_field_aux.zpow Polynomial.SplittingFieldAux.zpow

-- I'm not sure why these two lemmas break, but inlining them seems to not work.
-- Porting note: original proof was `Nat.recOn n (fun K fK f => zero_nsmul) fun n ih K fK f => ih`
private theorem nsmul_zero (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ {f : K[X]} (x : SplittingFieldAux n f), (0 : ℕ) • x = SplittingFieldAux.zero n := by
  induction' n with _ hn
  · intro K fK f
    change ∀ (x : K), (0 : ℕ) • x = SplittingFieldAux.zero 0
    exact zero_nsmul
  · intro K fK f
    apply hn

set_option maxHeartbeats 300000 in
-- Porting note: original proof was
-- `Nat.recOn n (fun K fK f n x => succ_nsmul x n) fun n ih K fK f => ih`
private theorem nsmul_succ (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ {f : K[X]} (k : ℕ) (x : SplittingFieldAux n f),
        (k + 1) • x = SplittingFieldAux.add n x (k • x) := by
  induction' n with _ hn
  · intro K fK _ k
    change ∀ (x : K), (k + 1) • x = x + (k • x)
    intro x
    exact succ_nsmul x _
  · intro K fK f
    apply hn

set_option maxHeartbeats 3500000 in
instance field (n : ℕ) {K : Type u} [Field K] {f : K[X]} : Field (SplittingFieldAux n f) := by
  refine'
    { zero := SplittingFieldAux.zero n
      one := SplittingFieldAux.one n
      add := SplittingFieldAux.add n
      zero_add := have h := @zero_add
        _
      add_zero := have h := @add_zero
        _
      add_assoc := have h := @add_assoc
        _
      add_comm := have h := @add_comm
        _
      neg := SplittingFieldAux.neg n
      add_left_neg := have h := @add_left_neg
        _
      sub := SplittingFieldAux.sub n
      sub_eq_add_neg := have h := @sub_eq_add_neg
        _
      mul := SplittingFieldAux.mul n
      zero_mul := have h := @zero_mul
        _
      mul_zero := have h := @mul_zero
        _
      one_mul := have h := @one_mul
        _
      mul_one := have h := @mul_one
        _
      mul_assoc := have h := @mul_assoc
        _
      left_distrib := have h := @left_distrib
        _
      right_distrib := have h := @right_distrib
        _
      mul_comm := have h := @mul_comm
        _
      inv := SplittingFieldAux.inv n
      inv_zero := have h := @inv_zero
        _
      div := SplittingFieldAux.div n
      div_eq_mul_inv := have h := @div_eq_mul_inv
        _
      mul_inv_cancel := have h := @mul_inv_cancel
        _
      exists_pair_ne := have h := @exists_pair_ne
        _
      natCast := SplittingFieldAux.mk n ∘ (fun (k : ℕ) => (k : K))
      natCast_zero := have h := @AddMonoidWithOne.natCast_zero
        _
      natCast_succ := have h := @AddMonoidWithOne.natCast_succ
        _
      nsmul := (· • ·)
      nsmul_zero := fun x => nsmul_zero n x
      nsmul_succ := nsmul_succ n
      intCast := SplittingFieldAux.mk n ∘ ((↑) : ℤ → K)
      intCast_ofNat := have h := @AddGroupWithOne.intCast_ofNat
        _
      intCast_negSucc := have h := @AddGroupWithOne.intCast_negSucc
        _
      zsmul := (· • ·)
      zsmul_zero' :=  have h := @SubNegMonoid.zsmul_zero'
        _
      zsmul_succ' := have h := @SubNegMonoid.zsmul_succ'
        _
      zsmul_neg' := have h := @SubNegMonoid.zsmul_neg'
        _
      ratCast := SplittingFieldAux.mk n ∘ ((↑) : ℚ → K)
      ratCast_mk := have h := @Field.ratCast_mk
        _
      qsmul := (· • ·)
      qsmul_eq_mul' := have h := @Field.qsmul_eq_mul'
        _
      npow := SplittingFieldAux.npow n
      npow_zero := have h := @Monoid.npow_zero
        _
      npow_succ :=  have h := @Monoid.npow_succ
        _
      zpow := SplittingFieldAux.zpow n
      zpow_zero' := have h := @Field.zpow_zero'
        _
      zpow_succ' := have h := @Field.zpow_succ'
        _
      zpow_neg' := have h := @Field.zpow_neg'
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
protected def mkHom (n : ℕ) {K : Type u} [Field K] {f : K[X]} : K →+* SplittingFieldAux n f where
  toFun := SplittingFieldAux.mk n
  map_one' := by
    induction' n with _ hk generalizing K
    · simp [SplittingFieldAux.mk]
    exact hk
  map_mul' := by
    induction' n with k hk generalizing K
    · simp [SplittingFieldAux.mk]
    intro x y
    change (SplittingFieldAux.mk k) ((AdjoinRoot.of f.factor) _) = _
    rw [map_mul]
    exact hk _ _
  map_zero' := by
    induction' n with k hk generalizing K
    · simp [SplittingFieldAux.mk]
    simp only at hk ⊢
    change (SplittingFieldAux.mk k) ((AdjoinRoot.of f.factor) 0) = _
    rw [map_zero, hk]
  map_add' := by
    induction' n with k hk generalizing K
    · simp [SplittingFieldAux.mk]
    simp only at hk ⊢
    intro x y
    change (SplittingFieldAux.mk k) ((AdjoinRoot.of f.factor) _) = _
    rw [map_add]
    exact hk _ _
#align polynomial.splitting_field_aux.mk_hom Polynomial.SplittingFieldAux.mkHom

instance algebra (n : ℕ) (R : Type _) {K : Type u} [CommSemiring R] [Field K] [Algebra R K]
    {f : K[X]} : Algebra R (SplittingFieldAux n f) :=
  { (SplittingFieldAux.mkHom n).comp (algebraMap R K) with
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
  haveI-- finding this instance ourselves makes things faster
   : IsScalarTower K (AdjoinRoot f.factor) (AdjoinRoot f.factor) := IsScalarTower.right
  splitting_field_aux.is_scalar_tower n K (AdjoinRoot f.factor)
#align polynomial.splitting_field_aux.scalar_tower' Polynomial.SplittingFieldAux.scalar_tower'

instance scalar_tower {n : ℕ} {f : K[X]} :
    IsScalarTower K (AdjoinRoot f.factor) (SplittingFieldAux (n + 1) f) :=
  SplittingFieldAux.scalar_tower'
#align polynomial.splitting_field_aux.scalar_tower Polynomial.SplittingFieldAux.scalar_tower

theorem algebraMap_succ (n : ℕ) (f : K[X]) :
    algebraMap K (SplittingFieldAux (n + 1) f) =
      (algebraMap (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor)).comp
        (AdjoinRoot.of f.factor) :=
  IsScalarTower.algebraMap_eq _ _ _
#align polynomial.splitting_field_aux.algebra_map_succ Polynomial.SplittingFieldAux.algebraMap_succ

protected theorem splits (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n), Splits (algebraMap K <| SplittingFieldAux n f) f :=
  Nat.recOn
    (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n), Splits (algebraMap K <| SplittingFieldAux n f) f)
    n
    (fun {K} _ _ hf =>
      splits_of_degree_le_one _
        (le_trans degree_le_natDegree <| hf.symm ▸ WithBot.coe_le_coe.2 zero_le_one))
    fun n ih K _ f hf => by
    rw [← splits_id_iff_splits, algebraMap_succ, ← map_map, splits_id_iff_splits, ←
      X_sub_C_mul_remove_factor f fun h => by
        rw [h] at hf
        cases hf]
    exact splits_mul _ (splits_X_sub_C _) (ih _ (natDegree_removeFactor' hf))
#align polynomial.splitting_field_aux.splits Polynomial.SplittingFieldAux.splits

theorem exists_lift (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n) {L : Type _} [Field L],
        ∀ (j : K →+* L) (hf : Splits j f),
          ∃ k : SplittingFieldAux n f →+* L, k.comp (algebraMap _ _) = j :=
  Nat.recOn n (fun {K} _ _ _ L _ j _ => ⟨j, j.comp_id⟩) fun n ih K _ f hf L _ j hj =>
    have hndf : f.natDegree ≠ 0 := by
      intro h
      rw [h] at hf
      cases hf
    have hfn0 : f ≠ 0 := by
      intro h
      rw [h] at hndf
      exact hndf rfl
    let ⟨r, hr⟩ :=
      exists_root_of_splits _
        (splits_of_splits_of_dvd j hfn0 hj (factor_dvd_of_natDegree_ne_zero hndf))
        (mt isUnit_iff_degree_eq_zero.2 f.irreducible_factor.1)
    have hmf0 : map (AdjoinRoot.of f.factor) f ≠ 0 := map_ne_zero hfn0
    have hsf : Splits (AdjoinRoot.lift j r hr) f.removeFactor := by
      rw [← X_sub_C_mul_removeFactor _ hndf] at hmf0
      refine' (splits_of_splits_mul _ hmf0 _).2
      rwa [X_sub_C_mul_removeFactor _ hndf, ← splits_id_iff_splits, map_map,
        AdjoinRoot.lift_comp_of, splits_id_iff_splits]
    let ⟨k, hk⟩ := ih f.removeFactor (natDegree_removeFactor' hf) (AdjoinRoot.lift j r hr) hsf
    ⟨k, by rw [algebra_map_succ, ← RingHom.comp_assoc, hk, AdjoinRoot.lift_comp_of]⟩
#align polynomial.splitting_field_aux.exists_lift Polynomial.SplittingFieldAux.exists_lift

theorem adjoin_roots (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n),
        Algebra.adjoin K
            (↑(f.map <| algebraMap K <| SplittingFieldAux n f).roots.toFinset :
              Set (SplittingFieldAux n f)) =
          ⊤ :=
  Nat.recOn n (fun K _ f hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩)
    fun n ih K _ f hfn => by
    have hndf : f.natDegree ≠ 0 := by
      intro h
      rw [h] at hfn
      cases hfn
    have hfn0 : f ≠ 0 := by
      intro h
      rw [h] at hndf
      exact hndf rfl
    have hmf0 : map (algebraMap K (SplittingFieldAux n.succ f)) f ≠ 0 := map_ne_zero hfn0
    rw [algebra_map_succ, ← map_map, ← X_sub_C_mul_removeFactor _ hndf, Polynomial.map_mul]
      at hmf0⊢
    rw [roots_mul hmf0, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.toFinset_add,
      Finset.coe_union, Multiset.toFinset_singleton, Finset.coe_singleton,
      Algebra.adjoin_union_eq_adjoin_adjoin, ← Set.image_singleton,
      Algebra.adjoin_algebraMap K (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor),
      AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top,
      IsScalarTower.adjoin_range_toAlgHom K (AdjoinRoot f.factor)
        (SplittingFieldAux n f.removeFactor),
      ih _ (natDegree_removeFactor' hfn), Subalgebra.restrictScalars_top]
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
  charZero_of_injective_algebraMap (algebraMap K _).injective

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
      haveI := Classical.choose_spec (SplittingFieldAux.exists_lift _ _ rfl _ hb)
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

variable (K L)
variable [Algebra K L]

/-- Typeclass characterising splitting fields. -/
class IsSplittingField (f : K[X]) : Prop where
  splits' : Splits (algebraMap K L) f
  adjoin_roots' : Algebra.adjoin K (↑(f.map (algebraMap K L)).roots.toFinset : Set L) = ⊤
#align polynomial.is_splitting_field Polynomial.IsSplittingField

namespace IsSplittingField

variable {K}

-- Porting note: infer kinds are unsupported
theorem splits (f : K[X]) [IsSplittingField K L f] : Splits (algebraMap K L) f :=
  splits'
#align polynomial.is_splitting_field.splits Polynomial.IsSplittingField.splits

-- Porting note: infer kinds are unsupported
theorem adjoin_roots (f : K[X]) [IsSplittingField K L f] :
    Algebra.adjoin K (↑(f.map (algebraMap K L)).roots.toFinset : Set L) = ⊤ :=
  adjoin_roots'
#align polynomial.is_splitting_field.adjoin_roots Polynomial.IsSplittingField.adjoin_roots

instance splittingField (f : K[X]) : IsSplittingField K (SplittingField f) f :=
  ⟨SplittingField.splits f, SplittingField.adjoin_roots f⟩
#align polynomial.is_splitting_field.splitting_field Polynomial.IsSplittingField.splittingField

section ScalarTower

variable {L}
variable [Algebra F K] [Algebra F L] [IsScalarTower F K L]

instance map (f : F[X]) [IsSplittingField F L f] : IsSplittingField K L (f.map <| algebraMap F K) :=
  ⟨by
    rw [splits_map_iff, ← IsScalarTower.algebraMap_eq]
    exact splits L f,
    Subalgebra.restrictScalars_injective F <| by
      rw [map_map, ← IsScalarTower.algebraMap_eq, Subalgebra.restrictScalars_top, eq_top_iff, ←
        adjoin_roots L f, Algebra.adjoin_le_iff]
      exact fun x hx => @Algebra.subset_adjoin K _ _ _ _ _ _ hx⟩
#align polynomial.is_splitting_field.map Polynomial.IsSplittingField.map

variable (L)

theorem splits_iff (f : K[X]) [IsSplittingField K L f] :
    Polynomial.Splits (RingHom.id K) f ↔ (⊤ : Subalgebra K L) = ⊥ :=
  ⟨fun h => by
    -- Porting note: replaced term-mode proof
    rw [eq_bot_iff, ← adjoin_roots L f, roots_map (algebraMap K L) h, Algebra.adjoin_le_iff]
    intro y hy
    rw [Multiset.toFinset_map, Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨x : K, -, hxy : algebraMap K L x = y⟩ := hy
    rw [← hxy]
    exact SetLike.mem_coe.2 <| Subalgebra.algebraMap_mem _ _,
    fun h =>
    @RingEquiv.toRingHom_refl K _ ▸
      RingEquiv.self_trans_symm (RingEquiv.ofBijective _ <| Algebra.bijective_algebraMap_iff.2 h) ▸
        by
        rw [RingEquiv.toRingHom_trans]
        exact splits_comp_of_splits _ _ (splits L f)⟩
#align polynomial.is_splitting_field.splits_iff Polynomial.IsSplittingField.splits_iff

theorem mul (f g : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) [IsSplittingField F K f]
    [IsSplittingField K L (g.map <| algebraMap F K)] : IsSplittingField F L (f * g) :=
  ⟨(IsScalarTower.algebraMap_eq F K L).symm ▸
      splits_mul _ (splits_comp_of_splits _ _ (splits K f))
        ((splits_map_iff _ _).1 (splits L <| g.map <| algebraMap F K)), by
    rw [Polynomial.map_mul,
      roots_mul (mul_ne_zero (map_ne_zero hf : f.map (algebraMap F L) ≠ 0) (map_ne_zero hg)),
      Multiset.toFinset_add, Finset.coe_union, Algebra.adjoin_union_eq_adjoin_adjoin,
      IsScalarTower.algebraMap_eq F K L, ← map_map,
      roots_map (algebraMap K L) ((splits_id_iff_splits <| algebraMap F K).2 <| splits K f),
      Multiset.toFinset_map, Finset.coe_image, Algebra.adjoin_algebraMap, adjoin_roots,
      Algebra.map_top, IsScalarTower.adjoin_range_toAlgHom, ← map_map, adjoin_roots,
      Subalgebra.restrictScalars_top]⟩
#align polynomial.is_splitting_field.mul Polynomial.IsSplittingField.mul

end ScalarTower

/-- Splitting field of `f` embeds into any field that splits `f`. -/
def lift [Algebra K F] (f : K[X]) [IsSplittingField K L f]
    (hf : Polynomial.Splits (algebraMap K F) f) : L →ₐ[K] F :=
  if hf0 : f = 0 then
    (Algebra.ofId K F).comp <|
      (Algebra.botEquiv K L : (⊥ : Subalgebra K L) →ₐ[K] K).comp <| by
        rw [← (splits_iff L f).1 (show f.Splits (RingHom.id K) from hf0.symm ▸ splits_zero _)]
        exact Algebra.toTop
  else
    AlgHom.comp
      (by
        rw [← adjoin_roots L f]
        exact
          Classical.choice
            (lift_of_splits _ fun y hy =>
              have : aeval y f = 0 :=
                (eval₂_eq_eval_map _).trans <|
                  (mem_roots <| map_ne_zero hf0).1 (Multiset.mem_toFinset.mp hy)
              ⟨isAlgebraic_iff_isIntegral.1 ⟨f, hf0, this⟩,
                splits_of_splits_of_dvd _ hf0 hf <| minpoly.dvd _ _ this⟩))
      Algebra.toTop
#align polynomial.is_splitting_field.lift Polynomial.IsSplittingField.lift

theorem finiteDimensional (f : K[X]) [IsSplittingField K L f] : FiniteDimensional K L :=
  ⟨@Algebra.top_toSubmodule K L _ _ _ ▸
      adjoin_roots L f ▸
        FG_adjoin_of_finite (Finset.finite_toSet _) fun y hy =>
          if hf : f = 0 then by
            rw [hf, Polynomial.map_zero, roots_zero] at hy
            cases hy
          else
            isAlgebraic_iff_isIntegral.1
              ⟨f, hf,
                (eval₂_eq_eval_map _).trans <|
                  (mem_roots <| map_ne_zero hf).1 (Multiset.mem_toFinset.mp hy)⟩⟩
#align polynomial.is_splitting_field.finite_dimensional Polynomial.IsSplittingField.finiteDimensional

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

theorem of_algEquiv [Algebra K F] (p : K[X]) (f : F ≃ₐ[K] L) [IsSplittingField K F p] :
    IsSplittingField K L p := by
  constructor
  · rw [← f.toAlgHom.comp_algebraMap]
    exact splits_comp_of_splits _ _ (splits F p)
  · rw [← (Algebra.range_top_iff_surjective f.toAlgHom).mpr f.surjective, ← rootSet,
      adjoin_rootSet_eq_range (splits F p), rootSet, adjoin_roots F p]
#align polynomial.is_splitting_field.of_alg_equiv Polynomial.IsSplittingField.of_algEquiv

end IsSplittingField

end SplittingField

end Polynomial

namespace IntermediateField

open Polynomial

variable [Field K] [Field L] [Algebra K L] {p : K[X]}

theorem splits_of_splits {F : IntermediateField K L} (h : p.Splits (algebraMap K L))
    (hF : ∀ x ∈ p.rootSet L, x ∈ F) : p.Splits (algebraMap K F) := by
  simp_rw [rootSet, Finset.mem_coe, Multiset.mem_toFinset] at hF
  rw [splits_iff_exists_multiset]
  refine' ⟨Multiset.pmap Subtype.mk _ hF, map_injective _ (algebraMap F L).injective _⟩
  conv_lhs =>
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, eq_prod_roots_of_splits h, ←
      Multiset.pmap_eq_map _ _ _ hF]
  simp_rw [Polynomial.map_mul, Polynomial.map_multiset_prod, Multiset.map_pmap, Polynomial.map_sub,
    map_C, map_X]
  rfl
#align intermediate_field.splits_of_splits IntermediateField.splits_of_splits

end IntermediateField
