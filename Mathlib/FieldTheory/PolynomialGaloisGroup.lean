/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz

! This file was ported from Lean 3 source module field_theory.polynomial_galois_group
! leanprover-community/mathlib commit e3f4be1fcb5376c4948d7f095bec45350bfb9d1a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.Galois
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Galois Groups of Polynomials

In this file, we introduce the Galois group of a polynomial `p` over a field `F`,
defined as the automorphism group of its splitting field. We also provide
some results about some extension `E` above `p.splitting_field`, and some specific
results about the Galois groups of ℚ-polynomials with specific numbers of non-real roots.

## Main definitions

- `polynomial.gal p`: the Galois group of a polynomial p.
- `polynomial.gal.restrict p E`: the restriction homomorphism `(E ≃ₐ[F] E) → gal p`.
- `polynomial.gal.gal_action p E`: the action of `gal p` on the roots of `p` in `E`.

## Main results

- `polynomial.gal.restrict_smul`: `restrict p E` is compatible with `gal_action p E`.
- `polynomial.gal.gal_action_hom_injective`: `gal p` acting on the roots of `p` in `E` is faithful.
- `polynomial.gal.restrict_prod_injective`: `gal (p * q)` embeds as a subgroup of `gal p × gal q`.
- `polynomial.gal.card_of_separable`: For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`.
- `polynomial.gal.gal_action_hom_bijective_of_prime_degree`:
An irreducible polynomial of prime degree with two non-real roots has full Galois group.

## Other results
- `polynomial.gal.card_complex_roots_eq_card_real_add_card_not_gal_inv`: The number of complex roots
equals the number of real roots plus the number of roots not fixed by complex conjugation
(i.e. with some imaginary component).

-/


noncomputable section

open scoped Polynomial

open FiniteDimensional

namespace Polynomial

variable {F : Type _} [Field F] (p q : F[X]) (E : Type _) [Field E] [Algebra F E]

/-- The Galois group of a polynomial. -/
def Gal :=
  p.SplittingField ≃ₐ[F] p.SplittingField
-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5020):
-- deriving Group, Fintype
#align polynomial.gal Polynomial.Gal

namespace Gal

instance instGroup : Group (Gal p) :=
  inferInstanceAs (Group (p.SplittingField ≃ₐ[F] p.SplittingField))
instance instFintype : Fintype (Gal p) :=
  inferInstanceAs (Fintype (p.SplittingField ≃ₐ[F] p.SplittingField))

instance : CoeFun p.Gal fun _ => p.SplittingField → p.SplittingField :=
  AlgEquiv.hasCoeToFun

instance applyMulSemiringAction : MulSemiringAction p.Gal p.SplittingField :=
  AlgEquiv.applyMulSemiringAction
#align polynomial.gal.apply_mul_semiring_action Polynomial.Gal.applyMulSemiringAction

@[ext]
theorem ext {σ τ : p.Gal} (h : ∀ x ∈ p.rootSet p.SplittingField, σ x = τ x) : σ = τ := by
  refine'
    AlgEquiv.ext fun x =>
      (AlgHom.mem_equalizer σ.toAlgHom τ.toAlgHom x).mp
        ((SetLike.ext_iff.mp _ x).mpr Algebra.mem_top)
  rw [eq_top_iff, ← SplittingField.adjoin_rootSet, Algebra.adjoin_le_iff]
#align polynomial.gal.ext Polynomial.Gal.ext

/-- If `p` splits in `F` then the `p.gal` is trivial. -/
def uniqueGalOfSplits (h : p.Splits (RingHom.id F)) : Unique p.Gal where
  default := 1
  uniq f :=
    AlgEquiv.ext fun x => by
      obtain ⟨y, rfl⟩ :=
        algebra.mem_bot.mp
          ((set_like.ext_iff.mp ((is_splitting_field.splits_iff _ p).mp h) x).mp Algebra.mem_top)
      rw [AlgEquiv.commutes, AlgEquiv.commutes]
#align polynomial.gal.unique_gal_of_splits Polynomial.Gal.uniqueGalOfSplits

instance [h : Fact (p.Splits (RingHom.id F))] : Unique p.Gal :=
  uniqueGalOfSplits _ h.1

instance uniqueGalZero : Unique (0 : F[X]).Gal :=
  uniqueGalOfSplits _ (splits_zero _)
#align polynomial.gal.unique_gal_zero Polynomial.Gal.uniqueGalZero

instance uniqueGalOne : Unique (1 : F[X]).Gal :=
  uniqueGalOfSplits _ (splits_one _)
#align polynomial.gal.unique_gal_one Polynomial.Gal.uniqueGalOne

instance uniqueGalC (x : F) : Unique (C x).Gal :=
  uniqueGalOfSplits _ (splits_C _ _)
#align polynomial.gal.unique_gal_C Polynomial.Gal.uniqueGalC

instance uniqueGalX : Unique (X : F[X]).Gal :=
  uniqueGalOfSplits _ (splits_X _)
#align polynomial.gal.unique_gal_X Polynomial.Gal.uniqueGalX

instance uniqueGalXSubC (x : F) : Unique (X - C x).Gal :=
  uniqueGalOfSplits _ (splits_X_sub_C _)
#align polynomial.gal.unique_gal_X_sub_C Polynomial.Gal.uniqueGalXSubC

instance uniqueGalXPow (n : ℕ) : Unique (X ^ n : F[X]).Gal :=
  uniqueGalOfSplits _ (splits_X_pow _ _)
#align polynomial.gal.unique_gal_X_pow Polynomial.Gal.uniqueGalXPow

instance [h : Fact (p.Splits (algebraMap F E))] : Algebra p.SplittingField E :=
  (IsSplittingField.lift p.SplittingField p h.1).toRingHom.toAlgebra

instance [h : Fact (p.Splits (algebraMap F E))] : IsScalarTower F p.SplittingField E :=
  IsScalarTower.of_algebraMap_eq fun x =>
    ((IsSplittingField.lift p.SplittingField p h.1).commutes x).symm

-- The `algebra p.splitting_field E` instance above behaves badly when
-- `E := p.splitting_field`, since it may result in a unification problem
-- `is_splitting_field.lift.to_ring_hom.to_algebra =?= algebra.id`,
-- which takes an extremely long time to resolve, causing timeouts.
-- Since we don't really care about this definition, marking it as irreducible
-- causes that unification to error out early.
/-- Restrict from a superfield automorphism into a member of `gal p`. -/
def restrict [Fact (p.Splits (algebraMap F E))] : (E ≃ₐ[F] E) →* p.Gal :=
  AlgEquiv.restrictNormalHom p.SplittingField
#align polynomial.gal.restrict Polynomial.Gal.restrict

theorem restrict_surjective [Fact (p.Splits (algebraMap F E))] [Normal F E] :
    Function.Surjective (restrict p E) :=
  AlgEquiv.restrictNormalHom_surjective E
#align polynomial.gal.restrict_surjective Polynomial.Gal.restrict_surjective

section RootsAction

/-- The function taking `roots p p.splitting_field` to `roots p E`. This is actually a bijection,
see `polynomial.gal.map_roots_bijective`. -/
def mapRoots [Fact (p.Splits (algebraMap F E))] : rootSet p p.SplittingField → rootSet p E :=
  Set.MapsTo.restrict (IsScalarTower.toAlgHom F p.SplittingField E) _ _ <| rootSet_mapsTo _
#align polynomial.gal.map_roots Polynomial.Gal.mapRoots

theorem mapRoots_bijective [h : Fact (p.Splits (algebraMap F E))] :
    Function.Bijective (mapRoots p E) := by
  constructor
  · exact fun _ _ h => Subtype.ext (RingHom.injective _ (Subtype.ext_iff.mp h))
  · intro y
    -- this is just an equality of two different ways to write the roots of `p` as an `E`-polynomial
    have key :=
      roots_map (IsScalarTower.toAlgHom F p.SplittingField E : p.SplittingField →+* E)
        ((splits_id_iff_splits _).mpr (IsSplittingField.splits p.SplittingField p))
    rw [map_map, AlgHom.comp_algebraMap] at key
    have hy := Subtype.mem y
    simp only [rootSet, Finset.mem_coe, (Multiset.mem_toFinset), key, Multiset.mem_map] at hy
    rcases hy with ⟨x, hx1, hx2⟩
    exact ⟨⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr hx1⟩, Subtype.ext hx2⟩
#align polynomial.gal.map_roots_bijective Polynomial.Gal.mapRoots_bijective

/-- The bijection between `root_set p p.splitting_field` and `root_set p E`. -/
def rootsEquivRoots [Fact (p.Splits (algebraMap F E))] : rootSet p p.SplittingField ≃ rootSet p E :=
  Equiv.ofBijective (mapRoots p E) (mapRoots_bijective p E)
#align polynomial.gal.roots_equiv_roots Polynomial.Gal.rootsEquivRoots

instance galActionAux : MulAction p.Gal (rootSet p p.SplittingField) where
  smul ϕ := Set.MapsTo.restrict ϕ _ _ <| rootSet_mapsTo ϕ.toAlgHom
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl
#align polynomial.gal.gal_action_aux Polynomial.Gal.galActionAux

/-- The action of `gal p` on the roots of `p` in `E`. -/
instance galAction [Fact (p.Splits (algebraMap F E))] : MulAction p.Gal (rootSet p E) where
  smul ϕ x := rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm x)
  one_smul _ := by simp only [Equiv.apply_symm_apply, one_smul]
  mul_smul _ _ _ := by simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, mul_smul]
#align polynomial.gal.gal_action Polynomial.Gal.galAction

variable {p E}

/-- `polynomial.gal.restrict p E` is compatible with `polynomial.gal.gal_action p E`. -/
@[simp]
theorem restrict_smul [Fact (p.Splits (algebraMap F E))] (ϕ : E ≃ₐ[F] E) (x : rootSet p E) :
    ↑(restrict p E ϕ • x) = ϕ x := by
  let ψ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F p.SplittingField E)
  change ↑(ψ (ψ.symm _)) = ϕ x
  rw [AlgEquiv.apply_symm_apply ψ]
  change ϕ (roots_equiv_roots p E ((roots_equiv_roots p E).symm x)) = ϕ x
  rw [Equiv.apply_symm_apply (roots_equiv_roots p E)]
#align polynomial.gal.restrict_smul Polynomial.Gal.restrict_smul

variable (p E)

/-- `polynomial.gal.gal_action` as a permutation representation -/
def galActionHom [Fact (p.Splits (algebraMap F E))] : p.Gal →* Equiv.Perm (rootSet p E) :=
  MulAction.toPermHom _ _
#align polynomial.gal.gal_action_hom Polynomial.Gal.galActionHom

theorem galActionHom_restrict [Fact (p.Splits (algebraMap F E))] (ϕ : E ≃ₐ[F] E) (x : rootSet p E) :
    ↑(galActionHom p E (restrict p E ϕ) x) = ϕ x :=
  restrict_smul ϕ x
#align polynomial.gal.gal_action_hom_restrict Polynomial.Gal.galActionHom_restrict

/-- `gal p` embeds as a subgroup of permutations of the roots of `p` in `E`. -/
theorem galActionHom_injective [Fact (p.Splits (algebraMap F E))] :
    Function.Injective (galActionHom p E) := by
  rw [injective_iff_map_eq_one]
  intro ϕ hϕ
  ext (x hx)
  have key := equiv.perm.ext_iff.mp hϕ (roots_equiv_roots p E ⟨x, hx⟩)
  change
    roots_equiv_roots p E (ϕ • (roots_equiv_roots p E).symm (roots_equiv_roots p E ⟨x, hx⟩)) =
      roots_equiv_roots p E ⟨x, hx⟩
    at key
  rw [Equiv.symm_apply_apply] at key
  exact subtype.ext_iff.mp (Equiv.injective (roots_equiv_roots p E) key)
#align polynomial.gal.gal_action_hom_injective Polynomial.Gal.galActionHom_injective

end RootsAction

variable {p q}

/-- `polynomial.gal.restrict`, when both fields are splitting fields of polynomials. -/
def restrictDvd (hpq : p ∣ q) : q.Gal →* p.Gal :=
  haveI := Classical.dec (q = 0)
  if hq : q = 0 then 1
  else
    @restrict F _ p _ _ _
      ⟨splits_of_splits_of_dvd (algebraMap F q.SplittingField) hq (SplittingField.splits q) hpq⟩
#align polynomial.gal.restrict_dvd Polynomial.Gal.restrictDvd

theorem restrictDvd_def [Decidable (q = 0)] (hpq : p ∣ q) :
    restrictDvd hpq =
      if hq : q = 0 then 1
      else
        @restrict F _ p _ _ _
          ⟨splits_of_splits_of_dvd (algebraMap F q.SplittingField) hq (SplittingField.splits q)
              hpq⟩ :=
  by convert rfl
#align polynomial.gal.restrict_dvd_def Polynomial.Gal.restrictDvd_def

theorem restrictDvd_surjective (hpq : p ∣ q) (hq : q ≠ 0) : Function.Surjective (restrictDvd hpq) :=
  by classical simp only [restrictDvd_def, dif_neg hq, (restrict_surjective)]
#align polynomial.gal.restrict_dvd_surjective Polynomial.Gal.restrictDvd_surjective

variable (p q)

/-- The Galois group of a product maps into the product of the Galois groups.  -/
def restrictProd : (p * q).Gal →* p.Gal × q.Gal :=
  MonoidHom.prod (restrictDvd (dvd_mul_right p q)) (restrictDvd (dvd_mul_left q p))
#align polynomial.gal.restrict_prod Polynomial.Gal.restrictProd

/-- `polynomial.gal.restrict_prod` is actually a subgroup embedding. -/
theorem restrictProd_injective : Function.Injective (restrictProd p q) := by
  by_cases hpq : p * q = 0
  · have : Unique (p * q).Gal := by rw [hpq]; infer_instance
    exact fun f g h => Eq.trans (Unique.eq_default f) (Unique.eq_default g).symm
  intro f g hfg
  classical
  simp only [restrictProd, restrictDvd_def] at hfg
  simp only [dif_neg hpq, MonoidHom.prod_apply, Prod.mk.inj_iff] at hfg
  ext (x)
  intro hx
  rw [rootSet_def, Polynomial.map_mul, Polynomial.roots_mul] at hx
  cases' Multiset.mem_add.mp (Multiset.mem_toFinset.mp hx) with h h
  · haveI : Fact (p.splits (algebraMap F (p * q).SplittingField)) :=
      ⟨splits_of_splits_of_dvd _ hpq (splitting_field.splits (p * q)) (dvd_mul_right p q)⟩
    have key :
      x =
        algebraMap p.splitting_field (p * q).SplittingField
          ((roots_equiv_roots p _).invFun
            ⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr h⟩) :=
      subtype.ext_iff.mp (Equiv.apply_symm_apply (roots_equiv_roots p _) ⟨x, _⟩).symm
    rw [key, ← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes]
    exact congr_arg _ (alg_equiv.ext_iff.mp hfg.1 _)
  · haveI : Fact (q.splits (algebraMap F (p * q).SplittingField)) :=
      ⟨splits_of_splits_of_dvd _ hpq (splitting_field.splits (p * q)) (dvd_mul_left q p)⟩
    have key :
      x =
        algebraMap q.splitting_field (p * q).SplittingField
          ((roots_equiv_roots q _).invFun
            ⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr h⟩) :=
      subtype.ext_iff.mp (Equiv.apply_symm_apply (roots_equiv_roots q _) ⟨x, _⟩).symm
    rw [key, ← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes]
    exact congr_arg _ (alg_equiv.ext_iff.mp hfg.2 _)
  · rwa [Ne.def, mul_eq_zero, map_eq_zero, map_eq_zero, ← mul_eq_zero]
#align polynomial.gal.restrict_prod_injective Polynomial.Gal.restrictProd_injective

theorem mul_splits_in_splittingField_of_mul {p₁ q₁ p₂ q₂ : F[X]} (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (h₁ : p₁.Splits (algebraMap F q₁.SplittingField))
    (h₂ : p₂.Splits (algebraMap F q₂.SplittingField)) :
    (p₁ * p₂).Splits (algebraMap F (q₁ * q₂).SplittingField) := by
  apply splits_mul
  · rw [←
      (splitting_field.lift q₁
          (splits_of_splits_of_dvd (algebraMap F (q₁ * q₂).SplittingField) (mul_ne_zero hq₁ hq₂)
            (splitting_field.splits _) (dvd_mul_right q₁ q₂))).comp_algebraMap]
    exact splits_comp_of_splits _ _ h₁
  · rw [←
      (splitting_field.lift q₂
          (splits_of_splits_of_dvd (algebraMap F (q₁ * q₂).SplittingField) (mul_ne_zero hq₁ hq₂)
            (splitting_field.splits _) (dvd_mul_left q₂ q₁))).comp_algebraMap]
    exact splits_comp_of_splits _ _ h₂
#align polynomial.gal.mul_splits_in_splitting_field_of_mul Polynomial.Gal.mul_splits_in_splittingField_of_mul

/-- `p` splits in the splitting field of `p ∘ q`, for `q` non-constant. -/
theorem splits_in_splittingField_of_comp (hq : q.natDegree ≠ 0) :
    p.Splits (algebraMap F (p.comp q).SplittingField) := by
  let P : F[X] → Prop := fun r => r.Splits (algebraMap F (r.comp q).SplittingField)
  have key1 : ∀ {r : F[X]}, Irreducible r → P r := by
    intro r hr
    by_cases hr' : nat_degree r = 0
    · exact splits_of_nat_degree_le_one _ (le_trans (le_of_eq hr') zero_le_one)
    obtain ⟨x, hx⟩ :=
      exists_root_of_splits _ (splitting_field.splits (r.comp q)) fun h =>
        hr'
          ((mul_eq_zero.mp
                (nat_degree_comp.symm.trans (nat_degree_eq_of_degree_eq_some h))).resolve_right
            hq)
    rw [← aeval_def, aeval_comp] at hx
    have h_normal : Normal F (r.comp q).SplittingField := splitting_field.normal (r.comp q)
    have qx_int := Normal.isIntegral h_normal (aeval x q)
    exact
      splits_of_splits_of_dvd _ (minpoly.ne_zero qx_int) (Normal.splits h_normal _)
        ((minpoly.irreducible qx_int).dvd_symm hr (minpoly.dvd F _ hx))
  have key2 : ∀ {p₁ p₂ : F[X]}, P p₁ → P p₂ → P (p₁ * p₂) := by
    intro p₁ p₂ hp₁ hp₂
    by_cases h₁ : p₁.comp q = 0
    · cases' comp_eq_zero_iff.mp h₁ with h h
      · rw [h, MulZeroClass.zero_mul]
        exact splits_zero _
      · exact False.ndrec _ (hq (by rw [h.2, nat_degree_C]))
    by_cases h₂ : p₂.comp q = 0
    · cases' comp_eq_zero_iff.mp h₂ with h h
      · rw [h, MulZeroClass.mul_zero]
        exact splits_zero _
      · exact False.ndrec _ (hq (by rw [h.2, nat_degree_C]))
    have key := mul_splits_in_splitting_field_of_mul h₁ h₂ hp₁ hp₂
    rwa [← mul_comp] at key
  exact
    WfDvdMonoid.induction_on_irreducible p (splits_zero _) (fun _ => splits_of_is_unit _)
      fun _ _ _ h => key2 (key1 h)
#align polynomial.gal.splits_in_splitting_field_of_comp Polynomial.Gal.splits_in_splittingField_of_comp

/-- `polynomial.gal.restrict` for the composition of polynomials. -/
def restrictComp (hq : q.natDegree ≠ 0) : (p.comp q).Gal →* p.Gal :=
  let h : Fact (Splits (algebraMap F (p.comp q).SplittingField) p) :=
    ⟨splits_in_splittingField_of_comp p q hq⟩
  @restrict F _ p _ _ _ h
#align polynomial.gal.restrict_comp Polynomial.Gal.restrictComp

theorem restrictComp_surjective (hq : q.natDegree ≠ 0) :
    Function.Surjective (restrictComp p q hq) := by simp only [restrict_comp, restrict_surjective]
#align polynomial.gal.restrict_comp_surjective Polynomial.Gal.restrictComp_surjective

variable {p q}

/-- For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`. -/
theorem card_of_separable (hp : p.Separable) : Fintype.card p.Gal = finrank F p.SplittingField :=
  haveI : IsGalois F p.splitting_field := IsGalois.of_separable_splitting_field hp
  IsGalois.card_aut_eq_finrank F p.splitting_field
#align polynomial.gal.card_of_separable Polynomial.Gal.card_of_separable

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem prime_degree_dvd_card [CharZero F] (p_irr : Irreducible p) (p_deg : p.natDegree.Prime) :
    p.natDegree ∣ Fintype.card p.Gal := by
  rw [gal.card_of_separable p_irr.separable]
  have hp : p.degree ≠ 0 := fun h =>
    Nat.Prime.ne_zero p_deg (nat_degree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h))
  let α : p.splitting_field :=
    root_of_splits (algebraMap F p.splitting_field) (splitting_field.splits p) hp
  have hα : IsIntegral F α := Algebra.isIntegral_of_finite _ _ α
  use FiniteDimensional.finrank F⟮⟯ p.splitting_field
  suffices (minpoly F α).natDegree = p.nat_degree by
    rw [← FiniteDimensional.finrank_mul_finrank F F⟮⟯ p.splitting_field,
      IntermediateField.adjoin.finrank hα, this]
  suffices minpoly F α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymm
    · exact nat_degree_le_of_dvd this p_irr.ne_zero
    · exact nat_degree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd F α
  rw [aeval_def, map_root_of_splits _ (splitting_field.splits p) hp]
#align polynomial.gal.prime_degree_dvd_card Polynomial.Gal.prime_degree_dvd_card

section Rationals

theorem splits_ℚ_ℂ {p : ℚ[X]} : Fact (p.Splits (algebraMap ℚ ℂ)) :=
  ⟨IsAlgClosed.splits_codomain p⟩
#align polynomial.gal.splits_ℚ_ℂ Polynomial.Gal.splits_ℚ_ℂ

attribute [local instance] splits_ℚ_ℂ

/-- The number of complex roots equals the number of real roots plus
    the number of roots not fixed by complex conjugation (i.e. with some imaginary component). -/
theorem card_complex_roots_eq_card_real_add_card_not_gal_inv (p : ℚ[X]) :
    (p.rootSet ℂ).toFinset.card =
      (p.rootSet ℝ).toFinset.card +
        (galActionHom p ℂ (restrict p ℂ (Complex.conjAe.restrictScalars ℚ))).support.card := by
  by_cases hp : p = 0
  · haveI : IsEmpty (p.root_set ℂ) := by rw [hp, root_set_zero]; infer_instance
    simp_rw [(gal_action_hom p ℂ _).support.eq_empty_of_isEmpty, hp, root_set_zero,
      Set.toFinset_empty, Finset.card_empty]
  have inj : Function.Injective (IsScalarTower.toAlgHom ℚ ℝ ℂ) := (algebraMap ℝ ℂ).Injective
  rw [← Finset.card_image_of_injective _ Subtype.coe_injective, ←
    Finset.card_image_of_injective _ inj]
  let a : Finset ℂ := _
  let b : Finset ℂ := _
  let c : Finset ℂ := _
  change a.card = b.card + c.card
  have ha : ∀ z : ℂ, z ∈ a ↔ aeval z p = 0 := by intro z;
    rw [Set.mem_toFinset, mem_root_set_of_ne hp]; infer_instance
  have hb : ∀ z : ℂ, z ∈ b ↔ aeval z p = 0 ∧ z.im = 0 := by
    intro z
    simp_rw [Finset.mem_image, exists_prop, Set.mem_toFinset, mem_root_set_of_ne hp]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨by rw [aeval_alg_hom_apply, hw, AlgHom.map_zero], rfl⟩
    · rintro ⟨hz1, hz2⟩
      have key : IsScalarTower.toAlgHom ℚ ℝ ℂ z.re = z := by ext; rfl; rw [hz2]; rfl
      exact ⟨z.re, inj (by rwa [← aeval_alg_hom_apply, key, AlgHom.map_zero]), key⟩
  have hc0 :
    ∀ w : p.root_set ℂ,
      gal_action_hom p ℂ (restrict p ℂ (complex.conj_ae.restrict_scalars ℚ)) w = w ↔ w.val.im = 0 :=
    by
    intro w
    rw [Subtype.ext_iff, gal_action_hom_restrict]
    exact Complex.conj_eq_iff_im
  have hc : ∀ z : ℂ, z ∈ c ↔ aeval z p = 0 ∧ z.im ≠ 0 := by
    intro z
    simp_rw [Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(mem_root_set.mp w.2).2, mt (hc0 w).mpr (equiv.perm.mem_support.mp hw)⟩
    · rintro ⟨hz1, hz2⟩
      exact ⟨⟨z, mem_root_set.mpr ⟨hp, hz1⟩⟩, equiv.perm.mem_support.mpr (mt (hc0 _).mp hz2), rfl⟩
  rw [← Finset.card_disjoint_union]
  · apply congr_arg Finset.card
    simp_rw [Finset.ext_iff, Finset.mem_union, ha, hb, hc]
    tauto
  · rw [Finset.disjoint_left]
    intro z
    rw [hb, hc]
    tauto
  · infer_instance
#align polynomial.gal.card_complex_roots_eq_card_real_add_card_not_gal_inv Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv

/-- An irreducible polynomial of prime degree with two non-real roots has full Galois group. -/
theorem galActionHom_bijective_of_prime_degree {p : ℚ[X]} (p_irr : Irreducible p)
    (p_deg : p.natDegree.Prime)
    (p_roots : Fintype.card (p.rootSet ℂ) = Fintype.card (p.rootSet ℝ) + 2) :
    Function.Bijective (galActionHom p ℂ) := by
  classical
  have h1 : Fintype.card (p.root_set ℂ) = p.nat_degree := by
    simp_rw [root_set_def, Finset.coe_sort_coe, Fintype.card_coe]
    rw [Multiset.toFinset_card_of_nodup, ← nat_degree_eq_card_roots]
    · exact IsAlgClosed.splits_codomain p
    · exact nodup_roots ((separable_map (algebraMap ℚ ℂ)).mpr p_irr.separable)
  have h2 : Fintype.card p.gal = Fintype.card (gal_action_hom p ℂ).range :=
    Fintype.card_congr (MonoidHom.ofInjective (gal_action_hom_injective p ℂ)).toEquiv
  let conj := restrict p ℂ (complex.conj_ae.restrict_scalars ℚ)
  refine'
    ⟨gal_action_hom_injective p ℂ, fun x =>
      (congr_arg (Membership.Mem x) (show (gal_action_hom p ℂ).range = ⊤ from _)).mpr
        (Subgroup.mem_top x)⟩
  apply Equiv.Perm.subgroup_eq_top_of_swap_mem
  · rwa [h1]
  · rw [h1]
    convert prime_degree_dvd_card p_irr p_deg using 1
    convert h2.symm
  · exact ⟨conj, rfl⟩
  · rw [← Equiv.Perm.card_support_eq_two]
    apply Nat.add_left_cancel
    rw [← p_roots, ← Set.toFinset_card (root_set p ℝ), ← Set.toFinset_card (root_set p ℂ)]
    exact (card_complex_roots_eq_card_real_add_card_not_gal_inv p).symm
#align polynomial.gal.gal_action_hom_bijective_of_prime_degree Polynomial.Gal.galActionHom_bijective_of_prime_degree

/-- An irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group. -/
theorem galActionHom_bijective_of_prime_degree' {p : ℚ[X]} (p_irr : Irreducible p)
    (p_deg : p.natDegree.Prime)
    (p_roots1 : Fintype.card (p.rootSet ℝ) + 1 ≤ Fintype.card (p.rootSet ℂ))
    (p_roots2 : Fintype.card (p.rootSet ℂ) ≤ Fintype.card (p.rootSet ℝ) + 3) :
    Function.Bijective (galActionHom p ℂ) := by
  apply gal_action_hom_bijective_of_prime_degree p_irr p_deg
  let n := (gal_action_hom p ℂ (restrict p ℂ (complex.conj_ae.restrict_scalars ℚ))).support.card
  have hn : 2 ∣ n :=
    Equiv.Perm.two_dvd_card_support
      (by
        rw [← MonoidHom.map_pow, ← MonoidHom.map_pow,
          show AlgEquiv.restrictScalars ℚ Complex.conjAe ^ 2 = 1 from
            AlgEquiv.ext Complex.conj_conj,
          MonoidHom.map_one, MonoidHom.map_one])
  have key := card_complex_roots_eq_card_real_add_card_not_gal_inv p
  simp_rw [Set.toFinset_card] at key
  rw [key, add_le_add_iff_left] at p_roots1 p_roots2
  rw [key, add_right_inj]
  suffices ∀ m : ℕ, 2 ∣ m → 1 ≤ m → m ≤ 3 → m = 2 by exact this n hn p_roots1 p_roots2
  rintro m ⟨k, rfl⟩ h2 h3
  exact
    le_antisymm
      (nat.lt_succ_iff.mp
        (lt_of_le_of_ne h3 (show 2 * k ≠ 2 * 1 + 1 from Nat.two_mul_ne_two_mul_add_one)))
      (nat.succ_le_iff.mpr
        (lt_of_le_of_ne h2 (show 2 * 0 + 1 ≠ 2 * k from nat.two_mul_ne_two_mul_add_one.symm)))
#align polynomial.gal.gal_action_hom_bijective_of_prime_degree' Polynomial.Gal.galActionHom_bijective_of_prime_degree'

end Rationals

end Gal

end Polynomial
