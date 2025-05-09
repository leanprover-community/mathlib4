/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathlib.FieldTheory.Galois.Basic

/-!
# Galois Groups of Polynomials

In this file, we introduce the Galois group of a polynomial `p` over a field `F`,
defined as the automorphism group of its splitting field. We also provide
some results about some extension `E` above `p.SplittingField`.

## Main definitions

- `Polynomial.Gal p`: the Galois group of a polynomial p.
- `Polynomial.Gal.restrict p E`: the restriction homomorphism `(E ≃ₐ[F] E) → gal p`.
- `Polynomial.Gal.galAction p E`: the action of `gal p` on the roots of `p` in `E`.

## Main results

- `Polynomial.Gal.restrict_smul`: `restrict p E` is compatible with `gal_action p E`.
- `Polynomial.Gal.galActionHom_injective`: `gal p` acting on the roots of `p` in `E` is faithful.
- `Polynomial.Gal.restrictProd_injective`: `gal (p * q)` embeds as a subgroup of `gal p × gal q`.
- `Polynomial.Gal.card_of_separable`: For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`.
- `Polynomial.Gal.galActionHom_bijective_of_prime_degree`:
An irreducible polynomial of prime degree with two non-real roots has full Galois group.

## Other results
- `Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv`: The number of complex roots
equals the number of real roots plus the number of roots not fixed by complex conjugation
(i.e. with some imaginary component).

-/

assert_not_exists Real

noncomputable section

open scoped Polynomial

open Module

namespace Polynomial

variable {F : Type*} [Field F] (p q : F[X]) (E : Type*) [Field E] [Algebra F E]

/-- The Galois group of a polynomial. -/
def Gal :=
  p.SplittingField ≃ₐ[F] p.SplittingField
-- The `Group, Fintype` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

namespace Gal

instance instGroup : Group (Gal p) :=
  inferInstanceAs (Group (p.SplittingField ≃ₐ[F] p.SplittingField))

instance instFintype : Fintype (Gal p) :=
  inferInstanceAs (Fintype (p.SplittingField ≃ₐ[F] p.SplittingField))

instance : EquivLike p.Gal p.SplittingField p.SplittingField :=
  inferInstanceAs (EquivLike (p.SplittingField ≃ₐ[F] p.SplittingField) _ _)

instance : AlgEquivClass p.Gal F p.SplittingField p.SplittingField :=
  inferInstanceAs (AlgEquivClass (p.SplittingField ≃ₐ[F] p.SplittingField) F _ _)

instance applyMulSemiringAction : MulSemiringAction p.Gal p.SplittingField :=
  AlgEquiv.applyMulSemiringAction

@[ext]
theorem ext {σ τ : p.Gal} (h : ∀ x ∈ p.rootSet p.SplittingField, σ x = τ x) : σ = τ := by
  refine
    AlgEquiv.ext fun x =>
      (AlgHom.mem_equalizer σ.toAlgHom τ.toAlgHom x).mp
        ((SetLike.ext_iff.mp ?_ x).mpr Algebra.mem_top)
  rwa [eq_top_iff, ← SplittingField.adjoin_rootSet, Algebra.adjoin_le_iff]

/-- If `p` splits in `F` then the `p.gal` is trivial. -/
def uniqueGalOfSplits (h : p.Splits (RingHom.id F)) : Unique p.Gal where
  default := 1
  uniq f :=
    AlgEquiv.ext fun x => by
      obtain ⟨y, rfl⟩ :=
        Algebra.mem_bot.mp
          ((SetLike.ext_iff.mp ((IsSplittingField.splits_iff _ p).mp h) x).mp Algebra.mem_top)
      rw [AlgEquiv.commutes, AlgEquiv.commutes]

instance [h : Fact (p.Splits (RingHom.id F))] : Unique p.Gal :=
  uniqueGalOfSplits _ h.1

instance uniqueGalZero : Unique (0 : F[X]).Gal :=
  uniqueGalOfSplits _ (splits_zero _)

instance uniqueGalOne : Unique (1 : F[X]).Gal :=
  uniqueGalOfSplits _ (splits_one _)

instance uniqueGalC (x : F) : Unique (C x).Gal :=
  uniqueGalOfSplits _ (splits_C _ _)

instance uniqueGalX : Unique (X : F[X]).Gal :=
  uniqueGalOfSplits _ (splits_X _)

instance uniqueGalXSubC (x : F) : Unique (X - C x).Gal :=
  uniqueGalOfSplits _ (splits_X_sub_C _)

instance uniqueGalXPow (n : ℕ) : Unique (X ^ n : F[X]).Gal :=
  uniqueGalOfSplits _ (splits_X_pow _ _)

instance [h : Fact (p.Splits (algebraMap F E))] : Algebra p.SplittingField E :=
  (IsSplittingField.lift p.SplittingField p h.1).toRingHom.toAlgebra

instance [h : Fact (p.Splits (algebraMap F E))] : IsScalarTower F p.SplittingField E :=
  IsScalarTower.of_algebraMap_eq fun x =>
    ((IsSplittingField.lift p.SplittingField p h.1).commutes x).symm

-- The `Algebra p.SplittingField E` instance above behaves badly when
-- `E := p.SplittingField`, since it may result in a unification problem
-- `IsSplittingField.lift.toRingHom.toAlgebra =?= Algebra.id`,
-- which takes an extremely long time to resolve, causing timeouts.
-- Since we don't really care about this definition, marking it as irreducible
-- causes that unification to error out early.
/-- Restrict from a superfield automorphism into a member of `gal p`. -/
def restrict [Fact (p.Splits (algebraMap F E))] : (E ≃ₐ[F] E) →* p.Gal :=
  AlgEquiv.restrictNormalHom p.SplittingField

theorem restrict_surjective [Fact (p.Splits (algebraMap F E))] [Normal F E] :
    Function.Surjective (restrict p E) :=
  AlgEquiv.restrictNormalHom_surjective E

section RootsAction

/-- The function taking `rootSet p p.SplittingField` to `rootSet p E`. This is actually a bijection,
see `Polynomial.Gal.mapRoots_bijective`. -/
def mapRoots [Fact (p.Splits (algebraMap F E))] : rootSet p p.SplittingField → rootSet p E :=
  Set.MapsTo.restrict (IsScalarTower.toAlgHom F p.SplittingField E) _ _ <| rootSet_mapsTo _

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
    simp only [rootSet, Finset.mem_coe, Multiset.mem_toFinset, key, Multiset.mem_map] at hy
    rcases hy with ⟨x, hx1, hx2⟩
    exact ⟨⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr hx1⟩, Subtype.ext hx2⟩

/-- The bijection between `rootSet p p.SplittingField` and `rootSet p E`. -/
def rootsEquivRoots [Fact (p.Splits (algebraMap F E))] : rootSet p p.SplittingField ≃ rootSet p E :=
  Equiv.ofBijective (mapRoots p E) (mapRoots_bijective p E)

instance galActionAux : MulAction p.Gal (rootSet p p.SplittingField) where
  smul ϕ := Set.MapsTo.restrict ϕ _ _ <| rootSet_mapsTo ϕ.toAlgHom
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl

instance smul [Fact (p.Splits (algebraMap F E))] : SMul p.Gal (rootSet p E) where
  smul ϕ x := rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm x)

theorem smul_def [Fact (p.Splits (algebraMap F E))] (ϕ : p.Gal) (x : rootSet p E) :
    ϕ • x = rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm x) :=
  rfl

/-- The action of `gal p` on the roots of `p` in `E`. -/
instance galAction [Fact (p.Splits (algebraMap F E))] : MulAction p.Gal (rootSet p E) where
  one_smul _ := by simp only [smul_def, Equiv.apply_symm_apply, one_smul]
  mul_smul _ _ _ := by
    simp only [smul_def, Equiv.apply_symm_apply, Equiv.symm_apply_apply, mul_smul]

lemma galAction_isPretransitive [Fact (p.Splits (algebraMap F E))] (hp : Irreducible p) :
    MulAction.IsPretransitive p.Gal (p.rootSet E) := by
  refine ⟨fun x y ↦ ?_⟩
  have hx := minpoly.eq_of_irreducible hp (mem_rootSet.mp ((rootsEquivRoots p E).symm x).2).2
  have hy := minpoly.eq_of_irreducible hp (mem_rootSet.mp ((rootsEquivRoots p E).symm y).2).2
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp (hy.symm.trans hx)
  exact ⟨g, (rootsEquivRoots p E).apply_eq_iff_eq_symm_apply.mpr (Subtype.ext hg)⟩

variable {p E}

/-- `Polynomial.Gal.restrict p E` is compatible with `Polynomial.Gal.galAction p E`. -/
@[simp]
theorem restrict_smul [Fact (p.Splits (algebraMap F E))] (ϕ : E ≃ₐ[F] E) (x : rootSet p E) :
    ↑(restrict p E ϕ • x) = ϕ x := by
  let ψ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F p.SplittingField E)
  change ↑(ψ (ψ.symm _)) = ϕ x
  rw [AlgEquiv.apply_symm_apply ψ]
  change ϕ (rootsEquivRoots p E ((rootsEquivRoots p E).symm x)) = ϕ x
  rw [Equiv.apply_symm_apply (rootsEquivRoots p E)]

variable (p E)

/-- `Polynomial.Gal.galAction` as a permutation representation -/
def galActionHom [Fact (p.Splits (algebraMap F E))] : p.Gal →* Equiv.Perm (rootSet p E) :=
  MulAction.toPermHom _ _

theorem galActionHom_restrict [Fact (p.Splits (algebraMap F E))] (ϕ : E ≃ₐ[F] E) (x : rootSet p E) :
    ↑(galActionHom p E (restrict p E ϕ) x) = ϕ x :=
  restrict_smul ϕ x

/-- `gal p` embeds as a subgroup of permutations of the roots of `p` in `E`. -/
theorem galActionHom_injective [Fact (p.Splits (algebraMap F E))] :
    Function.Injective (galActionHom p E) := by
  rw [injective_iff_map_eq_one]
  intro ϕ hϕ
  ext (x hx)
  have key := Equiv.Perm.ext_iff.mp hϕ (rootsEquivRoots p E ⟨x, hx⟩)
  change
    rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm (rootsEquivRoots p E ⟨x, hx⟩)) =
      rootsEquivRoots p E ⟨x, hx⟩
    at key
  rw [Equiv.symm_apply_apply] at key
  exact Subtype.ext_iff.mp (Equiv.injective (rootsEquivRoots p E) key)

end RootsAction

variable {p q}

/-- `Polynomial.Gal.restrict`, when both fields are splitting fields of polynomials. -/
def restrictDvd (hpq : p ∣ q) : q.Gal →* p.Gal :=
  haveI := Classical.dec (q = 0)
  if hq : q = 0 then 1
  else
    @restrict F _ p _ _ _
      ⟨splits_of_splits_of_dvd (algebraMap F q.SplittingField) hq (SplittingField.splits q) hpq⟩

theorem restrictDvd_def [Decidable (q = 0)] (hpq : p ∣ q) :
    restrictDvd hpq =
      if hq : q = 0 then 1
      else
        @restrict F _ p _ _ _
          ⟨splits_of_splits_of_dvd (algebraMap F q.SplittingField) hq (SplittingField.splits q)
              hpq⟩ := by
  unfold restrictDvd
  congr

theorem restrictDvd_surjective (hpq : p ∣ q) (hq : q ≠ 0) :
    Function.Surjective (restrictDvd hpq) := by
  classical
  haveI := Fact.mk <|
    splits_of_splits_of_dvd (algebraMap F q.SplittingField) hq (SplittingField.splits q) hpq
  simpa only [restrictDvd_def, dif_neg hq] using restrict_surjective _ _

variable (p q)

/-- The Galois group of a product maps into the product of the Galois groups. -/
def restrictProd : (p * q).Gal →* p.Gal × q.Gal :=
  MonoidHom.prod (restrictDvd (dvd_mul_right p q)) (restrictDvd (dvd_mul_left q p))

/-- `Polynomial.Gal.restrictProd` is actually a subgroup embedding. -/
theorem restrictProd_injective : Function.Injective (restrictProd p q) := by
  by_cases hpq : p * q = 0
  · have : Unique (p * q).Gal := by rw [hpq]; infer_instance
    exact fun f g _ => Eq.trans (Unique.eq_default f) (Unique.eq_default g).symm
  intro f g hfg
  classical
  simp only [restrictProd, restrictDvd_def] at hfg
  simp only [dif_neg hpq, MonoidHom.prod_apply, Prod.mk_inj] at hfg
  ext (x hx)
  rw [rootSet_def, aroots_mul hpq] at hx
  rcases Multiset.mem_add.mp (Multiset.mem_toFinset.mp hx) with h | h
  · haveI : Fact (p.Splits (algebraMap F (p * q).SplittingField)) :=
      ⟨splits_of_splits_of_dvd _ hpq (SplittingField.splits (p * q)) (dvd_mul_right p q)⟩
    have key :
      x =
        algebraMap p.SplittingField (p * q).SplittingField
          ((rootsEquivRoots p _).invFun
            ⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr h⟩) :=
      Subtype.ext_iff.mp (Equiv.apply_symm_apply (rootsEquivRoots p _) ⟨x, _⟩).symm
    rw [key, ← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes]
    exact congr_arg _ (AlgEquiv.ext_iff.mp hfg.1 _)
  · haveI : Fact (q.Splits (algebraMap F (p * q).SplittingField)) :=
      ⟨splits_of_splits_of_dvd _ hpq (SplittingField.splits (p * q)) (dvd_mul_left q p)⟩
    have key :
      x =
        algebraMap q.SplittingField (p * q).SplittingField
          ((rootsEquivRoots q _).invFun
            ⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr h⟩) :=
      Subtype.ext_iff.mp (Equiv.apply_symm_apply (rootsEquivRoots q _) ⟨x, _⟩).symm
    rw [key, ← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes]
    exact congr_arg _ (AlgEquiv.ext_iff.mp hfg.2 _)

theorem mul_splits_in_splittingField_of_mul {p₁ q₁ p₂ q₂ : F[X]} (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (h₁ : p₁.Splits (algebraMap F q₁.SplittingField))
    (h₂ : p₂.Splits (algebraMap F q₂.SplittingField)) :
    (p₁ * p₂).Splits (algebraMap F (q₁ * q₂).SplittingField) := by
  apply splits_mul
  · rw [←
      (SplittingField.lift q₁
          (splits_of_splits_of_dvd (algebraMap F (q₁ * q₂).SplittingField) (mul_ne_zero hq₁ hq₂)
            (SplittingField.splits _) (dvd_mul_right q₁ q₂))).comp_algebraMap]
    exact splits_comp_of_splits _ _ h₁
  · rw [←
      (SplittingField.lift q₂
          (splits_of_splits_of_dvd (algebraMap F (q₁ * q₂).SplittingField) (mul_ne_zero hq₁ hq₂)
            (SplittingField.splits _) (dvd_mul_left q₂ q₁))).comp_algebraMap]
    exact splits_comp_of_splits _ _ h₂

/-- `p` splits in the splitting field of `p ∘ q`, for `q` non-constant. -/
theorem splits_in_splittingField_of_comp (hq : q.natDegree ≠ 0) :
    p.Splits (algebraMap F (p.comp q).SplittingField) := by
  let P : F[X] → Prop := fun r => r.Splits (algebraMap F (r.comp q).SplittingField)
  have key1 : ∀ {r : F[X]}, Irreducible r → P r := by
    intro r hr
    by_cases hr' : natDegree r = 0
    · exact splits_of_natDegree_le_one _ (le_trans (le_of_eq hr') zero_le_one)
    obtain ⟨x, hx⟩ :=
      exists_root_of_splits _ (SplittingField.splits (r.comp q)) fun h =>
        hr'
          ((mul_eq_zero.mp
                (natDegree_comp.symm.trans (natDegree_eq_of_degree_eq_some h))).resolve_right
            hq)
    rw [← aeval_def, aeval_comp] at hx
    have h_normal : Normal F (r.comp q).SplittingField := SplittingField.instNormal (r.comp q)
    have qx_int := Normal.isIntegral h_normal (aeval x q)
    exact
      splits_of_splits_of_dvd _ (minpoly.ne_zero qx_int) (Normal.splits h_normal _)
        ((minpoly.irreducible qx_int).dvd_symm hr (minpoly.dvd F _ hx))
  have key2 : ∀ {p₁ p₂ : F[X]}, P p₁ → P p₂ → P (p₁ * p₂) := by
    intro p₁ p₂ hp₁ hp₂
    by_cases h₁ : p₁.comp q = 0
    · rcases comp_eq_zero_iff.mp h₁ with h | h
      · rw [h, zero_mul]
        exact splits_zero _
      · exact False.elim (hq (by rw [h.2, natDegree_C]))
    by_cases h₂ : p₂.comp q = 0
    · rcases comp_eq_zero_iff.mp h₂ with h | h
      · rw [h, mul_zero]
        exact splits_zero _
      · exact False.elim (hq (by rw [h.2, natDegree_C]))
    have key := mul_splits_in_splittingField_of_mul h₁ h₂ hp₁ hp₂
    rwa [← mul_comp] at key
  exact
    WfDvdMonoid.induction_on_irreducible p (splits_zero _) (fun _ => splits_of_isUnit _)
      fun _ _ _ h => key2 (key1 h)

/-- `Polynomial.Gal.restrict` for the composition of polynomials. -/
def restrictComp (hq : q.natDegree ≠ 0) : (p.comp q).Gal →* p.Gal :=
  let h : Fact (Splits (algebraMap F (p.comp q).SplittingField) p) :=
    ⟨splits_in_splittingField_of_comp p q hq⟩
  @restrict F _ p _ _ _ h

theorem restrictComp_surjective (hq : q.natDegree ≠ 0) :
    Function.Surjective (restrictComp p q hq) := by
  haveI : Fact (Splits (algebraMap F (SplittingField (comp p q))) p) :=
    ⟨splits_in_splittingField_of_comp p q hq⟩
  simpa only [restrictComp] using restrict_surjective _ _

variable {p q}

open scoped IntermediateField

/-- For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`. -/
theorem card_of_separable (hp : p.Separable) : Fintype.card p.Gal = finrank F p.SplittingField :=
  haveI : IsGalois F p.SplittingField := IsGalois.of_separable_splitting_field hp
  IsGalois.card_aut_eq_finrank F p.SplittingField

theorem prime_degree_dvd_card [CharZero F] (p_irr : Irreducible p) (p_deg : p.natDegree.Prime) :
    p.natDegree ∣ Fintype.card p.Gal := by
  rw [Gal.card_of_separable p_irr.separable]
  have hp : p.degree ≠ 0 := fun h =>
    Nat.Prime.ne_zero p_deg (natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h))
  let α : p.SplittingField :=
    rootOfSplits (algebraMap F p.SplittingField) (SplittingField.splits p) hp
  have hα : IsIntegral F α := .of_finite F α
  use Module.finrank F⟮α⟯ p.SplittingField
  suffices (minpoly F α).natDegree = p.natDegree by
    letI _ : AddCommGroup F⟮α⟯ := Ring.toAddCommGroup
    rw [← Module.finrank_mul_finrank F F⟮α⟯ p.SplittingField,
      IntermediateField.adjoin.finrank hα, this]
  suffices minpoly F α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymm
    · exact natDegree_le_of_dvd this p_irr.ne_zero
    · exact natDegree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd F α
  rw [aeval_def, map_rootOfSplits _ (SplittingField.splits p) hp]

end Gal

end Polynomial
