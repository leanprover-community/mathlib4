/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison

! This file was ported from Lean 3 source module linear_algebra.invariant_basis_number
! leanprover-community/mathlib commit 5fd3186f1ec30a75d5f65732e3ce5e623382556f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Ideal.Quotient
import Mathbin.RingTheory.PrincipalIdealDomain

/-!
# Invariant basis number property

We say that a ring `R` satisfies the invariant basis number property if there is a well-defined
notion of the rank of a finitely generated free (left) `R`-module. Since a finitely generated free
module with a basis consisting of `n` elements is linearly equivalent to `fin n → R`, it is
sufficient that `(fin n → R) ≃ₗ[R] (fin m → R)` implies `n = m`.

It is also useful to consider two stronger conditions, namely the rank condition,
that a surjective linear map `(fin n → R) →ₗ[R] (fin m → R)` implies `m ≤ n` and
the strong rank condition, that an injective linear map `(fin n → R) →ₗ[R] (fin m → R)`
implies `n ≤ m`.

The strong rank condition implies the rank condition, and the rank condition implies
the invariant basis number property.

## Main definitions

`strong_rank_condition R` is a type class stating that `R` satisfies the strong rank condition.
`rank_condition R` is a type class stating that `R` satisfies the rank condition.
`invariant_basis_number R` is a type class stating that `R` has the invariant basis number property.

## Main results

We show that every nontrivial left-noetherian ring satisfies the strong rank condition,
(and so in particular every division ring or field),
and then use this to show every nontrivial commutative ring has the invariant basis number property.

More generally, every commutative ring satisfies the strong rank condition. This is proved in
`linear_algebra/free_module/strong_rank_condition`. We keep
`invariant_basis_number_of_nontrivial_of_comm_ring` here since it imports fewer files.

## Future work

So far, there is no API at all for the `invariant_basis_number` class. There are several natural
ways to formulate that a module `M` is finitely generated and free, for example
`M ≃ₗ[R] (fin n → R)`, `M ≃ₗ[R] (ι → R)`, where `ι` is a fintype, or providing a basis indexed by
a finite type. There should be lemmas applying the invariant basis number property to each
situation.

The finite version of the invariant basis number property implies the infinite analogue, i.e., that
`(ι →₀ R) ≃ₗ[R] (ι' →₀ R)` implies that `cardinal.mk ι = cardinal.mk ι'`. This fact (and its
variants) should be formalized.

## References

* https://en.wikipedia.org/wiki/Invariant_basis_number
* https://mathoverflow.net/a/2574/

## Tags

free module, rank, invariant basis number, IBN

-/


noncomputable section

open Classical BigOperators

open Function

universe u v w

section

variable (R : Type u) [Semiring R]

/-- We say that `R` satisfies the strong rank condition if `(fin n → R) →ₗ[R] (fin m → R)` injective
    implies `n ≤ m`. -/
@[mk_iff]
class StrongRankCondition : Prop where
  le_of_fin_injective : ∀ {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R), Injective f → n ≤ m
#align strong_rank_condition StrongRankCondition

theorem le_of_fin_injective [StrongRankCondition R] {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R) :
    Injective f → n ≤ m :=
  StrongRankCondition.le_of_fin_injective f
#align le_of_fin_injective le_of_fin_injective

/-- A ring satisfies the strong rank condition if and only if, for all `n : ℕ`, any linear map
`(fin (n + 1) → R) →ₗ[R] (fin n → R)` is not injective. -/
theorem strongRankCondition_iff_succ :
    StrongRankCondition R ↔
      ∀ (n : ℕ) (f : (Fin (n + 1) → R) →ₗ[R] Fin n → R), ¬Function.Injective f :=
  by
  refine' ⟨fun h n => fun f hf => _, fun h => ⟨fun n m f hf => _⟩⟩
  · letI : StrongRankCondition R := h
    exact Nat.not_succ_le_self n (le_of_fin_injective R f hf)
  · by_contra H
    exact
      h m (f.comp (Function.ExtendByZero.linearMap R (Fin.castLe (not_le.1 H))))
        (hf.comp (Function.extend_injective (RelEmbedding.injective _) 0))
#align strong_rank_condition_iff_succ strongRankCondition_iff_succ

theorem card_le_of_injective [StrongRankCondition R] {α β : Type _} [Fintype α] [Fintype β]
    (f : (α → R) →ₗ[R] β → R) (i : Injective f) : Fintype.card α ≤ Fintype.card β :=
  by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact
    le_of_fin_injective R ((Q.symm.to_linear_map.comp f).comp P.to_linear_map)
      (((LinearEquiv.symm Q).Injective.comp i).comp (LinearEquiv.injective P))
#align card_le_of_injective card_le_of_injective

theorem card_le_of_injective' [StrongRankCondition R] {α β : Type _} [Fintype α] [Fintype β]
    (f : (α →₀ R) →ₗ[R] β →₀ R) (i : Injective f) : Fintype.card α ≤ Fintype.card β :=
  by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact
    card_le_of_injective R ((P.to_linear_map.comp f).comp Q.to_linear_map)
      ((P.injective.comp i).comp Q.injective)
#align card_le_of_injective' card_le_of_injective'

/-- We say that `R` satisfies the rank condition if `(fin n → R) →ₗ[R] (fin m → R)` surjective
    implies `m ≤ n`. -/
class RankCondition : Prop where
  le_of_fin_surjective : ∀ {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R), Surjective f → m ≤ n
#align rank_condition RankCondition

theorem le_of_fin_surjective [RankCondition R] {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R) :
    Surjective f → m ≤ n :=
  RankCondition.le_of_fin_surjective f
#align le_of_fin_surjective le_of_fin_surjective

theorem card_le_of_surjective [RankCondition R] {α β : Type _} [Fintype α] [Fintype β]
    (f : (α → R) →ₗ[R] β → R) (i : Surjective f) : Fintype.card β ≤ Fintype.card α :=
  by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact
    le_of_fin_surjective R ((Q.symm.to_linear_map.comp f).comp P.to_linear_map)
      (((LinearEquiv.symm Q).Surjective.comp i).comp (LinearEquiv.surjective P))
#align card_le_of_surjective card_le_of_surjective

theorem card_le_of_surjective' [RankCondition R] {α β : Type _} [Fintype α] [Fintype β]
    (f : (α →₀ R) →ₗ[R] β →₀ R) (i : Surjective f) : Fintype.card β ≤ Fintype.card α :=
  by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact
    card_le_of_surjective R ((P.to_linear_map.comp f).comp Q.to_linear_map)
      ((P.surjective.comp i).comp Q.surjective)
#align card_le_of_surjective' card_le_of_surjective'

/-- By the universal property for free modules, any surjective map `(fin n → R) →ₗ[R] (fin m → R)`
has an injective splitting `(fin m → R) →ₗ[R] (fin n → R)`
from which the strong rank condition gives the necessary inequality for the rank condition.
-/
instance (priority := 100) rankCondition_of_strongRankCondition [StrongRankCondition R] :
    RankCondition R
    where le_of_fin_surjective n m f s :=
    le_of_fin_injective R _ (f.splittingOfFunOnFintypeSurjective_injective s)
#align rank_condition_of_strong_rank_condition rankCondition_of_strongRankCondition

/-- We say that `R` has the invariant basis number property if `(fin n → R) ≃ₗ[R] (fin m → R)`
    implies `n = m`. This gives rise to a well-defined notion of rank of a finitely generated free
    module. -/
class InvariantBasisNumber : Prop where
  eq_of_fin_equiv : ∀ {n m : ℕ}, ((Fin n → R) ≃ₗ[R] Fin m → R) → n = m
#align invariant_basis_number InvariantBasisNumber

instance (priority := 100) invariantBasisNumber_of_rankCondition [RankCondition R] :
    InvariantBasisNumber R
    where eq_of_fin_equiv n m e :=
    le_antisymm (le_of_fin_surjective R e.symm.toLinearMap e.symm.Surjective)
      (le_of_fin_surjective R e.toLinearMap e.Surjective)
#align invariant_basis_number_of_rank_condition invariantBasisNumber_of_rankCondition

end

section

variable (R : Type u) [Semiring R] [InvariantBasisNumber R]

theorem eq_of_fin_equiv {n m : ℕ} : ((Fin n → R) ≃ₗ[R] Fin m → R) → n = m :=
  InvariantBasisNumber.eq_of_fin_equiv
#align eq_of_fin_equiv eq_of_fin_equiv

theorem card_eq_of_lequiv {α β : Type _} [Fintype α] [Fintype β] (f : (α → R) ≃ₗ[R] β → R) :
    Fintype.card α = Fintype.card β :=
  eq_of_fin_equiv R
    ((LinearEquiv.funCongrLeft R R (Fintype.equivFin α)).trans f ≪≫ₗ
      (LinearEquiv.funCongrLeft R R (Fintype.equivFin β)).symm)
#align card_eq_of_lequiv card_eq_of_lequiv

theorem nontrivial_of_invariantBasisNumber : Nontrivial R :=
  by
  by_contra h
  refine' zero_ne_one (eq_of_fin_equiv R _)
  haveI := not_nontrivial_iff_subsingleton.1 h
  haveI : Subsingleton (Fin 1 → R) := ⟨fun a b => funext fun x => Subsingleton.elim _ _⟩
  refine' { .. } <;>
    first
      |·
        intros
        exact 0|tidy
#align nontrivial_of_invariant_basis_number nontrivial_of_invariantBasisNumber

end

section

variable (R : Type u) [Ring R] [Nontrivial R] [IsNoetherianRing R]

-- Note this includes fields,
-- and we use this below to show any commutative ring has invariant basis number.
/-- Any nontrivial noetherian ring satisfies the strong rank condition.

An injective map `((fin n ⊕ fin (1 + m)) → R) →ₗ[R] (fin n → R)` for some left-noetherian `R`
would force `fin (1 + m) → R ≃ₗ punit` (via `is_noetherian.equiv_punit_of_prod_injective`),
which is not the case!
-/
instance (priority := 100) noetherian_ring_strongRankCondition : StrongRankCondition R :=
  by
  fconstructor
  intro m n f i
  by_contra h
  rw [not_le, ← Nat.add_one_le_iff, le_iff_exists_add] at h
  obtain ⟨m, rfl⟩ := h
  let e : Fin (n + 1 + m) ≃ Sum (Fin n) (Fin (1 + m)) :=
    (finCongr (add_assoc _ _ _)).trans fin_sum_fin_equiv.symm
  let f' :=
    f.comp
      ((LinearEquiv.sumArrowLequivProdArrow _ _ R R).symm.trans
          (LinearEquiv.funCongrLeft R R e)).toLinearMap
  have i' : injective f' := i.comp (LinearEquiv.injective _)
  apply @zero_ne_one (Fin (1 + m) → R) _ _
  apply (IsNoetherian.equivPunitOfProdInjective f' i').Injective
  ext
#align noetherian_ring_strong_rank_condition noetherian_ring_strongRankCondition

end

/-!
  We want to show that nontrivial commutative rings have invariant basis number. The idea is to
  take a maximal ideal `I` of `R` and use an isomorphism `R^n ≃ R^m` of `R` modules to produce an
  isomorphism `(R/I)^n ≃ (R/I)^m` of `R/I`-modules, which will imply `n = m` since `R/I` is a field
  and we know that fields have invariant basis number.

  We construct the isomorphism in two steps:
  1. We construct the ring `R^n/I^n`, show that it is an `R/I`-module and show that there is an
     isomorphism of `R/I`-modules `R^n/I^n ≃ (R/I)^n`. This isomorphism is called
    `ideal.pi_quot_equiv` and is located in the file `ring_theory/ideals.lean`.
  2. We construct an isomorphism of `R/I`-modules `R^n/I^n ≃ R^m/I^m` using the isomorphism
     `R^n ≃ R^m`.
-/


section

variable {R : Type u} [CommRing R] (I : Ideal R) {ι : Type v} [Fintype ι] {ι' : Type w}

/-- An `R`-linear map `R^n → R^m` induces a function `R^n/I^n → R^m/I^m`. -/
private def induced_map (I : Ideal R) (e : (ι → R) →ₗ[R] ι' → R) :
    (ι → R) ⧸ I.pi ι → (ι' → R) ⧸ I.pi ι' := fun x =>
  Quotient.liftOn' x (fun y => Ideal.Quotient.mk _ (e y))
    (by
      refine' fun a b hab => Ideal.Quotient.eq.2 fun h => _
      rw [Submodule.quotientRel_r_def] at hab
      rw [← LinearMap.map_sub]
      exact Ideal.map_pi _ _ hab e h)
#align induced_map induced_map

/-- An isomorphism of `R`-modules `R^n ≃ R^m` induces an isomorphism of `R/I`-modules
    `R^n/I^n ≃ R^m/I^m`. -/
private def induced_equiv [Fintype ι'] (I : Ideal R) (e : (ι → R) ≃ₗ[R] ι' → R) :
    ((ι → R) ⧸ I.pi ι) ≃ₗ[R ⧸ I] (ι' → R) ⧸ I.pi ι' :=
  by
  refine'
    { toFun := induced_map I e
      invFun := induced_map I e.symm.. }
  all_goals
    first |rintro ⟨a⟩ ⟨b⟩|rintro ⟨a⟩
    convert_to Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    congr
    simp only [map_add, LinearEquiv.coe_coe, LinearEquiv.map_smulₛₗ, RingHom.id_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
#align induced_equiv induced_equiv

end

section

attribute [local instance] Ideal.Quotient.field

/-- Nontrivial commutative rings have the invariant basis number property.

In fact, any nontrivial commutative ring satisfies the strong rank condition, see
`comm_ring_strong_rank_condition`. We prove this instance separately to avoid dependency on
`linear_algebra.charpoly.basic`. -/
instance (priority := 100) invariantBasisNumber_of_nontrivial_of_commRing {R : Type u} [CommRing R]
    [Nontrivial R] : InvariantBasisNumber R :=
  ⟨fun n m e =>
    let ⟨I, hI⟩ := Ideal.exists_maximal R
    eq_of_fin_equiv (R ⧸ I)
      ((Ideal.piQuotEquiv _ _).symm ≪≫ₗ (induced_equiv _ e ≪≫ₗ Ideal.piQuotEquiv _ _))⟩
#align invariant_basis_number_of_nontrivial_of_comm_ring invariantBasisNumber_of_nontrivial_of_commRing

end

