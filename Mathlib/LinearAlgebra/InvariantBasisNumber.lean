/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathlib.RingTheory.OrzechProperty
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.PrincipalIdealDomain

#align_import linear_algebra.invariant_basis_number from "leanprover-community/mathlib"@"5fd3186f1ec30a75d5f65732e3ce5e623382556f"

/-!
# Invariant basis number property

## Main definitions

Let `R` be a (not necessary commutative) ring.

- `InvariantBasisNumber R` is a type class stating that `(Fin n → R) ≃ₗ[R] (Fin m → R)`
  implies `n = m`, a property known as the *invariant basis number property.*

  This assumption implies that there is a well-defined notion of the rank
  of a finitely generated free (left) `R`-module.

It is also useful to consider the following stronger conditions:

- the *rank condition*, witnessed by the type class `RankCondition R`, states that
  the existence of a surjective linear map `(Fin n → R) →ₗ[R] (Fin m → R)` implies `m ≤ n`

- the *strong rank condition*, witnessed by the type class `StrongRankCondition R`, states
  that the existence of an injective linear map `(Fin n → R) →ₗ[R] (Fin m → R)`
  implies `n ≤ m`.

- `OrzechProperty R`, defined in `Mathlib/RingTheory/OrzechProperty.lean`,
  states that for any finitely generated `R`-module `M`, any surjective homomorphism `f : N → M`
  from a submodule `N` of `M` to `M` is injective.


## Instances

- `strongRankCondition_of_orzechProperty` : the Orzech property implies the strong rank condition
  (for non trivial rings).

- `IsNoetherianRing.strongRankCondition` : every nontrivial left-noetherian ring satisfies the
  strong rank condition (and so in particular every division ring or field).

- `rankCondition_of_strongRankCondition` : the strong rank condition implies the rank condition.

- `invariantBasisNumber_of_rankCondition` : the rank condition implies the
  invariant basis number property.

- `invariantBasisNumber_of_nontrivial_of_commRing`: a nontrivial commutative ring satisfies
  the invariant basis number property

More generally, every commutative ring satisfies the strong rank condition. This is proved in
`LinearAlgebra/FreeModule/StrongRankCondition`. We keep
`invariantBasisNumber_of_nontrivial_of_commRing` here since it imports fewer files.


## Counterexamples to converse results

The following examples can be found in the book of Lam [lam_1999]
(see also <https://math.stackexchange.com/questions/4711904>):

- Let `k` be a field, then the free (non-commutative) algebra `k⟨x, y⟩` satisfies
  the rank condition but not the strong rank condition.
- The free (non-commutative) algebra `ℚ⟨a, b, c, d⟩` quotient by the
  two-sided ideal `(ac − 1, bd − 1, ab, cd)` satisfies the invariant basis number property
  but not the rank condition.


## Future work

So far, there is no API at all for the `InvariantBasisNumber` class. There are several natural
ways to formulate that a module `M` is finitely generated and free, for example
`M ≃ₗ[R] (Fin n → R)`, `M ≃ₗ[R] (ι → R)`, where `ι` is a fintype, or providing a basis indexed by
a finite type. There should be lemmas applying the invariant basis number property to each
situation.

The finite version of the invariant basis number property implies the infinite analogue, i.e., that
`(ι →₀ R) ≃ₗ[R] (ι' →₀ R)` implies that `Cardinal.mk ι = Cardinal.mk ι'`. This fact (and its
variants) should be formalized.

## References

* https://en.wikipedia.org/wiki/Invariant_basis_number
* https://mathoverflow.net/a/2574/
* [Lam, T. Y. *Lectures on Modules and Rings*][lam_1999]
* [Orzech, Morris. *Onto endomorphisms are isomorphisms*][orzech1971]
* [Djoković, D. Ž. *Epimorphisms of modules which must be isomorphisms*][djokovic1973]
* [Ribenboim, Paulo.
  *Épimorphismes de modules qui sont nécessairement des isomorphismes*][ribenboim1971]

## Tags

free module, rank, Orzech property, (strong) rank condition, invariant basis number, IBN

-/


noncomputable section

open Function

universe u v w

section

variable (R : Type u) [Semiring R]

/-- We say that `R` satisfies the strong rank condition if `(Fin n → R) →ₗ[R] (Fin m → R)` injective
    implies `n ≤ m`. -/
@[mk_iff]
class StrongRankCondition : Prop where
  /-- Any injective linear map from `Rⁿ` to `Rᵐ` guarantees `n ≤ m`. -/
  le_of_fin_injective : ∀ {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R), Injective f → n ≤ m
#align strong_rank_condition StrongRankCondition

theorem le_of_fin_injective [StrongRankCondition R] {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R) :
    Injective f → n ≤ m :=
  StrongRankCondition.le_of_fin_injective f
#align le_of_fin_injective le_of_fin_injective

/-- A ring satisfies the strong rank condition if and only if, for all `n : ℕ`, any linear map
`(Fin (n + 1) → R) →ₗ[R] (Fin n → R)` is not injective. -/
theorem strongRankCondition_iff_succ :
    StrongRankCondition R ↔
      ∀ (n : ℕ) (f : (Fin (n + 1) → R) →ₗ[R] Fin n → R), ¬Function.Injective f := by
  refine ⟨fun h n => fun f hf => ?_, fun h => ⟨@fun n m f hf => ?_⟩⟩
  · letI : StrongRankCondition R := h
    exact Nat.not_succ_le_self n (le_of_fin_injective R f hf)
  · by_contra H
    exact
      h m (f.comp (Function.ExtendByZero.linearMap R (Fin.castLE (not_le.1 H))))
        (hf.comp (Function.extend_injective (Fin.strictMono_castLE _).injective _))
#align strong_rank_condition_iff_succ strongRankCondition_iff_succ

/-- Any nontrivial ring satisfying Orzech property also satisfies strong rank condition. -/
instance (priority := 100) strongRankCondition_of_orzechProperty
    [Nontrivial R] [OrzechProperty R] : StrongRankCondition R := by
  refine (strongRankCondition_iff_succ R).2 fun n i hi ↦ ?_
  let f : (Fin (n + 1) → R) →ₗ[R] Fin n → R := {
    toFun := fun x ↦ x ∘ Fin.castSucc
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
  }
  have h : (0 : Fin (n + 1) → R) = update (0 : Fin (n + 1) → R) (Fin.last n) 1 := by
    apply OrzechProperty.injective_of_surjective_of_injective i f hi
      (Fin.castSucc_injective _).surjective_comp_right
    ext m
    simp [f, update_apply, (Fin.castSucc_lt_last m).ne]
  simpa using congr_fun h (Fin.last n)

theorem card_le_of_injective [StrongRankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α → R) →ₗ[R] β → R) (i : Injective f) : Fintype.card α ≤ Fintype.card β := by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact
    le_of_fin_injective R ((Q.symm.toLinearMap.comp f).comp P.toLinearMap)
      (((LinearEquiv.symm Q).injective.comp i).comp (LinearEquiv.injective P))
#align card_le_of_injective card_le_of_injective

theorem card_le_of_injective' [StrongRankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α →₀ R) →ₗ[R] β →₀ R) (i : Injective f) : Fintype.card α ≤ Fintype.card β := by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact
    card_le_of_injective R ((P.toLinearMap.comp f).comp Q.toLinearMap)
      ((P.injective.comp i).comp Q.injective)
#align card_le_of_injective' card_le_of_injective'

/-- We say that `R` satisfies the rank condition if `(Fin n → R) →ₗ[R] (Fin m → R)` surjective
    implies `m ≤ n`. -/
class RankCondition : Prop where
  /-- Any surjective linear map from `Rⁿ` to `Rᵐ` guarantees `m ≤ n`. -/
  le_of_fin_surjective : ∀ {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R), Surjective f → m ≤ n
#align rank_condition RankCondition

theorem le_of_fin_surjective [RankCondition R] {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R) :
    Surjective f → m ≤ n :=
  RankCondition.le_of_fin_surjective f
#align le_of_fin_surjective le_of_fin_surjective

theorem card_le_of_surjective [RankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α → R) →ₗ[R] β → R) (i : Surjective f) : Fintype.card β ≤ Fintype.card α := by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact
    le_of_fin_surjective R ((Q.symm.toLinearMap.comp f).comp P.toLinearMap)
      (((LinearEquiv.symm Q).surjective.comp i).comp (LinearEquiv.surjective P))
#align card_le_of_surjective card_le_of_surjective

theorem card_le_of_surjective' [RankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α →₀ R) →ₗ[R] β →₀ R) (i : Surjective f) : Fintype.card β ≤ Fintype.card α := by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact
    card_le_of_surjective R ((P.toLinearMap.comp f).comp Q.toLinearMap)
      ((P.surjective.comp i).comp Q.surjective)
#align card_le_of_surjective' card_le_of_surjective'

/-- By the universal property for free modules, any surjective map `(Fin n → R) →ₗ[R] (Fin m → R)`
has an injective splitting `(Fin m → R) →ₗ[R] (Fin n → R)`
from which the strong rank condition gives the necessary inequality for the rank condition.
-/
instance (priority := 100) rankCondition_of_strongRankCondition [StrongRankCondition R] :
    RankCondition R where
  le_of_fin_surjective f s :=
    le_of_fin_injective R _ (f.splittingOfFunOnFintypeSurjective_injective s)
#align rank_condition_of_strong_rank_condition rankCondition_of_strongRankCondition

/-- We say that `R` has the invariant basis number property if `(Fin n → R) ≃ₗ[R] (Fin m → R)`
    implies `n = m`. This gives rise to a well-defined notion of rank of a finitely generated free
    module. -/
class InvariantBasisNumber : Prop where
  /-- Any linear equiv between `Rⁿ` and `Rᵐ` guarantees `m = n`. -/
  eq_of_fin_equiv : ∀ {n m : ℕ}, ((Fin n → R) ≃ₗ[R] Fin m → R) → n = m
#align invariant_basis_number InvariantBasisNumber

instance (priority := 100) invariantBasisNumber_of_rankCondition [RankCondition R] :
    InvariantBasisNumber R where
  eq_of_fin_equiv e := le_antisymm (le_of_fin_surjective R e.symm.toLinearMap e.symm.surjective)
    (le_of_fin_surjective R e.toLinearMap e.surjective)
#align invariant_basis_number_of_rank_condition invariantBasisNumber_of_rankCondition

end

section

variable (R : Type u) [Semiring R] [InvariantBasisNumber R]

theorem eq_of_fin_equiv {n m : ℕ} : ((Fin n → R) ≃ₗ[R] Fin m → R) → n = m :=
  InvariantBasisNumber.eq_of_fin_equiv
#align eq_of_fin_equiv eq_of_fin_equiv

theorem card_eq_of_linearEquiv {α β : Type*} [Fintype α] [Fintype β] (f : (α → R) ≃ₗ[R] β → R) :
    Fintype.card α = Fintype.card β :=
  eq_of_fin_equiv R
    ((LinearEquiv.funCongrLeft R R (Fintype.equivFin α)).trans f ≪≫ₗ
      (LinearEquiv.funCongrLeft R R (Fintype.equivFin β)).symm)
#align card_eq_of_lequiv card_eq_of_linearEquiv
-- Porting note: this was not well-named because `lequiv` could mean other things
-- (e.g., `localEquiv`)

theorem nontrivial_of_invariantBasisNumber : Nontrivial R := by
  by_contra h
  refine zero_ne_one (eq_of_fin_equiv R ?_)
  haveI := not_nontrivial_iff_subsingleton.1 h
  haveI : Subsingleton (Fin 1 → R) :=
    Subsingleton.intro fun a b => funext fun x => Subsingleton.elim _ _
  exact
    { toFun := 0
      invFun := 0
      map_add' := by aesop
      map_smul' := by aesop
      left_inv := fun _ => by simp [eq_iff_true_of_subsingleton]
      right_inv := fun _ => by simp [eq_iff_true_of_subsingleton] }
#align nontrivial_of_invariant_basis_number nontrivial_of_invariantBasisNumber

end

section

variable (R : Type u) [Ring R] [Nontrivial R] [IsNoetherianRing R]

-- Note this includes fields,
-- and we use this below to show any commutative ring has invariant basis number.
/-- Any nontrivial noetherian ring satisfies the strong rank condition.

An injective map `((Fin n ⊕ Fin (1 + m)) → R) →ₗ[R] (Fin n → R)` for some left-noetherian `R`
would force `Fin (1 + m) → R ≃ₗ PUnit` (via `IsNoetherian.equivPUnitOfProdInjective`),
which is not the case!
-/
instance (priority := 100) IsNoetherianRing.strongRankCondition : StrongRankCondition R := by
  constructor
  intro m n f i
  by_contra h
  rw [not_le, ← Nat.add_one_le_iff, le_iff_exists_add] at h
  obtain ⟨m, rfl⟩ := h
  let e : Fin (n + 1 + m) ≃ Sum (Fin n) (Fin (1 + m)) :=
    (finCongr (add_assoc _ _ _)).trans finSumFinEquiv.symm
  let f' :=
    f.comp
      ((LinearEquiv.sumArrowLequivProdArrow _ _ R R).symm.trans
          (LinearEquiv.funCongrLeft R R e)).toLinearMap
  have i' : Injective f' := i.comp (LinearEquiv.injective _)
  apply @zero_ne_one (Fin (1 + m) → R) _ _
  apply (IsNoetherian.equivPUnitOfProdInjective f' i').injective
  ext
#align noetherian_ring_strong_rank_condition IsNoetherianRing.strongRankCondition

end

/-!
  We want to show that nontrivial commutative rings have invariant basis number. The idea is to
  take a maximal ideal `I` of `R` and use an isomorphism `R^n ≃ R^m` of `R` modules to produce an
  isomorphism `(R/I)^n ≃ (R/I)^m` of `R/I`-modules, which will imply `n = m` since `R/I` is a field
  and we know that fields have invariant basis number.

  We construct the isomorphism in two steps:
  1. We construct the ring `R^n/I^n`, show that it is an `R/I`-module and show that there is an
     isomorphism of `R/I`-modules `R^n/I^n ≃ (R/I)^n`. This isomorphism is called
    `Ideal.piQuotEquiv` and is located in the file `RingTheory/Ideals.lean`.
  2. We construct an isomorphism of `R/I`-modules `R^n/I^n ≃ R^m/I^m` using the isomorphism
     `R^n ≃ R^m`.
-/


section

variable {R : Type u} [CommRing R] (I : Ideal R) {ι : Type v} [Fintype ι] {ι' : Type w}

/-- An `R`-linear map `R^n → R^m` induces a function `R^n/I^n → R^m/I^m`. -/
private def induced_map (I : Ideal R) (e : (ι → R) →ₗ[R] ι' → R) :
    (ι → R) ⧸ I.pi ι → (ι' → R) ⧸ I.pi ι' := fun x =>
  Quotient.liftOn' x (fun y => Ideal.Quotient.mk (I.pi ι') (e y))
    (by
      refine fun a b hab => Ideal.Quotient.eq.2 fun h => ?_
      rw [Submodule.quotientRel_r_def] at hab
      rw [← LinearMap.map_sub]
      exact Ideal.map_pi _ _ hab e h)
#noalign induced_map
-- Porting note: `#noalign` since this is marked `private`

/-- An isomorphism of `R`-modules `R^n ≃ R^m` induces an isomorphism of `R/I`-modules
    `R^n/I^n ≃ R^m/I^m`. -/
private def induced_equiv [Fintype ι'] (I : Ideal R) (e : (ι → R) ≃ₗ[R] ι' → R) :
    ((ι → R) ⧸ I.pi ι) ≃ₗ[R ⧸ I] (ι' → R) ⧸ I.pi ι' := by
  refine'
    { toFun := induced_map I e
      invFun := induced_map I e.symm.. }
  all_goals
    first |rintro ⟨a⟩ ⟨b⟩|rintro ⟨a⟩
  -- Porting note: the next 4 lines were necessary because Lean couldn't correctly infer `(I.pi ι)`
  -- and `(I.pi ι')` on its own.
  pick_goal 3
  · convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    congr
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  all_goals
    convert_to Ideal.Quotient.mk (I.pi ι') _ = Ideal.Quotient.mk (I.pi ι') _
    congr
    simp only [map_add, LinearEquiv.coe_coe, LinearEquiv.map_smulₛₗ, RingHom.id_apply,
      LinearEquiv.apply_symm_apply]
#noalign induced_equiv
-- Porting note: `#noalign` since this is marked `private`

end

section

attribute [local instance] Ideal.Quotient.field

/-- Nontrivial commutative rings have the invariant basis number property.

In fact, any nontrivial commutative ring satisfies the strong rank condition, see
`commRing_strongRankCondition`. We prove this instance separately to avoid dependency on
`LinearAlgebra.Charpoly.Basic`. -/
instance (priority := 100) invariantBasisNumber_of_nontrivial_of_commRing {R : Type u} [CommRing R]
    [Nontrivial R] : InvariantBasisNumber R :=
  ⟨fun e =>
    let ⟨I, _hI⟩ := Ideal.exists_maximal R
    eq_of_fin_equiv (R ⧸ I)
      ((Ideal.piQuotEquiv _ _).symm ≪≫ₗ (induced_equiv _ e ≪≫ₗ Ideal.piQuotEquiv _ _))⟩
#align invariant_basis_number_of_nontrivial_of_comm_ring invariantBasisNumber_of_nontrivial_of_commRing

end
