/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed
import Mathlib.ModelTheory.Algebra.Ring.Definability
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Ax-Grothendieck

This file proves that if `K` is an algebraically closed field,
then any injective polynomial map `K^n → K^n` is also surjective.

## Main results

* `ax_grothendieck_zeroLocus`: If `K` is algebraically closed, `ι` is a finite type, and
`S : Set (ι → K)` is the `zeroLocus` of some ideal of `MvPolynomial ι K`, then any injective
polynomial map `S → S` is also surjective on `S`.
* `ax_grothendieck_univ`: Any injective polynomial map `K^n → K^n` is also surjective if `K` is an
algberaically closed field.
* `ax_grothendieck_of_definable`: Any injective polynomial map `S → S` is also surjective on `S` if
`K` is an algebraically closed field and `S` is a definable subset of `K^n`.
* `ax_grothendieck_of_locally_finite`: any injective polynomial map `R^n → R^n` is also surjective
whenever `R` is an algebraic extension of a finite field.

## References

The first order theory of algebraically closed fields, along with the Lefschetz Principle and
the Ax-Grothendieck Theorem were first formalized in Lean 3 by Joseph Hua
[here](https://github.com/Jlh18/ModelTheoryInLean8) with the master's thesis
[here](https://github.com/Jlh18/ModelTheory8Report)

-/


noncomputable section

open MvPolynomial Finset

/-- Any injective polynomial map over an algebraic extension of a finite field is surjective. -/
theorem ax_grothendieck_of_locally_finite {ι K R : Type*} [Field K] [Finite K] [CommRing R]
    [Finite ι] [Algebra K R] [alg : Algebra.IsAlgebraic K R] (ps : ι → MvPolynomial ι R)
    (S : Set (ι → R))
    (hm : S.MapsTo (fun v i => eval v (ps i)) S)
    (hinj : S.InjOn (fun v i => eval v (ps i))) :
    S.SurjOn (fun v i => eval v (ps i)) S := by
  have is_int : ∀ x : R, IsIntegral K x := fun x => isAlgebraic_iff_isIntegral.1
    (alg.isAlgebraic x)
  classical
  intro v hvS
  cases nonempty_fintype ι
  /- `s` is the set of all coefficients of the polynomial, as well as all of
    the coordinates of `v`, the point I am trying to find the preimage of. -/
  let s : Finset R :=
    (Finset.biUnion (univ : Finset ι) fun i => (ps i).support.image fun x => coeff x (ps i)) ∪
      (univ : Finset ι).image v
  have hv : ∀ i, v i ∈ Algebra.adjoin K (s : Set R) := fun j =>
    Algebra.subset_adjoin (mem_union_right _ (mem_image.2 ⟨j, mem_univ _, rfl⟩))
  have hs₁ : ∀ (i : ι) (k : ι →₀ ℕ),
      k ∈ (ps i).support → coeff k (ps i) ∈ Algebra.adjoin K (s : Set R) :=
    fun i k hk => Algebra.subset_adjoin
      (mem_union_left _ (mem_biUnion.2 ⟨i, mem_univ _, mem_image_of_mem _ hk⟩))
  have := isNoetherian_adjoin_finset s fun x _ => is_int x
  have := Module.IsNoetherian.finite K (Algebra.adjoin K (s : Set R))
  have : Finite (Algebra.adjoin K (s : Set R)) := Module.finite_of_finite K
  -- The restriction of the polynomial map, `ps`, to the subalgebra generated by `s`
  let S' : Set (ι → Algebra.adjoin K (s : Set R)) :=
    (fun v => Subtype.val ∘ v) ⁻¹' S
  let res : S' → S' := fun x => ⟨fun i =>
    ⟨eval (fun j : ι => (x.1 j : R)) (ps i), eval_mem (hs₁ _) fun i => (x.1 i).2⟩,
      hm x.2⟩
  have hres_surj : Function.Surjective res := by
    rw [← Finite.injective_iff_surjective]
    intro x y hxy
    ext i
    simp only [Subtype.ext_iff, funext_iff] at hxy
    exact congr_fun (hinj x.2 y.2 (funext hxy)) i
  rcases hres_surj ⟨fun i => ⟨v i, hv i⟩, hvS⟩ with ⟨⟨w, hwS'⟩, hw⟩
  refine ⟨fun i => w i, hwS', ?_⟩
  simpa [Subtype.ext_iff, funext_iff] using hw

end

namespace FirstOrder

open MvPolynomial FreeCommRing Language Field Ring BoundedFormula

variable {ι α : Type*} [Finite α] {K : Type*} [Field K] [CompatibleRing K]

/-- The collection of first order formulas corresponding to the Ax-Grothendieck theorem. -/
noncomputable def genericPolyMapSurjOnOfInjOn [Finite ι]
    (φ : ring.Formula (α ⊕ ι))
    (mons : ι → Finset (ι →₀ ℕ)) : Language.ring.Sentence :=
  let l1 : ι → Language.ring.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    fun i =>
      (termOfFreeCommRing (genericPolyMap mons i)).relabel
        (Sum.inl ∘ Sum.map id (fun i => (0, i)))
    =' (termOfFreeCommRing (genericPolyMap mons i)).relabel
        (Sum.inl ∘ Sum.map id (fun i => (1, i)))
  -- p(x) = p(y) as a formula
  let f1 : Language.ring.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    iInf l1
  let l2 : ι → Language.ring.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    fun i => .var (Sum.inl (Sum.inr (0, i))) =' .var (Sum.inl (Sum.inr (1, i)))
  -- x = y as a formula
  let f2 : Language.ring.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    iInf l2
  let injOn : Language.ring.Formula (α ⊕ Σ i : ι, mons i) :=
    Formula.iAlls (Fin 2 × ι)
      (φ.relabel (Sum.map Sum.inl (fun i => (0, i))) ⟹
       φ.relabel (Sum.map Sum.inl (fun i => (1, i))) ⟹
        (f1.imp f2).relabel (fun x => (Equiv.sumAssoc _ _ _).symm (Sum.inr x)))
  let l3 : ι → Language.ring.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    fun i => (termOfFreeCommRing (genericPolyMap mons i)).relabel
        (Sum.inl ∘ Sum.map id (fun i => (0, i))) ='
      .var (Sum.inl (Sum.inr (1, i)))
  let f3 : Language.ring.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    iInf l3
  let surjOn : Language.ring.Formula (α ⊕ Σ i : ι, mons i) :=
    Formula.iAlls ι
      (Formula.imp (φ.relabel (Sum.map Sum.inl id)) <|
        Formula.iExs ι <|
          ((φ.relabel (Sum.map Sum.inl (fun i => (0, i)))) ⊓
            (f3.relabel (fun x => (Equiv.sumAssoc _ _ _).symm (Sum.inr x)))).relabel
        (fun (i : (α ⊕ (Σ i : ι, mons i)) ⊕ (Fin 2 × ι)) =>
          show ((α ⊕ (Σ i : ι, mons i)) ⊕ ι) ⊕ ι
          from Sum.elim (Sum.inl ∘ Sum.inl)
            (fun i => if i.1 = 0 then Sum.inr i.2 else (Sum.inl (Sum.inr i.2))) i))
  let mapsTo : Language.ring.Formula (α ⊕ Σ i : ι, mons i) :=
    Formula.iAlls ι
      (Formula.imp (φ.relabel (Sum.map Sum.inl id))
        (φ.subst <| Sum.elim
          (fun a => .var (Sum.inl (Sum.inl a)))
          (fun i => (termOfFreeCommRing (genericPolyMap mons i)).relabel
            (fun i => (Equiv.sumAssoc _ _ _).symm (Sum.inr i)))))
  Formula.iAlls (α ⊕ Σ i : ι, mons i) ((mapsTo.imp <| injOn.imp <| surjOn).relabel Sum.inr)

theorem realize_genericPolyMapSurjOnOfInjOn
    [Finite ι] (φ : ring.Formula (α ⊕ ι)) (mons : ι → Finset (ι →₀ ℕ)) :
    (K ⊨ genericPolyMapSurjOnOfInjOn φ mons) ↔
      ∀ (v : α → K) (p : { p : ι → MvPolynomial ι K // (∀ i, (p i).support ⊆ mons i) }),
        let f : (ι → K) → (ι → K) := fun v i => eval v (p.1 i)
        let S : Set (ι → K) := fun x => φ.Realize (Sum.elim v x)
        S.MapsTo f S → S.InjOn f → S.SurjOn f S := by
  classical
  have injOnAlt : ∀ {S : Set (ι → K)} (f : (ι → K) → (ι → K)),
      S.InjOn f ↔ ∀ x y, x ∈ S → y ∈ S → f x = f y → x = y := by
    simp [Set.InjOn]; tauto
  simp only [Sentence.Realize, Formula.Realize, genericPolyMapSurjOnOfInjOn, Formula.relabel,
    Function.comp_def, Sum.map, id_eq, Equiv.sumAssoc, Equiv.coe_fn_symm_mk, Sum.elim_inr,
    realize_iAlls, realize_imp, realize_relabel, Fin.natAdd_zero, realize_subst, realize_iInf,
    Finset.mem_univ, realize_bdEqual, Term.realize_relabel, true_imp_iff,
    Equiv.forall_congr_left (Equiv.curry (Fin 2) ι K), Equiv.curry_symm_apply, Function.uncurry,
    Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, realize_iExs, realize_inf, Sum.forall_sum,
    Set.MapsTo, Set.mem_def, injOnAlt, funext_iff, Set.SurjOn, Set.image, setOf,
    Set.subset_def, Equiv.forall_congr_left (mvPolynomialSupportLEEquiv mons)]
  simp +singlePass only [← Sum.elim_comp_inl_inr]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Fin.castAdd_zero, Fin.cast_eq_self,
    Nat.add_zero, Term.realize_var, Term.realize_relabel, realize_termOfFreeCommRing,
    lift_genericPolyMap, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair, Fin.cons_zero,
    Fin.cons_one, ↓reduceIte, one_ne_zero]

theorem ACF_models_genericPolyMapSurjOnOfInjOn_of_prime [Finite ι]
    {p : ℕ} (hp : p.Prime) (φ : ring.Formula (α ⊕ ι)) (mons : ι → Finset (ι →₀ ℕ)) :
    Theory.ACF p ⊨ᵇ genericPolyMapSurjOnOfInjOn φ mons := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  letI := compatibleRingOfRing (AlgebraicClosure (ZMod p))
  have : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_algebraMap
      (RingHom.injective (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) p
  rw [← (ACF_isComplete (Or.inl hp)).realize_sentence_iff _
    (AlgebraicClosure (ZMod p)), realize_genericPolyMapSurjOnOfInjOn]
  rintro v ⟨f, _⟩
  exact ax_grothendieck_of_locally_finite (K := ZMod p) (ι := ι) f _

theorem ACF_models_genericPolyMapSurjOnOfInjOn_of_prime_or_zero
    [Finite ι] {p : ℕ} (hp : p.Prime ∨ p = 0)
    (φ : ring.Formula (α ⊕ ι)) (mons : ι → Finset (ι →₀ ℕ)) :
    Theory.ACF p ⊨ᵇ genericPolyMapSurjOnOfInjOn φ mons := by
  rcases hp with hp | rfl
  · exact ACF_models_genericPolyMapSurjOnOfInjOn_of_prime hp φ mons
  · rw [ACF_zero_realize_iff_infinite_ACF_prime_realize]
    convert Set.infinite_univ (α := Nat.Primes)
    rw [Set.eq_univ_iff_forall]
    intro ⟨p, hp⟩
    exact ACF_models_genericPolyMapSurjOnOfInjOn_of_prime hp φ mons

end FirstOrder

open FirstOrder Language Field Ring MvPolynomial

variable {K ι : Type*} [Field K] [IsAlgClosed K] [Finite ι]

/-- A slight generalization of the **Ax-Grothendieck** theorem

If `K` is an algebraically closed field, `ι` is a finite type, and `S` is a definable subset of
`ι → K`, then any injective polynomial map `S → S`  is also surjective on `S`. -/
theorem ax_grothendieck_of_definable [CompatibleRing K] {c : Set K}
    (S : Set (ι → K)) (hS : c.Definable Language.ring S)
    (ps : ι → MvPolynomial ι K) :
    S.MapsTo (fun v i => eval v (ps i)) S →
    S.InjOn (fun v i => eval v (ps i)) →
    S.SurjOn (fun v i => eval v (ps i)) S := by
  letI := Fintype.ofFinite ι
  let p : ℕ := ringChar K
  have : CharP K p := ⟨ringChar.spec K⟩
  rw [Set.definable_iff_finitely_definable] at hS
  rcases hS with ⟨c, _, hS⟩
  rw [Set.definable_iff_exists_formula_sum] at hS
  rcases hS with ⟨φ, hφ⟩
  rw [hφ]
  have := ACF_models_genericPolyMapSurjOnOfInjOn_of_prime_or_zero
    (CharP.char_is_prime_or_zero K p) φ (fun i => (ps i).support)
  rw [← (ACF_isComplete (CharP.char_is_prime_or_zero K p)).realize_sentence_iff _ K,
    realize_genericPolyMapSurjOnOfInjOn] at this
  exact this Subtype.val ⟨ps, fun i => Set.Subset.refl _⟩

/-- The **Ax-Grothendieck** theorem

If `K` is an algebraically closed field, and `S : Set (ι → K)` is the `zeroLocus` of an ideal
of the multivariable polynomial ring, then any injective polynomial map `S → S`  is also
surjective on `S`. -/
theorem ax_grothendieck_zeroLocus
    (I : Ideal (MvPolynomial ι K))
    (p : ι → MvPolynomial ι K) :
    let S := zeroLocus I
    S.MapsTo (fun v i => eval v (p i)) S →
    S.InjOn (fun v i => eval v (p i)) →
    S.SurjOn (fun v i => eval v (p i)) S := by
  letI := compatibleRingOfRing K
  intro S
  obtain ⟨s, rfl⟩ : I.FG := IsNoetherian.noetherian I
  exact ax_grothendieck_of_definable S (mvPolynomial_zeroLocus_definable s) p

/-- A special case of the **Ax-Grothendieck** theorem

Any injective polynomial map `K^n → K^n` is also surjective if `K` is an
algberaically closed field. -/
theorem ax_grothendieck_univ (p : ι → MvPolynomial ι K) :
    (fun v i => eval v (p i)).Injective →
    (fun v i => eval v (p i)).Surjective := by
  simpa [Set.injective_iff_injOn_univ, Set.surjective_iff_surjOn_univ] using
      ax_grothendieck_zeroLocus 0 p
