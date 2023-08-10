/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Algebra.Field.AlgClosed
import Mathlib.Data.MvPolynomial.Basic

universe u v

namespace FirstOrder

open MvPolynomial FreeCommRing Language Language.field

def genericPolyMap {ι : Type _} (monoms : ι → Finset (ι →₀ ℕ)) :
    ι → FreeCommRing ((Σ i : ι, monoms i) ⊕ ι) :=
  fun i => (monoms i).attach.sum
    (fun m => FreeCommRing.of (Sum.inl ⟨i, m⟩) *
      Finsupp.prod m.1 (fun j n => FreeCommRing.of (Sum.inr j)^ n))



noncomputable def mvPolynomialSupportLEEquiv (ι : Type u)
    [Fintype ι] [DecidableEq ι]
    (R : Type _) [CommRing R] [DecidableEq R]
    (monoms : ι → Finset (ι →₀ ℕ)) :
    ({ p : ι → MvPolynomial ι R // ∀ i, (p i).support ⊆ monoms i }) ≃
      ((Σ i, monoms i) → R) :=
  { toFun := fun p i => (p.1 i.1).coeff i.2,
    invFun := fun p => ⟨fun i =>
      { toFun := fun m => if hm : m ∈ monoms i then p ⟨i, ⟨m, hm⟩⟩ else 0
        support := (monoms i).filter (fun m => ∃ hm : m ∈ monoms i, p ⟨i, ⟨m, hm⟩⟩ ≠ 0),
        mem_support_toFun := by  simp (config := {contextual := true}) },
      fun i => Finset.filter_subset _ _⟩,
    left_inv := fun p => by
      ext i m
      simp only [coeff, ne_eq, exists_prop, dite_eq_ite, Finsupp.coe_mk, ite_eq_left_iff]
      intro hm
      have : m ∉ (p.1 i).support := fun h => hm (p.2 i h)
      rw [MvPolynomial.mem_support_iff] at this
      simpa [coeff, eq_comm] using this
    right_inv := fun p => by ext; simp [coeff] }

@[simp]
theorem lift_genericPolyMap {R : Type _} [CommRing R] [Fintype ι]
    [DecidableEq ι] [DecidableEq R] (mons : ι → Finset (ι →₀ ℕ))
    (f :  (i : ι) × { x // x ∈ mons i } ⊕ ι → R) (i : ι) :
    FreeCommRing.lift (R := R) f (genericPolyMap mons i) =
      MvPolynomial.eval (f ∘ Sum.inr)
        (((mvPolynomialSupportLEEquiv ι R mons).symm
          (f ∘ Sum.inl)).1 i) := by
  conv_rhs => rw [MvPolynomial.eval_eq]
  simp only [genericPolyMap, Finsupp.prod_pow, map_sum, map_mul, lift_of, support,
    mvPolynomialSupportLEEquiv, coeff, map_prod,
    ne_eq, Function.comp, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]
  rw [Finset.sum_filter]
  conv_rhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intros m _
  simp only [map_pow, lift_of, Subtype.coe_eta, Finset.coe_mem,
    exists_prop, true_and, dite_eq_ite, ite_true, ite_not]
  split_ifs with h0
  · simp_all
  · congr 1
    apply Eq.symm
    refine Finset.prod_subset (Finset.subset_univ _) ?_
    simp (config := {contextual := true})

noncomputable def genericPolyMapSurjectiveOfInjective {ι : Type u} [Fintype ι]
    (mons : ι → Finset (ι →₀ ℕ)) : Language.field.Sentence :=
  let l1 : List (Language.field.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι))) :=
    (Finset.univ : Finset ι).toList.map (fun i =>
      (termOfFreeCommRing (genericPolyMap mons i)).relabel
        (Sum.inl ∘ Sum.map id (fun i => (0, i)))
    =' (termOfFreeCommRing (genericPolyMap mons i)).relabel
        (Sum.inl ∘ Sum.map id (fun i => (1, i))))
  let f1 : Language.field.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    l1.foldr (. ⊓ .) ⊤
  let l2 : List (Language.field.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι))) :=
    (Finset.univ : Finset ι).toList.map  (fun i =>
      .var (Sum.inl (Sum.inr (0, i))) =' .var (Sum.inl (Sum.inr (1, i))))
  let f2 : Language.field.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    l2.foldr (. ⊓ .) ⊤
  let inj : Language.field.Formula (Σ i : ι, mons i) :=
    Formula.allsᵢ (γ := Fin 2 × ι) id (f1 ⟹ f2)
  let l3 : List (Language.field.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι))) :=
    (Finset.univ : Finset ι).toList.map  (fun i =>
      (termOfFreeCommRing (genericPolyMap mons i)).relabel
        (Sum.inl ∘ Sum.map id (fun i => (0, i))) ='
      .var (Sum.inl (Sum.inr (1, i))))
  let f3 : Language.field.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    l3.foldr (. ⊓ .) ⊤
  let surj : Language.field.Formula (Σ i : ι, mons i) :=
    Formula.allsᵢ.{0, 0, u, u, u} (γ := ι) id
      (Formula.exsᵢ.{0, 0, u, u, u} (γ := ι)
        (fun (i : (Σ i : ι, mons i) ⊕ (Fin 2 × ι)) =>
          show ((Σ i : ι, mons i) ⊕ ι) ⊕ ι
          from Sum.elim (Sum.inl ∘ Sum.inl)
            (fun i => if i.1 = 0 then Sum.inr i.2 else (Sum.inl (Sum.inr i.2))) i) f3)
  Formula.allsᵢ (γ := Σ i : ι, mons i) Sum.inr (inj ⟹ surj)

theorem realize_genericPolyMapSurjectiveOfInjective
    {K : Type v} [CompatibleField K] {ι : Type u} [Fintype ι]
    (mons : ι → Finset (ι →₀ ℕ)) :
    (K ⊨ genericPolyMapSurjectiveOfInjective mons) ↔
      ∀ p : { p : ι → MvPolynomial ι K // (∀ i, (p i).support ⊆ mons i) },
        Function.Injective (fun v i => MvPolynomial.eval v (p.1 i)) →
        Function.Surjective (fun v i => MvPolynomial.eval v (p.1 i)) := by
  letI := Classical.decEq K
  letI := Classical.decEq ι
  rw [Equiv.forall_congr_left' (mvPolynomialSupportLEEquiv ι K mons)]
  simp only [Sentence.Realize, Formula.Realize, genericPolyMapSurjectiveOfInjective, Function.comp,
    Sum.map, id_eq, BoundedFormula.realize_allsᵢ, Sum.elim_inr, BoundedFormula.realize_imp,
    BoundedFormula.realize_foldr_inf, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff', BoundedFormula.realize_bdEqual,
    Term.realize_relabel, Sum.elim_inl, realize_termOfFreeCommRing, lift_genericPolyMap,
    Term.realize_var, Equiv.forall_congr_left' (Equiv.curry (Fin 2) ι K), Equiv.curry_symm_apply,
    Function.uncurry_apply_pair, Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi,
    BoundedFormula.realize_exsᵢ, ite_true, one_ne_zero, ite_false, Function.Injective,
    Function.funext_iff, Function.Surjective]
  rfl

end FirstOrder
