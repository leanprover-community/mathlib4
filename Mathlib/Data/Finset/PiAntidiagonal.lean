/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Eric Wieser, Bhavik Mehta
-/
import Mathlib.Data.Finset.Antidiagonal
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic

/-!
# Partial HasAntidiagonal for functions with finite support

For an `AddCommMonoid` `μ`,
`Finset.HasAntidiagonal μ` provides a function `antidiagonal : μ → Finset (μ × μ)`
which maps `n : μ` to a `Finset` of pairs `(a, b)` such that `a + b = n`.

In this file, we provide an analogous definition for `ι →₀ μ`,
with an explicit finiteness condition on the support,
assuming `AddCommMonoid μ`, `HasAntidiagonal μ`,
For computability reasons, we also need `DecidableEq ι` and `DecidableEq μ`.

This Finset could be viewed inside `ι → μ`,
but the `Finsupp` condition provides a natural `DecidableEq` instance.

## Main definitions

* `Finset.piAntidiagonal s n` is the finite set of all functions
  with finite support contained in `s` and sum `n : μ`
  That condition is expressed by `Finset.mem_piAntidiagonal`
* `Finset.mem_piAntidiagonal'` rewrites the `Finsupp.sum` condition as a `Finset.sum`.
* `Finset.finAntidiagonal`, a more general case of `Finset.Nat.antidiagonalTuple`
  (TODO: deduplicate).

-/

namespace Finset

variable {ι μ μ' : Type*}

open scoped BigOperators

open Function Finsupp

section Fin

variable [AddCommMonoid μ] [DecidableEq μ] [HasAntidiagonal μ]

/-- `finAntidiagonal d n` is the type of `d`-tuples with sum `n`.

TODO: deduplicate with the less general `Finset.Nat.antidiagonalTuple`. -/
def finAntidiagonal (d : ℕ) (n : μ) : Finset (Fin d → μ) :=
  aux d n
where
  /-- Auxiliary construction for `finAntidiagonal` that bundles a proof of lawfulness
  (`mem_finAntidiagonal`), as this is needed to invoke `disjiUnion`. Using `Finset.disjiUnion` makes
  this computationally much more efficient than using `Finset.biUnion`. -/
  aux (d : ℕ) (n : μ) : {s : Finset (Fin d → μ) // ∀ f, f ∈ s ↔ ∑ i, f i = n} :=
    match d with
    | 0 =>
      if h : n = 0 then
        ⟨{0}, by simp [h, Subsingleton.elim finZeroElim ![]]⟩
      else
        ⟨∅, by simp [Ne.symm h]⟩
    | d + 1 =>
      { val := (antidiagonal n).disjiUnion
          (fun ab => (aux d ab.2).1.map {
              toFun := Fin.cons (ab.1)
              inj' := Fin.cons_right_injective _ })
          (fun i _hi j _hj hij => Finset.disjoint_left.2 fun t hti htj => hij <| by
            simp_rw [Finset.mem_map, Embedding.coeFn_mk] at hti htj
            obtain ⟨ai, hai, hij'⟩ := hti
            obtain ⟨aj, haj, rfl⟩ := htj
            rw [Fin.cons_eq_cons] at hij'
            ext
            · exact hij'.1
            · obtain ⟨-, rfl⟩ := hij'
              rw [← (aux d i.2).prop ai |>.mp hai, ← (aux d j.2).prop ai |>.mp haj])
        property := fun f => by
          simp_rw [mem_disjiUnion, mem_antidiagonal, mem_map, Embedding.coeFn_mk, Prod.exists,
            (aux d _).prop, Fin.sum_univ_succ]
          constructor
          · rintro ⟨a, b, rfl, g, rfl, rfl⟩
            simp only [Fin.cons_zero, Fin.cons_succ]
          · intro hf
            exact ⟨_, _, hf, _, rfl, Fin.cons_self_tail f⟩ }

lemma mem_finAntidiagonal (d : ℕ) (n : μ) (f : Fin d → μ) :
    f ∈ finAntidiagonal d n ↔ ∑ i, f i = n :=
  (finAntidiagonal.aux d n).prop f

/-- `finAntidiagonal₀ d n` is the type of d-tuples with sum `n` -/
def finAntidiagonal₀ (d : ℕ) (n : μ) : Finset (Fin d →₀ μ) :=
  (finAntidiagonal d n).map
    { toFun := fun f =>
        -- this is `Finsupp.onFinset`, but computable
        { toFun := f, support := univ.filter (f · ≠ 0), mem_support_toFun := fun x => by simp }
      inj' := fun _ _ h => DFunLike.coe_fn_eq.mpr h }

lemma mem_finAntidiagonal₀' (d : ℕ) (n : μ) (f : Fin d →₀ μ) :
    f ∈ finAntidiagonal₀ d n ↔ ∑ i, f i = n := by
  simp only [finAntidiagonal₀, mem_map, Embedding.coeFn_mk, ← mem_finAntidiagonal,
    ← DFunLike.coe_injective.eq_iff, Finsupp.coe_mk, exists_eq_right]

lemma mem_finAntidiagonal₀ (d : ℕ) (n : μ) (f : Fin d →₀ μ) :
    f ∈ finAntidiagonal₀ d n ↔ sum f (fun _ x => x) = n := by
  rw [mem_finAntidiagonal₀', sum_of_support_subset f (subset_univ _) _ (fun _ _ => rfl)]

end Fin

section piAntidiagonal

variable [DecidableEq ι]
variable [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ]

/-- The Finset of functions `ι →₀ μ` with support contained in `s` and sum `n`. -/
def piAntidiagonal (s : Finset ι) (n : μ) : Finset (ι →₀ μ) :=
  let x : Finset (s →₀ μ) :=
    -- any ordering of elements of `s` will do, the result is the same
    (Fintype.truncEquivFinOfCardEq <| Fintype.card_coe s).lift
      (fun e => (finAntidiagonal₀ s.card n).map (equivCongrLeft e.symm).toEmbedding)
      (fun e1 e2 => Finset.ext fun x => by
        simp only [mem_map_equiv, equivCongrLeft_symm, Equiv.symm_symm, equivCongrLeft_apply,
          mem_finAntidiagonal₀, sum_equivMapDomain])
  x.map
    ⟨Finsupp.extendDomain, Function.LeftInverse.injective subtypeDomain_extendDomain⟩

/-- A function belongs to `piAntidiagonal s n`
    iff its support is contained in `s` and the sum of its components is equal to `n` -/
lemma mem_piAntidiagonal {s : Finset ι} {n : μ} {f : ι →₀ μ} :
    f ∈ piAntidiagonal s n ↔ f.support ⊆ s ∧ Finsupp.sum f (fun _ x => x) = n := by
  simp only [piAntidiagonal, mem_map, Embedding.coeFn_mk, mem_finAntidiagonal₀]
  induction' (Fintype.truncEquivFinOfCardEq <| Fintype.card_coe s) using Trunc.ind with e'
  simp_rw [Trunc.lift_mk, mem_map_equiv, equivCongrLeft_symm, Equiv.symm_symm, equivCongrLeft_apply,
    mem_finAntidiagonal₀, sum_equivMapDomain]
  constructor
  · rintro ⟨f, rfl, rfl⟩
    dsimp [sum]
    constructor
    · exact Finset.coe_subset.mpr (support_extendDomain_subset _)
    · simp
  · rintro ⟨hsupp, rfl⟩
    refine (Function.RightInverse.surjective subtypeDomain_extendDomain).exists.mpr ⟨f, ?_⟩
    constructor
    · simp_rw [sum, support_subtypeDomain, subtypeDomain_apply, sum_subtype_of_mem _ hsupp]
    · rw [extendDomain_subtypeDomain _ hsupp]

end piAntidiagonal

section

variable [DecidableEq ι]
variable [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ]
variable [AddCommMonoid μ'] [HasAntidiagonal μ'] [DecidableEq μ']

lemma mem_piAntidiagonal' (s : Finset ι) (n : μ) (f) :
    f ∈ piAntidiagonal s n ↔ f.support ⊆ s ∧ s.sum f = n := by
  rw [mem_piAntidiagonal, and_congr_right_iff]
  intro hs
  rw [sum_of_support_subset _ hs]
  exact fun _ _ => rfl

@[simp]
theorem piAntidiagonal_empty_of_zero :
    piAntidiagonal (∅ : Finset ι) (0 : μ) = {0} := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [mem_singleton, subset_empty]
  rw [support_eq_empty, and_iff_left_iff_imp]
  intro hf
  rw [hf, sum_zero_index]

theorem piAntidiagonal_empty_of_ne_zero {n : μ} (hn : n ≠ 0) :
    piAntidiagonal (∅ : Finset ι) n = ∅ := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [subset_empty, support_eq_empty, sum_empty,
    not_mem_empty, iff_false, not_and]
  intro hf
  rw [hf, sum_zero_index]
  exact Ne.symm hn

theorem piAntidiagonal_empty [DecidableEq μ] (n : μ) :
    piAntidiagonal (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  split_ifs with hn
  · rw [hn]
    apply piAntidiagonal_empty_of_zero
  · apply piAntidiagonal_empty_of_ne_zero hn

theorem mem_piAntidiagonal_insert [DecidableEq ι] {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) {f : ι →₀ μ} :
    f ∈ piAntidiagonal (insert a s) n ↔
      ∃ m ∈ antidiagonal n, ∃ (g : ι →₀ μ),
        f = Finsupp.update g a m.1 ∧ g ∈ piAntidiagonal s m.2 := by
  simp only [mem_piAntidiagonal', mem_antidiagonal, Prod.exists, sum_insert h]
  constructor
  · rintro ⟨hsupp, rfl⟩
    refine ⟨_, _, rfl, Finsupp.erase a f, ?_, ?_, ?_⟩
    · rw [update_erase_eq_update, update_self]
    · rwa [support_erase, ← subset_insert_iff]
    · apply sum_congr rfl
      intro x hx
      rw [Finsupp.erase_ne (ne_of_mem_of_not_mem hx h)]
  · rintro ⟨n1, n2, rfl, g, rfl, hgsupp, rfl⟩
    constructor
    · exact (support_update_subset _ _).trans (insert_subset_insert a hgsupp)
    · simp only [coe_update]
      apply congr_arg₂
      · rw [update_same]
      · apply sum_congr rfl
        intro x hx
        rw [update_noteq (ne_of_mem_of_not_mem hx h) n1 ⇑g]

theorem piAntidiagonal_insert [DecidableEq ι] [DecidableEq μ] {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) :
    piAntidiagonal (insert a s) n = (antidiagonal n).biUnion
      (fun p : μ × μ =>
        (piAntidiagonal s p.snd).attach.map
        ⟨fun f => Finsupp.update f.val a p.fst,
        (fun ⟨f, hf⟩ ⟨g, hg⟩ hfg => Subtype.ext <| by
          simp only [mem_val, mem_piAntidiagonal] at hf hg
          simp only [DFunLike.ext_iff] at hfg ⊢
          intro x
          obtain rfl | hx := eq_or_ne x a
          · replace hf := mt (hf.1 ·) h
            replace hg := mt (hg.1 ·) h
            rw [not_mem_support_iff.mp hf, not_mem_support_iff.mp hg]
          · simpa only [coe_update, Function.update, dif_neg hx] using hfg x)⟩) := by
  ext f
  rw [mem_piAntidiagonal_insert h, mem_biUnion]
  simp_rw [mem_map, mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk, exists_prop, and_comm,
    eq_comm]

-- This should work under the assumption that e is an embedding and an AddHom
lemma mapRange_piAntidiagonal_subset {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (piAntidiagonal s n).map (mapRange.addEquiv e).toEmbedding ⊆ piAntidiagonal s (e n) := by
  intro f
  simp only [mem_map, mem_piAntidiagonal]
  rintro ⟨g, ⟨hsupp, hsum⟩, rfl⟩
  simp only [AddEquiv.toEquiv_eq_coe, mapRange.addEquiv_toEquiv, Equiv.coe_toEmbedding,
    mapRange.equiv_apply, EquivLike.coe_coe]
  constructor
  · exact subset_trans (support_mapRange) hsupp
  · rw [sum_mapRange_index (fun _ => rfl), ← hsum, _root_.map_finsupp_sum]

lemma mapRange_piAntidiagonal_eq {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (piAntidiagonal s n).map (mapRange.addEquiv e).toEmbedding = piAntidiagonal s (e n) := by
  ext f
  constructor
  · apply mapRange_piAntidiagonal_subset
  · set h := (mapRange.addEquiv e).toEquiv with hh
    intro hf
    have : n = e.symm (e n) := (AddEquiv.eq_symm_apply e).mpr rfl
    rw [mem_map_equiv, this]
    apply mapRange_piAntidiagonal_subset
    rw [← mem_map_equiv]
    convert hf
    rw [map_map, hh]
    convert map_refl
    apply Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

end

section CanonicallyOrderedAddCommMonoid
variable [DecidableEq ι]
variable [CanonicallyOrderedAddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ]

theorem piAntidiagonal_zero (s : Finset ι) :
    piAntidiagonal s (0 : μ) = {(0 : ι →₀ μ)} := by
  ext f
  simp_rw [mem_piAntidiagonal', mem_singleton, sum_eq_zero_iff, Finset.subset_iff,
    mem_support_iff, not_imp_comm, ← forall_and, ← or_imp, DFunLike.ext_iff, zero_apply, or_comm,
    or_not, true_imp_iff]

end CanonicallyOrderedAddCommMonoid

end Finset
