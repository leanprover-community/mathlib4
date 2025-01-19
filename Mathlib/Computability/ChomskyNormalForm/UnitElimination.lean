/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.ChomskyNormalForm.EmptyElimination

/-!
# Unit Elimination

This file contains the algorithm to eliminate rules from a context-free grammar which rewrite to a
single nonterminal symbol, while preserving the language of the grammar.

## Main definitions
* `ContextFreeGrammar.computeUnitPairs`: Fixpoint iteration to compute all `UnitPair`s, i.e., all
pairs of two nonterminal symbols for which the second can be derived from the first by a chain of
rule applications which rewrite to a single nonterminal.
* `ContextFreeGrammar.eliminateUnitRules`: Eliminates all rules rewriting to a single nonterminal.

## Main theorems
* `ContextFreeGrammar.computeUnitPairs_iff`: All and only `UnitPair`s are computed.
* `ContextFreeGrammar.eliminateUnitRules_correct`: The transformed grammar's language coincides with
the original.

## References
* [John E. Hopcroft, Rajeev Motwani, and Jeffrey D. Ullman. 2006. Introduction to Automata Theory,
   Languages, and Computation (3rd Edition). Addison-Wesley Longman Publishing Co., Inc., USA.]
   [Hopcroft et al. 2006]
-/

universe uN uT
namespace ContextFreeGrammar

variable {T : Type uT}

/- Definition of `ContextFreeGrammar.UnitPair n₁ n₂` relating two nonterminals `n₁` and `n₂`, if
`n₁` can be transformed to `n₂` using only rules rewriting to a single nonterminal. -/
section UnitPairs

variable {g : ContextFreeGrammar.{uN, uT} T} [DecidableEq g.NT]

/-- Convenient to talk about the rule rewriting a nonterminal `nᵢ` to another nonterminal `nₒ` -/
abbrev unitRule (nᵢ nₒ : g.NT) : ContextFreeRule T g.NT := ⟨nᵢ, [Symbol.nonterminal nₒ]⟩

/-- `UnitPair n₁ n₂`, (w.r.t. a ContextFreeGrammar `g`) means that `g` can derive `n₂` from `n₁`
only using unitRules -/
inductive UnitPair : g.NT → g.NT → Prop where
  /- UnitPair is reflexive due to the empty derivation -/
  | refl {n : g.NT} (hng : n ∈ g.generators) : UnitPair n n
  /- UnitPair is transitive -/
  | trans {n₁ n₂ n₃ : g.NT} (hng : unitRule n₁ n₂ ∈ g.rules) (hnn : UnitPair n₂ n₃) : UnitPair n₁ n₃

@[refl]
lemma UnitPair.rfl {n : g.NT} (hn : n ∈ g.generators) : UnitPair n n := UnitPair.refl hn

lemma UnitPair.derives {n₁ n₂ : g.NT} (hnn : UnitPair n₁ n₂) :
    g.Derives [Symbol.nonterminal n₁] [Symbol.nonterminal n₂] := by
  induction hnn with
  | refl => rfl
  | trans hr _ ih => exact Produces.trans_derives ⟨_, hr, ContextFreeRule.Rewrites.head []⟩ ih

/-- We use this to concisely state a rule is not a `unitRule` if its output is `NonUnit` -/
abbrev NonUnit {N : Type*} (u : List (Symbol T N)) : Prop :=
  match u with
  | [Symbol.nonterminal _] => False
  | _ => True

lemma DerivesIn.unitPair_prefix {u : List T} {v : List (Symbol T g.NT)} {n : g.NT} {m : ℕ}
    (hvu : g.DerivesIn v (u.map Symbol.terminal) m) (hng : n ∈ g.generators)
    (hv : [Symbol.nonterminal n] = v) :
    ∃ n' w k,
      UnitPair n n' ∧ g.Produces [Symbol.nonterminal n'] w ∧ NonUnit w ∧ k ≤ m
      ∧ g.DerivesIn w (u.map Symbol.terminal) k := by
  induction hvu using DerivesIn.head_induction_on generalizing n with
  | refl =>
    cases u <;> simp only
      [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, List.map_eq_nil_iff, false_and]
        at hv
  | @head m v w hvw hwu ih =>
    by_cases hw : NonUnit w
    · exact ⟨n, w, m, UnitPair.rfl hng, hv ▸ hvw, hw, m.le_succ, hwu⟩
    · match w with
      | [Symbol.nonterminal n'] =>
        have hn' : n' ∈ g.generators := by
          cases m with
          | zero => cases u <;> cases hwu
          | succ =>
            obtain ⟨w', hgw', _⟩ := hwu.head_of_succ
            exact input_mem_generators hgw'.rule
        obtain ⟨v'', w', m, hnv'', hgv'', hw', hm, hgw'⟩ := ih hn' rfl
        exact ⟨v'', w', m, UnitPair.trans (hv ▸ hvw).rule hnv'', hgv'', hw', Nat.le_succ_of_le hm,
          hgw'⟩
      | [Symbol.terminal _] => simp at hw
      | [] => simp at hw
      | _ :: _ :: _ => simp [NonUnit] at hw

end UnitPairs

/-! Fixpoint iteration to compute all `UnitPair`s.
A unit pair is a pair `(n₁, n₂)` of nonterminals s.t. `g` can transform `n₁` to `n₂` only using
`unitRule`s, i.e., a chain of productions rewriting nonterminals to nonterminals -/
section ComputeUnitPairs

variable {g : ContextFreeGrammar.{uN,uT} T} [DecidableEq g.NT]

/-- `generatorsProdDiag g` is the diagonal of `g.generators × g.generators` -/
noncomputable def generatorsProdDiag : Finset (g.NT × g.NT) :=
  (g.rules.toList.map (fun r ↦ (r.input, r.input))).toFinset

lemma generatorsProdDiag_subset_generators_prod :
    g.generatorsProdDiag ⊆ g.generators ×ˢ g.generators := by
  unfold generatorsProdDiag generators
  cases g.rules.toList with
  | nil => simp
  | cons a l =>
    simp only [List.map_cons, List.toFinset_cons]
    intro p hp
    rw [Finset.mem_insert, List.mem_toFinset, List.mem_map] at hp
    cases hp with
    | inl hpd =>
      simp [Finset.mem_product, hpd]
    | inr hlp =>
      obtain ⟨p', hp', rfl⟩ := hlp
      simp only [Finset.mem_product, Finset.mem_insert, List.mem_toFinset, List.mem_map, and_self]
      right
      use p'

lemma generatorsProdDiag_unitPairs {p : g.NT × g.NT} (hp : p ∈ g.generatorsProdDiag) :
    UnitPair p.1 p.2 := by
  unfold generatorsProdDiag at hp
  revert hp
  cases heq : g.rules.toList with
  | nil => tauto
  | cons r l =>
    simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
      List.mem_map]
    intro hp
    cases hp with
    | inl hpr =>
      rw [hpr]
      change UnitPair r.input r.input
      constructor
      apply input_mem_generators
      rw [← Finset.mem_toList, heq]
      exact List.mem_cons_self r l
    | inr hap =>
      obtain ⟨v, hvl, hvp⟩ := hap
      rw [← hvp]
      constructor
      apply input_mem_generators
      rw [← Finset.mem_toList, heq]
      exact List.mem_cons_of_mem r hvl

/-- Reflects transitivity of unit pairs. If `(n₂, n₃)` is a unit pair and `g` rewrites `n₁` to `n₂`
then `(n₁, n₃)` are also a unit pair -/
def addUnitPair (nᵢ nₒ : g.NT) (p : g.NT × g.NT) (l : Finset (g.NT × g.NT)) :=
  if nₒ = p.1 then insert (nᵢ, p.2) l else l

/-- If `r` is a unit rule, add all unit pairs `(r.input, n)` to `l` for all unit pairs
`(r.output, n)` in `l` -/
def collectUnitPairs (r : ContextFreeRule T g.NT) (l : List (g.NT × g.NT)) :=
  match r.output with
  | [Symbol.nonterminal v] => l.foldr (addUnitPair r.input v) ∅
  | _ => ∅

lemma collectUnitPairs_unitPair_rec {nᵢ nₒ : g.NT} {p : g.NT × g.NT} {l : List (g.NT × g.NT)}
    {x : Finset (g.NT × g.NT)} (hp : p ∈ l.foldr (addUnitPair nᵢ nₒ) x) :
    p ∈ x ∨ ∃ v, (nₒ, v) ∈ l ∧ p = (nᵢ, v) := by
  induction l generalizing x with
  | nil =>
    left
    exact hp
  | cons a l ih =>
    simp only [addUnitPair, List.foldr_cons, List.mem_cons] at hp
    split at hp <;> rename_i ha
    · simp only [Finset.mem_insert] at hp
      cases hp with
      | inl hpd =>
        right
        exact ⟨a.2, ha ▸ l.mem_cons_self a, hpd⟩
      | inr hpl =>
        specialize ih hpl
        cases ih with
        | inl => left; assumption
        | inr hlp =>
          obtain ⟨v, hvl, hpv⟩ := hlp
          right
          exact ⟨v, List.mem_cons_of_mem a hvl, hpv ▸ rfl⟩
    · specialize ih hp
      cases ih with
      | inl => left; assumption
      | inr hlp =>
        obtain ⟨v, hvl, hpv⟩ := hlp
        right
        exact ⟨v, List.mem_cons_of_mem a hvl, hpv ▸ rfl⟩

lemma collectUnitPairs_unitPair {r : ContextFreeRule T g.NT} {l : List (g.NT × g.NT)}
    (hrg : r ∈ g.rules) (hp : ∀ p ∈ l, UnitPair p.1 p.2) :
    ∀ p ∈ collectUnitPairs r l, UnitPair p.1 p.2 := by
  intro p hprl
  match hro : r.output with
  | [] => simp [collectUnitPairs, hro] at hprl
  | _ :: _ :: _ => simp [collectUnitPairs, hro] at hprl
  | [Symbol.terminal _ ] => simp [collectUnitPairs, hro] at hprl
  | [Symbol.nonterminal _] =>
    rw [collectUnitPairs, hro] at hprl
    cases collectUnitPairs_unitPair_rec hprl
    · contradiction
    · rename_i hp''
      obtain ⟨v', hl, hpr⟩ := hp''
      exact UnitPair.trans ((congr_arg (⟨p.fst, · ⟩ ∈ g.rules) hro).mp (hpr ▸ hrg))
        (hpr ▸ (hp _ hl))

/-- Single step of fixpoint iteration, adding unit pairs to `l` for all rules `r` in `g.rules` -/
noncomputable def addUnitPairs (l : Finset (g.NT × g.NT)) : Finset (g.NT × g.NT) :=
  g.rules.toList.attach.foldr (fun r p ↦ collectUnitPairs r l.toList ∪ p) l

lemma collectUnitPairs_subset_generatorsProd {r : ContextFreeRule T g.NT} (l : Finset (g.NT × g.NT))
    (hlg : l ⊆ g.generators ×ˢ g.generators) (hrg : r ∈ g.rules) :
    collectUnitPairs r l.toList ⊆ g.generators ×ˢ g.generators := by
  unfold collectUnitPairs
  intro p hp
  match heq : r.output with
  | [Symbol.nonterminal v] =>
    rw [heq] at hp
    obtain hpp := collectUnitPairs_unitPair_rec hp
    cases hpp
    · contradiction
    rw [Finset.mem_product]
    rename_i hp'
    obtain ⟨v', hvl, hp2⟩ := hp'
    rw [hp2]
    constructor
    · exact input_mem_generators hrg
    · rw [Finset.mem_toList] at hvl
      specialize hlg hvl
      rw [Finset.mem_product] at hlg
      exact hlg.2
  | [] => simp [heq] at hp
  | [Symbol.terminal _] => simp [heq] at hp
  | _ :: _ :: _ => simp [heq] at hp

lemma addUnitPairs_subset_generatorsProd (l : Finset (g.NT × g.NT))
    (hlg : l ⊆ g.generators ×ˢ g.generators) :
    addUnitPairs l ⊆ g.generators ×ˢ g.generators := by
  unfold addUnitPairs
  induction g.rules.toList.attach with
  | nil => exact hlg
  | cons d _ ih =>
    simp only [List.pure_def, List.bind_eq_flatMap, Finset.mem_toList, List.flatMap_subtype,
      List.flatMap_singleton', List.flatMap_cons, List.singleton_append, List.foldr_cons] at ih ⊢
    exact Finset.union_subset
      (collectUnitPairs_subset_generatorsProd _ hlg (Finset.mem_toList.1 d.2)) ih

lemma subset_addUnitPairs (l : Finset (g.NT × g.NT)) : l ⊆ (addUnitPairs l) := by
  unfold addUnitPairs
  induction g.rules.toList.attach with
  | nil => rfl
  | cons _ _ ih => simp [subset_trans ih]

lemma generatorsProd_limits_unitPairs {l : Finset (g.NT × g.NT)}
    (hlg : l ⊆ g.generators ×ˢ g.generators)
    (hne : l ≠ addUnitPairs l) :
    (g.generators ×ˢ g.generators).card - (addUnitPairs l).card
      < (g.generators ×ˢ g.generators).card - l.card := by
   have hl := HasSubset.Subset.ssubset_of_ne (subset_addUnitPairs l) hne
   exact Nat.sub_lt_sub_left (Nat.lt_of_lt_of_le (Finset.card_lt_card hl)
     (Finset.card_le_card (addUnitPairs_subset_generatorsProd l hlg))) (Finset.card_lt_card hl)

/-- Fixpoint iteration computing the unit pairs of `g`. -/
noncomputable def addUnitPairsIter (l : Finset (g.NT × g.NT))
    (hlg : l ⊆ g.generators ×ˢ g.generators) :
    Finset (g.NT × g.NT) :=
  let l' := addUnitPairs l
  if l = l' then
    l
  else
    addUnitPairsIter l' (addUnitPairs_subset_generatorsProd l hlg)
  termination_by ((g.generators ×ˢ g.generators).card - l.card)
  decreasing_by
    rename_i hl
    exact generatorsProd_limits_unitPairs hlg hl

/-- Compute the least-fixpoint of `add_unitPairs_iter`, i.e., all (and only) unit pairs -/
noncomputable def computeUnitPairs : Finset (g.NT × g.NT) :=
  addUnitPairsIter g.generatorsProdDiag generatorsProdDiag_subset_generators_prod

lemma mem_addUnitPairs_unitPair (l : Finset (g.NT × g.NT)) (hl : ∀ p ∈ l, UnitPair p.1 p.2) :
    ∀ p ∈ addUnitPairs l, UnitPair p.1 p.2 := by
  unfold addUnitPairs
  induction g.rules.toList.attach with
  | nil =>
    intro p
    simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_nil, List.foldr_nil]
    exact hl p
  | cons a _ ih =>
    intro p hpl
    simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_cons, Finset.mem_toList,
      List.flatMap_subtype, List.flatMap_singleton', List.singleton_append, List.foldr_cons,
      Finset.mem_union] at hpl
    cases hpl with
    | inl hpdl =>
      apply collectUnitPairs_unitPair (Finset.mem_toList.1 a.2) _ _ hpdl
      intro p hp'
      simp [Finset.mem_toList] at hp'
      exact hl p hp'
    | inr hpl =>
      apply ih
      convert hpl
      simp

lemma mem_addUnitPairIter_unitPair (l : Finset (g.NT × g.NT))
    (hlg : l ⊆ g.generators ×ˢ g.generators) (hl : ∀ p ∈ l, UnitPair p.1 p.2) :
    ∀ p ∈ (addUnitPairsIter l hlg), UnitPair p.1 p.2 := by
  unfold addUnitPairsIter
  intro p
  dsimp only
  split
  · tauto
  · exact mem_addUnitPairIter_unitPair (addUnitPairs l)
          (addUnitPairs_subset_generatorsProd l hlg) (mem_addUnitPairs_unitPair l hl) p
  termination_by ((g.generators ×ˢ g.generators).card - l.card)
  decreasing_by
    rename_i hl
    exact generatorsProd_limits_unitPairs hlg hl

lemma addUnitPairsIter_fixpoint (l : Finset (g.NT × g.NT))
    (hlg : l ⊆ g.generators ×ˢ g.generators) :
    addUnitPairsIter l hlg = addUnitPairs (addUnitPairsIter l hlg) := by
  unfold addUnitPairsIter
  simp only
  split <;> rename_i h
  · exact h
  · apply addUnitPairsIter_fixpoint
  termination_by ((g.generators ×ˢ g.generators).card - l.card)
  decreasing_by
    rename_i hl
    exact generatorsProd_limits_unitPairs hlg hl

lemma subset_addUnitPairsIter {l : Finset (g.NT × g.NT)} {hlg : l ⊆ g.generators ×ˢ g.generators} :
    l ⊆ (addUnitPairsIter l hlg) := by
  unfold addUnitPairsIter
  intro p hpl
  simp only
  split
  · exact hpl
  · apply subset_addUnitPairsIter (subset_addUnitPairs _ hpl)
  termination_by ((g.generators ×ˢ g.generators).card - l.card)
  decreasing_by
    rename_i hl
    exact generatorsProd_limits_unitPairs hlg hl

lemma mem_collectUnitPairs {l : List (g.NT × g.NT)} {n₁ n₂ n₃ : g.NT} (hl : (n₂, n₃) ∈ l) :
    (n₁, n₃) ∈ collectUnitPairs (unitRule n₁ n₂) l := by
  unfold collectUnitPairs
  induction l with
  | nil => contradiction
  | cons _ _ ih =>
    simp only [List.mem_cons, List.foldr_cons] at hl ⊢
    unfold addUnitPair
    cases hl with
    | inl hd =>
      simp [← hd]
    | inr hl =>
      split
      · simp only [Finset.mem_insert, Prod.mk.injEq, true_and]
        right
        exact ih hl
      · exact ih hl

lemma mem_addUnitPairs {l : Finset (g.NT × g.NT)} {n₁ n₂ n₃ : g.NT} (hl : (n₂, n₃) ∈ l)
    (hg : ⟨n₁, [Symbol.nonterminal n₂]⟩ ∈ g.rules) :
    (n₁, n₃) ∈ addUnitPairs l := by
  unfold addUnitPairs
  have hgnn := g.rules.toList.mem_attach ⟨_, Finset.mem_toList.2 hg⟩
  revert hgnn n₂ l
  induction g.rules.toList.attach with
  | nil =>
    intro _ n₂ _ hg h
    contradiction
  | cons r t ih =>
    intro _ _ hl hg hrt
    cases hrt
    · simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_cons, Finset.mem_toList,
        List.flatMap_subtype, List.flatMap_singleton', List.singleton_append, List.foldr_cons,
        Finset.mem_union]
      left
      rw [← Finset.mem_toList] at hl
      exact mem_collectUnitPairs hl
    · simp only [List.pure_def, List.bind_eq_flatMap, Finset.mem_toList, List.flatMap_subtype,
        List.flatMap_singleton', List.flatMap_cons, List.singleton_append, List.foldr_cons,
        Finset.mem_union] at ih ⊢
      rename_i ht
      exact Or.inr (ih hl hg ht)

lemma unitPair_mem_addUnitPairsIter {l : Finset (g.NT × g.NT)} {n₁ n₂ : g.NT}
    (hlg : l ⊆ g.generators ×ˢ g.generators) (hgl : generatorsProdDiag ⊆ l) (hp : UnitPair n₁ n₂) :
    (n₁, n₂) ∈ addUnitPairsIter l hlg := by
  induction hp with
  | refl hvg =>
    apply Finset.mem_of_subset subset_addUnitPairsIter
    apply Finset.mem_of_subset hgl
    unfold generators at hvg
    unfold generatorsProdDiag
    rw [List.mem_toFinset, List.mem_map] at hvg ⊢
    obtain ⟨r, hrg, hr⟩ := hvg
    use r
    rw [hr]
    exact ⟨hrg, rfl⟩
  | trans hur hp ih =>
    rw [addUnitPairsIter_fixpoint]
    exact mem_addUnitPairs ih hur

lemma computeUnitPairs_iff {n₁ n₂ : g.NT} :
    (n₁, n₂) ∈ computeUnitPairs ↔ UnitPair n₁ n₂ := by
  constructor
  · intro hn
    apply mem_addUnitPairIter_unitPair g.generatorsProdDiag
      generatorsProdDiag_subset_generators_prod _ _ hn
    intro
    exact generatorsProdDiag_unitPairs
  · intro hnn
    apply unitPair_mem_addUnitPairsIter _ _ hnn
    rfl

end ComputeUnitPairs

/-! Definition and properties of `ContextFreeGrammar.eliminateUnitRules`, the algorithm to remove
all rules with a single nonterminal on the right-hand side. -/
section EliminateUnitRules

variable {g : ContextFreeGrammar T} [DecidableEq g.NT]

/-- For a given unit pair `(n₁, n₂)`, computes rules `r : n₁ → o`, s.t. there is a rule
`r' : n₂ → o` in `g` (and `o` is non-unit) -/
noncomputable def computeUnitPairRules (p : g.NT × g.NT) : List (ContextFreeRule T g.NT) :=
  let f (r : ContextFreeRule T g.NT) : Option (ContextFreeRule T g.NT) :=
    if r.input = p.2 then
      match r.output with
      | [Symbol.nonterminal _] => none
      | o => some ⟨p.1, o⟩
    else none
  g.rules.toList.filterMap f

/-- Computes non-unit rules for all unit pairs -/
noncomputable def removeUnitRules [DecidableEq T] (l : Finset (g.NT × g.NT)) :=
  ((l.toList).map computeUnitPairRules).flatten.toFinset


/-- Given `g`, computes a new grammar `g'` in which all unit rules are removed and, for each
unit pair `(n₁, n₂)`, we add rules `r : n₁ → o` if the rule `r' : n₂ → o` is in the grammar
(and non-unit) -/
noncomputable def eliminateUnitRules [DecidableEq T] (g : ContextFreeGrammar T)
    [DecidableEq g.NT] :=
  ContextFreeGrammar.mk g.NT g.initial (removeUnitRules computeUnitPairs)

lemma nonUnit_rules_mem {p : g.NT × g.NT} {r : ContextFreeRule T g.NT}
    (hrp : r ∈ computeUnitPairRules p) :
    r.input = p.1 ∧ ∃ r' ∈ g.rules, r.output = r'.output ∧ r'.input = p.2 := by
  simp only [List.mem_filterMap, Finset.mem_toList, Option.ite_none_right_eq_some,
    forall_exists_index, and_imp, computeUnitPairRules] at hrp
  obtain ⟨r', hrg, hrp, hrr⟩ := hrp
  split at hrr
  · contradiction
  · rw [Option.some.injEq] at hrr
    rw [← hrr]
    simp only [true_and]
    use r'

lemma mem_removeUnitRules_exists_UnitPair [DecidableEq T] {l : Finset (g.NT × g.NT)}
    {r : ContextFreeRule T g.NT} (hrl : r ∈ removeUnitRules l) :
    ∃ p r', p ∈ l ∧ r' ∈ g.rules ∧ r.input = p.1 ∧ r.output = r'.output ∧ r'.input = p.2 := by
  simp only [removeUnitRules, List.mem_toFinset, List.mem_flatten, List.mem_map,
    Finset.mem_toList, Prod.exists] at hrl
  obtain ⟨_, ⟨⟨u, v, _, rfl⟩, hruv⟩⟩ := hrl
  obtain ⟨_, ⟨r', _, _, _⟩⟩ := nonUnit_rules_mem hruv
  use (u, v), r'

lemma eliminateUnitRules_derives_to_derives [DecidableEq T] {u v : List (Symbol T g.NT)}
    (huv : g.eliminateUnitRules.Derives u v) : g.Derives u v := by
  change List (Symbol T g.eliminateUnitRules.NT) at u v
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih =>
    obtain ⟨r, hrin, hr⟩ := hp
    unfold eliminateUnitRules at hrin
    obtain ⟨⟨_, _⟩, r', hpin, hrin', heq1, heq2, heq3⟩ := mem_removeUnitRules_exists_UnitPair hrin
    simp only at heq1 heq3
    rw [r.rewrites_iff] at hr
    obtain ⟨p, q, rfl, hu⟩ := hr
    apply Derives.trans
    · apply Derives.append_right
      apply Derives.append_left
      · apply Derives.trans_produces
        · rewrite [computeUnitPairs_iff] at hpin
          rewrite [heq1]
          apply hpin.derives
        · rw [← heq3]
          exact Produces.input_output hrin'
    · rwa [← heq2, ← hu]

lemma nonUnit_mem_computeUnitPairRules {n₁ n₂ : g.NT} {w : List (Symbol T g.NT)}
    (hg : ⟨n₁, w⟩ ∈ g.rules) (hw : NonUnit w) :
    ⟨n₂, w⟩ ∈ computeUnitPairRules (n₂, n₁) := by
  simp only [computeUnitPairRules, List.mem_filterMap, Finset.mem_toList,
    Option.ite_none_right_eq_some]
  use ⟨n₁, w⟩
  simp only [true_and]
  use hg
  match w with
  | [Symbol.nonterminal _] => exact False.elim hw
  | [Symbol.terminal _] => rfl
  | [] => rfl
  | _ :: _ :: _ => simp

lemma nonUnit_mem_removeUnitRules [DecidableEq T] {n₁ n₂ : g.NT} {u : List (Symbol T g.NT)}
    {l : Finset (g.NT × g.NT)} (hug : ⟨n₂, u⟩ ∈ g.rules) (hu : NonUnit u) (hnn : (n₁, n₂) ∈ l) :
    ⟨n₁, u⟩ ∈ removeUnitRules l := by
  simp only [removeUnitRules, List.mem_toFinset, List.mem_flatten, List.mem_map,
    Finset.mem_toList, Prod.exists]
  exact ⟨computeUnitPairRules (n₁, n₂), ⟨n₁, n₂, hnn, rfl⟩, nonUnit_mem_computeUnitPairRules hug hu⟩

lemma produces_nonUnit_eliminateUnitRules_produces [DecidableEq T] {n₁ n₂ : g.NT}
    {u : List (Symbol T g.NT)} (hu : NonUnit u)
    (hnn : UnitPair n₁ n₂) (hgu : g.Produces [Symbol.nonterminal n₂] u) :
    g.eliminateUnitRules.Produces [Symbol.nonterminal n₁] u := by
  refine ⟨_, nonUnit_mem_removeUnitRules hgu.rule hu ((computeUnitPairs_iff).2 hnn), ?_⟩
  nth_rewrite 2 [← u.append_nil]
  exact ContextFreeRule.Rewrites.head []

variable [DecidableEq T]

lemma nonUnit_output_mem_eliminateUnitRules {r : ContextFreeRule T g.NT}
    (hrg : r ∈ g.rules) (hro : NonUnit r.output) :
    r ∈ g.eliminateUnitRules.rules := by
  simp only [eliminateUnitRules, removeUnitRules,
    List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList, Prod.exists]
  refine ⟨computeUnitPairRules (r.input, r.input), ⟨r.input, r.input, ?_, rfl⟩,
    nonUnit_mem_computeUnitPairRules hrg hro⟩
  rw [computeUnitPairs_iff]
  exact UnitPair.rfl (input_mem_generators hrg)

lemma derives_to_eliminateUnitRules_derives {u : List (Symbol T g.NT)} {v : List T} {m : ℕ}
    (huv : g.DerivesIn u (v.map Symbol.terminal) m) :
    g.eliminateUnitRules.Derives u (v.map Symbol.terminal):= by
  cases m with
  | zero =>
    cases huv
    rfl
  | succ =>
    obtain ⟨u, hp, hd⟩ := huv.head_of_succ
    obtain ⟨r, hr, hru⟩ := hp
    obtain ⟨p, q, hw, hu⟩ := hru.exists_parts
    by_cases hro : NonUnit r.output
    · apply Produces.trans_derives _ (derives_to_eliminateUnitRules_derives hd)
      exact ⟨r, nonUnit_output_mem_eliminateUnitRules hr hro, hru⟩
    · match hr' : r.output with
      | [Symbol.nonterminal v] =>
        rw [hr'] at hu
        rw [hu] at hd
        obtain ⟨_, _, _, _, m, _, hs, hd1, hd2, hd3, -⟩ := hd.three_split
        obtain ⟨s', s₃, hs', hs'', hs₃⟩ := List.map_eq_append_iff.1 hs
        obtain ⟨s₁, s₂, hs''', hs₁, hs₂⟩ := List.map_eq_append_iff.1 hs''
        rw [← hs₁] at hd1
        rw [← hs₂] at hd2
        rw [← hs₃] at hd3
        rw [hs, hw, ← hs₁, ← hs₂, ← hs₃]
        apply Derives.append_left_trans
        · apply derives_to_eliminateUnitRules_derives hd3
        · apply Derives.append_left_trans _ (derives_to_eliminateUnitRules_derives hd1)
          have hvg : v ∈ g.generators := by
            cases m with
            | zero => cases s₂ <;> cases hd2
            | succ =>
              obtain ⟨w', hp, _⟩ := hd2.head_of_succ
              exact input_mem_generators hp.rule
          obtain ⟨u, w', _, hvu, hp, hw', _, hd2'⟩ := hd2.unitPair_prefix hvg rfl
          apply Produces.trans_derives _ (derives_to_eliminateUnitRules_derives hd2')
          · apply produces_nonUnit_eliminateUnitRules_produces hw' _ hp
            apply UnitPair.trans _ hvu
            unfold unitRule
            rwa [← hr']
      | [Symbol.terminal _] => rw [hr'] at hro; simp at hro
      | [] => rw [hr'] at hro; simp at hro
      | _ :: _ :: _ => rw [hr'] at hro; simp [NonUnit] at hro

theorem eliminateUnitRules_correct :
    g.language = g.eliminateUnitRules.language := by
  apply Set.eq_of_subset_of_subset <;> intro w hw
  · rw [mem_language_iff] at hw
    obtain ⟨n, hn⟩ := (derives_iff_derivesIn _ _ _).1 hw
    exact derives_to_eliminateUnitRules_derives hn
  · rw [mem_language_iff]
    exact eliminateUnitRules_derives_to_derives hw

end EliminateUnitRules

end ContextFreeGrammar
