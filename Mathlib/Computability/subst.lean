
/-
I have proven that context-free languages are closed under substitution.
The main theorem is `IsContextFree.subst`, which states that if a language `L` is context-free and we substitute each terminal `a` with a context-free language `f a`, the resulting language `L.subst f` is also context-free.
To prove this, I first showed that the language of the substitution grammar `g.subst f` is exactly the substitution of the languages of the component grammars (`ContextFreeGrammar.subst_language_eq`).
This required proving two inclusions:
1. `g.language.subst (fun a => (f a).language) ⊆ (g.subst f).language` (`ContextFreeGrammar.subst_language_subset_1`), which was already provided (or assumed proven).
2. `(g.subst f).language ⊆ g.language.subst (fun a => (f a).language)` (`ContextFreeGrammar.subst_language_subset_2`), which I proved by decomposing derivations in the substitution grammar into G-derivations and F-derivations.
I defined `IsContextFree` as the existence of a context-free grammar for the language.
Finally, I used the construction of the substitution grammar to prove `IsContextFree.subst`.

As corrolaries we can show the closure properties of context free languages.
Closure properties of context-free languages derived as corollaries of closure under substitution.
We prove:
1. `IsContextFree.mul` — CFLs are closed under concatenation.
2. `IsContextFree.add` — CFLs are closed under union.
3. `IsContextFree.kstar` — CFLs are closed under Kleene star.
Each is derived from `IsContextFree.subst` (proved in `subst.lean`) by constructing a simple
context-free language and an appropriate substitution function.


This proof follows the structure of section 7.3 in Introduction to Automata Theory, Languages, and Computation (Hopcroft, Motwani, Ullman)
-/


import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic
import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn

open scoped Classical

noncomputable section

#print Language
#print ContextFreeGrammar

/-
The set of terminals used in a context-free grammar `g` is the set of all terminals appearing in the right-hand side of any rule in `g`.
-/
def ContextFreeGrammar.usedTerminals {α : Type} (g : ContextFreeGrammar α) : Finset α :=
  g.rules.sup (fun r => r.output.foldr (fun s acc => match s with | Symbol.terminal a => insert a acc | _ => acc) ∅)

/-
The rules from the substituting grammars `f a` are lifted to the combined non-terminal type `g.NT ⊕ (Σ a, (f a).NT)`. We only include rules for terminals `a` that are actually used in `g`.
-/
def ContextFreeGrammar.subst_rules_f {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) : Finset (ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) :=
  g.usedTerminals.sup (fun a =>
    (f a).rules.map ⟨fun r => ContextFreeRule.mk (Sum.inr ⟨a, r.input⟩) (r.output.map (fun s =>
      match s with
      | Symbol.nonterminal n => Symbol.nonterminal (Sum.inr ⟨a, n⟩)
      | Symbol.terminal b => Symbol.terminal b)), by
        intro r s h;
        cases r ; cases s ; simp +decide at h ⊢;
        exact ⟨ h.1, by simpa using List.map_injective_iff.mpr ( by rintro ( _ | _ ) ( _ | _ ) <;> simp +decide ) h.2 ⟩⟩)

/-
The rules of the original grammar `g` are transformed. Non-terminals `n` become `Sum.inl n`, and terminals `a` are replaced by the start symbol of the substituting grammar `f a`, which is `Sum.inr ⟨a, (f a).initial⟩`.
-/
def ContextFreeGrammar.subst_rules_g {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) : Finset (ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) :=
  g.rules.map ⟨fun r => ContextFreeRule.mk (Sum.inl r.input) (r.output.map (fun s =>
    match s with
    | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)
    | Symbol.terminal a => Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩))), by
      intro r s h;
      cases r ; cases s ; simp +decide at h ⊢;
      refine' ⟨ h.1, List.map_injective_iff.2 _ h.2 ⟩;
      intro s t; cases s <;> cases t <;> simp +decide ;
      tauto⟩

/-
The substitution grammar is constructed by taking the disjoint union of non-terminals and the union of the transformed rules from `g` and the lifted rules from `f`.
-/
def ContextFreeGrammar.subst {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) : ContextFreeGrammar β :=
  ContextFreeGrammar.mk (g.NT ⊕ (Σ a, (f a).NT)) (Sum.inl g.initial) (g.subst_rules_g f ∪ g.subst_rules_f f)

/-
`liftSymbolG` maps symbols from `g` to the substitution grammar. Non-terminals are mapped to the left component of the sum, and terminals are mapped to the start symbol of the corresponding substituting grammar. `liftSymbolF` maps symbols from `f a` to the substitution grammar. Non-terminals are mapped to the right component of the sum, and terminals are kept as terminals.
-/
def ContextFreeGrammar.liftSymbolG {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (s : Symbol α g.NT) : Symbol β (g.NT ⊕ (Σ a, (f a).NT)) :=
  match s with
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)
  | Symbol.terminal a => Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩)

def ContextFreeGrammar.liftSymbolF {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (a : α) (s : Symbol β (f a).NT) : Symbol β (g.NT ⊕ (Σ a, (f a).NT)) :=
  match s with
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inr ⟨a, n⟩)
  | Symbol.terminal b => Symbol.terminal b

/-
If a rule `r` is in `g.rules`, then the rule obtained by lifting `r` (mapping non-terminals to `Sum.inl` and terminals to the start symbol of the corresponding substituting grammar) is in the rules of the substitution grammar `g.subst f`.
-/
theorem ContextFreeGrammar.rule_mem_subst {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (r : ContextFreeRule α g.NT) (hr : r ∈ g.rules) :
    { input := Sum.inl r.input, output := r.output.map (g.liftSymbolG f) } ∈ (g.subst f).rules := by
  unfold ContextFreeGrammar.subst; unfold ContextFreeGrammar.subst_rules_g; aesop;

/-
If `g` produces `v` from `u` in one step, then `g.subst f` produces the lifted version of `v` from the lifted version of `u`.
-/
theorem ContextFreeGrammar.produces_lift_g {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    {u v : List (Symbol α g.NT)} (h : g.Produces u v) :
    (g.subst f).Produces (u.map (g.liftSymbolG f)) (v.map (g.liftSymbolG f)) := by
  -- By definition of `Produces`, there exists an intermediate state where `u` is replaced by `r.output`.
  obtain ⟨r, hr, l, ρ, hu, hv⟩ : ∃ r ∈ g.rules, ∃ l ρ : List (Symbol α g.NT), u = l ++ [Symbol.nonterminal r.input] ++ ρ ∧ v = l ++ r.output ++ ρ := by
    contrapose! h;
    rintro ⟨ ⟩;
    rename_i r hr;
    obtain ⟨l, ρ, hu, hv⟩ : ∃ l ρ : List (Symbol α g.NT), u = l ++ [Symbol.nonterminal r.input] ++ ρ ∧ v = l ++ r.output ++ ρ := by
      have := hr.right
      exact?;
    exact h r hr.1 l ρ hu hv;
  simp +decide [ *, List.map_append ];
  have h_subst : (g.subst f).Produces (g.liftSymbolG f (Symbol.nonterminal r.input) :: List.map (g.liftSymbolG f) ρ) (List.map (g.liftSymbolG f) r.output ++ List.map (g.liftSymbolG f) ρ) := by
    constructor;
    constructor;
    convert ContextFreeGrammar.rule_mem_subst g f r hr using 1;
    constructor;
  exact?

#print ContextFreeGrammar.Produces

#check ContextFreeGrammar.produces_lift_g

/-
If `g` derives `v` from `u`, then `g.subst f` derives the lifted version of `v` from the lifted version of `u`.
-/
theorem ContextFreeGrammar.derives_lift_g {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    {u v : List (Symbol α g.NT)} (h : g.Derives u v) :
    (g.subst f).Derives (u.map (g.liftSymbolG f)) (v.map (g.liftSymbolG f)) := by
      induction' h with u v h ih;
      · constructor;
      · exact Relation.ReflTransGen.tail ‹_› ( by exact? )

/-
If `a` is a used terminal in `g` and `r` is a rule in `f a`, then the lifted rule (where non-terminals are tagged with `a`) is in the substitution grammar.
-/
theorem ContextFreeGrammar.rule_mem_subst_f {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (a : α) (ha : a ∈ g.usedTerminals) (r : ContextFreeRule β (f a).NT) (hr : r ∈ (f a).rules) :
    { input := Sum.inr ⟨a, r.input⟩, output := r.output.map (g.liftSymbolF f a) } ∈ (g.subst f).rules := by
  convert Finset.mem_union_right _ ( Finset.mem_sup.mpr ⟨ a, _, ?_ ⟩ );
  · assumption;
  · exact Finset.mem_map.mpr ⟨ r, hr, rfl ⟩

#check ContextFreeGrammar.language

#print ContextFreeGrammar.Produces
#print ContextFreeGrammar.Derives

#print ContextFreeRule
#print ContextFreeRule.Rewrites

/-
If a rule `r` rewrites `u` to `v`, and we map symbols via `f` such that `r` maps to `r'`, then `r'` rewrites `f(u)` to `f(v)`.
-/
theorem ContextFreeRule.Rewrites.map {T N T' N'} (f : Symbol T N → Symbol T' N')
    (r : ContextFreeRule T N) (r' : ContextFreeRule T' N')
    (u v : List (Symbol T N)) (h : r.Rewrites u v)
    (h_input : f (Symbol.nonterminal r.input) = Symbol.nonterminal r'.input)
    (h_output : r'.output = r.output.map f) :
    r'.Rewrites (u.map f) (v.map f) := by
      induction' h with u v h ih generalizing f r';
      · rw [ List.map_cons, List.map_append ];
        exact h_input.symm ▸ h_output.symm ▸ ( by tauto );
      · cases v <;> cases r <;> simp_all +decide [ ContextFreeRule.Rewrites ];
        · exact?;
        · exact?

/-
If a substituting grammar `f a` produces `v` from `u`, then the substitution grammar `g.subst f` produces the lifted version of `v` from the lifted version of `u`.
-/
theorem ContextFreeGrammar.produces_lift_f {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (a : α) (ha : a ∈ g.usedTerminals)
    {u v : List (Symbol β (f a).NT)} (h : (f a).Produces u v) :
    (g.subst f).Produces (u.map (g.liftSymbolF f a)) (v.map (g.liftSymbolF f a)) := by
      induction' h with u v h ih;
      refine' ⟨ _, _, _ ⟩;
      exact ⟨ Sum.inr ⟨ a, u.input ⟩, u.output.map ( g.liftSymbolF f a ) ⟩;
      · convert rule_mem_subst_f g f a ha u v.1 using 1;
      · apply_rules [ ContextFreeRule.Rewrites.map ];
        exact v.2

/-
If a substituting grammar `f a` derives `v` from `u`, then the substitution grammar `g.subst f` derives the lifted version of `v` from the lifted version of `u`.
-/
theorem ContextFreeGrammar.derives_lift_f {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (a : α) (ha : a ∈ g.usedTerminals)
    {u v : List (Symbol β (f a).NT)} (h : (f a).Derives u v) :
    (g.subst f).Derives (u.map (g.liftSymbolF f a)) (v.map (g.liftSymbolF f a)) := by
      induction h;
      · constructor;
      · exact Relation.ReflTransGen.tail ‹_› ( by exact? )

#print Language

/-
If a grammar derives `w_i` from `s_i` for each `i`, then it derives the concatenation of `w_i`s from the sequence of `s_i`s.
-/
universe u

theorem ContextFreeGrammar.Derives.distrib_prod {T : Type u} {g : ContextFreeGrammar T}
    (S : List (Symbol T g.NT)) (W : List (List (Symbol T g.NT)))
    (h : List.Forall₂ (fun s w => g.Derives [s] w) S W) :
    g.Derives S W.flatten := by
      induction' h with s w S W h ih;
      · constructor;
      · -- By transitivity of derivations, we can combine the two derivations.
        have h_trans : g.Derives (s :: S) (w ++ S) := by
          have h_trans : ∀ {u v : List (Symbol T g.NT)}, g.Derives u v → ∀ {S : List (Symbol T g.NT)}, g.Derives (u ++ S) (v ++ S) := by
            intro u v h S; induction h ; aesop;
            rename_i h₁ h₂ h₃;
            exact h₃.tail ( by exact? );
          exact h_trans h;
        have h_trans : g.Derives (w ++ S) (w ++ W.flatten) := by
          exact?;
        exact?

#check Set.mem_list_prod

/-
If `u` is a list of used terminals and `W` is a list of strings such that each string in `W` is in the language of the corresponding terminal in `u`, then the substitution grammar derives the concatenation of `W` from the lifted terminals of `u`.
-/
lemma ContextFreeGrammar.subst_derives_prod {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u : List α) (W : List (List β))
    (h : List.Forall₂ (fun w a => w ∈ (f a).language) W u)
    (hu : ∀ a ∈ u, a ∈ g.usedTerminals) :
    (g.subst f).Derives (u.map (fun a => g.liftSymbolG f (Symbol.terminal a))) (W.flatten.map Symbol.terminal) := by
      -- Apply the distributive property of derivation over product.
      have h_distrib : (g.subst f).Derives (List.map (fun a => g.liftSymbolG f (Symbol.terminal a)) u) (List.flatten (List.map (fun w => List.map Symbol.terminal w) W)) := by
        apply ContextFreeGrammar.Derives.distrib_prod;
        rw [ List.forall₂_iff_get ] at *;
        simp_all +decide [ ContextFreeGrammar.liftSymbolG ];
        intro i hi; specialize h; have := h.2 i ( by linarith ) hi; simp_all +decide [ ContextFreeGrammar.Derives ] ;
        convert ContextFreeGrammar.derives_lift_f g f ( u[i] ) ( hu _ ( by simp ) ) ( h _ hi ) using 1;
        unfold ContextFreeGrammar.liftSymbolF; aesop;
      grind

/-
If a terminal appears in the output of a rule in the grammar, it is in the set of used terminals.
-/
lemma ContextFreeGrammar.mem_usedTerminals_of_rule_output {α : Type} (g : ContextFreeGrammar α)
    (r : ContextFreeRule α g.NT) (hr : r ∈ g.rules) (a : α) (ha : Symbol.terminal a ∈ r.output) :
    a ∈ g.usedTerminals := by
      -- Since `a` is a terminal in `r.output`, it must be inserted into the set during the foldr.
      have h_insert : ∀ {l : List (Symbol α g.NT)}, Symbol.terminal a ∈ l → a ∈ List.foldr (fun (s : Symbol α g.NT) (acc : Finset α) => match s with | Symbol.terminal a => Insert.insert a acc | x => acc) ∅ l := by
        intro l hl; induction l <;> aesop;
      exact Finset.mem_sup.mpr ⟨ r, hr, h_insert ha ⟩

/-
If a rule rewrites `u` to `v`, then any terminal in `v` is either in `u` or in the output of the rule.
-/
lemma ContextFreeRule.Rewrites.mem_terminal_of_mem_target {T N : Type} (r : ContextFreeRule T N)
    (u v : List (Symbol T N)) (h : r.Rewrites u v) (a : T) (ha : Symbol.terminal a ∈ v) :
    Symbol.terminal a ∈ u ∨ Symbol.terminal a ∈ r.output := by
      have h_rewrite : ∃ x y : List (Symbol T N), u = x ++ [Symbol.nonterminal r.input] ++ y ∧ v = x ++ r.output ++ y := by
        exact?;
      grind +ring

/-
If `g` produces `v` from `u`, then any terminal in `v` is either in `u` or is a used terminal of `g`.
-/
lemma ContextFreeGrammar.terminals_of_produces {α : Type} (g : ContextFreeGrammar α) {u v : List (Symbol α g.NT)} (h : g.Produces u v) :
    ∀ a, Symbol.terminal a ∈ v → Symbol.terminal a ∈ u ∨ a ∈ g.usedTerminals := by
      intro a ha;
      obtain ⟨r, hr⟩ : ∃ r ∈ g.rules, r.Rewrites u v := by
        exact?;
      exact Classical.or_iff_not_imp_left.2 fun h => by have := ContextFreeRule.Rewrites.mem_terminal_of_mem_target r u v hr.2 a ha; exact this.resolve_left h |> fun h => by exact ContextFreeGrammar.mem_usedTerminals_of_rule_output g r hr.1 a h;

/-
If `g` derives `v` from `u`, then any terminal in `v` is either in `u` or is a used terminal of `g`.
-/
lemma ContextFreeGrammar.terminals_of_derives {α : Type} (g : ContextFreeGrammar α) {u v : List (Symbol α g.NT)} (h : g.Derives u v) :
    ∀ a, Symbol.terminal a ∈ v → Symbol.terminal a ∈ u ∨ a ∈ g.usedTerminals := by
      intro a ha
      induction' h with u v huv ih generalizing a;
      · exact Or.inl ha;
      · have := ContextFreeGrammar.terminals_of_produces g ih a ha; aesop;

/-
Any terminal appearing in a string in the language of a context-free grammar must be in the set of used terminals of that grammar.
-/
lemma ContextFreeGrammar.usedTerminals_of_mem_language {α : Type} (g : ContextFreeGrammar α) (w : List α) (hw : w ∈ g.language) :
    ∀ a ∈ w, a ∈ g.usedTerminals := by
      -- By definition of `ContextFreeGrammar.language`, we know that `w ∈ g.language` means `g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal)`.
      have h_deriv : g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) := by
        exact?;
      intro a ha
      have h_term : a ∈ g.usedTerminals := by
        have := ContextFreeGrammar.terminals_of_derives g h_deriv a (by
        exact List.mem_map.mpr ⟨ a, ha, rfl ⟩) ; aesop;
      exact h_term

/-
The substitution of the languages is a subset of the language of the substitution grammar.
-/
theorem ContextFreeGrammar.subst_language_subset_1 {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) :
    ∀ w, w ∈ g.language.subst (fun a => (f a).language) → w ∈ (g.subst f).language := by
      -- Let's unfold the definition of `Language.subst`.
      intro w hw
      obtain ⟨u, hu, hu'⟩ := hw;
      -- By `Language.mem_list_prod_iff_forall2`, there exists `W` such that `w = W.flatten` and `List.Forall₂ (fun w_i a => w_i ∈ (f a).language) W u`.
      obtain ⟨W, hW⟩ := Language.mem_list_prod_iff_forall2 (List.map (fun a => (f a).language) u) w |>.1 hu';
      -- By `ContextFreeGrammar.derives_lift_g`, `(g.subst f).Derives [Symbol.nonterminal (Sum.inl g.initial)] (u.map (fun a => g.liftSymbolG f (Symbol.terminal a)))`.
      have h_derives_lift_g : (g.subst f).Derives [Symbol.nonterminal (Sum.inl g.initial)] (u.map (fun a => g.liftSymbolG f (Symbol.terminal a))) := by
        have h_derives_lift_g : g.Derives [Symbol.nonterminal g.initial] (u.map Symbol.terminal) := by
          exact?;
        convert ContextFreeGrammar.derives_lift_g g f h_derives_lift_g using 1;
        aesop;
      -- By `ContextFreeGrammar.subst_derives_prod`, `(g.subst f).Derives (u.map (fun a => g.liftSymbolG f (Symbol.terminal a))) (W.flatten.map Symbol.terminal)`.
      have h_subst_derives_prod : (g.subst f).Derives (u.map (fun a => g.liftSymbolG f (Symbol.terminal a))) (W.flatten.map Symbol.terminal) := by
        apply ContextFreeGrammar.subst_derives_prod g f u W;
        · rw [ List.forall₂_iff_get ] at * ; aesop;
        · exact?;
      convert h_derives_lift_g.trans h_subst_derives_prod using 1 ; aesop

/-
If a non-terminal symbol appears in a string lifted from `f a`, it must be of the form `Sum.inr ⟨a, n⟩`.
-/
lemma ContextFreeGrammar.mem_liftSymbolF_nonterminal_iff {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (a : α) (u : List (Symbol β (f a).NT)) (x : g.NT ⊕ (Σ a, (f a).NT)) :
    Symbol.nonterminal x ∈ u.map (g.liftSymbolF f a) → ∃ n, x = Sum.inr ⟨a, n⟩ := by
      contrapose!;
      intro hx; induction u <;> simp_all +decide [ List.map ] ;
      cases ‹Symbol β ( f a ).NT› <;> simp_all +decide [ ContextFreeGrammar.liftSymbolF ]

/-
A rule is a G-rule if its input non-terminal comes from G (left side of the sum).
-/
def ContextFreeGrammar.is_G_rule {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (r : ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) : Prop :=
  match r.input with
  | Sum.inl _ => True
  | Sum.inr _ => False

/-
A rule is an F-rule if its input non-terminal comes from one of the F grammars (right side of the sum).
-/
def ContextFreeGrammar.is_F_rule {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (r : ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) : Prop :=
  match r.input with
  | Sum.inl _ => False
  | Sum.inr _ => True

/-
If a rule rewrites a string lifted from `f a`, its input non-terminal must be of the form `Sum.inr ⟨a, n⟩`.
-/
lemma ContextFreeGrammar.input_eq_of_rewrites_lifted {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (a : α) (u : List (Symbol β (f a).NT)) (r : ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) (v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) (h : r.Rewrites (u.map (g.liftSymbolF f a)) v) : ∃ n, r.input = Sum.inr ⟨a, n⟩ := by
  apply ContextFreeGrammar.mem_liftSymbolF_nonterminal_iff;
  swap;
  exact u.filter ( fun s => Symbol.nonterminal ( r.input ) = g.liftSymbolF f a s );
  simp +zetaDelta at *;
  have h_nonterminal : ∀ {u v : List (Symbol β (g.NT ⊕ (a : α) × (f a).NT))}, r.Rewrites u v → ∃ x, x ∈ u ∧ Symbol.nonterminal r.input = x := by
    intros u v h; induction' h with u v h ih; aesop;
    aesop;
  obtain ⟨ x, hx₁, hx₂ ⟩ := h_nonterminal h; use Classical.choose ( List.mem_map.mp hx₁ ) ; have := Classical.choose_spec ( List.mem_map.mp hx₁ ) ; aesop;

/-
If a rule in the substitution grammar has an input non-terminal of the form `Sum.inr ⟨a, n⟩`, then it must be a lifted rule from `f a`.
-/
lemma ContextFreeGrammar.rule_of_input_inr {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (r : ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) (hr : r ∈ (g.subst f).rules)
    (a : α) (n : (f a).NT) (h_input : r.input = Sum.inr ⟨a, n⟩) :
    ∃ r' ∈ (f a).rules, r.output = r'.output.map (g.liftSymbolF f a) := by
      contrapose! hr;
      unfold ContextFreeGrammar.subst;
      rw [ Finset.mem_union ] ; simp +decide [ h_input, hr, ContextFreeGrammar.subst_rules_g, ContextFreeGrammar.subst_rules_f ] ; aesop;

/-
If a rule `r'` rewrites a mapped string `u.map f` to `v'`, and `r'` is the image of `r` under `f` (where `f` is injective), then `v'` is the image of some `v` such that `r` rewrites `u` to `v`.
-/
lemma ContextFreeRule.Rewrites.map_inv {T N T' N'} (f : Symbol T N → Symbol T' N')
    (hf : Function.Injective f)
    (r : ContextFreeRule T N) (r' : ContextFreeRule T' N')
    (u : List (Symbol T N)) (v' : List (Symbol T' N'))
    (h : r'.Rewrites (u.map f) v')
    (h_input : f (Symbol.nonterminal r.input) = Symbol.nonterminal r'.input)
    (h_output : r'.output = r.output.map f) :
    ∃ v, v' = v.map f ∧ r.Rewrites u v := by
      -- Since `u.map f = x' ++ [Symbol.nonterminal r'.input] ++ y'`, we can split `u` into `x ++ [Symbol.nonterminal r.input] ++ y` where `x' = x.map f` and `y' = y.map f`.
      obtain ⟨x, y, hx, hy, hv'⟩ : ∃ x y : List (Symbol T N), u = x ++ [Symbol.nonterminal r.input] ++ y ∧ v' = List.map f x ++ List.map f r.output ++ List.map f y := by
        obtain ⟨x', y', hx', hy', hv'⟩ : ∃ x' y' : List (Symbol T' N'), List.map f u = x' ++ [Symbol.nonterminal r'.input] ++ y' ∧ v' = x' ++ r'.output ++ y' := by
          exact?;
        obtain ⟨x, y, hx, hy, hv'⟩ : ∃ x y : List (Symbol T N), u = x ++ [Symbol.nonterminal r.input] ++ y ∧ List.map f x = x' ∧ List.map f y = y' := by
          -- Since `f` is injective, we can split `u` into `x`, `[Symbol.nonterminal r.input]`, and `y` such that `List.map f x = x'` and `List.map f y = y'` by using the fact that `List.map f` is injective.
          have h_split : ∃ x y : List (Symbol T N), u = x ++ [Symbol.nonterminal r.input] ++ y ∧ List.map f x = x' ∧ List.map f y = y' := by
            have h_split : List.map f u = List.map f (u.take (List.length x')) ++ [Symbol.nonterminal r'.input] ++ List.map f (u.drop (List.length x' + 1)) := by
              convert hx' using 1;
              rw [ ← List.take_append_drop ( List.length x' + 1 ) u, List.map_append ] at * ; aesop
            refine' ⟨ List.take x'.length u, List.drop ( x'.length + 1 ) u, _, _, _ ⟩;
            · refine' List.map_injective_iff.mpr hf _;
              grind;
            · have h_split : List.take (List.length x') (List.map f u) = List.map f (List.take x'.length u) := by
                rw [ List.map_take ];
              rw [ ← h_split, hx', List.take_append_of_le_length ] <;> simp +decide;
            · replace h_split := congr_arg ( fun z => z.drop ( x'.length + 1 ) ) h_split ; simp_all +decide [ List.drop_append ] ;
          exact h_split;
        aesop;
      use x ++ r.output ++ y;
      exact ⟨ by simp +decide, by rw [ hx ] ; exact? ⟩

/-
The function `liftSymbolF` is injective.
-/
lemma ContextFreeGrammar.liftSymbolF_injective {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (a : α) :
    Function.Injective (g.liftSymbolF f a) := by
      -- To prove injectivity, we consider the cases where the input is a non-terminal or a terminal.
      intro x y hxy
      cases x <;> cases y <;> simp +decide [ ContextFreeGrammar.liftSymbolF ] at hxy ⊢;
      · exact hxy;
      · exact hxy

/-
If the substitution grammar produces `v'` from a string of symbols lifted from `f a`, then `v'` must be the lifting of some `v` produced by `f a` from the original string.
-/
lemma ContextFreeGrammar.produces_lift_f_inv {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (a : α)
    (u : List (Symbol β (f a).NT)) (v' : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : (g.subst f).Produces (u.map (g.liftSymbolF f a)) v') :
    ∃ v, v' = v.map (g.liftSymbolF f a) ∧ (f a).Produces u v := by
      revert h;
      -- By definition of `Produces`, if `(g.subst f).Produces (u.map (g.liftSymbolF f a)) v'`, then there exists a sequence of rewrites leading from `u.map (g.liftSymbolF f a)` to `v'`.
      intro hv'
      obtain ⟨r, hr⟩ : ∃ r : ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT)), r ∈ (g.subst f).rules ∧ r.Rewrites (u.map (g.liftSymbolF f a)) v' := by
        cases hv' ; aesop;
      obtain ⟨n, hn⟩ : ∃ n : (f a).NT, r.input = Sum.inr ⟨a, n⟩ := by
        apply ContextFreeGrammar.input_eq_of_rewrites_lifted g f a u r v' hr.2;
      obtain ⟨r', hr', hr''⟩ : ∃ r' ∈ (f a).rules, r.output = r'.output.map (g.liftSymbolF f a) ∧ r'.input = n := by
        have h_rule_in_f : r ∈ g.subst_rules_f f := by
          have h_rule_in_f : r ∈ g.subst_rules_f f ∪ g.subst_rules_g f := by
            convert hr.1 using 1;
            exact Finset.union_comm _ _;
          unfold ContextFreeGrammar.subst_rules_g at h_rule_in_f; aesop;
        unfold ContextFreeGrammar.subst_rules_f at h_rule_in_f; simp_all +decide ;
        obtain ⟨ a', ha', r', hr', rfl ⟩ := h_rule_in_f;
        cases hn ; tauto;
      obtain ⟨v, hv⟩ : ∃ v : List (Symbol β (f a).NT), v' = v.map (g.liftSymbolF f a) ∧ r'.Rewrites u v := by
        apply ContextFreeRule.Rewrites.map_inv (g.liftSymbolF f a) (ContextFreeGrammar.liftSymbolF_injective g f a) r' r u v' hr.2 (by
        aesop) (by
        exact hr''.1);
      exact ⟨ v, hv.1, by exact ⟨ r', hr', hv.2 ⟩ ⟩

/-
If the substitution grammar derives a string of lifted symbols from another string of lifted symbols (where the lifting is for a specific component grammar `f a`), then the component grammar `f a` derives the corresponding unlifted string.
-/
lemma ContextFreeGrammar.derives_of_subst_derives_f {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (a : α) (u v : List (Symbol β (f a).NT)) :
    (g.subst f).Derives (u.map (g.liftSymbolF f a)) (v.map (g.liftSymbolF f a)) → (f a).Derives u v := by
      intro h;
      have h_ind : ∀ w' : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))), (g.subst f).Derives (u.map (g.liftSymbolF f a)) w' → ∃ w : List (Symbol β (f a).NT), w' = w.map (g.liftSymbolF f a) ∧ (f a).Derives u w := by
        intro w' hw';
        induction' hw' with w' hw' ih;
        · exact ⟨ u, rfl, by constructor ⟩;
        · obtain ⟨ w, rfl, hw ⟩ := ‹∃ w, w' = List.map ( g.liftSymbolF f a ) w ∧ ( f a ).Derives u w›;
          obtain ⟨ w', rfl, hw' ⟩ := ContextFreeGrammar.produces_lift_f_inv g f a w _ ‹_›;
          exact ⟨ w', rfl, hw.trans ( Relation.ReflTransGen.single hw' ) ⟩;
      obtain ⟨ w, hw₁, hw₂ ⟩ := h_ind _ h;
      convert hw₂ using 1;
      exact List.map_injective_iff.mpr ( ContextFreeGrammar.liftSymbolF_injective g f a ) hw₁

/-
Definitions of single-step productions using only G-rules or only F-rules.
-/
def ContextFreeGrammar.ProducesG {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) : Prop :=
  ∃ r ∈ g.subst_rules_g f, r.Rewrites u v

def ContextFreeGrammar.ProducesF {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) : Prop :=
  ∃ r ∈ g.subst_rules_f f, r.Rewrites u v

/-
The output of an F-rule does not contain any non-terminals from G (i.e., `Sum.inl` symbols).
-/
lemma ContextFreeGrammar.is_F_rule_output_no_inl {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (r : ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) (hr : r ∈ (g.subst f).rules) :
    g.is_F_rule f r → ∀ s ∈ r.output, ∀ n, s ≠ Symbol.nonterminal (Sum.inl n) := by
      intro hr' s hs n hn; simp_all +decide [ ContextFreeGrammar.is_F_rule ] ;
      unfold ContextFreeGrammar.subst at hr; simp_all +decide [ Finset.mem_union ] ;
      rcases hr with ( hr | hr ) <;> simp_all +decide [ ContextFreeGrammar.subst_rules_g, ContextFreeGrammar.subst_rules_f ];
      · grind +ring;
      · rcases hr with ⟨ a, ha, r', hr', rfl ⟩ ; simp_all +decide [ List.mem_map ] ;
        rcases hs with ⟨ s, hs, hs' ⟩ ; cases s <;> cases hs' ;

/-
Definitions of derivations using only G-rules or only F-rules.
-/
def ContextFreeGrammar.DerivesG {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) : Prop :=
  Relation.ReflTransGen (g.ProducesG f) u v

def ContextFreeGrammar.DerivesF {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) : Prop :=
  Relation.ReflTransGen (g.ProducesF f) u v

/-
If a list can be split as `x ++ mid ++ y` and also as `x' ++ [a] ++ y'`, and `a` is not in `mid`, then the two splits are disjoint (one is strictly before or after the other).
-/
lemma List.split_commute_of_not_mem {α : Type} (x y x' y' : List α) (mid : List α) (a : α)
    (h : x ++ mid ++ y = x' ++ [a] ++ y')
    (h_not_mem : a ∉ mid) :
    (∃ z, x' = x ++ mid ++ z ∧ y = z ++ [a] ++ y') ∨ (∃ z, x = x' ++ [a] ++ z ∧ y' = z ++ mid ++ y) := by
      revert x y x' y' mid a h h_not_mem;
      intros x y x' y' mid a h1 h2; induction' x with x x ih generalizing y x' y' mid a <;> simp_all +decide [ List.append_assoc ] ;
      · cases' List.append_eq_append_iff.mp h1 with h h ; aesop ( simp_config := { singlePass := true } ) ;
        rcases h with ⟨ bs, rfl, h ⟩ ; rcases bs with ( _ | ⟨ b, bs ⟩ ) <;> simp_all +decide [ List.append_assoc ] ;
      · rcases x' with ( _ | ⟨ b, x' ⟩ ) <;> simp_all +decide [ List.append_assoc ]

#print ContextFreeRule.Rewrites

/-
If `r1` rewrites `u` to `v` and `r2` rewrites `v` to `w`, and the input symbol of `r2` does not appear in the output of `r1`, then `r2` can be applied to `u` first, followed by `r1`, to reach the same `w`.
-/
lemma ContextFreeRule.Rewrites.commute_of_not_mem_output {T N : Type}
    (r1 r2 : ContextFreeRule T N)
    (u v w : List (Symbol T N))
    (h1 : r1.Rewrites u v)
    (h2 : r2.Rewrites v w)
    (h_disjoint : Symbol.nonterminal r2.input ∉ r1.output) :
    ∃ v', r2.Rewrites u v' ∧ r1.Rewrites v' w := by
      revert h1 h2 h_disjoint;
      intro h1 h2 h3;
      rw [ ContextFreeRule.rewrites_iff ] at *;
      -- Apply `List.split_commute_of_not_mem` to this equality with `mid = r1.output` and `a = Symbol.nonterminal r2.input`.
      obtain ⟨p1, q1, hp1, hv1⟩ := h1
      obtain ⟨p2, q2, hp2, hw2⟩ := h2
      have h_split : ∃ z, p2 = p1 ++ r1.output ++ z ∧ q1 = z ++ [Symbol.nonterminal r2.input] ++ q2 ∨ p1 = p2 ++ [Symbol.nonterminal r2.input] ++ z ∧ q2 = z ++ r1.output ++ q1 := by
        have h_split : p1 ++ r1.output ++ q1 = p2 ++ [Symbol.nonterminal r2.input] ++ q2 := by
          rw [ ← hv1, hp2 ];
        have := List.split_commute_of_not_mem p1 q1 p2 q2 r1.output ( Symbol.nonterminal r2.input ) h_split h3; aesop;
      rcases h_split with ⟨ z, h | h ⟩ <;> simp_all +decide [ ContextFreeRule.rewrites_iff ];
      · grind;
      · exact ⟨ p2, z ++ Symbol.nonterminal r1.input :: q1, rfl, p2 ++ r2.output ++ z, q1, by simp [List.append_assoc], by simp [List.append_assoc] ⟩

/-
If a derivation step using an F-rule is followed by a step using a G-rule, they can be swapped to perform the G-rule first.
-/
lemma ContextFreeGrammar.produces_F_commutes_G {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u v w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h_F : g.ProducesF f u v)
    (h_G : g.ProducesG f v w) :
    ∃ v', g.ProducesG f u v' ∧ g.ProducesF f v' w := by
      obtain ⟨ rF, hrF, hv ⟩ := h_F
      obtain ⟨ rG, hrG, hw ⟩ := h_G
      have h_comm : Symbol.nonterminal rG.input ∉ rF.output := by
        obtain ⟨ a, ha, hrF ⟩ := Finset.mem_sup.mp hrF;
        obtain ⟨ rF', hrF', hrF ⟩ := Finset.mem_map.mp hrF;
        obtain ⟨ rG', hrG', hrG ⟩ := Finset.mem_map.mp hrG;
        rw [ ← hrG, ← hrF ];
        simp +decide [ List.mem_map ];
        intro x hx; cases x <;> simp +decide ;
      obtain ⟨ v', hv', hw' ⟩ := ContextFreeRule.Rewrites.commute_of_not_mem_output rF rG u v w hv hw h_comm;
      exact ⟨ v', ⟨ rG, hrG, hv' ⟩, ⟨ rF, hrF, hw' ⟩ ⟩

#print ContextFreeGrammar.Derives.distrib_prod

/-
If we have an F-production followed by a sequence of G-productions, we can move the F-production to the end of the sequence.
-/
lemma ContextFreeGrammar.producesF_derivesG_commute {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u v w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h_F : g.ProducesF f u v)
    (h_G : g.DerivesG f v w) :
    ∃ v', g.DerivesG f u v' ∧ g.ProducesF f v' w := by
      induction' h_G with v w h_G ih;
      · exact ⟨ u, by tauto, by tauto ⟩;
      · rcases ‹_› with ⟨ v', hv₁, hv₂ ⟩;
        have := ContextFreeGrammar.produces_F_commutes_G g f v' v w hv₂ ih;
        obtain ⟨ v'', hv₃, hv₄ ⟩ := this; exact ⟨ v'', hv₁.tail hv₃, hv₄ ⟩ ;

/-
If we have a sequence of F-productions followed by a sequence of G-productions, we can move all F-productions to the end.
-/
lemma ContextFreeGrammar.derivesF_derivesG_commute {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u v w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h_F : g.DerivesF f u v)
    (h_G : g.DerivesG f v w) :
    ∃ v', g.DerivesG f u v' ∧ g.DerivesF f v' w := by
      induction' h_F with u v h_F ih generalizing w;
      · exact ⟨ w, h_G, by exact Relation.ReflTransGen.refl ⟩;
      · obtain ⟨ v', hv' ⟩ := ContextFreeGrammar.producesF_derivesG_commute g f u v w ih h_G;
        exact Exists.elim ( ‹∀ w, g.DerivesG f u w → ∃ v', g.DerivesG f _ v' ∧ g.DerivesF f v' w› v' hv'.1 ) fun x hx => ⟨ x, hx.1, hx.2.trans ( Relation.ReflTransGen.single hv'.2 ) ⟩

/-
A production in the substitution grammar is either a G-production or an F-production.
-/
lemma ContextFreeGrammar.produces_subst_iff {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) :
    (g.subst f).Produces u v ↔ g.ProducesG f u v ∨ g.ProducesF f u v := by
      constructor <;> intro h;
      · unfold ContextFreeGrammar.ProducesG ContextFreeGrammar.ProducesF at *;
        obtain ⟨ r, hr, h ⟩ := h;
        unfold ContextFreeGrammar.subst at hr; aesop;
      · cases' h with h h;
        · obtain ⟨ r, hr, h ⟩ := h; exact ⟨ r, by simp [ContextFreeGrammar.subst]; exact Finset.mem_union_left _ hr, h ⟩
        · obtain ⟨ r, hr, h ⟩ := h; exact ⟨ r, by simp [ContextFreeGrammar.subst]; exact Finset.mem_union_right _ hr, h ⟩

/-
Any derivation in the substitution grammar can be rearranged into a sequence of G-rules followed by a sequence of F-rules.
-/
lemma ContextFreeGrammar.derives_split_G_F {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : (g.subst f).Derives u w) :
    ∃ v, g.DerivesG f u v ∧ g.DerivesF f v w := by
      revert h;
      -- Let's unfold the definitions of `Derives` and `DerivesG`.
      intro h
      induction' h using Relation.ReflTransGen.head_induction_on with u w h h ih;
      · exact ⟨ w, by constructor, by constructor ⟩;
      · rename_i h';
        obtain ⟨ v, hv₁, hv₂ ⟩ := ih;
        by_cases h_case : g.ProducesG f u w;
        · exact ⟨ v, Relation.ReflTransGen.single h_case |> Relation.ReflTransGen.trans <| hv₁, hv₂ ⟩;
        · obtain ⟨ v', hv'₁, hv'₂ ⟩ := ContextFreeGrammar.derivesF_derivesG_commute g f u w v (by
          exact Relation.ReflTransGen.single ( by rw [ ContextFreeGrammar.produces_subst_iff ] at h'; aesop )) hv₁;
          exact ⟨ v', hv'₁, hv'₂.trans hv₂ ⟩

/-
If `g` derives `v` from `u`, then the substitution grammar derives the lifted version of `v` from the lifted version of `u` using only G-rules.
-/
lemma ContextFreeGrammar.derivesG_of_derives {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    {u v : List (Symbol α g.NT)} (h : g.Derives u v) :
    g.DerivesG f (u.map (g.liftSymbolG f)) (v.map (g.liftSymbolG f)) := by
      induction h;
      · constructor;
      · rename_i h₁ h₂ h₃;
        obtain ⟨ r, hr, h ⟩ := h₂;
        refine' h₃.trans ( Relation.ReflTransGen.single _ );
        refine' ⟨ _, _, _ ⟩;
        exact ⟨ Sum.inl r.input, r.output.map ( g.liftSymbolG f ) ⟩;
        · exact Finset.mem_map.mpr ⟨ r, hr, rfl ⟩;
        · convert ContextFreeRule.Rewrites.map _ _ _ _ _ h _ _ using 1;
          · rfl;
          · rfl

/-
If `f a` produces `v` from `u`, then the substitution grammar produces the lifted version of `v` from the lifted version of `u` using an F-rule.
-/
lemma ContextFreeGrammar.producesF_lift_f {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (a : α) (ha : a ∈ g.usedTerminals)
    {u v : List (Symbol β (f a).NT)} (h : (f a).Produces u v) :
    g.ProducesF f (u.map (g.liftSymbolF f a)) (v.map (g.liftSymbolF f a)) := by
      obtain ⟨ r, hr, h ⟩ := h;
      refine' ⟨ _, _, _ ⟩;
      exact ⟨ Sum.inr ⟨ a, r.input ⟩, r.output.map ( g.liftSymbolF f a ) ⟩;
      · unfold ContextFreeGrammar.subst_rules_f; aesop;
      · apply_rules [ ContextFreeRule.Rewrites.map ]

/-
If `f a` derives `v` from `u`, then the substitution grammar derives the lifted version of `v` from the lifted version of `u` using only F-rules.
-/
lemma ContextFreeGrammar.derivesF_lift_f {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (a : α) (ha : a ∈ g.usedTerminals)
    {u v : List (Symbol β (f a).NT)} (h : (f a).Derives u v) :
    g.DerivesF f (u.map (g.liftSymbolF f a)) (v.map (g.liftSymbolF f a)) := by
      induction' h with u v h ih;
      · constructor;
      · exact Relation.ReflTransGen.tail ‹_› ( by exact? )

/-
If the substitution grammar produces `v'` from the lifted version of `u` using a G-rule, then `v'` is the lifted version of some `v` produced by `g` from `u`.
-/
lemma ContextFreeGrammar.producesG_unlift {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u : List (Symbol α g.NT)) (v' : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.ProducesG f (u.map (g.liftSymbolG f)) v') :
    ∃ v, v' = v.map (g.liftSymbolG f) ∧ g.Produces u v := by
      obtain ⟨ r, hr, h ⟩ := h;
      unfold ContextFreeGrammar.subst_rules_g at hr; simp_all +decide [ Finset.mem_map ] ;
      rcases hr with ⟨ r, hr, rfl ⟩;
      -- By definition of `Rewrites`, there exists a list `v` such that `v' = v.map (g.liftSymbolG f)` and `u` is rewritten to `v` by `r`.
      obtain ⟨v, hv⟩ : ∃ v, v' = v.map (g.liftSymbolG f) ∧ r.Rewrites u v := by
        apply_rules [ ContextFreeRule.Rewrites.map_inv ];
        intro x y; cases x <;> cases y <;> simp +decide [ ContextFreeGrammar.liftSymbolG ] ;
        tauto;
      exact ⟨ v, hv.1, ⟨ r, hr, hv.2 ⟩ ⟩

/-
If the substitution grammar derives `v'` from the lifted version of `u` using only G-rules, then `v'` is the lifted version of some `v` derived by `g` from `u`.
-/
lemma ContextFreeGrammar.derivesG_unlift {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u : List (Symbol α g.NT)) (v' : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.DerivesG f (u.map (g.liftSymbolG f)) v') :
    ∃ v, v' = v.map (g.liftSymbolG f) ∧ g.Derives u v := by
      induction' h with u v w huv hw ih;
      · exact ⟨ u, rfl, by rfl ⟩;
      · obtain ⟨ v, rfl, hv ⟩ := hw;
        obtain ⟨ v', rfl, hv' ⟩ := ContextFreeGrammar.producesG_unlift g f v _ huv;
        exact ⟨ v', rfl, hv.trans ( Relation.ReflTransGen.single hv' ) ⟩

/-
If the lifted string has no `Sum.inl` non-terminals, then the original string consists only of terminals.
-/
lemma ContextFreeGrammar.is_terminal_of_lift_no_inl {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u : List (Symbol α g.NT))
    (h : ∀ s ∈ u.map (g.liftSymbolG f), ∀ n, s ≠ Symbol.nonterminal (Sum.inl n)) :
    ∀ s ∈ u, ∃ a, s = Symbol.terminal a := by
      contrapose! h;
      rcases h with ⟨ s, hs, hs' ⟩ ; cases s <;> aesop;

/-
If the substitution grammar produces `v'` from the lifted version of `u` using an F-rule, and `u` belongs to component `a`, then `v'` is the lifted version of some `v` produced by `f a` from `u`.
-/
lemma ContextFreeGrammar.producesF_unlift {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (a : α) (u : List (Symbol β (f a).NT)) (v' : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.ProducesF f (u.map (g.liftSymbolF f a)) v') :
    ∃ v, v' = v.map (g.liftSymbolF f a) ∧ (f a).Produces u v := by
      have := @ContextFreeGrammar.produces_lift_f_inv;
      contrapose! this;
      use α, β, g, f, a, u, v';
      refine' ⟨ _, this ⟩;
      -- Since h is a producesF step, it is also a produces step in the substitution grammar.
      apply (ContextFreeGrammar.produces_subst_iff g f (List.map (g.liftSymbolF f a) u) v').mpr;
      exact Or.inr h

/-
If the substitution grammar derives `v'` from the lifted version of `u` using only F-rules, and `u` belongs to component `a`, then `v'` is the lifted version of some `v` derived by `f a` from `u`.
-/
lemma ContextFreeGrammar.derivesF_unlift {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (a : α) (u : List (Symbol β (f a).NT)) (v' : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.DerivesF f (u.map (g.liftSymbolF f a)) v') :
    ∃ v, v' = v.map (g.liftSymbolF f a) ∧ (f a).Derives u v := by
      revert h v';
      intro v' hv';
      -- Apply induction on the derivation `hv'`.
      induction' hv' with u v' hv' ih;
      · exact ⟨ u, rfl, by rfl ⟩;
      · obtain ⟨ v, rfl, hv ⟩ := ‹_›;
        obtain ⟨ w, rfl, hw ⟩ := ContextFreeGrammar.producesF_unlift g f a v v' ih;
        exact ⟨ w, rfl, hv.trans ( Relation.ReflTransGen.single hw ) ⟩

#check ContextFreeGrammar.subst_language_subset_1

/-
If an F-production results in a string with no `Sum.inl` non-terminals, then the input string also had no `Sum.inl` non-terminals.
-/
lemma ContextFreeGrammar.not_mem_inl_of_producesF {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.ProducesF f u v)
    (h_no_inl : ∀ s ∈ v, ∀ n, s ≠ Symbol.nonterminal (Sum.inl n)) :
    ∀ s ∈ u, ∀ n, s ≠ Symbol.nonterminal (Sum.inl n) := by
      obtain ⟨r, hr⟩ := h;
      obtain ⟨x, y, hx, hy⟩ : ∃ x y, u = x ++ [Symbol.nonterminal r.input] ++ y ∧ v = x ++ r.output ++ y := by
        obtain ⟨x, y, hx, hy⟩ : ∃ x y, u = x ++ [Symbol.nonterminal r.input] ++ y ∧ v = x ++ r.output ++ y := by
          have h_rewrite : r.Rewrites u v := hr.right
          obtain ⟨x, y, hx, hy⟩ : ∃ x y, u = x ++ [Symbol.nonterminal r.input] ++ y ∧ v = x ++ r.output ++ y := by
            have h_rewrite : r.Rewrites u v := h_rewrite
            exact?;
          use x, y;
        use x, y;
      cases h : r.input <;> simp_all +decide;
      · unfold ContextFreeGrammar.subst_rules_f at hr; aesop;
      · grind +ring

/-
The substitution of the languages is a subset of the language of the substitution grammar.
-/
theorem ContextFreeGrammar.subst_language_subset_1' {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) :
    ∀ w, w ∈ g.language.subst (fun a => (f a).language) → w ∈ (g.subst f).language := by
      apply_rules [ ContextFreeGrammar.subst_language_subset_1 ]

/-
If an F-derivation results in a string with no `Sum.inl` non-terminals, then the input string also had no `Sum.inl` non-terminals.
-/
lemma ContextFreeGrammar.not_mem_inl_of_derivesF {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.DerivesF f u v)
    (h_no_inl : ∀ s ∈ v, ∀ n, s ≠ Symbol.nonterminal (Sum.inl n)) :
    ∀ s ∈ u, ∀ n, s ≠ Symbol.nonterminal (Sum.inl n) := by
      induction' h with u v h ih;
      · assumption;
      · apply_rules [ ContextFreeGrammar.not_mem_inl_of_producesF ]

/-
If a rule rewrites a concatenation `u ++ v`, the rewrite must occur entirely within `u` or entirely within `v`.
-/
lemma ContextFreeRule.Rewrites.split_append {T N : Type} (r : ContextFreeRule T N)
    (u v w : List (Symbol T N))
    (h : r.Rewrites (u ++ v) w) :
    (∃ u', r.Rewrites u u' ∧ w = u' ++ v) ∨ (∃ v', r.Rewrites v v' ∧ w = u ++ v') := by
      -- By definition of Rewrites, if r.Rewrites (u ++ v) w, then there exists some s such that u ++ v = s ++ [n] ++ t, and w = s ++ r.output ++ t.
      obtain ⟨s, t, hs, ht⟩ : ∃ s t : List (Symbol T N), u ++ v = s ++ [Symbol.nonterminal r.input] ++ t ∧ w = s ++ r.output ++ t := by
        exact?;
      by_cases h_cases : s.length < u.length;
      · -- Since $s$ is a prefix of $u$, we can split $u$ into $s$ and some $u'$.
        obtain ⟨u', hu'⟩ : ∃ u' : List (Symbol T N), u = s ++ [Symbol.nonterminal r.input] ++ u' := by
          rw [ List.append_eq_append_iff ] at hs;
          rcases hs with ( ⟨ as, hs, ht ⟩ | ⟨ bs, rfl, ht ⟩ ) <;> simp_all +decide [ List.append_assoc ];
          replace hs := congr_arg List.length hs ; simp_all +arith +decide;
          cases as <;> simp_all +arith +decide;
        exact Or.inl ⟨ s ++ r.output ++ u', by
          rw [ ContextFreeRule.rewrites_iff ];
          exact ⟨ s, u', hu', rfl ⟩, by
          aesop ⟩;
      · -- Since $s.length \geq u.length$, we have $s = u ++ s'$ for some $s'$.
        obtain ⟨s', hs'⟩ : ∃ s', s = u ++ s' := by
          simp +zetaDelta at *;
          rw [ List.append_eq_append_iff ] at hs ; aesop;
        simp_all +decide [ List.append_assoc ];
        exact Or.inr <| by rw [ ContextFreeRule.rewrites_iff ] ; aesop;

/-
If a context-free grammar produces `w` from `u ++ v`, then the production must occur entirely within `u` or entirely within `v`.
-/
lemma ContextFreeGrammar.Produces.split_append {T : Type u} {g : ContextFreeGrammar T}
    (u v w : List (Symbol T g.NT))
    (h : g.Produces (u ++ v) w) :
    (∃ u', g.Produces u u' ∧ w = u' ++ v) ∨ (∃ v', g.Produces v v' ∧ w = u ++ v') := by
      obtain ⟨ r, hr, h ⟩ := h;
      -- Apply `ContextFreeRule.Rewrites.split_append` to `h`.
      have h_split : (∃ u', r.Rewrites u u' ∧ w = u' ++ v) ∨ (∃ v', r.Rewrites v v' ∧ w = u ++ v') := by
        have h_split : ∀ r : ContextFreeRule T g.NT, ∀ u v w : List (Symbol T g.NT), r.Rewrites (u ++ v) w → (∃ u', r.Rewrites u u' ∧ w = u' ++ v) ∨ (∃ v', r.Rewrites v v' ∧ w = u ++ v') := by
          intros r u v w h;
          induction' u with u hu generalizing v w;
          · aesop;
          · cases h;
            · exact Or.inl ⟨ r.output ++ hu, by tauto, by simp +decide [ List.append_assoc ] ⟩;
            · rename_i s₂ hrs;
              rename_i ih;
              specialize ih v s₂ hrs;
              cases' ih with ih ih <;> simp_all +decide [ ContextFreeRule.Rewrites ];
              obtain ⟨ u', hu', rfl ⟩ := ih; exact Or.inl ⟨ u :: u', by exact? , by simp +decide [ hu' ] ⟩ ;
        exact h_split r u v w h;
      exact Or.imp ( fun ⟨ u', hu', hw ⟩ => ⟨ u', ⟨ r, hr, hu' ⟩, hw ⟩ ) ( fun ⟨ v', hv', hw ⟩ => ⟨ v', ⟨ r, hr, hv' ⟩, hw ⟩ ) h_split

#check ContextFreeGrammar

/-
If a context-free grammar derives `w` from `u ++ v`, then `w` can be split into `u' ++ v'` such that `u` derives `u'` and `v` derives `v'`.
-/
lemma ContextFreeGrammar.Derives.split_append {T : Type u} {g : ContextFreeGrammar T}
    (u v w : List (Symbol T g.NT))
    (h : g.Derives (u ++ v) w) :
    ∃ u' v', g.Derives u u' ∧ g.Derives v v' ∧ w = u' ++ v' := by
      revert h w u v;
      -- By induction on the derivation, we can show that if $u ++ v$ derives $w$, then there exist $u'$ and $v'$ such that $u$ derives $u'$, $v$ derives $v'$, and $w = u' ++ v'$.
      intro u v w h_deriv
      induction' h_deriv with u v w h_deriv ih;
      · exact ⟨ u, v, by constructor, by constructor, rfl ⟩;
      · obtain ⟨ u', v', hu', hv', rfl ⟩ := ih;
        -- By the properties of the derivation relation, we can split the derivation into two parts: one for `u'` and one for `v'`.
        obtain ⟨ u'', v'', hu'', hv'', rfl ⟩ := ContextFreeGrammar.Produces.split_append u' v' v h_deriv;
        · exact ⟨ u'', v', hu'.trans ( Relation.ReflTransGen.single v'' ), hv', rfl ⟩;
        · obtain ⟨ v'', hv'', rfl ⟩ := ‹∃ v'_1, g.Produces v' v'_1 ∧ v = u' ++ v'_1›; exact ⟨ u', v'', hu', hv'.trans ( Relation.ReflTransGen.single hv'' ), rfl ⟩ ;

/-
If `ProducesF` transforms `u ++ v` to `w`, then the transformation occurs entirely within `u` or entirely within `v`.
-/
lemma ContextFreeGrammar.ProducesF.split_append {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u v w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.ProducesF f (u ++ v) w) :
    (∃ u', g.ProducesF f u u' ∧ w = u' ++ v) ∨ (∃ v', g.ProducesF f v v' ∧ w = u ++ v') := by
      obtain ⟨ r, hr, h ⟩ := h;
      have h_split : ∃ u' v', r.Rewrites u u' ∧ w = u' ++ v ∨ r.Rewrites v v' ∧ w = u ++ v' := by
        have := ContextFreeRule.Rewrites.split_append r u v w h; aesop;
      rcases h_split with ⟨ u', v', h | h ⟩ <;> [ exact Or.inl ⟨ u', ⟨ r, hr, h.1 ⟩, h.2 ⟩ ; exact Or.inr ⟨ v', ⟨ r, hr, h.1 ⟩, h.2 ⟩ ]

/-
If `DerivesF` transforms `u ++ v` to `w`, then `w` splits into `u'` and `v'` such that `u` derives `u'` and `v` derives `v'` using only F-rules.
-/
lemma ContextFreeGrammar.DerivesF.split_append {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u v w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.DerivesF f (u ++ v) w) :
    ∃ u' v', g.DerivesF f u u' ∧ g.DerivesF f v v' ∧ w = u' ++ v' := by
      induction' h with u v w h ih;
      · exact ⟨ u, v, by constructor, by constructor, rfl ⟩;
      · obtain ⟨u', v', hu', hv', rfl⟩ := ih;
        obtain ⟨ u'', hu'', hv'' ⟩ := ContextFreeGrammar.ProducesF.split_append g f u' v' v h;
        · exact ⟨ u'', v', hu'.trans ( Relation.ReflTransGen.single hu'' ), hv', hv'' ⟩;
        · obtain ⟨ v'', hv'', rfl ⟩ := ‹∃ v'_1, g.ProducesF f v' v'_1 ∧ v = u' ++ v'_1›; exact ⟨ u', v'', hu', hv'.trans ( Relation.ReflTransGen.single hv'' ), rfl ⟩ ;

/-
If `u` derives `w` using F-rules, then `w` can be split into parts corresponding to each symbol in `u`.
-/
lemma ContextFreeGrammar.DerivesF_distrib {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) (w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.DerivesF f u w) :
    ∃ W, w = W.flatten ∧ List.Forall₂ (fun s w' => g.DerivesF f [s] w') u W := by
      revert h;
      induction' u with s us ih generalizing w;
      · intro hw
        use []
        simp [hw];
        induction hw;
        · rfl;
        · rename_i h₁ h₂ h₃;
          obtain ⟨ r, hr, h ⟩ := h₂;
          cases h ; aesop;
          cases h₃;
      · intro h
        obtain ⟨w1, w2, hw1, hw2, hw⟩ : ∃ w1 w2, g.DerivesF f [s] w1 ∧ g.DerivesF f us w2 ∧ w = w1 ++ w2 := by
          have := h;
          have := this;
          have := @ContextFreeGrammar.DerivesF.split_append α β g f [s] us w this; aesop;
        obtain ⟨ W, rfl, hW ⟩ := ih _ hw2; use w1 :: W; aesop;

/-
If the start symbol of `f a` (lifted) derives a terminal string `w` (lifted) using F-rules, then `w` is in the language of `f a`.
-/
lemma ContextFreeGrammar.DerivesF_terminal_of_lift {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (a : α) (w : List β)
    (h : g.DerivesF f [Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩)] (w.map Symbol.terminal)) :
    w ∈ (f a).language := by
      convert h using 1;
      constructor;
      · exact?;
      · intro hw;
        obtain ⟨ v, hv₁, hv₂ ⟩ := ContextFreeGrammar.derivesF_unlift g f a [Symbol.nonterminal (f a).initial] (List.map Symbol.terminal w) hw;
        have h_eq : ∀ {l1 l2 : List (Symbol β (f a).NT)}, List.map Symbol.terminal w = List.map (g.liftSymbolF f a) l1 → List.map Symbol.terminal w = List.map (g.liftSymbolF f a) l2 → l1 = l2 := by
          intros l1 l2 hl1 hl2;
          have h_eq : List.map (g.liftSymbolF f a) l1 = List.map (g.liftSymbolF f a) l2 := by
            rw [ ← hl1, ← hl2 ];
          exact List.map_injective_iff.mpr ( ContextFreeGrammar.liftSymbolF_injective g f a ) h_eq;
        contrapose! h_eq;
        use v, List.map Symbol.terminal w;
        simp [hv₁];
        exact ⟨ hv₁.symm, fun h => h_eq <| by simpa [ h ] using hv₂ ⟩

/-
If a list of lifted start symbols derives a terminal string using F-rules, then the terminal string is in the product of the languages of the corresponding grammars.
-/
lemma ContextFreeGrammar.mem_subst_of_derivesF {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u : List α) (w : List β)
    (h : g.DerivesF f (u.map (fun a => Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩))) (w.map Symbol.terminal)) :
    w ∈ (u.map (fun a => (f a).language)).prod := by
      obtain ⟨W, hW⟩ : ∃ W : List (List β), w = W.flatten ∧ List.Forall₂ (fun w_part a => g.DerivesF f (List.map (fun a => Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩)) [a]) (List.map Symbol.terminal w_part)) W u := by
        have := @ContextFreeGrammar.DerivesF_distrib α β g f ( List.map ( fun a => Symbol.nonterminal ( Sum.inr ⟨ a, ( f a ).initial ⟩ ) ) u ) ( List.map Symbol.terminal w ) h;
        obtain ⟨ W, hW₁, hW₂ ⟩ := this;
        -- Since `W.flatten` consists of terminals, each element of `W` must consist of terminals.
        have hW_terminals : ∀ w' ∈ W, ∀ s ∈ w', ∃ b : β, s = Symbol.terminal b := by
          have hW_terminals : ∀ w' ∈ W, ∀ s ∈ w', ∃ b : β, s = Symbol.terminal b := by
            intro w' hw' s hs
            have h_terminal : s ∈ List.map Symbol.terminal w := by
              exact hW₁.symm ▸ List.mem_flatten.mpr ⟨ w', hw', hs ⟩
            rw [ List.mem_map ] at h_terminal; obtain ⟨ b, hb, rfl ⟩ := h_terminal; exact ⟨ b, rfl ⟩ ;
          assumption;
        -- Since `W.flatten` consists of terminals, we can replace each element of `W` with its corresponding list of terminals.
        obtain ⟨W', hW'⟩ : ∃ W' : List (List β), W = W'.map (List.map Symbol.terminal) := by
          have hW_terminals : ∀ w' ∈ W, ∃ w'' : List β, w' = w''.map Symbol.terminal := by
            intro w' hw'
            obtain ⟨w'', hw''⟩ : ∃ w'' : List β, w' = w''.map Symbol.terminal := by
              have hW'' : ∀ s ∈ w', ∃ b : β, s = Symbol.terminal b := hW_terminals w' hw'
              have hW'' : ∀ {l : List (Symbol β (g.NT ⊕ (a : α) × (f a).NT))}, (∀ s ∈ l, ∃ b : β, s = Symbol.terminal b) → ∃ l' : List β, l = l'.map Symbol.terminal := by
                intros l hl; induction' l with s l ih <;> simp_all +decide ;
                rcases hl.1 with ⟨ b, rfl ⟩ ; obtain ⟨ l', rfl ⟩ := ih; exact ⟨ b :: l', by simp +decide ⟩ ;
              exact hW'' ‹_›;
            use w'';
          choose! W' hW' using hW_terminals;
          use List.map W' W;
          refine' List.ext_get _ _ <;> simp +decide [ ← hW' ];
        refine' ⟨ W', _, _ ⟩ <;> simp_all +decide [ List.map_map ];
        · exact List.map_injective_iff.mpr ( by aesop_cat ) ( hW₁.trans ( by simp +decide [ List.map_flatten ] ) );
        · exact?;
      rw [ hW.1, Language.mem_list_prod_iff_forall2 ];
      refine' ⟨ W, rfl, _ ⟩;
      have hW_lifted : ∀ {w_part : List β} {a : α}, g.DerivesF f (List.map (fun a => Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩)) [a]) (List.map Symbol.terminal w_part) → w_part ∈ (f a).language := by
        exact?;
      rw [ List.forall₂_iff_get ] at *;
      grind

/-
The language of the substitution grammar is a subset of the substitution of the languages.
-/
theorem ContextFreeGrammar.subst_language_subset_2 {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) :
    ∀ w, w ∈ (g.subst f).language → w ∈ g.language.subst (fun a => (f a).language) := by
      intro w hw;
      obtain ⟨ v, hv ⟩ := ContextFreeGrammar.derives_split_G_F g f [Symbol.nonterminal (Sum.inl g.initial)] ( w.map Symbol.terminal ) hw;
      obtain ⟨ u, hu ⟩ := ContextFreeGrammar.derivesG_unlift g f [Symbol.nonterminal g.initial] v hv.1;
      -- Since `v` has no `Sum.inl` symbols, `u` must consist only of terminals.
      have hu_terminals : ∀ s ∈ u, ∃ a, s = Symbol.terminal a := by
        have hu_terminals : ∀ s ∈ v, ∀ n, s ≠ Symbol.nonterminal (Sum.inl n) := by
          have hv_no_inl : ∀ s ∈ v, ∀ n, s ≠ Symbol.nonterminal (Sum.inl n) := by
            intro s hs n
            have := hv.2
            have := ContextFreeGrammar.not_mem_inl_of_derivesF g f v ( List.map Symbol.terminal w ) this; aesop;
          exact hv_no_inl;
        apply ContextFreeGrammar.is_terminal_of_lift_no_inl g f u;
        aesop;
      -- Since `u` consists only of terminals, we can write `u` as `u_str.map Symbol.terminal` for some `u_str`.
      obtain ⟨ u_str, hu_str ⟩ : ∃ u_str : List α, u = u_str.map Symbol.terminal := by
        have hu_str : ∀ {l : List (Symbol α g.NT)}, (∀ s ∈ l, ∃ a, s = Symbol.terminal a) → ∃ u_str : List α, l = u_str.map Symbol.terminal := by
          intros l hl; induction' l with s l ih;
          · exact ⟨ [ ], rfl ⟩;
          · obtain ⟨ a, rfl ⟩ := hl s ( by simp +decide ) ; obtain ⟨ u_str, hu_str ⟩ := ih fun s hs => hl s ( by simp +decide [ hs ] ) ; exact ⟨ a :: u_str, by simp +decide [ hu_str ] ⟩ ;
        exact hu_str hu_terminals;
      -- Since `v = u_str.map (fun a => Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩))`, we can apply `mem_subst_of_derivesF` to conclude that `w ∈ (u_str.map (fun a => (f a).language)).prod`.
      have hw_prod : w ∈ (u_str.map (fun a => (f a).language)).prod := by
        apply ContextFreeGrammar.mem_subst_of_derivesF g f u_str w;
        aesop;
      exact ⟨ u_str, by aesop ⟩

#check ContextFreeGrammar.subst_language_subset_1

/-
The language of the substitution grammar is exactly the substitution of the languages of the component grammars. This proves that context-free languages are closed under substitution.
-/
theorem ContextFreeGrammar.subst_language_eq {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) :
    (g.subst f).language = g.language.subst (fun a => (f a).language) := by
      ext w;
      constructor;
      · exact?;
      · exact?

/-
A language is context-free if it is the language of some context-free grammar.
-/
def IsContextFree {α : Type u} (L : Language α) : Prop :=
  ∃ g : ContextFreeGrammar α, g.language = L

/-
Context-free languages are closed under substitution.
-/
theorem IsContextFree.subst {α β : Type} (L : Language α) (f : α → Language β)
    (hL : IsContextFree L) (hf : ∀ a, IsContextFree (f a)) :
    IsContextFree (L.subst f) := by
      obtain ⟨ g, hg ⟩ := hL
      obtain ⟨ F, hF ⟩ : ∃ F : α → ContextFreeGrammar β, ∀ a, (F a).language = f a := by
        exact ⟨ fun a => Classical.choose ( hf a ), fun a => Classical.choose_spec ( hf a ) ⟩
      set G := g.subst F
      have hG : G.language = (L.subst f) := by
        rw [ ← hg, ← funext hF, ContextFreeGrammar.subst_language_eq ]
      exact ⟨ G, hG ⟩

/-
-/
/-! ### Substitution equals concatenation -/
/-
PROBLEM
Show that `Language.subst {[false, true]} f = f false * f true` where `Language.subst` is defined
as `{ u | ∃ w ∈ L, u ∈ (w.map f).prod }` and `*` on `Language` is `Set.image2 (· ++ ·)`.
PROVIDED SOLUTION
If `u ∈ Language.subst {[false, true]} f`, then the only `w` is `[false, true]`, so
`u ∈ ([f false, f true]).prod = f false * f true`. Conversely, any `u ∈ f false * f true`
witnesses `w = [false, true]`.
Key: `List.prod_cons`, `List.prod_nil`, `Language.mul_def`, `Language.one_def`.
-/
theorem Language.subst_pair_eq_mul {β : Type} (f : Bool → Language β) :
    Language.subst ({[false, true]} : Language Bool) f = f false * f true := by
      -- To prove equality of sets, we show each set is a subset of the other.
      apply Set.ext
      intro u
      simp [Language.subst, Language.mul_def];
      simp +decide [ List.prod ];
      -- To prove equality of sets, we show each set is a subset of the other. We start with the forward direction.
      apply Iff.intro;
      · simp [Language.mul_def, Language.one_def] at *;
        grind;
      · -- If there exist $a \in f(\text{false})$ and $b \in f(\text{true})$ such that $a ++ b = u$, then $u$ is in the concatenation of $f(\text{false})$ and $f(\text{true})$, which is exactly what the foldr operation computes.
        intro h
        obtain ⟨a, ha, b, hb, hab⟩ := h
        use [false, true]
        simp [ha, hb, hab];
        exact ⟨ rfl, ⟨ a, ha, b, hb, hab ⟩ ⟩
/-! ### Substitution equals union -/
/-
PROBLEM
Show that `Language.subst {[false], [true]} f = f false + f true`.
Here `+` on `Language` is union (by `Language.add_def`).
PROVIDED SOLUTION
Unfold `Language.subst`. We need `{ u | ∃ w ∈ {[false], [true]}, u ∈ (w.map f).prod } = f false + f true`.
Case on `w ∈ {[false], [true]}`: either `w = [false]` giving `u ∈ [f false].prod = f false`
(since `List.prod [x] = x` in a monoid), or `w = [true]` giving `u ∈ f true`.
Thus the set is `f false ∪ f true = f false + f true`.
Key: `Language.add_def`, `List.prod_cons`, `List.prod_nil`.
-/
theorem Language.subst_singletons_eq_add {β : Type} (f : Bool → Language β) :
    Language.subst ({[false], [true]} : Language Bool) f = f false + f true := by
      ext u;
      constructor;
      · rintro ⟨ w, hw, hu ⟩;
        rcases hw with ( rfl | rfl ) <;> simp_all +decide [ List.prod ];
        · exact Or.inl hu;
        · exact Or.inr hu;
      · intro hu
        cases' hu with hu_false hu_true;
        · use [false]
          constructor
          · tauto
          · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
            exact hu_false
        · -- For the case when `u ∈ f true`, we can use the fact that `[true]` is in the input language and `u` is in `f true`.
          use [true]
          constructor
          · tauto
          · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
            exact hu_true
/-! ### Substitution equals Kleene star -/
/-
PROBLEM
Show that `Language.subst (Set.univ : Language Unit) f = KStar.kstar (f ())`.
Here `Language.subst L f = { u | ∃ w ∈ L, u ∈ (w.map f).prod }` and
`Language.kstar_def` says `KStar.kstar l = {x | ∃ L, x = L.flatten ∧ ∀ y ∈ L, y ∈ l}`.
PROVIDED SOLUTION
(→) Given `w ∈ Set.univ` of length `n`, every element of `w` is `()`, so `w.map f = List.replicate n (f ())`.
Then `u ∈ (List.replicate n (f ())).prod = (f ())^n`. Any element of `⋃ₙ (f ())^n` is in `(f ())*`.
Use `Language.kstar_def` and show that membership in `(f ())^n` means `u` is a concatenation of
strings from `f ()`.
(←) Given `u ∈ (f ())*`, by `Language.kstar_def`, there exist `s₁, ..., sₙ ∈ f ()` with `u = s₁ ++ ... ++ sₙ`.
Take `w = List.replicate n ()`. Then `w.map f = List.replicate n (f ())` and
`u ∈ (List.replicate n (f ())).prod`.
-/
theorem Language.subst_univ_unit_eq_kstar {β : Type} (f : Unit → Language β) :
    Language.subst (Set.univ : Language Unit) f = KStar.kstar (f ()) := by
      ext u; exact ⟨by
      rintro ⟨ w, hw, hu ⟩;
      -- By induction on the length of the list `w`, we can show that `u` is in the kstar of `f ()`.
      induction' w with w ih generalizing u;
      · exact ⟨ [ ], by simpa using hu ⟩;
      · rcases hu with ⟨ u₁, hu₁, u₂, hu₂, rfl ⟩;
        rename_i h;
        obtain ⟨ L, hL₁, hL₂ ⟩ := h u₂ ( Set.mem_univ _ ) hu₂;
        exact ⟨ [ u₁ ] ++ L, by aesop ⟩, by
        rintro ⟨ L, rfl, hL ⟩;
        use List.replicate L.length ();
        induction L <;> simp_all +decide [ List.prod ];
        · trivial;
        · exact ⟨ Set.mem_univ _, Set.mem_image2_of_mem hL.1 ( by aesop ) ⟩⟩;
/-! ### Helper: no rewrites on terminal-only strings -/
lemma no_rewrites_of_all_terminal {T N : Type} (r : ContextFreeRule T N) (w : List T) (v : List (Symbol T N)) :
    ¬ r.Rewrites (w.map Symbol.terminal) v := by
  intro h
  rw [ContextFreeRule.rewrites_iff] at h
  obtain ⟨p, q, hp, _⟩ := h
  have : Symbol.nonterminal r.input ∈ w.map Symbol.terminal := by
    rw [hp]; simp
  simp at this
lemma no_produces_of_all_terminal {T : Type} (g : ContextFreeGrammar T) (w : List T) (v : List (Symbol T g.NT)) :
    ¬ g.Produces (w.map Symbol.terminal) v := by
  rintro ⟨r, _, hr⟩
  exact no_rewrites_of_all_terminal r w v hr
lemma derives_of_all_terminal {T : Type} (g : ContextFreeGrammar T) (w : List T) (v : List (Symbol T g.NT)) :
    g.Derives (w.map Symbol.terminal) v → v = w.map Symbol.terminal := by
  intro h
  induction h with
  | refl => rfl
  | tail _ h2 ih => subst ih; exact absurd h2 (no_produces_of_all_terminal g w _)
/-! ### Singleton language is context-free -/
/-
PROBLEM
Show that for any word `w`, the singleton language `{w}` is context-free.
PROVIDED SOLUTION
Construct a CFG `g` with nonterminal type `Unit`, initial = `()`, and a single rule
`() → w.map Symbol.terminal`.
Forward (g.language ⊆ {w}): If `u ∈ g.language`, then `g.Derives [S] (u.map Symbol.terminal)`.
The only rule has input `()` = S. So the first step gives `[S] → w.map Symbol.terminal`.
Since `w.map Symbol.terminal` is all terminals, `derives_of_all_terminal` shows no further
derivation steps are possible. So `u.map Symbol.terminal = w.map Symbol.terminal`, hence `u = w`.
Backward ({w} ⊆ g.language): Apply the single rule to get
`[S] → w.map Symbol.terminal`. This is one derivation step, so `w ∈ g.language`.
Use `no_produces_of_all_terminal` and `derives_of_all_terminal` as helper lemmas.
Use `ContextFreeGrammar.mk Unit () {⟨(), w.map Symbol.terminal⟩}`.
-/
/-
PROBLEM
Prove `isContextFree_singleton`.
PROVIDED SOLUTION
Let `g := ContextFreeGrammar.mk Unit () {⟨(), w.map Symbol.terminal⟩}`.
We show `g.language = {w}` by `Set.ext`.
Backward (`w ∈ g.language`): We need `g.Derives [Symbol.nonterminal ()] (w.map Symbol.terminal)`.
Apply `Relation.ReflTransGen.single`. The single step uses `⟨(), w.map Symbol.terminal⟩` from the
rules (by `Finset.mem_singleton_self`) with `ContextFreeRule.Rewrites.head []`, converting
`r.output ++ [] = r.output` by `simp`.
Forward (`u ∈ g.language → u = w`): We have `g.Derives [Symbol.nonterminal ()] (u.map Symbol.terminal)`.
We need to show this forces `u = w`.
First step: any `g.Produces [Symbol.nonterminal ()] v` forces `v = w.map Symbol.terminal`.
Proof: `rintro ⟨r, hr, hrw⟩; simp [singleton_grammar] at hr; subst hr; cases hrw` with
- `head s`: gives `v = w.map Symbol.terminal ++ s`, but `s = []` since `[S]` has length 1.
- `cons x h`: impossible since `[S]` has no preceding element.
Actually: the only rule has `input = ()`. So from `[S]` (length 1 list with S = ()), the only
Rewrite gives `w.map Symbol.terminal ++ []`.
Then: since `v = w.map Symbol.terminal` is all terminals, `derives_of_all_terminal` gives
`u.map Symbol.terminal = w.map Symbol.terminal`, so `u = w` by `List.map_injective_iff` with
`Symbol.terminal.injective` (i.e., `Symbol.terminal_injective`).
-/
theorem isContextFree_singleton {α : Type} (w : List α) :
    IsContextFree ({w} : Language α) := by
  use ContextFreeGrammar.mk Unit () ({ContextFreeRule.mk () (w.map Symbol.terminal)})
  ext u; constructor
  · intro hd
    rcases Relation.ReflTransGen.cases_head hd with h | ⟨mid, hstep, hrest⟩
    · exfalso
      have : Symbol.nonterminal () ∈ u.map (Symbol.terminal (N := Unit)) := by rw [← h]; simp
      simp [List.mem_map] at this
    · have hmid : mid = w.map Symbol.terminal := by
        obtain ⟨r, hr, hrw⟩ := hstep
        have := Finset.mem_singleton.mp hr; subst this
        cases hrw with | head s => simp | cons x h => cases h
      rw [hmid] at hrest
      have heq := derives_of_all_terminal _ w _ hrest
      show u = w
      exact ((Function.Injective.list_map (f := Symbol.terminal (N := Unit))
        (by intro a b hab; simpa using hab)) heq.symm).symm
  · intro (hu : u = w)
    subst hu
    exact Relation.ReflTransGen.single ⟨⟨(), u.map Symbol.terminal⟩, Finset.mem_singleton_self _,
      by convert ContextFreeRule.Rewrites.head (r := ContextFreeRule.mk () (u.map Symbol.terminal)) [] using 1; simp⟩
/-! ### Finite language {[false], [true]} is context-free -/
/-
PROBLEM
Show that `{[false], [true]} : Language Bool` is context-free.
PROVIDED SOLUTION
Construct a CFG `g` with nonterminal type `Unit`, initial = `()`, and two rules:
`() → [Symbol.terminal false]` and `() → [Symbol.terminal true]`.
Forward: If `u ∈ g.language`, then `g.Derives [S] (u.map Symbol.terminal)`.
Since both rules produce all-terminal strings, after one step we get either
`[Symbol.terminal false]` or `[Symbol.terminal true]`, and no further derivation
is possible (by `no_produces_of_all_terminal`). So `u` is either `[false]` or `[true]`.
Backward: Apply the appropriate rule.
Use `no_produces_of_all_terminal` and `derives_of_all_terminal`.
Use `ContextFreeGrammar.mk Unit () {⟨(), [Symbol.terminal false]⟩, ⟨(), [Symbol.terminal true]⟩}`.
-/
/-
PROBLEM
Prove `isContextFree_pair_bool`.
PROVIDED SOLUTION
Let `g := ContextFreeGrammar.mk Unit () {⟨(), [Symbol.terminal false]⟩, ⟨(), [Symbol.terminal true]⟩}`.
We show `g.language = {[false], [true]}` by `Set.ext`.
Backward: For `[false]`, apply rule `⟨(), [Symbol.terminal false]⟩` (one step).
  For `[true]`, apply rule `⟨(), [Symbol.terminal true]⟩` (one step).
  Both use `Relation.ReflTransGen.single`, `ContextFreeRule.Rewrites.head []`.
Forward: If `u ∈ g.language`, then `g.Derives [Symbol.nonterminal ()] (u.map Symbol.terminal)`.
  Any `g.Produces [Symbol.nonterminal ()] v` uses one of the two rules, giving either
  `v = [Symbol.terminal false]` or `v = [Symbol.terminal true]`.
  Proof: `rintro ⟨r, hr, hrw⟩`, then `hr : r ∈ {rule1, rule2}`, case split.
  In each case, `hrw` has form `Rewrites.head []`, so `v` is determined.
  After one step, `v` is all terminals, so `derives_of_all_terminal` shows
  `u.map Symbol.terminal = v`, hence `u = [false]` or `u = [true]`.
-/
theorem isContextFree_pair_bool :
    IsContextFree ({[false], [true]} : Language Bool) := by
  use ContextFreeGrammar.mk Unit () ({ContextFreeRule.mk () [Symbol.terminal false], ContextFreeRule.mk () [Symbol.terminal true]})
  ext u; constructor
  · intro hd
    rcases Relation.ReflTransGen.cases_head hd with h | ⟨mid, hstep, hrest⟩
    · exfalso
      have : Symbol.nonterminal () ∈ u.map (Symbol.terminal (N := Unit)) := by rw [← h]; simp
      simp [List.mem_map] at this
    · obtain ⟨r, hr, hrw⟩ := hstep
      rcases Finset.mem_insert.mp hr with h1 | h1
      · subst h1
        have hmid : mid = [Symbol.terminal false] := by
          cases hrw with | head s => simp | cons x h => cases h
        rw [hmid] at hrest
        have := derives_of_all_terminal _ [false] _ hrest
        show u ∈ ({[false], [true]} : Set (List Bool))
        left
        exact ((Function.Injective.list_map (f := Symbol.terminal (N := Unit))
          (by intro a b hab; simpa using hab)) this.symm).symm
      · have h2 := Finset.mem_singleton.mp h1; subst h2
        have hmid : mid = [Symbol.terminal true] := by
          cases hrw with | head s => simp | cons x h => cases h
        rw [hmid] at hrest
        have := derives_of_all_terminal _ [true] _ hrest
        show u ∈ ({[false], [true]} : Set (List Bool))
        right
        exact ((Function.Injective.list_map (f := Symbol.terminal (N := Unit))
          (by intro a b hab; simpa using hab)) this.symm).symm
  · intro hu
    rcases hu with rfl | rfl
    · exact Relation.ReflTransGen.single ⟨⟨(), [Symbol.terminal false]⟩,
        Finset.mem_insert_self _ _, ContextFreeRule.Rewrites.head []⟩
    · exact Relation.ReflTransGen.single ⟨⟨(), [Symbol.terminal true]⟩,
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        ContextFreeRule.Rewrites.head []⟩
/-! ### The universal language over Unit is context-free -/
/-
PROBLEM
Show that `Set.univ : Language Unit` (all strings over a single-symbol alphabet) is context-free.
PROVIDED SOLUTION
Construct a grammar `g` with one nonterminal type `Unit`, initial = `()`, and rules:
  `S → ε` (output = [])
  `S → () · S` (output = [Symbol.terminal (), Symbol.nonterminal ()])
Forward: trivial since `Set.univ` contains everything.
Backward: given `w : List Unit`, show `g.Generates (w.map Symbol.terminal)` by induction on `w`.
- Base case `w = []`: apply rule `S → ε` to get `[S] → []`. Done.
- Inductive case `w = () :: w'`:
  Apply rule `S → () · S` to get `[S] → [terminal (), nonterminal ()]`.
  Then by the induction hypothesis, `nonterminal ()` derives `w'.map Symbol.terminal`.
  So overall `[S] → [terminal ()] ++ w'.map Symbol.terminal = w.map Symbol.terminal`.
For the derivation step, use `ContextFreeGrammar.Produces` and `Relation.ReflTransGen`.
Use `ContextFreeGrammar.mk Unit () {⟨(), []⟩, ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}`.
-/
theorem isContextFree_univ_unit : IsContextFree (Set.univ : Language Unit) := by
  -- Let's choose the context-free grammar with the initial symbol `S` and the rules `S → ε` and `S → aS`.
  use ⟨Unit, (), {⟨(), []⟩, ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}⟩;
  refine' Set.eq_univ_of_forall _;
  intro x
  induction' x with x ih;
  · constructor ; tauto;
    constructor ; tauto;
  · rename_i h;
    -- Apply the rule that adds a terminal symbol to the front of the list.
    have h_add_terminal : ∀ (u : List (Symbol Unit Unit)), (ContextFreeGrammar.mk Unit () {⟨(), []⟩, ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}).Derives [Symbol.nonterminal ()] u → (ContextFreeGrammar.mk Unit () {⟨(), []⟩, ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}).Derives [Symbol.nonterminal ()] ([Symbol.terminal ()] ++ u) := by
      intro u hu
      have h_add_terminal : (ContextFreeGrammar.mk Unit () {⟨(), []⟩, ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}).Derives [Symbol.nonterminal ()] ([Symbol.terminal ()] ++ u) := by
        have h_step : (ContextFreeGrammar.mk Unit () {⟨(), []⟩, ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}).Derives [Symbol.nonterminal ()] ([Symbol.terminal (), Symbol.nonterminal ()]) := by
          apply_rules [ Relation.ReflTransGen.single ];
          exact ⟨ _, Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ), by tauto ⟩
        have h_step : (ContextFreeGrammar.mk Unit () {⟨(), []⟩, ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}).Derives ([Symbol.terminal (), Symbol.nonterminal ()]) ([Symbol.terminal ()] ++ u) := by
          have h_step : ∀ (u v : List (Symbol Unit Unit)), (ContextFreeGrammar.mk Unit () {⟨(), []⟩, ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}).Derives u v → (ContextFreeGrammar.mk Unit () {⟨(), []⟩, ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}).Derives ([Symbol.terminal ()] ++ u) ([Symbol.terminal ()] ++ v) := by
            intros u v huv
            induction' huv with u v huv ih;
            · constructor;
            · exact .trans ‹_› ( .single <| by
                obtain ⟨ r, hr, h ⟩ := ih;
                use r;
                simp_all +decide [ ContextFreeRule.Rewrites ];
                exact ContextFreeRule.Rewrites.cons (Symbol.terminal ()) h );
          exact h_step _ _ hu;
        exact Relation.ReflTransGen.trans ‹_› ‹_›;
      exact h_add_terminal;
    convert h_add_terminal _ h using 1
/-! ### Main corollaries -/
/-
PROBLEM
Show: if `L₁` and `L₂` are context-free, then `L₁ * L₂` is context-free.
PROVIDED SOLUTION
Define `f : Bool → Language α` by `f false = L₁`, `f true = L₂`.
The language `{[false, true]}` is context-free by `isContextFree_singleton`.
By `Language.subst_pair_eq_mul`, `Language.subst {[false, true]} f = f false * f true = L₁ * L₂`.
By `IsContextFree.subst`, the result follows.
Use `isContextFree_singleton`, `Language.subst_pair_eq_mul`, `IsContextFree.subst`.
-/
theorem IsContextFree.mul {α : Type} {L₁ L₂ : Language α}
    (h₁ : IsContextFree L₁) (h₂ : IsContextFree L₂) :
    IsContextFree (L₁ * L₂) := by
      have h_subst : IsContextFree (Language.subst ({[false, true]} : Language Bool) (fun b => if b then L₂ else L₁)) := by
        apply IsContextFree.subst;
        · exact isContextFree_singleton [false, true];
        · grind;
      convert h_subst using 1;
      exact Eq.symm ( by simpa using Language.subst_pair_eq_mul ( fun b => if b = true then L₂ else L₁ ) )
/-
PROBLEM
Show: if `L₁` and `L₂` are context-free, then `L₁ + L₂` (= `L₁ ∪ L₂`) is context-free.
PROVIDED SOLUTION
Define `f : Bool → Language α` by `f false = L₁`, `f true = L₂`.
The language `{[false], [true]}` is context-free by `isContextFree_pair_bool`.
By `Language.subst_singletons_eq_add`, `Language.subst {[false], [true]} f = f false + f true = L₁ + L₂`.
By `IsContextFree.subst`, the result follows.
Use `isContextFree_pair_bool`, `Language.subst_singletons_eq_add`, `IsContextFree.subst`.
-/
theorem IsContextFree.add {α : Type} {L₁ L₂ : Language α}
    (h₁ : IsContextFree L₁) (h₂ : IsContextFree L₂) :
    IsContextFree (L₁ + L₂) := by
      obtain ⟨ g₁, hg₁ ⟩ := h₁
      obtain ⟨ g₂, hg₂ ⟩ := h₂
      set f : Bool → Language α := fun b => if b then g₂.language else g₁.language
      have h_subst : IsContextFree (Language.subst ({[false], [true]} : Language Bool) f) := by
        apply_rules [ IsContextFree.subst, isContextFree_pair_bool ];
        exact fun a => by cases a <;> [ exact ⟨ g₁, rfl ⟩ ; exact ⟨ g₂, rfl ⟩ ] ;
      exact (by
      convert h_subst using 1;
      rw [ ← hg₁, ← hg₂, Language.subst_singletons_eq_add ] ; aesop;)
/-
PROBLEM
Show: if `L` is context-free, then `KStar.kstar L` is context-free.
PROVIDED SOLUTION
Define `f : Unit → Language α` by `f () = L`.
The language `Set.univ : Language Unit` is context-free by `isContextFree_univ_unit`.
By `Language.subst_univ_unit_eq_kstar`, `Language.subst Set.univ f = KStar.kstar (f ()) = KStar.kstar L`.
By `IsContextFree.subst`, the result follows.
Use `isContextFree_univ_unit`, `Language.subst_univ_unit_eq_kstar`, `IsContextFree.subst`.
-/
theorem IsContextFree.kstar {α : Type} {L : Language α}
    (h : IsContextFree L) :
    IsContextFree (KStar.kstar L) := by
      convert IsContextFree.subst _ _ _ _;
      convert Language.subst_univ_unit_eq_kstar ( fun _ => L ) |> Eq.symm;
      · exact isContextFree_univ_unit;
      · exact fun _ => h

end
