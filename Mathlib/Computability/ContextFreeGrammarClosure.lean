import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic
import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn

/-!
# Context-Free Languages are Closed Under Substitution

The main theorem is `IsContextFree.subst`: Context-Free Grammars are closed under substitution.

From this follow as simple corollaries that Context Free Gramamrs are closed under
addition (mul), union (add) and Kleene Star.
-/

noncomputable section

namespace ContextFreeGrammar

/--
The set of terminals used in a context-free grammar `g` is the set of all terminals appearing in the
right-hand side of any rule in `g`.
-/
def usedTerminals {α : Type} [DecidableEq α] (g : ContextFreeGrammar α) :
  Finset α :=
  g.rules.sup fun r =>
    (r.output.filterMap fun | .terminal a => some a | _ => none).toFinset

/--
The rules from the substituting grammars `f a` are lifted to the combined non-terminal type
`g.NT ⊕ (Σ a, (f a).NT)`. We only include rules for terminals `a` that are actually used in `g`.
-/
def subst_rules_f {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT] :
    Finset (ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) :=
  g.usedTerminals.sup (fun a =>
    (f a).rules.map ⟨fun r => ContextFreeRule.mk (Sum.inr ⟨a, r.input⟩) (r.output.map (fun s =>
      match s with
      | Symbol.nonterminal n => Symbol.nonterminal (Sum.inr ⟨a, n⟩)
      | Symbol.terminal b => Symbol.terminal b)), by
        intro r s h
        cases r
        cases s
        simp only [ContextFreeRule.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
          at h ⊢
        exact ⟨ h.1, by simpa using List.map_injective_iff.mpr (by
          rintro ( _ | _ ) ( _ | _ ) <;> simp) h.2 ⟩⟩
        )

/--
The rules of the original grammar `g` are transformed. Non-terminals `n` become `Sum.inl n`, and
terminals `a` are replaced by the start symbol of the substituting grammar `f a`, which is
`Sum.inr ⟨a, (f a).initial⟩`.
-/
def subst_rules_g {α β : Type} [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT] :
    Finset (ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) :=
  g.rules.map ⟨fun r => ContextFreeRule.mk (Sum.inl r.input) (r.output.map (fun s =>
    match s with
    | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)
    | Symbol.terminal a => Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩))), by
      intro r s h;
      cases r ; cases s ; simp only [ContextFreeRule.mk.injEq, Sum.inl.injEq] at h ⊢;
      refine ⟨ h.1, List.map_injective_iff.2 ?_ h.2 ⟩;
      intro s t; cases s <;> cases t <;> simp  ;
      tauto⟩

/-
The substitution grammar is constructed by taking the disjoint union of non-terminals and the union
of the transformed rules from `g` and the lifted rules from `f`.
-/
def subst {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT] :
    ContextFreeGrammar β :=
  ContextFreeGrammar.mk (g.NT ⊕ (Σ a, (f a).NT)) (Sum.inl g.initial)
    (g.subst_rules_g f ∪ g.subst_rules_f f)

/-
`liftSymbolG` maps symbols from `g` to the substitution grammar. Non-terminals are mapped to
the left component of the sum, and terminals are mapped to the start symbol of the corresponding
substituting grammar. `liftSymbolF` maps symbols from `f a` to the substitution grammar.
Non-terminals are mapped to the right component of the sum, and terminals are kept as terminals.
-/
def liftSymbolG {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (s : Symbol α g.NT) : Symbol β (g.NT ⊕ (Σ a, (f a).NT)) :=
  match s with
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)
  | Symbol.terminal a => Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩)

def liftSymbolF {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (a : α) (s : Symbol β (f a).NT) : Symbol β (g.NT ⊕ (Σ a, (f a).NT)) :=
  match s with
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inr ⟨a, n⟩)
  | Symbol.terminal b => Symbol.terminal b

/-
If `r` is in `g.rules`, then the lifted rule (non-terminals to `Sum.inl`, terminals to the start
symbol of `f a`) is in the rules of `g.subst f`.
-/
theorem rule_mem_subst {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (r : ContextFreeRule α g.NT) (hr : r ∈ g.rules) :
    { input := Sum.inl r.input, output := r.output.map (g.liftSymbolG f) } ∈ (g.subst f).rules := by
  unfold ContextFreeGrammar.subst; unfold ContextFreeGrammar.subst_rules_g; aesop;

/-
If `g` produces `v` from `u` in one step, then `g.subst f` produces the lifted version of `v`
from the lifted version of `u`.
-/
theorem produces_lift_g {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    {u v : List (Symbol α g.NT)} (h : g.Produces u v) :
    (g.subst f).Produces (u.map (g.liftSymbolG f)) (v.map (g.liftSymbolG f)) := by
  obtain ⟨r, hr, l, ρ, hu, hv⟩ :
      ∃ r ∈ g.rules, ∃ l ρ : List (Symbol α g.NT),
        u = l ++ [Symbol.nonterminal r.input] ++ ρ ∧ v = l ++ r.output ++ ρ := by
    contrapose! h;
    rintro ⟨ ⟩;
    rename_i r hr;
    obtain ⟨l, ρ, hu, hv⟩ :
        ∃ l ρ : List (Symbol α g.NT),
          u = l ++ [Symbol.nonterminal r.input] ++ ρ ∧ v = l ++ r.output ++ ρ := by
      have := hr.right
      exact ContextFreeRule.Rewrites.exists_parts this;
    exact h r hr.1 l ρ hu hv;
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.map_append, List.map_cons,
    hu, hv];
  have h_subst : (g.subst f).Produces
      (g.liftSymbolG f (Symbol.nonterminal r.input) :: List.map (g.liftSymbolG f) ρ)
      (List.map (g.liftSymbolG f) r.output ++ List.map (g.liftSymbolG f) ρ) := by
    constructor;
    constructor;
    · convert ContextFreeGrammar.rule_mem_subst g f r hr using 1;
    · constructor;
  exact Produces.append_left h_subst (List.map (g.liftSymbolG f) l)

/-
If `g` derives `v` from `u`, then `g.subst f` derives the lifted version of `v` from the
lifted version of `u`.
-/
theorem derives_lift_g {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    {u v : List (Symbol α g.NT)} (h : g.Derives u v) :
    (g.subst f).Derives (u.map (g.liftSymbolG f)) (v.map (g.liftSymbolG f)) := by
      induction h with
      | refl => constructor
      | tail _ h_step ih => exact Relation.ReflTransGen.tail ih (produces_lift_g g f h_step)

/-
If `a` is a used terminal in `g` and `r` is a rule in `f a`, then the lifted rule (where
non-terminals are tagged with `a`) is in the substitution grammar.
-/
theorem rule_mem_subst_f {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (a : α) (ha : a ∈ g.usedTerminals) (r : ContextFreeRule β (f a).NT) (hr : r ∈ (f a).rules) :
    { input := Sum.inr ⟨a, r.input⟩,
      output := r.output.map (g.liftSymbolF f a) } ∈ (g.subst f).rules := by
  convert Finset.mem_union_right _ ( Finset.mem_sup.mpr ⟨ a, _, ?_ ⟩ );
  · assumption;
  · exact Finset.mem_map.mpr ⟨ r, hr, rfl ⟩

/-
If a substituting grammar `f a` produces `v` from `u`, then the substitution grammar `g.subst f`
produces the lifted version of `v` from the lifted version of `u`.
-/
theorem produces_lift_f {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (a : α) (ha : a ∈ g.usedTerminals)
    {u v : List (Symbol β (f a).NT)} (h : (f a).Produces u v) :
    (g.subst f).Produces (u.map (g.liftSymbolF f a)) (v.map (g.liftSymbolF f a)) := by
      obtain ⟨r, hr, h_rew⟩ := h;
      refine ⟨ ?_, ?_, ?_ ⟩;
      · exact ⟨ Sum.inr ⟨ a, r.input ⟩, r.output.map ( g.liftSymbolF f a ) ⟩;
      · convert rule_mem_subst_f g f a ha r hr using 1;
      · apply_rules [ ContextFreeRule.Rewrites.map ];

/-
If a substituting grammar `f a` derives `v` from `u`, then the substitution grammar `g.subst f`
derives the lifted version of `v` from the lifted version of `u`.
-/
theorem derives_lift_f {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (a : α) (ha : a ∈ g.usedTerminals)
    {u v : List (Symbol β (f a).NT)} (h : (f a).Derives u v) :
    (g.subst f).Derives (u.map (g.liftSymbolF f a)) (v.map (g.liftSymbolF f a)) := by
      induction h with
      | refl => constructor
      | tail _ h_step ih => exact Relation.ReflTransGen.tail ih (produces_lift_f g f a ha h_step)

/-
If each `W[i]` is in `(f u[i]).language`, then `g.subst f` derives the concatenation of `W`
from the lifted terminals of `u`.
-/
lemma subst_derives_prod {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u : List α) (W : List (List β))
    (h : List.Forall₂ (fun w a => w ∈ (f a).language) W u)
    (hu : ∀ a ∈ u, a ∈ g.usedTerminals) :
    (g.subst f).Derives
        (u.map (fun a => g.liftSymbolG f (Symbol.terminal a)))
        (W.flatten.map Symbol.terminal) := by
      have h_distrib : (g.subst f).Derives
          (List.map (fun a => g.liftSymbolG f (Symbol.terminal a)) u)
          (List.flatten (List.map (fun w => List.map Symbol.terminal w) W)) := by
        apply ContextFreeGrammar.Derives.distrib_prod;
        rw [ List.forall₂_iff_get ] at *;
        simp_all only [List.get_eq_getElem, mem_language_iff, List.length_map, List.getElem_map,
          forall_true_left, true_and];
        intro i hi; specialize h
        have := h.2 i ( by linarith ) hi
        simp_all only [Derives, forall_true_left, true_and]
        convert ContextFreeGrammar.derives_lift_f g f (u[i])
            (hu _ (by simp)) (h _ hi) using 1
        unfold ContextFreeGrammar.liftSymbolF; aesop;
      grind

/-
If a terminal appears in the output of a rule in the grammar, it is in the set of used terminals.
-/
lemma mem_usedTerminals_of_rule_output {α : Type} [DecidableEq α]
    (g : ContextFreeGrammar α)
    (r : ContextFreeRule α g.NT) (hr : r ∈ g.rules) (a : α) (ha : Symbol.terminal a ∈ r.output) :
    a ∈ g.usedTerminals := by
      refine Finset.mem_sup.mpr ⟨r, hr, ?_⟩
      simp only [List.mem_toFinset, List.mem_filterMap]
      exact ⟨Symbol.terminal a, ha, rfl⟩

/-
If `g` produces `v` from `u`, then any terminal in `v` is either in `u` or is a used terminal
of `g`.
-/
lemma terminals_of_produces {α : Type} [DecidableEq α]
    (g : ContextFreeGrammar α) {u v : List (Symbol α g.NT)} (h : g.Produces u v) :
    ∀ a, Symbol.terminal a ∈ v → Symbol.terminal a ∈ u ∨ a ∈ g.usedTerminals := by
      intro a ha;
      obtain ⟨r, hr⟩ : ∃ r ∈ g.rules, r.Rewrites u v := by
        exact Set.inter_nonempty.mp h;
      exact Classical.or_iff_not_imp_left.2 fun h => by
        have := ContextFreeRule.Rewrites.mem_terminal_of_mem_target r u v hr.2 a ha
        exact this.resolve_left h |> fun h =>
          ContextFreeGrammar.mem_usedTerminals_of_rule_output g r hr.1 a h

/-
If `g` derives `v` from `u`, then any terminal in `v` is either in `u` or is a used terminal
of `g`.
-/
lemma terminals_of_derives {α : Type} [DecidableEq α]
    (g : ContextFreeGrammar α) {u v : List (Symbol α g.NT)} (h : g.Derives u v) :
    ∀ a, Symbol.terminal a ∈ v → Symbol.terminal a ∈ u ∨ a ∈ g.usedTerminals := by
      intro a ha
      induction h with
      | refl => exact Or.inl ha
      | tail _ h_step ih =>
        have := ContextFreeGrammar.terminals_of_produces g h_step a ha; aesop;

/-
Any terminal in a string in the language of `g` must be a used terminal of `g`.
-/
lemma usedTerminals_of_mem_language {α : Type} [DecidableEq α]
    (g : ContextFreeGrammar α) (w : List α) (hw : w ∈ g.language) :
    ∀ a ∈ w, a ∈ g.usedTerminals := by
      have h_deriv : g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) := by
        exact (mem_language_iff g w).mp hw;
      intro a ha
      have h_term : a ∈ g.usedTerminals := by
        have := ContextFreeGrammar.terminals_of_derives g h_deriv a (by
        exact List.mem_map.mpr ⟨ a, ha, rfl ⟩) ; aesop;
      exact h_term

/-
The substitution of the languages is a subset of the language of the substitution grammar.
-/
theorem subst_language_subset_1 {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT] :
    ∀ w, w ∈ g.language.subst (fun a => (f a).language) → w ∈ (g.subst f).language := by
      intro w hw
      obtain ⟨u, hu, hu'⟩ := hw;
      obtain ⟨W, hW⟩ :=
        Language.mem_list_prod_iff_forall2 (List.map (fun a => (f a).language) u) w |>.1 hu'
      have h_derives_lift_g : (g.subst f).Derives
          [Symbol.nonterminal (Sum.inl g.initial)]
          (u.map (fun a => g.liftSymbolG f (Symbol.terminal a))) := by
        convert ContextFreeGrammar.derives_lift_g g f hu using 1;
          simp only [List.map_map]; rfl
      have h_subst_derives_prod : (g.subst f).Derives
          (u.map (fun a => g.liftSymbolG f (Symbol.terminal a)))
          (W.flatten.map Symbol.terminal) := by
        apply ContextFreeGrammar.subst_derives_prod g f u W;
        · rw [ List.forall₂_iff_get ] at * ; aesop;
        · exact fun a a_1 ↦ usedTerminals_of_mem_language g u hu a a_1;
      convert h_derives_lift_g.trans h_subst_derives_prod using 1 ; aesop

/-
If a non-terminal symbol appears in a string lifted from `f a`, it must be of the form `Sum.inr ⟨a,
n⟩`.
-/
lemma mem_liftSymbolF_nonterminal_iff {α β : Type}
    (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (a : α) (u : List (Symbol β (f a).NT)) (x : g.NT ⊕ (Σ a, (f a).NT)) :
    Symbol.nonterminal x ∈ u.map (g.liftSymbolF f a) → ∃ n, x = Sum.inr ⟨a, n⟩ := by
      contrapose!;
      intro hx;
      induction u with
      | nil => simp
      | cons hd tl ih =>
        simp_all  [ List.map ];
        cases hd <;> simp_all  [ ContextFreeGrammar.liftSymbolF ]

/-
A rule is a G-rule if its input non-terminal comes from G (left side of the sum).
-/
def is_G_rule {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (r : ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) : Prop :=
  match r.input with
  | Sum.inl _ => True
  | Sum.inr _ => False

/-
A rule is an F-rule if its input non-terminal comes from one of the F grammars (`Sum.inr`).
-/
def is_F_rule {α β : Type} (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (r : ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) : Prop :=
  match r.input with
  | Sum.inl _ => False
  | Sum.inr _ => True

/-
If a rule rewrites a string lifted from `f a`, its input must be of the form `Sum.inr ⟨a, n⟩`.
-/
lemma input_eq_of_rewrites_lifted {α β : Type}
    (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (a : α) (u : List (Symbol β (f a).NT))
    (r : ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT)))
    (v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : r.Rewrites (u.map (g.liftSymbolF f a)) v) : ∃ n, r.input = Sum.inr ⟨a, n⟩ := by
  apply ContextFreeGrammar.mem_liftSymbolF_nonterminal_iff;
  swap;
  · haveI : DecidablePred (fun s => Symbol.nonterminal (r.input) = g.liftSymbolF f a s) :=
      fun s => Classical.dec _
    exact u.filter ( fun s => Symbol.nonterminal ( r.input ) = g.liftSymbolF f a s );
  simp +zetaDelta only [List.mem_map, List.mem_filter, decide_eq_true_eq] at *;
  have h_nonterminal :
      ∀ {u v : List (Symbol β (g.NT ⊕ (a : α) × (f a).NT))},
      r.Rewrites u v → ∃ x, x ∈ u ∧ Symbol.nonterminal r.input = x := by
    intros u v h;
    induction h with
    | head s => aesop
    | cons x h_rec ih => aesop
  obtain ⟨ x, hx₁, hx₂ ⟩ := h_nonterminal h
  use Classical.choose ( List.mem_map.mp hx₁ )
  have := Classical.choose_spec ( List.mem_map.mp hx₁ )
  aesop

/-
If a rule in `g.subst f` has input `Sum.inr ⟨a, n⟩`, it must be a lifted rule from `f a`.
-/
lemma rule_of_input_inr {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (r : ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) (hr : r ∈ (g.subst f).rules)
    (a : α) (n : (f a).NT) (h_input : r.input = Sum.inr ⟨a, n⟩) :
    ∃ r' ∈ (f a).rules, r.output = r'.output.map (g.liftSymbolF f a) := by
      contrapose! hr;
      unfold ContextFreeGrammar.subst;
      rw [ Finset.mem_union ]
      simp  [ ContextFreeGrammar.subst_rules_g, ContextFreeGrammar.subst_rules_f ]
      aesop

/-
The function `liftSymbolF` is injective.
-/
lemma liftSymbolF_injective {α β : Type}
    (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β) (a : α) :
    Function.Injective (g.liftSymbolF f a) := by
      intro x y hxy
      cases x <;> cases y <;> simp_all only [ContextFreeGrammar.liftSymbolF, Symbol.terminal.injEq,
          Symbol.nonterminal.injEq, Sum.inr.injEq, reduceCtorEq, Sigma.mk.injEq, heq_iff_eq];

/-
If `g.subst f` produces `v'` from a lifted string of `f a` symbols, then `v'` is a lifting of
some `v` produced by `f a`.
-/
lemma produces_lift_f_inv {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (a : α)
    (u : List (Symbol β (f a).NT)) (v' : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : (g.subst f).Produces (u.map (g.liftSymbolF f a)) v') :
    ∃ v, v' = v.map (g.liftSymbolF f a) ∧ (f a).Produces u v := by
      obtain ⟨r, hr⟩ :
          ∃ r : ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT)),
            r ∈ (g.subst f).rules ∧ r.Rewrites (u.map (g.liftSymbolF f a)) v' := by
        cases h ; aesop;
      obtain ⟨n, hn⟩ : ∃ n : (f a).NT, r.input = Sum.inr ⟨a, n⟩ := by
        apply ContextFreeGrammar.input_eq_of_rewrites_lifted g f a u r v' hr.2;
      obtain ⟨r', hr', hr''⟩ :
          ∃ r' ∈ (f a).rules,
            r.output = r'.output.map (g.liftSymbolF f a) ∧ r'.input = n := by
        have h_rule_in_f : r ∈ g.subst_rules_f f := by
          have h_rule_in_f : r ∈ g.subst_rules_f f ∪ g.subst_rules_g f := by
            convert hr.1 using 1;
            exact Finset.union_comm _ _;
          unfold ContextFreeGrammar.subst_rules_g at h_rule_in_f; aesop;
        unfold ContextFreeGrammar.subst_rules_f at h_rule_in_f; simp_all  ;
        obtain ⟨ a', ha', r', hr', rfl ⟩ := h_rule_in_f;
        cases hn ; tauto;
      obtain ⟨v, hv⟩ :
          ∃ v : List (Symbol β (f a).NT),
            v' = v.map (g.liftSymbolF f a) ∧ r'.Rewrites u v := by
        apply ContextFreeRule.Rewrites.map_inv (g.liftSymbolF f a)
          (ContextFreeGrammar.liftSymbolF_injective g f a) r' r u v' hr.2 (by
        aesop) (by
        exact hr''.1);
      exact ⟨ v, hv.1, by exact ⟨ r', hr', hv.2 ⟩ ⟩

/-
If the substitution grammar derives one lifted string from another (for component `f a`),
then `f a` derives the corresponding unlifted string.
-/
lemma derives_of_subst_derives_f {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (a : α) (u v : List (Symbol β (f a).NT)) :
    (g.subst f).Derives (u.map (g.liftSymbolF f a)) (v.map (g.liftSymbolF f a)) →
    (f a).Derives u v := by
      intro h;
      have h_ind :
          ∀ w' : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))),
          (g.subst f).Derives (u.map (g.liftSymbolF f a)) w' →
          ∃ w : List (Symbol β (f a).NT),
            w' = w.map (g.liftSymbolF f a) ∧ (f a).Derives u w := by
        intro w' hw';
        induction hw' with
        | refl => exact ⟨ u, rfl, by constructor ⟩
        | tail _ h_step ih =>
          obtain ⟨ w, rfl, hw ⟩ := ih;
          obtain ⟨ w', rfl, hw' ⟩ := ContextFreeGrammar.produces_lift_f_inv g f a w _ h_step;
          exact ⟨ w', rfl, hw.trans ( Relation.ReflTransGen.single hw' ) ⟩;
      obtain ⟨ w, hw₁, hw₂ ⟩ := h_ind _ h;
      convert hw₂ using 1;
      exact List.map_injective_iff.mpr ( ContextFreeGrammar.liftSymbolF_injective g f a ) hw₁

/-
Definitions of single-step productions using only G-rules or only F-rules.
-/
def ProducesG {α β : Type} [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) : Prop :=
  ∃ r ∈ g.subst_rules_g f, r.Rewrites u v

def ProducesF {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) : Prop :=
  ∃ r ∈ g.subst_rules_f f, r.Rewrites u v

/-
The output of an F-rule does not contain any non-terminals from G (i.e., `Sum.inl` symbols).
-/
lemma is_F_rule_output_no_inl {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (r : ContextFreeRule β (g.NT ⊕ (Σ a, (f a).NT))) (hr : r ∈ (g.subst f).rules) :
    g.is_F_rule f r → ∀ s ∈ r.output, ∀ n, s ≠ Symbol.nonterminal (Sum.inl n) := by
      intro hr' s hs n hn; simp_all only [ContextFreeGrammar.is_F_rule] ;
      unfold ContextFreeGrammar.subst at hr; simp_all only [Finset.mem_union] ;
      rcases hr with ( hr | hr ) <;>
        simp_all [ ContextFreeGrammar.subst_rules_g, ContextFreeGrammar.subst_rules_f ]
      · grind +ring;
      · rcases hr with ⟨ a, ha, r', hr', rfl ⟩ ; simp_all  [ List.mem_map ] ;
        rcases hs with ⟨ s, hs, hs' ⟩ ; cases s <;> cases hs' ;

/-
Definitions of derivations using only G-rules or only F-rules.
-/
def DerivesG {α β : Type} [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) : Prop :=
  Relation.ReflTransGen (g.ProducesG f) u v

def DerivesF {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) : Prop :=
  Relation.ReflTransGen (g.ProducesF f) u v

/-
If a derivation step using an F-rule is followed by a step using a G-rule, they can be swapped to
perform the G-rule first.
-/
lemma produces_F_commutes_G {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
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
        simp only [Function.Embedding.coeFn_mk, List.mem_map, not_exists, not_and];
        intro x hx; cases x <;> simp  ;
      obtain ⟨ v', hv', hw' ⟩ :=
        ContextFreeRule.Rewrites.commute_of_not_mem_output rF rG u v w hv hw h_comm
      exact ⟨ v', ⟨ rG, hrG, hv' ⟩, ⟨ rF, hrF, hw' ⟩ ⟩

/-
If we have an F-production followed by a sequence of G-productions, we can move the F-production
to the end of the sequence.
-/
lemma producesF_derivesG_commute {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u v w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h_F : g.ProducesF f u v)
    (h_G : g.DerivesG f v w) :
    ∃ v', g.DerivesG f u v' ∧ g.ProducesF f v' w := by
      induction h_G with
      | refl => exact ⟨ u, by tauto, by tauto ⟩
      | tail _ h_step ih =>
        rcases ih with ⟨ v', hv₁, hv₂ ⟩;
        have := ContextFreeGrammar.produces_F_commutes_G g f _ _ _ hv₂ h_step;
        obtain ⟨ v'', hv₃, hv₄ ⟩ := this; exact ⟨ v'', hv₁.tail hv₃, hv₄ ⟩ ;

/-
If we have a sequence of F-productions followed by a sequence of G-productions, we can move all
F-productions to the end.
-/
lemma derivesF_derivesG_commute {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u v w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h_F : g.DerivesF f u v)
    (h_G : g.DerivesG f v w) :
    ∃ v', g.DerivesG f u v' ∧ g.DerivesF f v' w := by
      induction h_F generalizing w with
      | refl => exact ⟨ w, h_G, by exact Relation.ReflTransGen.refl ⟩
      | tail _ h_step ih =>
        obtain ⟨ v', hv' ⟩ := ContextFreeGrammar.producesF_derivesG_commute g f _ _ w h_step h_G;
        exact Exists.elim ( ih v' hv'.1 ) fun x hx =>
          ⟨ x, hx.1, hx.2.trans ( Relation.ReflTransGen.single hv'.2 ) ⟩

/-
A production in the substitution grammar is either a G-production or an F-production.
-/
lemma produces_subst_iff {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) :
    (g.subst f).Produces u v ↔ g.ProducesG f u v ∨ g.ProducesF f u v := by
      constructor <;> intro h;
      · unfold ContextFreeGrammar.ProducesG ContextFreeGrammar.ProducesF at *;
        obtain ⟨ r, hr, h ⟩ := h;
        unfold ContextFreeGrammar.subst at hr; aesop;
      · rcases h with h | h;
        · obtain ⟨ r, hr, h ⟩ := h
          exact ⟨ r, by simp only [ContextFreeGrammar.subst]; exact Finset.mem_union_left _ hr, h ⟩
        · obtain ⟨ r, hr, h ⟩ := h
          exact ⟨ r, by simp only [ContextFreeGrammar.subst]; exact Finset.mem_union_right _ hr, h ⟩

/-
Any derivation in the substitution grammar can be rearranged into a sequence of G-rules followed by
a sequence of F-rules.
-/
lemma derives_split_G_F {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : (g.subst f).Derives u w) :
    ∃ v, g.DerivesG f u v ∧ g.DerivesF f v w := by
      revert h;
      intro h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨ w, by constructor, by constructor ⟩
      | @head u_start u_mid h' h_rest ih =>
        obtain ⟨ v, hv₁, hv₂ ⟩ := ih;
        rcases Classical.em (g.ProducesG f u_start u_mid) with h_case | h_case;
        · exact ⟨ v,
            Relation.ReflTransGen.single h_case |> Relation.ReflTransGen.trans <| hv₁,
            hv₂ ⟩
        · obtain ⟨ v', hv'₁, hv'₂ ⟩ :=
            ContextFreeGrammar.derivesF_derivesG_commute g f u_start u_mid v
              (Relation.ReflTransGen.single
                (by rw [ ContextFreeGrammar.produces_subst_iff ] at h'; aesop))
              hv₁
          exact ⟨ v', hv'₁, hv'₂.trans hv₂ ⟩

/-
If `g` derives `v` from `u`, then `g.subst f` derives the lifted `v` from the lifted `u` using
only G-rules.
-/
lemma derivesG_of_derives {α β : Type} [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    {u v : List (Symbol α g.NT)} (h : g.Derives u v) :
    g.DerivesG f (u.map (g.liftSymbolG f)) (v.map (g.liftSymbolG f)) := by
      induction h with
      | refl => constructor
      | tail _ h_step ih =>
        obtain ⟨ r, hr, h ⟩ := h_step;
        refine ih.trans ( Relation.ReflTransGen.single ?_ );
        refine ⟨ ?_, ?_, ?_ ⟩;
        · exact ⟨ Sum.inl r.input, r.output.map ( g.liftSymbolG f ) ⟩;
        · exact Finset.mem_map.mpr ⟨ r, hr, rfl ⟩;
        · convert ContextFreeRule.Rewrites.map _ _ _ _ _ h _ _ using 1;
          · rfl;
          · rfl

/-
If `f a` produces `v` from `u`, then `g.subst f` produces the lifted `v` from the lifted `u`
using an F-rule.
-/
lemma producesF_lift_f {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (a : α) (ha : a ∈ g.usedTerminals)
    {u v : List (Symbol β (f a).NT)} (h : (f a).Produces u v) :
    g.ProducesF f (u.map (g.liftSymbolF f a)) (v.map (g.liftSymbolF f a)) := by
      obtain ⟨ r, hr, h ⟩ := h;
      refine ⟨ ?_, ?_, ?_ ⟩;
      · exact ⟨ Sum.inr ⟨ a, r.input ⟩, r.output.map ( g.liftSymbolF f a ) ⟩;
      · unfold ContextFreeGrammar.subst_rules_f; aesop;
      · apply_rules [ ContextFreeRule.Rewrites.map ]

/-
If `f a` derives `v` from `u`, then the substitution grammar derives the lifted version of `v`
from the lifted version of `u` using only F-rules.
-/
lemma derivesF_lift_f {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (a : α) (ha : a ∈ g.usedTerminals)
    {u v : List (Symbol β (f a).NT)} (h : (f a).Derives u v) :
    g.DerivesF f (u.map (g.liftSymbolF f a)) (v.map (g.liftSymbolF f a)) := by
      induction h with
      | refl => constructor
      | tail _ h_step ih => exact Relation.ReflTransGen.tail ih (producesF_lift_f g f a ha h_step)

/-
If `g.subst f` produces `v'` from a lifted `u` via a G-rule, then `v'` is a lifting of some `v`
produced by `g` from `u`.
-/
lemma producesG_unlift {α β : Type} [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u : List (Symbol α g.NT)) (v' : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.ProducesG f (u.map (g.liftSymbolG f)) v') :
    ∃ v, v' = v.map (g.liftSymbolG f) ∧ g.Produces u v := by
      obtain ⟨ r, hr, h ⟩ := h;
      unfold ContextFreeGrammar.subst_rules_g at hr; simp_all only [Finset.mem_map] ;
      rcases hr with ⟨ r, hr, rfl ⟩;
      obtain ⟨v, hv⟩ : ∃ v, v' = v.map (g.liftSymbolG f) ∧ r.Rewrites u v := by
        apply_rules [ ContextFreeRule.Rewrites.map_inv ];
        intro x y; cases x <;> cases y <;> simp  [ ContextFreeGrammar.liftSymbolG ] ; tauto;
      exact ⟨ v, hv.1, ⟨ r, hr, hv.2 ⟩ ⟩

/-
If `g.subst f` derives `v'` from a lifted `u` using only G-rules, then `v'` is a lifting of some
`v` derived by `g` from `u`.
-/
lemma derivesG_unlift {α β : Type} [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u : List (Symbol α g.NT)) (v' : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.DerivesG f (u.map (g.liftSymbolG f)) v') :
    ∃ v, v' = v.map (g.liftSymbolG f) ∧ g.Derives u v := by
      induction h with
      | refl => exact ⟨ u, rfl, by rfl ⟩
      | tail _ h_step ih =>
        obtain ⟨ v, rfl, hv ⟩ := ih;
        obtain ⟨ v', rfl, hv' ⟩ := ContextFreeGrammar.producesG_unlift g f v _ h_step;
        exact ⟨ v', rfl, hv.trans ( Relation.ReflTransGen.single hv' ) ⟩

/-
If the lifted string has no `Sum.inl` non-terminals, then the original string consists only of
terminals.
-/
lemma is_terminal_of_lift_no_inl {α β : Type}
    (g : ContextFreeGrammar α) (f : α → ContextFreeGrammar β)
    (u : List (Symbol α g.NT))
    (h : ∀ s ∈ u.map (g.liftSymbolG f), ∀ n, s ≠ Symbol.nonterminal (Sum.inl n)) :
    ∀ s ∈ u, ∃ a, s = Symbol.terminal a := by
      contrapose! h;
      rcases h with ⟨ s, hs, hs' ⟩ ; cases s <;> aesop;

/-
If `g.subst f` produces `v'` from a lifted `u` (from component `a`) via an F-rule, then `v'` is
a lifting of some `v` produced by `f a` from `u`.
-/
lemma producesF_unlift {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (a : α) (u : List (Symbol β (f a).NT)) (v' : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.ProducesF f (u.map (g.liftSymbolF f a)) v') :
    ∃ v, v' = v.map (g.liftSymbolF f a) ∧ (f a).Produces u v := by
      have h' : (g.subst f).Produces (u.map (g.liftSymbolF f a)) v' := by
        apply (ContextFreeGrammar.produces_subst_iff g f (List.map (g.liftSymbolF f a) u) v').mpr;
        exact Or.inr h
      exact ContextFreeGrammar.produces_lift_f_inv g f a u v' h'

/-
If `g.subst f` derives `v'` from a lifted `u` (from component `a`) using only F-rules, then `v'`
is a lifting of some `v` derived by `f a` from `u`.
-/
lemma derivesF_unlift {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (a : α) (u : List (Symbol β (f a).NT)) (v' : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.DerivesF f (u.map (g.liftSymbolF f a)) v') :
    ∃ v, v' = v.map (g.liftSymbolF f a) ∧ (f a).Derives u v := by
      revert h v';
      intro v' hv';
      induction hv' with
      | refl => exact ⟨ u, rfl, by rfl ⟩
      | tail _ h_step ih =>
        obtain ⟨ v, rfl, hv ⟩ := ih;
        obtain ⟨ w, rfl, hw ⟩ := ContextFreeGrammar.producesF_unlift g f a v _ h_step;
        exact ⟨ w, rfl, hv.trans ( Relation.ReflTransGen.single hw ) ⟩

/-
If an F-production results in a string with no `Sum.inl` non-terminals, then the input string
also had no `Sum.inl` non-terminals.
-/
lemma not_mem_inl_of_producesF {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.ProducesF f u v)
    (h_no_inl : ∀ s ∈ v, ∀ n, s ≠ Symbol.nonterminal (Sum.inl n)) :
    ∀ s ∈ u, ∀ n, s ≠ Symbol.nonterminal (Sum.inl n) := by
      obtain ⟨r, hr⟩ := h;
      obtain ⟨x, y, hx, hy⟩ :
          ∃ x y, u = x ++ [Symbol.nonterminal r.input] ++ y ∧ v = x ++ r.output ++ y := by
        exact ContextFreeRule.Rewrites.exists_parts hr.2;
      cases h : r.input <;> simp_all ;
      · unfold ContextFreeGrammar.subst_rules_f at hr; aesop;
      · grind +ring

/-
The substitution of the languages is a subset of the language of the substitution grammar.
-/
theorem subst_language_subset_1' {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT] :
    ∀ w, w ∈ g.language.subst (fun a => (f a).language) → w ∈ (g.subst f).language := by
      apply_rules [ ContextFreeGrammar.subst_language_subset_1 ]

/-
If an F-derivation results in a string with no `Sum.inl` non-terminals, then the input string also
had no `Sum.inl` non-terminals.
-/
lemma not_mem_inl_of_derivesF {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u v : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.DerivesF f u v)
    (h_no_inl : ∀ s ∈ v, ∀ n, s ≠ Symbol.nonterminal (Sum.inl n)) :
    ∀ s ∈ u, ∀ n, s ≠ Symbol.nonterminal (Sum.inl n) := by
      induction h with
      | refl => assumption
      | tail _ h_step ih => apply_rules [ ContextFreeGrammar.not_mem_inl_of_producesF ]

/-
If `ProducesF` transforms `u ++ v` to `w`, then the transformation occurs entirely within `u`
or entirely within `v`.
-/
lemma ProducesF.split_append {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u v w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.ProducesF f (u ++ v) w) :
    (∃ u', g.ProducesF f u u' ∧ w = u' ++ v) ∨ (∃ v', g.ProducesF f v v' ∧ w = u ++ v') := by
      obtain ⟨ r, hr, h ⟩ := h;
      have h_split : ∃ u' v', r.Rewrites u u' ∧ w = u' ++ v ∨ r.Rewrites v v' ∧ w = u ++ v' := by
        have := ContextFreeRule.Rewrites.split_append r u v w h; aesop;
      rcases h_split with ⟨ u', v', h | h ⟩ <;>
        [ exact Or.inl ⟨ u', ⟨ r, hr, h.1 ⟩, h.2 ⟩
        ; exact Or.inr ⟨ v', ⟨ r, hr, h.1 ⟩, h.2 ⟩ ]

/-
If `DerivesF` transforms `u ++ v` to `w`, then `w` splits into `u'` and `v'` such that `u`
derives `u'` and `v` derives `v'` using only F-rules.
-/
lemma DerivesF.split_append {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u v w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.DerivesF f (u ++ v) w) :
    ∃ u' v', g.DerivesF f u u' ∧ g.DerivesF f v v' ∧ w = u' ++ v' := by
      induction h with
      | refl => exact ⟨ u, v, by constructor, by constructor, rfl ⟩
      | tail _ h_step ih =>
        obtain ⟨u', v', hu', hv', rfl⟩ := ih;
        rcases ContextFreeGrammar.ProducesF.split_append g f u' v' _ h_step
          with ⟨ u'', hu'', rfl ⟩ | ⟨ v'', hv'', rfl ⟩
        · exact ⟨ u'', v', hu'.trans ( Relation.ReflTransGen.single hu'' ), hv', rfl ⟩;
        · exact ⟨ u', v'', hu', hv'.trans ( Relation.ReflTransGen.single hv'' ), rfl ⟩ ;

/-
If `u` derives `w` using F-rules, then `w` can be split into parts corresponding to each symbol
in `u`.
-/
lemma DerivesF_distrib {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT)))) (w : List (Symbol β (g.NT ⊕ (Σ a, (f a).NT))))
    (h : g.DerivesF f u w) :
    ∃ W, w = W.flatten ∧ List.Forall₂ (fun s w' => g.DerivesF f [s] w') u W := by
      revert h;
      induction u generalizing w with
      | nil =>
        intro hw
        use []
        simp only [List.flatten_nil, List.forall₂_nil_right_iff, and_true];
        induction hw with
        | refl => rfl
        | tail _ h_step _ =>
          obtain ⟨ r, hr, h ⟩ := h_step;
          cases h; · aesop;
          rename_i h; cases h
      | cons s us ih =>
        intro h
        obtain ⟨w1, w2, hw1, hw2, hw⟩ :
            ∃ w1 w2, g.DerivesF f [s] w1 ∧ g.DerivesF f us w2 ∧ w = w1 ++ w2 := by
          have := @ContextFreeGrammar.DerivesF.split_append α β _ _ g _ f _ [s] us w h; aesop;
        obtain ⟨ W, rfl, hW ⟩ := ih _ hw2; use w1 :: W; aesop;

/-
If the lifted start symbol of `f a` F-derives a lifted terminal string `w`,
then `w ∈ (f a).language`.
-/
lemma DerivesF_terminal_of_lift {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (a : α) (w : List β)
    (h : g.DerivesF f [Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩)] (w.map Symbol.terminal)) :
    w ∈ (f a).language := by
      convert h using 1;
      constructor;
      · exact fun a_1 ↦ ((fun a ↦ h) ∘ f) a;
      · intro hw;
        obtain ⟨ v, hv₁, hv₂ ⟩ :=
          ContextFreeGrammar.derivesF_unlift g f a
            [Symbol.nonterminal (f a).initial] (List.map Symbol.terminal w) hw
        have h_eq :
            ∀ {l1 l2 : List (Symbol β (f a).NT)},
              List.map Symbol.terminal w = List.map (g.liftSymbolF f a) l1 →
              List.map Symbol.terminal w = List.map (g.liftSymbolF f a) l2 → l1 = l2 := by
          intros l1 l2 hl1 hl2;
          have h_eq : List.map (g.liftSymbolF f a) l1 = List.map (g.liftSymbolF f a) l2 := by
            rw [ ← hl1, ← hl2 ];
          exact List.map_injective_iff.mpr ( ContextFreeGrammar.liftSymbolF_injective g f a ) h_eq;
        contrapose! h_eq;
        use v, List.map Symbol.terminal w;
        simp only [hv₁, List.map_map, ne_eq, true_and];
        exact ⟨ hv₁.symm, fun h => h_eq <| by simpa [ h ] using hv₂ ⟩

/-
If lifted start symbols of `u` F-derive a terminal string `w`, then `w` is in the product of the
languages `(f a).language` for each `a ∈ u`.
-/
lemma mem_subst_of_derivesF {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT]
    (u : List α) (w : List β)
    (h : g.DerivesF f
        (u.map (fun a => Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩)))
        (w.map Symbol.terminal)) :
    w ∈ (u.map (fun a => (f a).language)).prod := by
      obtain ⟨W, hW⟩ :
          ∃ W : List (List β), w = W.flatten ∧
          List.Forall₂ (fun w_part a =>
            g.DerivesF f
              (List.map (fun a => Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩)) [a])
              (List.map Symbol.terminal w_part)) W u := by
        have := @ContextFreeGrammar.DerivesF_distrib α β _ _ g _ f _
          ( List.map ( fun a => Symbol.nonterminal ( Sum.inr ⟨ a, ( f a ).initial ⟩ ) ) u )
          ( List.map Symbol.terminal w ) h
        obtain ⟨ W, hW₁, hW₂ ⟩ := this;
        have hW_terminals : ∀ w' ∈ W, ∀ s ∈ w', ∃ b : β, s = Symbol.terminal b := by
          intro w' hw' s hs
          have h_terminal : s ∈ List.map Symbol.terminal w :=
            hW₁.symm ▸ List.mem_flatten.mpr ⟨ w', hw', hs ⟩
          rw [ List.mem_map ] at h_terminal
          obtain ⟨ b, hb, rfl ⟩ := h_terminal
          exact ⟨ b, rfl ⟩
        have hW_each : ∀ w' ∈ W, ∃ w'' : List β, w' = w''.map Symbol.terminal := by
          intro w' hw'; have hall := hW_terminals w' hw'; clear hw'
          induction w' with
          | nil => exact ⟨ [], rfl ⟩
          | cons hd tl ih =>
            rcases hall hd List.mem_cons_self with ⟨ b, rfl ⟩
            obtain ⟨ l', rfl ⟩ := ih (fun s hs => hall s (List.mem_cons_of_mem _ hs))
            exact ⟨ b :: l', by simp ⟩
        obtain ⟨W', hW'⟩ : ∃ W' : List (List β), W = W'.map (List.map Symbol.terminal) := by
          choose! W' hW' using hW_each;
          use List.map W' W;
          refine List.ext_get ?_ ?_ <;> simp  [ ← hW' ];
        refine ⟨ W', ?_, ?_ ⟩ <;> simp_all only [List.forall₂_map_right_iff,
          List.forall₂_map_left_iff, List.mem_map, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, Symbol.terminal.injEq, exists_eq', implies_true,
          exists_apply_eq_apply'];
        · exact List.map_injective_iff.mpr ( by aesop_cat )
            ( hW₁.trans ( by simp [ List.map_flatten ] ) )
        · exact List.Forall₂.flip hW₂;
      rw [ hW.1, Language.mem_list_prod_iff_forall2 ];
      refine ⟨ W, rfl, ?_ ⟩;
      have hW_lifted :
          ∀ {w_part : List β} {a : α},
          g.DerivesF f
            (List.map (fun a => Symbol.nonterminal (Sum.inr ⟨a, (f a).initial⟩)) [a])
            (List.map Symbol.terminal w_part) → w_part ∈ (f a).language := by
        exact fun {w_part} {a} a_1 ↦ DerivesF_terminal_of_lift g f a w_part a_1;
      rw [ List.forall₂_iff_get ] at *;
      grind

/-
The language of the substitution grammar is a subset of the substitution of the languages.
-/
theorem subst_language_subset_2 {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT] :
    ∀ w, w ∈ (g.subst f).language → w ∈ g.language.subst (fun a => (f a).language) := by
      intro w hw;
      obtain ⟨ v, hv ⟩ := ContextFreeGrammar.derives_split_G_F g f
        [Symbol.nonterminal (Sum.inl g.initial)] ( w.map Symbol.terminal ) hw
      obtain ⟨ u, hu ⟩ :=
        ContextFreeGrammar.derivesG_unlift g f [Symbol.nonterminal g.initial] v hv.1
      have hu_terminals : ∀ s ∈ u, ∃ a, s = Symbol.terminal a := by
        apply ContextFreeGrammar.is_terminal_of_lift_no_inl g f u;
        intro s hs n
        have := ContextFreeGrammar.not_mem_inl_of_derivesF g f v
          ( List.map Symbol.terminal w ) hv.2
        aesop
      obtain ⟨ u_str, hu_str ⟩ : ∃ u_str : List α, u = u_str.map Symbol.terminal := by
        have hu_str :
            ∀ {l : List (Symbol α g.NT)},
            (∀ s ∈ l, ∃ a, s = Symbol.terminal a) →
            ∃ u_str : List α, l = u_str.map Symbol.terminal := by
          intros l hl;
          induction l with
          | nil => exact ⟨ [ ], rfl ⟩
          | cons hd tl ih =>
            obtain ⟨ a, rfl ⟩ := hl hd ( by simp )
            obtain ⟨ u_str, hu_str ⟩ := ih fun s hs => hl s ( by simp [ hs ] )
            exact ⟨ a :: u_str, by simp [ hu_str ] ⟩
        exact hu_str hu_terminals;
      have hw_prod : w ∈ (u_str.map (fun a => (f a).language)).prod := by
        apply ContextFreeGrammar.mem_subst_of_derivesF g f u_str w;
        aesop;
      exact ⟨ u_str, by aesop ⟩

/-
The language of the substitution grammar is exactly the substitution of the languages of the
component grammars. This proves that context-free languages are closed under substitution.
-/
theorem subst_language_eq {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : ContextFreeGrammar α) [DecidableEq g.NT]
    (f : α → ContextFreeGrammar β) [∀ a, DecidableEq (f a).NT] :
    (g.subst f).language = g.language.subst (fun a => (f a).language) := by
      ext w;
      constructor;
      · exact fun a ↦ subst_language_subset_2 g f w a;
      · exact fun a ↦ subst_language_subset_1 g f w a

end ContextFreeGrammar

/-- A language is context-free if it is the language of some context-free grammar. -/
def IsContextFree {α : Type} (L : Language α) : Prop :=
  ∃ g : ContextFreeGrammar α, g.language = L

/-- Context-free languages are closed under substitution. -/
theorem IsContextFree.subst {α β : Type}
    (L : Language α) (f : α → Language β)
    (hL : IsContextFree L) (hf : ∀ a, IsContextFree (f a)) :
    IsContextFree (L.subst f) := by
      obtain ⟨ g, hg ⟩ := hL
      obtain ⟨ F, hF ⟩ : ∃ F : α → ContextFreeGrammar β, ∀ a, (F a).language = f a := by
        exact ⟨ fun a => Classical.choose ( hf a ), fun a => Classical.choose_spec ( hf a ) ⟩
      classical
      exact ⟨ g.subst F, by rw [ ← hg, ← funext hF, ContextFreeGrammar.subst_language_eq ] ⟩

/-! ### Singleton language is context-free -/
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
      have heq := ContextFreeGrammar.derives_of_all_terminal _ w _ hrest
      change u = w
      exact ((Function.Injective.list_map (f := Symbol.terminal (N := Unit))
        (by intro a b hab; simpa using hab)) heq.symm).symm
  · intro (hu : u = w)
    subst hu
    exact Relation.ReflTransGen.single ⟨⟨(), u.map Symbol.terminal⟩, Finset.mem_singleton_self _,
      by convert ContextFreeRule.Rewrites.head
           (r := ContextFreeRule.mk () (u.map Symbol.terminal)) [] using 1; simp⟩
/-! ### Finite language {[false], [true]} is context-free -/
theorem isContextFree_pair_bool :
    IsContextFree ({[false], [true]} : Language Bool) := by
  use ContextFreeGrammar.mk Unit () ({ContextFreeRule.mk () [Symbol.terminal false],
    ContextFreeRule.mk () [Symbol.terminal true]})
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
        have := ContextFreeGrammar.derives_of_all_terminal _ [false] _ hrest
        change u ∈ ({[false], [true]} : Set (List Bool))
        left
        exact ((Function.Injective.list_map (f := Symbol.terminal (N := Unit))
          (by intro a b hab; simpa using hab)) this.symm).symm
      · have h2 := Finset.mem_singleton.mp h1; subst h2
        have hmid : mid = [Symbol.terminal true] := by
          cases hrw with | head s => simp | cons x h => cases h
        rw [hmid] at hrest
        have := ContextFreeGrammar.derives_of_all_terminal _ [true] _ hrest
        change u ∈ ({[false], [true]} : Set (List Bool))
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
theorem isContextFree_univ_unit : IsContextFree (Set.univ : Language Unit) := by
  use ⟨Unit, (), {⟨(), []⟩, ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}⟩;
  refine Set.eq_univ_of_forall ?_;
  intro x
  induction x with
  | nil =>
    constructor
    · tauto
    · constructor
      tauto
  | cons x ih =>
    rename_i h;
    have h_add_terminal : ∀ (u : List (Symbol Unit Unit)),
        (ContextFreeGrammar.mk Unit () {⟨(), []⟩,
          ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}).Derives [Symbol.nonterminal ()] u →
        (ContextFreeGrammar.mk Unit () {⟨(), []⟩,
          ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}).Derives
          [Symbol.nonterminal ()] ([Symbol.terminal ()] ++ u) := by
      intro u hu
      have h_step1 : (ContextFreeGrammar.mk Unit () {⟨(), []⟩,
          ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}).Derives
          [Symbol.nonterminal ()] ([Symbol.terminal (), Symbol.nonterminal ()]) := by
        apply_rules [ Relation.ReflTransGen.single ];
        exact ⟨ _, Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ), by tauto ⟩
      have h_prepend : ∀ (u v : List (Symbol Unit Unit)),
          (ContextFreeGrammar.mk Unit () {⟨(), []⟩,
            ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}).Derives u v →
          (ContextFreeGrammar.mk Unit () {⟨(), []⟩,
            ⟨(), [Symbol.terminal (), Symbol.nonterminal ()]⟩}).Derives
            ([Symbol.terminal ()] ++ u) ([Symbol.terminal ()] ++ v) := by
        intros u v huv
        induction huv with
        | refl => constructor;
        | tail _ ih => exact .trans ‹_› ( .single <| by
            obtain ⟨ r, hr, h ⟩ := ih; use r;
            simp_all only [List.cons_append, List.nil_append, Finset.mem_insert,
              Finset.mem_singleton, true_and];
            exact ContextFreeRule.Rewrites.cons (Symbol.terminal ()) h );
      exact Relation.ReflTransGen.trans h_step1 (h_prepend _ _ hu);
    convert h_add_terminal _ h using 1

/-! ### Main corollaries: Closure under addition, union, and Kleene star -/
theorem IsContextFree.mul {α : Type} {L₁ L₂ : Language α}
    (h₁ : IsContextFree L₁) (h₂ : IsContextFree L₂) :
    IsContextFree (L₁ * L₂) := by
      have h_subst : IsContextFree
          (Language.subst ({[false, true]} : Language Bool) (fun b => if b then L₂ else L₁)) := by
        classical
        apply IsContextFree.subst;
        · exact isContextFree_singleton [false, true];
        · grind;
      convert h_subst using 1;
      exact Eq.symm ( by simpa using
        Language.subst_pair_eq_mul ( fun b => if b = true then L₂ else L₁ ) )
theorem IsContextFree.add {α : Type} {L₁ L₂ : Language α}
    (h₁ : IsContextFree L₁) (h₂ : IsContextFree L₂) :
    IsContextFree (L₁ + L₂) := by
      classical
      obtain ⟨ g₁, hg₁ ⟩ := h₁
      obtain ⟨ g₂, hg₂ ⟩ := h₂
      set f : Bool → Language α := fun b => if b then g₂.language else g₁.language
      have h_subst : IsContextFree (Language.subst ({[false], [true]} : Language Bool) f) := by
        classical
        apply_rules [ IsContextFree.subst, isContextFree_pair_bool ];
        exact fun a => by cases a <;> [ exact ⟨ g₁, rfl ⟩ ; exact ⟨ g₂, rfl ⟩ ] ;
      exact (by
        convert h_subst using 1
        rw [ ← hg₁, ← hg₂, Language.subst_singletons_eq_add ]
        aesop
      )
theorem IsContextFree.kstar {α : Type} {L : Language α}
    (h : IsContextFree L) :
    IsContextFree (KStar.kstar L) := by
      have := IsContextFree.subst (Set.univ : Language Unit) (fun _ => L)
          isContextFree_univ_unit (fun _ => h)
      rwa [Language.subst_univ_unit_eq_kstar] at this
end
