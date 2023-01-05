/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.list.infix
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Basic

/-!
# Prefixes, subfixes, infixes

This file proves properties about
* `list.prefix`: `l₁` is a prefix of `l₂` if `l₂` starts with `l₁`.
* `list.subfix`: `l₁` is a subfix of `l₂` if `l₂` ends with `l₁`.
* `list.infix`: `l₁` is an infix of `l₂` if `l₁` is a prefix of some subfix of `l₂`.
* `list.inits`: The list of prefixes of a list.
* `list.tails`: The list of prefixes of a list.
* `insert` on lists

All those (except `insert`) are defined in `data.list.defs`.

## Notation

`l₁ <+: l₂`: `l₁` is a prefix of `l₂`.
`l₁ <:+ l₂`: `l₁` is a subfix of `l₂`.
`l₁ <:+: l₂`: `l₁` is an infix of `l₂`.
-/


open Nat

variable {α β : Type _}

namespace List

variable {l l₁ l₂ l₃ : List α} {a b : α} {m n : ℕ}

/-! ### prefix, suffix, infix -/


section Fix

@[simp]
theorem prefix_append (l₁ l₂ : List α) : l₁ <+: l₁ ++ l₂ :=
  ⟨l₂, rfl⟩
#align list.prefix_append List.prefix_append

@[simp]
theorem suffix_append (l₁ l₂ : List α) : l₂ <:+ l₁ ++ l₂ :=
  ⟨l₁, rfl⟩
#align list.suffix_append List.suffix_append

theorem infix_append (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ l₂ ++ l₃ :=
  ⟨l₁, l₃, rfl⟩
#align list.infix_append List.infix_append

@[simp]
theorem infix_append' (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [← List.append_assoc] <;> apply infix_append
#align list.infix_append' List.infix_append'

theorem isPrefix.is_infix : l₁ <+: l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨[], t, h⟩
#align list.is_prefix.is_infix List.isPrefix.is_infix

theorem isSuffix.is_infix : l₁ <:+ l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨t, [], by rw [h, append_nil]⟩
#align list.is_suffix.is_infix List.isSuffix.is_infix

theorem nil_prefix (l : List α) : [] <+: l :=
  ⟨l, rfl⟩
#align list.nil_prefix List.nil_prefix

theorem nil_suffix (l : List α) : [] <:+ l :=
  ⟨l, append_nil _⟩
#align list.nil_suffix List.nil_suffix

theorem nil_infix (l : List α) : [] <:+: l :=
  (nil_prefix _).isInfix
#align list.nil_infix List.nil_infix

@[refl]
theorem prefix_refl (l : List α) : l <+: l :=
  ⟨[], append_nil _⟩
#align list.prefix_refl List.prefix_refl

@[refl]
theorem suffix_refl (l : List α) : l <:+ l :=
  ⟨[], rfl⟩
#align list.suffix_refl List.suffix_refl

@[refl]
theorem infix_refl (l : List α) : l <:+: l :=
  (prefix_refl l).isInfix
#align list.infix_refl List.infix_refl

theorem prefix_rfl : l <+: l :=
  prefix_refl _
#align list.prefix_rfl List.prefix_rfl

theorem suffix_rfl : l <:+ l :=
  suffix_refl _
#align list.suffix_rfl List.suffix_rfl

theorem infix_rfl : l <:+: l :=
  infix_refl _
#align list.infix_rfl List.infix_rfl

@[simp]
theorem suffix_cons (a : α) : ∀ l, l <:+ a :: l :=
  suffix_append [a]
#align list.suffix_cons List.suffix_cons

theorem prefix_concat (a : α) (l) : l <+: concat l a := by simp
#align list.prefix_concat List.prefix_concat

theorem infix_cons : l₁ <:+: l₂ → l₁ <:+: a :: l₂ := fun ⟨L₁, L₂, h⟩ => ⟨a :: L₁, L₂, h ▸ rfl⟩
#align list.infix_cons List.infix_cons

theorem infix_concat : l₁ <:+: l₂ → l₁ <:+: concat l₂ a := fun ⟨L₁, L₂, h⟩ =>
  ⟨L₁, concat L₂ a, by simp_rw [← h, concat_eq_append, append_assoc]⟩
#align list.infix_concat List.infix_concat

@[trans]
theorem isPrefix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₂ → l₂ <+: l₃ → l₁ <+: l₃
  | l, _, _, ⟨r₁, rfl⟩, ⟨r₂, rfl⟩ => ⟨r₁ ++ r₂, (append_assoc _ _ _).symm⟩
#align list.is_prefix.trans List.isPrefix.trans

@[trans]
theorem isSuffix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+ l₂ → l₂ <:+ l₃ → l₁ <:+ l₃
  | l, _, _, ⟨l₁, rfl⟩, ⟨l₂, rfl⟩ => ⟨l₂ ++ l₁, append_assoc _ _ _⟩
#align list.is_suffix.trans List.isSuffix.trans

@[trans]
theorem isInfix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+: l₂ → l₂ <:+: l₃ → l₁ <:+: l₃
  | l, _, _, ⟨l₁, r₁, rfl⟩, ⟨l₂, r₂, rfl⟩ => ⟨l₂ ++ l₁, r₁ ++ r₂, by simp only [append_assoc]⟩
#align list.is_infix.trans List.isInfix.trans

protected theorem isInfix.sublist : l₁ <:+: l₂ → l₁ <+ l₂ := fun ⟨s, t, h⟩ =>
  by
  rw [← h]
  exact (sublist_append_right _ _).trans (sublist_append_left _ _)
#align list.is_infix.sublist List.isInfix.sublist

protected theorem isInfix.subset (hl : l₁ <:+: l₂) : l₁ ⊆ l₂ :=
  hl.Sublist.Subset
#align list.is_infix.subset List.isInfix.subset

protected theorem isPrefix.sublist (h : l₁ <+: l₂) : l₁ <+ l₂ :=
  h.isInfix.Sublist
#align list.is_prefix.sublist List.isPrefix.sublist

protected theorem isPrefix.subset (hl : l₁ <+: l₂) : l₁ ⊆ l₂ :=
  hl.Sublist.Subset
#align list.is_prefix.subset List.isPrefix.subset

protected theorem isSuffix.sublist (h : l₁ <:+ l₂) : l₁ <+ l₂ :=
  h.isInfix.Sublist
#align list.is_suffix.sublist List.isSuffix.sublist

protected theorem isSuffix.subset (hl : l₁ <:+ l₂) : l₁ ⊆ l₂ :=
  hl.Sublist.Subset
#align list.is_suffix.subset List.isSuffix.subset

@[simp]
theorem reverse_suffix : reverse l₁ <:+ reverse l₂ ↔ l₁ <+: l₂ :=
  ⟨fun ⟨r, e⟩ => ⟨reverse r, by rw [← reverse_reverse l₁, ← reverse_append, e, reverse_reverse]⟩,
    fun ⟨r, e⟩ => ⟨reverse r, by rw [← reverse_append, e]⟩⟩
#align list.reverse_suffix List.reverse_suffix

@[simp]
theorem reverse_prefix : reverse l₁ <+: reverse l₂ ↔ l₁ <:+ l₂ := by
  rw [← reverse_suffix] <;> simp only [reverse_reverse]
#align list.reverse_prefix List.reverse_prefix

@[simp]
theorem reverse_infix : reverse l₁ <:+: reverse l₂ ↔ l₁ <:+: l₂ :=
  ⟨fun ⟨s, t, e⟩ =>
    ⟨reverse t, reverse s, by
      rw [← reverse_reverse l₁, append_assoc, ← reverse_append, ← reverse_append, e,
        reverse_reverse]⟩,
    fun ⟨s, t, e⟩ =>
    ⟨reverse t, reverse s, by rw [append_assoc, ← reverse_append, ← reverse_append, e]⟩⟩
#align list.reverse_infix List.reverse_infix

alias reverse_prefix ↔ _ is_suffix.reverse

alias reverse_suffix ↔ _ is_prefix.reverse

alias reverse_infix ↔ _ is_infix.reverse

theorem isInfix.length_le (h : l₁ <:+: l₂) : l₁.length ≤ l₂.length :=
  h.Sublist.length_le
#align list.is_infix.length_le List.isInfix.length_le

theorem isPrefix.length_le (h : l₁ <+: l₂) : l₁.length ≤ l₂.length :=
  h.Sublist.length_le
#align list.is_prefix.length_le List.isPrefix.length_le

theorem isSuffix.length_le (h : l₁ <:+ l₂) : l₁.length ≤ l₂.length :=
  h.Sublist.length_le
#align list.is_suffix.length_le List.isSuffix.length_le

theorem eq_nil_of_infix_nil (h : l <:+: []) : l = [] :=
  eq_nil_of_sublist_nil h.Sublist
#align list.eq_nil_of_infix_nil List.eq_nil_of_infix_nil

@[simp]
theorem infix_nil_iff : l <:+: [] ↔ l = [] :=
  ⟨fun h => eq_nil_of_sublist_nil h.Sublist, fun h => h ▸ infix_rfl⟩
#align list.infix_nil_iff List.infix_nil_iff

alias infix_nil_iff ↔ eq_nil_of_infix_nil _

@[simp]
theorem prefix_nil_iff : l <+: [] ↔ l = [] :=
  ⟨fun h => eq_nil_of_infix_nil h.isInfix, fun h => h ▸ prefix_rfl⟩
#align list.prefix_nil_iff List.prefix_nil_iff

@[simp]
theorem suffix_nil_iff : l <:+ [] ↔ l = [] :=
  ⟨fun h => eq_nil_of_infix_nil h.isInfix, fun h => h ▸ suffix_rfl⟩
#align list.suffix_nil_iff List.suffix_nil_iff

alias prefix_nil_iff ↔ eq_nil_of_prefix_nil _

alias suffix_nil_iff ↔ eq_nil_of_suffix_nil _

theorem infix_iff_prefix_suffix (l₁ l₂ : List α) : l₁ <:+: l₂ ↔ ∃ t, l₁ <+: t ∧ t <:+ l₂ :=
  ⟨fun ⟨s, t, e⟩ => ⟨l₁ ++ t, ⟨_, rfl⟩, by rw [← e, append_assoc] <;> exact ⟨_, rfl⟩⟩,
    fun ⟨_, ⟨t, rfl⟩, s, e⟩ => ⟨s, t, by rw [append_assoc] <;> exact e⟩⟩
#align list.infix_iff_prefix_suffix List.infix_iff_prefix_suffix

theorem eq_of_infix_of_length_eq (h : l₁ <:+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.Sublist.eq_of_length
#align list.eq_of_infix_of_length_eq List.eq_of_infix_of_length_eq

theorem eq_of_prefix_of_length_eq (h : l₁ <+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.Sublist.eq_of_length
#align list.eq_of_prefix_of_length_eq List.eq_of_prefix_of_length_eq

theorem eq_of_suffix_of_length_eq (h : l₁ <:+ l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.Sublist.eq_of_length
#align list.eq_of_suffix_of_length_eq List.eq_of_suffix_of_length_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `prefix_of_prefix_length_le [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.implicitBinder "{" [`l₁ `l₂ `l₃] [":" (Term.app `List [`α])] "}")]
         []
         ","
         (Term.arrow
          (List.Data.List.Defs.«term_<+:_» `l₁ " <+: " `l₃)
          "→"
          (Term.arrow
           (List.Data.List.Defs.«term_<+:_» `l₂ " <+: " `l₃)
           "→"
           (Term.arrow
            («term_≤_» (Term.app `length [`l₁]) "≤" (Term.app `length [`l₂]))
            "→"
            (List.Data.List.Defs.«term_<+:_» `l₁ " <+: " `l₂)))))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]") "," `l₂ "," `l₃ "," `h₁ "," `h₂ "," (Term.hole "_")]]
           "=>"
           (Term.app `nil_prefix [(Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[(«term_::_» `a "::" `l₁)
             ","
             («term_::_» `b "::" `l₂)
             ","
             (Term.hole "_")
             ","
             (Term.anonymousCtor "⟨" [`r₁ "," `rfl] "⟩")
             ","
             (Term.anonymousCtor "⟨" [`r₂ "," `e] "⟩")
             ","
             `ll]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.injection "injection" `e ["with" ["_" `e']])
               ";"
               (Tactic.subst "subst" [`b])
               []
               (Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget
                  []
                  (Term.app
                   `prefix_of_prefix_length_le
                   [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")
                    (Term.anonymousCtor "⟨" [(Term.hole "_") "," `e'] "⟩")
                    (Term.app `le_of_succ_le_succ [`ll])]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r₃)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])
                  [])])
               []
               (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`r₃ "," `rfl] "⟩"))]))))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.injection "injection" `e ["with" ["_" `e']])
          ";"
          (Tactic.subst "subst" [`b])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget
             []
             (Term.app
              `prefix_of_prefix_length_le
              [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")
               (Term.anonymousCtor "⟨" [(Term.hole "_") "," `e'] "⟩")
               (Term.app `le_of_succ_le_succ [`ll])]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r₃)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`r₃ "," `rfl] "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`r₃ "," `rfl] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`r₃ "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r₃
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          `prefix_of_prefix_length_le
          [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")
           (Term.anonymousCtor "⟨" [(Term.hole "_") "," `e'] "⟩")
           (Term.app `le_of_succ_le_succ [`ll])]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r₃)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `prefix_of_prefix_length_le
       [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")
        (Term.anonymousCtor "⟨" [(Term.hole "_") "," `e'] "⟩")
        (Term.app `le_of_succ_le_succ [`ll])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_succ_le_succ [`ll])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ll
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_succ_le_succ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `le_of_succ_le_succ [`ll])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `e'] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `prefix_of_prefix_length_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.subst "subst" [`b])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.injection "injection" `e ["with" ["_" `e']])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '_', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '_', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  prefix_of_prefix_length_le
  : ∀ { l₁ l₂ l₃ : List α } , l₁ <+: l₃ → l₂ <+: l₃ → length l₁ ≤ length l₂ → l₁ <+: l₂
  | [ ] , l₂ , l₃ , h₁ , h₂ , _ => nil_prefix _
    |
      a :: l₁ , b :: l₂ , _ , ⟨ r₁ , rfl ⟩ , ⟨ r₂ , e ⟩ , ll
      =>
      by
        injection e with _ e'
          ;
          subst b
          rcases
            prefix_of_prefix_length_le ⟨ _ , rfl ⟩ ⟨ _ , e' ⟩ le_of_succ_le_succ ll
            with ⟨ r₃ , rfl ⟩
          exact ⟨ r₃ , rfl ⟩
#align list.prefix_of_prefix_length_le List.prefix_of_prefix_length_le

theorem prefix_or_prefix_of_prefix (h₁ : l₁ <+: l₃) (h₂ : l₂ <+: l₃) : l₁ <+: l₂ ∨ l₂ <+: l₁ :=
  (le_total (length l₁) (length l₂)).imp (prefix_of_prefix_length_le h₁ h₂)
    (prefix_of_prefix_length_le h₂ h₁)
#align list.prefix_or_prefix_of_prefix List.prefix_or_prefix_of_prefix

theorem suffix_of_suffix_length_le (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) (ll : length l₁ ≤ length l₂) :
    l₁ <:+ l₂ :=
  reverse_prefix.1 <|
    prefix_of_prefix_length_le (reverse_prefix.2 h₁) (reverse_prefix.2 h₂) (by simp [ll])
#align list.suffix_of_suffix_length_le List.suffix_of_suffix_length_le

theorem suffix_or_suffix_of_suffix (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) : l₁ <:+ l₂ ∨ l₂ <:+ l₁ :=
  (prefix_or_prefix_of_prefix (reverse_prefix.2 h₁) (reverse_prefix.2 h₂)).imp reverse_prefix.1
    reverse_prefix.1
#align list.suffix_or_suffix_of_suffix List.suffix_or_suffix_of_suffix

theorem suffix_cons_iff : l₁ <:+ a :: l₂ ↔ l₁ = a :: l₂ ∨ l₁ <:+ l₂ :=
  by
  constructor
  · rintro ⟨⟨hd, tl⟩, hl₃⟩
    · exact Or.inl hl₃
    · simp only [cons_append] at hl₃
      exact Or.inr ⟨_, hl₃.2⟩
  · rintro (rfl | hl₁)
    · exact (a :: l₂).suffix_refl
    · exact hl₁.trans (l₂.suffix_cons _)
#align list.suffix_cons_iff List.suffix_cons_iff

theorem infix_cons_iff : l₁ <:+: a :: l₂ ↔ l₁ <+: a :: l₂ ∨ l₁ <:+: l₂ :=
  by
  constructor
  · rintro ⟨⟨hd, tl⟩, t, hl₃⟩
    · exact Or.inl ⟨t, hl₃⟩
    · simp only [cons_append] at hl₃
      exact Or.inr ⟨_, t, hl₃.2⟩
  · rintro (h | hl₁)
    · exact h.is_infix
    · exact infix_cons hl₁
#align list.infix_cons_iff List.infix_cons_iff

theorem infix_of_mem_join : ∀ {L : List (List α)}, l ∈ L → l <:+: join L
  | _ :: L, Or.inl rfl => infix_append [] _ _
  | l' :: L, Or.inr h => isInfix.trans (infix_of_mem_join h) <| (suffix_append _ _).isInfix
#align list.infix_of_mem_join List.infix_of_mem_join

theorem prefix_append_right_inj (l) : l ++ l₁ <+: l ++ l₂ ↔ l₁ <+: l₂ :=
  exists_congr fun r => by rw [append_assoc, append_right_inj]
#align list.prefix_append_right_inj List.prefix_append_right_inj

theorem prefix_cons_inj (a) : a :: l₁ <+: a :: l₂ ↔ l₁ <+: l₂ :=
  prefix_append_right_inj [a]
#align list.prefix_cons_inj List.prefix_cons_inj

theorem take_prefix (n) (l : List α) : take n l <+: l :=
  ⟨_, take_append_drop _ _⟩
#align list.take_prefix List.take_prefix

theorem drop_suffix (n) (l : List α) : drop n l <:+ l :=
  ⟨_, take_append_drop _ _⟩
#align list.drop_suffix List.drop_suffix

theorem take_sublist (n) (l : List α) : take n l <+ l :=
  (take_prefix n l).Sublist
#align list.take_sublist List.take_sublist

theorem drop_sublist (n) (l : List α) : drop n l <+ l :=
  (drop_suffix n l).Sublist
#align list.drop_sublist List.drop_sublist

theorem take_subset (n) (l : List α) : take n l ⊆ l :=
  (take_sublist n l).Subset
#align list.take_subset List.take_subset

theorem drop_subset (n) (l : List α) : drop n l ⊆ l :=
  (drop_sublist n l).Subset
#align list.drop_subset List.drop_subset

theorem mem_of_mem_take (h : a ∈ l.take n) : a ∈ l :=
  take_subset n l h
#align list.mem_of_mem_take List.mem_of_mem_take

/- warning: list.mem_of_mem_drop -> List.mem_of_mem_drop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {a : α} {n : Nat}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (List.drop.{u1} α n l)) -> (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l)
but is expected to have type
  forall {α : Type.{u1}} {l : α} {a : Nat} {n : List.{u1} α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) l (List.drop.{u1} α a n)) -> (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) l n)
Case conversion may be inaccurate. Consider using '#align list.mem_of_mem_drop List.mem_of_mem_dropₓ'. -/
theorem mem_of_mem_drop (h : a ∈ l.drop n) : a ∈ l :=
  drop_subset n l h
#align list.mem_of_mem_drop List.mem_of_mem_drop

theorem take_while_prefix (p : α → Prop) [DecidablePred p] : l.takeWhile p <+: l :=
  ⟨l.dropWhile p, take_while_append_drop p l⟩
#align list.take_while_prefix List.take_while_prefix

theorem drop_while_suffix (p : α → Prop) [DecidablePred p] : l.dropWhile p <:+ l :=
  ⟨l.takeWhile p, take_while_append_drop p l⟩
#align list.drop_while_suffix List.drop_while_suffix

theorem init_prefix : ∀ l : List α, l.init <+: l
  | [] => ⟨nil, by rw [init, List.append_nil]⟩
  | a :: l => ⟨_, init_append_last (cons_ne_nil a l)⟩
#align list.init_prefix List.init_prefix

theorem tail_suffix (l : List α) : tail l <:+ l := by rw [← drop_one] <;> apply drop_suffix
#align list.tail_suffix List.tail_suffix

theorem init_sublist (l : List α) : l.init <+ l :=
  (init_prefix l).Sublist
#align list.init_sublist List.init_sublist

theorem tail_sublist (l : List α) : l.tail <+ l :=
  (tail_suffix l).Sublist
#align list.tail_sublist List.tail_sublist

theorem init_subset (l : List α) : l.init ⊆ l :=
  (init_sublist l).Subset
#align list.init_subset List.init_subset

theorem tail_subset (l : List α) : tail l ⊆ l :=
  (tail_sublist l).Subset
#align list.tail_subset List.tail_subset

theorem mem_of_mem_init (h : a ∈ l.init) : a ∈ l :=
  init_subset l h
#align list.mem_of_mem_init List.mem_of_mem_init

theorem mem_of_mem_tail (h : a ∈ l.tail) : a ∈ l :=
  tail_subset l h
#align list.mem_of_mem_tail List.mem_of_mem_tail

theorem prefix_iff_eq_append : l₁ <+: l₂ ↔ l₁ ++ drop (length l₁) l₂ = l₂ :=
  ⟨by rintro ⟨r, rfl⟩ <;> rw [drop_left], fun e => ⟨_, e⟩⟩
#align list.prefix_iff_eq_append List.prefix_iff_eq_append

theorem suffix_iff_eq_append : l₁ <:+ l₂ ↔ take (length l₂ - length l₁) l₂ ++ l₁ = l₂ :=
  ⟨by rintro ⟨r, rfl⟩ <;> simp only [length_append, add_tsub_cancel_right, take_left], fun e =>
    ⟨_, e⟩⟩
#align list.suffix_iff_eq_append List.suffix_iff_eq_append

theorem prefix_iff_eq_take : l₁ <+: l₂ ↔ l₁ = take (length l₁) l₂ :=
  ⟨fun h => append_right_cancel <| (prefix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ take_prefix _ _⟩
#align list.prefix_iff_eq_take List.prefix_iff_eq_take

theorem suffix_iff_eq_drop : l₁ <:+ l₂ ↔ l₁ = drop (length l₂ - length l₁) l₂ :=
  ⟨fun h => append_left_cancel <| (suffix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ drop_suffix _ _⟩
#align list.suffix_iff_eq_drop List.suffix_iff_eq_drop

instance decidablePrefix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <+: l₂)
  | [], l₂ => isTrue ⟨l₂, rfl⟩
  | a :: l₁, [] => is_false fun ⟨t, te⟩ => List.noConfusion te
  | a :: l₁, b :: l₂ =>
    if h : a = b then
      decidable_of_decidable_of_iff (decidable_prefix l₁ l₂) (by rw [← h, prefix_cons_inj])
    else is_false fun ⟨t, te⟩ => h <| by injection te
#align list.decidable_prefix List.decidablePrefix

-- Alternatively, use mem_tails
instance decidableSuffix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+ l₂)
  | [], l₂ => isTrue ⟨l₂, append_nil _⟩
  | a :: l₁, [] => is_false <| mt (sublist.length_le ∘ is_suffix.sublist) (by decide)
  | l₁, b :: l₂ =>
    decidable_of_decidable_of_iff (@Or.decidable _ _ _ (l₁.decidableSuffix l₂)) suffix_cons_iff.symm
#align list.decidable_suffix List.decidableSuffix

instance decidableInfix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+: l₂)
  | [], l₂ => isTrue ⟨[], l₂, rfl⟩
  | a :: l₁, [] => is_false fun ⟨s, t, te⟩ => by simp at te <;> exact te
  | l₁, b :: l₂ =>
    decidable_of_decidable_of_iff
      (@Or.decidable _ _ (l₁.decidablePrefix (b :: l₂)) (l₁.decidableInfix l₂)) infix_cons_iff.symm
#align list.decidable_infix List.decidableInfix

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:564:6: unsupported: specialize @hyp -/
theorem prefix_take_le_iff {L : List (List (Option α))} (hm : m < L.length) :
    L.take m <+: L.take n ↔ m ≤ n :=
  by
  simp only [prefix_iff_eq_take, length_take]
  induction' m with m IH generalizing L n
  · simp only [min_eq_left, eq_self_iff_true, Nat.zero_le, take]
  cases' L with l ls
  · exact (not_lt_bot hm).elim
  cases n
  · refine' iff_of_false _ (zero_lt_succ _).not_le
    rw [take_zero, take_nil]
    simp only [take]
    exact not_false
  · simp only [length] at hm
    specialize IH ls n (Nat.lt_of_succ_lt_succ hm)
    simp only [le_of_lt (Nat.lt_of_succ_lt_succ hm), min_eq_left] at IH
    simp only [le_of_lt hm, IH, true_and_iff, min_eq_left, eq_self_iff_true, length, take]
    exact ⟨Nat.succ_le_succ, Nat.le_of_succ_le_succ⟩
#align list.prefix_take_le_iff List.prefix_take_le_iff

theorem cons_prefix_iff : a :: l₁ <+: b :: l₂ ↔ a = b ∧ l₁ <+: l₂ :=
  by
  constructor
  · rintro ⟨L, hL⟩
    simp only [cons_append] at hL
    exact ⟨hL.left, ⟨L, hL.right⟩⟩
  · rintro ⟨rfl, h⟩
    rwa [prefix_cons_inj]
#align list.cons_prefix_iff List.cons_prefix_iff

theorem isPrefix.map (h : l₁ <+: l₂) (f : α → β) : l₁.map f <+: l₂.map f :=
  by
  induction' l₁ with hd tl hl generalizing l₂
  · simp only [nil_prefix, map_nil]
  · cases' l₂ with hd₂ tl₂
    · simpa only using eq_nil_of_prefix_nil h
    · rw [cons_prefix_iff] at h
      simp only [h, prefix_cons_inj, hl, map]
#align list.is_prefix.map List.isPrefix.map

theorem isPrefix.filter_map (h : l₁ <+: l₂) (f : α → Option β) :
    l₁.filterMap f <+: l₂.filterMap f :=
  by
  induction' l₁ with hd₁ tl₁ hl generalizing l₂
  · simp only [nil_prefix, filter_map_nil]
  · cases' l₂ with hd₂ tl₂
    · simpa only using eq_nil_of_prefix_nil h
    · rw [cons_prefix_iff] at h
      rw [← @singleton_append _ hd₁ _, ← @singleton_append _ hd₂ _, filter_map_append,
        filter_map_append, h.left, prefix_append_right_inj]
      exact hl h.right
#align list.is_prefix.filter_map List.isPrefix.filter_map

theorem isPrefix.reduce_option {l₁ l₂ : List (Option α)} (h : l₁ <+: l₂) :
    l₁.reduceOption <+: l₂.reduceOption :=
  h.filterMap id
#align list.is_prefix.reduce_option List.isPrefix.reduce_option

theorem isPrefix.filter (p : α → Prop) [DecidablePred p] ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    l₁.filter p <+: l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]
  exact prefix_append _ _
#align list.is_prefix.filter List.isPrefix.filter

theorem isSuffix.filter (p : α → Prop) [DecidablePred p] ⦃l₁ l₂ : List α⦄ (h : l₁ <:+ l₂) :
    l₁.filter p <:+ l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]
  exact suffix_append _ _
#align list.is_suffix.filter List.isSuffix.filter

theorem isInfix.filter (p : α → Prop) [DecidablePred p] ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    l₁.filter p <:+: l₂.filter p := by
  obtain ⟨xs, ys, rfl⟩ := h
  rw [filter_append, filter_append]
  exact infix_append _ _ _
#align list.is_infix.filter List.isInfix.filter

instance : IsPartialOrder (List α) (· <+: ·)
    where
  refl := prefix_refl
  trans _ _ _ := isPrefix.trans
  antisymm _ _ h₁ h₂ := eq_of_prefix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

instance : IsPartialOrder (List α) (· <:+ ·)
    where
  refl := suffix_refl
  trans _ _ _ := isSuffix.trans
  antisymm _ _ h₁ h₂ := eq_of_suffix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

instance : IsPartialOrder (List α) (· <:+: ·)
    where
  refl := infix_refl
  trans _ _ _ := isInfix.trans
  antisymm _ _ h₁ h₂ := eq_of_infix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

end Fix

section InitsTails

@[simp]
theorem mem_inits : ∀ s t : List α, s ∈ inits t ↔ s <+: t
  | s, [] =>
    suffices s = nil ↔ s <+: nil by simpa only [inits, mem_singleton]
    ⟨fun h => h.symm ▸ prefix_refl [], eq_nil_of_prefix_nil⟩
  | s, a :: t =>
    suffices (s = nil ∨ ∃ l ∈ inits t, a :: l = s) ↔ s <+: a :: t by simpa
    ⟨fun o =>
      match s, o with
      | _, Or.inl rfl => ⟨_, rfl⟩
      | s, Or.inr ⟨r, hr, hs⟩ => by
        let ⟨s, ht⟩ := (mem_inits _ _).1 hr
        rw [← hs, ← ht] <;> exact ⟨s, rfl⟩,
      fun mi =>
      match s, mi with
      | [], ⟨_, rfl⟩ => Or.inl rfl
      | b :: s, ⟨r, hr⟩ =>
        (List.noConfusion hr) fun ba (st : s ++ r = t) =>
          Or.inr <| by rw [ba] <;> exact ⟨_, (mem_inits _ _).2 ⟨_, st⟩, rfl⟩⟩
#align list.mem_inits List.mem_inits

@[simp]
theorem mem_tails : ∀ s t : List α, s ∈ tails t ↔ s <:+ t
  | s, [] => by
    simp only [tails, mem_singleton] <;>
      exact ⟨fun h => by rw [h] <;> exact suffix_refl [], eq_nil_of_suffix_nil⟩
  | s, a :: t => by
    simp only [tails, mem_cons_iff, mem_tails s t] <;>
      exact
        show s = a :: t ∨ s <:+ t ↔ s <:+ a :: t from
          ⟨fun o =>
            match s, t, o with
            | _, t, Or.inl rfl => suffix_rfl
            | s, _, Or.inr ⟨l, rfl⟩ => ⟨a :: l, rfl⟩,
            fun e =>
            match s, t, e with
            | _, t, ⟨[], rfl⟩ => Or.inl rfl
            | s, t, ⟨b :: l, he⟩ => List.noConfusion he fun ab lt => Or.inr ⟨l, lt⟩⟩
#align list.mem_tails List.mem_tails

theorem inits_cons (a : α) (l : List α) : inits (a :: l) = [] :: l.inits.map fun t => a :: t := by
  simp
#align list.inits_cons List.inits_cons

theorem tails_cons (a : α) (l : List α) : tails (a :: l) = (a :: l) :: l.tails := by simp
#align list.tails_cons List.tails_cons

@[simp]
theorem inits_append : ∀ s t : List α, inits (s ++ t) = s.inits ++ t.inits.tail.map fun l => s ++ l
  | [], [] => by simp
  | [], a :: t => by simp
  | a :: s, t => by simp [inits_append s t]
#align list.inits_append List.inits_append

@[simp]
theorem tails_append :
    ∀ s t : List α, tails (s ++ t) = (s.tails.map fun l => l ++ t) ++ t.tails.tail
  | [], [] => by simp
  | [], a :: t => by simp
  | a :: s, t => by simp [tails_append s t]
#align list.tails_append List.tails_append

-- the lemma names `inits_eq_tails` and `tails_eq_inits` are like `sublists_eq_sublists'`
theorem inits_eq_tails : ∀ l : List α, l.inits = (reverse <| map reverse <| tails <| reverse l)
  | [] => by simp
  | a :: l => by simp [inits_eq_tails l, map_eq_map_iff]
#align list.inits_eq_tails List.inits_eq_tails

theorem tails_eq_inits : ∀ l : List α, l.tails = (reverse <| map reverse <| inits <| reverse l)
  | [] => by simp
  | a :: l => by simp [tails_eq_inits l, append_left_inj]
#align list.tails_eq_inits List.tails_eq_inits

theorem inits_reverse (l : List α) : inits (reverse l) = reverse (map reverse l.tails) :=
  by
  rw [tails_eq_inits l]
  simp [reverse_involutive.comp_self]
#align list.inits_reverse List.inits_reverse

theorem tails_reverse (l : List α) : tails (reverse l) = reverse (map reverse l.inits) :=
  by
  rw [inits_eq_tails l]
  simp [reverse_involutive.comp_self]
#align list.tails_reverse List.tails_reverse

theorem map_reverse_inits (l : List α) : map reverse l.inits = (reverse <| tails <| reverse l) :=
  by
  rw [inits_eq_tails l]
  simp [reverse_involutive.comp_self]
#align list.map_reverse_inits List.map_reverse_inits

theorem map_reverse_tails (l : List α) : map reverse l.tails = (reverse <| inits <| reverse l) :=
  by
  rw [tails_eq_inits l]
  simp [reverse_involutive.comp_self]
#align list.map_reverse_tails List.map_reverse_tails

@[simp]
theorem length_tails (l : List α) : length (tails l) = length l + 1 :=
  by
  induction' l with x l IH
  · simp
  · simpa using IH
#align list.length_tails List.length_tails

@[simp]
theorem length_inits (l : List α) : length (inits l) = length l + 1 := by simp [inits_eq_tails]
#align list.length_inits List.length_inits

@[simp]
theorem nth_le_tails (l : List α) (n : ℕ) (hn : n < length (tails l)) :
    nthLe (tails l) n hn = l.drop n :=
  by
  induction' l with x l IH generalizing n
  · simp
  · cases n
    · simp
    · simpa using IH n _
#align list.nth_le_tails List.nth_le_tails

@[simp]
theorem nth_le_inits (l : List α) (n : ℕ) (hn : n < length (inits l)) :
    nthLe (inits l) n hn = l.take n :=
  by
  induction' l with x l IH generalizing n
  · simp
  · cases n
    · simp
    · simpa using IH n _
#align list.nth_le_inits List.nth_le_inits

end InitsTails

/-! ### insert -/


section Insert

variable [DecidableEq α]

@[simp]
theorem insert_nil (a : α) : insert a nil = [a] :=
  rfl
#align list.insert_nil List.insert_nil

theorem insert.def (a : α) (l : List α) : insert a l = if a ∈ l then l else a :: l :=
  rfl
#align list.insert.def List.insert.def

/- warning: list.insert_of_mem -> List.insert_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {a : α} [_inst_1 : DecidableEq.{succ u1} α], (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (Eq.{succ u1} (List.{u1} α) (Insert.insert.{u1, u1} α (List.{u1} α) (List.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a l) l)
but is expected to have type
  forall {α : Type.{u1}} [l : DecidableEq.{succ u1} α] {a : α} {_inst_1 : List.{u1} α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a _inst_1) -> (Eq.{succ u1} (List.{u1} α) (List.insert.{u1} α (fun (a : α) (b : α) => l a b) a _inst_1) _inst_1)
Case conversion may be inaccurate. Consider using '#align list.insert_of_mem List.insert_of_memₓ'. -/
@[simp]
theorem insert_of_mem (h : a ∈ l) : insert a l = l := by simp only [insert.def, if_pos h]
#align list.insert_of_mem List.insert_of_mem

/- warning: list.insert_of_not_mem -> List.insert_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {a : α} [_inst_1 : DecidableEq.{succ u1} α], (Not (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l)) -> (Eq.{succ u1} (List.{u1} α) (Insert.insert.{u1, u1} α (List.{u1} α) (List.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a l) (List.cons.{u1} α a l))
but is expected to have type
  forall {α : Type.{u1}} [l : DecidableEq.{succ u1} α] {a : α} {_inst_1 : List.{u1} α}, (Not (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a _inst_1)) -> (Eq.{succ u1} (List.{u1} α) (List.insert.{u1} α (fun (a : α) (b : α) => l a b) a _inst_1) (List.cons.{u1} α a _inst_1))
Case conversion may be inaccurate. Consider using '#align list.insert_of_not_mem List.insert_of_not_memₓ'. -/
@[simp]
theorem insert_of_not_mem (h : a ∉ l) : insert a l = a :: l := by
  simp only [insert.def, if_neg h] <;> constructor <;> rfl
#align list.insert_of_not_mem List.insert_of_not_mem

/- warning: list.mem_insert_iff -> List.mem_insert_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {a : α} {b : α} [_inst_1 : DecidableEq.{succ u1} α], Iff (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (Insert.insert.{u1, u1} α (List.{u1} α) (List.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) b l)) (Or (Eq.{succ u1} α a b) (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l))
but is expected to have type
  forall {α : Type.{u1}} [l : DecidableEq.{succ u1} α] {a : α} {b : α} {_inst_1 : List.{u1} α}, Iff (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a (List.insert.{u1} α (fun (a : α) (b : α) => l a b) b _inst_1)) (Or (Eq.{succ u1} α a b) (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a _inst_1))
Case conversion may be inaccurate. Consider using '#align list.mem_insert_iff List.mem_insert_iffₓ'. -/
@[simp]
theorem mem_insert_iff : a ∈ insert b l ↔ a = b ∨ a ∈ l :=
  by
  by_cases h' : b ∈ l
  · simp only [insert_of_mem h']
    apply (or_iff_right_of_imp _).symm
    exact fun e => e.symm ▸ h'
  · simp only [insert_of_not_mem h', mem_cons_iff]
#align list.mem_insert_iff List.mem_insert_iff

@[simp]
theorem suffix_insert (a : α) (l : List α) : l <:+ insert a l := by
  by_cases a ∈ l <;> [simp only [insert_of_mem h], simp only [insert_of_not_mem h, suffix_cons]]
#align list.suffix_insert List.suffix_insert

theorem infix_insert (a : α) (l : List α) : l <:+: insert a l :=
  (suffix_insert a l).isInfix
#align list.infix_insert List.infix_insert

theorem sublist_insert (a : α) (l : List α) : l <+ l.insert a :=
  (suffix_insert a l).Sublist
#align list.sublist_insert List.sublist_insert

theorem subset_insert (a : α) (l : List α) : l ⊆ l.insert a :=
  (sublist_insert a l).Subset
#align list.subset_insert List.subset_insert

#print List.mem_insert_self /-
@[simp]
theorem mem_insert_self (a : α) (l : List α) : a ∈ l.insert a :=
  mem_insert_iff.2 <| Or.inl rfl
#align list.mem_insert_self List.mem_insert_self
-/

/- warning: list.mem_insert_of_mem -> List.mem_insert_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {a : α} {b : α} [_inst_1 : DecidableEq.{succ u1} α], (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (Insert.insert.{u1, u1} α (List.{u1} α) (List.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) b l))
but is expected to have type
  forall {α : Type.{u1}} [l : DecidableEq.{succ u1} α] {a : α} {b : α} {_inst_1 : List.{u1} α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a _inst_1) -> (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a (List.insert.{u1} α (fun (a : α) (b : α) => l a b) b _inst_1))
Case conversion may be inaccurate. Consider using '#align list.mem_insert_of_mem List.mem_insert_of_memₓ'. -/
theorem mem_insert_of_mem (h : a ∈ l) : a ∈ insert b l :=
  mem_insert_iff.2 (Or.inr h)
#align list.mem_insert_of_mem List.mem_insert_of_mem

/- warning: list.eq_or_mem_of_mem_insert -> List.eq_or_mem_of_mem_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {a : α} {b : α} [_inst_1 : DecidableEq.{succ u1} α], (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (Insert.insert.{u1, u1} α (List.{u1} α) (List.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) b l)) -> (Or (Eq.{succ u1} α a b) (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l))
but is expected to have type
  forall {α : Type.{u1}} [l : DecidableEq.{succ u1} α] {a : α} {b : α} {_inst_1 : List.{u1} α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a (List.insert.{u1} α (fun (a : α) (b : α) => l a b) b _inst_1)) -> (Or (Eq.{succ u1} α a b) (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a _inst_1))
Case conversion may be inaccurate. Consider using '#align list.eq_or_mem_of_mem_insert List.eq_or_mem_of_mem_insertₓ'. -/
theorem eq_or_mem_of_mem_insert (h : a ∈ insert b l) : a = b ∨ a ∈ l :=
  mem_insert_iff.1 h
#align list.eq_or_mem_of_mem_insert List.eq_or_mem_of_mem_insert

/- warning: list.length_insert_of_mem -> List.length_insert_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {a : α} [_inst_1 : DecidableEq.{succ u1} α], (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (Eq.{1} Nat (List.length.{u1} α (Insert.insert.{u1, u1} α (List.{u1} α) (List.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a l)) (List.length.{u1} α l))
but is expected to have type
  forall {α : Type.{u1}} [l : DecidableEq.{succ u1} α] {a : α} {_inst_1 : List.{u1} α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a _inst_1) -> (Eq.{1} Nat (List.length.{u1} α (List.insert.{u1} α (fun (a : α) (b : α) => l a b) a _inst_1)) (List.length.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align list.length_insert_of_mem List.length_insert_of_memₓ'. -/
@[simp]
theorem length_insert_of_mem (h : a ∈ l) : (insert a l).length = l.length :=
  congr_arg _ <| insert_of_mem h
#align list.length_insert_of_mem List.length_insert_of_mem

/- warning: list.length_insert_of_not_mem -> List.length_insert_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {a : α} [_inst_1 : DecidableEq.{succ u1} α], (Not (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l)) -> (Eq.{1} Nat (List.length.{u1} α (Insert.insert.{u1, u1} α (List.{u1} α) (List.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a l)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (List.length.{u1} α l) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} [l : DecidableEq.{succ u1} α] {a : α} {_inst_1 : List.{u1} α}, (Not (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a _inst_1)) -> (Eq.{1} Nat (List.length.{u1} α (List.insert.{u1} α (fun (a : α) (b : α) => l a b) a _inst_1)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (List.length.{u1} α _inst_1) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align list.length_insert_of_not_mem List.length_insert_of_not_memₓ'. -/
@[simp]
theorem length_insert_of_not_mem (h : a ∉ l) : (insert a l).length = l.length + 1 :=
  congr_arg _ <| insert_of_not_mem h
#align list.length_insert_of_not_mem List.length_insert_of_not_mem

end Insert

theorem mem_of_mem_suffix (hx : a ∈ l₁) (hl : l₁ <:+ l₂) : a ∈ l₂ :=
  hl.Subset hx
#align list.mem_of_mem_suffix List.mem_of_mem_suffix

end List

