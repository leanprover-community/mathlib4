/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.seq.seq
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Basic
import Mathbin.Data.LazyList
import Mathbin.Data.Nat.Basic
import Mathbin.Data.Stream.Init
import Mathbin.Data.Seq.Computation

universe u v w

/-
coinductive seq (α : Type u) : Type u
| nil : seq α
| cons : α → seq α → seq α
-/
/-- A stream `s : option α` is a sequence if `s.nth n = none` implies `s.nth (n + 1) = none`.
-/
def Stream'.IsSeq {α : Type u} (s : Stream' (Option α)) : Prop :=
  ∀ {n : ℕ}, s n = none → s (n + 1) = none
#align stream.is_seq Stream'.IsSeq

/- warning: seq clashes with has_seq -> Seq
warning: seq -> Seq is a dubious translation:
lean 3 declaration is
  Type.{u} -> Type.{u}
but is expected to have type
  (Type.{u} -> Type.{v}) -> Type.{max (succ u) v}
Case conversion may be inaccurate. Consider using '#align seq Seqₓ'. -/
/-- `seq α` is the type of possibly infinite lists (referred here as sequences).
  It is encoded as an infinite stream of options such that if `f n = none`, then
  `f m = none` for all `m ≥ n`. -/
def Seq (α : Type u) : Type u :=
  { f : Stream' (Option α) // f.IsSeq }
#align seq Seq

/-- `seq1 α` is the type of nonempty sequences. -/
def Seq1 (α) :=
  α × Seq α
#align seq1 Seq1

namespace Seq

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The empty sequence -/
def nil : Seq α :=
  ⟨Stream'.const none, fun n h => rfl⟩
#align seq.nil Seq.nil

instance : Inhabited (Seq α) :=
  ⟨nil⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Prepend an element to a sequence -/
def cons (a : α) (s : Seq α) : Seq α :=
  ⟨some a::s.1, by
    rintro (n | _) h
    · contradiction
    · exact s.2 h⟩
#align seq.cons Seq.cons

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem val_cons (s : Seq α) (x : α) : (cons x s).val = some x::s.val :=
  rfl
#align seq.val_cons Seq.val_cons

/-- Get the nth element of a sequence (if it exists) -/
def nth : Seq α → ℕ → Option α :=
  Subtype.val
#align seq.nth Seq.nth

@[simp]
theorem nth_mk (f hf) : @nth α ⟨f, hf⟩ = f :=
  rfl
#align seq.nth_mk Seq.nth_mk

@[simp]
theorem nth_nil (n : ℕ) : (@nil α).nth n = none :=
  rfl
#align seq.nth_nil Seq.nth_nil

@[simp]
theorem nth_cons_zero (a : α) (s : Seq α) : (cons a s).nth 0 = some a :=
  rfl
#align seq.nth_cons_zero Seq.nth_cons_zero

@[simp]
theorem nth_cons_succ (a : α) (s : Seq α) (n : ℕ) : (cons a s).nth (n + 1) = s.nth n :=
  rfl
#align seq.nth_cons_succ Seq.nth_cons_succ

@[ext]
protected theorem ext {s t : Seq α} (h : ∀ n : ℕ, s.nth n = t.nth n) : s = t :=
  Subtype.eq <| funext h
#align seq.ext Seq.ext

theorem cons_injective2 : Function.Injective2 (cons : α → Seq α → Seq α) := fun x y s t h =>
  ⟨by rw [← Option.some_inj, ← nth_cons_zero, h, nth_cons_zero],
    Seq.ext fun n => by simp_rw [← nth_cons_succ x s n, h, nth_cons_succ]⟩
#align seq.cons_injective2 Seq.cons_injective2

theorem cons_left_injective (s : Seq α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _
#align seq.cons_left_injective Seq.cons_left_injective

theorem cons_right_injective (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _
#align seq.cons_right_injective Seq.cons_right_injective

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
def TerminatedAt (s : Seq α) (n : ℕ) : Prop :=
  s.nth n = none
#align seq.terminated_at Seq.TerminatedAt

/-- It is decidable whether a sequence terminates at a given position. -/
instance terminatedAtDecidable (s : Seq α) (n : ℕ) : Decidable (s.TerminatedAt n) :=
  decidable_of_iff' (s.nth n).isNone <| by unfold terminated_at <;> cases s.nth n <;> simp
#align seq.terminated_at_decidable Seq.terminatedAtDecidable

/-- A sequence terminates if there is some position `n` at which it has terminated. -/
def Terminates (s : Seq α) : Prop :=
  ∃ n : ℕ, s.TerminatedAt n
#align seq.terminates Seq.Terminates

theorem not_terminates_iff {s : Seq α} : ¬s.Terminates ↔ ∀ n, (s.nth n).isSome := by
  simp [terminates, terminated_at, ← Ne.def, Option.ne_none_iff_isSome]
#align seq.not_terminates_iff Seq.not_terminates_iff

/-- Functorial action of the functor `option (α × _)` -/
@[simp]
def omap (f : β → γ) : Option (α × β) → Option (α × γ)
  | none => none
  | some (a, b) => some (a, f b)
#align seq.omap Seq.omap

/-- Get the first element of a sequence -/
def head (s : Seq α) : Option α :=
  nth s 0
#align seq.head Seq.head

/-- Get the tail of a sequence (or `nil` if the sequence is `nil`) -/
def tail (s : Seq α) : Seq α :=
  ⟨s.1.tail, fun n => by
    cases' s with f al
    exact al⟩
#align seq.tail Seq.tail

protected def Mem (a : α) (s : Seq α) :=
  some a ∈ s.1
#align seq.mem Seq.Mem

instance : Membership α (Seq α) :=
  ⟨Seq.Mem⟩

theorem le_stable (s : Seq α) {m n} (h : m ≤ n) : s.nth m = none → s.nth n = none :=
  by
  cases' s with f al
  induction' h with n h IH
  exacts[id, fun h2 => al (IH h2)]
#align seq.le_stable Seq.le_stable

/-- If a sequence terminated at position `n`, it also terminated at `m ≥ n `. -/
theorem terminatedStable : ∀ (s : Seq α) {m n : ℕ}, m ≤ n → s.TerminatedAt m → s.TerminatedAt n :=
  le_stable
#align seq.terminated_stable Seq.terminatedStable

/-- If `s.nth n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such
that `s.nth = some aₘ` for `m ≤ n`.
-/
theorem ge_stable (s : Seq α) {aₙ : α} {n m : ℕ} (m_le_n : m ≤ n)
    (s_nth_eq_some : s.nth n = some aₙ) : ∃ aₘ : α, s.nth m = some aₘ :=
  have : s.nth n ≠ none := by simp [s_nth_eq_some]
  have : s.nth m ≠ none := mt (s.le_stable m_le_n) this
  Option.ne_none_iff_exists'.mp this
#align seq.ge_stable Seq.ge_stable

theorem not_mem_nil (a : α) : a ∉ @nil α := fun ⟨n, (h : some a = none)⟩ => by injection h
#align seq.not_mem_nil Seq.not_mem_nil

theorem mem_cons (a : α) : ∀ s : Seq α, a ∈ cons a s
  | ⟨f, al⟩ => Stream'.mem_cons (some a) _
#align seq.mem_cons Seq.mem_cons

theorem mem_cons_of_mem (y : α) {a : α} : ∀ {s : Seq α}, a ∈ s → a ∈ cons y s
  | ⟨f, al⟩ => Stream'.mem_cons_of_mem (some y)
#align seq.mem_cons_of_mem Seq.mem_cons_of_mem

theorem eq_or_mem_of_mem_cons {a b : α} : ∀ {s : Seq α}, a ∈ cons b s → a = b ∨ a ∈ s
  | ⟨f, al⟩, h => (Stream'.eq_or_mem_of_mem_cons h).imp_left fun h => by injection h
#align seq.eq_or_mem_of_mem_cons Seq.eq_or_mem_of_mem_cons

@[simp]
theorem mem_cons_iff {a b : α} {s : Seq α} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
  ⟨eq_or_mem_of_mem_cons, by rintro (rfl | m) <;> [apply mem_cons, exact mem_cons_of_mem _ m]⟩
#align seq.mem_cons_iff Seq.mem_cons_iff

/-- Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `cons a s`). -/
def destruct (s : Seq α) : Option (Seq1 α) :=
  (fun a' => (a', s.tail)) <$> nth s 0
#align seq.destruct Seq.destruct

theorem destruct_eq_nil {s : Seq α} : destruct s = none → s = nil :=
  by
  dsimp [destruct]
  induction' f0 : nth s 0 with <;> intro h
  · apply Subtype.eq
    funext n
    induction' n with n IH
    exacts[f0, s.2 IH]
  · contradiction
#align seq.destruct_eq_nil Seq.destruct_eq_nil

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `destruct_eq_cons [])
      (Command.declSig
       [(Term.implicitBinder "{" [`s] [":" (Term.app `Seq [`α])] "}")
        (Term.implicitBinder "{" [`a `s'] [] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         («term_=_»
          (Term.app `destruct [`s])
          "="
          (Term.app `some [(Term.tuple "(" [`a "," [`s']] ")")]))
         "→"
         («term_=_» `s "=" (Term.app `cons [`a `s'])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `destruct)] "]"] [])
           []
           (Tactic.«tactic_<;>_»
            (Tactic.induction'
             "induction'"
             [(Tactic.casesTarget [`f0 ":"] (Term.app `nth [`s (num "0")]))]
             []
             ["with" [(Lean.binderIdent `a')]]
             [])
            "<;>"
            (Tactic.intro "intro" [`h]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.contradiction "contradiction")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.cases'
              "cases'"
              [(Tactic.casesTarget [] `s)]
              []
              ["with" [(Lean.binderIdent `f) (Lean.binderIdent `al)]])
             []
             (Tactic.injections "injections" ["_" `h1 `h2])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h2)] "]")
              [])
             []
             (Tactic.apply "apply" `Subtype.eq)
             []
             (Tactic.dsimp
              "dsimp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] `tail) "," (Tactic.simpLemma [] [] `cons)] "]"]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`f0] []))])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `f0)] "]")
              [])
             []
             (Tactic.exact "exact" (Term.proj (Term.app `Stream'.eta [`f]) "." `symm))])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `destruct)] "]"] [])
          []
          (Tactic.«tactic_<;>_»
           (Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [`f0 ":"] (Term.app `nth [`s (num "0")]))]
            []
            ["with" [(Lean.binderIdent `a')]]
            [])
           "<;>"
           (Tactic.intro "intro" [`h]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.contradiction "contradiction")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.cases'
             "cases'"
             [(Tactic.casesTarget [] `s)]
             []
             ["with" [(Lean.binderIdent `f) (Lean.binderIdent `al)]])
            []
            (Tactic.injections "injections" ["_" `h1 `h2])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h2)] "]")
             [])
            []
            (Tactic.apply "apply" `Subtype.eq)
            []
            (Tactic.dsimp
             "dsimp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `tail) "," (Tactic.simpLemma [] [] `cons)] "]"]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`f0] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `f0)] "]")
             [])
            []
            (Tactic.exact "exact" (Term.proj (Term.app `Stream'.eta [`f]) "." `symm))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.cases'
         "cases'"
         [(Tactic.casesTarget [] `s)]
         []
         ["with" [(Lean.binderIdent `f) (Lean.binderIdent `al)]])
        []
        (Tactic.injections "injections" ["_" `h1 `h2])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h2)] "]")
         [])
        []
        (Tactic.apply "apply" `Subtype.eq)
        []
        (Tactic.dsimp
         "dsimp"
         []
         []
         []
         ["[" [(Tactic.simpLemma [] [] `tail) "," (Tactic.simpLemma [] [] `cons)] "]"]
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`f0] []))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `f0)] "]")
         [])
        []
        (Tactic.exact "exact" (Term.proj (Term.app `Stream'.eta [`f]) "." `symm))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.proj (Term.app `Stream'.eta [`f]) "." `symm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Stream'.eta [`f]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Stream'.eta [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Stream'.eta
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Stream'.eta [`f]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `f0)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`f0] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `tail) "," (Tactic.simpLemma [] [] `cons)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tail
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `Subtype.eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h2)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.injections "injections" ["_" `h1 `h2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '_', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '_', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  destruct_eq_cons
  { s : Seq α } { a s' } : destruct s = some ( a , s' ) → s = cons a s'
  :=
    by
      dsimp [ destruct ]
        induction' f0 : nth s 0 with a' <;> intro h
        · contradiction
        ·
          cases' s with f al
            injections _ h1 h2
            rw [ ← h2 ]
            apply Subtype.eq
            dsimp [ tail , cons ]
            rw [ h1 ] at f0
            rw [ ← f0 ]
            exact Stream'.eta f . symm
#align seq.destruct_eq_cons Seq.destruct_eq_cons

@[simp]
theorem destruct_nil : destruct (nil : Seq α) = none :=
  rfl
#align seq.destruct_nil Seq.destruct_nil

@[simp]
theorem destruct_cons (a : α) : ∀ s, destruct (cons a s) = some (a, s)
  | ⟨f, al⟩ => by
    unfold cons destruct Functor.map
    apply congr_arg fun s => some (a, s)
    apply Subtype.eq; dsimp [tail]; rw [Stream'.tail_cons]
#align seq.destruct_cons Seq.destruct_cons

theorem head_eq_destruct (s : Seq α) : head s = Prod.fst <$> destruct s := by
  unfold destruct head <;> cases nth s 0 <;> rfl
#align seq.head_eq_destruct Seq.head_eq_destruct

@[simp]
theorem head_nil : head (nil : Seq α) = none :=
  rfl
#align seq.head_nil Seq.head_nil

@[simp]
theorem head_cons (a : α) (s) : head (cons a s) = some a := by
  rw [head_eq_destruct, destruct_cons] <;> rfl
#align seq.head_cons Seq.head_cons

@[simp]
theorem tail_nil : tail (nil : Seq α) = nil :=
  rfl
#align seq.tail_nil Seq.tail_nil

@[simp]
theorem tail_cons (a : α) (s) : tail (cons a s) = s := by
  cases' s with f al <;> apply Subtype.eq <;> dsimp [tail, cons] <;> rw [Stream'.tail_cons]
#align seq.tail_cons Seq.tail_cons

@[simp]
theorem nth_tail (s : Seq α) (n) : nth (tail s) n = nth s (n + 1) :=
  rfl
#align seq.nth_tail Seq.nth_tail

/- warning: seq.rec_on clashes with has_seq.rec_on -> Seq.recOn
warning: seq.rec_on -> Seq.recOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {C : (Seq.{u} α) -> Sort.{v}} (s : Seq.{u} α), (C (Seq.nil.{u} α)) -> (forall (x : α) (s : Seq.{u} α), C (Seq.cons.{u} α x s)) -> (C s)
but is expected to have type
  forall {α : Type.{u} -> Type.{v}} {C : (Seq.{u, v} α) -> Sort.{u_1}} (s : Seq.{u, v} α), (forall (seq : forall {α_1 : Type.{u}} {β : Type.{u}}, (α (α_1 -> β)) -> (Unit -> (α α_1)) -> (α β)), C (Seq.mk.{u, v} α seq)) -> (C s)
Case conversion may be inaccurate. Consider using '#align seq.rec_on Seq.recOnₓ'. -/
/-- Recursion principle for sequences, compare with `list.rec_on`. -/
def recOn {C : Seq α → Sort v} (s : Seq α) (h1 : C nil) (h2 : ∀ x s, C (cons x s)) : C s :=
  by
  induction' H : destruct s with v v
  · rw [destruct_eq_nil H]
    apply h1
  · cases' v with a s'
    rw [destruct_eq_cons H]
    apply h2
#align seq.rec_on Seq.recOn

theorem memRecOn {C : Seq α → Prop} {a s} (M : a ∈ s) (h1 : ∀ b s', a = b ∨ C s' → C (cons b s')) :
    C s := by
  cases' M with k e; unfold Stream'.nth at e
  induction' k with k IH generalizing s
  · have TH : s = cons a (tail s) := by
      apply destruct_eq_cons
      unfold destruct nth Functor.map
      rw [← e]
      rfl
    rw [TH]
    apply h1 _ _ (Or.inl rfl)
  revert e; apply s.rec_on _ fun b s' => _ <;> intro e
  · injection e
  · have h_eq : (cons b s').val (Nat.succ k) = s'.val k := by cases s' <;> rfl
    rw [h_eq] at e
    apply h1 _ _ (Or.inr (IH e))
#align seq.mem_rec_on Seq.memRecOn

def Corec.f (f : β → Option (α × β)) : Option β → Option α × Option β
  | none => (none, none)
  | some b =>
    match f b with
    | none => (none, none)
    | some (a, b') => (some a, some b')
#align seq.corec.F Seq.Corec.f

/-- Corecursor for `seq α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
def corec (f : β → Option (α × β)) (b : β) : Seq α :=
  by
  refine' ⟨Stream'.corec' (corec.F f) (some b), fun n h => _⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (corec.F f) (corec.F f (some b)).2 n = none
  revert h; generalize some b = o; revert o
  induction' n with n IH <;> intro o
  · change (corec.F f o).1 = none → (corec.F f (corec.F f o).2).1 = none
    cases' o with b <;> intro h
    · rfl
    dsimp [corec.F] at h
    dsimp [corec.F]
    cases' f b with s
    · rfl
    · cases' s with a b'
      contradiction
  · rw [Stream'.corec'_eq (corec.F f) (corec.F f o).2, Stream'.corec'_eq (corec.F f) o]
    exact IH (corec.F f o).2
#align seq.corec Seq.corec

@[simp]
theorem corec_eq (f : β → Option (α × β)) (b : β) : destruct (corec f b) = omap (corec f) (f b) :=
  by
  dsimp [corec, destruct, nth]
  change Stream'.corec' (corec.F f) (some b) 0 with (corec.F f (some b)).1
  dsimp [corec.F]
  induction' h : f b with s; · rfl
  cases' s with a b'; dsimp [corec.F]
  apply congr_arg fun b' => some (a, b')
  apply Subtype.eq
  dsimp [corec, tail]
  rw [Stream'.corec'_eq, Stream'.tail_cons]
  dsimp [corec.F]; rw [h]; rfl
#align seq.corec_eq Seq.corec_eq

section Bisim

variable (R : Seq α → Seq α → Prop)

-- mathport name: R
local infixl:50 " ~ " => R

def BisimO : Option (Seq1 α) → Option (Seq1 α) → Prop
  | none, none => True
  | some (a, s), some (a', s') => a = a' ∧ R s s'
  | _, _ => False
#align seq.bisim_o Seq.BisimO

attribute [simp] bisim_o

def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → BisimO R (destruct s₁) (destruct s₂)
#align seq.is_bisimulation Seq.IsBisimulation

-- If two streams are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ :=
  by
  apply Subtype.eq
  apply Stream'.eq_of_bisim fun x y => ∃ s s' : Seq α, s.1 = x ∧ s'.1 = y ∧ R s s'
  dsimp [Stream'.IsBisimulation]
  intro t₁ t₂ e
  exact
    match t₁, t₂, e with
    | _, _, ⟨s, s', rfl, rfl, r⟩ =>
      by
      suffices head s = head s' ∧ R (tail s) (tail s') from
        And.imp id (fun r => ⟨tail s, tail s', by cases s <;> rfl, by cases s' <;> rfl, r⟩) this
      have := bisim r; revert r this
      apply rec_on s _ _ <;> intros <;> apply rec_on s' _ _ <;> intros <;> intro r this
      · constructor
        rfl
        assumption
      · rw [destruct_nil, destruct_cons] at this
        exact False.elim this
      · rw [destruct_nil, destruct_cons] at this
        exact False.elim this
      · rw [destruct_cons, destruct_cons] at this
        rw [head_cons, head_cons, tail_cons, tail_cons]
        cases' this with h1 h2
        constructor
        rw [h1]
        exact h2
  exact ⟨s₁, s₂, rfl, rfl, r⟩
#align seq.eq_of_bisim Seq.eq_of_bisim

end Bisim

theorem coinduction :
    ∀ {s₁ s₂ : Seq α},
      head s₁ = head s₂ →
        (∀ (β : Type u) (fr : Seq α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂
  | ⟨f₁, a₁⟩, ⟨f₂, a₂⟩, hh, ht =>
    Subtype.eq (Stream'.coinduction hh fun β fr => ht β fun s => fr s.1)
#align seq.coinduction Seq.coinduction

theorem coinduction2 (s) (f g : Seq α → Seq β)
    (H :
      ∀ s,
        BisimO (fun s1 s2 : Seq β => ∃ s : Seq α, s1 = f s ∧ s2 = g s) (destruct (f s))
          (destruct (g s))) :
    f s = g s :=
  by
  refine' eq_of_bisim (fun s1 s2 => ∃ s, s1 = f s ∧ s2 = g s) _ ⟨s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨s, h1, h2⟩
  rw [h1, h2]; apply H
#align seq.coinduction2 Seq.coinduction2

/-- Embed a list as a sequence -/
def ofList (l : List α) : Seq α :=
  ⟨List.get? l, fun n h => by
    rw [List.get?_eq_none] at h⊢
    exact h.trans (Nat.le_succ n)⟩
#align seq.of_list Seq.ofList

instance coeList : Coe (List α) (Seq α) :=
  ⟨ofList⟩
#align seq.coe_list Seq.coeList

@[simp]
theorem ofList_nil : ofList [] = (nil : Seq α) :=
  rfl
#align seq.of_list_nil Seq.ofList_nil

@[simp]
theorem ofList_nth (l : List α) (n : ℕ) : (ofList l).nth n = l.nth n :=
  rfl
#align seq.of_list_nth Seq.ofList_nth

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem ofList_cons (a : α) (l : List α) : ofList (a::l) = cons a (ofList l) := by
  ext1 (_ | n) <;> rfl
#align seq.of_list_cons Seq.ofList_cons

/-- Embed an infinite stream as a sequence -/
def ofStream (s : Stream' α) : Seq α :=
  ⟨s.map some, fun n h => by contradiction⟩
#align seq.of_stream Seq.ofStream

instance coeStream : Coe (Stream' α) (Seq α) :=
  ⟨ofStream⟩
#align seq.coe_stream Seq.coeStream

/-- Embed a `lazy_list α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `lazy_list`s created by meta constructions. -/
def ofLazyList : LazyList α → Seq α :=
  corec fun l =>
    match l with
    | LazyList.nil => none
    | LazyList.cons a l' => some (a, l' ())
#align seq.of_lazy_list Seq.ofLazyList

instance coeLazyList : Coe (LazyList α) (Seq α) :=
  ⟨ofLazyList⟩
#align seq.coe_lazy_list Seq.coeLazyList

/-- Translate a sequence into a `lazy_list`. Since `lazy_list` and `list`
  are isomorphic as non-meta types, this function is necessarily meta. -/
unsafe def to_lazy_list : Seq α → LazyList α
  | s =>
    match destruct s with
    | none => LazyList.nil
    | some (a, s') => LazyList.cons a (to_lazy_list s')
#align seq.to_lazy_list seq.to_lazy_list

/-- Translate a sequence to a list. This function will run forever if
  run on an infinite sequence. -/
unsafe def force_to_list (s : Seq α) : List α :=
  (to_lazy_list s).toList
#align seq.force_to_list seq.force_to_list

/-- The sequence of natural numbers some 0, some 1, ... -/
def nats : Seq ℕ :=
  Stream'.nats
#align seq.nats Seq.nats

@[simp]
theorem nats_nth (n : ℕ) : nats.nth n = some n :=
  rfl
#align seq.nats_nth Seq.nats_nth

/-- Append two sequences. If `s₁` is infinite, then `s₁ ++ s₂ = s₁`,
  otherwise it puts `s₂` at the location of the `nil` in `s₁`. -/
def append (s₁ s₂ : Seq α) : Seq α :=
  @corec α (Seq α × Seq α)
    (fun ⟨s₁, s₂⟩ =>
      match destruct s₁ with
      | none => omap (fun s₂ => (nil, s₂)) (destruct s₂)
      | some (a, s₁') => some (a, s₁', s₂))
    (s₁, s₂)
#align seq.append Seq.append

/-- Map a function over a sequence. -/
def map (f : α → β) : Seq α → Seq β
  | ⟨s, al⟩ =>
    ⟨s.map (Option.map f), fun n =>
      by
      dsimp [Stream'.map, Stream'.nth]
      induction' e : s n with <;> intro
      · rw [al e]
        assumption; · contradiction⟩
#align seq.map Seq.map

/-- Flatten a sequence of sequences. (It is required that the
  sequences be nonempty to ensure productivity; in the case
  of an infinite sequence of `nil`, the first element is never
  generated.) -/
def join : Seq (Seq1 α) → Seq α :=
  corec fun S =>
    match destruct S with
    | none => none
    | some ((a, s), S') =>
      some
        (a,
          match destruct s with
          | none => S'
          | some s' => cons s' S')
#align seq.join Seq.join

/-- Remove the first `n` elements from the sequence. -/
def drop (s : Seq α) : ℕ → Seq α
  | 0 => s
  | n + 1 => tail (drop n)
#align seq.drop Seq.drop

attribute [simp] drop

/-- Take the first `n` elements of the sequence (producing a list) -/
def take : ℕ → Seq α → List α
  | 0, s => []
  | n + 1, s =>
    match destruct s with
    | none => []
    | some (x, r) => List.cons x (take n r)
#align seq.take Seq.take

/-- Split a sequence at `n`, producing a finite initial segment
  and an infinite tail. -/
def splitAt : ℕ → Seq α → List α × Seq α
  | 0, s => ([], s)
  | n + 1, s =>
    match destruct s with
    | none => ([], nil)
    | some (x, s') =>
      let (l, r) := split_at n s'
      (List.cons x l, r)
#align seq.split_at Seq.splitAt

section ZipWith

/-- Combine two sequences with a function -/
def zipWith (f : α → β → γ) (s₁ : Seq α) (s₂ : Seq β) : Seq γ :=
  ⟨fun n => Option.map₂ f (s₁.nth n) (s₂.nth n), fun n hn =>
    Option.map₂_eq_none_iff.2 <| (Option.map₂_eq_none_iff.1 hn).imp s₁.2 s₂.2⟩
#align seq.zip_with Seq.zipWith

variable {s : Seq α} {s' : Seq β} {n : ℕ}

@[simp]
theorem nth_zipWith (f : α → β → γ) (s s' n) :
    (zipWith f s s').nth n = Option.map₂ f (s.nth n) (s'.nth n) :=
  rfl
#align seq.nth_zip_with Seq.nth_zipWith

end ZipWith

/-- Pair two sequences into a sequence of pairs -/
def zip : Seq α → Seq β → Seq (α × β) :=
  zipWith Prod.mk
#align seq.zip Seq.zip

theorem nth_zip (s : Seq α) (t : Seq β) (n : ℕ) :
    nth (zip s t) n = Option.map₂ Prod.mk (nth s n) (nth t n) :=
  nth_zipWith _ _ _ _
#align seq.nth_zip Seq.nth_zip

/-- Separate a sequence of pairs into two sequences -/
def unzip (s : Seq (α × β)) : Seq α × Seq β :=
  (map Prod.fst s, map Prod.snd s)
#align seq.unzip Seq.unzip

/-- Enumerate a sequence by tagging each element with its index. -/
def enum (s : Seq α) : Seq (ℕ × α) :=
  Seq.zip nats s
#align seq.enum Seq.enum

@[simp]
theorem nth_enum (s : Seq α) (n : ℕ) : nth (enum s) n = Option.map (Prod.mk n) (nth s n) :=
  nth_zip _ _ _
#align seq.nth_enum Seq.nth_enum

@[simp]
theorem enum_nil : enum (nil : Seq α) = nil :=
  rfl
#align seq.enum_nil Seq.enum_nil

/-- Convert a sequence which is known to terminate into a list -/
def toList (s : Seq α) (h : s.Terminates) : List α :=
  take (Nat.find h) s
#align seq.to_list Seq.toList

/-- Convert a sequence which is known not to terminate into a stream -/
def toStream (s : Seq α) (h : ¬s.Terminates) : Stream' α := fun n =>
  Option.get <| not_terminates_iff.1 h n
#align seq.to_stream Seq.toStream

/-- Convert a sequence into either a list or a stream depending on whether
  it is finite or infinite. (Without decidability of the infiniteness predicate,
  this is not constructively possible.) -/
def toListOrStream (s : Seq α) [Decidable s.Terminates] : Sum (List α) (Stream' α) :=
  if h : s.Terminates then Sum.inl (toList s h) else Sum.inr (toStream s h)
#align seq.to_list_or_stream Seq.toListOrStream

@[simp]
theorem nil_append (s : Seq α) : append nil s = s :=
  by
  apply coinduction2; intro s
  dsimp [append]; rw [corec_eq]
  dsimp [append]; apply rec_on s _ _
  · trivial
  · intro x s
    rw [destruct_cons]
    dsimp
    exact ⟨rfl, s, rfl, rfl⟩
#align seq.nil_append Seq.nil_append

@[simp]
theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
  destruct_eq_cons <| by
    dsimp [append]; rw [corec_eq]
    dsimp [append]; rw [destruct_cons]
    dsimp [append]; rfl
#align seq.cons_append Seq.cons_append

@[simp]
theorem append_nil (s : Seq α) : append s nil = s :=
  by
  apply coinduction2 s; intro s
  apply rec_on s _ _
  · trivial
  · intro x s
    rw [cons_append, destruct_cons, destruct_cons]
    dsimp
    exact ⟨rfl, s, rfl, rfl⟩
#align seq.append_nil Seq.append_nil

@[simp]
theorem append_assoc (s t u : Seq α) : append (append s t) u = append s (append t u) :=
  by
  apply eq_of_bisim fun s1 s2 => ∃ s t u, s1 = append (append s t) u ∧ s2 = append s (append t u)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, t, u, rfl, rfl⟩ => by
        apply rec_on s <;> simp
        · apply rec_on t <;> simp
          · apply rec_on u <;> simp
            · intro x u
              refine' ⟨nil, nil, u, _, _⟩ <;> simp
          · intro x t
            refine' ⟨nil, t, u, _, _⟩ <;> simp
        · intro x s
          exact ⟨s, t, u, rfl, rfl⟩
  · exact ⟨s, t, u, rfl, rfl⟩
#align seq.append_assoc Seq.append_assoc

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl
#align seq.map_nil Seq.map_nil

@[simp]
theorem map_cons (f : α → β) (a) : ∀ s, map f (cons a s) = cons (f a) (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq <;> dsimp [cons, map] <;> rw [Stream'.map_cons] <;> rfl
#align seq.map_cons Seq.map_cons

@[simp]
theorem map_id : ∀ s : Seq α, map id s = s
  | ⟨s, al⟩ => by
    apply Subtype.eq <;> dsimp [map]
    rw [Option.map_id, Stream'.map_id] <;> rfl
#align seq.map_id Seq.map_id

@[simp]
theorem map_tail (f : α → β) : ∀ s, map f (tail s) = tail (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq <;> dsimp [tail, map] <;> rw [Stream'.map_tail] <;> rfl
#align seq.map_tail Seq.map_tail

theorem map_comp (f : α → β) (g : β → γ) : ∀ s : Seq α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.eq <;> dsimp [map]
    rw [Stream'.map_map]
    apply congr_arg fun f : _ → Option γ => Stream'.map f s
    ext ⟨⟩ <;> rfl
#align seq.map_comp Seq.map_comp

@[simp]
theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) :=
  by
  apply
    eq_of_bisim (fun s1 s2 => ∃ s t, s1 = map f (append s t) ∧ s2 = append (map f s) (map f t)) _
      ⟨s, t, rfl, rfl⟩
  intro s1 s2 h;
  exact
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl⟩ => by
      apply rec_on s <;> simp
      · apply rec_on t <;> simp
        · intro x t
          refine' ⟨nil, t, _, _⟩ <;> simp
      · intro x s
        refine' ⟨s, t, rfl, rfl⟩
#align seq.map_append Seq.map_append

@[simp]
theorem map_nth (f : α → β) : ∀ s n, nth (map f s) n = (nth s n).map f
  | ⟨s, al⟩, n => rfl
#align seq.map_nth Seq.map_nth

instance : Functor Seq where map := @map

instance : LawfulFunctor Seq where
  id_map := @map_id
  comp_map := @map_comp

@[simp]
theorem join_nil : join nil = (nil : Seq α) :=
  destruct_eq_nil rfl
#align seq.join_nil Seq.join_nil

@[simp]
theorem join_cons_nil (a : α) (S) : join (cons (a, nil) S) = cons a (join S) :=
  destruct_eq_cons <| by simp [join]
#align seq.join_cons_nil Seq.join_cons_nil

@[simp]
theorem join_cons_cons (a b : α) (s S) :
    join (cons (a, cons b s) S) = cons a (join (cons (b, s) S)) :=
  destruct_eq_cons <| by simp [join]
#align seq.join_cons_cons Seq.join_cons_cons

@[simp]
theorem join_cons (a : α) (s S) : join (cons (a, s) S) = cons a (append s (join S)) :=
  by
  apply
    eq_of_bisim
      (fun s1 s2 => s1 = s2 ∨ ∃ a s S, s1 = join (cons (a, s) S) ∧ s2 = cons a (append s (join S)))
      _ (Or.inr ⟨a, s, S, rfl, rfl⟩)
  intro s1 s2 h
  exact
    match s1, s2, h with
    | _, _, Or.inl <| Eq.refl s => by
      apply rec_on s; · trivial
      · intro x s
        rw [destruct_cons]
        exact ⟨rfl, Or.inl rfl⟩
    | _, _, Or.inr ⟨a, s, S, rfl, rfl⟩ => by
      apply rec_on s
      · simp
      · intro x s
        simp
        refine' Or.inr ⟨x, s, S, rfl, rfl⟩
#align seq.join_cons Seq.join_cons

@[simp]
theorem join_append (S T : Seq (Seq1 α)) : join (append S T) = append (join S) (join T) :=
  by
  apply
    eq_of_bisim fun s1 s2 =>
      ∃ s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, T, rfl, rfl⟩ => by
        apply rec_on s <;> simp
        · apply rec_on S <;> simp
          · apply rec_on T
            · simp
            · intro s T
              cases' s with a s <;> simp
              refine' ⟨s, nil, T, _, _⟩ <;> simp
          · intro s S
            cases' s with a s <;> simp
            exact ⟨s, S, T, rfl, rfl⟩
        · intro x s
          exact ⟨s, S, T, rfl, rfl⟩
  · refine' ⟨nil, S, T, _, _⟩ <;> simp
#align seq.join_append Seq.join_append

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem ofStream_cons (a : α) (s) : ofStream (a::s) = cons a (ofStream s) := by
  apply Subtype.eq <;> simp [of_stream, cons] <;> rw [Stream'.map_cons]
#align seq.of_stream_cons Seq.ofStream_cons

@[simp]
theorem ofList_append (l l' : List α) : ofList (l ++ l') = append (ofList l) (ofList l') := by
  induction l <;> simp [*]
#align seq.of_list_append Seq.ofList_append

@[simp]
theorem ofStream_append (l : List α) (s : Stream' α) :
    ofStream (l ++ₛ s) = append (ofList l) (ofStream s) := by
  induction l <;> simp [*, Stream'.nil_append_stream, Stream'.cons_append_stream]
#align seq.of_stream_append Seq.ofStream_append

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Convert a sequence into a list, embedded in a computation to allow for
  the possibility of infinite sequences (in which case the computation
  never returns anything). -/
def toList' {α} (s : Seq α) : Computation (List α) :=
  @Computation.corec (List α) (List α × Seq α)
    (fun ⟨l, s⟩ =>
      match destruct s with
      | none => Sum.inl l.reverse
      | some (a, s') => Sum.inr (a::l, s'))
    ([], s)
#align seq.to_list' Seq.toList'

theorem dropn_add (s : Seq α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (dropn_add n)
#align seq.dropn_add Seq.dropn_add

theorem dropn_tail (s : Seq α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [add_comm] <;> symm <;> apply dropn_add
#align seq.dropn_tail Seq.dropn_tail

@[simp]
theorem head_dropn (s : Seq α) (n) : head (drop s n) = nth s n :=
  by
  induction' n with n IH generalizing s; · rfl
  rw [Nat.succ_eq_add_one, ← nth_tail, ← dropn_tail]; apply IH
#align seq.head_dropn Seq.head_dropn

theorem mem_map (f : α → β) {a : α} : ∀ {s : Seq α}, a ∈ s → f a ∈ map f s
  | ⟨g, al⟩ => Stream'.mem_map (Option.map f)
#align seq.mem_map Seq.mem_map

theorem exists_of_mem_map {f} {b : β} : ∀ {s : Seq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b
  | ⟨g, al⟩, h => by
    let ⟨o, om, oe⟩ := Stream'.exists_of_mem_map h
    cases' o with a <;> injection oe with h' <;> exact ⟨a, om, h'⟩
#align seq.exists_of_mem_map Seq.exists_of_mem_map

theorem of_mem_append {s₁ s₂ : Seq α} {a : α} (h : a ∈ append s₁ s₂) : a ∈ s₁ ∨ a ∈ s₂ :=
  by
  have := h; revert this
  generalize e : append s₁ s₂ = ss; intro h; revert s₁
  apply mem_rec_on h _
  intro b s' o s₁
  apply s₁.rec_on _ fun c t₁ => _ <;> intro m e <;> have := congr_arg destruct e
  · apply Or.inr
    simpa using m
  · cases' show a = c ∨ a ∈ append t₁ s₂ by simpa using m with e' m
    · rw [e']
      exact Or.inl (mem_cons _ _)
    · cases' show c = b ∧ append t₁ s₂ = s' by simpa with i1 i2
      cases' o with e' IH
      · simp [i1, e']
      · exact Or.imp_left (mem_cons_of_mem _) (IH m i2)
#align seq.of_mem_append Seq.of_mem_append

theorem mem_append_left {s₁ s₂ : Seq α} {a : α} (h : a ∈ s₁) : a ∈ append s₁ s₂ := by
  apply mem_rec_on h <;> intros <;> simp [*]
#align seq.mem_append_left Seq.mem_append_left

@[simp]
theorem enum_cons (s : Seq α) (x : α) :
    enum (cons x s) = cons (0, x) (map (Prod.map Nat.succ id) (enum s)) :=
  by
  ext ⟨n⟩ : 1
  · simp
  · simp only [nth_enum, nth_cons_succ, map_nth, Option.map_map]
    congr
#align seq.enum_cons Seq.enum_cons

end Seq

namespace Seq1

variable {α : Type u} {β : Type v} {γ : Type w}

open Seq

/-- Convert a `seq1` to a sequence. -/
def toSeq : Seq1 α → Seq α
  | (a, s) => cons a s
#align seq1.to_seq Seq1.toSeq

instance coeSeq : Coe (Seq1 α) (Seq α) :=
  ⟨toSeq⟩
#align seq1.coe_seq Seq1.coeSeq

/-- Map a function on a `seq1` -/
def map (f : α → β) : Seq1 α → Seq1 β
  | (a, s) => (f a, Seq.map f s)
#align seq1.map Seq1.map

theorem map_id : ∀ s : Seq1 α, map id s = s
  | ⟨a, s⟩ => by simp [map]
#align seq1.map_id Seq1.map_id

/-- Flatten a nonempty sequence of nonempty sequences -/
def join : Seq1 (Seq1 α) → Seq1 α
  | ((a, s), S) =>
    match destruct s with
    | none => (a, Seq.join S)
    | some s' => (a, Seq.join (cons s' S))
#align seq1.join Seq1.join

@[simp]
theorem join_nil (a : α) (S) : join ((a, nil), S) = (a, Seq.join S) :=
  rfl
#align seq1.join_nil Seq1.join_nil

@[simp]
theorem join_cons (a b : α) (s S) : join ((a, cons b s), S) = (a, Seq.join (cons (b, s) S)) := by
  dsimp [join] <;> rw [destruct_cons] <;> rfl
#align seq1.join_cons Seq1.join_cons

/-- The `return` operator for the `seq1` monad,
  which produces a singleton sequence. -/
def ret (a : α) : Seq1 α :=
  (a, nil)
#align seq1.ret Seq1.ret

instance [Inhabited α] : Inhabited (Seq1 α) :=
  ⟨ret default⟩

/-- The `bind` operator for the `seq1` monad,
  which maps `f` on each element of `s` and appends the results together.
  (Not all of `s` may be evaluated, because the first few elements of `s`
  may already produce an infinite result.) -/
def bind (s : Seq1 α) (f : α → Seq1 β) : Seq1 β :=
  join (map f s)
#align seq1.bind Seq1.bind

@[simp]
theorem join_map_ret (s : Seq α) : Seq.join (Seq.map ret s) = s := by
  apply coinduction2 s <;> intro s <;> apply rec_on s <;> simp [ret]
#align seq1.join_map_ret Seq1.join_map_ret

@[simp]
theorem bind_ret (f : α → β) : ∀ s, bind s (ret ∘ f) = map f s
  | ⟨a, s⟩ => by
    dsimp [bind, map]; change fun x => ret (f x) with ret ∘ f
    rw [map_comp]; simp [Function.comp, ret]
#align seq1.bind_ret Seq1.bind_ret

@[simp]
theorem ret_bind (a : α) (f : α → Seq1 β) : bind (ret a) f = f a :=
  by
  simp [ret, bind, map]
  cases' f a with a s
  apply rec_on s <;> intros <;> simp
#align seq1.ret_bind Seq1.ret_bind

@[simp]
theorem map_join' (f : α → β) (S) : Seq.map f (Seq.join S) = Seq.join (Seq.map (map f) S) :=
  by
  apply
    eq_of_bisim fun s1 s2 =>
      ∃ s S, s1 = append s (Seq.map f (Seq.join S)) ∧ s2 = append s (Seq.join (Seq.map (map f) S))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, rfl, rfl⟩ => by
        apply rec_on s <;> simp
        · apply rec_on S <;> simp
          · intro x S
            cases' x with a s <;> simp [map]
            exact ⟨_, _, rfl, rfl⟩
        · intro x s
          refine' ⟨s, S, rfl, rfl⟩
  · refine' ⟨nil, S, _, _⟩ <;> simp
#align seq1.map_join' Seq1.map_join'

@[simp]
theorem map_join (f : α → β) : ∀ S, map f (join S) = join (map (map f) S)
  | ((a, s), S) => by apply rec_on s <;> intros <;> simp [map]
#align seq1.map_join Seq1.map_join

@[simp]
theorem join_join (SS : Seq (Seq1 (Seq1 α))) :
    Seq.join (Seq.join SS) = Seq.join (Seq.map join SS) :=
  by
  apply
    eq_of_bisim fun s1 s2 =>
      ∃ s SS,
        s1 = Seq.append s (Seq.join (Seq.join SS)) ∧ s2 = Seq.append s (Seq.join (Seq.map join SS))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, SS, rfl, rfl⟩ => by
        apply rec_on s <;> simp
        · apply rec_on SS <;> simp
          · intro S SS
            cases' S with s S <;> cases' s with x s <;> simp [map]
            apply rec_on s <;> simp
            · exact ⟨_, _, rfl, rfl⟩
            · intro x s
              refine' ⟨cons x (append s (Seq.join S)), SS, _, _⟩ <;> simp
        · intro x s
          exact ⟨s, SS, rfl, rfl⟩
  · refine' ⟨nil, SS, _, _⟩ <;> simp
#align seq1.join_join Seq1.join_join

@[simp]
theorem bind_assoc (s : Seq1 α) (f : α → Seq1 β) (g : β → Seq1 γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g :=
  by
  cases' s with a s
  simp [bind, map]
  rw [← map_comp]
  change fun x => join (map g (f x)) with join ∘ map g ∘ f
  rw [map_comp _ join]
  generalize Seq.map (map g ∘ f) s = SS
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩
  apply rec_on s <;> intros <;> apply rec_on S <;> intros <;> simp
  · cases' x with x t
    apply rec_on t <;> intros <;> simp
  · cases' x_1 with y t <;> simp
#align seq1.bind_assoc Seq1.bind_assoc

instance : Monad Seq1 where
  map := @map
  pure := @ret
  bind := @bind

instance : LawfulMonad Seq1 where
  id_map := @map_id
  bind_pure_comp_eq_map := @bind_ret
  pure_bind := @ret_bind
  bind_assoc := @bind_assoc

end Seq1

