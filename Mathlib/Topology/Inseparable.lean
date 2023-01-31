/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.inseparable
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.ContinuousOn
import Mathbin.Data.Setoid.Basic
import Mathbin.Tactic.Tfae

/-!
# Inseparable points in a topological space

In this file we define

* `specializes` (notation: `x ⤳ y`) : a relation saying that `𝓝 x ≤ 𝓝 y`;

* `inseparable`: a relation saying that two points in a topological space have the same
  neighbourhoods; equivalently, they can't be separated by an open set;

* `inseparable_setoid X`: same relation, as a `setoid`;

* `separation_quotient X`: the quotient of `X` by its `inseparable_setoid`.

We also prove various basic properties of the relation `inseparable`.

## Notations

- `x ⤳ y`: notation for `specializes x y`;
- `x ~ y` is used as a local notation for `inseparable x y`;
- `𝓝 x` is the neighbourhoods filter `nhds x` of a point `x`, defined elsewhere.

## Tags

topological space, separation setoid
-/


open Set Filter Function

open Topology Filter

variable {X Y Z α ι : Type _} {π : ι → Type _} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [∀ i, TopologicalSpace (π i)] {x y z : X} {s : Set X} {f : X → Y}

/-!
### `specializes` relation
-/


/-- `x` specializes to `y` (notation: `x ⤳ y`) if either of the following equivalent properties
hold:

* `𝓝 x ≤ 𝓝 y`; this property is used as the definition;
* `pure x ≤ 𝓝 y`; in other words, any neighbourhood of `y` contains `x`;
* `y ∈ closure {x}`;
* `closure {y} ⊆ closure {x}`;
* for any closed set `s` we have `x ∈ s → y ∈ s`;
* for any open set `s` we have `y ∈ s → x ∈ s`;
* `y` is a cluster point of the filter `pure x = 𝓟 {x}`.

This relation defines a `preorder` on `X`. If `X` is a T₀ space, then this preorder is a partial
order. If `X` is a T₁ space, then this partial order is trivial : `x ⤳ y ↔ x = y`. -/
def Specializes (x y : X) : Prop :=
  𝓝 x ≤ 𝓝 y
#align specializes Specializes

-- mathport name: «expr ⤳ »
infixl:300 " ⤳ " => Specializes

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A collection of equivalent definitions of `x ⤳ y`. The public API is given by `iff` lemmas\nbelow. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `specializes_tFAE [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `X] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `TFAE
         [(«term[_]»
           "["
           [(Topology.Inseparable.«term_⤳_» `x " ⤳ " `y)
            ","
            («term_≤_» (Term.app `pure [`x]) "≤" (Term.app (Topology.Topology.Basic.nhds "𝓝") [`y]))
            ","
            (Term.forall
             "∀"
             [`s]
             [(Term.typeSpec ":" (Term.app `Set [`X]))]
             ","
             (Term.arrow
              (Term.app `IsOpen [`s])
              "→"
              (Term.arrow («term_∈_» `y "∈" `s) "→" («term_∈_» `x "∈" `s))))
            ","
            (Term.forall
             "∀"
             [`s]
             [(Term.typeSpec ":" (Term.app `Set [`X]))]
             ","
             (Term.arrow
              (Term.app `IsClosed [`s])
              "→"
              (Term.arrow («term_∈_» `x "∈" `s) "→" («term_∈_» `y "∈" `s))))
            ","
            («term_∈_»
             `y
             "∈"
             (Term.app
              `closure
              [(Term.typeAscription "(" («term{_}» "{" [`x] "}") ":" [(Term.app `Set [`X])] ")")]))
            ","
            («term_⊆_»
             (Term.app
              `closure
              [(Term.typeAscription "(" («term{_}» "{" [`y] "}") ":" [(Term.app `Set [`X])] ")")])
             "⊆"
             (Term.app `closure [(«term{_}» "{" [`x] "}")]))
            ","
            (Term.app `ClusterPt [`y (Term.app `pure [`x])])]
           "]")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "2"))
           ";"
           (Tactic.exact "exact" (Term.proj (Term.app `pure_le_nhds [(Term.hole "_")]) "." `trans))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "3"))
           ";"
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [`h `s `hso `hy]
              []
              "=>"
              (Term.app `h [(Term.app (Term.proj `hso "." `mem_nhds) [`hy])]))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "4"))
           ";"
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [`h `s `hsc `hx]
              []
              "=>"
              (Term.app
               `of_not_not
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`hy]
                  []
                  "=>"
                  (Term.app
                   `h
                   [(Order.Basic.«term_ᶜ» `s "ᶜ")
                    (Term.proj `hsc "." `is_open_compl)
                    `hy
                    `hx])))]))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "5"))
           ";"
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [`h]
              []
              "=>"
              (Term.app
               `h
               [(Term.hole "_")
                `isClosed_closure
                («term_<|_» `subset_closure "<|" (Term.app `mem_singleton [(Term.hole "_")]))]))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "6") "↔" (num "5"))
           ";"
           (Tactic.exact
            "exact"
            (Term.app `is_closed_closure.closure_subset_iff.trans [`singleton_subset_iff]))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "5") "↔" (num "7"))
           ";"
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `mem_closure_iff_clusterPt)
                ","
                (Tactic.rwRule [] `principal_singleton)]
               "]")
              [])])
           []
           (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "1"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.refine'
              "refine'"
              (Term.fun
               "fun"
               (Term.basicFun
                [`h]
                []
                "=>"
                (Term.app
                 (Term.proj
                  (Term.proj (Term.app `nhds_basis_opens [(Term.hole "_")]) "." `ge_iff)
                  "."
                  (fieldIdx "2"))
                 [(Term.hole "_")]))))
             []
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `s))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ho)])
                   [])]
                 "⟩"))]
              [])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app (Term.proj `mem_closure_iff "." (fieldIdx "1")) [`h `s `ho `hy]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxs)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                     [":" («term_=_» `z "=" `x)])]
                   "⟩")])
                [])])
             []
             (Tactic.exact "exact" (Term.app `ho.mem_nhds [`hxs]))])
           []
           (Tactic.tfaeFinish "tfae_finish")])))
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
         [(Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "2"))
          ";"
          (Tactic.exact "exact" (Term.proj (Term.app `pure_le_nhds [(Term.hole "_")]) "." `trans))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "3"))
          ";"
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [`h `s `hso `hy]
             []
             "=>"
             (Term.app `h [(Term.app (Term.proj `hso "." `mem_nhds) [`hy])]))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "4"))
          ";"
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [`h `s `hsc `hx]
             []
             "=>"
             (Term.app
              `of_not_not
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`hy]
                 []
                 "=>"
                 (Term.app
                  `h
                  [(Order.Basic.«term_ᶜ» `s "ᶜ")
                   (Term.proj `hsc "." `is_open_compl)
                   `hy
                   `hx])))]))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "5"))
          ";"
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [`h]
             []
             "=>"
             (Term.app
              `h
              [(Term.hole "_")
               `isClosed_closure
               («term_<|_» `subset_closure "<|" (Term.app `mem_singleton [(Term.hole "_")]))]))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "6") "↔" (num "5"))
          ";"
          (Tactic.exact
           "exact"
           (Term.app `is_closed_closure.closure_subset_iff.trans [`singleton_subset_iff]))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "5") "↔" (num "7"))
          ";"
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `mem_closure_iff_clusterPt)
               ","
               (Tactic.rwRule [] `principal_singleton)]
              "]")
             [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "1"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.fun
              "fun"
              (Term.basicFun
               [`h]
               []
               "=>"
               (Term.app
                (Term.proj
                 (Term.proj (Term.app `nhds_basis_opens [(Term.hole "_")]) "." `ge_iff)
                 "."
                 (fieldIdx "2"))
                [(Term.hole "_")]))))
            []
            (Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `s))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ho)])
                  [])]
                "⟩"))]
             [])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app (Term.proj `mem_closure_iff "." (fieldIdx "1")) [`h `s `ho `hy]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxs)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [":" («term_=_» `z "=" `x)])]
                  "⟩")])
               [])])
            []
            (Tactic.exact "exact" (Term.app `ho.mem_nhds [`hxs]))])
          []
          (Tactic.tfaeFinish "tfae_finish")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeFinish "tfae_finish")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.app
            (Term.proj
             (Term.proj (Term.app `nhds_basis_opens [(Term.hole "_")]) "." `ge_iff)
             "."
             (fieldIdx "2"))
            [(Term.hole "_")]))))
        []
        (Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `s))
          (Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ho)])
              [])]
            "⟩"))]
         [])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app (Term.proj `mem_closure_iff "." (fieldIdx "1")) [`h `s `ho `hy]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxs)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [":" («term_=_» `z "=" `x)])]
              "⟩")])
           [])])
        []
        (Tactic.exact "exact" (Term.app `ho.mem_nhds [`hxs]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `ho.mem_nhds [`hxs]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ho.mem_nhds [`hxs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ho.mem_nhds
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app (Term.proj `mem_closure_iff "." (fieldIdx "1")) [`h `s `ho `hy]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxs)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
              [":" («term_=_» `z "=" `x)])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `z "=" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `mem_closure_iff "." (fieldIdx "1")) [`h `s `ho `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ho
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `mem_closure_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `mem_closure_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `s))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ho)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.fun
        "fun"
        (Term.basicFun
         [`h]
         []
         "=>"
         (Term.app
          (Term.proj
           (Term.proj (Term.app `nhds_basis_opens [(Term.hole "_")]) "." `ge_iff)
           "."
           (fieldIdx "2"))
          [(Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.app
         (Term.proj
          (Term.proj (Term.app `nhds_basis_opens [(Term.hole "_")]) "." `ge_iff)
          "."
          (fieldIdx "2"))
         [(Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj (Term.app `nhds_basis_opens [(Term.hole "_")]) "." `ge_iff)
        "."
        (fieldIdx "2"))
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj (Term.app `nhds_basis_opens [(Term.hole "_")]) "." `ge_iff)
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `nhds_basis_opens [(Term.hole "_")]) "." `ge_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `nhds_basis_opens [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nhds_basis_opens
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `nhds_basis_opens [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« → »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« ↔ »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« ← »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    A collection of equivalent definitions of `x ⤳ y`. The public API is given by `iff` lemmas
    below. -/
  theorem
    specializes_tFAE
    ( x y : X )
      :
        TFAE
          [
            x ⤳ y
              ,
              pure x ≤ 𝓝 y
              ,
              ∀ s : Set X , IsOpen s → y ∈ s → x ∈ s
              ,
              ∀ s : Set X , IsClosed s → x ∈ s → y ∈ s
              ,
              y ∈ closure ( { x } : Set X )
              ,
              closure ( { y } : Set X ) ⊆ closure { x }
              ,
              ClusterPt y pure x
            ]
    :=
      by
        tfae_have 1 → 2
          ;
          exact pure_le_nhds _ . trans
          tfae_have 2 → 3
          ;
          exact fun h s hso hy => h hso . mem_nhds hy
          tfae_have 3 → 4
          ;
          exact fun h s hsc hx => of_not_not fun hy => h s ᶜ hsc . is_open_compl hy hx
          tfae_have 4 → 5
          ;
          exact fun h => h _ isClosed_closure subset_closure <| mem_singleton _
          tfae_have 6 ↔ 5
          ;
          exact is_closed_closure.closure_subset_iff.trans singleton_subset_iff
          tfae_have 5 ↔ 7
          ;
          · rw [ mem_closure_iff_clusterPt , principal_singleton ]
          tfae_have 5 → 1
          ·
            refine' fun h => nhds_basis_opens _ . ge_iff . 2 _
              rintro s ⟨ hy , ho ⟩
              rcases mem_closure_iff . 1 h s ho hy with ⟨ z , hxs , rfl : z = x ⟩
              exact ho.mem_nhds hxs
          tfae_finish
#align specializes_tfae specializes_tFAE

theorem specializes_iff_nhds : x ⤳ y ↔ 𝓝 x ≤ 𝓝 y :=
  Iff.rfl
#align specializes_iff_nhds specializes_iff_nhds

theorem specializes_iff_pure : x ⤳ y ↔ pure x ≤ 𝓝 y :=
  (specializes_tFAE x y).out 0 1
#align specializes_iff_pure specializes_iff_pure

alias specializes_iff_nhds ↔ Specializes.nhds_le_nhds _
#align specializes.nhds_le_nhds Specializes.nhds_le_nhds

alias specializes_iff_pure ↔ Specializes.pure_le_nhds _
#align specializes.pure_le_nhds Specializes.pure_le_nhds

theorem specializes_iff_forall_open : x ⤳ y ↔ ∀ s : Set X, IsOpen s → y ∈ s → x ∈ s :=
  (specializes_tFAE x y).out 0 2
#align specializes_iff_forall_open specializes_iff_forall_open

theorem Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (hy : y ∈ s) : x ∈ s :=
  specializes_iff_forall_open.1 h s hs hy
#align specializes.mem_open Specializes.mem_open

theorem IsOpen.not_specializes (hs : IsOpen s) (hx : x ∉ s) (hy : y ∈ s) : ¬x ⤳ y := fun h =>
  hx <| h.mem_open hs hy
#align is_open.not_specializes IsOpen.not_specializes

theorem specializes_iff_forall_closed : x ⤳ y ↔ ∀ s : Set X, IsClosed s → x ∈ s → y ∈ s :=
  (specializes_tFAE x y).out 0 3
#align specializes_iff_forall_closed specializes_iff_forall_closed

theorem Specializes.mem_closed (h : x ⤳ y) (hs : IsClosed s) (hx : x ∈ s) : y ∈ s :=
  specializes_iff_forall_closed.1 h s hs hx
#align specializes.mem_closed Specializes.mem_closed

theorem IsClosed.not_specializes (hs : IsClosed s) (hx : x ∈ s) (hy : y ∉ s) : ¬x ⤳ y := fun h =>
  hy <| h.mem_closed hs hx
#align is_closed.not_specializes IsClosed.not_specializes

theorem specializes_iff_mem_closure : x ⤳ y ↔ y ∈ closure ({x} : Set X) :=
  (specializes_tFAE x y).out 0 4
#align specializes_iff_mem_closure specializes_iff_mem_closure

alias specializes_iff_mem_closure ↔ Specializes.mem_closure _
#align specializes.mem_closure Specializes.mem_closure

theorem specializes_iff_closure_subset : x ⤳ y ↔ closure ({y} : Set X) ⊆ closure {x} :=
  (specializes_tFAE x y).out 0 5
#align specializes_iff_closure_subset specializes_iff_closure_subset

alias specializes_iff_closure_subset ↔ Specializes.closure_subset _
#align specializes.closure_subset Specializes.closure_subset

theorem Filter.HasBasis.specializes_iff {ι} {p : ι → Prop} {s : ι → Set X}
    (h : (𝓝 y).HasBasis p s) : x ⤳ y ↔ ∀ i, p i → x ∈ s i :=
  specializes_iff_pure.trans h.ge_iff
#align filter.has_basis.specializes_iff Filter.HasBasis.specializes_iff

theorem specializes_rfl : x ⤳ x :=
  le_rfl
#align specializes_rfl specializes_rfl

@[refl]
theorem specializes_refl (x : X) : x ⤳ x :=
  specializes_rfl
#align specializes_refl specializes_refl

@[trans]
theorem Specializes.trans : x ⤳ y → y ⤳ z → x ⤳ z :=
  le_trans
#align specializes.trans Specializes.trans

theorem specializes_of_eq (e : x = y) : x ⤳ y :=
  e ▸ specializes_refl x
#align specializes_of_eq specializes_of_eq

theorem specializes_of_nhdsWithin (h₁ : 𝓝[s] x ≤ 𝓝[s] y) (h₂ : x ∈ s) : x ⤳ y :=
  specializes_iff_pure.2 <|
    calc
      pure x ≤ 𝓝[s] x := le_inf (pure_le_nhds _) (le_principal_iff.2 h₂)
      _ ≤ 𝓝[s] y := h₁
      _ ≤ 𝓝 y := inf_le_left
      
#align specializes_of_nhds_within specializes_of_nhdsWithin

theorem Specializes.map_of_continuousAt (h : x ⤳ y) (hy : ContinuousAt f y) : f x ⤳ f y :=
  specializes_iff_pure.2 fun s hs =>
    mem_pure.2 <| mem_preimage.1 <| mem_of_mem_nhds <| hy.mono_left h hs
#align specializes.map_of_continuous_at Specializes.map_of_continuousAt

theorem Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳ f y :=
  h.map_of_continuous_at hf.ContinuousAt
#align specializes.map Specializes.map

theorem Inducing.specializes_iff (hf : Inducing f) : f x ⤳ f y ↔ x ⤳ y := by
  simp only [specializes_iff_mem_closure, hf.closure_eq_preimage_closure_image, image_singleton,
    mem_preimage]
#align inducing.specializes_iff Inducing.specializes_iff

theorem subtype_specializes_iff {p : X → Prop} (x y : Subtype p) : x ⤳ y ↔ (x : X) ⤳ y :=
  inducing_coe.specializes_iff.symm
#align subtype_specializes_iff subtype_specializes_iff

@[simp]
theorem specializes_prod {x₁ x₂ : X} {y₁ y₂ : Y} : (x₁, y₁) ⤳ (x₂, y₂) ↔ x₁ ⤳ x₂ ∧ y₁ ⤳ y₂ := by
  simp only [Specializes, nhds_prod_eq, prod_le_prod]
#align specializes_prod specializes_prod

theorem Specializes.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ⤳ x₂) (hy : y₁ ⤳ y₂) :
    (x₁, y₁) ⤳ (x₂, y₂) :=
  specializes_prod.2 ⟨hx, hy⟩
#align specializes.prod Specializes.prod

@[simp]
theorem specializes_pi {f g : ∀ i, π i} : f ⤳ g ↔ ∀ i, f i ⤳ g i := by
  simp only [Specializes, nhds_pi, pi_le_pi]
#align specializes_pi specializes_pi

theorem not_specializes_iff_exists_open : ¬x ⤳ y ↔ ∃ S : Set X, IsOpen S ∧ y ∈ S ∧ x ∉ S :=
  by
  rw [specializes_iff_forall_open]
  push_neg
  rfl
#align not_specializes_iff_exists_open not_specializes_iff_exists_open

theorem not_specializes_iff_exists_closed : ¬x ⤳ y ↔ ∃ S : Set X, IsClosed S ∧ x ∈ S ∧ y ∉ S :=
  by
  rw [specializes_iff_forall_closed]
  push_neg
  rfl
#align not_specializes_iff_exists_closed not_specializes_iff_exists_closed

variable (X)

/-- Specialization forms a preorder on the topological space. -/
def specializationPreorder : Preorder X :=
  {
    Preorder.lift (OrderDual.toDual ∘
        𝓝) with
    le := fun x y => y ⤳ x
    lt := fun x y => y ⤳ x ∧ ¬x ⤳ y }
#align specialization_preorder specializationPreorder

variable {X}

/-- A continuous function is monotone with respect to the specialization preorders on the domain and
the codomain. -/
theorem Continuous.specialization_monotone (hf : Continuous f) :
    @Monotone _ _ (specializationPreorder X) (specializationPreorder Y) f := fun x y h => h.map hf
#align continuous.specialization_monotone Continuous.specialization_monotone

/-!
### `inseparable` relation
-/


/-- Two points `x` and `y` in a topological space are `inseparable` if any of the following
equivalent properties hold:

- `𝓝 x = 𝓝 y`; we use this property as the definition;
- for any open set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_open`;
- for any closed set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_closed`;
- `x ∈ closure {y}` and `y ∈ closure {x}`, see `inseparable_iff_mem_closure`;
- `closure {x} = closure {y}`, see `inseparable_iff_closure_eq`.
-/
def Inseparable (x y : X) : Prop :=
  𝓝 x = 𝓝 y
#align inseparable Inseparable

-- mathport name: «expr ~ »
local infixl:0 " ~ " => Inseparable

theorem inseparable_def : (x ~ y) ↔ 𝓝 x = 𝓝 y :=
  Iff.rfl
#align inseparable_def inseparable_def

theorem inseparable_iff_specializes_and : (x ~ y) ↔ x ⤳ y ∧ y ⤳ x :=
  le_antisymm_iff
#align inseparable_iff_specializes_and inseparable_iff_specializes_and

theorem Inseparable.specializes (h : x ~ y) : x ⤳ y :=
  h.le
#align inseparable.specializes Inseparable.specializes

theorem Inseparable.specializes' (h : x ~ y) : y ⤳ x :=
  h.ge
#align inseparable.specializes' Inseparable.specializes'

theorem Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x ~ y :=
  le_antisymm h₁ h₂
#align specializes.antisymm Specializes.antisymm

theorem inseparable_iff_forall_open : (x ~ y) ↔ ∀ s : Set X, IsOpen s → (x ∈ s ↔ y ∈ s) := by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_open, ← forall_and, ← iff_def,
    Iff.comm]
#align inseparable_iff_forall_open inseparable_iff_forall_open

theorem not_inseparable_iff_exists_open : ¬(x ~ y) ↔ ∃ s : Set X, IsOpen s ∧ Xor' (x ∈ s) (y ∈ s) :=
  by simp [inseparable_iff_forall_open, ← xor_iff_not_iff]
#align not_inseparable_iff_exists_open not_inseparable_iff_exists_open

theorem inseparable_iff_forall_closed : (x ~ y) ↔ ∀ s : Set X, IsClosed s → (x ∈ s ↔ y ∈ s) := by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_closed, ← forall_and, ←
    iff_def]
#align inseparable_iff_forall_closed inseparable_iff_forall_closed

theorem inseparable_iff_mem_closure :
    (x ~ y) ↔ x ∈ closure ({y} : Set X) ∧ y ∈ closure ({x} : Set X) :=
  inseparable_iff_specializes_and.trans <| by simp only [specializes_iff_mem_closure, and_comm']
#align inseparable_iff_mem_closure inseparable_iff_mem_closure

theorem inseparable_iff_closure_eq : (x ~ y) ↔ closure ({x} : Set X) = closure {y} := by
  simp only [inseparable_iff_specializes_and, specializes_iff_closure_subset, ← subset_antisymm_iff,
    eq_comm]
#align inseparable_iff_closure_eq inseparable_iff_closure_eq

theorem inseparable_of_nhdsWithin_eq (hx : x ∈ s) (hy : y ∈ s) (h : 𝓝[s] x = 𝓝[s] y) : x ~ y :=
  (specializes_of_nhdsWithin h.le hx).antisymm (specializes_of_nhdsWithin h.ge hy)
#align inseparable_of_nhds_within_eq inseparable_of_nhdsWithin_eq

theorem Inducing.inseparable_iff (hf : Inducing f) : (f x ~ f y) ↔ (x ~ y) := by
  simp only [inseparable_iff_specializes_and, hf.specializes_iff]
#align inducing.inseparable_iff Inducing.inseparable_iff

theorem subtype_inseparable_iff {p : X → Prop} (x y : Subtype p) : (x ~ y) ↔ ((x : X) ~ y) :=
  inducing_coe.inseparable_iff.symm
#align subtype_inseparable_iff subtype_inseparable_iff

@[simp]
theorem inseparable_prod {x₁ x₂ : X} {y₁ y₂ : Y} : ((x₁, y₁) ~ (x₂, y₂)) ↔ (x₁ ~ x₂) ∧ (y₁ ~ y₂) :=
  by simp only [Inseparable, nhds_prod_eq, prod_inj]
#align inseparable_prod inseparable_prod

theorem Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ x₂) (hy : y₁ ~ y₂) :
    (x₁, y₁) ~ (x₂, y₂) :=
  inseparable_prod.2 ⟨hx, hy⟩
#align inseparable.prod Inseparable.prod

@[simp]
theorem inseparable_pi {f g : ∀ i, π i} : (f ~ g) ↔ ∀ i, f i ~ g i := by
  simp only [Inseparable, nhds_pi, funext_iff, pi_inj]
#align inseparable_pi inseparable_pi

namespace Inseparable

@[refl]
theorem refl (x : X) : x ~ x :=
  Eq.refl (𝓝 x)
#align inseparable.refl Inseparable.refl

theorem rfl : x ~ x :=
  refl x
#align inseparable.rfl Inseparable.rfl

theorem of_eq (e : x = y) : Inseparable x y :=
  e ▸ refl x
#align inseparable.of_eq Inseparable.of_eq

@[symm]
theorem symm (h : x ~ y) : y ~ x :=
  h.symm
#align inseparable.symm Inseparable.symm

@[trans]
theorem trans (h₁ : x ~ y) (h₂ : y ~ z) : x ~ z :=
  h₁.trans h₂
#align inseparable.trans Inseparable.trans

theorem nhds_eq (h : x ~ y) : 𝓝 x = 𝓝 y :=
  h
#align inseparable.nhds_eq Inseparable.nhds_eq

theorem mem_open_iff (h : x ~ y) (hs : IsOpen s) : x ∈ s ↔ y ∈ s :=
  inseparable_iff_forall_open.1 h s hs
#align inseparable.mem_open_iff Inseparable.mem_open_iff

theorem mem_closed_iff (h : x ~ y) (hs : IsClosed s) : x ∈ s ↔ y ∈ s :=
  inseparable_iff_forall_closed.1 h s hs
#align inseparable.mem_closed_iff Inseparable.mem_closed_iff

theorem map_of_continuousAt (h : x ~ y) (hx : ContinuousAt f x) (hy : ContinuousAt f y) :
    f x ~ f y :=
  (h.Specializes.map_of_continuous_at hy).antisymm (h.specializes'.map_of_continuous_at hx)
#align inseparable.map_of_continuous_at Inseparable.map_of_continuousAt

theorem map (h : x ~ y) (hf : Continuous f) : f x ~ f y :=
  h.map_of_continuous_at hf.ContinuousAt hf.ContinuousAt
#align inseparable.map Inseparable.map

end Inseparable

theorem IsClosed.not_inseparable (hs : IsClosed s) (hx : x ∈ s) (hy : y ∉ s) : ¬(x ~ y) := fun h =>
  hy <| (h.mem_closed_iff hs).1 hx
#align is_closed.not_inseparable IsClosed.not_inseparable

theorem IsOpen.not_inseparable (hs : IsOpen s) (hx : x ∈ s) (hy : y ∉ s) : ¬(x ~ y) := fun h =>
  hy <| (h.mem_open_iff hs).1 hx
#align is_open.not_inseparable IsOpen.not_inseparable

/-!
### Separation quotient

In this section we define the quotient of a topological space by the `inseparable` relation.
-/


variable (X)

/-- A `setoid` version of `inseparable`, used to define the `separation_quotient`. -/
def inseparableSetoid : Setoid X :=
  { Setoid.comap 𝓝 ⊥ with R := (· ~ ·) }
#align inseparable_setoid inseparableSetoid

/-- The quotient of a topological space by its `inseparable_setoid`. This quotient is guaranteed to
be a T₀ space. -/
def SeparationQuotient :=
  Quotient (inseparableSetoid X)deriving TopologicalSpace
#align separation_quotient SeparationQuotient

variable {X} {t : Set (SeparationQuotient X)}

namespace SeparationQuotient

/-- The natural map from a topological space to its separation quotient. -/
def mk : X → SeparationQuotient X :=
  Quotient.mk''
#align separation_quotient.mk SeparationQuotient.mk

theorem quotientMap_mk : QuotientMap (mk : X → SeparationQuotient X) :=
  quotientMap_quot_mk
#align separation_quotient.quotient_map_mk SeparationQuotient.quotientMap_mk

theorem continuous_mk : Continuous (mk : X → SeparationQuotient X) :=
  continuous_quot_mk
#align separation_quotient.continuous_mk SeparationQuotient.continuous_mk

@[simp]
theorem mk_eq_mk : mk x = mk y ↔ (x ~ y) :=
  Quotient.eq''
#align separation_quotient.mk_eq_mk SeparationQuotient.mk_eq_mk

theorem surjective_mk : Surjective (mk : X → SeparationQuotient X) :=
  surjective_quot_mk _
#align separation_quotient.surjective_mk SeparationQuotient.surjective_mk

@[simp]
theorem range_mk : range (mk : X → SeparationQuotient X) = univ :=
  surjective_mk.range_eq
#align separation_quotient.range_mk SeparationQuotient.range_mk

instance [Nonempty X] : Nonempty (SeparationQuotient X) :=
  Nonempty.map mk ‹_›

instance [Inhabited X] : Inhabited (SeparationQuotient X) :=
  ⟨mk default⟩

instance [Subsingleton X] : Subsingleton (SeparationQuotient X) :=
  surjective_mk.Subsingleton

theorem preimage_image_mk_open (hs : IsOpen s) : mk ⁻¹' (mk '' s) = s :=
  by
  refine' subset.antisymm _ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_open_iff hs).1 hys
#align separation_quotient.preimage_image_mk_open SeparationQuotient.preimage_image_mk_open

theorem isOpenMap_mk : IsOpenMap (mk : X → SeparationQuotient X) := fun s hs =>
  quotientMap_mk.is_open_preimage.1 <| by rwa [preimage_image_mk_open hs]
#align separation_quotient.is_open_map_mk SeparationQuotient.isOpenMap_mk

theorem preimage_image_mk_closed (hs : IsClosed s) : mk ⁻¹' (mk '' s) = s :=
  by
  refine' subset.antisymm _ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_closed_iff hs).1 hys
#align separation_quotient.preimage_image_mk_closed SeparationQuotient.preimage_image_mk_closed

theorem inducing_mk : Inducing (mk : X → SeparationQuotient X) :=
  ⟨le_antisymm (continuous_iff_le_induced.1 continuous_mk) fun s hs =>
      ⟨mk '' s, isOpenMap_mk s hs, preimage_image_mk_open hs⟩⟩
#align separation_quotient.inducing_mk SeparationQuotient.inducing_mk

theorem isClosedMap_mk : IsClosedMap (mk : X → SeparationQuotient X) :=
  inducing_mk.IsClosedMap <| by
    rw [range_mk]
    exact isClosed_univ
#align separation_quotient.is_closed_map_mk SeparationQuotient.isClosedMap_mk

@[simp]
theorem comap_mk_nhds_mk : comap mk (𝓝 (mk x)) = 𝓝 x :=
  (inducing_mk.nhds_eq_comap _).symm
#align separation_quotient.comap_mk_nhds_mk SeparationQuotient.comap_mk_nhds_mk

@[simp]
theorem comap_mk_nhdsSet_image : comap mk (𝓝ˢ (mk '' s)) = 𝓝ˢ s :=
  (inducing_mk.nhds_set_eq_comap _).symm
#align separation_quotient.comap_mk_nhds_set_image SeparationQuotient.comap_mk_nhdsSet_image

theorem map_mk_nhds : map mk (𝓝 x) = 𝓝 (mk x) := by
  rw [← comap_mk_nhds_mk, map_comap_of_surjective surjective_mk]
#align separation_quotient.map_mk_nhds SeparationQuotient.map_mk_nhds

theorem map_mk_nhdsSet : map mk (𝓝ˢ s) = 𝓝ˢ (mk '' s) := by
  rw [← comap_mk_nhds_set_image, map_comap_of_surjective surjective_mk]
#align separation_quotient.map_mk_nhds_set SeparationQuotient.map_mk_nhdsSet

theorem comap_mk_nhdsSet : comap mk (𝓝ˢ t) = 𝓝ˢ (mk ⁻¹' t) := by
  conv_lhs => rw [← image_preimage_eq t surjective_mk, comap_mk_nhds_set_image]
#align separation_quotient.comap_mk_nhds_set SeparationQuotient.comap_mk_nhdsSet

theorem preimage_mk_closure : mk ⁻¹' closure t = closure (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_closure_eq_closure_preimage continuous_mk t
#align separation_quotient.preimage_mk_closure SeparationQuotient.preimage_mk_closure

theorem preimage_mk_interior : mk ⁻¹' interior t = interior (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_interior_eq_interior_preimage continuous_mk t
#align separation_quotient.preimage_mk_interior SeparationQuotient.preimage_mk_interior

theorem preimage_mk_frontier : mk ⁻¹' frontier t = frontier (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_frontier_eq_frontier_preimage continuous_mk t
#align separation_quotient.preimage_mk_frontier SeparationQuotient.preimage_mk_frontier

theorem image_mk_closure : mk '' closure s = closure (mk '' s) :=
  (image_closure_subset_closure_image continuous_mk).antisymm <|
    isClosedMap_mk.closure_image_subset _
#align separation_quotient.image_mk_closure SeparationQuotient.image_mk_closure

theorem map_prod_map_mk_nhds (x : X) (y : Y) : map (Prod.map mk mk) (𝓝 (x, y)) = 𝓝 (mk x, mk y) :=
  by rw [nhds_prod_eq, ← prod_map_map_eq', map_mk_nhds, map_mk_nhds, nhds_prod_eq]
#align separation_quotient.map_prod_map_mk_nhds SeparationQuotient.map_prod_map_mk_nhds

theorem map_mk_nhdsWithin_preimage (s : Set (SeparationQuotient X)) (x : X) :
    map mk (𝓝[mk ⁻¹' s] x) = 𝓝[s] mk x := by
  rw [nhdsWithin, ← comap_principal, Filter.push_pull, nhdsWithin, map_mk_nhds]
#align separation_quotient.map_mk_nhds_within_preimage SeparationQuotient.map_mk_nhdsWithin_preimage

/-- Lift a map `f : X → α` such that `inseparable x y → f x = f y` to a map
`separation_quotient X → α`. -/
def lift (f : X → α) (hf : ∀ x y, (x ~ y) → f x = f y) : SeparationQuotient X → α := fun x =>
  Quotient.liftOn' x f hf
#align separation_quotient.lift SeparationQuotient.lift

@[simp]
theorem lift_mk {f : X → α} (hf : ∀ x y, (x ~ y) → f x = f y) (x : X) : lift f hf (mk x) = f x :=
  rfl
#align separation_quotient.lift_mk SeparationQuotient.lift_mk

@[simp]
theorem lift_comp_mk {f : X → α} (hf : ∀ x y, (x ~ y) → f x = f y) : lift f hf ∘ mk = f :=
  rfl
#align separation_quotient.lift_comp_mk SeparationQuotient.lift_comp_mk

@[simp]
theorem tendsto_lift_nhds_mk {f : X → α} {hf : ∀ x y, (x ~ y) → f x = f y} {x : X} {l : Filter α} :
    Tendsto (lift f hf) (𝓝 <| mk x) l ↔ Tendsto f (𝓝 x) l := by
  simp only [← map_mk_nhds, tendsto_map'_iff, lift_comp_mk]
#align separation_quotient.tendsto_lift_nhds_mk SeparationQuotient.tendsto_lift_nhds_mk

@[simp]
theorem tendsto_lift_nhdsWithin_mk {f : X → α} {hf : ∀ x y, (x ~ y) → f x = f y} {x : X}
    {s : Set (SeparationQuotient X)} {l : Filter α} :
    Tendsto (lift f hf) (𝓝[s] mk x) l ↔ Tendsto f (𝓝[mk ⁻¹' s] x) l := by
  simp only [← map_mk_nhds_within_preimage, tendsto_map'_iff, lift_comp_mk]
#align separation_quotient.tendsto_lift_nhds_within_mk SeparationQuotient.tendsto_lift_nhdsWithin_mk

@[simp]
theorem continuousAt_lift {f : X → Y} {hf : ∀ x y, (x ~ y) → f x = f y} {x : X} :
    ContinuousAt (lift f hf) (mk x) ↔ ContinuousAt f x :=
  tendsto_lift_nhds_mk
#align separation_quotient.continuous_at_lift SeparationQuotient.continuousAt_lift

@[simp]
theorem continuousWithinAt_lift {f : X → Y} {hf : ∀ x y, (x ~ y) → f x = f y}
    {s : Set (SeparationQuotient X)} {x : X} :
    ContinuousWithinAt (lift f hf) s (mk x) ↔ ContinuousWithinAt f (mk ⁻¹' s) x :=
  tendsto_lift_nhds_within_mk
#align separation_quotient.continuous_within_at_lift SeparationQuotient.continuousWithinAt_lift

@[simp]
theorem continuousOn_lift {f : X → Y} {hf : ∀ x y, (x ~ y) → f x = f y}
    {s : Set (SeparationQuotient X)} : ContinuousOn (lift f hf) s ↔ ContinuousOn f (mk ⁻¹' s) := by
  simp only [ContinuousOn, surjective_mk.forall, continuous_within_at_lift, mem_preimage]
#align separation_quotient.continuous_on_lift SeparationQuotient.continuousOn_lift

@[simp]
theorem continuous_lift {f : X → Y} {hf : ∀ x y, (x ~ y) → f x = f y} :
    Continuous (lift f hf) ↔ Continuous f := by
  simp only [continuous_iff_continuousOn_univ, continuous_on_lift, preimage_univ]
#align separation_quotient.continuous_lift SeparationQuotient.continuous_lift

/-- Lift a map `f : X → Y → α` such that `inseparable a b → inseparable c d → f a c = f b d` to a
map `separation_quotient X → separation_quotient Y → α`. -/
def lift₂ (f : X → Y → α) (hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d) :
    SeparationQuotient X → SeparationQuotient Y → α := fun x y => Quotient.liftOn₂' x y f hf
#align separation_quotient.lift₂ SeparationQuotient.lift₂

@[simp]
theorem lift₂_mk {f : X → Y → α} (hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d) (x : X)
    (y : Y) : lift₂ f hf (mk x) (mk y) = f x y :=
  rfl
#align separation_quotient.lift₂_mk SeparationQuotient.lift₂_mk

@[simp]
theorem tendsto_lift₂_nhds {f : X → Y → α} {hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d}
    {x : X} {y : Y} {l : Filter α} :
    Tendsto (uncurry <| lift₂ f hf) (𝓝 (mk x, mk y)) l ↔ Tendsto (uncurry f) (𝓝 (x, y)) l :=
  by
  rw [← map_prod_map_mk_nhds, tendsto_map'_iff]
  rfl
#align separation_quotient.tendsto_lift₂_nhds SeparationQuotient.tendsto_lift₂_nhds

@[simp]
theorem tendsto_lift₂_nhdsWithin {f : X → Y → α} {hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d}
    {x : X} {y : Y} {s : Set (SeparationQuotient X × SeparationQuotient Y)} {l : Filter α} :
    Tendsto (uncurry <| lift₂ f hf) (𝓝[s] (mk x, mk y)) l ↔
      Tendsto (uncurry f) (𝓝[Prod.map mk mk ⁻¹' s] (x, y)) l :=
  by
  rw [nhdsWithin, ← map_prod_map_mk_nhds, ← Filter.push_pull, comap_principal]
  rfl
#align separation_quotient.tendsto_lift₂_nhds_within SeparationQuotient.tendsto_lift₂_nhdsWithin

@[simp]
theorem continuousAt_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d}
    {x : X} {y : Y} :
    ContinuousAt (uncurry <| lift₂ f hf) (mk x, mk y) ↔ ContinuousAt (uncurry f) (x, y) :=
  tendsto_lift₂_nhds
#align separation_quotient.continuous_at_lift₂ SeparationQuotient.continuousAt_lift₂

@[simp]
theorem continuousWithinAt_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} {x : X} {y : Y} :
    ContinuousWithinAt (uncurry <| lift₂ f hf) s (mk x, mk y) ↔
      ContinuousWithinAt (uncurry f) (Prod.map mk mk ⁻¹' s) (x, y) :=
  tendsto_lift₂_nhds_within
#align separation_quotient.continuous_within_at_lift₂ SeparationQuotient.continuousWithinAt_lift₂

@[simp]
theorem continuousOn_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} :
    ContinuousOn (uncurry <| lift₂ f hf) s ↔ ContinuousOn (uncurry f) (Prod.map mk mk ⁻¹' s) :=
  by
  simp_rw [ContinuousOn, (surjective_mk.prod_map surjective_mk).forall, Prod.forall, Prod.map,
    continuous_within_at_lift₂]
  rfl
#align separation_quotient.continuous_on_lift₂ SeparationQuotient.continuousOn_lift₂

@[simp]
theorem continuous_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d} :
    Continuous (uncurry <| lift₂ f hf) ↔ Continuous (uncurry f) := by
  simp only [continuous_iff_continuousOn_univ, continuous_on_lift₂, preimage_univ]
#align separation_quotient.continuous_lift₂ SeparationQuotient.continuous_lift₂

end SeparationQuotient

