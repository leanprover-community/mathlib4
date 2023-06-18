/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha

! This file was ported from Lean 3 source module miu_language.basic
! leanprover-community/mathlib commit 7e3fa4c114f6f12380cf3b181fd4bd03a2f05b79
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Tactic.Linarith.Default

/-!
# An MIU Decision Procedure in Lean

The [MIU formal system](https://en.wikipedia.org/wiki/MU_puzzle) was introduced by Douglas
Hofstadter in the first chapter of his 1979 book,
[Gödel, Escher, Bach](https://en.wikipedia.org/wiki/G%C3%B6del,_Escher,_Bach).
The system is defined by four rules of inference, one axiom, and an alphabet of three symbols:
`M`, `I`, and `U`.

Hofstadter's central question is: can the string `"MU"` be derived?

It transpires that there is a simple decision procedure for this system. A string is derivable if
and only if it starts with `M`, contains no other `M`s, and the number of `I`s in the string is
congruent to 1 or 2 modulo 3.

The principal aim of this project is to give a Lean proof that the derivability of a string is a
decidable predicate.

## The MIU System

In Hofstadter's description, an _atom_ is any one of `M`, `I` or `U`. A _string_ is a finite
sequence of zero or more symbols. To simplify notation, we write a sequence `[I,U,U,M]`,
for example, as `IUUM`.

The four rules of inference are:

1. xI → xIU,
2. Mx → Mxx,
3. xIIIy → xUy,
4. xUUy → xy,

where the notation α → β is to be interpreted as 'if α is derivable, then β is derivable'.

Additionally, he has an axiom:

* `MI` is derivable.

In Lean, it is natural to treat the rules of inference and the axiom on an equal footing via an
inductive data type `derivable` designed so that `derivable x` represents the notion that the string
`x` can be derived from the axiom by the rules of inference. The axiom is represented as a
nonrecursive constructor for `derivable`. This mirrors the translation of Peano's axiom '0 is a
natural number' into the nonrecursive constructor `zero` of the inductive type `nat`.

## References

* [Jeremy Avigad, Leonardo de Moura and Soonho Kong, _Theorem Proving in Lean_]
  [avigad_moura_kong-2017]
* [Douglas R Hofstadter, _Gödel, Escher, Bach_][Hofstadter-1979]

## Tags

miu, derivable strings

-/


namespace Miu

/-!
### Declarations and instance derivations for `miu_atom` and `miustr`
-/


/-- The atoms of MIU can be represented as an enumerated type in Lean.
-/
inductive MiuAtom : Type
  | M : miu_atom
  | I : miu_atom
  | U : miu_atom
  deriving DecidableEq
#align miu.miu_atom Miu.MiuAtom

/-!
The annotation `@[derive decidable_eq]` above assigns the attribute `derive` to `miu_atom`, through
which Lean automatically derives that `miu_atom` is an instance of `decidable_eq`. The use of
`derive` is crucial in this project and will lead to the automatic derivation of decidability.
-/


open MiuAtom

/--
We show that the type `miu_atom` is inhabited, giving `M` (for no particular reason) as the default
element.
-/
instance miuAtomInhabited : Inhabited MiuAtom :=
  Inhabited.mk M
#align miu.miu_atom_inhabited Miu.miuAtomInhabited

/-- `miu_atom.repr` is the 'natural' function from `miu_atom` to `string`.
-/
def MiuAtom.repr : MiuAtom → String
  | M => "M"
  | I => "I"
  | U => "U"
#align miu.miu_atom.repr Miu.MiuAtom.repr

/-- Using `miu_atom.repr`, we prove that ``miu_atom` is an instance of `has_repr`.
-/
instance : Repr MiuAtom :=
  ⟨fun u => u.repr⟩

/- ./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler has_mem[has_mem] miu_atom[miu.miu_atom] -/
/-- For simplicity, an `miustr` is just a list of elements of type `miu_atom`.
-/
def Miustr :=
  List MiuAtom
deriving Append,
  «./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler has_mem[has_mem] miu_atom[miu.miu_atom]»
#align miu.miustr Miu.Miustr

/-- For display purposes, an `miustr` can be represented as a `string`.
-/
def Miustr.mrepr : Miustr → String
  | [] => ""
  | c :: cs => c.repr ++ miustr.mrepr cs
#align miu.miustr.mrepr Miu.Miustr.mrepr

instance miurepr : Repr Miustr :=
  ⟨fun u => u.mrepr⟩
#align miu.miurepr Miu.miurepr

/-- In the other direction, we set up a coercion from `string` to `miustr`.
-/
def lcharToMiustr : List Char → Miustr
  | [] => []
  | c :: cs =>
    let ms := lchar_to_miustr cs
    match c with
    | 'M' => M :: ms
    | 'I' => I :: ms
    | 'U' => U :: ms
    | _ => []
#align miu.lchar_to_miustr Miu.lcharToMiustr

instance stringCoeMiustr : Coe String Miustr :=
  ⟨fun st => lcharToMiustr st.data⟩
#align miu.string_coe_miustr Miu.stringCoeMiustr

/-!
### Derivability
-/


/--
The inductive type `derivable` has five constructors. The nonrecursive constructor `mk` corresponds
to Hofstadter's axiom that `"MI"` is derivable. Each of the constructors `r1`, `r2`, `r3`, `r4`
corresponds to the one of Hofstadter's rules of inference.
-/
inductive Derivable : Miustr → Prop
  | mk : derivable "MI"
  | r1 {x} : derivable (x ++ [I]) → derivable (x ++ [I, U])
  | r2 {x} : derivable (M :: x) → derivable (M :: x ++ x)
  | r3 {x y} : derivable (x ++ [I, I, I] ++ y) → derivable (x ++ U :: y)
  | r4 {x y} : derivable (x ++ [U, U] ++ y) → derivable (x ++ y)
#align miu.derivable Miu.Derivable

/-!
### Rule usage examples
-/


example (h : Derivable "UMI") : Derivable "UMIU" := by
  change ("UMIU" : miustr) with [U, M] ++ [I, U]
  exact derivable.r1 h

-- Rule 1
example (h : Derivable "MIIU") : Derivable "MIIUIIU" := by
  change ("MIIUIIU" : miustr) with M :: [I, I, U] ++ [I, I, U]
  exact derivable.r2 h

-- Rule 2
example (h : Derivable "UIUMIIIMMM") : Derivable "UIUMUMMM" := by
  change ("UIUMUMMM" : miustr) with [U, I, U, M] ++ U :: [M, M, M]
  exact derivable.r3 h

-- Rule 3
example (h : Derivable "MIMIMUUIIM") : Derivable "MIMIMIIM" := by
  change ("MIMIMIIM" : miustr) with [M, I, M, I, M] ++ [I, I, M]
  exact derivable.r4 h

/-!
### Derivability examples
-/


-- Rule 4
private theorem MIU_der : Derivable "MIU" := by
  change ("MIU" : miustr) with [M] ++ [I, U]
  apply derivable.r1
  -- reduce to deriving "MI",
  constructor

-- which is the base of the inductive construction.
example : Derivable "MIUIU" := by
  change ("MIUIU" : miustr) with M :: [I, U] ++ [I, U]
  exact derivable.r2 MIU_der

-- `"MIUIU"` can be derived as `"MIU"` can.
example : Derivable "MUI" := by
  have h₂ : derivable "MII" := by
    change ("MII" : miustr) with M :: [I] ++ [I]
    exact derivable.r2 derivable.mk
  have h₃ : derivable "MIIII" := by
    change ("MIIII" : miustr) with M :: [I, I] ++ [I, I]
    exact derivable.r2 h₂
  change ("MUI" : miustr) with [M] ++ U :: [I]
  exact derivable.r3 h₃

-- We prove our main goal using rule 3
end Miu

