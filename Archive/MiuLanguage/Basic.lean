/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/
import Mathlib.Tactic.Linarith

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
inductive data type `Derivable` designed so that `Derivable x` represents the notion that the string
`x` can be derived from the axiom by the rules of inference. The axiom is represented as a
nonrecursive constructor for `Derivable`. This mirrors the translation of Peano's axiom '0 is a
natural number' into the nonrecursive constructor `zero` of the inductive type `Nat`.

## References

* [Jeremy Avigad, Leonardo de Moura and Soonho Kong, _Theorem Proving in Lean_]
  [avigad_moura_kong-2017]
* [Douglas R Hofstadter, _Gödel, Escher, Bach_][Hofstadter-1979]

## Tags

miu, derivable strings

-/


namespace Miu

/-!
### Declarations and instance derivations for `MiuAtom` and `Miustr`
-/


/-- The atoms of MIU can be represented as an enumerated type in Lean.
-/
inductive MiuAtom : Type
  | M : MiuAtom
  | I : MiuAtom
  | U : MiuAtom
  deriving DecidableEq

/-!
The annotation `deriving DecidableEq` above indicates that Lean will automatically derive that
`MiuAtom` is an instance of `DecidableEq`. The use of `deriving` is crucial in this project and will
lead to the automatic derivation of decidability.
-/


open MiuAtom

/--
We show that the type `MiuAtom` is inhabited, giving `M` (for no particular reason) as the default
element.
-/
instance miuAtomInhabited : Inhabited MiuAtom :=
  Inhabited.mk M

/-- `MiuAtom.repr` is the 'natural' function from `MiuAtom` to `String`.
-/
def MiuAtom.repr : MiuAtom → String
  | M => "M"
  | I => "I"
  | U => "U"

/-- Using `MiuAtom.repr`, we prove that `MiuAtom` is an instance of `Repr`.
-/
instance : Repr MiuAtom :=
  ⟨fun u _ => u.repr⟩

/-- For simplicity, an `Miustr` is just a list of elements of type `MiuAtom`.
-/
abbrev Miustr := List MiuAtom

instance : Membership MiuAtom Miustr := by unfold Miustr; infer_instance

/-- For display purposes, an `Miustr` can be represented as a `String`.
-/
def Miustr.mrepr : Miustr → String
  | [] => ""
  | c :: cs => c.repr ++ Miustr.mrepr cs

instance miurepr : Repr Miustr :=
  ⟨fun u _ => u.mrepr⟩

/-- In the other direction, we set up a coercion from `String` to `Miustr`.
-/
def lcharToMiustr : List Char → Miustr
  | [] => []
  | c :: cs =>
    let ms := lcharToMiustr cs
    match c with
    | 'M' => M :: ms
    | 'I' => I :: ms
    | 'U' => U :: ms
    | _ => []

instance stringCoeMiustr : Coe String Miustr :=
  ⟨fun st => lcharToMiustr st.data⟩

/-!
### Derivability
-/


/--
The inductive type `Derivable` has five constructors. The nonrecursive constructor `mk` corresponds
to Hofstadter's axiom that `"MI"` is derivable. Each of the constructors `r1`, `r2`, `r3`, `r4`
corresponds to the one of Hofstadter's rules of inference.
-/
inductive Derivable : Miustr → Prop
  | mk : Derivable "MI"
  | r1 {x} : Derivable (x ++ [I]) → Derivable (x ++ [I, U])
  | r2 {x} : Derivable (M :: x) → Derivable (M :: x ++ x)
  | r3 {x y} : Derivable (x ++ [I, I, I] ++ y) → Derivable (x ++ (U :: y))
  | r4 {x y} : Derivable (x ++ [U, U] ++ y) → Derivable (x ++ y)

/-!
### Rule usage examples
-/


example (h : Derivable "UMI") : Derivable "UMIU" := by
  change Derivable ([U, M] ++ [I, U])
  exact Derivable.r1 h -- Rule 1

example (h : Derivable "MIIU") : Derivable "MIIUIIU" := by
  change Derivable (M :: [I, I, U] ++ [I, I, U])
  exact Derivable.r2 h -- Rule 2

example (h : Derivable "UIUMIIIMMM") : Derivable "UIUMUMMM" := by
  change Derivable ([U, I, U, M] ++ U :: [M, M, M])
  exact Derivable.r3 h -- Rule 3

example (h : Derivable "MIMIMUUIIM") : Derivable "MIMIMIIM" := by
  change Derivable ([M, I, M, I, M] ++ [I, I, M])
  exact Derivable.r4 h -- Rule 4

/-!
### Derivability examples
-/


private theorem MIU_der : Derivable "MIU" := by
  change Derivable ([M] ++ [I, U])
  apply Derivable.r1 -- reduce to deriving `"MI"`,
  constructor -- which is the base of the inductive construction.

example : Derivable "MIUIU" := by
  change Derivable (M :: [I, U] ++ [I, U])
  exact Derivable.r2 MIU_der -- `"MIUIU"` can be derived as `"MIU"` can.

example : Derivable "MUI" := by
  have h₂ : Derivable "MII" := by
    change Derivable (M :: [I] ++ [I])
    exact Derivable.r2 Derivable.mk
  have h₃ : Derivable "MIIII" := by
    change Derivable (M :: [I, I] ++ [I, I])
    exact Derivable.r2 h₂
  change Derivable ([M] ++ U :: [I])
  exact Derivable.r3 h₃ -- We prove our main goal using rule 3

end Miu
