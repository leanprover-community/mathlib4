/-
Copyright (c) 2026 zayn7lie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Wang
-/
import Mathlib.Computability.LambdaCalculus.DeBruijnSyntax
import Mathlib.Logic.Relation

/-!
# One-step β-reduction and its reflexive-transitive closure

This file defines the usual compatible one-step β-reduction on de Bruijn lambda terms.
It also introduces its reflexive-transitive closure and proves basic closure lemmas for
application and abstraction.

## Main definitions

* `Lambda.Beta`: one-step β-reduction.
* `Lambda.BetaStar`: the reflexive-transitive closure of `Beta`.

## Main lemmas

Inside `namespace BetaStar` we provide the standard constructors and congruence lemmas:

* `BetaStar.refl`
* `BetaStar.head`
* `BetaStar.tail`
* `BetaStar.trans`
* `BetaStar.appL`, `BetaStar.appR`, `BetaStar.app`
* `BetaStar.abs`

These lemmas are used later to compare β-reduction with parallel reduction.
-/


namespace Lambda
open Term

/-- One-step β-reduction (compatible closure). -/
inductive Beta : Term → Term → Prop
  | abs  {t t'}        : Beta t t' → Beta (λ.t) (λ.t')
  | appL {t t' u}      : Beta t t' → Beta (t·u) (t'·u)
  | appR {t u u'}      : Beta u u' → Beta (t·u) (t·u')
  | red  (t' s : Term) : Beta ((λ.t')·s) (t'.sub 0 s)
abbrev BetaStar := Relation.ReflTransGen Beta

namespace BetaStar

theorem refl (t : Term) : BetaStar t t :=
  Relation.ReflTransGen.refl
theorem head {a b c} (hab : Beta a b) (hbc : BetaStar b c) : 
    BetaStar a c := 
  Relation.ReflTransGen.head hab hbc
theorem tail {a b c} (hab : BetaStar a b) (hbc : Beta b c) : 
    BetaStar a c :=
  Relation.ReflTransGen.tail hab hbc
theorem trans {a b c}
    (hab : BetaStar a b) (hbc : BetaStar b c) :
    BetaStar a c := 
  Relation.ReflTransGen.trans hab hbc

theorem appL {t t' u : Term} (h : BetaStar t t') :
    BetaStar (t·u) (t'·u) := by
  induction h with
  | refl => exact BetaStar.refl (t·u)
  | tail hab hbc ih => exact BetaStar.tail ih (Beta.appL hbc)
theorem appR {t u u' : Term} (h : BetaStar u u') :
    BetaStar (t·u) (t·u') := by
  induction h with
  | refl => exact BetaStar.refl (t·u)
  | tail hab hbc ih => exact BetaStar.tail ih (Beta.appR hbc)
theorem app {t t' u u'}
    (ht : BetaStar t t')
    (hu : BetaStar u u') : 
    BetaStar (t·u) (t'·u') := by
  induction ht with
  | refl => exact BetaStar.appR hu
  | tail hab hbc ih => exact BetaStar.tail ih (Beta.appL hbc) 

theorem abs {t t' : Term} (h : BetaStar t t') :
    BetaStar (λ.t) (λ.t') := by
  induction h with
  | refl => exact BetaStar.refl (λ.t)
  | tail hab hbc ih => exact BetaStar.tail ih (Beta.abs hbc)

end BetaStar
end Lambda
