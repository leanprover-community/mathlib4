/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Logic.Nontrivial
import Mathlib.Tactic.NontrivialityTag

/-! # The `nontriviality` tactic. -/

attribute [nontriviality] eq_iff_true_of_subsingleton Subsingleton.le

namespace Tactic

/-- Tries to generate a `Nontrivial α` instance by performing case analysis on
`subsingleton_or_nontrivial α`,
attempting to discharge the subsingleton branch using lemmas with `@[nontriviality]` attribute,
including `Subsingleton.le` and `eq_iff_true_of_subsingleton`.
-/
unsafe def nontriviality_by_elim (α : expr) (lems : interactive.parse simp_arg_list) : tactic Unit := do
  let alternative ← to_expr (pquote.1 (subsingleton_or_nontrivial (%%ₓα)))
  let n ← get_unused_name "_inst"
  tactic.cases Alternative [n, n]
  (solve1 <| do
        reset_instance_cache
        apply_instance <|> interactive.simp none none ff lems [`nontriviality] (Interactive.Loc.ns [none])) <|>
      fail f! "Could not prove goal assuming `subsingleton {α}`"
  reset_instance_cache

/- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs] -/
/-- Tries to generate a `Nontrivial α` instance using `nontrivial_of_ne` or `nontrivial_of_lt`
and local hypotheses.
-/
unsafe def nontriviality_by_assumption (α : expr) : tactic Unit := do
  let n ← get_unused_name "_inst"
  to_expr (pquote.1 (Nontrivial (%%ₓα))) >>= assert n
  apply_instance <|> sorry
  reset_instance_cache

end Tactic

namespace Tactic.Interactive

open Tactic

setup_tactic_parser

/-- Attempts to generate a `Nontrivial α` hypothesis.

The tactic first looks for an instance using `apply_instance`.

If the goal is an (in)equality, the type `α` is inferred from the goal.
Otherwise, the type needs to be specified in the tactic invocation, as `nontriviality α`.

The `nontriviality` tactic will first look for strict inequalities amongst the hypotheses,
and use these to derive the `nontrivial` instance directly.

Otherwise, it will perform a case split on `subsingleton α ∨ nontrivial α`, and attempt to discharge
the `Subsingleton` goal using `simp [lemmas] with nontriviality`, where `[lemmas]` is a list of
additional `simp` lemmas that can be passed to `nontriviality` using the syntax
`nontriviality α using [lemmas]`.

```
example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : 0 < a :=
begin
  nontriviality, -- There is now a `nontrivial R` hypothesis available.
  assumption,
end
```

```
example {R : Type} [comm_ring R] {r s : R} : r * s = s * r :=
begin
  nontriviality, -- There is now a `nontrivial R` hypothesis available.
  apply mul_comm,
end
```

```
example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : (2 : ℕ) ∣ 4 :=
begin
  nontriviality R, -- there is now a `nontrivial R` hypothesis available.
  dec_trivial
end
```

```
def myeq {α : Type} (a b : α) : Prop := a = b

example {α : Type} (a b : α) (h : a = b) : myeq a b :=
begin
  success_if_fail { nontriviality α }, -- Fails
  nontriviality α using [myeq], -- There is now a `nontrivial α` hypothesis available
  assumption
end
```
-/
unsafe def nontriviality (t : parse texpr ?) (lems : parse (tk "using" *> simp_arg_list <|> pure [])) : tactic Unit :=
  do
  let α ←
    match t with
      | some α => to_expr α
      | none =>
        (do
            let t ← mk_mvar
            let e ← to_expr (pquote.1 (@Eq (%%ₓt) _ _))
            target >>= unify e
            return t) <|>
          (do
              let t ← mk_mvar
              let e ← to_expr (pquote.1 (@LE.le (%%ₓt) _ _ _))
              target >>= unify e
              return t) <|>
            (do
                let t ← mk_mvar
                let e ← to_expr (pquote.1 (@Ne (%%ₓt) _ _))
                target >>= unify e
                return t) <|>
              (do
                  let t ← mk_mvar
                  let e ← to_expr (pquote.1 (@LT.lt (%%ₓt) _ _ _))
                  target >>= unify e
                  return t) <|>
                fail
                  "The goal is not an (in)equality, so you'll need to specify the desired `nontrivial α`\n      instance by invoking `nontriviality α`."
  nontriviality_by_assumption α <|> nontriviality_by_elim α lems

add_tactic_doc
  { Name := "nontriviality", category := DocCategory.tactic, declNames := [`tactic.interactive.nontriviality],
    tags := ["logic", "type class"] }

end Tactic.Interactive
