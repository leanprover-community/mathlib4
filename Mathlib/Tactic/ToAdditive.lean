/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn
-/
import Lean
import Mathlib.Data.List.Defs

/-!
# Transport multiplicative to additive

This file defines an attribute `toAdditive` that can be used to
automatically transport theorems and definitions (but not inductive
types and structures) from a multiplicative theory to an additive theory.

### Missing features

* Currently this is a no-op implementation.

-/

open Lean Meta

syntax (name := toAdditiveIgnoreArgs) "toAdditiveIgnoreArgs" num* : attr
syntax (name := toAdditiveRelevantArg) "toAdditiveRelevantArg" num : attr
syntax (name := toAdditiveReorder) "toAdditiveReorder" num* : attr
syntax (name := toAdditive) "toAdditive" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive!) "toAdditive!" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive?) "toAdditive?" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive!?) "toAdditive!?" (ppSpace ident)? (ppSpace str)? : attr

/-!
An attribute that tells `@[to_additive]` that certain arguments of this definition are not
involved when using `@[to_additive]`.
This helps the heuristic of `@[to_additive]` by also transforming definitions if `ℕ` or another
fixed type occurs as one of these arguments.
-/
initialize toAdditiveIgnoreArgsAttr : ParametricAttribute (List Nat) ←
  registerParametricAttribute {
    name := `toAdditiveIgnoreArgs
    descr :=
      "Auxiliary attribute for `to_additive` stating that certain arguments are not additivized."
    getParam := λ decl stx =>
      match stx with
        -- todo: check that the arguments are indeed numerals
        | `(attr|toAdditiveIgnoreArgs $[$ns]*) =>
          if (ns.map (·.isNatLit?)).all (·.isSome) then (ns.map (·.toNat)).toList else
          throwError "expected a list of (small) natural numbers at {ns}" -- can this code be reached?
        | _ => throwError "unexpected toAdditiveIgnoreArgs syntax {stx}" -- can this code be reached?
  }

/-!
An attribute that is automatically added to declarations tagged with `@[to_additive]`, if needed.

This attribute tells which argument is the type where this declaration uses the multiplicative
structure. If there are multiple argument, we typically tag the first one.
If this argument contains a fixed type, this declaration will note be additivized.
See the Heuristics section of `to_additive.attr` for more details.

If a declaration is not tagged, it is presumed that the first argument is relevant.
`@[to_additive]` uses the function `to_additive.first_multiplicative_arg` to automatically tag
declarations. It is ok to update it manually if the automatic tagging made an error.

Implementation note: we only allow exactly 1 relevant argument, even though some declarations
(like `prod.group`) have multiple arguments with a multiplicative structure on it.
The reason is that whether we additivize a declaration is an all-or-nothing decision, and if
we will not be able to additivize declarations that (e.g.) talk about multiplication on `ℕ × α`
anyway.

Warning: adding `@[to_additive_reorder]` with an equal or smaller number than the number in this
attribute is currently not supported.
-/
initialize toAdditiveRelevantArgAttr : ParametricAttribute Nat ←
  registerParametricAttribute {
    name := `toAdditiveRelevantArg
    descr :=
      "Auxiliary attribute for `to_additive` stating which arguments are the types with a " ++
      "multiplicative structure."
    getParam := λ decl stx =>
      match stx with
        | `(attr|toAdditiveRelevantArg $ns) =>
          if ns.isNatLit?.isSome then ns.toNat else
          throwError "expected (small) natural number at {ns}" -- can this code be reached?
        | _ => throwError "unexpected toAdditiveRelevantArg syntax {stx}" -- can this code be reached?
  }

/-!
An attribute that stores all the declarations that needs their arguments reordered when
applying `@[to_additive]`. Currently, we only support swapping consecutive arguments.
The list of the natural numbers contains the positions of the first of the two arguments
to be swapped.
If the first two arguments are swapped, the first two universe variables are also swapped.
Example: `@[to_additive_reorder 1 4]` swaps the first two arguments and the arguments in
positions 4 and 5.
-/
initialize toAdditiveReorderAttr : ParametricAttribute (List Nat) ←
  registerParametricAttribute {
    name := `toAdditiveReorder
    descr :=
      "Auxiliary attribute for `to_additive` that stores arguments that need to be reordered."
    getParam := λ decl stx =>
      match stx with
        -- todo: check that the arguments are indeed numerals
        | `(attr|toAdditiveReorder $[$ns]*) =>
          if (ns.map (·.isNatLit?)).all λ o => o.isSome && o.get! ≠ 0 then (ns.map (·.toNat)).toList
          else throwError "expected a list of (small) positive natural numbers at {ns}"
        | _ => throwError "unexpected toAdditiveReorder syntax {stx}" -- can this code be reached?
  }

/--
Find the first argument of `nm` that has a multiplicative type-class on it.
Returns 1 if there are no types with a multiplicative class as arguments.
E.g. `prod.group` returns 1, and `pi.has_one` returns 2.
-/
def firstMultiplicativeArg (nm : Name) : CoreM Nat := do
  let env ← getEnv
  let some d ← env.find? nm | throwError "Cannot find declaration {nm}."
  d.type
  -- let (es, _) := d.type.piBinders
  -- let l ← es.mmap_with_index $ λ n bi => do
  --   let tgt := bi.type.pi_codomain
  --   let n_bi := bi.type.pi_binders.fst.length
  --   tt ← has_attribute' `to_additive tgt.get_app_fn.const_name | return none
  --   let n2 := tgt.get_app_args.head.get_app_fn.match_var.map $ λ m, n + n_bi - m
  --   return n2
  -- let l := l.reduce_option
  return 0-- (if l = [] then 1 else l.foldr min l.head)


initialize toAdditiveAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `toAdditive
    descr := "Transport multiplicative declarations to additive ones.",
    getParam := λ decl attr => do
      let env ← getEnv

      return Inhabited.default
  }
