/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Data.Fintype.Sets
public meta import Mathlib.Tactic.ToDual
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Multiset.Bind
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive

/-!
# Big operators

In this file we define products and sums indexed by finite sets (specifically, `Finset`).

## Notation

We introduce the following notation.

Let `s` be a `Finset ι`, and `f : ι → β` a function.

* `∏ x ∈ s, f x` is notation for `Finset.prod s f` (assuming `β` is a `CommMonoid`)
* `∑ x ∈ s, f x` is notation for `Finset.sum s f` (assuming `β` is an `AddCommMonoid`)
* `∏ x, f x` is notation for `Finset.prod Finset.univ f`
  (assuming `ι` is a `Fintype` and `β` is a `CommMonoid`)
* `∑ x, f x` is notation for `Finset.sum Finset.univ f`
  (assuming `ι` is a `Fintype` and `β` is an `AddCommMonoid`)
* `∏ x ∈ s with p x, f x` is notation for `Finset.prod (Finset.filter p s) f`.
* `∑ x ∈ s with p x, f x` is notation for `Finset.sum (Finset.filter p s) f`.
* `∏ (x ∈ s) (y ∈ t), f x y` is notation for `Finset.prod (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.
* `∑ (x ∈ s) (y ∈ t), f x y` is notation for `Finset.sum (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.
* Other supported binders: `x < n`, `x > n`, `x ≤ n`, `x ≥ n`, `x ≠ n`, `x ∉ s`, `x + y = n`

## Implementation Notes

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

-/

@[expose] public section

assert_not_exists AddCommMonoidWithOne
assert_not_exists MonoidWithZero
assert_not_exists MulAction
assert_not_exists IsOrderedMonoid

variable {ι κ M N G α : Type*}

open Fin Function

namespace Finset

/-- `∏ x ∈ s, f x` is the product of `f x` as `x` ranges over the elements of the finite set `s`.

When the index type is a `Fintype`, the notation `∏ x, f x`, is a shorthand for
`∏ x ∈ Finset.univ, f x`. -/
@[to_additive /-- `∑ x ∈ s, f x` is the sum of `f x` as `x` ranges over the elements
of the finite set `s`.

When the index type is a `Fintype`, the notation `∑ x, f x`, is a shorthand for
`∑ x ∈ Finset.univ, f x`. -/]
protected def prod [CommMonoid M] (s : Finset ι) (f : ι → M) : M :=
  (s.1.map f).prod

@[to_additive (attr := simp)]
theorem prod_mk [CommMonoid M] (s : Multiset ι) (hs : s.Nodup) (f : ι → M) :
    (⟨s, hs⟩ : Finset ι).prod f = (s.map f).prod :=
  rfl

@[to_additive (attr := simp)]
theorem prod_val [CommMonoid M] (s : Finset M) : s.1.prod = s.prod id := by
  rw [Finset.prod, Multiset.map_id]

end Finset

library_note «operator precedence of big operators» /--
There is no established mathematical convention
for the operator precedence of big operators like `∏` and `∑`.
We will have to make a choice.

Online discussions, such as https://math.stackexchange.com/q/185538/30839
seem to suggest that `∏` and `∑` should have the same precedence,
and that this should be somewhere between `*` and `+`.
The latter have precedence levels `70` and `65` respectively,
and we therefore choose the level `67`.

In practice, this means that parentheses should be placed as follows:
```lean
∑ k ∈ K, (a k + b k) = ∑ k ∈ K, a k + ∑ k ∈ K, b k →
  ∏ k ∈ K, a k * b k = (∏ k ∈ K, a k) * (∏ k ∈ K, b k)
```
(Example taken from page 490 of Knuth's *Concrete Mathematics*.)
-/

namespace BigOperators
open Batteries.ExtendedBinder Lean Meta

-- TODO: contribute this modification back to `extBinder`

/-- A `bigOpBinder` is like an `extBinder` and has the form `x`, `x : ty`, or `x pred`
where `pred` is a `binderPred` like `< 2`.
Unlike `extBinder`, `x` is a term. -/
syntax bigOpBinder := term:max((" : "term) <|> binderPred)?
/-- A BigOperator binder in parentheses -/
syntax bigOpBinderParenthesized := " ("bigOpBinder")"
/-- A list of parenthesized binders -/
syntax bigOpBinderCollection := bigOpBinderParenthesized+
/-- A single (unparenthesized) binder, or a list of parenthesized binders -/
syntax bigOpBinders := bigOpBinderCollection <|> (ppSpace bigOpBinder)

/-- Collects additional binder/Finset pairs for the given `bigOpBinder`.

Note: this is not extensible at the moment, unlike the usual `bigOpBinder` expansions. -/
meta def processBigOpBinder (processed : (Array (Term × Term))) (binder : TSyntax ``bigOpBinder) :
    MacroM (Array (Term × Term)) :=
  set_option hygiene false in
  withRef binder do
    match binder with
    | `(bigOpBinder| $x:term) =>
      match x with
      | `(($a + $b = $n)) => -- Maybe this is too cute.
        return processed |>.push (← `(⟨$a, $b⟩), ← `(Finset.Nat.antidiagonal $n))
      | _ => return processed |>.push (x, ← ``(Finset.univ))
    | `(bigOpBinder| $x : $t) => return processed |>.push (x, ← ``((Finset.univ : Finset $t)))
    | `(bigOpBinder| $x ∈ $s) => return processed |>.push (x, ← `(finset% $s))
    | `(bigOpBinder| $x ∉ $s) => return processed |>.push (x, ← `(finset% $sᶜ))
    | `(bigOpBinder| $x ≠ $n) => return processed |>.push (x, ← `(Finset.univ.erase $n))
    | `(bigOpBinder| $x < $n) => return processed |>.push (x, ← `(Finset.Iio $n))
    | `(bigOpBinder| $x ≤ $n) => return processed |>.push (x, ← `(Finset.Iic $n))
    | `(bigOpBinder| $x > $n) => return processed |>.push (x, ← `(Finset.Ioi $n))
    | `(bigOpBinder| $x ≥ $n) => return processed |>.push (x, ← `(Finset.Ici $n))
    | _ => Macro.throwUnsupported

/-- Collects the binder/Finset pairs for the given `bigOpBinders`. -/
meta def processBigOpBinders (binders : TSyntax ``bigOpBinders) :
    MacroM (Array (Term × Term)) :=
  match binders with
  | `(bigOpBinders| $b:bigOpBinder) => processBigOpBinder #[] b
  | `(bigOpBinders| $[($bs:bigOpBinder)]*) => bs.foldlM processBigOpBinder #[]
  | _ => Macro.throwUnsupported

/-- Collects the binderIdents into a `⟨...⟩` expression. -/
meta def bigOpBindersPattern (processed : Array (Term × Term)) : MacroM Term := do
  let ts := processed.map Prod.fst
  if h : ts.size = 1 then
    return ts[0]
  else
    `(⟨$ts,*⟩)

/-- Collects the terms into a product of sets. -/
meta def bigOpBindersProd (processed : Array (Term × Term)) : MacroM Term := do
  if h₀ : processed.size = 0 then
    `((Finset.univ : Finset Unit))
  else if h₁ : processed.size = 1 then
    return processed[0].2
  else
    processed.foldrM (fun s p => `(SProd.sprod $(s.2) $p)) processed.back.2
      (start := processed.size - 1)

/--
- `∑ x, f x` is notation for `Finset.sum Finset.univ f`. It is the sum of `f x`,
  where `x` ranges over the finite domain of `f`.
- `∑ x ∈ s, f x` is notation for `Finset.sum s f`. It is the sum of `f x`,
  where `x` ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
- `∑ x ∈ s with p x, f x` is notation for `Finset.sum (Finset.filter p s) f`.
- `∑ x ∈ s with h : p x, f x h` is notation for `Finset.sum s fun x ↦ if h : p x then f x h else 0`.
- `∑ (x ∈ s) (y ∈ t), f x y` is notation for `Finset.sum (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.

These support destructuring, for example `∑ ⟨x, y⟩ ∈ s ×ˢ t, f x y`.

Notation: `"∑" bigOpBinders* (" with" (ident ":")? term)? "," term` -/
syntax (name := bigsum)
  "∑ " bigOpBinders (" with " atomic(binderIdent " : ")? term)? ", " term:67 : term

/--
- `∏ x, f x` is notation for `Finset.prod Finset.univ f`. It is the product of `f x`,
  where `x` ranges over the finite domain of `f`.
- `∏ x ∈ s, f x` is notation for `Finset.prod s f`. It is the product of `f x`,
  where `x` ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
- `∏ x ∈ s with p x, f x` is notation for `Finset.prod (Finset.filter p s) f`.
- `∏ x ∈ s with h : p x, f x h` is notation for
  `Finset.prod s fun x ↦ if h : p x then f x h else 1`.
- `∏ (x ∈ s) (y ∈ t), f x y` is notation for `Finset.prod (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.

These support destructuring, for example `∏ ⟨x, y⟩ ∈ s ×ˢ t, f x y`.

Notation: `"∏" bigOpBinders* ("with" (ident ":")? term)? "," term` -/
syntax (name := bigprod)
  "∏ " bigOpBinders (" with " atomic(binderIdent " : ")? term)? ", " term:67 : term

macro_rules (kind := bigsum)
  | `(∑ $bs:bigOpBinders $[with $[$hx??:binderIdent :]? $p?:term]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    -- `a` is interpreted as the filtering proposition, unless `b` exists, in which case `a` is the
    -- proof and `b` is the filtering proposition
    match hx??, p? with
    | some (some hx), some p =>
      `(Finset.sum $s fun $x ↦ if $hx : $p then $v else 0)
    | _, some p => `(Finset.sum (Finset.filter (fun $x ↦ $p) $s) (fun $x ↦ $v))
    | _, none => `(Finset.sum $s (fun $x ↦ $v))

macro_rules (kind := bigprod)
  | `(∏ $bs:bigOpBinders $[with $[$hx??:binderIdent :]? $p?:term]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    -- `a` is interpreted as the filtering proposition, unless `b` exists, in which case `a` is the
    -- proof and `b` is the filtering proposition
    match hx??, p? with
    | some (some hx), some p =>
      `(Finset.prod $s fun $x ↦ if $hx : $p then $v else 1)
    | _, some p => `(Finset.prod (Finset.filter (fun $x ↦ $p) $s) (fun $x ↦ $v))
    | _, none => `(Finset.prod $s (fun $x ↦ $v))

open PrettyPrinter.Delaborator SubExpr
open scoped Batteries.ExtendedBinder

/-- The possibilities we distinguish to delaborate the finset indexing a big operator:
* `finset s` corresponds to `∑ x ∈ s, f x`
* `univ` corresponds to `∑ x, f x`
* `filter s p` corresponds to `∑ x ∈ s with p x, f x`
* `filterUniv p` corresponds to `∑ x with p x, f x`
-/
private inductive FinsetResult where
  | finset (s : Term)
  | univ
  | filter (s : Term) (p : Term)
  | filterUniv (p : Term)

/-- Delaborates a finset indexing a big operator. In case it is a `Finset.filter`, `i` is used for
the binder name. -/
private meta def delabFinsetArg (i : Ident) : DelabM FinsetResult := do
  let s ← getExpr
  if s.isAppOfArity ``Finset.univ 2 then
    return .univ
  else if s.isAppOfArity ``Finset.filter 4 then
    let #[_, _, _, t] := s.getAppArgs | failure
    let p ←
      withNaryArg 1 do
        if (← getExpr).isLambda then
          withBindingBody i.getId delab
        else
          let p ← delab
          return (← `($p $i))
    if t.isAppOfArity ``Finset.univ 2 then
      return .filterUniv p
    else
      let ss ← withNaryArg 3 delab
      return .filter ss p
  else
    let ss ← delab
    return .finset ss

/-- Delaborator for `Finset.prod`. The `pp.funBinderTypes` option controls whether
to show the domain type when the product is over `Finset.univ`. -/
@[app_delab Finset.prod] meta def delabFinsetProd : Delab :=
  whenPPOption getPPNotation <| withOverApp 5 do
  let #[_, _, _, _, f] := (← getExpr).getAppArgs | failure
  guard f.isLambda
  let ppDomain ← withAppArg <| getPPOption getPPFunBinderTypes
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i => do
    return (⟨i⟩, ← delab)
  let res ← withNaryArg 3 <| delabFinsetArg i
  match res with
  | .finset ss => `(∏ $i:ident ∈ $ss, $body)
  | .univ =>
    let binder ←
      if ppDomain then
        let ty ← withNaryArg 0 delab
        `(bigOpBinder| $i:ident : $ty)
      else
        `(bigOpBinder| $i:ident)
    `(∏ $binder:bigOpBinder, $body)
  | .filter ss p =>
    `(∏ $i:ident ∈ $ss with $p, $body)
  | .filterUniv p =>
    let binder ←
    if ppDomain then
      let ty ← withNaryArg 0 delab
      `(bigOpBinder| $i:ident : $ty)
    else
      `(bigOpBinder| $i:ident)
    `(∏ $binder:bigOpBinder with $p, $body)

/-- Delaborator for `Finset.sum`. The `pp.funBinderTypes` option controls whether
to show the domain type when the sum is over `Finset.univ`. -/
@[app_delab Finset.sum] meta def delabFinsetSum : Delab :=
  whenPPOption getPPNotation <| withOverApp 5 do
  let #[_, _, _, _, f] := (← getExpr).getAppArgs | failure
  guard f.isLambda
  let ppDomain ← withAppArg <| getPPOption getPPFunBinderTypes
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i => do
    return ((⟨i⟩ : Ident), ← delab)
  let res ← withNaryArg 3 <| delabFinsetArg i
  match res with
  | .finset ss => `(∑ $i:ident ∈ $ss, $body)
  | .univ =>
    let binder ←
    if ppDomain then
      let ty ← withNaryArg 0 delab
      `(bigOpBinder| $i:ident : $ty)
    else
      `(bigOpBinder| $i:ident)
    `(∑ $binder:bigOpBinder, $body)
  | .filter ss p =>
    `(∑ $i:ident ∈ $ss with $p, $body)
  | .filterUniv p =>
    let binder ←
    if ppDomain then
      let ty ← withNaryArg 0 delab
      `(bigOpBinder| $i:ident : $ty)
    else
      `(bigOpBinder| $i:ident)
    `(∑ $binder:bigOpBinder with $p, $body)

end BigOperators

namespace Finset

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

@[to_additive]
theorem prod_eq_multiset_prod [CommMonoid M] (s : Finset ι) (f : ι → M) :
    ∏ x ∈ s, f x = (s.1.map f).prod :=
  rfl

@[to_additive (attr := simp)]
lemma prod_map_val [CommMonoid M] (s : Finset ι) (f : ι → M) : (s.1.map f).prod = ∏ a ∈ s, f a :=
  rfl

@[simp]
theorem sum_multiset_singleton (s : Finset ι) : ∑ a ∈ s, {a} = s.val := by
  simp only [sum_eq_multiset_sum, Multiset.sum_map_singleton]

end Finset

@[to_additive (attr := simp)]
theorem map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G M N] [MonoidHomClass G M N]
    (g : G) (f : ι → M) (s : Finset ι) : g (∏ x ∈ s, f x) = ∏ x ∈ s, g (f x) := by
  simp only [Finset.prod_eq_multiset_prod, map_multiset_prod, Multiset.map_map]; rfl

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

namespace Finset

section CommMonoid

variable [CommMonoid M]

@[to_additive (attr := simp)]
theorem prod_empty : ∏ x ∈ ∅, f x = 1 :=
  rfl

/-- Variant of `prod_empty` not applied to a function. -/
@[to_additive (attr := grind =)]
theorem prod_empty' : Finset.prod (∅ : Finset ι) = fun (_ : ι → M) => 1 :=
  rfl

@[to_additive]
theorem prod_of_isEmpty [IsEmpty ι] (s : Finset ι) : ∏ i ∈ s, f i = 1 := by
  rw [eq_empty_of_isEmpty s, prod_empty]

@[to_additive (attr := simp)]
theorem prod_const_one : (∏ _x ∈ s, (1 : M)) = 1 := by
  simp only [Finset.prod, Multiset.map_const', Multiset.prod_replicate, one_pow]

@[to_additive (attr := simp)]
theorem prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ → M) :
    ∏ x ∈ s.map e, f x = ∏ x ∈ s, f (e x) := by
  rw [Finset.prod, Finset.map_val, Multiset.map_map]; rfl

/-- Variant of `prod_map` not applied to a function. -/
@[to_additive (attr := grind =)]
theorem prod_map' (s : Finset ι) (e : ι ↪ κ) :
    Finset.prod (s.map e) = fun (f : κ → M) => ∏ x ∈ s, f (e x) := by
  funext f
  simp

section ToList

@[to_additive (attr := simp, grind =)]
theorem prod_map_toList (s : Finset ι) (f : ι → M) : (s.toList.map f).prod = s.prod f := by
  rw [Finset.prod, ← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]

@[to_additive (attr := simp, grind =)]
theorem prod_toList {M : Type*} [CommMonoid M] (s : Finset M) :
    s.toList.prod = ∏ x ∈ s, x := by
  simpa using s.prod_map_toList id

end ToList

@[to_additive]
theorem _root_.Equiv.Perm.prod_comp (σ : Equiv.Perm ι) (s : Finset ι) (f : ι → M)
    (hs : { a | σ a ≠ a } ⊆ s) : (∏ x ∈ s, f (σ x)) = ∏ x ∈ s, f x := by
  convert (prod_map s σ.toEmbedding f).symm
  exact (map_perm hs).symm

@[to_additive]
theorem _root_.Equiv.Perm.prod_comp' (σ : Equiv.Perm ι) (s : Finset ι) (f : ι → ι → M)
    (hs : { a | σ a ≠ a } ⊆ s) : (∏ x ∈ s, f (σ x) x) = ∏ x ∈ s, f x (σ.symm x) := by
  convert σ.prod_comp s (fun x => f x (σ.symm x)) hs
  rw [Equiv.symm_apply_apply]

end CommMonoid

end Finset

namespace Finset

section CommMonoid

variable [CommMonoid M]

section bij
variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

/-- Reorder a product.

The difference with `Finset.prod_bij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.prod_nbij` is that the bijection is allowed to use membership of the
domain of the product, rather than being a non-dependent function. -/
@[to_additive /-- Reorder a sum.

The difference with `Finset.sum_bij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.sum_nbij` is that the bijection is allowed to use membership of the
domain of the sum, rather than being a non-dependent function. -/]
theorem prod_bij (i : ∀ a ∈ s, κ) (hi : ∀ a ha, i a ha ∈ t)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) (h : ∀ a ha, f a = g (i a ha)) :
    ∏ x ∈ s, f x = ∏ x ∈ t, g x :=
  congr_arg Multiset.prod (Multiset.map_eq_map_of_bij_of_nodup f g s.2 t.2 i hi i_inj i_surj h)

/-- Reorder a product.

The difference with `Finset.prod_bij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.prod_nbij'` is that the bijection and its inverse are allowed to use
membership of the domains of the products, rather than being non-dependent functions. -/
@[to_additive /-- Reorder a sum.

The difference with `Finset.sum_bij` is that the bijection is specified with an inverse, rather than
as a surjective injection.

The difference with `Finset.sum_nbij'` is that the bijection and its inverse are allowed to use
membership of the domains of the sums, rather than being non-dependent functions. -/]
theorem prod_bij' (i : ∀ a ∈ s, κ) (j : ∀ a ∈ t, ι) (hi : ∀ a ha, i a ha ∈ t)
    (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) (h : ∀ a ha, f a = g (i a ha)) :
    ∏ x ∈ s, f x = ∏ x ∈ t, g x := by
  refine prod_bij i hi (fun a1 h1 a2 h2 eq ↦ ?_) (fun b hb ↦ ⟨_, hj b hb, right_inv b hb⟩) h
  rw [← left_inv a1 h1, ← left_inv a2 h2]
  simp only [eq]

/-- Reorder a product.

The difference with `Finset.prod_nbij'` is that the bijection is specified as a surjective
injection, rather than by an inverse function.

The difference with `Finset.prod_bij` is that the bijection is a non-dependent function, rather than
being allowed to use membership of the domain of the product. -/
@[to_additive /-- Reorder a sum.

The difference with `Finset.sum_nbij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.sum_bij` is that the bijection is a non-dependent function, rather than
being allowed to use membership of the domain of the sum. -/]
lemma prod_nbij (i : ι → κ) (hi : ∀ a ∈ s, i a ∈ t) (i_inj : (s : Set ι).InjOn i)
    (i_surj : (s : Set ι).SurjOn i t) (h : ∀ a ∈ s, f a = g (i a)) :
    ∏ x ∈ s, f x = ∏ x ∈ t, g x :=
  prod_bij (fun a _ ↦ i a) hi i_inj (by simpa using i_surj) h

/-- Reorder a product.

The difference with `Finset.prod_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.prod_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains of the products.

The difference with `Finset.prod_equiv` is that bijectivity is only required to hold on the domains
of the products, rather than on the entire types.
-/
@[to_additive /-- Reorder a sum.

The difference with `Finset.sum_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.sum_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains of the sums.

The difference with `Finset.sum_equiv` is that bijectivity is only required to hold on the domains
of the sums, rather than on the entire types. -/]
lemma prod_nbij' (i : ι → κ) (j : κ → ι) (hi : ∀ a ∈ s, i a ∈ t) (hj : ∀ a ∈ t, j a ∈ s)
    (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a)
    (h : ∀ a ∈ s, f a = g (i a)) : ∏ x ∈ s, f x = ∏ x ∈ t, g x :=
  prod_bij' (fun a _ ↦ i a) (fun b _ ↦ j b) hi hj left_inv right_inv h

/-- Specialization of `Finset.prod_nbij'` that automatically fills in most arguments.

See `Fintype.prod_equiv` for the version where `s` and `t` are `univ`. -/
@[to_additive /-- Specialization of `Finset.sum_nbij'` that automatically fills in most arguments.

See `Fintype.sum_equiv` for the version where `s` and `t` are `univ`. -/]
lemma prod_equiv (e : ι ≃ κ) (hst : ∀ i, i ∈ s ↔ e i ∈ t) (hfg : ∀ i ∈ s, f i = g (e i)) :
    ∏ i ∈ s, f i = ∏ i ∈ t, g i := by refine prod_nbij' e e.symm ?_ ?_ ?_ ?_ hfg <;> simp [hst]

/-- Specialization of `Finset.prod_bij` that automatically fills in most arguments.

See `Fintype.prod_bijective` for the version where `s` and `t` are `univ`. -/
@[to_additive /-- Specialization of `Finset.sum_bij` that automatically fills in most arguments.

See `Fintype.sum_bijective` for the version where `s` and `t` are `univ`. -/]
lemma prod_bijective (e : ι → κ) (he : e.Bijective) (hst : ∀ i, i ∈ s ↔ e i ∈ t)
    (hfg : ∀ i ∈ s, f i = g (e i)) :
    ∏ i ∈ s, f i = ∏ i ∈ t, g i := prod_equiv (.ofBijective e he) hst hfg

end bij

@[to_additive]
theorem prod_hom_rel [CommMonoid N] {r : M → N → Prop} {f : ι → M} {g : ι → N} {s : Finset ι}
    (h₁ : r 1 1) (h₂ : ∀ a b c, r b c → r (f a * b) (g a * c)) :
    r (∏ x ∈ s, f x) (∏ x ∈ s, g x) := by
  delta Finset.prod
  apply Multiset.prod_hom_rel <;> assumption

variable (f s)

@[to_additive]
theorem prod_coe_sort_eq_attach (f : s → M) : ∏ i : s, f i = ∏ i ∈ s.attach, f i :=
  rfl

variable {f s}

@[to_additive]
theorem prod_ite_index (p : Prop) [Decidable p] (s t : Finset ι) (f : ι → M) :
    ∏ x ∈ if p then s else t, f x = if p then ∏ x ∈ s, f x else ∏ x ∈ t, f x :=
  apply_ite (fun s => ∏ x ∈ s, f x) _ _ _

@[to_additive (attr := simp)]
theorem prod_ite_irrel (p : Prop) [Decidable p] (s : Finset ι) (f g : ι → M) :
    ∏ x ∈ s, (if p then f x else g x) = if p then ∏ x ∈ s, f x else ∏ x ∈ s, g x := by
  split_ifs with h <;> rfl

@[to_additive (attr := simp)]
theorem prod_dite_irrel (p : Prop) [Decidable p] (s : Finset ι) (f : p → ι → M) (g : ¬p → ι → M) :
    ∏ x ∈ s, (if h : p then f h x else g h x) =
      if h : p then ∏ x ∈ s, f h x else ∏ x ∈ s, g h x := by
  split_ifs with h <;> rfl

@[to_additive]
theorem ite_prod_one (p : Prop) [Decidable p] (s : Finset ι) (f : ι → M) :
    (if p then (∏ x ∈ s, f x) else 1) = ∏ x ∈ s, if p then f x else 1 := by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]
theorem ite_one_prod (p : Prop) [Decidable p] (s : Finset ι) (f : ι → M) :
    (if p then 1 else (∏ x ∈ s, f x)) = ∏ x ∈ s, if p then 1 else f x := by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]
theorem nonempty_of_prod_ne_one (h : ∏ x ∈ s, f x ≠ 1) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun H => False.elim <| h <| H.symm ▸ prod_empty) id

@[to_additive]
theorem prod_range_zero (f : ℕ → M) : ∏ k ∈ range 0, f k = 1 := by rw [range_zero, prod_empty]

open List

theorem sum_filter_count_eq_countP [DecidableEq ι] (p : ι → Prop) [DecidablePred p] (l : List ι) :
    ∑ x ∈ l.toFinset with p x, l.count x = l.countP p := by
  simp [Finset.sum, sum_map_count_dedup_filter_eq_countP p l]

open Multiset


@[to_additive]
theorem prod_mem_multiset [DecidableEq ι] (m : Multiset ι) (f : { x // x ∈ m } → M) (g : ι → M)
    (hfg : ∀ x, f x = g x) : ∏ x : { x // x ∈ m }, f x = ∏ x ∈ m.toFinset, g x := by
  refine prod_bij' (fun x _ ↦ x) (fun x hx ↦ ⟨x, Multiset.mem_toFinset.1 hx⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp [hfg]

/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors. -/
@[to_additive /-- To prove a property of a sum, it suffices to prove that
the property is additive and holds on summands. -/]
theorem prod_induction {M : Type*} [CommMonoid M] (f : ι → M) (p : M → Prop)
    (hom : ∀ a b, p a → p b → p (a * b)) (unit : p 1) (base : ∀ x ∈ s, p <| f x) :
    p <| ∏ x ∈ s, f x :=
  Multiset.prod_induction _ _ hom unit (Multiset.forall_mem_map_iff.mpr base)

/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors. -/
@[to_additive /-- To prove a property of a sum, it suffices to prove that
the property is additive and holds on summands. -/]
theorem prod_induction_nonempty {M : Type*} [CommMonoid M] (f : ι → M) (p : M → Prop)
    (hom : ∀ a b, p a → p b → p (a * b)) (nonempty : s.Nonempty) (base : ∀ x ∈ s, p <| f x) :
    p <| ∏ x ∈ s, f x :=
  Multiset.prod_induction_nonempty p hom (by simp [nonempty_iff_ne_empty.mp nonempty])
    (Multiset.forall_mem_map_iff.mpr base)

@[to_additive]
theorem prod_pow (s : Finset ι) (n : ℕ) (f : ι → M) : ∏ x ∈ s, f x ^ n = (∏ x ∈ s, f x) ^ n :=
  Multiset.prod_map_pow

theorem prod_dvd_prod_of_subset {ι M : Type*} [CommMonoid M] (s t : Finset ι) (f : ι → M)
    (h : s ⊆ t) : (∏ i ∈ s, f i) ∣ ∏ i ∈ t, f i :=
  Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| by simpa

end CommMonoid

section MulOpposite
variable [AddCommMonoid M] (s : Finset ι)

open MulOpposite

/-- Moving to the opposite additive commutative monoid commutes with summing. -/
@[simp] lemma op_sum (f : ι → M) : op (∑ x ∈ s, f x) = ∑ x ∈ s, op (f x) := map_sum opAddEquiv ..

@[simp] lemma unop_sum (f : ι → Mᵐᵒᵖ) : unop (∑ x ∈ s, f x) = ∑ x ∈ s, unop (f x) :=
  map_sum opAddEquiv.symm ..

end MulOpposite

section AddOpposite
variable [CommMonoid M] (s : Finset ι)

open AddOpposite

@[simp] lemma op_prod (f : ι → M) : op (∏ i ∈ s, f i) = ∏ i ∈ s, op (f i) := map_prod opMulEquiv ..

@[simp] lemma unop_prod (f : ι → Mᵐᵒᵖ) : unop (∏ i ∈ s, f i) = ∏ i ∈ s, unop (f i) :=
  map_prod opMulEquiv.symm ..

end AddOpposite

section DivisionCommMonoid

variable [DivisionCommMonoid G]

@[to_additive (attr := simp)]
theorem prod_inv_distrib (f : ι → G) : (∏ x ∈ s, (f x)⁻¹) = (∏ x ∈ s, f x)⁻¹ :=
  Multiset.prod_map_inv

@[to_additive (attr := simp)]
theorem prod_div_distrib (f g : ι → G) : ∏ x ∈ s, f x / g x = (∏ x ∈ s, f x) / ∏ x ∈ s, g x :=
  Multiset.prod_map_div

@[to_additive]
theorem prod_zpow (f : ι → G) (s : Finset ι) (n : ℤ) : ∏ a ∈ s, f a ^ n = (∏ a ∈ s, f a) ^ n :=
  Multiset.prod_map_zpow

end DivisionCommMonoid

theorem sum_nat_mod (s : Finset ι) (n : ℕ) (f : ι → ℕ) :
    (∑ i ∈ s, f i) % n = (∑ i ∈ s, f i % n) % n :=
  (Multiset.sum_nat_mod _ _).trans <| by rw [Finset.sum, Multiset.map_map]; rfl

theorem prod_nat_mod (s : Finset ι) (n : ℕ) (f : ι → ℕ) :
    (∏ i ∈ s, f i) % n = (∏ i ∈ s, f i % n) % n :=
  (Multiset.prod_nat_mod _ _).trans <| by rw [Finset.prod, Multiset.map_map]; rfl

theorem sum_int_mod (s : Finset ι) (n : ℤ) (f : ι → ℤ) :
    (∑ i ∈ s, f i) % n = (∑ i ∈ s, f i % n) % n :=
  (Multiset.sum_int_mod _ _).trans <| by rw [Finset.sum, Multiset.map_map]; rfl

theorem prod_int_mod (s : Finset ι) (n : ℤ) (f : ι → ℤ) :
    (∏ i ∈ s, f i) % n = (∏ i ∈ s, f i % n) % n :=
  (Multiset.prod_int_mod _ _).trans <| by rw [Finset.prod, Multiset.map_map]; rfl

end Finset

namespace Fintype
variable [Fintype ι] [Fintype κ]

open Finset

section CommMonoid
variable [CommMonoid M]

/-- `Fintype.prod_bijective` is a variant of `Finset.prod_bij` that accepts `Function.Bijective`.

See `Function.Bijective.prod_comp` for a version without `h`. -/
@[to_additive /-- `Fintype.sum_bijective` is a variant of `Finset.sum_bij` that accepts
`Function.Bijective`.

See `Function.Bijective.sum_comp` for a version without `h`. -/]
lemma prod_bijective (e : ι → κ) (he : e.Bijective) (f : ι → M) (g : κ → M)
    (h : ∀ x, f x = g (e x)) : ∏ x, f x = ∏ x, g x :=
  prod_equiv (.ofBijective e he) (by simp) (by simp [h])

@[to_additive] alias _root_.Function.Bijective.finsetProd := prod_bijective

@[deprecated (since := "2026-04-08")]
alias _root_.Function.Bijective.finset_sum := _root_.Function.Bijective.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias _root_.Function.Bijective.finset_prod := _root_.Function.Bijective.finsetProd

/-- `Fintype.prod_equiv` is a specialization of `Finset.prod_bij` that
automatically fills in most arguments.

See `Equiv.prod_comp` for a version without `h`.
-/
@[to_additive /-- `Fintype.sum_equiv` is a specialization of `Finset.sum_bij` that
automatically fills in most arguments.

See `Equiv.sum_comp` for a version without `h`. -/]
lemma prod_equiv (e : ι ≃ κ) (f : ι → M) (g : κ → M) (h : ∀ x, f x = g (e x)) :
    ∏ x, f x = ∏ x, g x := prod_bijective _ e.bijective _ _ h

@[to_additive]
lemma _root_.Function.Bijective.prod_comp {e : ι → κ} (he : e.Bijective) (g : κ → M) :
    ∏ i, g (e i) = ∏ i, g i := prod_bijective _ he _ _ fun _ ↦ rfl

@[to_additive]
lemma _root_.Equiv.prod_comp (e : ι ≃ κ) (g : κ → M) : ∏ i, g (e i) = ∏ i, g i :=
  prod_equiv e _ _ fun _ ↦ rfl

@[to_additive]
theorem prod_empty [IsEmpty ι] (f : ι → M) : ∏ x : ι, f x = 1 := prod_of_isEmpty _

end CommMonoid
end Fintype

namespace Finset
variable [CommMonoid M]

@[to_additive (attr := simp)]
lemma prod_attach_univ [Fintype ι] (f : {i // i ∈ @univ ι _} → M) :
    ∏ i ∈ univ.attach, f i = ∏ i, f ⟨i, mem_univ _⟩ :=
  Fintype.prod_equiv (Equiv.subtypeUnivEquiv mem_univ) _ _ <| by simp

@[to_additive]
theorem prod_erase_attach [DecidableEq ι] {s : Finset ι} (f : ι → M) (i : ↑s) :
    ∏ j ∈ s.attach.erase i, f ↑j = ∏ j ∈ s.erase ↑i, f j := by
  rw [← Function.Embedding.coe_subtype, ← prod_map]
  simp [attach_map_val]

end Finset

namespace Multiset

@[simp]
lemma card_sum (s : Finset ι) (f : ι → Multiset α) : card (∑ i ∈ s, f i) = ∑ i ∈ s, card (f i) :=
  map_sum cardHom ..

theorem disjoint_list_sum_left {a : Multiset α} {l : List (Multiset α)} :
    Disjoint l.sum a ↔ ∀ b ∈ l, Disjoint b a := by
  induction l with
  | nil =>
    simp only [zero_disjoint, List.not_mem_nil, IsEmpty.forall_iff, forall_const, List.sum_nil]
  | cons b bs ih =>
    simp [ih]

theorem disjoint_list_sum_right {a : Multiset α} {l : List (Multiset α)} :
    Disjoint a l.sum ↔ ∀ b ∈ l, Disjoint a b := by
  simpa only [disjoint_comm (a := a)] using disjoint_list_sum_left

theorem disjoint_sum_left {a : Multiset α} {i : Multiset (Multiset α)} :
    Disjoint i.sum a ↔ ∀ b ∈ i, Disjoint b a :=
  Quotient.inductionOn i fun l => by
    rw [quot_mk_to_coe, Multiset.sum_coe]
    exact disjoint_list_sum_left

theorem disjoint_sum_right {a : Multiset α} {i : Multiset (Multiset α)} :
    Disjoint a i.sum ↔ ∀ b ∈ i, Disjoint a b := by
  simpa only [disjoint_comm (a := a)] using disjoint_sum_left

theorem disjoint_finsetSum_left {i : Finset ι} {f : ι → Multiset α} {a : Multiset α} :
    Disjoint (i.sum f) a ↔ ∀ b ∈ i, Disjoint (f b) a := by
  convert @disjoint_sum_left _ a (map f i.val)
  simp

@[deprecated (since := "2026-04-08")] alias disjoint_finset_sum_left := disjoint_finsetSum_left

theorem disjoint_finsetSum_right {i : Finset ι} {f : ι → Multiset α}
    {a : Multiset α} : Disjoint a (i.sum f) ↔ ∀ b ∈ i, Disjoint a (f b) := by
  simpa only [disjoint_comm] using disjoint_finsetSum_left

@[deprecated (since := "2026-04-08")] alias disjoint_finset_sum_right := disjoint_finsetSum_right

variable [DecidableEq α]

theorem count_sum' {s : Finset ι} {a : α} {f : ι → Multiset α} :
    count a (∑ x ∈ s, f x) = ∑ x ∈ s, count a (f x) := by
  dsimp only [Finset.sum]
  rw [count_sum]

theorem toFinset_prod_dvd_prod [DecidableEq M] [CommMonoid M] (S : Multiset M) :
    S.toFinset.prod id ∣ S.prod := by
  rw [Finset.prod_eq_multiset_prod]
  refine Multiset.prod_dvd_prod_of_le ?_
  simp [Multiset.dedup_le S]

end Multiset

@[simp, norm_cast]
theorem Units.coe_prod [CommMonoid M] (f : α → Mˣ) (s : Finset α) :
    (↑(∏ i ∈ s, f i) : M) = ∏ i ∈ s, (f i : M) :=
  map_prod (Units.coeHom M) _ _


/-! ### `Additive`, `Multiplicative` -/


open Additive Multiplicative

section Monoid

variable [Monoid M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem ofMul_list_prod (s : List M) : ofMul s.prod = (s.map ofMul).sum := by simp [ofMul]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem toMul_list_sum (s : List (Additive M)) : s.sum.toMul = (s.map toMul).prod := by
  simp [toMul, ofMul]; rfl

end Monoid

section AddMonoid

variable [AddMonoid M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem ofAdd_list_prod (s : List M) : ofAdd s.sum = (s.map ofAdd).prod := by simp [ofAdd]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem toAdd_list_sum (s : List (Multiplicative M)) : s.prod.toAdd = (s.map toAdd).sum := by
  simp [toAdd, ofAdd]; rfl

end AddMonoid

section CommMonoid

variable [CommMonoid M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem ofMul_multiset_prod (s : Multiset M) : ofMul s.prod = (s.map ofMul).sum := by
  simp [ofMul]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem toMul_multiset_sum (s : Multiset (Additive M)) : s.sum.toMul = (s.map toMul).prod := by
  simp [toMul, ofMul]; rfl

@[simp]
theorem ofMul_prod (s : Finset ι) (f : ι → M) : ofMul (∏ i ∈ s, f i) = ∑ i ∈ s, ofMul (f i) :=
  rfl

@[simp]
theorem toMul_sum (s : Finset ι) (f : ι → Additive M) :
    (∑ i ∈ s, f i).toMul = ∏ i ∈ s, (f i).toMul :=
  rfl

end CommMonoid

section AddCommMonoid

variable [AddCommMonoid M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem ofAdd_multiset_prod (s : Multiset M) : ofAdd s.sum = (s.map ofAdd).prod := by
  simp [ofAdd]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem toAdd_multiset_sum (s : Multiset (Multiplicative M)) :
    s.prod.toAdd = (s.map toAdd).sum := by
  simp [toAdd, ofAdd]; rfl

@[simp]
theorem ofAdd_sum (s : Finset ι) (f : ι → M) : ofAdd (∑ i ∈ s, f i) = ∏ i ∈ s, ofAdd (f i) :=
  rfl

@[simp]
theorem toAdd_prod (s : Finset ι) (f : ι → Multiplicative M) :
    (∏ i ∈ s, f i).toAdd = ∑ i ∈ s, (f i).toAdd :=
  rfl

end AddCommMonoid
