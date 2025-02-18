/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Multiset.Bind

/-!
# Big operators

In this file we define products and sums indexed by finite sets (specifically, `Finset`).

## Notation

We introduce the following notation.

Let `s` be a `Finset α`, and `f : α → β` a function.

* `∏ x ∈ s, f x` is notation for `Finset.prod s f` (assuming `β` is a `CommMonoid`)
* `∑ x ∈ s, f x` is notation for `Finset.sum s f` (assuming `β` is an `AddCommMonoid`)
* `∏ x, f x` is notation for `Finset.prod Finset.univ f`
  (assuming `α` is a `Fintype` and `β` is a `CommMonoid`)
* `∑ x, f x` is notation for `Finset.sum Finset.univ f`
  (assuming `α` is a `Fintype` and `β` is an `AddCommMonoid`)

## Implementation Notes

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

-/

-- TODO
-- assert_not_exists AddCommMonoidWithOne
assert_not_exists MonoidWithZero
assert_not_exists MulAction
assert_not_exists OrderedCommMonoid

variable {ι κ α β γ : Type*}

open Fin Function

namespace Finset

/-- `∏ x ∈ s, f x` is the product of `f x` as `x` ranges over the elements of the finite set `s`.

When the index type is a `Fintype`, the notation `∏ x, f x`, is a shorthand for
`∏ x ∈ Finset.univ, f x`. -/
@[to_additive "`∑ x ∈ s, f x` is the sum of `f x` as `x` ranges over the elements
of the finite set `s`.

When the index type is a `Fintype`, the notation `∑ x, f x`, is a shorthand for
`∑ x ∈ Finset.univ, f x`."]
protected def prod [CommMonoid β] (s : Finset α) (f : α → β) : β :=
  (s.1.map f).prod

@[to_additive (attr := simp)]
theorem prod_mk [CommMonoid β] (s : Multiset α) (hs : s.Nodup) (f : α → β) :
    (⟨s, hs⟩ : Finset α).prod f = (s.map f).prod :=
  rfl

@[to_additive (attr := simp)]
theorem prod_val [CommMonoid α] (s : Finset α) : s.1.prod = s.prod id := by
  rw [Finset.prod, Multiset.map_id]

end Finset

library_note "operator precedence of big operators"/--
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
syntax bigOpBinder := term:max ((" : " term) <|> binderPred)?
/-- A BigOperator binder in parentheses -/
syntax bigOpBinderParenthesized := " (" bigOpBinder ")"
/-- A list of parenthesized binders -/
syntax bigOpBinderCollection := bigOpBinderParenthesized+
/-- A single (unparenthesized) binder, or a list of parenthesized binders -/
syntax bigOpBinders := bigOpBinderCollection <|> (ppSpace bigOpBinder)

/-- Collects additional binder/Finset pairs for the given `bigOpBinder`.
Note: this is not extensible at the moment, unlike the usual `bigOpBinder` expansions. -/
def processBigOpBinder (processed : (Array (Term × Term)))
    (binder : TSyntax ``bigOpBinder) : MacroM (Array (Term × Term)) :=
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
    | `(bigOpBinder| $x < $n) => return processed |>.push (x, ← `(Finset.Iio $n))
    | `(bigOpBinder| $x ≤ $n) => return processed |>.push (x, ← `(Finset.Iic $n))
    | `(bigOpBinder| $x > $n) => return processed |>.push (x, ← `(Finset.Ioi $n))
    | `(bigOpBinder| $x ≥ $n) => return processed |>.push (x, ← `(Finset.Ici $n))
    | _ => Macro.throwUnsupported

/-- Collects the binder/Finset pairs for the given `bigOpBinders`. -/
def processBigOpBinders (binders : TSyntax ``bigOpBinders) :
    MacroM (Array (Term × Term)) :=
  match binders with
  | `(bigOpBinders| $b:bigOpBinder) => processBigOpBinder #[] b
  | `(bigOpBinders| $[($bs:bigOpBinder)]*) => bs.foldlM processBigOpBinder #[]
  | _ => Macro.throwUnsupported

/-- Collect the binderIdents into a `⟨...⟩` expression. -/
def bigOpBindersPattern (processed : (Array (Term × Term))) :
    MacroM Term := do
  let ts := processed.map Prod.fst
  if ts.size == 1 then
    return ts[0]!
  else
    `(⟨$ts,*⟩)

/-- Collect the terms into a product of sets. -/
def bigOpBindersProd (processed : (Array (Term × Term))) :
    MacroM Term := do
  if processed.isEmpty then
    `((Finset.univ : Finset Unit))
  else if processed.size == 1 then
    return processed[0]!.2
  else
    processed.foldrM (fun s p => `(SProd.sprod $(s.2) $p)) processed.back!.2
      (start := processed.size - 1)

/--
- `∑ x, f x` is notation for `Finset.sum Finset.univ f`. It is the sum of `f x`,
  where `x` ranges over the finite domain of `f`.
- `∑ x ∈ s, f x` is notation for `Finset.sum s f`. It is the sum of `f x`,
  where `x` ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
- `∑ x ∈ s with p x, f x` is notation for `Finset.sum (Finset.filter p s) f`.
- `∑ (x ∈ s) (y ∈ t), f x y` is notation for `Finset.sum (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.

These support destructuring, for example `∑ ⟨x, y⟩ ∈ s ×ˢ t, f x y`.

Notation: `"∑" bigOpBinders* ("with" term)? "," term` -/
syntax (name := bigsum) "∑ " bigOpBinders ("with " term)? ", " term:67 : term

/--
- `∏ x, f x` is notation for `Finset.prod Finset.univ f`. It is the product of `f x`,
  where `x` ranges over the finite domain of `f`.
- `∏ x ∈ s, f x` is notation for `Finset.prod s f`. It is the product of `f x`,
  where `x` ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
- `∏ x ∈ s with p x, f x` is notation for `Finset.prod (Finset.filter p s) f`.
- `∏ (x ∈ s) (y ∈ t), f x y` is notation for `Finset.prod (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.

These support destructuring, for example `∏ ⟨x, y⟩ ∈ s ×ˢ t, f x y`.

Notation: `"∏" bigOpBinders* ("with" term)? "," term` -/
syntax (name := bigprod) "∏ " bigOpBinders ("with " term)? ", " term:67 : term

macro_rules (kind := bigsum)
  | `(∑ $bs:bigOpBinders $[with $p?]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    match p? with
    | some p => `(Finset.sum (Finset.filter (fun $x ↦ $p) $s) (fun $x ↦ $v))
    | none => `(Finset.sum $s (fun $x ↦ $v))

macro_rules (kind := bigprod)
  | `(∏ $bs:bigOpBinders $[with $p?]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    match p? with
    | some p => `(Finset.prod (Finset.filter (fun $x ↦ $p) $s) (fun $x ↦ $v))
    | none => `(Finset.prod $s (fun $x ↦ $v))

section deprecated -- since 2024-30-01
open Elab Term Tactic TryThis

/-- Deprecated, use `∑ x ∈ s, f x` instead. -/
syntax (name := bigsumin) "∑ " extBinder " in " term ", " term:67 : term

/-- Deprecated, use `∏ x ∈ s, f x` instead. -/
syntax (name := bigprodin) "∏ " extBinder " in " term ", " term:67 : term

elab_rules : term
  | `(∑%$tk $x:ident in $s, $r) => do
    addSuggestion tk (← `(∑ $x ∈ $s, $r)) (origSpan? := ← getRef) (header :=
      "The '∑ x in s, f x' notation is deprecated: please use '∑ x ∈ s, f x' instead:\n")
    elabTerm (← `(∑ $x:ident ∈ $s, $r)) none
  | `(∑%$tk $x:ident : $_t in $s, $r) => do
    addSuggestion tk (← `(∑ $x ∈ $s, $r)) (origSpan? := ← getRef) (header :=
      "The '∑ x : t in s, f x' notation is deprecated: please use '∑ x ∈ s, f x' instead:\n")
    elabTerm (← `(∑ $x:ident ∈ $s, $r)) none

elab_rules : term
  | `(∏%$tk $x:ident in $s, $r) => do
    addSuggestion tk (← `(∏ $x ∈ $s, $r)) (origSpan? := ← getRef) (header :=
      "The '∏ x in s, f x' notation is deprecated: please use '∏ x ∈ s, f x' instead:\n")
    elabTerm (← `(∏ $x:ident ∈ $s, $r)) none
  | `(∏%$tk $x:ident : $_t in $s, $r) => do
    addSuggestion tk (← `(∏ $x ∈ $s, $r)) (origSpan? := ← getRef) (header :=
      "The '∏ x : t in s, f x' notation is deprecated: please use '∏ x ∈ s, f x' instead:\n")
    elabTerm (← `(∏ $x:ident ∈ $s, $r)) none

end deprecated

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr Qq
open scoped Batteries.ExtendedBinder

/-- For a finset of the form `{x ∈ s | p x}`, returns `(s, some p)`. For any other finset `s`,
returns `(s, none)`. -/
def getFinsetFilter {u : Level} {α : Q(Type u)} (s : Q(Finset $α)) :
    MetaM (Q(Finset $α) × Option Q($α → Prop)) := do
  match s with
  | ~q(@Finset.filter _ _ $s $p) => return (s, some p)
  | _ => return (s, none)

/-- Delaborator for `Finset.prod`. The `pp.piBinderTypes` option controls whether
to show the domain type when the product is over `Finset.univ`. -/
@[app_delab Finset.prod] def delabFinsetProd : Delab :=
  whenPPOption getPPNotation <| withOverApp 5 <| do
  let #[_, _, _, s, f] := (← getExpr).getAppArgs | failure
  guard f.isLambda
  let ppDomain ← getPPOption getPPPiBinderTypes
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i => do
    return (i, ← delab)
  let ⟨.succ _, ~q(Finset $α), s⟩ ← inferTypeQ s | failure
  let (s, p) ← getFinsetFilter (α := α) s
  if s.isAppOfArity ``Finset.univ 2 then
    let binder ←
      if ppDomain then
        let ty ← withNaryArg 0 delab
        `(bigOpBinder| $(.mk i):ident : $ty)
      else
        `(bigOpBinder| $(.mk i):ident)
    -- Help! How do I delaborate `s` and `p` here?
    match p with
    | some _ => `(∏ $binder:bigOpBinder, $body)
    | none => `(∏ $binder:bigOpBinder, $body)
  else
    let ss ← withNaryArg 3 delab
    match p with
    | some _ => `(∏ $(.mk i):ident ∈ $ss, $body)
    | none => `(∏ $(.mk i):ident ∈ $ss, $body)

/-- Delaborator for `Finset.sum`. The `pp.piBinderTypes` option controls whether
to show the domain type when the sum is over `Finset.univ`. -/
@[app_delab Finset.sum] def delabFinsetSum : Delab :=
  whenPPOption getPPNotation <| withOverApp 5 <| do
  let #[_, _, _, s, f] := (← getExpr).getAppArgs | failure
  guard f.isLambda
  let ppDomain ← getPPOption getPPPiBinderTypes
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i => do
    return (i, ← delab)
  if s.isAppOfArity ``Finset.univ 2 then
    let binder ←
      if ppDomain then
        let ty ← withNaryArg 0 delab
        `(bigOpBinder| $(.mk i):ident : $ty)
      else
        `(bigOpBinder| $(.mk i):ident)
    `(∑ $binder:bigOpBinder, $body)
  else
    let ss ← withNaryArg 3 delab
    `(∑ $(.mk i):ident ∈ $ss, $body)

end BigOperators

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

@[to_additive]
theorem prod_eq_multiset_prod [CommMonoid β] (s : Finset α) (f : α → β) :
    ∏ x ∈ s, f x = (s.1.map f).prod :=
  rfl

@[to_additive (attr := simp)]
lemma prod_map_val [CommMonoid β] (s : Finset α) (f : α → β) : (s.1.map f).prod = ∏ a ∈ s, f a :=
  rfl

@[simp]
theorem sum_multiset_singleton (s : Finset α) : ∑ a ∈ s, {a} = s.val := by
  simp only [sum_eq_multiset_sum, Multiset.sum_map_singleton]

end Finset

@[to_additive (attr := simp)]
theorem map_prod [CommMonoid β] [CommMonoid γ] {G : Type*} [FunLike G β γ] [MonoidHomClass G β γ]
    (g : G) (f : α → β) (s : Finset α) : g (∏ x ∈ s, f x) = ∏ x ∈ s, g (f x) := by
  simp only [Finset.prod_eq_multiset_prod, map_multiset_prod, Multiset.map_map]; rfl

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

namespace Finset

section CommMonoid

variable [CommMonoid β]

@[to_additive (attr := simp)]
theorem prod_empty : ∏ x ∈ ∅, f x = 1 :=
  rfl

@[to_additive]
theorem prod_of_isEmpty [IsEmpty α] (s : Finset α) : ∏ i ∈ s, f i = 1 := by
  rw [eq_empty_of_isEmpty s, prod_empty]

@[to_additive (attr := simp)]
theorem prod_const_one : (∏ _x ∈ s, (1 : β)) = 1 := by
  simp only [Finset.prod, Multiset.map_const', Multiset.prod_replicate, one_pow]

@[to_additive (attr := simp)]
theorem prod_map (s : Finset α) (e : α ↪ γ) (f : γ → β) :
    ∏ x ∈ s.map e, f x = ∏ x ∈ s, f (e x) := by
  rw [Finset.prod, Finset.map_val, Multiset.map_map]; rfl

section ToList

@[to_additive (attr := simp)]
theorem prod_to_list (s : Finset α) (f : α → β) : (s.toList.map f).prod = s.prod f := by
  rw [Finset.prod, ← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]

end ToList

@[to_additive]
theorem _root_.Equiv.Perm.prod_comp (σ : Equiv.Perm α) (s : Finset α) (f : α → β)
    (hs : { a | σ a ≠ a } ⊆ s) : (∏ x ∈ s, f (σ x)) = ∏ x ∈ s, f x := by
  convert (prod_map s σ.toEmbedding f).symm
  exact (map_perm hs).symm

@[to_additive]
theorem _root_.Equiv.Perm.prod_comp' (σ : Equiv.Perm α) (s : Finset α) (f : α → α → β)
    (hs : { a | σ a ≠ a } ⊆ s) : (∏ x ∈ s, f (σ x) x) = ∏ x ∈ s, f x (σ.symm x) := by
  convert σ.prod_comp s (fun x => f x (σ.symm x)) hs
  rw [Equiv.symm_apply_apply]

end CommMonoid

end Finset

namespace Finset

section CommMonoid

variable [CommMonoid β]

section bij
variable {ι κ α : Type*} [CommMonoid α] {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α}

/-- Reorder a product.

The difference with `Finset.prod_bij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.prod_nbij` is that the bijection is allowed to use membership of the
domain of the product, rather than being a non-dependent function. -/
@[to_additive "Reorder a sum.

The difference with `Finset.sum_bij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.sum_nbij` is that the bijection is allowed to use membership of the
domain of the sum, rather than being a non-dependent function."]
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
@[to_additive "Reorder a sum.

The difference with `Finset.sum_bij` is that the bijection is specified with an inverse, rather than
as a surjective injection.

The difference with `Finset.sum_nbij'` is that the bijection and its inverse are allowed to use
membership of the domains of the sums, rather than being non-dependent functions."]
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
@[to_additive "Reorder a sum.

The difference with `Finset.sum_nbij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.sum_bij` is that the bijection is a non-dependent function, rather than
being allowed to use membership of the domain of the sum."]
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
@[to_additive "Reorder a sum.

The difference with `Finset.sum_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.sum_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains of the sums.

The difference with `Finset.sum_equiv` is that bijectivity is only required to hold on the domains
of the sums, rather than on the entire types."]
lemma prod_nbij' (i : ι → κ) (j : κ → ι) (hi : ∀ a ∈ s, i a ∈ t) (hj : ∀ a ∈ t, j a ∈ s)
    (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a)
    (h : ∀ a ∈ s, f a = g (i a)) : ∏ x ∈ s, f x = ∏ x ∈ t, g x :=
  prod_bij' (fun a _ ↦ i a) (fun b _ ↦ j b) hi hj left_inv right_inv h

/-- Specialization of `Finset.prod_nbij'` that automatically fills in most arguments.

See `Fintype.prod_equiv` for the version where `s` and `t` are `univ`. -/
@[to_additive "`Specialization of `Finset.sum_nbij'` that automatically fills in most arguments.

See `Fintype.sum_equiv` for the version where `s` and `t` are `univ`."]
lemma prod_equiv (e : ι ≃ κ) (hst : ∀ i, i ∈ s ↔ e i ∈ t) (hfg : ∀ i ∈ s, f i = g (e i)) :
    ∏ i ∈ s, f i = ∏ i ∈ t, g i := by refine prod_nbij' e e.symm ?_ ?_ ?_ ?_ hfg <;> simp [hst]

/-- Specialization of `Finset.prod_bij` that automatically fills in most arguments.

See `Fintype.prod_bijective` for the version where `s` and `t` are `univ`. -/
@[to_additive "`Specialization of `Finset.sum_bij` that automatically fills in most arguments.

See `Fintype.sum_bijective` for the version where `s` and `t` are `univ`."]
lemma prod_bijective (e : ι → κ) (he : e.Bijective) (hst : ∀ i, i ∈ s ↔ e i ∈ t)
    (hfg : ∀ i ∈ s, f i = g (e i)) :
    ∏ i ∈ s, f i = ∏ i ∈ t, g i := prod_equiv (.ofBijective e he) hst hfg

end bij

@[to_additive]
theorem prod_hom_rel [CommMonoid γ] {r : β → γ → Prop} {f : α → β} {g : α → γ} {s : Finset α}
    (h₁ : r 1 1) (h₂ : ∀ a b c, r b c → r (f a * b) (g a * c)) :
    r (∏ x ∈ s, f x) (∏ x ∈ s, g x) := by
  delta Finset.prod
  apply Multiset.prod_hom_rel <;> assumption

variable (f s)

@[to_additive]
theorem prod_coe_sort_eq_attach (f : s → β) : ∏ i : s, f i = ∏ i ∈ s.attach, f i :=
  rfl

variable {f s}

@[to_additive]
theorem prod_ite_index (p : Prop) [Decidable p] (s t : Finset α) (f : α → β) :
    ∏ x ∈ if p then s else t, f x = if p then ∏ x ∈ s, f x else ∏ x ∈ t, f x :=
  apply_ite (fun s => ∏ x ∈ s, f x) _ _ _

@[to_additive (attr := simp)]
theorem prod_ite_irrel (p : Prop) [Decidable p] (s : Finset α) (f g : α → β) :
    ∏ x ∈ s, (if p then f x else g x) = if p then ∏ x ∈ s, f x else ∏ x ∈ s, g x := by
  split_ifs with h <;> rfl

@[to_additive (attr := simp)]
theorem prod_dite_irrel (p : Prop) [Decidable p] (s : Finset α) (f : p → α → β) (g : ¬p → α → β) :
    ∏ x ∈ s, (if h : p then f h x else g h x) =
      if h : p then ∏ x ∈ s, f h x else ∏ x ∈ s, g h x := by
  split_ifs with h <;> rfl

@[to_additive]
theorem ite_prod_one (p : Prop) [Decidable p] (s : Finset α) (f : α → β) :
    (if p then (∏ x ∈ s, f x) else 1) = ∏ x ∈ s, if p then f x else 1 := by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]
theorem ite_one_prod (p : Prop) [Decidable p] (s : Finset α) (f : α → β) :
    (if p then 1 else (∏ x ∈ s, f x)) = ∏ x ∈ s, if p then 1 else f x := by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]
theorem nonempty_of_prod_ne_one (h : ∏ x ∈ s, f x ≠ 1) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun H => False.elim <| h <| H.symm ▸ prod_empty) id

@[to_additive]
theorem prod_range_zero (f : ℕ → β) : ∏ k ∈ range 0, f k = 1 := by rw [range_zero, prod_empty]

open List

theorem sum_filter_count_eq_countP [DecidableEq α] (p : α → Prop) [DecidablePred p] (l : List α) :
    ∑ x ∈ l.toFinset with p x, l.count x = l.countP p := by
  simp [Finset.sum, sum_map_count_dedup_filter_eq_countP p l]

open Multiset


@[to_additive]
theorem prod_mem_multiset [DecidableEq α] (m : Multiset α) (f : { x // x ∈ m } → β) (g : α → β)
    (hfg : ∀ x, f x = g x) : ∏ x : { x // x ∈ m }, f x = ∏ x ∈ m.toFinset, g x := by
  refine prod_bij' (fun x _ ↦ x) (fun x hx ↦ ⟨x, Multiset.mem_toFinset.1 hx⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp [hfg]

/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors. -/
@[to_additive "To prove a property of a sum, it suffices to prove that
the property is additive and holds on summands."]
theorem prod_induction {M : Type*} [CommMonoid M] (f : α → M) (p : M → Prop)
    (hom : ∀ a b, p a → p b → p (a * b)) (unit : p 1) (base : ∀ x ∈ s, p <| f x) :
    p <| ∏ x ∈ s, f x :=
  Multiset.prod_induction _ _ hom unit (Multiset.forall_mem_map_iff.mpr base)

/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors. -/
@[to_additive "To prove a property of a sum, it suffices to prove that
the property is additive and holds on summands."]
theorem prod_induction_nonempty {M : Type*} [CommMonoid M] (f : α → M) (p : M → Prop)
    (hom : ∀ a b, p a → p b → p (a * b)) (nonempty : s.Nonempty) (base : ∀ x ∈ s, p <| f x) :
    p <| ∏ x ∈ s, f x :=
  Multiset.prod_induction_nonempty p hom (by simp [nonempty_iff_ne_empty.mp nonempty])
    (Multiset.forall_mem_map_iff.mpr base)

@[to_additive]
theorem prod_pow (s : Finset α) (n : ℕ) (f : α → β) : ∏ x ∈ s, f x ^ n = (∏ x ∈ s, f x) ^ n :=
  Multiset.prod_map_pow

theorem prod_dvd_prod_of_subset {ι M : Type*} [CommMonoid M] (s t : Finset ι) (f : ι → M)
    (h : s ⊆ t) : (∏ i ∈ s, f i) ∣ ∏ i ∈ t, f i :=
  Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| by simpa

end CommMonoid

section Opposite

open MulOpposite

/-- Moving to the opposite additive commutative monoid commutes with summing. -/
@[simp]
theorem op_sum [AddCommMonoid β] {s : Finset α} (f : α → β) :
    op (∑ x ∈ s, f x) = ∑ x ∈ s, op (f x) :=
  map_sum (opAddEquiv : β ≃+ βᵐᵒᵖ) _ _

@[simp]
theorem unop_sum [AddCommMonoid β] {s : Finset α} (f : α → βᵐᵒᵖ) :
    unop (∑ x ∈ s, f x) = ∑ x ∈ s, unop (f x) :=
  map_sum (opAddEquiv : β ≃+ βᵐᵒᵖ).symm _ _

end Opposite

section DivisionCommMonoid

variable [DivisionCommMonoid β]

@[to_additive (attr := simp)]
theorem prod_inv_distrib : (∏ x ∈ s, (f x)⁻¹) = (∏ x ∈ s, f x)⁻¹ :=
  Multiset.prod_map_inv

@[to_additive (attr := simp)]
theorem prod_div_distrib : ∏ x ∈ s, f x / g x = (∏ x ∈ s, f x) / ∏ x ∈ s, g x :=
  Multiset.prod_map_div

@[to_additive]
theorem prod_zpow (f : α → β) (s : Finset α) (n : ℤ) : ∏ a ∈ s, f a ^ n = (∏ a ∈ s, f a) ^ n :=
  Multiset.prod_map_zpow

end DivisionCommMonoid

theorem sum_nat_mod (s : Finset α) (n : ℕ) (f : α → ℕ) :
    (∑ i ∈ s, f i) % n = (∑ i ∈ s, f i % n) % n :=
  (Multiset.sum_nat_mod _ _).trans <| by rw [Finset.sum, Multiset.map_map]; rfl

theorem prod_nat_mod (s : Finset α) (n : ℕ) (f : α → ℕ) :
    (∏ i ∈ s, f i) % n = (∏ i ∈ s, f i % n) % n :=
  (Multiset.prod_nat_mod _ _).trans <| by rw [Finset.prod, Multiset.map_map]; rfl

theorem sum_int_mod (s : Finset α) (n : ℤ) (f : α → ℤ) :
    (∑ i ∈ s, f i) % n = (∑ i ∈ s, f i % n) % n :=
  (Multiset.sum_int_mod _ _).trans <| by rw [Finset.sum, Multiset.map_map]; rfl

theorem prod_int_mod (s : Finset α) (n : ℤ) (f : α → ℤ) :
    (∏ i ∈ s, f i) % n = (∏ i ∈ s, f i % n) % n :=
  (Multiset.prod_int_mod _ _).trans <| by rw [Finset.prod, Multiset.map_map]; rfl

end Finset

namespace Fintype
variable {ι κ α : Type*} [Fintype ι] [Fintype κ]

open Finset

section CommMonoid
variable [CommMonoid α]

/-- `Fintype.prod_bijective` is a variant of `Finset.prod_bij` that accepts `Function.Bijective`.

See `Function.Bijective.prod_comp` for a version without `h`. -/
@[to_additive "`Fintype.sum_bijective` is a variant of `Finset.sum_bij` that accepts
`Function.Bijective`.

See `Function.Bijective.sum_comp` for a version without `h`. "]
lemma prod_bijective (e : ι → κ) (he : e.Bijective) (f : ι → α) (g : κ → α)
    (h : ∀ x, f x = g (e x)) : ∏ x, f x = ∏ x, g x :=
  prod_equiv (.ofBijective e he) (by simp) (by simp [h])

@[to_additive] alias _root_.Function.Bijective.finset_prod := prod_bijective

/-- `Fintype.prod_equiv` is a specialization of `Finset.prod_bij` that
automatically fills in most arguments.

See `Equiv.prod_comp` for a version without `h`.
-/
@[to_additive "`Fintype.sum_equiv` is a specialization of `Finset.sum_bij` that
automatically fills in most arguments.

See `Equiv.sum_comp` for a version without `h`."]
lemma prod_equiv (e : ι ≃ κ) (f : ι → α) (g : κ → α) (h : ∀ x, f x = g (e x)) :
    ∏ x, f x = ∏ x, g x := prod_bijective _ e.bijective _ _ h

@[to_additive]
lemma _root_.Function.Bijective.prod_comp {e : ι → κ} (he : e.Bijective) (g : κ → α) :
    ∏ i, g (e i) = ∏ i, g i := prod_bijective _ he _ _ fun _ ↦ rfl

@[to_additive]
lemma _root_.Equiv.prod_comp (e : ι ≃ κ) (g : κ → α) : ∏ i, g (e i) = ∏ i, g i :=
  prod_equiv e _ _ fun _ ↦ rfl

@[to_additive]
theorem prod_empty {α β : Type*} [CommMonoid β] [IsEmpty α] [Fintype α] (f : α → β) :
    ∏ x : α, f x = 1 :=
  Finset.prod_of_isEmpty _

end CommMonoid
end Fintype

namespace Finset
variable [CommMonoid α]

@[to_additive (attr := simp)]
lemma prod_attach_univ [Fintype ι] (f : {i // i ∈ @univ ι _} → α) :
    ∏ i ∈ univ.attach, f i = ∏ i, f ⟨i, mem_univ _⟩ :=
  Fintype.prod_equiv (Equiv.subtypeUnivEquiv mem_univ) _ _ <| by simp

@[to_additive]
theorem prod_erase_attach [DecidableEq ι] {s : Finset ι} (f : ι → α) (i : ↑s) :
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
    simp_rw [List.sum_cons, disjoint_add_left, List.mem_cons, forall_eq_or_imp]
    simp [and_congr_left_iff, ih]

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

theorem disjoint_finset_sum_left {β : Type*} {i : Finset β} {f : β → Multiset α} {a : Multiset α} :
    Disjoint (i.sum f) a ↔ ∀ b ∈ i, Disjoint (f b) a := by
  convert @disjoint_sum_left _ a (map f i.val)
  simp [and_congr_left_iff]

theorem disjoint_finset_sum_right {β : Type*} {i : Finset β} {f : β → Multiset α}
    {a : Multiset α} : Disjoint a (i.sum f) ↔ ∀ b ∈ i, Disjoint a (f b) := by
  simpa only [disjoint_comm] using disjoint_finset_sum_left

variable [DecidableEq α]

theorem count_sum' {s : Finset β} {a : α} {f : β → Multiset α} :
    count a (∑ x ∈ s, f x) = ∑ x ∈ s, count a (f x) := by
  dsimp only [Finset.sum]
  rw [count_sum]

theorem toFinset_prod_dvd_prod [CommMonoid α] (S : Multiset α) : S.toFinset.prod id ∣ S.prod := by
  rw [Finset.prod_eq_multiset_prod]
  refine Multiset.prod_dvd_prod_of_le ?_
  simp [Multiset.dedup_le S]

end Multiset

@[simp, norm_cast]
theorem Units.coe_prod {M : Type*} [CommMonoid M] (f : α → Mˣ) (s : Finset α) :
    (↑(∏ i ∈ s, f i) : M) = ∏ i ∈ s, (f i : M) :=
  map_prod (Units.coeHom M) _ _


/-! ### `Additive`, `Multiplicative` -/


open Additive Multiplicative

section Monoid

variable [Monoid α]

@[simp]
theorem ofMul_list_prod (s : List α) : ofMul s.prod = (s.map ofMul).sum := by simp [ofMul]; rfl

@[simp]
theorem toMul_list_sum (s : List (Additive α)) : s.sum.toMul = (s.map toMul).prod := by
  simp [toMul, ofMul]; rfl

end Monoid

section AddMonoid

variable [AddMonoid α]

@[simp]
theorem ofAdd_list_prod (s : List α) : ofAdd s.sum = (s.map ofAdd).prod := by simp [ofAdd]; rfl

@[simp]
theorem toAdd_list_sum (s : List (Multiplicative α)) : s.prod.toAdd = (s.map toAdd).sum := by
  simp [toAdd, ofAdd]; rfl

end AddMonoid

section CommMonoid

variable [CommMonoid α]

@[simp]
theorem ofMul_multiset_prod (s : Multiset α) : ofMul s.prod = (s.map ofMul).sum := by
  simp [ofMul]; rfl

@[simp]
theorem toMul_multiset_sum (s : Multiset (Additive α)) : s.sum.toMul = (s.map toMul).prod := by
  simp [toMul, ofMul]; rfl

@[simp]
theorem ofMul_prod (s : Finset ι) (f : ι → α) : ofMul (∏ i ∈ s, f i) = ∑ i ∈ s, ofMul (f i) :=
  rfl

@[simp]
theorem toMul_sum (s : Finset ι) (f : ι → Additive α) :
    (∑ i ∈ s, f i).toMul = ∏ i ∈ s, (f i).toMul :=
  rfl

end CommMonoid

section AddCommMonoid

variable [AddCommMonoid α]

@[simp]
theorem ofAdd_multiset_prod (s : Multiset α) : ofAdd s.sum = (s.map ofAdd).prod := by
  simp [ofAdd]; rfl

@[simp]
theorem toAdd_multiset_sum (s : Multiset (Multiplicative α)) :
    s.prod.toAdd = (s.map toAdd).sum := by
  simp [toAdd, ofAdd]; rfl

@[simp]
theorem ofAdd_sum (s : Finset ι) (f : ι → α) : ofAdd (∑ i ∈ s, f i) = ∏ i ∈ s, ofAdd (f i) :=
  rfl

@[simp]
theorem toAdd_prod (s : Finset ι) (f : ι → Multiplicative α) :
    (∏ i ∈ s, f i).toAdd = ∑ i ∈ s, (f i).toAdd :=
  rfl

end AddCommMonoid
