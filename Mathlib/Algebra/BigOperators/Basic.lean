/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Multiset.Lemmas
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Pi
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Set.Pairwise.Basic

#align_import algebra.big_operators.basic from "leanprover-community/mathlib"@"fa2309577c7009ea243cffdf990cd6c84f0ad497"

/-!
# Big operators

In this file we define products and sums indexed by finite sets (specifically, `Finset`).

## Notation

We introduce the following notation, localized in `BigOperators`.
To enable the notation, use `open BigOperators`.

Let `s` be a `Finset α`, and `f : α → β` a function.

* `∏ x in s, f x` is notation for `Finset.prod s f` (assuming `β` is a `CommMonoid`)
* `∑ x in s, f x` is notation for `Finset.sum s f` (assuming `β` is an `AddCommMonoid`)
* `∏ x, f x` is notation for `Finset.prod Finset.univ f`
  (assuming `α` is a `Fintype` and `β` is a `CommMonoid`)
* `∑ x, f x` is notation for `Finset.sum Finset.univ f`
  (assuming `α` is a `Fintype` and `β` is an `AddCommMonoid`)

## Implementation Notes

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

-/


universe u v w

variable {ι : Type*} {β : Type u} {α : Type v} {γ : Type w}

open Fin

namespace Finset

/-- `∏ x in s, f x` is the product of `f x`
as `x` ranges over the elements of the finite set `s`.
-/
@[to_additive "`∑ x in s, f x` is the sum of `f x` as `x` ranges over the elements
of the finite set `s`."]
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
∑ k in K, (a k + b k) = ∑ k in K, a k + ∑ k in K, b k →
  ∏ k in K, a k * b k = (∏ k in K, a k) * (∏ k in K, b k)
```
(Example taken from page 490 of Knuth's *Concrete Mathematics*.)
-/

-- TODO: Use scoped[NS], when implemented?
namespace BigOperators
open Std.ExtendedBinder

/-- `∑ x, f x` is notation for `Finset.sum Finset.univ f`. It is the sum of `f x`,
where `x` ranges over the finite domain of `f`. -/
scoped syntax (name := bigsum) "∑ " extBinder ", " term:67 : term
scoped macro_rules (kind := bigsum)
  | `(∑ $x:ident, $p) => `(Finset.sum Finset.univ (fun $x:ident ↦ $p))
  | `(∑ $x:ident : $t, $p) => `(Finset.sum Finset.univ (fun $x:ident : $t ↦ $p))

/-- `∏ x, f x` is notation for `Finset.prod Finset.univ f`. It is the product of `f x`,
where `x` ranges over the finite domain of `f`. -/
scoped syntax (name := bigprod) "∏ " extBinder ", " term:67 : term
scoped macro_rules (kind := bigprod)
  | `(∏ $x:ident, $p) => `(Finset.prod Finset.univ (fun $x:ident ↦ $p))
  | `(∏ $x:ident : $t, $p) => `(Finset.prod Finset.univ (fun $x:ident : $t ↦ $p))

/-- `∑ x in s, f x` is notation for `Finset.sum s f`. It is the sum of `f x`,
where `x` ranges over the finite set `s`. -/
scoped syntax (name := bigsumin) "∑ " extBinder " in " term ", " term:67 : term
scoped macro_rules (kind := bigsumin)
  | `(∑ $x:ident in $s, $r) => `(Finset.sum $s (fun $x ↦ $r))
  | `(∑ $x:ident : $t in $s, $p) => `(Finset.sum $s (fun $x:ident : $t ↦ $p))

/-- `∏ x in s, f x` is notation for `Finset.prod s f`. It is the product of `f x`,
where `x` ranges over the finite set `s`. -/
scoped syntax (name := bigprodin) "∏ " extBinder " in " term ", " term:67 : term
scoped macro_rules (kind := bigprodin)
  | `(∏ $x:ident in $s, $r) => `(Finset.prod $s (fun $x ↦ $r))
  | `(∏ $x:ident : $t in $s, $p) => `(Finset.prod $s (fun $x:ident : $t ↦ $p))

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr
open Std.ExtendedBinder

/-- Delaborator for `Finset.prod`. The `pp.piBinderTypes` option controls whether
to show the domain type when the product is over `Finset.univ`. -/
@[scoped delab app.Finset.prod] def delabFinsetProd : Delab := whenPPOption getPPNotation do
  let #[_, _, _, s, f] := (← getExpr).getAppArgs | failure
  guard <| f.isLambda
  let ppDomain ← getPPOption getPPPiBinderTypes
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i => do
    return (i, ← delab)
  if s.isAppOfArity ``Finset.univ 2 then
    let binder ←
      if ppDomain then
        let ty ← withNaryArg 1 delab
        `(extBinder| $(.mk i):ident : $ty)
      else
        `(extBinder| $(.mk i):ident)
    `(∏ $binder, $body)
  else
    let ss ← withNaryArg 3 <| delab
    `(∏ $(.mk i):ident in $ss, $body)

/-- Delaborator for `Finset.prod`. The `pp.piBinderTypes` option controls whether
to show the domain type when the sum is over `Finset.univ`. -/
@[scoped delab app.Finset.sum] def delabFinsetSum : Delab := whenPPOption getPPNotation do
  let #[_, _, _, s, f] := (← getExpr).getAppArgs | failure
  guard <| f.isLambda
  let ppDomain ← getPPOption getPPPiBinderTypes
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i => do
    return (i, ← delab)
  if s.isAppOfArity ``Finset.univ 2 then
    let binder ←
      if ppDomain then
        let ty ← withNaryArg 1 delab
        `(extBinder| $(.mk i):ident : $ty)
      else
        `(extBinder| $(.mk i):ident)
    `(∑ $binder, $body)
  else
    let ss ← withNaryArg 3 <| delab
    `(∑ $(.mk i):ident in $ss, $body)

end BigOperators

open BigOperators

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

@[to_additive]
theorem prod_eq_multiset_prod [CommMonoid β] (s : Finset α) (f : α → β) :
    ∏ x in s, f x = (s.1.map f).prod :=
  rfl

@[to_additive]
theorem prod_eq_fold [CommMonoid β] (s : Finset α) (f : α → β) :
    ∏ x in s, f x = s.fold ((· * ·) : β → β → β) 1 f :=
  rfl

@[simp]
theorem sum_multiset_singleton (s : Finset α) : (s.sum fun x => {x}) = s.val := by
  simp only [sum_eq_multiset_sum, Multiset.sum_map_singleton]

end Finset

@[to_additive (attr := simp)]
theorem map_prod [CommMonoid β] [CommMonoid γ] {G : Type*} [MonoidHomClass G β γ] (g : G)
    (f : α → β) (s : Finset α) : g (∏ x in s, f x) = ∏ x in s, g (f x) := by
  simp only [Finset.prod_eq_multiset_prod, map_multiset_prod, Multiset.map_map]; rfl

section Deprecated

/-- Deprecated: use `_root_.map_prod` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `_root_.map_sum` instead."]
protected theorem MonoidHom.map_prod [CommMonoid β] [CommMonoid γ] (g : β →* γ) (f : α → β)
    (s : Finset α) : g (∏ x in s, f x) = ∏ x in s, g (f x) :=
  map_prod g f s

/-- Deprecated: use `_root_.map_prod` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `_root_.map_sum` instead."]
protected theorem MulEquiv.map_prod [CommMonoid β] [CommMonoid γ] (g : β ≃* γ) (f : α → β)
    (s : Finset α) : g (∏ x in s, f x) = ∏ x in s, g (f x) :=
  map_prod g f s

@[deprecated _root_.map_list_prod]
protected theorem RingHom.map_list_prod [Semiring β] [Semiring γ] (f : β →+* γ) (l : List β) :
    f l.prod = (l.map f).prod :=
  map_list_prod f l

@[deprecated _root_.map_list_sum]
protected theorem RingHom.map_list_sum [NonAssocSemiring β] [NonAssocSemiring γ] (f : β →+* γ)
    (l : List β) : f l.sum = (l.map f).sum :=
  map_list_sum f l

/-- A morphism into the opposite ring acts on the product by acting on the reversed elements. -/
@[deprecated _root_.unop_map_list_prod]
protected theorem RingHom.unop_map_list_prod [Semiring β] [Semiring γ] (f : β →+* γᵐᵒᵖ)
    (l : List β) : MulOpposite.unop (f l.prod) = (l.map (MulOpposite.unop ∘ f)).reverse.prod :=
  unop_map_list_prod f l

@[deprecated _root_.map_multiset_prod]
protected theorem RingHom.map_multiset_prod [CommSemiring β] [CommSemiring γ] (f : β →+* γ)
    (s : Multiset β) : f s.prod = (s.map f).prod :=
  map_multiset_prod f s

@[deprecated _root_.map_multiset_sum]
protected theorem RingHom.map_multiset_sum [NonAssocSemiring β] [NonAssocSemiring γ] (f : β →+* γ)
    (s : Multiset β) : f s.sum = (s.map f).sum :=
  map_multiset_sum f s

@[deprecated _root_.map_prod]
protected theorem RingHom.map_prod [CommSemiring β] [CommSemiring γ] (g : β →+* γ) (f : α → β)
    (s : Finset α) : g (∏ x in s, f x) = ∏ x in s, g (f x) :=
  map_prod g f s

@[deprecated _root_.map_sum]
protected theorem RingHom.map_sum [NonAssocSemiring β] [NonAssocSemiring γ] (g : β →+* γ)
    (f : α → β) (s : Finset α) : g (∑ x in s, f x) = ∑ x in s, g (f x) :=
  map_sum g f s

end Deprecated

@[to_additive]
theorem MonoidHom.coe_finset_prod [MulOneClass β] [CommMonoid γ] (f : α → β →* γ) (s : Finset α) :
    ⇑(∏ x in s, f x) = ∏ x in s, ⇑f x :=
  (MonoidHom.coeFn β γ).map_prod _ _

/-- See also `Finset.prod_apply`, with the same conclusion but with the weaker hypothesis
`f : α → β → γ` -/
@[to_additive (attr := simp)
  "See also `Finset.sum_apply`, with the same conclusion but with the weaker hypothesis
  `f : α → β → γ`"]
theorem MonoidHom.finset_prod_apply [MulOneClass β] [CommMonoid γ] (f : α → β →* γ) (s : Finset α)
    (b : β) : (∏ x in s, f x) b = ∏ x in s, f x b :=
  (MonoidHom.eval b).map_prod _ _

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

namespace Finset

section CommMonoid

variable [CommMonoid β]

@[to_additive (attr := simp)]
theorem prod_empty : ∏ x in ∅, f x = 1 :=
  rfl

@[to_additive]
theorem prod_of_empty [IsEmpty α] (s : Finset α) : ∏ i in s, f i = 1 := by
  rw [eq_empty_of_isEmpty s, prod_empty]

@[to_additive (attr := simp)]
theorem prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a * ∏ x in s, f x :=
  fold_cons h

@[to_additive (attr := simp)]
theorem prod_insert [DecidableEq α] : a ∉ s → ∏ x in insert a s, f x = f a * ∏ x in s, f x :=
  fold_insert

/-- The product of `f` over `insert a s` is the same as
the product over `s`, as long as `a` is in `s` or `f a = 1`. -/
@[to_additive (attr := simp) "The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `a` is in `s` or `f a = 0`."]
theorem prod_insert_of_eq_one_if_not_mem [DecidableEq α] (h : a ∉ s → f a = 1) :
    ∏ x in insert a s, f x = ∏ x in s, f x := by
  by_cases hm : a ∈ s
  · simp_rw [insert_eq_of_mem hm]
  · rw [prod_insert hm, h hm, one_mul]

/-- The product of `f` over `insert a s` is the same as
the product over `s`, as long as `f a = 1`. -/
@[to_additive (attr := simp) "The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `f a = 0`."]
theorem prod_insert_one [DecidableEq α] (h : f a = 1) : ∏ x in insert a s, f x = ∏ x in s, f x :=
  prod_insert_of_eq_one_if_not_mem fun _ => h

@[to_additive (attr := simp)]
theorem prod_singleton (f : α → β) (a : α) : ∏ x in singleton a, f x = f a :=
  Eq.trans fold_singleton <| mul_one _

@[to_additive]
theorem prod_pair [DecidableEq α] {a b : α} (h : a ≠ b) :
    (∏ x in ({a, b} : Finset α), f x) = f a * f b := by
  rw [prod_insert (not_mem_singleton.2 h), prod_singleton]

@[to_additive (attr := simp)]
theorem prod_const_one : (∏ _x in s, (1 : β)) = 1 := by
  simp only [Finset.prod, Multiset.map_const', Multiset.prod_replicate, one_pow]

@[to_additive (attr := simp)]
theorem prod_image [DecidableEq α] {s : Finset γ} {g : γ → α} :
    (∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) → ∏ x in s.image g, f x = ∏ x in s, f (g x) :=
  fold_image

@[to_additive (attr := simp)]
theorem prod_map (s : Finset α) (e : α ↪ γ) (f : γ → β) :
    ∏ x in s.map e, f x = ∏ x in s, f (e x) := by
  rw [Finset.prod, Finset.map_val, Multiset.map_map]; rfl

@[to_additive (attr := congr)]
theorem prod_congr (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g := by
  rw [h]; exact fold_congr

@[to_additive]
theorem prod_disjUnion (h) :
    ∏ x in s₁.disjUnion s₂ h, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x := by
  refine' Eq.trans _ (fold_disjUnion h)
  rw [one_mul]
  rfl

@[to_additive]
theorem prod_disjiUnion (s : Finset ι) (t : ι → Finset α) (h) :
    ∏ x in s.disjiUnion t h, f x = ∏ i in s, ∏ x in t i, f x := by
  refine' Eq.trans _ (fold_disjiUnion h)
  dsimp [Finset.prod, Multiset.prod, Multiset.fold, Finset.disjUnion, Finset.fold]
  congr
  exact prod_const_one.symm

@[to_additive]
theorem prod_union_inter [DecidableEq α] :
    (∏ x in s₁ ∪ s₂, f x) * ∏ x in s₁ ∩ s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x :=
  fold_union_inter

@[to_additive]
theorem prod_union [DecidableEq α] (h : Disjoint s₁ s₂) :
    ∏ x in s₁ ∪ s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x := by
  rw [← prod_union_inter, disjoint_iff_inter_eq_empty.mp h]; exact (mul_one _).symm

@[to_additive]
theorem prod_filter_mul_prod_filter_not
    (s : Finset α) (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] (f : α → β) :
    (∏ x in s.filter p, f x) * ∏ x in s.filter fun x => ¬p x, f x = ∏ x in s, f x := by
  have := Classical.decEq α
  rw [← prod_union (disjoint_filter_filter_neg s s p), filter_union_filter_neg_eq]

section ToList

@[to_additive (attr := simp)]
theorem prod_to_list (s : Finset α) (f : α → β) : (s.toList.map f).prod = s.prod f := by
  rw [Finset.prod, ← Multiset.coe_prod, ← Multiset.coe_map, Finset.coe_toList]

end ToList

@[to_additive]
theorem _root_.Equiv.Perm.prod_comp (σ : Equiv.Perm α) (s : Finset α) (f : α → β)
    (hs : { a | σ a ≠ a } ⊆ s) : (∏ x in s, f (σ x)) = ∏ x in s, f x := by
  convert (prod_map s σ.toEmbedding f).symm
  exact (map_perm hs).symm

@[to_additive]
theorem _root_.Equiv.Perm.prod_comp' (σ : Equiv.Perm α) (s : Finset α) (f : α → α → β)
    (hs : { a | σ a ≠ a } ⊆ s) : (∏ x in s, f (σ x) x) = ∏ x in s, f x (σ.symm x) := by
  convert σ.prod_comp s (fun x => f x (σ.symm x)) hs
  rw [Equiv.symm_apply_apply]

end CommMonoid

end Finset

section

open Finset

variable [Fintype α] [CommMonoid β]

@[to_additive]
theorem IsCompl.prod_mul_prod {s t : Finset α} (h : IsCompl s t) (f : α → β) :
    (∏ i in s, f i) * ∏ i in t, f i = ∏ i, f i :=
  (Finset.prod_disjUnion h.disjoint).symm.trans <| by
    classical rw [Finset.disjUnion_eq_union, ← Finset.sup_eq_union, h.sup_eq_top]; rfl

end

namespace Finset

section CommMonoid

variable [CommMonoid β]

/-- Multiplying the products of a function over `s` and over `sᶜ` gives the whole product.
For a version expressed with subtypes, see `Fintype.prod_subtype_mul_prod_subtype`. -/
@[to_additive "Adding the sums of a function over `s` and over `sᶜ` gives the whole sum.
For a version expressed with subtypes, see `Fintype.sum_subtype_add_sum_subtype`. "]
theorem prod_mul_prod_compl [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
    (∏ i in s, f i) * ∏ i in sᶜ, f i = ∏ i, f i :=
  IsCompl.prod_mul_prod isCompl_compl f

@[to_additive]
theorem prod_compl_mul_prod [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
    (∏ i in sᶜ, f i) * ∏ i in s, f i = ∏ i, f i :=
  (@isCompl_compl _ s _).symm.prod_mul_prod f

@[to_additive]
theorem prod_sdiff [DecidableEq α] (h : s₁ ⊆ s₂) :
    (∏ x in s₂ \ s₁, f x) * ∏ x in s₁, f x = ∏ x in s₂, f x := by
  rw [← prod_union sdiff_disjoint, sdiff_union_of_subset h]

@[to_additive (attr := simp)]
theorem prod_disj_sum (s : Finset α) (t : Finset γ) (f : Sum α γ → β) :
    ∏ x in s.disjSum t, f x = (∏ x in s, f (Sum.inl x)) * ∏ x in t, f (Sum.inr x) := by
  rw [← map_inl_disjUnion_map_inr, prod_disjUnion, prod_map, prod_map]
  rfl

@[to_additive]
theorem prod_sum_elim (s : Finset α) (t : Finset γ) (f : α → β) (g : γ → β) :
    ∏ x in s.disjSum t, Sum.elim f g x = (∏ x in s, f x) * ∏ x in t, g x := by simp

@[to_additive]
theorem prod_biUnion [DecidableEq α] {s : Finset γ} {t : γ → Finset α}
    (hs : Set.PairwiseDisjoint (↑s) t) : ∏ x in s.biUnion t, f x = ∏ x in s, ∏ i in t x, f i := by
  rw [← disjiUnion_eq_biUnion _ _ hs, prod_disjiUnion]

/-- Product over a sigma type equals the product of fiberwise products. For rewriting
in the reverse direction, use `Finset.prod_sigma'`.  -/
@[to_additive "Sum over a sigma type equals the sum of fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_sigma'`"]
theorem prod_sigma {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : Sigma σ → β) :
    ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in t a, f ⟨a, s⟩ := by
  simp_rw [← disjiUnion_map_sigma_mk, prod_disjiUnion, prod_map, Function.Embedding.sigmaMk_apply]

@[to_additive]
theorem prod_sigma' {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : ∀ a, σ a → β) :
    (∏ a in s, ∏ s in t a, f a s) = ∏ x in s.sigma t, f x.1 x.2 :=
  Eq.symm <| prod_sigma s t fun x => f x.1 x.2

/-- Reorder a product.

  The difference with `prod_bij'` is that the bijection is specified as a surjective injection,
  rather than by an inverse function.
-/
@[to_additive "Reorder a sum.

  The difference with `sum_bij'` is that the bijection is specified as a surjective injection,
  rather than by an inverse function."]
theorem prod_bij {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β} (i : ∀ a ∈ s, γ)
    (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) : ∏ x in s, f x = ∏ x in t, g x :=
  congr_arg Multiset.prod (Multiset.map_eq_map_of_bij_of_nodup f g s.2 t.2 i hi h i_inj i_surj)

/-- Reorder a product.

  The difference with `prod_bij` is that the bijection is specified with an inverse, rather than
  as a surjective injection.
-/
@[to_additive "Reorder a sum.

  The difference with `sum_bij` is that the bijection is specified with an inverse, rather than
  as a surjective injection."]
theorem prod_bij' {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β} (i : ∀ a ∈ s, γ)
    (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha)) (j : ∀ a ∈ t, α)
    (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) : ∏ x in s, f x = ∏ x in t, g x := by
  refine' prod_bij i hi h _ _
  · intro a1 a2 h1 h2 eq
    rw [← left_inv a1 h1, ← left_inv a2 h2]
    simp only [eq]
  · intro b hb
    use j b hb
    use hj b hb
    exact (right_inv b hb).symm

/-- Reindexing a product over a finset along an equivalence.
See `Equiv.prod_comp` for the version where `s` and `s'` are `univ`. -/
@[to_additive " Reindexing a sum over a finset along an equivalence.
See `Equiv.sum_comp` for the version where `s` and `s'` are `univ`. "]
theorem Equiv.prod_comp_finset {ι'} [DecidableEq ι] (e : ι ≃ ι') (f : ι' → β) {s' : Finset ι'}
    {s : Finset ι} (h : s = s'.image e.symm) : ∏ i' in s', f i' = ∏ i in s, f (e i) := by
  rw [h]
  refine'
    Finset.prod_bij' (fun i' _hi' => e.symm i') (fun a ha => Finset.mem_image_of_mem _ ha)
      (fun a _ha => by simp_rw [e.apply_symm_apply]) (fun i _hi => e i) (fun a ha => _)
      (fun a _ha => e.apply_symm_apply a) fun a _ha => e.symm_apply_apply a
  rcases Finset.mem_image.mp ha with ⟨i', hi', rfl⟩
  dsimp only
  rwa [e.apply_symm_apply]

@[to_additive]
theorem prod_finset_product (r : Finset (γ × α)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ × α → β} :
    ∏ p in r, f p = ∏ c in s, ∏ a in t c, f (c, a) := by
  refine' Eq.trans _ (prod_sigma s t fun p => f (p.1, p.2))
  exact
    prod_bij' (fun p _hp => ⟨p.1, p.2⟩) (fun p => mem_sigma.mpr ∘ (h p).mp)
      (fun p _ => rfl) (fun p _hp => (p.1, p.2))
      (fun p => (h (p.1, p.2)).mpr ∘ mem_sigma.mp) (fun p _ => rfl) fun p _hp => p.eta

@[to_additive]
theorem prod_finset_product' (r : Finset (γ × α)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ → α → β} :
    ∏ p in r, f p.1 p.2 = ∏ c in s, ∏ a in t c, f c a :=
  prod_finset_product r s t h

@[to_additive]
theorem prod_finset_product_right (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α × γ → β} :
    ∏ p in r, f p = ∏ c in s, ∏ a in t c, f (a, c) := by
  refine' Eq.trans _ (prod_sigma s t fun p => f (p.2, p.1))
  exact
    prod_bij' (fun p _hp => ⟨p.2, p.1⟩) (fun p => mem_sigma.mpr ∘ (h p).mp)
      (fun p _c => rfl) (fun p _hp => (p.2, p.1))
      (fun p => (h (p.2, p.1)).mpr ∘ mem_sigma.mp) (fun p _ => rfl) fun p _hp => p.eta

@[to_additive]
theorem prod_finset_product_right' (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α → γ → β} :
    ∏ p in r, f p.1 p.2 = ∏ c in s, ∏ a in t c, f a c :=
  prod_finset_product_right r s t h

@[to_additive]
theorem prod_fiberwise_of_maps_to [DecidableEq γ] {s : Finset α} {t : Finset γ} {g : α → γ}
    (h : ∀ x ∈ s, g x ∈ t) (f : α → β) :
    (∏ y in t, ∏ x in s.filter fun x => g x = y, f x) = ∏ x in s, f x := by
  rw [← prod_disjiUnion, disjiUnion_filter_eq_of_maps_to h]

@[to_additive]
theorem prod_image' [DecidableEq α] {s : Finset γ} {g : γ → α} (h : γ → β)
    (eq : ∀ c ∈ s, f (g c) = ∏ x in s.filter fun c' => g c' = g c, h x) :
    ∏ x in s.image g, f x = ∏ x in s, h x :=
  calc
    ∏ x in s.image g, f x = ∏ x in s.image g, ∏ x in s.filter fun c' => g c' = x, h x :=
      (prod_congr rfl) fun _x hx =>
        let ⟨c, hcs, hc⟩ := mem_image.1 hx
        hc ▸ eq c hcs
    _ = ∏ x in s, h x := prod_fiberwise_of_maps_to (fun _x => mem_image_of_mem g) _

@[to_additive]
theorem prod_mul_distrib : ∏ x in s, f x * g x = (∏ x in s, f x) * ∏ x in s, g x :=
  Eq.trans (by rw [one_mul]; rfl) fold_op_distrib

@[to_additive]
theorem prod_product {s : Finset γ} {t : Finset α} {f : γ × α → β} :
    ∏ x in s ×ˢ t, f x = ∏ x in s, ∏ y in t, f (x, y) :=
  prod_finset_product (s ×ˢ t) s (fun _a => t) fun _p => mem_product

/-- An uncurried version of `Finset.prod_product`. -/
@[to_additive "An uncurried version of `Finset.sum_product`"]
theorem prod_product' {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    ∏ x in s ×ˢ t, f x.1 x.2 = ∏ x in s, ∏ y in t, f x y :=
  prod_product

@[to_additive]
theorem prod_product_right {s : Finset γ} {t : Finset α} {f : γ × α → β} :
    ∏ x in s ×ˢ t, f x = ∏ y in t, ∏ x in s, f (x, y) :=
  prod_finset_product_right (s ×ˢ t) t (fun _a => s) fun _p => mem_product.trans and_comm

/-- An uncurried version of `Finset.prod_product_right`. -/
@[to_additive "An uncurried version of `Finset.sum_product_right`"]
theorem prod_product_right' {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    ∏ x in s ×ˢ t, f x.1 x.2 = ∏ y in t, ∏ x in s, f x y :=
  prod_product_right

/-- Generalization of `Finset.prod_comm` to the case when the inner `Finset`s depend on the outer
variable. -/
@[to_additive "Generalization of `Finset.sum_comm` to the case when the inner `Finset`s depend on
the outer variable."]
theorem prod_comm' {s : Finset γ} {t : γ → Finset α} {t' : Finset α} {s' : α → Finset γ}
    (h : ∀ x y, x ∈ s ∧ y ∈ t x ↔ x ∈ s' y ∧ y ∈ t') {f : γ → α → β} :
    (∏ x in s, ∏ y in t x, f x y) = ∏ y in t', ∏ x in s' y, f x y := by
  classical
    have : ∀ z : γ × α, (z ∈ s.biUnion fun x => (t x).map <| Function.Embedding.sectr x _) ↔
      z.1 ∈ s ∧ z.2 ∈ t z.1 := by
      rintro ⟨x, y⟩
      simp only [mem_biUnion, mem_map, Function.Embedding.sectr_apply, Prod.mk.injEq,
        exists_eq_right, ← and_assoc]
    exact
      (prod_finset_product' _ _ _ this).symm.trans
        ((prod_finset_product_right' _ _ _) fun ⟨x, y⟩ => (this _).trans ((h x y).trans and_comm))

@[to_additive]
theorem prod_comm {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    (∏ x in s, ∏ y in t, f x y) = ∏ y in t, ∏ x in s, f x y :=
  prod_comm' fun _ _ => Iff.rfl

@[to_additive]
theorem prod_hom_rel [CommMonoid γ] {r : β → γ → Prop} {f : α → β} {g : α → γ} {s : Finset α}
    (h₁ : r 1 1) (h₂ : ∀ a b c, r b c → r (f a * b) (g a * c)) :
    r (∏ x in s, f x) (∏ x in s, g x) := by
  delta Finset.prod
  apply Multiset.prod_hom_rel <;> assumption

@[to_additive]
theorem prod_eq_one {f : α → β} {s : Finset α} (h : ∀ x ∈ s, f x = 1) : ∏ x in s, f x = 1 :=
  calc
    ∏ x in s, f x = ∏ _x in s, 1 := Finset.prod_congr rfl h
    _ = 1 := Finset.prod_const_one

@[to_additive]
theorem prod_subset_one_on_sdiff [DecidableEq α] (h : s₁ ⊆ s₂) (hg : ∀ x ∈ s₂ \ s₁, g x = 1)
    (hfg : ∀ x ∈ s₁, f x = g x) : ∏ i in s₁, f i = ∏ i in s₂, g i := by
  rw [← prod_sdiff h, prod_eq_one hg, one_mul]
  exact prod_congr rfl hfg

@[to_additive]
theorem prod_subset (h : s₁ ⊆ s₂) (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 1) :
    ∏ x in s₁, f x = ∏ x in s₂, f x :=
  haveI := Classical.decEq α
  prod_subset_one_on_sdiff h (by simpa) fun _ _ => rfl

@[to_additive]
theorem prod_filter_of_ne {p : α → Prop} [DecidablePred p] (hp : ∀ x ∈ s, f x ≠ 1 → p x) :
    ∏ x in s.filter p, f x = ∏ x in s, f x :=
  (prod_subset (filter_subset _ _)) fun x => by
    classical
      rw [not_imp_comm, mem_filter]
      exact fun h₁ h₂ => ⟨h₁, by simpa using hp _ h₁ h₂⟩

-- If we use `[DecidableEq β]` here, some rewrites fail because they find a wrong `Decidable`
-- instance first; `{∀ x, Decidable (f x ≠ 1)}` doesn't work with `rw ← prod_filter_ne_one`
@[to_additive]
theorem prod_filter_ne_one [∀ x, Decidable (f x ≠ 1)] :
    ∏ x in s.filter fun x => f x ≠ 1, f x = ∏ x in s, f x :=
  prod_filter_of_ne fun _ _ => id

@[to_additive]
theorem prod_filter (p : α → Prop) [DecidablePred p] (f : α → β) :
    ∏ a in s.filter p, f a = ∏ a in s, if p a then f a else 1 :=
  calc
    ∏ a in s.filter p, f a = ∏ a in s.filter p, if p a then f a else 1 :=
      prod_congr rfl fun a h => by rw [if_pos]; simpa using (mem_filter.1 h).2
    _ = ∏ a in s, if p a then f a else 1 := by
      { refine' prod_subset (filter_subset _ s) fun x hs h => _
        rw [mem_filter, not_and] at h
        exact if_neg (by simpa using h hs) }

@[to_additive]
theorem prod_eq_single_of_mem {s : Finset α} {f : α → β} (a : α) (h : a ∈ s)
    (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) : ∏ x in s, f x = f a := by
  haveI := Classical.decEq α
  calc
    ∏ x in s, f x = ∏ x in {a}, f x := by
      { refine' (prod_subset _ _).symm
        · intro _ H
          rwa [mem_singleton.1 H]
        · simpa only [mem_singleton] }
    _ = f a := prod_singleton _ _

@[to_additive]
theorem prod_eq_single {s : Finset α} {f : α → β} (a : α) (h₀ : ∀ b ∈ s, b ≠ a → f b = 1)
    (h₁ : a ∉ s → f a = 1) : ∏ x in s, f x = f a :=
  haveI := Classical.decEq α
  by_cases (prod_eq_single_of_mem a · h₀) fun this =>
    (prod_congr rfl fun b hb => h₀ b hb <| by rintro rfl; exact this hb).trans <|
      prod_const_one.trans (h₁ this).symm

@[to_additive]
theorem prod_eq_mul_of_mem {s : Finset α} {f : α → β} (a b : α) (ha : a ∈ s) (hb : b ∈ s)
    (hn : a ≠ b) (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) : ∏ x in s, f x = f a * f b := by
  haveI := Classical.decEq α; let s' := ({a, b} : Finset α)
  have hu : s' ⊆ s := by
    refine' insert_subset_iff.mpr _
    apply And.intro ha
    apply singleton_subset_iff.mpr hb
  have hf : ∀ c ∈ s, c ∉ s' → f c = 1 := by
    intro c hc hcs
    apply h₀ c hc
    apply not_or.mp
    intro hab
    apply hcs
    apply mem_insert.mpr
    rw [mem_singleton]
    exact hab
  rw [← prod_subset hu hf]
  exact Finset.prod_pair hn

@[to_additive]
theorem prod_eq_mul {s : Finset α} {f : α → β} (a b : α) (hn : a ≠ b)
    (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) (ha : a ∉ s → f a = 1) (hb : b ∉ s → f b = 1) :
    ∏ x in s, f x = f a * f b := by
  haveI := Classical.decEq α; by_cases h₁ : a ∈ s <;> by_cases h₂ : b ∈ s
  · exact prod_eq_mul_of_mem a b h₁ h₂ hn h₀
  · rw [hb h₂, mul_one]
    apply prod_eq_single_of_mem a h₁
    exact fun c hc hca => h₀ c hc ⟨hca, ne_of_mem_of_not_mem hc h₂⟩
  · rw [ha h₁, one_mul]
    apply prod_eq_single_of_mem b h₂
    exact fun c hc hcb => h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, hcb⟩
  · rw [ha h₁, hb h₂, mul_one]
    exact
      _root_.trans
        (prod_congr rfl fun c hc =>
          h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, ne_of_mem_of_not_mem hc h₂⟩)
        prod_const_one

@[to_additive]
theorem prod_attach {f : α → β} : ∏ x in s.attach, f x = ∏ x in s, f x :=
  haveI := Classical.decEq α
  calc
    ∏ x in s.attach, f x.val = ∏ x in s.attach.image Subtype.val, f x := by
      { rw [prod_image]; exact fun x _ y _ => Subtype.eq }
    _ = _ := by rw [attach_image_val]

-- Porting note: simpNF linter complains that LHS doesn't simplify, but it does
/-- A product over `s.subtype p` equals one over `s.filter p`. -/
@[to_additive (attr := simp, nolint simpNF)
  "A sum over `s.subtype p` equals one over `s.filter p`."]
theorem prod_subtype_eq_prod_filter (f : α → β) {p : α → Prop} [DecidablePred p] :
    ∏ x in s.subtype p, f x = ∏ x in s.filter p, f x := by
  conv_lhs => erw [← prod_map (s.subtype p) (Function.Embedding.subtype _) f]
  exact prod_congr (subtype_map _) fun x _hx => rfl

/-- If all elements of a `Finset` satisfy the predicate `p`, a product
over `s.subtype p` equals that product over `s`. -/
@[to_additive "If all elements of a `Finset` satisfy the predicate `p`, a sum
over `s.subtype p` equals that sum over `s`."]
theorem prod_subtype_of_mem (f : α → β) {p : α → Prop} [DecidablePred p] (h : ∀ x ∈ s, p x) :
    ∏ x in s.subtype p, f x = ∏ x in s, f x := by
  rw [prod_subtype_eq_prod_filter, filter_true_of_mem]
  simpa using h

/-- A product of a function over a `Finset` in a subtype equals a
product in the main type of a function that agrees with the first
function on that `Finset`. -/
@[to_additive "A sum of a function over a `Finset` in a subtype equals a
sum in the main type of a function that agrees with the first
function on that `Finset`."]
theorem prod_subtype_map_embedding {p : α → Prop} {s : Finset { x // p x }} {f : { x // p x } → β}
    {g : α → β} (h : ∀ x : { x // p x }, x ∈ s → g x = f x) :
    (∏ x in s.map (Function.Embedding.subtype _), g x) = ∏ x in s, f x := by
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl h

variable (f s)

@[to_additive]
theorem prod_coe_sort_eq_attach (f : s → β) : ∏ i : s, f i = ∏ i in s.attach, f i :=
  rfl

@[to_additive]
theorem prod_coe_sort : ∏ i : s, f i = ∏ i in s, f i :=
  prod_attach

@[to_additive]
theorem prod_finset_coe (f : α → β) (s : Finset α) : (∏ i : (s : Set α), f i) = ∏ i in s, f i :=
  prod_coe_sort s f

variable {f s}

@[to_additive]
theorem prod_subtype {p : α → Prop} {F : Fintype (Subtype p)} (s : Finset α) (h : ∀ x, x ∈ s ↔ p x)
    (f : α → β) : ∏ a in s, f a = ∏ a : Subtype p, f a := by
  have : (· ∈ s) = p := Set.ext h
  subst p
  rw [← prod_coe_sort]
  congr!

@[to_additive]
theorem prod_set_coe (s : Set α) [Fintype s] : (∏ i : s, f i) = ∏ i in s.toFinset, f i :=
(Finset.prod_subtype s.toFinset (fun _ ↦ Set.mem_toFinset) f).symm

/-- The product of a function `g` defined only on a set `s` is equal to
the product of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 1` off `s`. -/
@[to_additive "The sum of a function `g` defined only on a set `s` is equal to
the sum of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 0` off `s`."]
theorem prod_congr_set {α : Type*} [CommMonoid α] {β : Type*} [Fintype β] (s : Set β)
    [DecidablePred (· ∈ s)] (f : β → α) (g : s → α) (w : ∀ (x : β) (h : x ∈ s), f x = g ⟨x, h⟩)
    (w' : ∀ x : β, x ∉ s → f x = 1) : Finset.univ.prod f = Finset.univ.prod g := by
  rw [← @Finset.prod_subset _ _ s.toFinset Finset.univ f _ (by simp)]
  · rw [Finset.prod_subtype]
    · apply Finset.prod_congr rfl
      exact fun ⟨x, h⟩ _ => w x h
    · simp
  · rintro x _ h
    exact w' x (by simpa using h)

@[to_additive]
theorem prod_apply_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p}
    [DecidablePred fun x => ¬p x] (f : ∀ x : α, p x → γ) (g : ∀ x : α, ¬p x → γ) (h : γ → β) :
    (∏ x in s, h (if hx : p x then f x hx else g x hx)) =
      (∏ x in (s.filter p).attach, h (f x.1 $ by simpa using (mem_filter.mp x.2).2)) *
        ∏ x in (s.filter fun x => ¬p x).attach, h (g x.1 $ by simpa using (mem_filter.mp x.2).2) :=
  calc
    (∏ x in s, h (if hx : p x then f x hx else g x hx)) =
        (∏ x in s.filter p, h (if hx : p x then f x hx else g x hx)) *
          ∏ x in s.filter fun x => ¬p x, h (if hx : p x then f x hx else g x hx) :=
      (prod_filter_mul_prod_filter_not s p _).symm
    _ = (∏ x in (s.filter p).attach, h (if hx : p x.1 then f x.1 hx else g x.1 hx)) *
          ∏ x in (s.filter fun x => ¬p x).attach, h (if hx : p x.1 then f x.1 hx else g x.1 hx) :=
      congr_arg₂ _ prod_attach.symm prod_attach.symm
    _ = (∏ x in (s.filter p).attach, h (f x.1 $ by simpa using (mem_filter.mp x.2).2)) *
          ∏ x in (s.filter fun x ↦ ¬p x).attach, h (g x.1 $ by simpa using (mem_filter.mp x.2).2) :=
      congr_arg₂ _ (prod_congr rfl fun x _hx ↦
        congr_arg h (dif_pos $ by simpa using (mem_filter.mp x.2).2))
        (prod_congr rfl fun x _hx => congr_arg h (dif_neg $ by simpa using (mem_filter.mp x.2).2))

@[to_additive]
theorem prod_apply_ite {s : Finset α} {p : α → Prop} {_hp : DecidablePred p} (f g : α → γ)
    (h : γ → β) :
    (∏ x in s, h (if p x then f x else g x)) =
      (∏ x in s.filter p, h (f x)) * ∏ x in s.filter fun x => ¬p x, h (g x) :=
  _root_.trans (prod_apply_dite _ _ _)
    (congr_arg₂ _ (@prod_attach _ _ _ _ (h ∘ f)) (@prod_attach _ _ _ _ (h ∘ g)))

@[to_additive]
theorem prod_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f : ∀ x : α, p x → β)
    (g : ∀ x : α, ¬p x → β) :
    ∏ x in s, (if hx : p x then f x hx else g x hx) =
      (∏ x in (s.filter p).attach, f x.1 (by simpa using (mem_filter.mp x.2).2)) *
        ∏ x in (s.filter fun x => ¬p x).attach, g x.1 (by simpa using (mem_filter.mp x.2).2) := by
  simp [prod_apply_dite _ _ fun x => x]

@[to_additive]
theorem prod_ite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f g : α → β) :
    ∏ x in s, (if p x then f x else g x) =
      (∏ x in s.filter p, f x) * ∏ x in s.filter fun x => ¬p x, g x := by
  simp [prod_apply_ite _ _ fun x => x]

@[to_additive]
theorem prod_ite_of_false {p : α → Prop} {hp : DecidablePred p} (f g : α → β) (h : ∀ x ∈ s, ¬p x) :
    ∏ x in s, (if p x then f x else g x) = ∏ x in s, g x := by
  rw [prod_ite, filter_false_of_mem, filter_true_of_mem]
  · simp only [prod_empty, one_mul]
  all_goals intros; apply h; assumption

@[to_additive]
theorem prod_ite_of_true {p : α → Prop} {hp : DecidablePred p} (f g : α → β) (h : ∀ x ∈ s, p x) :
    ∏ x in s, (if p x then f x else g x) = ∏ x in s, f x := by
  simp_rw [← ite_not (p _)]
  apply prod_ite_of_false
  simpa

@[to_additive]
theorem prod_apply_ite_of_false {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β)
    (h : ∀ x ∈ s, ¬p x) : (∏ x in s, k (if p x then f x else g x)) = ∏ x in s, k (g x) := by
  simp_rw [apply_ite k]
  exact prod_ite_of_false _ _ h

@[to_additive]
theorem prod_apply_ite_of_true {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β)
    (h : ∀ x ∈ s, p x) : (∏ x in s, k (if p x then f x else g x)) = ∏ x in s, k (f x) := by
  simp_rw [apply_ite k]
  exact prod_ite_of_true _ _ h

@[to_additive]
theorem prod_extend_by_one [DecidableEq α] (s : Finset α) (f : α → β) :
    ∏ i in s, (if i ∈ s then f i else 1) = ∏ i in s, f i :=
  (prod_congr rfl) fun _i hi => if_pos hi

@[to_additive (attr := simp)]
theorem prod_ite_mem [DecidableEq α] (s t : Finset α) (f : α → β) :
    ∏ i in s, (if i ∈ t then f i else 1) = ∏ i in s ∩ t, f i := by
  rw [← Finset.prod_filter, Finset.filter_mem_eq_inter]

@[to_additive (attr := simp)]
theorem prod_dite_eq [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, a = x → β) :
    ∏ x in s, (if h : a = x then b x h else 1) = ite (a ∈ s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intros _ _ h
      rw [dif_neg]
      exact h.symm
    · simp [h]
  · rw [Finset.prod_eq_one]
    intros
    rw [dif_neg]
    rintro rfl
    contradiction

@[to_additive (attr := simp)]
theorem prod_dite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, x = a → β) :
    ∏ x in s, (if h : x = a then b x h else 1) = ite (a ∈ s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intros _ _ h
      rw [dif_neg]
      exact h
    · simp [h]
  · rw [Finset.prod_eq_one]
    intros
    rw [dif_neg]
    rintro rfl
    contradiction

@[to_additive (attr := simp)]
theorem prod_ite_eq [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
    (∏ x in s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq s a fun x _ => b x

/-- A product taken over a conditional whose condition is an equality test on the index and whose
alternative is `1` has value either the term at that index or `1`.

The difference with `Finset.prod_ite_eq` is that the arguments to `Eq` are swapped. -/
@[to_additive (attr := simp) "A sum taken over a conditional whose condition is an equality
test on the index and whose alternative is `0` has value either the term at that index or `0`.

The difference with `Finset.sum_ite_eq` is that the arguments to `eq` are swapped."]
theorem prod_ite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
    (∏ x in s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x

@[to_additive]
theorem prod_ite_index (p : Prop) [Decidable p] (s t : Finset α) (f : α → β) :
    ∏ x in if p then s else t, f x = if p then ∏ x in s, f x else ∏ x in t, f x :=
  apply_ite (fun s => ∏ x in s, f x) _ _ _

@[to_additive (attr := simp)]
theorem prod_ite_irrel (p : Prop) [Decidable p] (s : Finset α) (f g : α → β) :
    ∏ x in s, (if p then f x else g x) = if p then ∏ x in s, f x else ∏ x in s, g x := by
  split_ifs with h <;> rfl

@[to_additive (attr := simp)]
theorem prod_dite_irrel (p : Prop) [Decidable p] (s : Finset α) (f : p → α → β) (g : ¬p → α → β) :
    ∏ x in s, (if h : p then f h x else g h x) =
      if h : p then ∏ x in s, f h x else ∏ x in s, g h x := by
  split_ifs with h <;> rfl

@[to_additive (attr := simp)]
theorem prod_pi_mulSingle' [DecidableEq α] (a : α) (x : β) (s : Finset α) :
    ∏ a' in s, Pi.mulSingle a x a' = if a ∈ s then x else 1 :=
  prod_dite_eq' _ _ _

@[to_additive (attr := simp)]
theorem prod_pi_mulSingle {β : α → Type*} [DecidableEq α] [∀ a, CommMonoid (β a)] (a : α)
    (f : ∀ a, β a) (s : Finset α) :
    (∏ a' in s, Pi.mulSingle a' (f a') a) = if a ∈ s then f a else 1 :=
  prod_dite_eq _ _ _

@[to_additive]
theorem prod_bij_ne_one {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β}
    (i : ∀ a ∈ s, f a ≠ 1 → γ) (hi : ∀ a h₁ h₂, i a h₁ h₂ ∈ t)
    (i_inj : ∀ a₁ a₂ h₁₁ h₁₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, g b ≠ 1 → ∃ a h₁ h₂, b = i a h₁ h₂) (h : ∀ a h₁ h₂, f a = g (i a h₁ h₂)) :
    ∏ x in s, f x = ∏ x in t, g x := by
  classical
  calc
    ∏ x in s, f x = ∏ x in s.filter fun x => f x ≠ 1, f x := prod_filter_ne_one.symm
    _ = ∏ x in t.filter fun x => g x ≠ 1, g x :=
      prod_bij (fun a ha => i a (mem_filter.mp ha).1 $ by simpa using (mem_filter.mp ha).2)
        ?_ ?_ ?_ ?_
    _ = ∏ x in t, g x := prod_filter_ne_one
  · intros a ha
    refine' (mem_filter.mp ha).elim _
    intros h₁ h₂
    refine (mem_filter.mpr ⟨hi a h₁ _, ?_⟩)
    specialize h a h₁ fun H ↦ by rw [H] at h₂; simp at h₂
    rwa [← h]
  · refine' (fun a ha => (mem_filter.mp ha).elim fun h₁ h₂ ↦ _)
    exact h a h₁ fun H ↦ by rw [H] at h₂; simp at h₂
  · intros a₁ a₂ ha₁ ha₂
    refine' (mem_filter.mp ha₁).elim fun _ha₁₁ _ha₁₂ ↦ _
    refine' (mem_filter.mp ha₂).elim fun _ha₂₁ _ha₂₂ ↦ _
    apply i_inj
  · intros b hb
    refine' (mem_filter.mp hb).elim fun h₁ h₂ ↦ _
    obtain ⟨a, ha₁, ha₂, eq⟩ := i_surj b h₁ fun H ↦ by rw [H] at h₂; simp at h₂
    exact ⟨a, mem_filter.mpr ⟨ha₁, ha₂⟩, eq⟩

@[to_additive]
theorem prod_dite_of_false {p : α → Prop} {hp : DecidablePred p} (h : ∀ x ∈ s, ¬p x)
    (f : ∀ x : α, p x → β) (g : ∀ x : α, ¬p x → β) :
    ∏ x in s, (if hx : p x then f x hx else g x hx) = ∏ x : s, g x.val (h x.val x.property) :=
  prod_bij (fun x hx => ⟨x, hx⟩) (fun x hx => by simp)
    (fun a ha => by
      dsimp
      rw [dif_neg])
    (fun a₁ a₂ h₁ h₂ hh => congr_arg Subtype.val hh) fun b _hb => ⟨b.1, b.2, by simp⟩

@[to_additive]
theorem prod_dite_of_true {p : α → Prop} {hp : DecidablePred p} (h : ∀ x ∈ s, p x)
    (f : ∀ x : α, p x → β) (g : ∀ x : α, ¬p x → β) :
    ∏ x in s, (if hx : p x then f x hx else g x hx) = ∏ x : s, f x.val (h x.val x.property) :=
  prod_bij (fun x hx => ⟨x, hx⟩) (fun x hx => by simp)
    (fun a ha => by
      dsimp
      rw [dif_pos])
    (fun a₁ a₂ h₁ h₂ hh => congr_arg Subtype.val hh) fun b _hb => ⟨b.1, b.2, by simp⟩

@[to_additive]
theorem nonempty_of_prod_ne_one (h : ∏ x in s, f x ≠ 1) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun H => False.elim <| h <| H.symm ▸ prod_empty) id

@[to_additive]
theorem exists_ne_one_of_prod_ne_one (h : ∏ x in s, f x ≠ 1) : ∃ a ∈ s, f a ≠ 1 := by
  classical
    rw [← prod_filter_ne_one] at h
    rcases nonempty_of_prod_ne_one h with ⟨x, hx⟩
    exact ⟨x, (mem_filter.1 hx).1, by simpa using (mem_filter.1 hx).2⟩

@[to_additive]
theorem prod_range_succ_comm (f : ℕ → β) (n : ℕ) :
    (∏ x in range (n + 1), f x) = f n * ∏ x in range n, f x := by
  rw [range_succ, prod_insert not_mem_range_self]

@[to_additive]
theorem prod_range_succ (f : ℕ → β) (n : ℕ) :
    (∏ x in range (n + 1), f x) = (∏ x in range n, f x) * f n := by
  simp only [mul_comm, prod_range_succ_comm]

@[to_additive]
theorem prod_range_succ' (f : ℕ → β) :
    ∀ n : ℕ, (∏ k in range (n + 1), f k) = (∏ k in range n, f (k + 1)) * f 0
  | 0 => prod_range_succ _ _
  | n + 1 => by rw [prod_range_succ _ n, mul_right_comm, ← prod_range_succ' _ n, prod_range_succ]

@[to_additive]
theorem eventually_constant_prod {u : ℕ → β} {N : ℕ} (hu : ∀ n ≥ N, u n = 1) {n : ℕ} (hn : N ≤ n) :
    (∏ k in range n, u k) = ∏ k in range N, u k := by
  obtain ⟨m, rfl : n = N + m⟩ := le_iff_exists_add.mp hn
  clear hn
  induction' m with m hm
  · simp
  erw [prod_range_succ, hm]
  simp [hu, @zero_le' ℕ]

@[to_additive]
theorem prod_range_add (f : ℕ → β) (n m : ℕ) :
    (∏ x in range (n + m), f x) = (∏ x in range n, f x) * ∏ x in range m, f (n + x) := by
  induction' m with m hm
  · simp
  · erw [Nat.add_succ, prod_range_succ, prod_range_succ, hm, mul_assoc]

@[to_additive]
theorem prod_range_add_div_prod_range {α : Type*} [CommGroup α] (f : ℕ → α) (n m : ℕ) :
    (∏ k in range (n + m), f k) / ∏ k in range n, f k = ∏ k in Finset.range m, f (n + k) :=
  div_eq_of_eq_mul' (prod_range_add f n m)

@[to_additive]
theorem prod_range_zero (f : ℕ → β) : ∏ k in range 0, f k = 1 := by rw [range_zero, prod_empty]

@[to_additive sum_range_one]
theorem prod_range_one (f : ℕ → β) : ∏ k in range 1, f k = f 0 := by
  rw [range_one, prod_singleton]

open List

@[to_additive]
theorem prod_list_map_count [DecidableEq α] (l : List α) {M : Type*} [CommMonoid M] (f : α → M) :
    (l.map f).prod = ∏ m in l.toFinset, f m ^ l.count m := by
  induction' l with a s IH; · simp only [map_nil, prod_nil, count_nil, pow_zero, prod_const_one]
  simp only [List.map, List.prod_cons, toFinset_cons, IH]
  by_cases has : a ∈ s.toFinset
  · rw [insert_eq_of_mem has, ← insert_erase has, prod_insert (not_mem_erase _ _),
      prod_insert (not_mem_erase _ _), ← mul_assoc, count_cons_self, pow_succ]
    congr 1
    refine' prod_congr rfl fun x hx => _
    rw [count_cons_of_ne (ne_of_mem_erase hx)]
  rw [prod_insert has, count_cons_self, count_eq_zero_of_not_mem (mt mem_toFinset.2 has), pow_one]
  congr 1
  refine' prod_congr rfl fun x hx => _
  rw [count_cons_of_ne]
  rintro rfl
  exact has hx

@[to_additive]
theorem prod_list_count [DecidableEq α] [CommMonoid α] (s : List α) :
    s.prod = ∏ m in s.toFinset, m ^ s.count m := by simpa using prod_list_map_count s id

@[to_additive]
theorem prod_list_count_of_subset [DecidableEq α] [CommMonoid α] (m : List α) (s : Finset α)
    (hs : m.toFinset ⊆ s) : m.prod = ∏ i in s, i ^ m.count i := by
  rw [prod_list_count]
  refine' prod_subset hs fun x _ hx => _
  rw [mem_toFinset] at hx
  rw [count_eq_zero_of_not_mem hx, pow_zero]

theorem sum_filter_count_eq_countP [DecidableEq α] (p : α → Prop) [DecidablePred p] (l : List α) :
    ∑ x in l.toFinset.filter p, l.count x = l.countP p := by
  simp [Finset.sum, sum_map_count_dedup_filter_eq_countP p l]

open Multiset

@[to_additive]
theorem prod_multiset_map_count [DecidableEq α] (s : Multiset α) {M : Type*} [CommMonoid M]
    (f : α → M) : (s.map f).prod = ∏ m in s.toFinset, f m ^ s.count m := by
  refine' Quot.induction_on s fun l => _
  simp [prod_list_map_count l f]

@[to_additive]
theorem prod_multiset_count [DecidableEq α] [CommMonoid α] (s : Multiset α) :
    s.prod = ∏ m in s.toFinset, m ^ s.count m := by
  convert prod_multiset_map_count s id
  rw [Multiset.map_id]

@[to_additive]
theorem prod_multiset_count_of_subset [DecidableEq α] [CommMonoid α] (m : Multiset α) (s : Finset α)
    (hs : m.toFinset ⊆ s) : m.prod = ∏ i in s, i ^ m.count i := by
  revert hs
  refine' Quot.induction_on m fun l => _
  simp only [quot_mk_to_coe'', coe_prod, coe_count]
  apply prod_list_count_of_subset l s

@[to_additive]
theorem prod_mem_multiset [DecidableEq α] (m : Multiset α) (f : { x // x ∈ m } → β) (g : α → β)
    (hfg : ∀ x, f x = g x) : ∏ x : { x // x ∈ m }, f x = ∏ x in m.toFinset, g x :=
  prod_bij (fun x _ => x.1) (fun x _ => Multiset.mem_toFinset.mpr x.2) (fun _ _ => hfg _)
    (fun _ _ _ _ h => by
      ext
      assumption)
    fun y hy => ⟨⟨y, Multiset.mem_toFinset.mp hy⟩, Finset.mem_univ _, rfl⟩

/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors. -/
@[to_additive "To prove a property of a sum, it suffices to prove that
the property is additive and holds on summands."]
theorem prod_induction {M : Type*} [CommMonoid M] (f : α → M) (p : M → Prop)
    (hom : ∀ a b, p a → p b → p (a * b)) (unit : p 1) (base : ∀ x ∈ s, p <| f x) :
    p <| ∏ x in s, f x :=
  Multiset.prod_induction _ _ hom unit (Multiset.forall_mem_map_iff.mpr base)

/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors. -/
@[to_additive "To prove a property of a sum, it suffices to prove that
the property is additive and holds on summands."]
theorem prod_induction_nonempty {M : Type*} [CommMonoid M] (f : α → M) (p : M → Prop)
    (hom : ∀ a b, p a → p b → p (a * b)) (nonempty : s.Nonempty) (base : ∀ x ∈ s, p <| f x) :
    p <| ∏ x in s, f x :=
  Multiset.prod_induction_nonempty p hom (by simp [nonempty_iff_ne_empty.mp nonempty])
    (Multiset.forall_mem_map_iff.mpr base)

/-- For any product along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can verify
that it's equal to a different function just by checking ratios of adjacent terms.

This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
@[to_additive "For any sum along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can
verify that it's equal to a different function just by checking differences of adjacent terms.

This is a discrete analogue of the fundamental theorem of calculus."]
theorem prod_range_induction (f s : ℕ → β) (base : s 0 = 1)
    (step : ∀ n, s (n + 1) = s n * f n) (n : ℕ) :
    ∏ k in Finset.range n, f k = s n := by
  induction' n with k hk
  · rw [Finset.prod_range_zero, base]
  · simp only [hk, Finset.prod_range_succ, step, mul_comm]

/-- A telescoping product along `{0, ..., n - 1}` of a commutative group valued function reduces to
the ratio of the last and first factors. -/
@[to_additive "A telescoping sum along `{0, ..., n - 1}` of an additive commutative group valued
function reduces to the difference of the last and first terms."]
theorem prod_range_div {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    (∏ i in range n, f (i + 1) / f i) = f n / f 0 := by apply prod_range_induction <;> simp

@[to_additive]
theorem prod_range_div' {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    (∏ i in range n, f i / f (i + 1)) = f 0 / f n := by apply prod_range_induction <;> simp

@[to_additive]
theorem eq_prod_range_div {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    f n = f 0 * ∏ i in range n, f (i + 1) / f i := by rw [prod_range_div, mul_div_cancel'_right]

@[to_additive]
theorem eq_prod_range_div' {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    f n = ∏ i in range (n + 1), if i = 0 then f 0 else f i / f (i - 1) := by
  conv_lhs => rw [Finset.eq_prod_range_div f]
  simp [Finset.prod_range_succ', mul_comm]

/-- A telescoping sum along `{0, ..., n-1}` of an `ℕ`-valued function
reduces to the difference of the last and first terms
when the function we are summing is monotone.
-/
theorem sum_range_tsub [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] {f : ℕ → α} (h : Monotone f) (n : ℕ) :
    ∑ i in range n, (f (i + 1) - f i) = f n - f 0 := by
  apply sum_range_induction
  case base => apply tsub_self
  case step =>
    intro n
    have h₁ : f n ≤ f (n + 1) := h (Nat.le_succ _)
    have h₂ : f 0 ≤ f n := h (Nat.zero_le _)
    rw [tsub_add_eq_add_tsub h₂, add_tsub_cancel_of_le h₁]

@[to_additive (attr := simp)]
theorem prod_const (b : β) : ∏ _x in s, b = b ^ s.card :=
  (congr_arg _ <| s.val.map_const b).trans <| Multiset.prod_replicate s.card b

@[to_additive sum_eq_card_nsmul]
theorem prod_eq_pow_card {b : β} (hf : ∀ a ∈ s, f a = b) : ∏ a in s, f a = b ^ s.card :=
  (prod_congr rfl hf).trans <| prod_const _

@[to_additive]
theorem pow_eq_prod_const (b : β) : ∀ n, b ^ n = ∏ _k in range n, b := by simp

@[to_additive]
theorem prod_pow (s : Finset α) (n : ℕ) (f : α → β) : ∏ x in s, f x ^ n = (∏ x in s, f x) ^ n :=
  Multiset.prod_map_pow

/-- A product over `Finset.powersetCard` which only depends on the size of the sets is constant. -/
@[to_additive
"A sum over `Finset.powersetCard` which only depends on the size of the sets is constant."]
lemma prod_powersetCard (n : ℕ) (s : Finset α) (f : ℕ → β) :
    ∏ t in powersetCard n s, f t.card = f n ^ s.card.choose n := by
  rw [prod_eq_pow_card, card_powersetCard]; rintro a ha; rw [(mem_powersetCard.1 ha).2]

@[to_additive]
theorem prod_flip {n : ℕ} (f : ℕ → β) :
    (∏ r in range (n + 1), f (n - r)) = ∏ k in range (n + 1), f k := by
  induction' n with n ih
  · rw [prod_range_one, prod_range_one]
  · rw [prod_range_succ', prod_range_succ _ (Nat.succ n)]
    simp [← ih]

@[to_additive]
theorem prod_involution {s : Finset α} {f : α → β} :
    ∀ (g : ∀ a ∈ s, α) (_ : ∀ a ha, f a * f (g a ha) = 1) (_ : ∀ a ha, f a ≠ 1 → g a ha ≠ a)
      (g_mem : ∀ a ha, g a ha ∈ s) (_ : ∀ a ha, g (g a ha) (g_mem a ha) = a),
      ∏ x in s, f x = 1 := by
  haveI := Classical.decEq α; haveI := Classical.decEq β
  exact
    Finset.strongInductionOn s fun s ih g h g_ne g_mem g_inv =>
      s.eq_empty_or_nonempty.elim (fun hs => hs.symm ▸ rfl) fun ⟨x, hx⟩ =>
        have hmem : ∀ y ∈ (s.erase x).erase (g x hx), y ∈ s := fun y hy =>
          mem_of_mem_erase (mem_of_mem_erase hy)
        have g_inj : ∀ {x hx y hy}, g x hx = g y hy → x = y := fun {x hx y hy} h => by
          rw [← g_inv x hx, ← g_inv y hy]; simp [h]
        have ih' : (∏ y in erase (erase s x) (g x hx), f y) = (1 : β) :=
          ih ((s.erase x).erase (g x hx))
            ⟨Subset.trans (erase_subset _ _) (erase_subset _ _), fun h =>
              not_mem_erase (g x hx) (s.erase x) (h (g_mem x hx))⟩
            (fun y hy => g y (hmem y hy)) (fun y hy => h y (hmem y hy))
            (fun y hy => g_ne y (hmem y hy))
            (fun y hy =>
              mem_erase.2
                ⟨fun h : g y _ = g x hx => by simp [g_inj h] at hy,
                  mem_erase.2
                    ⟨fun h : g y _ = x => by
                      have : y = g x hx := g_inv y (hmem y hy) ▸ by simp [h]
                      simp [this] at hy, g_mem y (hmem y hy)⟩⟩)
            fun y hy => g_inv y (hmem y hy)
        if hx1 : f x = 1 then
          ih' ▸
            Eq.symm
              (prod_subset hmem fun y hy hy₁ =>
                have : y = x ∨ y = g x hx := by
                  simpa [hy, -not_and, mem_erase, not_and_or, or_comm] using hy₁
                this.elim (fun hy => hy.symm ▸ hx1) fun hy =>
                  h x hx ▸ hy ▸ hx1.symm ▸ (one_mul _).symm)
        else by
          rw [← insert_erase hx, prod_insert (not_mem_erase _ _), ←
            insert_erase (mem_erase.2 ⟨g_ne x hx hx1, g_mem x hx⟩),
            prod_insert (not_mem_erase _ _), ih', mul_one, h x hx]

/-- The product of the composition of functions `f` and `g`, is the product over `b ∈ s.image g` of
`f b` to the power of the cardinality of the fibre of `b`. See also `Finset.prod_image`. -/
@[to_additive "The sum of the composition of functions `f` and `g`, is the sum over `b ∈ s.image g`
of `f b` times of the cardinality of the fibre of `b`. See also `Finset.sum_image`."]
theorem prod_comp [DecidableEq γ] (f : γ → β) (g : α → γ) :
    (∏ a in s, f (g a)) = ∏ b in s.image g, f b ^ (s.filter fun a => g a = b).card :=
  calc
    (∏ a in s, f (g a)) =
        ∏ x in (s.image g).sigma fun b : γ => s.filter fun a => g a = b, f (g x.2) :=
      prod_bij (fun a _ha => ⟨g a, a⟩) (by simp; tauto) (fun _ _ => rfl) (by simp)
        (by -- `(by finish)` closes this
          rintro ⟨b_fst, b_snd⟩ H
          simp only [mem_image, exists_prop, mem_filter, mem_sigma, decide_eq_true_eq] at H
          tauto)
    _ = ∏ b in s.image g, ∏ a in s.filter fun a => g a = b, f (g a) := prod_sigma _ _ _
    _ = ∏ b in s.image g, ∏ _a in s.filter fun a => g a = b, f b :=
      prod_congr rfl fun b _hb => prod_congr rfl (by simp (config := { contextual := true }))
    _ = ∏ b in s.image g, f b ^ (s.filter fun a => g a = b).card :=
      prod_congr rfl fun _ _ => prod_const _

@[to_additive]
theorem prod_piecewise [DecidableEq α] (s t : Finset α) (f g : α → β) :
    (∏ x in s, (t.piecewise f g) x) = (∏ x in s ∩ t, f x) * ∏ x in s \ t, g x := by
  erw [prod_ite, filter_mem_eq_inter, ← sdiff_eq_filter]

@[to_additive]
theorem prod_inter_mul_prod_diff [DecidableEq α] (s t : Finset α) (f : α → β) :
    (∏ x in s ∩ t, f x) * ∏ x in s \ t, f x = ∏ x in s, f x := by
  convert (s.prod_piecewise t f f).symm
  simp [Finset.piecewise]

@[to_additive]
theorem prod_eq_mul_prod_diff_singleton [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s)
    (f : α → β) : ∏ x in s, f x = f i * ∏ x in s \ {i}, f x := by
  convert (s.prod_inter_mul_prod_diff {i} f).symm
  simp [h]

@[to_additive]
theorem prod_eq_prod_diff_singleton_mul [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s)
    (f : α → β) : ∏ x in s, f x = (∏ x in s \ {i}, f x) * f i := by
  rw [prod_eq_mul_prod_diff_singleton h, mul_comm]

@[to_additive]
theorem _root_.Fintype.prod_eq_mul_prod_compl [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    ∏ i, f i = f a * ∏ i in {a}ᶜ, f i :=
  prod_eq_mul_prod_diff_singleton (mem_univ a) f

@[to_additive]
theorem _root_.Fintype.prod_eq_prod_compl_mul [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    ∏ i, f i = (∏ i in {a}ᶜ, f i) * f a :=
  prod_eq_prod_diff_singleton_mul (mem_univ a) f

theorem dvd_prod_of_mem (f : α → β) {a : α} {s : Finset α} (ha : a ∈ s) : f a ∣ ∏ i in s, f i := by
  classical
    rw [Finset.prod_eq_mul_prod_diff_singleton ha]
    exact dvd_mul_right _ _

/-- A product can be partitioned into a product of products, each equivalent under a setoid. -/
@[to_additive "A sum can be partitioned into a sum of sums, each equivalent under a setoid."]
theorem prod_partition (R : Setoid α) [DecidableRel R.r] :
    ∏ x in s, f x = ∏ xbar in s.image Quotient.mk'', ∏ y in s.filter (⟦·⟧ = xbar), f y := by
  refine' (Finset.prod_image' f fun x _hx => _).symm
  rfl

/-- If we can partition a product into subsets that cancel out, then the whole product cancels. -/
@[to_additive "If we can partition a sum into subsets that cancel out, then the whole sum cancels."]
theorem prod_cancels_of_partition_cancels (R : Setoid α) [DecidableRel R.r]
    (h : ∀ x ∈ s, ∏ a in s.filter fun y => y ≈ x, f a = 1) : ∏ x in s, f x = 1 := by
  rw [prod_partition R, ← Finset.prod_eq_one]
  intro xbar xbar_in_s
  obtain ⟨x, x_in_s, rfl⟩ := mem_image.mp xbar_in_s
  simp only [← Quotient.eq] at h
  exact h x x_in_s

@[to_additive]
theorem prod_update_of_not_mem [DecidableEq α] {s : Finset α} {i : α} (h : i ∉ s) (f : α → β)
    (b : β) : ∏ x in s, Function.update f i b x = ∏ x in s, f x := by
  apply prod_congr rfl
  intros j hj
  have : j ≠ i := by
    rintro rfl
    exact h hj
  simp [this]

@[to_additive]
theorem prod_update_of_mem [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s) (f : α → β) (b : β) :
    ∏ x in s, Function.update f i b x = b * ∏ x in s \ singleton i, f x := by
  rw [update_eq_piecewise, prod_piecewise]
  simp [h]

/-- If a product of a `Finset` of size at most 1 has a given value, so
do the terms in that product. -/
@[to_additive eq_of_card_le_one_of_sum_eq "If a sum of a `Finset` of size at most 1 has a given
value, so do the terms in that sum."]
theorem eq_of_card_le_one_of_prod_eq {s : Finset α} (hc : s.card ≤ 1) {f : α → β} {b : β}
    (h : ∏ x in s, f x = b) : ∀ x ∈ s, f x = b := by
  intro x hx
  by_cases hc0 : s.card = 0
  · exact False.elim (card_ne_zero_of_mem hx hc0)
  · have h1 : s.card = 1 := le_antisymm hc (Nat.one_le_of_lt (Nat.pos_of_ne_zero hc0))
    rw [card_eq_one] at h1
    cases' h1 with x2 hx2
    rw [hx2, mem_singleton] at hx
    simp_rw [hx2] at h
    rw [hx]
    rw [prod_singleton] at h
    exact h

/-- Taking a product over `s : Finset α` is the same as multiplying the value on a single element
`f a` by the product of `s.erase a`.

See `Multiset.prod_map_erase` for the `Multiset` version. -/
@[to_additive "Taking a sum over `s : Finset α` is the same as adding the value on a single element
`f a` to the sum over `s.erase a`.

See `Multiset.sum_map_erase` for the `Multiset` version."]
theorem mul_prod_erase [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
    (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x := by
  rw [← prod_insert (not_mem_erase a s), insert_erase h]

/-- A variant of `Finset.mul_prod_erase` with the multiplication swapped. -/
@[to_additive "A variant of `Finset.add_sum_erase` with the addition swapped."]
theorem prod_erase_mul [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
    (∏ x in s.erase a, f x) * f a = ∏ x in s, f x := by rw [mul_comm, mul_prod_erase s f h]

/-- If a function applied at a point is 1, a product is unchanged by
removing that point, if present, from a `Finset`. -/
@[to_additive "If a function applied at a point is 0, a sum is unchanged by
removing that point, if present, from a `Finset`."]
theorem prod_erase [DecidableEq α] (s : Finset α) {f : α → β} {a : α} (h : f a = 1) :
    ∏ x in s.erase a, f x = ∏ x in s, f x := by
  rw [← sdiff_singleton_eq_erase]
  refine' prod_subset (sdiff_subset _ _) fun x hx hnx => _
  rw [sdiff_singleton_eq_erase] at hnx
  rwa [eq_of_mem_of_not_mem_erase hx hnx]

/-- See also `Finset.prod_boole`. -/
@[to_additive "See also `Finset.sum_boole`."]
theorem prod_ite_one {f : α → Prop} [DecidablePred f] (hf : (s : Set α).PairwiseDisjoint f)
    (a : β) : (∏ i in s, ite (f i) a 1) = ite (∃ i ∈ s, f i) a 1 := by
  split_ifs with h
  · obtain ⟨i, hi, hfi⟩ := h
    rw [prod_eq_single_of_mem _ hi, if_pos hfi]
    exact fun j hj h => if_neg fun hfj => (hf hj hi h).le_bot ⟨hfj, hfi⟩
  · push_neg at h
    rw [prod_eq_one]
    exact fun i hi => if_neg (h i hi)

@[to_additive]
theorem prod_erase_lt_of_one_lt {γ : Type*} [DecidableEq α] [OrderedCommMonoid γ]
    [CovariantClass γ γ (· * ·) (· < ·)] {s : Finset α} {d : α} (hd : d ∈ s) {f : α → γ}
    (hdf : 1 < f d) : ∏ m : α in s.erase d, f m < ∏ m : α in s, f m := by
  conv in ∏ m in s, f m => rw [← Finset.insert_erase hd]
  rw [Finset.prod_insert (Finset.not_mem_erase d s)]
  exact lt_mul_of_one_lt_left' _ hdf

/-- If a product is 1 and the function is 1 except possibly at one
point, it is 1 everywhere on the `Finset`. -/
@[to_additive "If a sum is 0 and the function is 0 except possibly at one
point, it is 0 everywhere on the `Finset`."]
theorem eq_one_of_prod_eq_one {s : Finset α} {f : α → β} {a : α} (hp : ∏ x in s, f x = 1)
    (h1 : ∀ x ∈ s, x ≠ a → f x = 1) : ∀ x ∈ s, f x = 1 := by
  intro x hx
  classical
    by_cases h : x = a
    · rw [h]
      rw [h] at hx
      rw [← prod_subset (singleton_subset_iff.2 hx) fun t ht ha => h1 t ht (not_mem_singleton.1 ha),
        prod_singleton] at hp
      exact hp
    · exact h1 x hx h

@[to_additive sum_boole_nsmul]
theorem prod_pow_boole [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
    (∏ x in s, f x ^ ite (a = x) 1 0) = ite (a ∈ s) (f a) 1 := by simp

theorem prod_dvd_prod_of_dvd {S : Finset α} (g1 g2 : α → β) (h : ∀ a ∈ S, g1 a ∣ g2 a) :
    S.prod g1 ∣ S.prod g2 := by
  classical
    induction' S using Finset.induction_on' with a T _haS _hTS haT IH
    · simp
    rw [Finset.prod_insert haT, Finset.prod_insert haT]
    exact mul_dvd_mul (h a $ T.mem_insert_self a) (IH fun b hb ↦ h b $ Finset.mem_insert_of_mem hb)

theorem prod_dvd_prod_of_subset {ι M : Type*} [CommMonoid M] (s t : Finset ι) (f : ι → M)
    (h : s ⊆ t) : (∏ i in s, f i) ∣ ∏ i in t, f i :=
  Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| by simpa

end CommMonoid

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` over `s`
  is the sum of the products of `g` and `h`. -/
theorem prod_add_prod_eq [CommSemiring β] {s : Finset α} {i : α} {f g h : α → β} (hi : i ∈ s)
    (h1 : g i + h i = f i) (h2 : ∀ j ∈ s, j ≠ i → g j = f j) (h3 : ∀ j ∈ s, j ≠ i → h j = f j) :
    (∏ i in s, g i) + ∏ i in s, h i = ∏ i in s, f i := by
  classical
    simp_rw [prod_eq_mul_prod_diff_singleton hi, ← h1, right_distrib]
    congr 2 <;> apply prod_congr rfl <;> simpa

theorem card_eq_sum_ones (s : Finset α) : s.card = ∑ x in s, 1 := by
  rw [sum_const, smul_eq_mul, mul_one]

theorem sum_const_nat {m : ℕ} {f : α → ℕ} (h₁ : ∀ x ∈ s, f x = m) :
    ∑ x in s, f x = card s * m := by
  rw [← Nat.nsmul_eq_mul, ← sum_const]
  apply sum_congr rfl h₁

@[simp]
theorem sum_boole {s : Finset α} {p : α → Prop} [NonAssocSemiring β] {hp : DecidablePred p} :
    (∑ x in s, if p x then (1 : β) else (0 : β)) = (s.filter p).card := by
  simp only [add_zero, mul_one, Finset.sum_const, nsmul_eq_mul, eq_self_iff_true,
    Finset.sum_const_zero, Finset.sum_ite, mul_zero]

theorem _root_.Commute.sum_right [NonUnitalNonAssocSemiring β] (s : Finset α) (f : α → β) (b : β)
    (h : ∀ i ∈ s, Commute b (f i)) : Commute b (∑ i in s, f i) :=
  (Commute.multiset_sum_right _ _) fun b hb => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hb
    exact h _ hi

theorem _root_.Commute.sum_left [NonUnitalNonAssocSemiring β] (s : Finset α) (f : α → β) (b : β)
    (h : ∀ i ∈ s, Commute (f i) b) : Commute (∑ i in s, f i) b :=
  ((Commute.sum_right _ _ _) fun _i hi => (h _ hi).symm).symm

section Opposite

open MulOpposite

/-- Moving to the opposite additive commutative monoid commutes with summing. -/
@[simp]
theorem op_sum [AddCommMonoid β] {s : Finset α} (f : α → β) :
    op (∑ x in s, f x) = ∑ x in s, op (f x) :=
  (opAddEquiv : β ≃+ βᵐᵒᵖ).map_sum _ _

@[simp]
theorem unop_sum [AddCommMonoid β] {s : Finset α} (f : α → βᵐᵒᵖ) :
    unop (∑ x in s, f x) = ∑ x in s, unop (f x) :=
  (opAddEquiv : β ≃+ βᵐᵒᵖ).symm.map_sum _ _

end Opposite

section DivisionCommMonoid

variable [DivisionCommMonoid β]

@[to_additive (attr := simp)]
theorem prod_inv_distrib : (∏ x in s, (f x)⁻¹) = (∏ x in s, f x)⁻¹ :=
  Multiset.prod_map_inv

@[to_additive (attr := simp)]
theorem prod_div_distrib : ∏ x in s, f x / g x = (∏ x in s, f x) / ∏ x in s, g x :=
  Multiset.prod_map_div

@[to_additive]
theorem prod_zpow (f : α → β) (s : Finset α) (n : ℤ) : ∏ a in s, f a ^ n = (∏ a in s, f a) ^ n :=
  Multiset.prod_map_zpow

end DivisionCommMonoid

section CommGroup

variable [CommGroup β] [DecidableEq α]

@[to_additive (attr := simp)]
theorem prod_sdiff_eq_div (h : s₁ ⊆ s₂) :
    ∏ x in s₂ \ s₁, f x = (∏ x in s₂, f x) / ∏ x in s₁, f x := by
  rw [eq_div_iff_mul_eq', prod_sdiff h]

@[to_additive]
theorem prod_sdiff_div_prod_sdiff :
    (∏ x in s₂ \ s₁, f x) / ∏ x in s₁ \ s₂, f x = (∏ x in s₂, f x) / ∏ x in s₁, f x := by
  simp [← Finset.prod_sdiff (@inf_le_left _ _ s₁ s₂), ← Finset.prod_sdiff (@inf_le_right _ _ s₁ s₂)]

@[to_additive (attr := simp)]
theorem prod_erase_eq_div {a : α} (h : a ∈ s) :
    ∏ x in s.erase a, f x = (∏ x in s, f x) / f a := by
  rw [eq_div_iff_mul_eq', prod_erase_mul _ _ h]

end CommGroup

@[simp]
theorem card_sigma {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) :
    card (s.sigma t) = ∑ a in s, card (t a) :=
  Multiset.card_sigma _ _

@[simp]
theorem card_disjiUnion (s : Finset α) (t : α → Finset β) (h) :
    (s.disjiUnion t h).card = s.sum fun i => (t i).card :=
  Multiset.card_bind _ _

theorem card_biUnion [DecidableEq β] {s : Finset α} {t : α → Finset β}
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (t x) (t y)) :
    (s.biUnion t).card = ∑ u in s, card (t u) :=
  calc
    (s.biUnion t).card = ∑ i in s.biUnion t, 1 := card_eq_sum_ones _
    _ = ∑ a in s, ∑ _i in t a, 1 := Finset.sum_biUnion h
    _ = ∑ u in s, card (t u) := by simp_rw [card_eq_sum_ones]

theorem card_biUnion_le [DecidableEq β] {s : Finset α} {t : α → Finset β} :
    (s.biUnion t).card ≤ ∑ a in s, (t a).card :=
  haveI := Classical.decEq α
  Finset.induction_on s (by simp) fun a s has ih =>
    calc
      ((insert a s).biUnion t).card ≤ (t a).card + (s.biUnion t).card := by
        { rw [biUnion_insert]; exact Finset.card_union_le _ _ }
      _ ≤ ∑ a in insert a s, card (t a) := by rw [sum_insert has]; exact add_le_add_left ih _

theorem card_eq_sum_card_fiberwise [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β}
    (H : ∀ x ∈ s, f x ∈ t) : s.card = ∑ a in t, (s.filter fun x => f x = a).card := by
  simp only [card_eq_sum_ones, sum_fiberwise_of_maps_to H]

theorem card_eq_sum_card_image [DecidableEq β] (f : α → β) (s : Finset α) :
    s.card = ∑ a in s.image f, (s.filter fun x => f x = a).card :=
  card_eq_sum_card_fiberwise fun _ => mem_image_of_mem _

theorem mem_sum {f : α → Multiset β} (s : Finset α) (b : β) :
    (b ∈ ∑ x in s, f x) ↔ ∃ a ∈ s, b ∈ f a := by
  classical
    refine' s.induction_on (by simp) _
    · intro a t hi ih
      simp [sum_insert hi, ih, or_and_right, exists_or]

section ProdEqZero

variable [CommMonoidWithZero β]

theorem prod_eq_zero (ha : a ∈ s) (h : f a = 0) : ∏ x in s, f x = 0 := by
  haveI := Classical.decEq α
  rw [← prod_erase_mul _ _ ha, h, mul_zero]

theorem prod_boole {s : Finset α} {p : α → Prop} [DecidablePred p] :
    (∏ i in s, ite (p i) (1 : β) (0 : β)) = ite (∀ i ∈ s, p i) 1 0 := by
  split_ifs with h
  · apply prod_eq_one
    intro i hi
    rw [if_pos (h i hi)]
  · push_neg at h
    rcases h with ⟨i, hi, hq⟩
    apply prod_eq_zero hi
    rw [if_neg hq]

variable [Nontrivial β] [NoZeroDivisors β]

theorem prod_eq_zero_iff : ∏ x in s, f x = 0 ↔ ∃ a ∈ s, f a = 0 := by
  classical
    induction' s using Finset.induction_on with a s ha ih
    · exact ⟨Not.elim one_ne_zero, fun ⟨_, H, _⟩ => by simp at H⟩
    · rw [prod_insert ha, mul_eq_zero, exists_mem_insert, ih, ← bex_def]

theorem prod_ne_zero_iff : ∏ x in s, f x ≠ 0 ↔ ∀ a ∈ s, f a ≠ 0 := by
  rw [Ne, prod_eq_zero_iff]
  push_neg; rfl

end ProdEqZero

@[to_additive]
theorem prod_unique_nonempty {α β : Type*} [CommMonoid β] [Unique α] (s : Finset α) (f : α → β)
    (h : s.Nonempty) : ∏ x in s, f x = f default := by
  rw [h.eq_singleton_default, Finset.prod_singleton]

theorem sum_nat_mod (s : Finset α) (n : ℕ) (f : α → ℕ) :
    (∑ i in s, f i) % n = (∑ i in s, f i % n) % n :=
  (Multiset.sum_nat_mod _ _).trans <| by rw [Finset.sum, Multiset.map_map]; rfl

theorem prod_nat_mod (s : Finset α) (n : ℕ) (f : α → ℕ) :
    (∏ i in s, f i) % n = (∏ i in s, f i % n) % n :=
  (Multiset.prod_nat_mod _ _).trans <| by rw [Finset.prod, Multiset.map_map]; rfl

theorem sum_int_mod (s : Finset α) (n : ℤ) (f : α → ℤ) :
    (∑ i in s, f i) % n = (∑ i in s, f i % n) % n :=
  (Multiset.sum_int_mod _ _).trans <| by rw [Finset.sum, Multiset.map_map]; rfl

theorem prod_int_mod (s : Finset α) (n : ℤ) (f : α → ℤ) :
    (∏ i in s, f i) % n = (∏ i in s, f i % n) % n :=
  (Multiset.prod_int_mod _ _).trans <| by rw [Finset.prod, Multiset.map_map]; rfl

end Finset

namespace Fintype

open Finset

/-- `Fintype.prod_bijective` is a variant of `Finset.prod_bij` that accepts `Function.bijective`.

See `Function.bijective.prod_comp` for a version without `h`. -/
@[to_additive "`Fintype.sum_equiv` is a variant of `Finset.sum_bij` that accepts
`Function.bijective`.

See `Function.bijective.sum_comp` for a version without `h`. "]
theorem prod_bijective {α β M : Type*} [Fintype α] [Fintype β] [CommMonoid M] (e : α → β)
    (he : Function.Bijective e) (f : α → M) (g : β → M) (h : ∀ x, f x = g (e x)) :
    ∏ x : α, f x = ∏ x : β, g x :=
  prod_bij (fun x _ => e x) (fun x _ => mem_univ (e x)) (fun x _ => h x)
    (fun _x _x' _ _ h => he.injective h) fun y _ =>
    (he.surjective y).imp fun _a h => ⟨mem_univ _, h.symm⟩

/-- `Fintype.prod_equiv` is a specialization of `Finset.prod_bij` that
automatically fills in most arguments.

See `Equiv.prod_comp` for a version without `h`.
-/
@[to_additive "`Fintype.sum_equiv` is a specialization of `Finset.sum_bij` that
automatically fills in most arguments.

See `Equiv.sum_comp` for a version without `h`."]
theorem prod_equiv {α β M : Type*} [Fintype α] [Fintype β] [CommMonoid M] (e : α ≃ β) (f : α → M)
    (g : β → M) (h : ∀ x, f x = g (e x)) : ∏ x : α, f x = ∏ x : β, g x :=
  prod_bijective e e.bijective f g h

@[to_additive]
theorem prod_unique {α β : Type*} [CommMonoid β] [Unique α] [Fintype α] (f : α → β) :
    ∏ x : α, f x = f default := by rw [univ_unique, prod_singleton]

@[to_additive]
theorem prod_empty {α β : Type*} [CommMonoid β] [IsEmpty α] [Fintype α] (f : α → β) :
    ∏ x : α, f x = 1 :=
  Finset.prod_of_empty _

@[to_additive]
theorem prod_subsingleton {α β : Type*} [CommMonoid β] [Subsingleton α] [Fintype α] (f : α → β)
    (a : α) : ∏ x : α, f x = f a := by
  haveI : Unique α := uniqueOfSubsingleton a
  rw [prod_unique f, Subsingleton.elim default a]

@[to_additive]
theorem prod_subtype_mul_prod_subtype {α β : Type*} [Fintype α] [CommMonoid β] (p : α → Prop)
    (f : α → β) [DecidablePred p] :
    (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i = ∏ i, f i := by
  classical
    let s := { x | p x }.toFinset
    rw [← Finset.prod_subtype s, ← Finset.prod_subtype sᶜ]
    · exact Finset.prod_mul_prod_compl _ _
    · simp
    · simp

end Fintype

namespace List

@[to_additive]
theorem prod_toFinset {M : Type*} [DecidableEq α] [CommMonoid M] (f : α → M) :
    ∀ {l : List α} (_hl : l.Nodup), l.toFinset.prod f = (l.map f).prod
  | [], _ => by simp
  | a :: l, hl => by
    let ⟨not_mem, hl⟩ := List.nodup_cons.mp hl
    simp [Finset.prod_insert (mt List.mem_toFinset.mp not_mem), prod_toFinset _ hl]

end List

namespace Multiset

theorem disjoint_list_sum_left {a : Multiset α} {l : List (Multiset α)} :
    Multiset.Disjoint l.sum a ↔ ∀ b ∈ l, Multiset.Disjoint b a := by
  induction' l with b bs ih
  · simp only [zero_disjoint, List.not_mem_nil, IsEmpty.forall_iff, forall_const, List.sum_nil]
  · simp_rw [List.sum_cons, disjoint_add_left, List.mem_cons, forall_eq_or_imp]
    simp [and_congr_left_iff, iff_self_iff, ih]

theorem disjoint_list_sum_right {a : Multiset α} {l : List (Multiset α)} :
    Multiset.Disjoint a l.sum ↔ ∀ b ∈ l, Multiset.Disjoint a b := by
  simpa only [@disjoint_comm _ a] using disjoint_list_sum_left

theorem disjoint_sum_left {a : Multiset α} {i : Multiset (Multiset α)} :
    Multiset.Disjoint i.sum a ↔ ∀ b ∈ i, Multiset.Disjoint b a :=
  Quotient.inductionOn i fun l => by
    rw [quot_mk_to_coe, Multiset.coe_sum]
    exact disjoint_list_sum_left

theorem disjoint_sum_right {a : Multiset α} {i : Multiset (Multiset α)} :
    Multiset.Disjoint a i.sum ↔ ∀ b ∈ i, Multiset.Disjoint a b := by
  simpa only [@disjoint_comm _ a] using disjoint_sum_left

theorem disjoint_finset_sum_left {β : Type*} {i : Finset β} {f : β → Multiset α} {a : Multiset α} :
    Multiset.Disjoint (i.sum f) a ↔ ∀ b ∈ i, Multiset.Disjoint (f b) a := by
  convert @disjoint_sum_left _ a (map f i.val)
  simp [and_congr_left_iff, iff_self_iff]

theorem disjoint_finset_sum_right {β : Type*} {i : Finset β} {f : β → Multiset α}
    {a : Multiset α} : Multiset.Disjoint a (i.sum f) ↔ ∀ b ∈ i, Multiset.Disjoint a (f b) := by
  simpa only [disjoint_comm] using disjoint_finset_sum_left

variable [DecidableEq α]

theorem add_eq_union_left_of_le {x y z : Multiset α} (h : y ≤ x) :
    z + x = z ∪ y ↔ z.Disjoint x ∧ x = y := by
  rw [← add_eq_union_iff_disjoint]
  constructor
  · intro h0
    rw [and_iff_right_of_imp]
    · exact (le_of_add_le_add_left <| h0.trans_le <| union_le_add z y).antisymm h
    · rintro rfl
      exact h0
  · rintro ⟨h0, rfl⟩
    exact h0

theorem add_eq_union_right_of_le {x y z : Multiset α} (h : z ≤ y) :
    x + y = x ∪ z ↔ y = z ∧ x.Disjoint y := by
  simpa only [and_comm] using add_eq_union_left_of_le h

theorem finset_sum_eq_sup_iff_disjoint {β : Type*} {i : Finset β} {f : β → Multiset α} :
    i.sum f = i.sup f ↔
      ∀ (x) (_ : x ∈ i) (y) (_ : y ∈ i), x ≠ y → Multiset.Disjoint (f x) (f y) := by
  induction' i using Finset.cons_induction_on with z i hz hr
  · simp only [Finset.not_mem_empty, IsEmpty.forall_iff, imp_true_iff, Finset.sum_empty,
      Finset.sup_empty, bot_eq_zero, eq_self_iff_true]
  · simp_rw [Finset.sum_cons hz, Finset.sup_cons, Finset.mem_cons, Multiset.sup_eq_union,
      forall_eq_or_imp, Ne.def, IsEmpty.forall_iff, true_and_iff,
      imp_and, forall_and, ← hr, @eq_comm _ z]
    have := fun x (H : x ∈ i) => ne_of_mem_of_not_mem H hz
    simp (config := { contextual := true }) only [this, not_false_iff, true_imp_iff]
    simp_rw [← disjoint_finset_sum_left, ← disjoint_finset_sum_right, disjoint_comm, ← and_assoc,
      and_self_iff]
    exact add_eq_union_left_of_le (Finset.sup_le fun x hx => le_sum_of_mem (mem_map_of_mem f hx))

theorem sup_powerset_len {α : Type*} [DecidableEq α] (x : Multiset α) :
    (Finset.sup (Finset.range (card x + 1)) fun k => x.powersetCard k) = x.powerset := by
  convert bind_powerset_len x using 1
  rw [Multiset.bind, Multiset.join, ← Finset.range_val, ← Finset.sum_eq_multiset_sum]
  exact
    Eq.symm (finset_sum_eq_sup_iff_disjoint.mpr fun _ _ _ _ h => pairwise_disjoint_powersetCard x h)

@[simp]
theorem toFinset_sum_count_eq (s : Multiset α) : ∑ a in s.toFinset, s.count a = card s :=
  calc
    ∑ a in s.toFinset, s.count a = ∑ a in s.toFinset, s.count a • 1 := by
      { simp only [smul_eq_mul, mul_one] }
    _ = (s.map fun _ => 1).sum := (Finset.sum_multiset_map_count _ _).symm
    _ = card s := by simp

theorem count_sum' {s : Finset β} {a : α} {f : β → Multiset α} :
    count a (∑ x in s, f x) = ∑ x in s, count a (f x) := by
  dsimp only [Finset.sum]
  rw [count_sum]

@[simp]
theorem toFinset_sum_count_nsmul_eq (s : Multiset α) :
    ∑ a in s.toFinset, s.count a • {a} = s := by
  rw [← Finset.sum_multiset_map_count, Multiset.sum_map_singleton]

theorem exists_smul_of_dvd_count (s : Multiset α) {k : ℕ}
    (h : ∀ a : α, a ∈ s → k ∣ Multiset.count a s) : ∃ u : Multiset α, s = k • u := by
  use ∑ a in s.toFinset, (s.count a / k) • {a}
  have h₂ :
    (∑ x : α in s.toFinset, k • (count x s / k) • ({x} : Multiset α)) =
      ∑ x : α in s.toFinset, count x s • {x} := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← mul_nsmul', Nat.mul_div_cancel' (h x (mem_toFinset.mp hx))]
  rw [← Finset.sum_nsmul, h₂, toFinset_sum_count_nsmul_eq]

theorem toFinset_prod_dvd_prod [CommMonoid α] (S : Multiset α) : S.toFinset.prod id ∣ S.prod := by
  rw [Finset.prod_eq_multiset_prod]
  refine' Multiset.prod_dvd_prod_of_le _
  simp [Multiset.dedup_le S]

@[to_additive]
theorem prod_sum {α : Type*} {ι : Type*} [CommMonoid α] (f : ι → Multiset α) (s : Finset ι) :
    (∑ x in s, f x).prod = ∏ x in s, (f x).prod := by
  classical
    induction' s using Finset.induction_on with a t hat ih
    · rw [Finset.sum_empty, Finset.prod_empty, Multiset.prod_zero]
    · rw [Finset.sum_insert hat, Finset.prod_insert hat, Multiset.prod_add, ih]

end Multiset

namespace Nat

@[simp, norm_cast]
theorem cast_list_sum [AddMonoidWithOne β] (s : List ℕ) : (↑s.sum : β) = (s.map (↑)).sum :=
  map_list_sum (castAddMonoidHom β) _

@[simp, norm_cast]
theorem cast_list_prod [Semiring β] (s : List ℕ) : (↑s.prod : β) = (s.map (↑)).prod :=
  map_list_prod (castRingHom β) _

@[simp, norm_cast]
theorem cast_multiset_sum [AddCommMonoidWithOne β] (s : Multiset ℕ) :
    (↑s.sum : β) = (s.map (↑)).sum :=
  map_multiset_sum (castAddMonoidHom β) _

@[simp, norm_cast]
theorem cast_multiset_prod [CommSemiring β] (s : Multiset ℕ) : (↑s.prod : β) = (s.map (↑)).prod :=
  map_multiset_prod (castRingHom β) _

@[simp, norm_cast]
theorem cast_sum [AddCommMonoidWithOne β] (s : Finset α) (f : α → ℕ) :
    ↑(∑ x in s, f x : ℕ) = ∑ x in s, (f x : β) :=
  map_sum (castAddMonoidHom β) _ _

@[simp, norm_cast]
theorem cast_prod [CommSemiring β] (f : α → ℕ) (s : Finset α) :
    (↑(∏ i in s, f i) : β) = ∏ i in s, (f i : β) :=
  map_prod (castRingHom β) _ _

end Nat

namespace Int

@[simp, norm_cast]
theorem cast_list_sum [AddGroupWithOne β] (s : List ℤ) : (↑s.sum : β) = (s.map (↑)).sum :=
  map_list_sum (castAddHom β) _

@[simp, norm_cast]
theorem cast_list_prod [Ring β] (s : List ℤ) : (↑s.prod : β) = (s.map (↑)).prod :=
  map_list_prod (castRingHom β) _

@[simp, norm_cast]
theorem cast_multiset_sum [AddCommGroupWithOne β] (s : Multiset ℤ) :
    (↑s.sum : β) = (s.map (↑)).sum :=
  map_multiset_sum (castAddHom β) _

@[simp, norm_cast]
theorem cast_multiset_prod {R : Type*} [CommRing R] (s : Multiset ℤ) :
    (↑s.prod : R) = (s.map (↑)).prod :=
  map_multiset_prod (castRingHom R) _

@[simp, norm_cast]
theorem cast_sum [AddCommGroupWithOne β] (s : Finset α) (f : α → ℤ) :
    ↑(∑ x in s, f x : ℤ) = ∑ x in s, (f x : β) :=
  map_sum (castAddHom β) _ _

@[simp, norm_cast]
theorem cast_prod {R : Type*} [CommRing R] (f : α → ℤ) (s : Finset α) :
    (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R) :=
  (Int.castRingHom R).map_prod _ _

end Int

@[simp, norm_cast]
theorem Units.coe_prod {M : Type*} [CommMonoid M] (f : α → Mˣ) (s : Finset α) :
    (↑(∏ i in s, f i) : M) = ∏ i in s, (f i : M) :=
  (Units.coeHom M).map_prod _ _

theorem Units.mk0_prod [CommGroupWithZero β] (s : Finset α) (f : α → β) (h) :
    Units.mk0 (∏ b in s, f b) h =
      ∏ b in s.attach, Units.mk0 (f b) fun hh => h (Finset.prod_eq_zero b.2 hh) := by
  classical induction s using Finset.induction_on <;> simp [*]

theorem nat_abs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ i in s, f i).natAbs ≤ ∑ i in s, (f i).natAbs := by
  classical
    induction' s using Finset.induction_on with i s his IH
    · simp only [Finset.sum_empty, Int.natAbs_zero]
    · simp only [his, Finset.sum_insert, not_false_iff]
      exact (Int.natAbs_add_le _ _).trans (add_le_add le_rfl IH)

/-! ### `Additive`, `Multiplicative` -/


open Additive Multiplicative

section Monoid

variable [Monoid α]

@[simp]
theorem ofMul_list_prod (s : List α) : ofMul s.prod = (s.map ofMul).sum := by simp [ofMul]; rfl

@[simp]
theorem toMul_list_sum (s : List (Additive α)) : toMul s.sum = (s.map toMul).prod := by
  simp [toMul, ofMul]; rfl

end Monoid

section AddMonoid

variable [AddMonoid α]

@[simp]
theorem ofAdd_list_prod (s : List α) : ofAdd s.sum = (s.map ofAdd).prod := by simp [ofAdd]; rfl

@[simp]
theorem toAdd_list_sum (s : List (Multiplicative α)) : toAdd s.prod = (s.map toAdd).sum := by
  simp [toAdd, ofAdd]; rfl

end AddMonoid

section CommMonoid

variable [CommMonoid α]

@[simp]
theorem ofMul_multiset_prod (s : Multiset α) : ofMul s.prod = (s.map ofMul).sum := by
  simp [ofMul]; rfl

@[simp]
theorem toMul_multiset_sum (s : Multiset (Additive α)) : toMul s.sum = (s.map toMul).prod := by
  simp [toMul, ofMul]; rfl

@[simp]
theorem ofMul_prod (s : Finset ι) (f : ι → α) : ofMul (∏ i in s, f i) = ∑ i in s, ofMul (f i) :=
  rfl

@[simp]
theorem toMul_sum (s : Finset ι) (f : ι → Additive α) :
    toMul (∑ i in s, f i) = ∏ i in s, toMul (f i) :=
  rfl

end CommMonoid

section AddCommMonoid

variable [AddCommMonoid α]

@[simp]
theorem ofAdd_multiset_prod (s : Multiset α) : ofAdd s.sum = (s.map ofAdd).prod := by
  simp [ofAdd]; rfl

@[simp]
theorem toAdd_multiset_sum (s : Multiset (Multiplicative α)) :
    toAdd s.prod = (s.map toAdd).sum := by
  simp [toAdd, ofAdd]; rfl

@[simp]
theorem ofAdd_sum (s : Finset ι) (f : ι → α) : ofAdd (∑ i in s, f i) = ∏ i in s, ofAdd (f i) :=
  rfl

@[simp]
theorem toAdd_prod (s : Finset ι) (f : ι → Multiplicative α) :
    toAdd (∏ i in s, f i) = ∑ i in s, toAdd (f i) :=
  rfl

end AddCommMonoid
