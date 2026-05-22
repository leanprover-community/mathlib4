/-
Copyright (c) 2020 Kexing Ying and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Notation.FiniteSupport
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Set.Finite.Lattice

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite products and sums over types and sets

We define products and sums over types and subsets of types, with no finiteness hypotheses.
All infinite products and sums are defined to be junk values (i.e. one or zero).
This approach is sometimes easier to use than `Finset.sum`,
when issues arise with `Finset` and `Fintype` being data.

## Main definitions

We use the following variables:

* `α`, `β` - types with no structure;
* `s`, `t` - sets
* `M`, `N` - additive or multiplicative commutative monoids
* `f`, `g` - functions

Definitions in this file:

* `finsum f : M` : the sum of `f x` as `x` ranges over the support of `f`, if it's finite.
  Zero otherwise.

* `finprod f : M` : the product of `f x` as `x` ranges over the multiplicative support of `f`, if
  it's finite. One otherwise.

## Notation

* `∑ᶠ i, f i` and `∑ᶠ i : α, f i` for `finsum f`

* `∏ᶠ i, f i` and `∏ᶠ i : α, f i` for `finprod f`

This notation works for functions `f : p → M`, where `p : Prop`, so the following works:

* `∑ᶠ i ∈ s, f i`, where `f : α → M`, `s : Set α` : sum over the set `s`;
* `∑ᶠ n < 5, f n`, where `f : ℕ → M` : same as `f 0 + f 1 + f 2 + f 3 + f 4`;
* `∏ᶠ (n >= -2) (hn : n < 3), f n`, where `f : ℤ → M` : same as `f (-2) * f (-1) * f 0 * f 1 * f 2`.

## Implementation notes

`finsum` and `finprod` is "yet another way of doing finite sums and products in Lean". However
experiments in the wild (e.g. with matroids) indicate that it is a helpful approach in settings
where the user is not interested in computability and wants to do reasoning without running into
typeclass diamonds caused by the constructive finiteness used in definitions such as `Finset` and
`Fintype`. By sticking solely to `Set.Finite` we avoid these problems. We are aware that there are
other solutions but for beginner mathematicians this approach is easier in practice.

Another application is the construction of a partition of unity from a collection of “bump”
functions. In this case the finite set depends on the point and it's convenient to have a definition
that does not mention the set explicitly.

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

We did not add `IsFinite (X : Type) : Prop`, because it is simply `Nonempty (Fintype X)`.

## Tags

finsum, finprod, finite sum, finite product
-/

@[expose] public section


open Function Set

/-!
### Definition and relation to `Finset.sum` and `Finset.prod`
-/

section sort

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

section

/- Note: we use classical logic only for these definitions, to ensure that we do not write lemmas
with `Classical.dec` in their statement. -/

open Classical in
/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero
otherwise. -/
noncomputable irreducible_def finsum (lemma := finsum_def') [AddCommMonoid M] (f : α → M) : M :=
  if h : HasFiniteSupport (f ∘ PLift.down) then ∑ i ∈ h.toFinset, f i.down else 0

open Classical in
/-- Product of `f x` as `x` ranges over the elements of the multiplicative support of `f`, if it's
finite. One otherwise. -/
@[to_additive existing]
noncomputable irreducible_def finprod (lemma := finprod_def') (f : α → M) : M :=
  if h : HasFiniteMulSupport (f ∘ PLift.down) then ∏ i ∈ h.toFinset, f i.down else 1

attribute [to_additive existing] finprod_def'

end

open Batteries.ExtendedBinder

/-- `∑ᶠ x, f x` is notation for `finsum f`. It is the sum of `f x`, where `x` ranges over the
support of `f`, if it's finite, zero otherwise. Taking the sum over multiple arguments or
conditions is possible, e.g. `∏ᶠ (x) (y), f x y` and `∏ᶠ (x) (h: x ∈ s), f x` -/
notation3"∑ᶠ " (...) ", " r:67:(scoped f => finsum f) => r

/-- `∏ᶠ x, f x` is notation for `finprod f`. It is the product of `f x`, where `x` ranges over the
multiplicative support of `f`, if it's finite, one otherwise. Taking the product over multiple
arguments or conditions is possible, e.g. `∏ᶠ (x) (y), f x y` and `∏ᶠ (x) (h: x ∈ s), f x` -/
notation3"∏ᶠ " (...) ", " r:67:(scoped f => finprod f) => r

-- Porting note: The following ports the lean3 notation for this file, but is currently very fickle.

-- syntax (name := bigfinsum) "∑ᶠ" extBinders ", " term:67 : term
-- macro_rules (kind := bigfinsum)
--   | `(∑ᶠ $x:ident, $p) => `(finsum (fun $x:ident ↦ $p))
--   | `(∑ᶠ $x:ident : $t, $p) => `(finsum (fun $x:ident : $t ↦ $p))
--   | `(∑ᶠ $x:ident $b:binderPred, $p) =>
--     `(finsum fun $x => (finsum (α := satisfies_binder_pred% $x $b) (fun _ => $p)))

--   | `(∑ᶠ ($x:ident) ($h:ident : $t), $p) =>
--       `(finsum fun ($x) => finsum (α := $t) (fun $h => $p))
--   | `(∑ᶠ ($x:ident : $_) ($h:ident : $t), $p) =>
--       `(finsum fun ($x) => finsum (α := $t) (fun $h => $p))

--   | `(∑ᶠ ($x:ident) ($y:ident), $p) =>
--       `(finsum fun $x => (finsum fun $y => $p))
--   | `(∑ᶠ ($x:ident) ($y:ident) ($h:ident : $t), $p) =>
--       `(finsum fun $x => (finsum fun $y => (finsum (α := $t) fun $h => $p)))

--   | `(∑ᶠ ($x:ident) ($y:ident) ($z:ident), $p) =>
--       `(finsum fun $x => (finsum fun $y => (finsum fun $z => $p)))
--   | `(∑ᶠ ($x:ident) ($y:ident) ($z:ident) ($h:ident : $t), $p) =>
--       `(finsum fun $x => (finsum fun $y => (finsum fun $z => (finsum (α := $t) fun $h => $p))))
--
--
-- syntax (name := bigfinprod) "∏ᶠ " extBinders ", " term:67 : term
-- macro_rules (kind := bigfinprod)
--   | `(∏ᶠ $x:ident, $p) => `(finprod (fun $x:ident ↦ $p))
--   | `(∏ᶠ $x:ident : $t, $p) => `(finprod (fun $x:ident : $t ↦ $p))
--   | `(∏ᶠ $x:ident $b:binderPred, $p) =>
--     `(finprod fun $x => (finprod (α := satisfies_binder_pred% $x $b) (fun _ => $p)))

--   | `(∏ᶠ ($x:ident) ($h:ident : $t), $p) =>
--       `(finprod fun ($x) => finprod (α := $t) (fun $h => $p))
--   | `(∏ᶠ ($x:ident : $_) ($h:ident : $t), $p) =>
--       `(finprod fun ($x) => finprod (α := $t) (fun $h => $p))

--   | `(∏ᶠ ($x:ident) ($y:ident), $p) =>
--       `(finprod fun $x => (finprod fun $y => $p))
--   | `(∏ᶠ ($x:ident) ($y:ident) ($h:ident : $t), $p) =>
--       `(finprod fun $x => (finprod fun $y => (finprod (α := $t) fun $h => $p)))

--   | `(∏ᶠ ($x:ident) ($y:ident) ($z:ident), $p) =>
--       `(finprod fun $x => (finprod fun $y => (finprod fun $z => $p)))
--   | `(∏ᶠ ($x:ident) ($y:ident) ($z:ident) ($h:ident : $t), $p) =>
--       `(finprod fun $x => (finprod fun $y => (finprod fun $z =>
--          (finprod (α := $t) fun $h => $p))))

@[to_additive]
theorem finprod_eq_prod_plift_of_mulSupport_toFinset_subset {f : α → M}
    (hf : HasFiniteMulSupport (f ∘ PLift.down)) {s : Finset (PLift α)} (hs : hf.toFinset ⊆ s) :
    ∏ᶠ i, f i = ∏ i ∈ s, f i.down := by
  rw [finprod, dif_pos hf]
  refine Finset.prod_subset hs fun x _ hxf => ?_
  rwa [hf.mem_toFinset, notMem_mulSupport] at hxf

@[to_additive]
theorem finprod_eq_prod_plift_of_mulSupport_subset {f : α → M} {s : Finset (PLift α)}
    (hs : mulSupport (f ∘ PLift.down) ⊆ s) : ∏ᶠ i, f i = ∏ i ∈ s, f i.down :=
  finprod_eq_prod_plift_of_mulSupport_toFinset_subset (s.finite_toSet.subset hs) fun x hx => by
    rw [Finite.mem_toFinset] at hx
    exact hs hx

@[to_additive (attr := simp)]
theorem finprod_one : (∏ᶠ _ : α, (1 : M)) = 1 := by
  have : (mulSupport fun x : PLift α => (fun _ => 1 : α → M) x.down) ⊆ (∅ : Finset (PLift α)) :=
    fun x h => by simp at h
  rw [finprod_eq_prod_plift_of_mulSupport_subset this, Finset.prod_empty]

@[to_additive]
theorem finprod_of_isEmpty [IsEmpty α] (f : α → M) : ∏ᶠ i, f i = 1 := by
  rw [← finprod_one]
  congr
  simp [eq_iff_true_of_subsingleton]

@[to_additive (attr := simp)]
theorem finprod_false (f : False → M) : ∏ᶠ i, f i = 1 :=
  finprod_of_isEmpty _

@[to_additive]
theorem finprod_eq_single (f : α → M) (a : α) (ha : ∀ x, x ≠ a → f x = 1) :
    ∏ᶠ x, f x = f a := by
  have : mulSupport (f ∘ PLift.down) ⊆ ({PLift.up a} : Finset (PLift α)) := by
    intro x
    contrapose
    simpa [PLift.eq_up_iff_down_eq] using ha x.down
  rw [finprod_eq_prod_plift_of_mulSupport_subset this, Finset.prod_singleton]

@[to_additive]
theorem finprod_unique [Unique α] (f : α → M) : ∏ᶠ i, f i = f default :=
  finprod_eq_single f default fun _x hx => (hx <| Unique.eq_default _).elim

@[to_additive (attr := simp)]
theorem finprod_true (f : True → M) : ∏ᶠ i, f i = f trivial :=
  @finprod_unique M True _ ⟨⟨trivial⟩, fun _ => rfl⟩ f

@[to_additive]
theorem finprod_eq_dif {p : Prop} [Decidable p] (f : p → M) :
    ∏ᶠ i, f i = if h : p then f h else 1 := by
  split_ifs with h
  · haveI : Unique p := ⟨⟨h⟩, fun _ => rfl⟩
    exact finprod_unique f
  · haveI : IsEmpty p := ⟨h⟩
    exact finprod_of_isEmpty f

@[to_additive]
theorem finprod_eq_if {p : Prop} [Decidable p] {x : M} : ∏ᶠ _ : p, x = if p then x else 1 :=
  finprod_eq_dif fun _ => x

@[to_additive]
theorem finprod_congr {f g : α → M} (h : ∀ x, f x = g x) : finprod f = finprod g :=
  congr_arg _ <| funext h

@[to_additive (attr := congr)]
theorem finprod_congr_Prop {p q : Prop} {f : p → M} {g : q → M} (hpq : p = q)
    (hfg : ∀ h : q, f (hpq.mpr h) = g h) : finprod f = finprod g := by
  subst q
  exact finprod_congr hfg

/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on the factors. -/
@[to_additive
      /-- To prove a property of a finite sum, it suffices to prove that the property is
      additive and holds on the summands. -/]
theorem finprod_induction {f : α → M} (p : M → Prop) (hp₀ : p 1)
    (hp₁ : ∀ x y, p x → p y → p (x * y)) (hp₂ : ∀ i, p (f i)) : p (∏ᶠ i, f i) := by
  rw [finprod]
  split_ifs
  exacts [Finset.prod_induction _ _ hp₁ hp₀ fun i _ => hp₂ _, hp₀]

theorem finprod_nonneg {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {f : α → R} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ∏ᶠ x, f x :=
  finprod_induction (fun x => 0 ≤ x) zero_le_one (fun _ _ => mul_nonneg) hf

@[to_additive finsum_nonneg]
theorem one_le_finprod' {M : Type*} [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    {f : α → M} (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ᶠ i, f i :=
  finprod_induction _ le_rfl (fun _ _ => one_le_mul) hf

/-- A version of `one_le_finprod'` for `PosMulMono` in place of `MulLeftMono`. -/
lemma one_le_finprod {M : Type*} [CommMonoidWithZero M] [Preorder M] [ZeroLEOneClass M]
    [PosMulMono M] {f : α → M} (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ᶠ i, f i :=
  finprod_induction _ le_rfl (fun _ _ ↦ one_le_mul_of_one_le_of_one_le) hf

@[to_additive]
theorem MonoidHom.map_finprod_plift (f : M →* N) (g : α → M)
    (h : HasFiniteMulSupport <| g ∘ PLift.down) : f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) := by
  rw [finprod_eq_prod_plift_of_mulSupport_subset h.coe_toFinset.ge,
    finprod_eq_prod_plift_of_mulSupport_subset, _root_.map_prod]
  rw [h.coe_toFinset]
  exact mulSupport_comp_subset f.map_one (g ∘ PLift.down)

@[to_additive]
theorem MonoidHom.map_finprod_Prop {p : Prop} (f : M →* N) (g : p → M) :
    f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) :=
  f.map_finprod_plift g (Set.toFinite _)

@[to_additive]
theorem MonoidHom.map_finprod_of_preimage_one (f : M →* N) (hf : ∀ x, f x = 1 → x = 1) (g : α → M) :
    f (∏ᶠ i, g i) = ∏ᶠ i, f (g i) := by
  by_cases hg : HasFiniteMulSupport <| g ∘ PLift.down; · exact f.map_finprod_plift g hg
  rw [finprod, dif_neg, f.map_one, finprod, dif_neg]
  exacts [Infinite.mono (fun x hx => mt (hf (g x.down)) hx) hg, hg]

@[to_additive]
theorem MonoidHom.map_finprod_of_injective (g : M →* N) (hg : Injective g) (f : α → M) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.map_finprod_of_preimage_one (fun _ => (hg.eq_iff' g.map_one).mp) f

@[to_additive]
theorem MulEquiv.map_finprod (g : M ≃* N) (f : α → M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.toMonoidHom.map_finprod_of_injective (EquivLike.injective g) f

@[to_additive]
theorem MulEquivClass.map_finprod {F : Type*} [EquivLike F M N] [MulEquivClass F M N] (g : F)
    (f : α → M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  MulEquiv.map_finprod (MulEquivClass.toMulEquiv g) f

/-- The torsion-free assumption makes sure that the result holds even when the support of `f` is
infinite. For a more usual version assuming `HasFiniteSupport f` instead, see `finsum_smul'`. -/
theorem finsum_smul {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] (f : ι → R) (x : M) : (∑ᶠ i, f i) • x = ∑ᶠ i, f i • x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · exact ((smulAddHom R M).flip x).map_finsum_of_injective (smul_left_injective R hx) _

/-- The torsion-free assumption makes sure that the result holds even when the support of `f` is
infinite. For a more usual version assuming `HasFiniteSupport f` instead, see `smul_finsum'`. -/
theorem smul_finsum {R M : Type*} [Semiring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] (c : R) (f : ι → M) : c • ∑ᶠ i, f i = ∑ᶠ i, c • f i := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp
  · exact (smulAddHom R M c).map_finsum_of_injective (smul_right_injective M hc) _

@[to_additive]
theorem finprod_inv_distrib [DivisionCommMonoid G] (f : α → G) : (∏ᶠ x, (f x)⁻¹) = (∏ᶠ x, f x)⁻¹ :=
  ((MulEquiv.inv G).map_finprod f).symm

end sort

section type

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

@[to_additive]
theorem finprod_eq_mulIndicator_apply (s : Set α) (f : α → M) (a : α) :
    ∏ᶠ _ : a ∈ s, f a = mulIndicator s f a := by
  classical convert! finprod_eq_if (M := M) (p := a ∈ s) (x := f a)

@[to_additive (attr := simp)]
theorem finprod_apply_ne_one (f : α → M) (a : α) : ∏ᶠ _ : f a ≠ 1, f a = f a := by
  rw [← mem_mulSupport, finprod_eq_mulIndicator_apply, mulIndicator_mulSupport]

@[to_additive]
theorem finprod_mem_def (s : Set α) (f : α → M) : ∏ᶠ a ∈ s, f a = ∏ᶠ a, mulIndicator s f a :=
  finprod_congr <| finprod_eq_mulIndicator_apply s f

@[to_additive]
lemma finprod_mem_mulSupport (f : α → M) : ∏ᶠ a ∈ mulSupport f, f a = ∏ᶠ a, f a := by
  rw [finprod_mem_def, mulIndicator_mulSupport]

@[to_additive]
theorem finprod_eq_prod_of_mulSupport_subset (f : α → M) {s : Finset α} (h : mulSupport f ⊆ s) :
    ∏ᶠ i, f i = ∏ i ∈ s, f i := by
  have A : mulSupport (f ∘ PLift.down) = Equiv.plift.symm '' mulSupport f := by
    rw [mulSupport_comp_eq_preimage]
    exact (Equiv.plift.symm.image_eq_preimage_symm _).symm
  have : mulSupport (f ∘ PLift.down) ⊆ s.map Equiv.plift.symm.toEmbedding := by
    rw [A, Finset.coe_map]
    exact image_mono h
  rw [finprod_eq_prod_plift_of_mulSupport_subset this]
  simp only [Finset.prod_map, Equiv.coe_toEmbedding]
  congr

@[to_additive]
theorem finprod_eq_prod_of_mulSupport_toFinset_subset (f : α → M) (hf : HasFiniteMulSupport f)
    {s : Finset α} (h : hf.toFinset ⊆ s) : ∏ᶠ i, f i = ∏ i ∈ s, f i :=
  finprod_eq_prod_of_mulSupport_subset _ fun _ hx => h <| hf.mem_toFinset.2 hx

@[to_additive]
theorem finprod_eq_prod_of_mulSupport_subset_of_finite (f : α → M) {s : Set α}
    (h : mulSupport f ⊆ s) (hs : s.Finite) : ∏ᶠ i, f i = ∏ i ∈ hs.toFinset, f i :=
  finprod_eq_prod_of_mulSupport_subset f <| by rwa [Set.Finite.coe_toFinset]

@[to_additive]
theorem finprod_eq_finsetProd_of_mulSupport_subset (f : α → M) {s : Finset α}
    (h : mulSupport f ⊆ (s : Set α)) : ∏ᶠ i, f i = ∏ i ∈ s, f i :=
  haveI h' : (s.finite_toSet.subset h).toFinset ⊆ s := by
    simpa [← Finset.coe_subset, Set.coe_toFinset]
  finprod_eq_prod_of_mulSupport_toFinset_subset _ _ h'

@[deprecated (since := "2026-04-08")]
alias finsum_eq_finset_sum_of_support_subset := finsum_eq_finsetSum_of_support_subset

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finprod_eq_finset_prod_of_mulSupport_subset := finprod_eq_finsetProd_of_mulSupport_subset

@[to_additive]
theorem finprod_def (f : α → M) [Decidable (HasFiniteMulSupport f)] :
    ∏ᶠ i : α, f i = if h : HasFiniteMulSupport f then ∏ i ∈ h.toFinset, f i else 1 := by
  split_ifs with h
  · exact finprod_eq_prod_of_mulSupport_toFinset_subset _ h (Finset.Subset.refl _)
  · rw [finprod, dif_neg]
    rw [HasFiniteMulSupport, mulSupport_comp_eq_preimage]
    exact mt (fun hf => hf.of_preimage Equiv.plift.surjective) h

@[to_additive]
theorem finprod_of_infinite_mulSupport {f : α → M} (hf : (mulSupport f).Infinite) :
    ∏ᶠ i, f i = 1 := by
  classical
  rw [finprod_def]
  simp only [HasFiniteMulSupport]
  rw [dif_neg hf]

@[to_additive]
theorem finprod_of_not_hasFiniteMulSupport {f : α → M} (hf : ¬ f.HasFiniteMulSupport) :
    ∏ᶠ i, f i = 1 :=
  finprod_of_infinite_mulSupport <| Set.not_finite.mp hf

@[to_additive]
theorem hasFiniteMulSupport_of_finprod_ne_one {f : α → M} (h : ∏ᶠ i, f i ≠ 1) :
    HasFiniteMulSupport f :=
  not_infinite.mp <| (finprod_of_infinite_mulSupport ·).mt h

@[deprecated (since := "2026-03-03")] alias
  finite_mulSupport_of_finprod_ne_one := hasFiniteMulSupport_of_finprod_ne_one

@[deprecated (since := "2026-03-03")] alias
  finite_support_of_finsum_ne_zero := hasFiniteSupport_of_finsum_ne_zero

theorem hasFiniteSupport_of_finsum_eq_one {R : Type*} [NonAssocSemiring R] {f : α → R}
    (h : ∑ᶠ i, f i = 1) : HasFiniteSupport f := by
  cases subsingleton_or_nontrivial R
  · simp_rw [HasFiniteSupport, Subsingleton.support_eq, finite_empty]
  · apply hasFiniteSupport_of_finsum_ne_zero
    rw [h]
    exact one_ne_zero

@[deprecated (since := "2026-03-03")] alias
  finite_support_of_finsum_eq_one := hasFiniteSupport_of_finsum_eq_one

@[to_additive]
theorem finprod_eq_prod (f : α → M) (hf : HasFiniteMulSupport f) :
    ∏ᶠ i : α, f i = ∏ i ∈ hf.toFinset, f i := by classical rw [finprod_def, dif_pos hf]

@[to_additive]
theorem finprod_eq_prod_of_fintype [Fintype α] (f : α → M) : ∏ᶠ i : α, f i = ∏ i, f i :=
  finprod_eq_prod_of_mulSupport_toFinset_subset _ (Set.toFinite _) <| Finset.subset_univ _

theorem finprod_ne_zero {M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
    {f : α → M₀} (h : ∀ i, f i ≠ 0) :
    ∏ᶠ i, f i ≠ 0 := by
  by_cases h₂ : Set.Finite f.mulSupport
  · grind [finprod_eq_prod f h₂, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

@[to_additive]
theorem map_finsetProd {α F : Type*} [Fintype α] [EquivLike F M N] [MulEquivClass F M N] (f : F)
    (g : α → M) : f (∏ i : α, g i) = ∏ i : α, f (g i) := by
  simp [← finprod_eq_prod_of_fintype, MulEquivClass.map_finprod]

@[deprecated (since := "2026-04-08")] alias map_finset_sum := map_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias map_finset_prod := map_finsetProd

@[to_additive]
theorem finprod_cond_eq_prod_of_cond_iff (f : α → M) {p : α → Prop} {t : Finset α}
    (h : ∀ {x}, f x ≠ 1 → (p x ↔ x ∈ t)) : (∏ᶠ (i) (_ : p i), f i) = ∏ i ∈ t, f i := by
  set s := { x | p x }
  change ∏ᶠ (i : α) (_ : i ∈ s), f i = ∏ i ∈ t, f i
  have : mulSupport (s.mulIndicator f) ⊆ t := by
    rw [Set.mulSupport_mulIndicator]
    intro x hx
    exact (h hx.2).1 hx.1
  rw [finprod_mem_def, finprod_eq_prod_of_mulSupport_subset _ this]
  refine Finset.prod_congr rfl fun x hx => mulIndicator_apply_eq_self.2 fun hxs => ?_
  contrapose! hxs
  exact (h hxs).2 hx

@[to_additive]
theorem finprod_cond_ne (f : α → M) (a : α) [DecidableEq α] (hf : HasFiniteMulSupport f) :
    (∏ᶠ (i) (_ : i ≠ a), f i) = ∏ i ∈ hf.toFinset.erase a, f i := by
  apply finprod_cond_eq_prod_of_cond_iff
  intro x hx
  rw [Finset.mem_erase, Finite.mem_toFinset, mem_mulSupport]
  grind

@[to_additive]
theorem finprod_mem_eq_prod_of_inter_mulSupport_eq (f : α → M) {s : Set α} {t : Finset α}
    (h : s ∩ mulSupport f = ↑t ∩ mulSupport f) : ∏ᶠ i ∈ s, f i = ∏ i ∈ t, f i :=
  finprod_cond_eq_prod_of_cond_iff _ <| by
    intro x hxf
    rw [← mem_mulSupport] at hxf
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · refine ((mem_inter_iff x t (mulSupport f)).mp ?_).1
      rw [← Set.ext_iff.mp h x, mem_inter_iff]
      exact ⟨hx, hxf⟩
    · refine ((mem_inter_iff x s (mulSupport f)).mp ?_).1
      rw [Set.ext_iff.mp h x, mem_inter_iff]
      exact ⟨hx, hxf⟩

@[to_additive]
theorem finprod_mem_eq_prod_of_subset (f : α → M) {s : Set α} {t : Finset α}
    (h₁ : s ∩ mulSupport f ⊆ t) (h₂ : ↑t ⊆ s) : ∏ᶠ i ∈ s, f i = ∏ i ∈ t, f i :=
  finprod_cond_eq_prod_of_cond_iff _ fun hx => ⟨fun h => h₁ ⟨h, hx⟩, fun h => h₂ h⟩

@[to_additive]
theorem finprod_mem_eq_prod (f : α → M) {s : Set α} (hf : (s ∩ mulSupport f).Finite) :
    ∏ᶠ i ∈ s, f i = ∏ i ∈ hf.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by simp [inter_assoc]

@[to_additive]
theorem finprod_mem_eq_prod_filter (f : α → M) (s : Set α) [DecidablePred (· ∈ s)]
    (hf : HasFiniteMulSupport f) :
    ∏ᶠ i ∈ s, f i = ∏ i ∈ hf.toFinset with i ∈ s, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by
    ext x
    simp [and_comm]

@[to_additive]
theorem finprod_mem_eq_toFinset_prod (f : α → M) (s : Set α) [Fintype s] :
    ∏ᶠ i ∈ s, f i = ∏ i ∈ s.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by simp_rw [coe_toFinset s]

@[to_additive]
theorem finprod_mem_eq_finite_toFinset_prod (f : α → M) {s : Set α} (hs : s.Finite) :
    ∏ᶠ i ∈ s, f i = ∏ i ∈ hs.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by rw [hs.coe_toFinset]

@[to_additive]
theorem finprod_mem_finset_eq_prod (f : α → M) (s : Finset α) : ∏ᶠ i ∈ s, f i = ∏ i ∈ s, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl

@[to_additive]
theorem finprod_mem_coe_finset (f : α → M) (s : Finset α) :
    (∏ᶠ i ∈ (s : Set α), f i) = ∏ i ∈ s, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl

@[to_additive]
theorem finprod_mem_eq_one_of_infinite {f : α → M} {s : Set α} (hs : (s ∩ mulSupport f).Infinite) :
    ∏ᶠ i ∈ s, f i = 1 := by
  rw [finprod_mem_def]
  apply finprod_of_infinite_mulSupport
  rwa [← mulSupport_mulIndicator] at hs

@[to_additive]
theorem finprod_mem_eq_one_of_forall_eq_one {f : α → M} {s : Set α} (h : ∀ x ∈ s, f x = 1) :
    ∏ᶠ i ∈ s, f i = 1 := by simp +contextual [h]

@[to_additive]
theorem finprod_mem_inter_mulSupport (f : α → M) (s : Set α) :
    ∏ᶠ i ∈ s ∩ mulSupport f, f i = ∏ᶠ i ∈ s, f i := by
  rw [finprod_mem_def, finprod_mem_def, mulIndicator_inter_mulSupport]

@[to_additive]
theorem finprod_mem_inter_mulSupport_eq (f : α → M) (s t : Set α)
    (h : s ∩ mulSupport f = t ∩ mulSupport f) : ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mulSupport, h, finprod_mem_inter_mulSupport]

@[to_additive]
theorem finprod_mem_inter_mulSupport_eq' (f : α → M) (s t : Set α)
    (h : ∀ x ∈ mulSupport f, x ∈ s ↔ x ∈ t) : ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, f i := by
  apply finprod_mem_inter_mulSupport_eq
  ext x
  exact and_congr_left (h x)

@[to_additive]
theorem finprod_mem_univ (f : α → M) : ∏ᶠ i ∈ @Set.univ α, f i = ∏ᶠ i : α, f i :=
  finprod_congr fun _ => finprod_true _

variable {f g : α → M} {a b : α} {s t : Set α}

@[to_additive]
theorem finprod_mem_congr (h₀ : s = t) (h₁ : ∀ x ∈ t, f x = g x) :
    ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, g i :=
  h₀.symm ▸ finprod_congr fun i => finprod_congr_Prop rfl (h₁ i)

@[to_additive]
theorem finprod_eq_one_of_forall_eq_one {f : α → M} (h : ∀ x, f x = 1) : ∏ᶠ i, f i = 1 := by
  simp +contextual [h]

@[to_additive finsum_cond_pos]
theorem one_lt_finprod_cond {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
    {f : ι → M} {p : ι → Prop} (h : ∀ i, p i → 1 ≤ f i) (h' : ∃ i, p i ∧ 1 < f i)
    (hf : (mulSupport f ∩ {i | p i}).Finite) : 1 < ∏ᶠ (i) (_ : p i), f i := by
  rw [finprod_cond_eq_prod_of_cond_iff (t := hf.toFinset)]
  · apply Finset.one_lt_prod'
    · simp +contextual [h]
    · aesop
  · simp +contextual

@[deprecated (since := "2026-01-06")] alias finprod_cond_pos := finsum_cond_pos

@[to_additive finsum_pos]
theorem one_lt_finprod {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
    {f : ι → M}
    (h : ∀ i, 1 ≤ f i) (h' : ∃ i, 1 < f i) (hf : HasFiniteMulSupport f) : 1 < ∏ᶠ i, f i := by
  rw [← finprod_mem_univ]
  apply one_lt_finprod_cond <;> simpa

@[deprecated (since := "2026-01-03")]
alias finsum_pos' := finsum_pos

@[to_additive existing finsum_pos', deprecated (since := "2026-01-03")]
alias one_lt_finprod' := one_lt_finprod

/-- Monotonicity of `finprod`. See `finprod_le_finprod₀` for a variant where
`M` is a `CommMonoidWithZero`. -/
@[to_additive /-- Monotonicity of `finsum.` -/]
lemma finprod_le_finprod [PartialOrder M] [MulLeftMono M] (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) (h : f ≤ g) :
    ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  have : Fintype ↑(f.mulSupport ∪ g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport ∪ g.mulSupport).toFinset
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (show f.mulSupport ⊆ s by grind),
    finprod_eq_finsetProd_of_mulSupport_subset g (show g.mulSupport ⊆ s by grind)]
  exact Finset.prod_le_prod fun i _ ↦ h i

@[deprecated (since := "2026-05-22")] alias finprod_le_finprod' := finprod_le_finprod

/-- Monotonicity of `finprod`. See `finprod_le_finprod` for a variant where
`M` is an ordered `CommMonoid`. -/
lemma finprod_le_finprod₀ {M : Type*} [CommMonoidWithZero M] [PartialOrder M] [ZeroLEOneClass M]
    [PosMulMono M] {f g : α → M} (hf : HasFiniteMulSupport f) (hf₀ : ∀ a, 0 ≤ f a)
    (hg : HasFiniteMulSupport g) (h : f ≤ g) :
    ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  have : Fintype ↑(f.mulSupport ∪ g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport ∪ g.mulSupport).toFinset
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (show f.mulSupport ⊆ s by grind),
    finprod_eq_finsetProd_of_mulSupport_subset g (show g.mulSupport ⊆ s by grind)]
  exact Finset.prod_le_prod₀ (fun i _ ↦ hf₀ i) fun i _ ↦ h i

lemma finprod_zero_le_one {M α : Type*} [CommMonoidWithZero M] [PartialOrder M]
    [ZeroLEOneClass M] [PosMulMono M] :
    ∏ᶠ _ : α, (0 : M) ≤ 1 := by
  rw [← finprod_one (α := α)]
  by_cases H : (fun _ : α ↦ (0 : M)).HasFiniteMulSupport
  · exact finprod_le_finprod₀ H (fun _ ↦ le_rfl) (by fun_prop) fun _ ↦ zero_le_one
  · rw [finprod_of_not_hasFiniteMulSupport H]
    exact finprod_one.symm.le

/-!
### Distributivity w.r.t. addition, subtraction, and (scalar) multiplication
-/


/-- If the multiplicative supports of `f` and `g` are finite, then the product of `f i * g i` equals
the product of `f i` multiplied by the product of `g i`. -/
@[to_additive
      /-- If the additive supports of `f` and `g` are finite, then the sum of `f i + g i`
      equals the sum of `f i` plus the sum of `g i`. -/]
theorem finprod_mul_distrib (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    ∏ᶠ i, f i * g i = (∏ᶠ i, f i) * ∏ᶠ i, g i := by
  classical
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf Finset.subset_union_left,
      finprod_eq_prod_of_mulSupport_toFinset_subset g hg Finset.subset_union_right, ←
      Finset.prod_mul_distrib]
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    simp only [Finset.coe_union, Finite.coe_toFinset, mulSupport_subset_iff,
      mem_union, mem_mulSupport]
    intro x
    contrapose!
    rintro ⟨hf, hg⟩
    simp [hf, hg]

/-- If the multiplicative supports of `f` and `g` are finite, then the product of `f i / g i`
equals the product of `f i` divided by the product of `g i`. -/
@[to_additive
      /-- If the additive supports of `f` and `g` are finite, then the sum of `f i - g i`
      equals the sum of `f i` minus the sum of `g i`. -/]
theorem finprod_div_distrib [DivisionCommMonoid G] {f g : α → G} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) : ∏ᶠ i, f i / g i = (∏ᶠ i, f i) / ∏ᶠ i, g i := by
  simp only [div_eq_mul_inv, finprod_mul_distrib hf <| hg.fun_inv, finprod_inv_distrib]

/-- A more general version of `finprod_mem_mul_distrib` that only requires `s ∩ mulSupport f` and
`s ∩ mulSupport g` rather than `s` to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_add_distrib` that only requires `s ∩ support f`
      and `s ∩ support g` rather than `s` to be finite. -/]
theorem finprod_mem_mul_distrib' (hf : (s ∩ mulSupport f).Finite) (hg : (s ∩ mulSupport g).Finite) :
    ∏ᶠ i ∈ s, f i * g i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i := by
  rw [← mulSupport_mulIndicator] at hf hg
  simp only [finprod_mem_def, mulIndicator_mul, finprod_mul_distrib hf hg]

/-- The product of the constant function `1` over any set equals `1`. -/
@[to_additive /-- The sum of the constant function `0` over any set equals `0`. -/]
theorem finprod_mem_one (s : Set α) : (∏ᶠ i ∈ s, (1 : M)) = 1 := by simp

/-- If a function `f` equals `1` on a set `s`, then the product of `f i` over `i ∈ s` equals `1`. -/
@[to_additive
      /-- If a function `f` equals `0` on a set `s`, then the sum of `f i` over `i ∈ s`
      equals `0`. -/]
theorem finprod_mem_of_eqOn_one (hf : s.EqOn f 1) : ∏ᶠ i ∈ s, f i = 1 := by
  rw [← finprod_mem_one s]
  exact finprod_mem_congr rfl hf

/-- If the product of `f i` over `i ∈ s` is not equal to `1`, then there is some `x ∈ s` such that
`f x ≠ 1`. -/
@[to_additive
      /-- If the sum of `f i` over `i ∈ s` is not equal to `0`, then there is some `x ∈ s`
      such that `f x ≠ 0`. -/]
theorem exists_ne_one_of_finprod_mem_ne_one (h : ∏ᶠ i ∈ s, f i ≠ 1) : ∃ x ∈ s, f x ≠ 1 := by
  by_contra! h'
  exact h (finprod_mem_of_eqOn_one h')

/-- Given a finite set `s`, the product of `f i * g i` over `i ∈ s` equals the product of `f i`
over `i ∈ s` times the product of `g i` over `i ∈ s`. -/
@[to_additive
      /-- Given a finite set `s`, the sum of `f i + g i` over `i ∈ s` equals the sum of `f i`
      over `i ∈ s` plus the sum of `g i` over `i ∈ s`. -/]
theorem finprod_mem_mul_distrib (hs : s.Finite) :
    ∏ᶠ i ∈ s, f i * g i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i :=
  finprod_mem_mul_distrib' (hs.inter_of_left _) (hs.inter_of_left _)

@[to_additive]
theorem MonoidHom.map_finprod {f : α → M} (g : M →* N) (hf : HasFiniteMulSupport f) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.map_finprod_plift f <| hf.preimage Equiv.plift.injective.injOn

@[to_additive]
theorem map_finprod {G : Type*} [FunLike G M N] [MonoidHomClass G M N] (g : G)
    (hf : HasFiniteMulSupport f) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  (g : M →* N).map_finprod hf

@[to_additive]
theorem finprod_pow (hf : HasFiniteMulSupport f) (n : ℕ) : (∏ᶠ i, f i) ^ n = ∏ᶠ i, f i ^ n :=
  (powMonoidHom n).map_finprod hf

/-- See also `finsum_smul` for a version that works even when the support of `f` is not finite,
but with slightly stronger typeclass requirements. -/
theorem finsum_smul' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {f : ι → R}
    (hf : HasFiniteSupport f) (x : M) : (∑ᶠ i, f i) • x = ∑ᶠ i, f i • x :=
  ((smulAddHom R M).flip x).map_finsum hf

/-- See also `smul_finsum` for a version that works even when the support of `f` is not finite,
but with slightly stronger typeclass requirements. -/
theorem smul_finsum' {R M : Type*} [AddCommMonoid M] [DistribSMul R M] (c : R)
    {f : ι → M} (hf : HasFiniteSupport f) : (c • ∑ᶠ i, f i) = ∑ᶠ i, c • f i :=
  (DistribSMul.toAddMonoidHom M c).map_finsum hf

/-- A more general version of `MonoidHom.map_finprod_mem` that requires `s ∩ mulSupport f` rather
than `s` to be finite. -/
@[to_additive
      /-- A more general version of `AddMonoidHom.map_finsum_mem` that requires
      `s ∩ support f` rather than `s` to be finite. -/]
theorem MonoidHom.map_finprod_mem' {f : α → M} (g : M →* N) (h₀ : (s ∩ mulSupport f).Finite) :
    g (∏ᶠ j ∈ s, f j) = ∏ᶠ i ∈ s, g (f i) := by
  rw [g.map_finprod]
  · simp only [g.map_finprod_Prop]
  · simpa only [finprod_eq_mulIndicator_apply, HasFiniteMulSupport, mulSupport_mulIndicator]

/-- Given a monoid homomorphism `g : M →* N` and a function `f : α → M`, the value of `g` at the
product of `f i` over `i ∈ s` equals the product of `g (f i)` over `s`. -/
@[to_additive
      /-- Given an additive monoid homomorphism `g : M →* N` and a function `f : α → M`, the
      value of `g` at the sum of `f i` over `i ∈ s` equals the sum of `g (f i)` over `s`. -/]
theorem MonoidHom.map_finprod_mem (f : α → M) (g : M →* N) (hs : s.Finite) :
    g (∏ᶠ j ∈ s, f j) = ∏ᶠ i ∈ s, g (f i) :=
  g.map_finprod_mem' (hs.inter_of_left _)

@[to_additive]
theorem MulEquiv.map_finprod_mem (g : M ≃* N) (f : α → M) {s : Set α} (hs : s.Finite) :
    g (∏ᶠ i ∈ s, f i) = ∏ᶠ i ∈ s, g (f i) :=
  g.toMonoidHom.map_finprod_mem f hs

@[to_additive]
theorem finprod_mem_inv_distrib [DivisionCommMonoid G] (f : α → G) (hs : s.Finite) :
    (∏ᶠ x ∈ s, (f x)⁻¹) = (∏ᶠ x ∈ s, f x)⁻¹ :=
  ((MulEquiv.inv G).map_finprod_mem f hs).symm

/-- Given a finite set `s`, the product of `f i / g i` over `i ∈ s` equals the product of `f i`
over `i ∈ s` divided by the product of `g i` over `i ∈ s`. -/
@[to_additive
      /-- Given a finite set `s`, the sum of `f i / g i` over `i ∈ s` equals the sum of `f i`
      over `i ∈ s` minus the sum of `g i` over `i ∈ s`. -/]
theorem finprod_mem_div_distrib [DivisionCommMonoid G] (f g : α → G) (hs : s.Finite) :
    ∏ᶠ i ∈ s, f i / g i = (∏ᶠ i ∈ s, f i) / ∏ᶠ i ∈ s, g i := by
  simp only [div_eq_mul_inv, finprod_mem_mul_distrib hs, finprod_mem_inv_distrib g hs]

/-!
### `∏ᶠ x ∈ s, f x` and set operations
-/


/-- The product of any function over an empty set is `1`. -/
@[to_additive /-- The sum of any function over an empty set is `0`. -/]
theorem finprod_mem_empty : (∏ᶠ i ∈ (∅ : Set α), f i) = 1 := by simp

/-- A set `s` is nonempty if the product of some function over `s` is not equal to `1`. -/
@[to_additive
/-- A set `s` is nonempty if the sum of some function over `s` is not equal to `0`. -/]
theorem nonempty_of_finprod_mem_ne_one (h : ∏ᶠ i ∈ s, f i ≠ 1) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h' => h <| h'.symm ▸ finprod_mem_empty

/-- Given finite sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` times the product of
`f i` over `i ∈ s ∩ t` equals the product of `f i` over `i ∈ s` times the product of `f i`
over `i ∈ t`. -/
@[to_additive
      /-- Given finite sets `s` and `t`, the sum of `f i` over `i ∈ s ∪ t` plus the sum of
      `f i` over `i ∈ s ∩ t` equals the sum of `f i` over `i ∈ s` plus the sum of `f i`
      over `i ∈ t`. -/]
theorem finprod_mem_union_inter (hs : s.Finite) (ht : t.Finite) :
    ((∏ᶠ i ∈ s ∪ t, f i) * ∏ᶠ i ∈ s ∩ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  lift s to Finset α using hs; lift t to Finset α using ht
  classical
    rw [← Finset.coe_union, ← Finset.coe_inter]
    simp only [finprod_mem_coe_finset, Finset.prod_union_inter]

/-- A more general version of `finprod_mem_union_inter` that requires `s ∩ mulSupport f` and
`t ∩ mulSupport f` rather than `s` and `t` to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_union_inter` that requires `s ∩ support f` and
      `t ∩ support f` rather than `s` and `t` to be finite. -/]
theorem finprod_mem_union_inter' (hs : (s ∩ mulSupport f).Finite) (ht : (t ∩ mulSupport f).Finite) :
    ((∏ᶠ i ∈ s ∪ t, f i) * ∏ᶠ i ∈ s ∩ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mulSupport f s, ← finprod_mem_inter_mulSupport f t, ←
    finprod_mem_union_inter hs ht, ← union_inter_distrib_right, finprod_mem_inter_mulSupport, ←
    finprod_mem_inter_mulSupport f (s ∩ t)]
  rw [inter_left_comm, inter_assoc, inter_assoc, inter_self, inter_left_comm]

/-- A more general version of `finprod_mem_union` that requires `s ∩ mulSupport f` and
`t ∩ mulSupport f` rather than `s` and `t` to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_union` that requires `s ∩ support f` and
      `t ∩ support f` rather than `s` and `t` to be finite. -/]
theorem finprod_mem_union' (hst : Disjoint s t) (hs : (s ∩ mulSupport f).Finite)
    (ht : (t ∩ mulSupport f).Finite) : ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_union_inter' hs ht, disjoint_iff_inter_eq_empty.1 hst, finprod_mem_empty,
    mul_one]

/-- Given two finite disjoint sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` equals the
product of `f i` over `i ∈ s` times the product of `f i` over `i ∈ t`. -/
@[to_additive
      /-- Given two finite disjoint sets `s` and `t`, the sum of `f i` over `i ∈ s ∪ t` equals
      the sum of `f i` over `i ∈ s` plus the sum of `f i` over `i ∈ t`. -/]
theorem finprod_mem_union (hst : Disjoint s t) (hs : s.Finite) (ht : t.Finite) :
    ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
  finprod_mem_union' hst (hs.inter_of_left _) (ht.inter_of_left _)

/-- A more general version of `finprod_mem_union'` that requires `s ∩ mulSupport f` and
`t ∩ mulSupport f` rather than `s` and `t` to be disjoint -/
@[to_additive
      /-- A more general version of `finsum_mem_union'` that requires `s ∩ support f` and
      `t ∩ support f` rather than `s` and `t` to be disjoint -/]
theorem finprod_mem_union'' (hst : Disjoint (s ∩ mulSupport f) (t ∩ mulSupport f))
    (hs : (s ∩ mulSupport f).Finite) (ht : (t ∩ mulSupport f).Finite) :
    ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mulSupport f s, ← finprod_mem_inter_mulSupport f t, ←
    finprod_mem_union hst hs ht, ← union_inter_distrib_right, finprod_mem_inter_mulSupport]

/-- The product of `f i` over `i ∈ {a}` equals `f a`. -/
@[to_additive /-- The sum of `f i` over `i ∈ {a}` equals `f a`. -/]
theorem finprod_mem_singleton : (∏ᶠ i ∈ ({a} : Set α), f i) = f a := by
  rw [← Finset.coe_singleton, finprod_mem_coe_finset, Finset.prod_singleton]

@[to_additive (attr := simp)]
theorem finprod_cond_eq_left : (∏ᶠ (i) (_ : i = a), f i) = f a :=
  finprod_mem_singleton

@[to_additive (attr := simp)]
theorem finprod_cond_eq_right : (∏ᶠ (i) (_ : a = i), f i) = f a := by simp [@eq_comm _ a]

/-- A more general version of `finprod_mem_insert` that requires `s ∩ mulSupport f` rather than `s`
to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_insert` that requires `s ∩ support f` rather
      than `s` to be finite. -/]
theorem finprod_mem_insert' (f : α → M) (h : a ∉ s) (hs : (s ∩ mulSupport f).Finite) :
    ∏ᶠ i ∈ insert a s, f i = f a * ∏ᶠ i ∈ s, f i := by
  rw [insert_eq, finprod_mem_union' _ _ hs, finprod_mem_singleton]
  · rwa [disjoint_singleton_left]
  · exact (finite_singleton a).inter_of_left _

/-- Given a finite set `s` and an element `a ∉ s`, the product of `f i` over `i ∈ insert a s` equals
`f a` times the product of `f i` over `i ∈ s`. -/
@[to_additive
      /-- Given a finite set `s` and an element `a ∉ s`, the sum of `f i` over `i ∈ insert a s`
      equals `f a` plus the sum of `f i` over `i ∈ s`. -/]
theorem finprod_mem_insert (f : α → M) (h : a ∉ s) (hs : s.Finite) :
    ∏ᶠ i ∈ insert a s, f i = f a * ∏ᶠ i ∈ s, f i :=
  finprod_mem_insert' f h <| hs.inter_of_left _

/-- If `f a = 1` when `a ∉ s`, then the product of `f i` over `i ∈ insert a s` equals the product of
`f i` over `i ∈ s`. -/
@[to_additive
      /-- If `f a = 0` when `a ∉ s`, then the sum of `f i` over `i ∈ insert a s` equals the sum
      of `f i` over `i ∈ s`. -/]
theorem finprod_mem_insert_of_eq_one_if_notMem (h : a ∉ s → f a = 1) :
    ∏ᶠ i ∈ insert a s, f i = ∏ᶠ i ∈ s, f i := by
  refine finprod_mem_inter_mulSupport_eq' _ _ _ fun x hx => ⟨?_, Or.inr⟩
  rintro (rfl | hxs)
  exacts [not_imp_comm.1 h hx, hxs]

/-- If `f a = 1`, then the product of `f i` over `i ∈ insert a s` equals the product of `f i` over
`i ∈ s`. -/
@[to_additive
      /-- If `f a = 0`, then the sum of `f i` over `i ∈ insert a s` equals the sum of `f i`
      over `i ∈ s`. -/]
theorem finprod_mem_insert_one (h : f a = 1) : ∏ᶠ i ∈ insert a s, f i = ∏ᶠ i ∈ s, f i :=
  finprod_mem_insert_of_eq_one_if_notMem fun _ => h

/-- If the multiplicative support of `f` is finite, then for every `x` in the domain of `f`, `f x`
divides `finprod f`. -/
theorem finprod_mem_dvd {f : α → N} (a : α) (hf : HasFiniteMulSupport f) : f a ∣ finprod f := by
  by_cases ha : a ∈ mulSupport f
  · rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf (Set.Subset.refl _)]
    exact Finset.dvd_prod_of_mem f ((Finite.mem_toFinset hf).mpr ha)
  · rw [notMem_mulSupport.mp ha]
    exact one_dvd (finprod f)

/-- The product of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a * f b`. -/
@[to_additive /-- The sum of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a + f b`. -/]
theorem finprod_mem_pair (h : a ≠ b) : (∏ᶠ i ∈ ({a, b} : Set α), f i) = f a * f b := by
  rw [finprod_mem_insert, finprod_mem_singleton]
  exacts [h, finite_singleton b]

set_option backward.isDefEq.respectTransparency false in
/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s`
provided that `g` is injective on `s ∩ mulSupport (f ∘ g)`. -/
@[to_additive
      /-- The sum of `f y` over `y ∈ g '' s` equals the sum of `f (g i)` over `s` provided that
      `g` is injective on `s ∩ support (f ∘ g)`. -/]
theorem finprod_mem_image' {s : Set β} {g : β → α} (hg : (s ∩ mulSupport (f ∘ g)).InjOn g) :
    ∏ᶠ i ∈ g '' s, f i = ∏ᶠ j ∈ s, f (g j) := by
  classical
    by_cases hs : (s ∩ mulSupport (f ∘ g)).Finite
    · have hg : ∀ x ∈ hs.toFinset, ∀ y ∈ hs.toFinset, g x = g y → x = y := by
        simpa only [hs.mem_toFinset]
      have := finprod_mem_eq_prod (comp f g) hs
      unfold Function.comp at this
      rw [this, ← Finset.prod_image hg]
      refine finprod_mem_eq_prod_of_inter_mulSupport_eq f ?_
      rw [Finset.coe_image, hs.coe_toFinset, ← image_inter_mulSupport_eq, inter_assoc, inter_self]
    · unfold Function.comp at hs
      rw [finprod_mem_eq_one_of_infinite hs, finprod_mem_eq_one_of_infinite]
      rwa [image_inter_mulSupport_eq, infinite_image_iff hg]

/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s` provided that
`g` is injective on `s`. -/
@[to_additive
      /-- The sum of `f y` over `y ∈ g '' s` equals the sum of `f (g i)` over `s` provided that
      `g` is injective on `s`. -/]
theorem finprod_mem_image {s : Set β} {g : β → α} (hg : s.InjOn g) :
    ∏ᶠ i ∈ g '' s, f i = ∏ᶠ j ∈ s, f (g j) :=
  finprod_mem_image' <| hg.mono inter_subset_left

/-- The product of `f y` over `y ∈ Set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective on `mulSupport (f ∘ g)`. -/
@[to_additive
      /-- The sum of `f y` over `y ∈ Set.range g` equals the sum of `f (g i)` over all `i`
      provided that `g` is injective on `support (f ∘ g)`. -/]
theorem finprod_mem_range' {g : β → α} (hg : (mulSupport (f ∘ g)).InjOn g) :
    ∏ᶠ i ∈ range g, f i = ∏ᶠ j, f (g j) := by
  rw [← image_univ, finprod_mem_image', finprod_mem_univ]
  rwa [univ_inter]

/-- The product of `f y` over `y ∈ Set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective. -/
@[to_additive
      /-- The sum of `f y` over `y ∈ Set.range g` equals the sum of `f (g i)` over all `i`
      provided that `g` is injective. -/]
theorem finprod_mem_range {g : β → α} (hg : Injective g) : ∏ᶠ i ∈ range g, f i = ∏ᶠ j, f (g j) :=
  finprod_mem_range' hg.injOn

/-- See also `Finset.prod_bij`. -/
@[to_additive /-- See also `Finset.sum_bij`. -/]
theorem finprod_mem_eq_of_bijOn {s : Set α} {t : Set β} {f : α → M} {g : β → M} (e : α → β)
    (he₀ : s.BijOn e t) (he₁ : ∀ x ∈ s, f x = g (e x)) : ∏ᶠ i ∈ s, f i = ∏ᶠ j ∈ t, g j := by
  rw [← Set.BijOn.image_eq he₀, finprod_mem_image he₀.2.1]
  exact finprod_mem_congr rfl he₁

/-- See `finprod_comp`, `Fintype.prod_bijective` and `Finset.prod_bij`. -/
@[to_additive /-- See `finsum_comp`, `Fintype.sum_bijective` and `Finset.sum_bij`. -/]
theorem finprod_eq_of_bijective {f : α → M} {g : β → M} (e : α → β) (he₀ : Bijective e)
    (he₁ : ∀ x, f x = g (e x)) : ∏ᶠ i, f i = ∏ᶠ j, g j := by
  rw [← finprod_mem_univ f, ← finprod_mem_univ g]
  exact finprod_mem_eq_of_bijOn _ he₀.bijOn_univ fun x _ => he₁ x

/-- See also `finprod_eq_of_bijective`, `Fintype.prod_bijective` and `Finset.prod_bij`. -/
@[to_additive
/-- See also `finsum_eq_of_bijective`, `Fintype.sum_bijective` and `Finset.sum_bij`. -/]
theorem finprod_comp {g : β → M} (e : α → β) (he₀ : Function.Bijective e) :
    (∏ᶠ i, g (e i)) = ∏ᶠ j, g j :=
  finprod_eq_of_bijective e he₀ fun _ => rfl

@[to_additive]
theorem finprod_comp_equiv (e : α ≃ β) {f : β → M} : (∏ᶠ i, f (e i)) = ∏ᶠ i', f i' :=
  finprod_comp e e.bijective

@[to_additive]
theorem finprod_set_coe_eq_finprod_mem (s : Set α) : ∏ᶠ j : s, f j = ∏ᶠ i ∈ s, f i := by
  rw [← finprod_mem_range, Subtype.range_coe]
  exact Subtype.coe_injective

@[to_additive]
theorem finprod_subtype_eq_finprod_cond (p : α → Prop) :
    ∏ᶠ j : Subtype p, f j = ∏ᶠ (i) (_ : p i), f i :=
  finprod_set_coe_eq_finprod_mem { i | p i }

@[to_additive]
theorem finprod_mem_inter_mul_diff' (t : Set α) (h : (s ∩ mulSupport f).Finite) :
    ((∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i) = ∏ᶠ i ∈ s, f i := by
  rw [← finprod_mem_union', inter_union_diff]
  · rw [disjoint_iff_inf_le]
    exact fun x hx => hx.2.2 hx.1.2
  exacts [h.subset fun x hx => ⟨hx.1.1, hx.2⟩, h.subset fun x hx => ⟨hx.1.1, hx.2⟩]

@[to_additive]
theorem finprod_mem_inter_mul_diff (t : Set α) (h : s.Finite) :
    ((∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i) = ∏ᶠ i ∈ s, f i :=
  finprod_mem_inter_mul_diff' _ <| h.inter_of_left _

/-- A more general version of `finprod_mem_mul_diff` that requires `t ∩ mulSupport f` rather than
`t` to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_add_diff` that requires `t ∩ support f` rather
      than `t` to be finite. -/]
theorem finprod_mem_mul_diff' (hst : s ⊆ t) (ht : (t ∩ mulSupport f).Finite) :
    ((∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i) = ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mul_diff' _ ht, inter_eq_self_of_subset_right hst]

/-- Given a finite set `t` and a subset `s` of `t`, the product of `f i` over `i ∈ s`
times the product of `f i` over `t \ s` equals the product of `f i` over `i ∈ t`. -/
@[to_additive
      /-- Given a finite set `t` and a subset `s` of `t`, the sum of `f i` over `i ∈ s` plus
      the sum of `f i` over `t \ s` equals the sum of `f i` over `i ∈ t`. -/]
theorem finprod_mem_mul_diff (hst : s ⊆ t) (ht : t.Finite) :
    ((∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i) = ∏ᶠ i ∈ t, f i :=
  finprod_mem_mul_diff' hst (ht.inter_of_left _)

/-- Given a family of pairwise disjoint finite sets `t i` indexed by a finite type, the product of
`f a` over the union `⋃ i, t i` is equal to the product over all indexes `i` of the products of
`f a` over `a ∈ t i`. -/
@[to_additive
      /-- Given a family of pairwise disjoint finite sets `t i` indexed by a finite type, the
      sum of `f a` over the union `⋃ i, t i` is equal to the sum over all indexes `i` of the
      sums of `f a` over `a ∈ t i`. -/]
theorem finprod_mem_iUnion [Finite ι] {t : ι → Set α} (h : Pairwise (Disjoint on t))
    (ht : ∀ i, (t i).Finite) : ∏ᶠ a ∈ ⋃ i : ι, t i, f a = ∏ᶠ i, ∏ᶠ a ∈ t i, f a := by
  cases nonempty_fintype ι
  lift t to ι → Finset α using ht
  classical
    rw [← biUnion_univ, ← Finset.coe_univ, ← Finset.coe_biUnion, finprod_mem_coe_finset,
      Finset.prod_biUnion]
    · simp only [finprod_mem_coe_finset, finprod_eq_prod_of_fintype]
    · exact fun x _ y _ hxy => Finset.disjoint_coe.1 (h hxy)

/-- Given a family of sets `t : ι → Set α`, a finite set `I` in the index type such that all sets
`t i`, `i ∈ I`, are finite, if all `t i`, `i ∈ I`, are pairwise disjoint, then the product of `f a`
over `a ∈ ⋃ i ∈ I, t i` is equal to the product over `i ∈ I` of the products of `f a` over
`a ∈ t i`. -/
@[to_additive
      /-- Given a family of sets `t : ι → Set α`, a finite set `I` in the index type such that
      all sets `t i`, `i ∈ I`, are finite, if all `t i`, `i ∈ I`, are pairwise disjoint, then the
      sum of `f a` over `a ∈ ⋃ i ∈ I, t i` is equal to the sum over `i ∈ I` of the sums of `f a`
      over `a ∈ t i`. -/]
theorem finprod_mem_biUnion {I : Set ι} {t : ι → Set α} (h : I.PairwiseDisjoint t) (hI : I.Finite)
    (ht : ∀ i ∈ I, (t i).Finite) : ∏ᶠ a ∈ ⋃ x ∈ I, t x, f a = ∏ᶠ i ∈ I, ∏ᶠ j ∈ t i, f j := by
  haveI := hI.fintype
  rw [biUnion_eq_iUnion, finprod_mem_iUnion, ← finprod_set_coe_eq_finprod_mem]
  exacts [fun x y hxy => h x.2 y.2 (Subtype.coe_injective.ne hxy), fun b => ht b b.2]

/-- If `t` is a finite set of pairwise disjoint finite sets, then the product of `f a`
over `a ∈ ⋃₀ t` is the product over `s ∈ t` of the products of `f a` over `a ∈ s`. -/
@[to_additive
      /-- If `t` is a finite set of pairwise disjoint finite sets, then the sum of `f a` over
      `a ∈ ⋃₀ t` is the sum over `s ∈ t` of the sums of `f a` over `a ∈ s`. -/]
theorem finprod_mem_sUnion {t : Set (Set α)} (h : t.PairwiseDisjoint id) (ht₀ : t.Finite)
    (ht₁ : ∀ x ∈ t, Set.Finite x) : ∏ᶠ a ∈ ⋃₀ t, f a = ∏ᶠ s ∈ t, ∏ᶠ a ∈ s, f a := by
  rw [Set.sUnion_eq_biUnion]
  exact finprod_mem_biUnion h ht₀ ht₁

@[to_additive]
lemma finprod_option {f : Option α → M} (hf : HasFiniteMulSupport (f ∘ some)) :
    ∏ᶠ o, f o = f none * ∏ᶠ a, f (some a) := by
  replace hf : (mulSupport f).Finite := by simpa [finite_option]
  convert!
    finprod_mem_insert' f (show none ∉ Set.range Option.some by simp) (hf.subset inter_subset_right)
  · simp
  · rw [finprod_mem_range]
    exact Option.some_injective _

@[to_additive]
lemma finprod_mem_powerset_insert {f : Set α → M} {s : Set α} {a : α} (hs : s.Finite)
    (has : a ∉ s) : ∏ᶠ t ∈ 𝒫 insert a s, f t = (∏ᶠ t ∈ 𝒫 s, f t) * ∏ᶠ t ∈ 𝒫 s, f (insert a t) := by
  rw [Set.powerset_insert,
    finprod_mem_union (disjoint_powerset_insert has) hs.powerset (hs.powerset.image (insert a)),
    finprod_mem_image (powerset_insert_injOn has)]

@[to_additive]
lemma finprod_mem_powerset_diff_elem {f : Set α → M} {s : Set α} {a : α} (hs : s.Finite)
    (has : a ∈ s) : ∏ᶠ t ∈ 𝒫 s, f t = (∏ᶠ t ∈ 𝒫 (s \ {a}), f t)
    * ∏ᶠ t ∈ 𝒫 (s \ {a}), f (insert a t) := by
  nth_rw 1 2 [← Set.insert_diff_self_of_mem has] -- second appearance hidden by notation
  exact finprod_mem_powerset_insert (hs.subset Set.diff_subset)
    (notMem_diff_of_mem (Set.mem_singleton a))

@[to_additive]
theorem mul_finprod_cond_ne (a : α) (hf : HasFiniteMulSupport f) :
    (f a * ∏ᶠ (i) (_ : i ≠ a), f i) = ∏ᶠ i, f i := by
  classical
    rw [finprod_eq_prod _ hf]
    have h : ∀ x : α, f x ≠ 1 → (x ≠ a ↔ x ∈ hf.toFinset \ {a}) := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_singleton, Finite.mem_toFinset, mem_mulSupport]
      grind
    rw [finprod_cond_eq_prod_of_cond_iff f (fun hx => h _ hx), Finset.sdiff_singleton_eq_erase]
    by_cases ha : a ∈ mulSupport f
    · apply Finset.mul_prod_erase _ _ ((Finite.mem_toFinset _).mpr ha)
    · rw [mem_mulSupport, not_not] at ha
      rw [ha, one_mul]
      apply Finset.prod_erase _ ha

/-- If `s : Set α` and `t : Set β` are finite sets, then taking the product over `s` commutes with
taking the product over `t`. -/
@[to_additive
      /-- If `s : Set α` and `t : Set β` are finite sets, then summing over `s` commutes with
      summing over `t`. -/]
theorem finprod_mem_comm {s : Set α} {t : Set β} (f : α → β → M) (hs : s.Finite) (ht : t.Finite) :
    (∏ᶠ i ∈ s, ∏ᶠ j ∈ t, f i j) = ∏ᶠ j ∈ t, ∏ᶠ i ∈ s, f i j := by
  lift s to Finset α using hs; lift t to Finset β using ht
  simp only [finprod_mem_coe_finset]
  exact Finset.prod_comm

/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on factors. -/
@[to_additive
      /-- To prove a property of a finite sum, it suffices to prove that the property is
      additive and holds on summands. -/]
theorem finprod_mem_induction (p : M → Prop) (hp₀ : p 1) (hp₁ : ∀ x y, p x → p y → p (x * y))
    (hp₂ : ∀ x ∈ s, p <| f x) : p (∏ᶠ i ∈ s, f i) :=
  finprod_induction _ hp₀ hp₁ fun x => finprod_induction _ hp₀ hp₁ <| hp₂ x

theorem finprod_cond_nonneg {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {p : α → Prop} {f : α → R}
    (hf : ∀ x, p x → 0 ≤ f x) : 0 ≤ ∏ᶠ (x) (_ : p x), f x :=
  finprod_nonneg fun x => finprod_nonneg <| hf x

@[to_additive]
theorem single_le_finprod {M : Type*} [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    (i : α) {f : α → M}
    (hf : HasFiniteMulSupport f) (h : ∀ j, 1 ≤ f j) : f i ≤ ∏ᶠ j, f j := by
  classical calc
      f i ≤ ∏ j ∈ insert i hf.toFinset, f j :=
        Finset.single_le_prod (fun j _ => h j) (Finset.mem_insert_self _ _)
      _ = ∏ᶠ j, f j :=
        (finprod_eq_prod_of_mulSupport_toFinset_subset _ hf (Finset.subset_insert _ _)).symm

theorem finprod_eq_zero {M₀ : Type*} [CommMonoidWithZero M₀] (f : α → M₀) (x : α) (hx : f x = 0)
    (hf : HasFiniteMulSupport f) : ∏ᶠ x, f x = 0 := by
  nontriviality
  rw [finprod_eq_prod f hf]
  refine Finset.prod_eq_zero (hf.mem_toFinset.2 ?_) hx
  simp [hx]

@[to_additive]
theorem finprod_prod_comm (s : Finset β) (f : α → β → M)
    (h : ∀ b ∈ s, HasFiniteMulSupport fun a ↦ f a b) :
    (∏ᶠ a : α, ∏ b ∈ s, f a b) = ∏ b ∈ s, ∏ᶠ a : α, f a b := by
  have hU :
    (mulSupport fun a => ∏ b ∈ s, f a b) ⊆
      (s.finite_toSet.biUnion fun b hb => h b (Finset.mem_coe.1 hb)).toFinset := by
    rw [Finite.coe_toFinset]
    intro x hx
    simp only [exists_prop, mem_iUnion, Ne, mem_mulSupport, Finset.mem_coe]
    contrapose! hx
    rw [mem_mulSupport, not_not, Finset.prod_congr rfl hx, Finset.prod_const_one]
  rw [finprod_eq_prod_of_mulSupport_subset _ hU, Finset.prod_comm]
  refine Finset.prod_congr rfl fun b hb => (finprod_eq_prod_of_mulSupport_subset _ ?_).symm
  intro a ha
  simp only [Finite.coe_toFinset, mem_iUnion]
  exact ⟨b, hb, ha⟩

@[to_additive]
theorem prod_finprod_comm (s : Finset α) (f : α → β → M) (h : ∀ a ∈ s, HasFiniteMulSupport (f a)) :
    (∏ a ∈ s, ∏ᶠ b : β, f a b) = ∏ᶠ b : β, ∏ a ∈ s, f a b :=
  (finprod_prod_comm s (fun b a => f a b) h).symm

@[to_additive]
theorem finprod_prod_filter [DecidableEq α] (f : β → α) (s : Finset β) (g : β → M) :
    ∏ᶠ x, ∏ y ∈ s with f y = x, g y = ∏ k ∈ s, g k := by
  rw [finprod_eq_finsetProd_of_mulSupport_subset]
  · rw [Finset.prod_image']
    exact fun _ _ ↦ rfl
  · intro x hx
    rw [mem_mulSupport] at hx
    obtain ⟨a, h, -⟩ := Finset.exists_ne_one_of_prod_ne_one hx
    simp only [Finset.mem_filter, Finset.coe_image, mem_image, SetLike.mem_coe] at h ⊢
    exact ⟨a, h⟩

/--
For functions with finite support, multiplication commutes with finsums. See `mul_finsum` for a
statement assuming that `R` has no zero divisors.
-/
theorem mul_finsum' {R : Type*} [NonUnitalNonAssocSemiring R] (f : α → R) (r : R)
    (h : HasFiniteSupport f) : (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a :=
  (AddMonoidHom.mulLeft r).map_finsum h

/--
For finite sets, multiplication commutes with `finsum_mem`. See `mul_finsum_mem'` for a statement
assuming finiteness of support.
-/
theorem mul_finsum_mem' {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set α} (f : α → R) (r : R)
    (hs : s.Finite) : (r * ∑ᶠ a ∈ s, f a) = ∑ᶠ a ∈ s, r * f a :=
  (AddMonoidHom.mulLeft r).map_finsum_mem f hs

/--
For functions with finite support, multiplication commutes with finsums. See `finsum_mul` for a
statement assuming that `R` has no zero divisors.
-/
theorem finsum_mul' {R : Type*} [NonUnitalNonAssocSemiring R] (f : α → R) (r : R)
    (h : HasFiniteSupport f) : (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r :=
  (AddMonoidHom.mulRight r).map_finsum h

/--
For finite sets, multiplication commutes with `finsum_mem`. See `finsum_mem_mul'` for a statement
assuming finiteness of support.
-/
theorem finsum_mem_mul' {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set α} (f : α → R) (r : R)
    (hs : s.Finite) : (∑ᶠ a ∈ s, f a) * r = ∑ᶠ a ∈ s, f a * r :=
  (AddMonoidHom.mulRight r).map_finsum_mem f hs

open Classical in
/--
If `R` has no zero divisors, then multiplication commutes with finsums. See `mul_finsum'` for a
statement assuming finiteness of support.
-/
theorem mul_finsum {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f : α → R)
    (r : R) :
    (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a := by
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact mul_finsum' f r h
  simp [finsum_def, HasFiniteSupport, h, (by aesop : (r * f ·).support = f.support)]

/--
If `R` has no zero divisors, then multiplication commutes with `finsum_mem`. See `mul_finsum_mem'`
for a statement assuming finiteness of support.
-/
theorem mul_finsum_mem {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] {s : Set α}
    (f : α → R) (r : R) :
    (r * ∑ᶠ a ∈ s, f a) = ∑ᶠ a ∈ s, r * f a := by
  rw [mul_finsum]
  congr
  ext a
  by_cases h : a ∈ s <;> simp_all

open Classical in
/--
If `R` has no zero divisors, then multiplication commutes with finsums. See `finsum_mul'` for a
statement assuming finiteness of support.
-/
theorem finsum_mul {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f : α → R)
    (r : R) :
    (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r := by
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact finsum_mul' f r h
  simp [finsum_def, HasFiniteSupport, h, (by aesop : (f · * r).support = f.support)]

/--
If `R` has no zero divisors, then multiplication commutes with `finsum_mem`. See `finsum_mem_mul'`
for a statement assuming finiteness of support.
-/
theorem finsum_mem_mul {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] {s : Set α}
    (f : α → R) (r : R) :
    (∑ᶠ a ∈ s, f a) * r = ∑ᶠ a ∈ s, f a * r := by
  rw [finsum_mul]
  congr
  ext a
  by_cases h : a ∈ s <;> simp_all

@[to_additive (attr := simp)]
lemma finprod_apply {α ι : Type*} {f : ι → α → N} (hf : HasFiniteMulSupport f) (a : α) :
    (∏ᶠ i, f i) a = ∏ᶠ i, f i a := by
  classical
  have hf' : HasFiniteMulSupport fun i ↦ f i a := by fun_prop (disch := simp)
  simp only [finprod_def, dif_pos, hf, hf', Finset.prod_apply]
  symm
  apply Finset.prod_subset <;> aesop

@[to_additive]
theorem Finset.mulSupport_of_fiberwise_prod_subset_image [DecidableEq β] (s : Finset α) (f : α → M)
    (g : α → β) : (mulSupport fun b ↦ ∏ a ∈ s with g a = b, f a) ⊆ s.image g := by
  simp only [Finset.coe_image]
  intro b h
  suffices {a ∈ s | g a = b}.Nonempty by
    simpa only [fiber_nonempty_iff_mem_image, Finset.mem_image, exists_prop]
  exact Finset.nonempty_of_prod_ne_one h

/-- Note that `b ∈ (s.filter (fun ab => Prod.fst ab = a)).image Prod.snd` iff `(a, b) ∈ s` so
we can simplify the right-hand side of this lemma. However the form stated here is more useful for
iterating this lemma, e.g., if we have `f : α × β × γ → M`. -/
@[to_additive
      /-- Note that `b ∈ (s.filter (fun ab => Prod.fst ab = a)).image Prod.snd` iff `(a, b) ∈ s` so
      we can simplify the right-hand side of this lemma. However the form stated here is more
      useful for iterating this lemma, e.g., if we have `f : α × β × γ → M`. -/]
theorem finprod_mem_finset_product' [DecidableEq α] [DecidableEq β] (s : Finset (α × β))
    (f : α × β → M) :
    (∏ᶠ (ab) (_ : ab ∈ s), f ab) =
      ∏ᶠ (a) (b) (_ : b ∈ (s.filter fun ab => Prod.fst ab = a).image Prod.snd), f (a, b) := by
  have (a : _) :
      ∏ i ∈ (s.filter fun ab => Prod.fst ab = a).image Prod.snd, f (a, i) =
        (s.filter (Prod.fst · = a)).prod f := by
    refine Finset.prod_nbij' (fun b ↦ (a, b)) Prod.snd ?_ ?_ ?_ ?_ ?_ <;> aesop
  rw [finprod_mem_finset_eq_prod]
  simp_rw [finprod_mem_finset_eq_prod, this]
  rw [finprod_eq_prod_of_mulSupport_subset _
      (s.mulSupport_of_fiberwise_prod_subset_image f Prod.fst),
    ← Finset.prod_fiberwise_of_maps_to (t := Finset.image Prod.fst s) _ f]
  -- `finish` could close the goal here
  simp only [Finset.mem_image]
  exact fun x hx => ⟨x, hx, rfl⟩

/-- See also `finprod_mem_finset_product'`. -/
@[to_additive /-- See also `finsum_mem_finset_product'`. -/]
theorem finprod_mem_finset_product (s : Finset (α × β)) (f : α × β → M) :
    (∏ᶠ (ab) (_ : ab ∈ s), f ab) = ∏ᶠ (a) (b) (_ : (a, b) ∈ s), f (a, b) := by
  classical
    rw [finprod_mem_finset_product']
    simp

@[to_additive]
theorem finprod_mem_finset_product₃ {γ : Type*} (s : Finset (α × β × γ)) (f : α × β × γ → M) :
    (∏ᶠ (abc) (_ : abc ∈ s), f abc) = ∏ᶠ (a) (b) (c) (_ : (a, b, c) ∈ s), f (a, b, c) := by
  classical
    rw [finprod_mem_finset_product']
    simp_rw [finprod_mem_finset_product']
    simp

@[to_additive]
theorem finprod_curry (f : α × β → M) (hf : HasFiniteMulSupport f) :
    ∏ᶠ ab, f ab = ∏ᶠ (a) (b), f (a, b) := by
  have h₁ : ∀ a, ∏ᶠ _ : a ∈ hf.toFinset, f a = f a := by simp
  have h₂ : ∏ᶠ a, f a = ∏ᶠ (a) (_ : a ∈ hf.toFinset), f a := by simp
  simp_rw [h₂, finprod_mem_finset_product, h₁]

@[to_additive]
theorem finprod_curry₃ {γ : Type*} (f : α × β × γ → M) (h : HasFiniteMulSupport f) :
    ∏ᶠ abc, f abc = ∏ᶠ (a) (b) (c), f (a, b, c) := by
  rw [finprod_curry f h]
  congr
  ext a
  rw [finprod_curry]
  simp [h]

@[to_additive]
theorem finprod_dmem {s : Set α} [DecidablePred (· ∈ s)] (f : ∀ a : α, a ∈ s → M) :
    (∏ᶠ (a : α) (h : a ∈ s), f a h) = ∏ᶠ (a : α) (_ : a ∈ s), if h' : a ∈ s then f a h' else 1 :=
  finprod_congr fun _ => finprod_congr fun ha => (dif_pos ha).symm

@[to_additive]
theorem finprod_emb_domain' {f : α → β} (hf : Injective f) [DecidablePred (· ∈ Set.range f)]
    (g : α → M) :
    (∏ᶠ b : β, if h : b ∈ Set.range f then g (Classical.choose h) else 1) = ∏ᶠ a : α, g a := by
  simp_rw [← finprod_eq_dif]
  rw [finprod_dmem, finprod_mem_range hf, finprod_congr fun a => _]
  intro a
  rw [dif_pos (Set.mem_range_self a), hf (Classical.choose_spec (Set.mem_range_self a))]

@[to_additive]
theorem finprod_emb_domain (f : α ↪ β) [DecidablePred (· ∈ Set.range f)] (g : α → M) :
    (∏ᶠ b : β, if h : b ∈ Set.range f then g (Classical.choose h) else 1) = ∏ᶠ a : α, g a :=
  finprod_emb_domain' f.injective g

@[simp, norm_cast]
lemma Nat.cast_finprod [Finite ι] {R : Type*} [CommSemiring R] (f : ι → ℕ) :
    ↑(∏ᶠ x, f x : ℕ) = ∏ᶠ x, (f x : R) :=
  (Nat.castRingHom R).map_finprod f.mulSupport.toFinite

/-- This version does not assume that `ι` is finite (compare `Nat.cast_finprod`), but instead needs
to assume characteristic zero to deal with the infinite case. -/
@[simp, norm_cast]
lemma Nat.cast_finprod' {R : Type*} [CommSemiring R] [CharZero R] (f : ι → ℕ) :
    (∏ᶠ (x : ι), f x : ℕ) = ∏ᶠ (x : ι), (f x : R) := by
  by_cases hf : f.HasFiniteMulSupport
  · exact map_finprod (Nat.castRingHom R) hf
  · have H : ¬ (fun i ↦ (f i : R)).HasFiniteMulSupport :=
      fun h ↦ hf <| h.of_comp cast_one cast_injective
    rw [finprod_of_not_hasFiniteMulSupport hf, finprod_of_not_hasFiniteMulSupport H, cast_one]

@[simp, norm_cast]
lemma Nat.cast_finprod_mem {s : Set ι} (hs : s.Finite) {R : Type*} [CommSemiring R] (f : ι → ℕ) :
    ↑(∏ᶠ x ∈ s, f x : ℕ) = ∏ᶠ x ∈ s, (f x : R) :=
  (Nat.castRingHom R).map_finprod_mem _ hs

@[simp, norm_cast]
lemma Nat.cast_finsum [Finite ι] {M : Type*} [AddCommMonoidWithOne M]
    (f : ι → ℕ) : ↑(∑ᶠ x, f x : ℕ) = ∑ᶠ x, (f x : M) :=
  (Nat.castAddMonoidHom M).map_finsum f.support.toFinite

@[simp, norm_cast]
lemma Nat.cast_finsum_mem {s : Set ι} (hs : s.Finite) {M : Type*}
    [AddCommMonoidWithOne M] (f : ι → ℕ) : ↑(∑ᶠ x ∈ s, f x : ℕ) = ∑ᶠ x ∈ s, (f x : M) :=
  (Nat.castAddMonoidHom M).map_finsum_mem _ hs

end type

/-!
### Some API for `fun a ↦ f a ^ count a s` on multisets
-/

namespace Multiset

variable {α M : Type*} [DecidableEq α] [CommMonoid M]

@[to_additive]
lemma mulSupport_fun_pow_count_subset (s : Multiset α) (f : α → M) :
    (fun a ↦ f a ^ count a s).mulSupport ⊆ s.toFinset := by
  simp +contextual [not_imp_comm]

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_fun_pow_count (s : Multiset α) (f : α → M) :
    (fun a ↦ (f a) ^ s.count a).HasFiniteMulSupport :=
  s.toFinset.finite_toSet.subset <| mulSupport_fun_pow_count_subset ..

@[to_additive]
lemma prod_map_eq_finprod (s : Multiset α) (f : α → M) :
    (s.map f).prod = ∏ᶠ a, f a ^ s.count a := by
  rw [Finset.prod_multiset_map_count, eq_comm]
  exact finprod_eq_prod_of_mulSupport_subset _ <| mulSupport_fun_pow_count_subset ..

end Multiset
