/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.SProd
import Mathlib.Data.Subtype
import Mathlib.Order.Notation

/-!
# Basic definitions about sets

In this file we define various operations on sets.
We also provide basic lemmas needed to unfold the definitions.
More advanced theorems about these definitions are located in other files in `Mathlib/Data/Set`.

## Main definitions

- complement of a set and set difference;
- `Set.preimage f s`, a.k.a. `f ⁻¹' s`: preimage of a set;
- `Set.range f`: the range of a function;
  it is more general than `f '' univ` because it allows functions from `Sort*`;
- `s ×ˢ t`: product of `s : Set α` and `t : Set β` as a set in `α × β`;
- `Set.diagonal`: the diagonal in `α × α`;
- `Set.offDiag s`: the part of `s ×ˢ s` that is off the diagonal;
- `Set.pi`: indexed product of a family of sets `∀ i, Set (α i)`,
  as a set in `∀ i, α i`;
- `Set.EqOn f g s`: the predicate saying that two functions are equal on a set;
- `Set.MapsTo f s t`: the predicate saying that `f` sends all points of `s` to `t`;
- `Set.MapsTo.restrict`: restrict `f : α → β` to `f' : s → t` provided that `Set.MapsTo f s t`;
- `Set.restrictPreimage`: restrict `f : α → β` to `f' : (f ⁻¹' t) → t`;
- `Set.InjOn`: the predicate saying that `f` is injective on a set;
- `Set.SurjOn f s t`: the prediate saying that `t ⊆ f '' s`;
- `Set.BijOn f s t`: the predicate saying that `f` is injective on `s` and `f '' s = t`;
- `Set.graphOn`: the graph of a function on a set;
- `Set.LeftInvOn`, `Set.RightInvOn`, `Set.InvOn`:
  the predicates saying that `f'` is a left, right or two-sided inverse of `f` on `s`, `t`, or both;
- `Set.image2`: the image of a pair of sets under a binary operation,
  mostly useful to define pointwise algebraic operations on sets;
- `Set.seq`: monadic `seq` operation on sets;
  we don't use monadic notation to ensure support for maps between different universes.

## Notation

- `f '' s`: image of a set;
- `f ⁻¹' s`: preimage of a set;
- `s ×ˢ t`: the product of sets;
- `s ∪ t`: the union of two sets;
- `s ∩ t`: the intersection of two sets;
- `sᶜ`: the complement of a set;
- `s \ t`: the difference of two sets.

## Keywords

set, image, preimage
-/

attribute [ext] Set.ext

universe u v w

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ### Lemmas about `mem` and `setOf` -/

@[simp, mfld_simps]
theorem mem_setOf_eq {x : α} {p : α → Prop} : (x ∈ {y | p y}) = p x := rfl

grind_pattern mem_setOf_eq => x ∈ setOf p

/-- This lemma is intended for use with `rw` where a membership predicate is needed,
hence the explicit argument and the equality in the reverse direction from normal.
See also `Set.mem_setOf_eq` for the reverse direction applied to an argument. -/
theorem eq_mem_setOf (p : α → Prop) : p = (· ∈ {a | p a}) := rfl

theorem mem_setOf {a : α} {p : α → Prop} : a ∈ { x | p x } ↔ p a := Iff.rfl

/-- If `h : a ∈ {x | p x}` then `h.out : p x`. These are definitionally equal, but this can
nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
argument to `simp`. -/
alias ⟨_root_.Membership.mem.out, _⟩ := mem_setOf

theorem notMem_setOf_iff {a : α} {p : α → Prop} : a ∉ { x | p x } ↔ ¬p a := Iff.rfl

@[deprecated (since := "2025-05-24")] alias nmem_setOf_iff := notMem_setOf_iff

@[simp] theorem setOf_mem_eq {s : Set α} : { x | x ∈ s } = s := rfl

@[simp, mfld_simps, grind]
theorem mem_univ (x : α) : x ∈ @univ α := trivial

/-! ### Operations -/

instance : HasCompl (Set α) := ⟨fun s ↦ {x | x ∉ s}⟩

@[simp, grind =]
theorem mem_compl_iff (s : Set α) (x : α) : x ∈ sᶜ ↔ x ∉ s := Iff.rfl

theorem diff_eq (s t : Set α) : s \ t = s ∩ tᶜ := rfl

@[simp, grind =]
theorem mem_diff {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := Iff.rfl

theorem mem_diff_of_mem {s t : Set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t := ⟨h1, h2⟩

/-- The preimage of `s : Set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}

/-- `f ⁻¹' t` denotes the preimage of `t : Set β` under the function `f : α → β`. -/
infixl:80 " ⁻¹' " => preimage

@[simp, mfld_simps, grind =]
theorem mem_preimage {f : α → β} {s : Set β} {a : α} : a ∈ f ⁻¹' s ↔ f a ∈ s := Iff.rfl

/-- `f '' s` denotes the image of `s : Set α` under the function `f : α → β`. -/
infixl:80 " '' " => image

@[simp, grind =]
theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f '' s ↔ ∃ x ∈ s, f x = y :=
  Iff.rfl

@[mfld_simps]
theorem mem_image_of_mem (f : α → β) {x : α} {a : Set α} (h : x ∈ a) : f x ∈ f '' a :=
  ⟨_, h, rfl⟩

/-- Restriction of `f` to `s` factors through `s.imageFactorization f : s → f '' s`. -/
def imageFactorization (f : α → β) (s : Set α) : s → f '' s := fun p =>
  ⟨f p.1, mem_image_of_mem f p.2⟩

/-- `kernImage f s` is the set of `y` such that `f ⁻¹ y ⊆ s`. -/
def kernImage (f : α → β) (s : Set α) : Set β := {y | ∀ ⦃x⦄, f x = y → x ∈ s}

lemma subset_kernImage_iff {s : Set β} {t : Set α} {f : α → β} : s ⊆ kernImage f t ↔ f ⁻¹' s ⊆ t :=
  ⟨fun h _ hx ↦ h hx rfl,
    fun h _ hx y hy ↦ h (show f y ∈ s from hy.symm ▸ hx)⟩

section Range

variable {ι : Sort*} {f : ι → α}

/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : Set α := {x | ∃ y, f y = x}

@[simp, grind =] theorem mem_range {x : α} : x ∈ range f ↔ ∃ y, f y = x := Iff.rfl

@[mfld_simps] theorem mem_range_self (i : ι) : f i ∈ range f := ⟨i, rfl⟩

/-- Any map `f : ι → α` factors through a map `rangeFactorization f : ι → range f`. -/
def rangeFactorization (f : ι → α) : ι → range f := fun i => ⟨f i, mem_range_self i⟩

end Range

/-- We can use the axiom of choice to pick a preimage for every element of `range f`. -/
noncomputable def rangeSplitting (f : α → β) : range f → α := fun x => x.2.choose

-- This cannot be a `@[simp]` lemma because the head of the left-hand side is a variable.
theorem apply_rangeSplitting (f : α → β) (x : range f) : f (rangeSplitting f x) = x :=
  x.2.choose_spec

@[simp]
theorem comp_rangeSplitting (f : α → β) : f ∘ rangeSplitting f = Subtype.val := by
  ext
  simp only [Function.comp_apply]
  apply apply_rangeSplitting

section Prod

/-- The Cartesian product `Set.prod s t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
def prod (s : Set α) (t : Set β) : Set (α × β) := {p | p.1 ∈ s ∧ p.2 ∈ t}

@[default_instance]
instance instSProd : SProd (Set α) (Set β) (Set (α × β)) where
  sprod := Set.prod

theorem prod_eq (s : Set α) (t : Set β) : s ×ˢ t = Prod.fst ⁻¹' s ∩ Prod.snd ⁻¹' t := rfl

variable {a : α} {b : β} {s : Set α} {t : Set β} {p : α × β}

theorem mem_prod_eq : (p ∈ s ×ˢ t) = (p.1 ∈ s ∧ p.2 ∈ t) := rfl

@[simp, mfld_simps, grind =]
theorem mem_prod : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t := .rfl

@[mfld_simps]
theorem prodMk_mem_set_prod_eq : ((a, b) ∈ s ×ˢ t) = (a ∈ s ∧ b ∈ t) :=
  rfl

theorem mk_mem_prod (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t := ⟨ha, hb⟩

end Prod

section Diagonal

/-- `diagonal α` is the set of `α × α` consisting of all pairs of the form `(a, a)`. -/
def diagonal (α : Type*) : Set (α × α) := {p | p.1 = p.2}

theorem mem_diagonal (x : α) : (x, x) ∈ diagonal α := rfl

@[simp, grind =] theorem mem_diagonal_iff {x : α × α} : x ∈ diagonal α ↔ x.1 = x.2 := .rfl

/-- The off-diagonal of a set `s` is the set of pairs `(a, b)` with `a, b ∈ s` and `a ≠ b`. -/
def offDiag (s : Set α) : Set (α × α) := {x | x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2}

@[simp, grind =]
theorem mem_offDiag {x : α × α} {s : Set α} : x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 :=
  Iff.rfl

end Diagonal

section Pi

variable {ι : Type*} {α : ι → Type*}

/-- Given an index set `ι` and a family of sets `t : Π i, Set (α i)`, `pi s t`
is the set of dependent functions `f : Πa, π a` such that `f i` belongs to `t i`
whenever `i ∈ s`. -/
def pi (s : Set ι) (t : ∀ i, Set (α i)) : Set (∀ i, α i) := {f | ∀ i ∈ s, f i ∈ t i}

variable {s : Set ι} {t : ∀ i, Set (α i)} {f : ∀ i, α i}

@[simp, grind =] theorem mem_pi : f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i := .rfl

theorem mem_univ_pi : f ∈ pi univ t ↔ ∀ i, f i ∈ t i := by simp

end Pi

/-- Two functions `f₁ f₂ : α → β` are equal on `s` if `f₁ x = f₂ x` for all `x ∈ s`. -/
def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x

/-- `MapsTo f s t` means that the image of `s` is contained in `t`. -/
def MapsTo (f : α → β) (s : Set α) (t : Set β) : Prop := ∀ ⦃x⦄, x ∈ s → f x ∈ t

theorem mapsTo_image (f : α → β) (s : Set α) : MapsTo f s (f '' s) := fun _ ↦ mem_image_of_mem f

theorem mapsTo_preimage (f : α → β) (t : Set β) : MapsTo f (f ⁻¹' t) t := fun _ ↦ id

/-- Given a map `f` sending `s : Set α` into `t : Set β`, restrict domain of `f` to `s`
and the codomain to `t`. Same as `Subtype.map`. -/
def MapsTo.restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) : s → t :=
  Subtype.map f h

/-- The restriction of a function onto the preimage of a set. -/
@[simps!]
def restrictPreimage (t : Set β) (f : α → β) : f ⁻¹' t → t :=
  (Set.mapsTo_preimage f t).restrict _ _ _

/-- `f` is injective on `s` if the restriction of `f` to `s` is injective. -/
def InjOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂

/-- The graph of a function `f : α → β` on a set `s`. -/
def graphOn (f : α → β) (s : Set α) : Set (α × β) := (fun x ↦ (x, f x)) '' s

/-- `f` is surjective from `s` to `t` if `t` is contained in the image of `s`. -/
def SurjOn (f : α → β) (s : Set α) (t : Set β) : Prop := t ⊆ f '' s

/-- `f` is bijective from `s` to `t` if `f` is injective on `s` and `f '' s = t`. -/
def BijOn (f : α → β) (s : Set α) (t : Set β) : Prop := MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t

/-- `g` is a left inverse to `f` on `s` means that `g (f x) = x` for all `x ∈ s`. -/
def LeftInvOn (g : β → α) (f : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → g (f x) = x

/-- `g` is a right inverse to `f` on `t` if `f (g x) = x` for all `x ∈ t`. -/
abbrev RightInvOn (g : β → α) (f : α → β) (t : Set β) : Prop := LeftInvOn f g t

/-- `g` is an inverse to `f` viewed as a map from `s` to `t` -/
def InvOn (g : β → α) (f : α → β) (s : Set α) (t : Set β) : Prop :=
  LeftInvOn g f s ∧ RightInvOn g f t

section image2

/-- The image of a binary function `f : α → β → γ` as a function `Set α → Set β → Set γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def image2 (f : α → β → γ) (s : Set α) (t : Set β) : Set γ := {c | ∃ a ∈ s, ∃ b ∈ t, f a b = c}

variable {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β} {c : γ}

@[simp, grind =] theorem mem_image2 : c ∈ image2 f s t ↔ ∃ a ∈ s, ∃ b ∈ t, f a b = c := .rfl

theorem mem_image2_of_mem (ha : a ∈ s) (hb : b ∈ t) : f a b ∈ image2 f s t :=
  ⟨a, ha, b, hb, rfl⟩

end image2

/-- Given a set `s` of functions `α → β` and `t : Set α`, `seq s t` is the union of `f '' t` over
all `f ∈ s`. -/
def seq (s : Set (α → β)) (t : Set α) : Set β := image2 (fun f ↦ f) s t

@[simp, grind =]
theorem mem_seq_iff {s : Set (α → β)} {t : Set α} {b : β} :
    b ∈ seq s t ↔ ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b :=
  Iff.rfl

lemma seq_eq_image2 (s : Set (α → β)) (t : Set α) : seq s t = image2 (fun f a ↦ f a) s t := rfl

end Set
