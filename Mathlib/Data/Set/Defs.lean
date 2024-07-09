/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Scott Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
import Mathlib.Data.SProd
import Mathlib.Data.Subtype
import Mathlib.Order.Notation
import Mathlib.Util.CompileInductive

/-!
# Basic definitions about sets

In this file we define various operations on sets.
We also provide basic lemmas needed to unfold the definitions.
More advanced theorems about these definitions are located in other files in `Mathlib/Data/Set`.

## Main definitions

- complement of a set and set difference;
- `Set.Elem`: coercion of a set to a type; it is reducibly equal to `{x // x ∈ s}`;
- `Set.preimage f s`, a.k.a. `f ⁻¹' s`: preimage of a set;
- `Set.range f`: the range of a function;
  it is more general than `f '' univ` because it allows functions from `Sort*`;
- `s ×ˢ t`: product of `s : Set α` and `t : Set β` as a set in `α × β`;
- `Set.diagonal`: the diagonal in `α × α`;
- `Set.offDiag s`: the part of `s ×ˢ s` that is off the diagonal;
- `Set.pi`: indexed product of a family of sets `∀ i, Set (α i)`,
  as a set in `∀ i, α i`;
- `Set.EqOn f g s`: the predicate saying that two functions are equal on a set;
- `Set.MapsTo f s t`: the predicate syaing that `f` sends all points of `s` to `t;
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
  we don't use monadic notation to ensure support for maps between different universes;

## Notations

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

-- https://github.com/leanprover/lean4/issues/2096
compile_def% Union.union
compile_def% Inter.inter
compile_def% SDiff.sdiff
compile_def% HasCompl.compl
compile_def% EmptyCollection.emptyCollection
compile_def% Insert.insert
compile_def% Singleton.singleton

attribute [ext] Set.ext
#align set.ext Set.ext

universe u v w

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

@[simp, mfld_simps] theorem mem_setOf_eq {x : α} {p : α → Prop} : (x ∈ {y | p y}) = p x := rfl
#align set.mem_set_of_eq Set.mem_setOf_eq

@[simp, mfld_simps] theorem mem_univ (x : α) : x ∈ @univ α := trivial
#align set.mem_univ Set.mem_univ

instance : HasCompl (Set α) := ⟨fun s ↦ {x | x ∉ s}⟩

@[simp] theorem mem_compl_iff (s : Set α) (x : α) : x ∈ sᶜ ↔ x ∉ s := Iff.rfl
#align set.mem_compl_iff Set.mem_compl_iff

theorem diff_eq (s t : Set α) : s \ t = s ∩ tᶜ := rfl
#align set.diff_eq Set.diff_eq

@[simp] theorem mem_diff {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := Iff.rfl
#align set.mem_diff Set.mem_diff

theorem mem_diff_of_mem {s t : Set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t := ⟨h1, h2⟩
#align set.mem_diff_of_mem Set.mem_diff_of_mem

-- Porting note: I've introduced this abbreviation, with the `@[coe]` attribute,
-- so that `norm_cast` has something to index on.
-- It is currently an abbreviation so that instance coming from `Subtype` are available.
-- If you're interested in making it a `def`, as it probably should be,
-- you'll then need to create additional instances (and possibly prove lemmas about them).
-- The first error should appear below at `monotoneOn_iff_monotone`.
/-- Given the set `s`, `Elem s` is the `Type` of element of `s`. -/
@[coe, reducible] def Elem (s : Set α) : Type u := {x // x ∈ s}

/-- Coercion from a set to the corresponding subtype. -/
instance : CoeSort (Set α) (Type u) := ⟨Elem⟩

/-- The preimage of `s : Set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}
#align set.preimage Set.preimage

/-- `f ⁻¹' t` denotes the preimage of `t : Set β` under the function `f : α → β`. -/
infixl:80 " ⁻¹' " => preimage

@[simp, mfld_simps]
theorem mem_preimage {f : α → β} {s : Set β} {a : α} : a ∈ f ⁻¹' s ↔ f a ∈ s := Iff.rfl
#align set.mem_preimage Set.mem_preimage

/-- `f '' s` denotes the image of `s : Set α` under the function `f : α → β`. -/
infixl:80 " '' " => image

@[simp]
theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f '' s ↔ ∃ x ∈ s, f x = y :=
  Iff.rfl
#align set.mem_image Set.mem_image

@[mfld_simps]
theorem mem_image_of_mem (f : α → β) {x : α} {a : Set α} (h : x ∈ a) : f x ∈ f '' a :=
  ⟨_, h, rfl⟩
#align set.mem_image_of_mem Set.mem_image_of_mem

/-- Restriction of `f` to `s` factors through `s.imageFactorization f : s → f '' s`. -/
def imageFactorization (f : α → β) (s : Set α) : s → f '' s := fun p =>
  ⟨f p.1, mem_image_of_mem f p.2⟩
#align set.image_factorization Set.imageFactorization

/-- `kernImage f s` is the set of `y` such that `f ⁻¹ y ⊆ s`. -/
def kernImage (f : α → β) (s : Set α) : Set β := {y | ∀ ⦃x⦄, f x = y → x ∈ s}
#align set.kern_image Set.kernImage

lemma subset_kernImage_iff {s : Set β} {t : Set α} {f : α → β} : s ⊆ kernImage f t ↔ f ⁻¹' s ⊆ t :=
  ⟨fun h _ hx ↦ h hx rfl,
    fun h _ hx y hy ↦ h (show f y ∈ s from hy.symm ▸ hx)⟩

section Range

variable {ι : Sort*} {f : ι → α}

/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : Set α := {x | ∃ y, f y = x}
#align set.range Set.range

@[simp] theorem mem_range {x : α} : x ∈ range f ↔ ∃ y, f y = x := Iff.rfl
#align set.mem_range Set.mem_range

@[mfld_simps] theorem mem_range_self (i : ι) : f i ∈ range f := ⟨i, rfl⟩
#align set.mem_range_self Set.mem_range_self

/-- Any map `f : ι → α` factors through a map `rangeFactorization f : ι → range f`. -/
def rangeFactorization (f : ι → α) : ι → range f := fun i => ⟨f i, mem_range_self i⟩
#align set.range_factorization Set.rangeFactorization

end Range

/-- We can use the axiom of choice to pick a preimage for every element of `range f`. -/
noncomputable def rangeSplitting (f : α → β) : range f → α := fun x => x.2.choose
#align set.range_splitting Set.rangeSplitting

-- This can not be a `@[simp]` lemma because the head of the left hand side is a variable.
theorem apply_rangeSplitting (f : α → β) (x : range f) : f (rangeSplitting f x) = x :=
  x.2.choose_spec
#align set.apply_range_splitting Set.apply_rangeSplitting

@[simp]
theorem comp_rangeSplitting (f : α → β) : f ∘ rangeSplitting f = Subtype.val := by
  ext
  simp only [Function.comp_apply]
  apply apply_rangeSplitting
#align set.comp_range_splitting Set.comp_rangeSplitting

section Prod

/-- The cartesian product `Set.prod s t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
def prod (s : Set α) (t : Set β) : Set (α × β) := {p | p.1 ∈ s ∧ p.2 ∈ t}
#align set.prod Set.prod

@[default_instance]
instance instSProd : SProd (Set α) (Set β) (Set (α × β)) where
  sprod := Set.prod

theorem prod_eq (s : Set α) (t : Set β) : s ×ˢ t = Prod.fst ⁻¹' s ∩ Prod.snd ⁻¹' t := rfl
#align set.prod_eq Set.prod_eq

variable {a : α} {b : β} {s : Set α} {t : Set β} {p : α × β}

theorem mem_prod_eq : (p ∈ s ×ˢ t) = (p.1 ∈ s ∧ p.2 ∈ t) := rfl
#align set.mem_prod_eq Set.mem_prod_eq

@[simp, mfld_simps]
theorem mem_prod : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t := .rfl
#align set.mem_prod Set.mem_prod

@[mfld_simps]
theorem prod_mk_mem_set_prod_eq : ((a, b) ∈ s ×ˢ t) = (a ∈ s ∧ b ∈ t) := rfl
#align set.prod_mk_mem_set_prod_eq Set.prod_mk_mem_set_prod_eq

theorem mk_mem_prod (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t := ⟨ha, hb⟩
#align set.mk_mem_prod Set.mk_mem_prod

end Prod

section Diagonal

/-- `diagonal α` is the set of `α × α` consisting of all pairs of the form `(a, a)`. -/
def diagonal (α : Type*) : Set (α × α) := {p | p.1 = p.2}
#align set.diagonal Set.diagonal

theorem mem_diagonal (x : α) : (x, x) ∈ diagonal α := rfl
#align set.mem_diagonal Set.mem_diagonal

@[simp] theorem mem_diagonal_iff {x : α × α} : x ∈ diagonal α ↔ x.1 = x.2 := .rfl
#align set.mem_diagonal_iff Set.mem_diagonal_iff

/-- The off-diagonal of a set `s` is the set of pairs `(a, b)` with `a, b ∈ s` and `a ≠ b`. -/
def offDiag (s : Set α) : Set (α × α) := {x | x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2}
#align set.off_diag Set.offDiag

@[simp]
theorem mem_offDiag {x : α × α} {s : Set α} : x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 :=
  Iff.rfl
#align set.mem_off_diag Set.mem_offDiag

end Diagonal

section Pi

variable {ι : Type*} {α : ι → Type*}

/-- Given an index set `ι` and a family of sets `t : Π i, Set (α i)`, `pi s t`
is the set of dependent functions `f : Πa, π a` such that `f a` belongs to `t a`
whenever `a ∈ s`. -/
def pi (s : Set ι) (t : ∀ i, Set (α i)) : Set (∀ i, α i) := {f | ∀ i ∈ s, f i ∈ t i}
#align set.pi Set.pi

variable {s : Set ι} {t : ∀ i, Set (α i)} {f : ∀ i, α i}

@[simp] theorem mem_pi : f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i := .rfl
#align set.mem_pi Set.mem_pi

theorem mem_univ_pi : f ∈ pi univ t ↔ ∀ i, f i ∈ t i := by simp
#align set.mem_univ_pi Set.mem_univ_pi

end Pi

/-- Two functions `f₁ f₂ : α → β` are equal on `s` if `f₁ x = f₂ x` for all `x ∈ s`. -/
def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x
#align set.eq_on Set.EqOn

/-- `MapsTo f a b` means that the image of `a` is contained in `b`. -/
def MapsTo (f : α → β) (s : Set α) (t : Set β) : Prop := ∀ ⦃x⦄, x ∈ s → f x ∈ t
#align set.maps_to Set.MapsTo

theorem mapsTo_image (f : α → β) (s : Set α) : MapsTo f s (f '' s) := fun _ ↦ mem_image_of_mem f
#align set.maps_to_image Set.mapsTo_image

theorem mapsTo_preimage (f : α → β) (t : Set β) : MapsTo f (f ⁻¹' t) t := fun _ ↦ id
#align set.maps_to_preimage Set.mapsTo_preimage

/-- Given a map `f` sending `s : Set α` into `t : Set β`, restrict domain of `f` to `s`
and the codomain to `t`. Same as `Subtype.map`. -/
def MapsTo.restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) : s → t :=
  Subtype.map f h
#align set.maps_to.restrict Set.MapsTo.restrict

/-- The restriction of a function onto the preimage of a set. -/
@[simps!]
def restrictPreimage (t : Set β) (f : α → β) : f ⁻¹' t → t :=
  (Set.mapsTo_preimage f t).restrict _ _ _
#align set.restrict_preimage Set.restrictPreimage
#align set.restrict_preimage_coe Set.restrictPreimage_coe

/-- `f` is injective on `a` if the restriction of `f` to `a` is injective. -/
def InjOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂
#align set.inj_on Set.InjOn

/-- The graph of a function `f : α → β` on a set `s`. -/
def graphOn (f : α → β) (s : Set α) : Set (α × β) := (fun x ↦ (x, f x)) '' s

/-- `f` is surjective from `a` to `b` if `b` is contained in the image of `a`. -/
def SurjOn (f : α → β) (s : Set α) (t : Set β) : Prop := t ⊆ f '' s
#align set.surj_on Set.SurjOn

/-- `f` is bijective from `s` to `t` if `f` is injective on `s` and `f '' s = t`. -/
def BijOn (f : α → β) (s : Set α) (t : Set β) : Prop := MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t
#align set.bij_on Set.BijOn

/-- `g` is a left inverse to `f` on `a` means that `g (f x) = x` for all `x ∈ a`. -/
def LeftInvOn (f' : β → α) (f : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → f' (f x) = x
#align set.left_inv_on Set.LeftInvOn

/-- `g` is a right inverse to `f` on `b` if `f (g x) = x` for all `x ∈ b`. -/
abbrev RightInvOn (f' : β → α) (f : α → β) (t : Set β) : Prop := LeftInvOn f f' t
#align set.right_inv_on Set.RightInvOn

/-- `g` is an inverse to `f` viewed as a map from `a` to `b` -/
def InvOn (g : β → α) (f : α → β) (s : Set α) (t : Set β) : Prop :=
  LeftInvOn g f s ∧ RightInvOn g f t
#align set.inv_on Set.InvOn

section image2

/-- The image of a binary function `f : α → β → γ` as a function `Set α → Set β → Set γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def image2 (f : α → β → γ) (s : Set α) (t : Set β) : Set γ := {c | ∃ a ∈ s, ∃ b ∈ t, f a b = c}
#align set.image2 Set.image2

variable {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β} {c : γ}

@[simp] theorem mem_image2 : c ∈ image2 f s t ↔ ∃ a ∈ s, ∃ b ∈ t, f a b = c := .rfl
#align set.mem_image2 Set.mem_image2

theorem mem_image2_of_mem (ha : a ∈ s) (hb : b ∈ t) : f a b ∈ image2 f s t :=
  ⟨a, ha, b, hb, rfl⟩
#align set.mem_image2_of_mem Set.mem_image2_of_mem

end image2

/-- Given a set `s` of functions `α → β` and `t : Set α`, `seq s t` is the union of `f '' t` over
all `f ∈ s`. -/
def seq (s : Set (α → β)) (t : Set α) : Set β := image2 (fun f ↦ f) s t
#align set.seq Set.seq

@[simp]
theorem mem_seq_iff {s : Set (α → β)} {t : Set α} {b : β} :
    b ∈ seq s t ↔ ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b :=
  Iff.rfl
#align set.mem_seq_iff Set.mem_seq_iff

lemma seq_eq_image2 (s : Set (α → β)) (t : Set α) : seq s t = image2 (fun f a ↦ f a) s t := rfl

end Set
