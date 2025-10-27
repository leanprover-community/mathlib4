/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
import Mathlib.Algebra.Notation.Support
import Mathlib.Data.Set.Finite.Basic

/-!
# Type of functions with finite support

For any type `α` and any type `M` with zero, we define the type `Finsupp α M` (notation: `α →₀ M`)
of finitely supported functions from `α` to `M`, i.e. the functions which are zero everywhere
on `α` except on a finite set.

Functions with finite support are used (at least) in the following parts of the library:

* `MonoidAlgebra R M` and `AddMonoidAlgebra R M` are defined as `M →₀ R`;

* polynomials and multivariate polynomials are defined as `AddMonoidAlgebra`s, hence they use
  `Finsupp` under the hood;

* the linear combination of a family of vectors `v i` with coefficients `f i` (as used, e.g., to
  define linearly independent family `LinearIndependent`) is defined as a map
  `Finsupp.linearCombination : (ι → M) → (ι →₀ R) →ₗ[R] M`.

Some other constructions are naturally equivalent to `α →₀ M` with some `α` and `M` but are defined
in a different way in the library:

* `Multiset α ≃+ α →₀ ℕ`;
* `FreeAbelianGroup α ≃+ α →₀ ℤ`.

Most of the theory assumes that the range is a commutative additive monoid. This gives us the big
sum operator as a powerful way to construct `Finsupp` elements, which is defined in
`Mathlib/Algebra/BigOperators/Finsupp/Basic.lean`.

Many constructions based on `α →₀ M` are `def`s rather than `abbrev`s to avoid reusing unwanted type
class instances. E.g., `MonoidAlgebra`, `AddMonoidAlgebra`, and types based on these two have
non-pointwise multiplication.

## Main declarations

* `Finsupp`: The type of finitely supported functions from `α` to `β`.
* `Finsupp.onFinset`: The restriction of a function to a `Finset` as a `Finsupp`.
* `Finsupp.mapRange`: Composition of a `ZeroHom` with a `Finsupp`.
* `Finsupp.embDomain`: Maps the domain of a `Finsupp` by an embedding.
* `Finsupp.zipWith`: Postcomposition of two `Finsupp`s with a function `f` such that `f 0 0 = 0`.

## Notation

This file adds `α →₀ M` as a global notation for `Finsupp α M`.

We also use the following convention for `Type*` variables in this file

* `α`, `β`, `γ`: types with no additional structure that appear as the first argument to `Finsupp`
  somewhere in the statement;

* `ι` : an auxiliary index type;

* `M`, `M'`, `N`, `P`: types with `Zero` or `(Add)(Comm)Monoid` structure; `M` is also used
  for a (semi)module over a (semi)ring.

* `G`, `H`: groups (commutative or not, multiplicative or additive);

* `R`, `S`: (semi)rings.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* Expand the list of definitions and important lemmas to the module docstring.

-/

assert_not_exists CompleteLattice Monoid

noncomputable section

open Finset Function

variable {α β γ ι M M' N P G H R S : Type*}

/-- `Finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but finitely many `x`. -/
structure Finsupp (α : Type*) (M : Type*) [Zero M] where
  /-- The support of a finitely supported function (aka `Finsupp`). -/
  support : Finset α
  /-- The underlying function of a bundled finitely supported function (aka `Finsupp`). -/
  toFun : α → M
  /-- The witness that the support of a `Finsupp` is indeed the exact locus where its
  underlying function is nonzero. -/
  mem_support_toFun : ∀ a, a ∈ support ↔ toFun a ≠ 0

@[inherit_doc]
infixr:25 " →₀ " => Finsupp

namespace Finsupp

/-! ### Basic declarations about `Finsupp` -/


section Basic

variable [Zero M]

instance instFunLike : FunLike (α →₀ M) α M :=
  ⟨toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm⟩

@[ext]
theorem ext {f g : α →₀ M} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

lemma ne_iff {f g : α →₀ M} : f ≠ g ↔ ∃ a, f a ≠ g a := DFunLike.ne_iff

@[simp, norm_cast]
theorem coe_mk (f : α → M) (s : Finset α) (h : ∀ a, a ∈ s ↔ f a ≠ 0) : ⇑(⟨s, f, h⟩ : α →₀ M) = f :=
  rfl

instance instZero : Zero (α →₀ M) :=
  ⟨⟨∅, 0, fun _ => ⟨fun h ↦ (notMem_empty _ h).elim, fun H => (H rfl).elim⟩⟩⟩

@[simp, norm_cast] lemma coe_zero : ⇑(0 : α →₀ M) = 0 := rfl

theorem zero_apply {a : α} : (0 : α →₀ M) a = 0 :=
  rfl

@[simp]
theorem support_zero : (0 : α →₀ M).support = ∅ :=
  rfl

instance instInhabited : Inhabited (α →₀ M) :=
  ⟨0⟩

@[simp]
theorem mem_support_iff {f : α →₀ M} : ∀ {a : α}, a ∈ f.support ↔ f a ≠ 0 :=
  @(f.mem_support_toFun)

@[simp, norm_cast]
theorem fun_support_eq (f : α →₀ M) : Function.support f = f.support :=
  Set.ext fun _x => mem_support_iff.symm

theorem notMem_support_iff {f : α →₀ M} {a} : a ∉ f.support ↔ f a = 0 :=
  not_iff_comm.1 mem_support_iff.symm

@[deprecated (since := "2025-05-23")] alias not_mem_support_iff := notMem_support_iff

@[simp, norm_cast]
theorem coe_eq_zero {f : α →₀ M} : (f : α → M) = 0 ↔ f = 0 := by rw [← coe_zero, DFunLike.coe_fn_eq]

theorem ext_iff' {f g : α →₀ M} : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      classical
      exact if h : a ∈ f.support then h₂ a h else by
        have hf : f a = 0 := notMem_support_iff.1 h
        have hg : g a = 0 := by rwa [h₁, notMem_support_iff] at h
        rw [hf, hg]⟩

@[simp]
theorem support_eq_empty {f : α →₀ M} : f.support = ∅ ↔ f = 0 :=
  mod_cast @Function.support_eq_empty_iff _ _ _ f

theorem support_nonempty_iff {f : α →₀ M} : f.support.Nonempty ↔ f ≠ 0 := by
  simp only [Finsupp.support_eq_empty, Finset.nonempty_iff_ne_empty, Ne]

theorem card_support_eq_zero {f : α →₀ M} : #f.support = 0 ↔ f = 0 := by simp

instance instDecidableEq [DecidableEq α] [DecidableEq M] : DecidableEq (α →₀ M) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ a ∈ f.support, f a = g a) ext_iff'.symm

theorem finite_support (f : α →₀ M) : Set.Finite (Function.support f) :=
  f.fun_support_eq.symm ▸ f.support.finite_toSet

theorem support_subset_iff {s : Set α} {f : α →₀ M} :
    ↑f.support ⊆ s ↔ ∀ a ∉ s, f a = 0 := by
  simp only [Set.subset_def, mem_coe, mem_support_iff, forall_congr' fun a => not_imp_comm]

/-- Given `Finite α`, `equivFunOnFinite` is the `Equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
def equivFunOnFinite [Finite α] : (α →₀ M) ≃ (α → M) where
  toFun := (⇑)
  invFun f := mk (Function.support f).toFinite.toFinset f fun _a => Set.Finite.mem_toFinset _

@[simp]
theorem equivFunOnFinite_symm_coe {α} [Finite α] (f : α →₀ M) : equivFunOnFinite.symm f = f :=
  equivFunOnFinite.symm_apply_apply f

@[simp]
lemma coe_equivFunOnFinite_symm {α} [Finite α] (f : α → M) : ⇑(equivFunOnFinite.symm f) = f := rfl

/--
If `α` has a unique term, the type of finitely supported functions `α →₀ β` is equivalent to `β`.
-/
@[simps!]
noncomputable def _root_.Equiv.finsuppUnique {ι : Type*} [Unique ι] : (ι →₀ M) ≃ M :=
  Finsupp.equivFunOnFinite.trans (Equiv.funUnique ι M)

@[ext]
theorem unique_ext [Unique α] {f g : α →₀ M} (h : f default = g default) : f = g :=
  ext fun a => by rwa [Unique.eq_default a]

end Basic

/-! ### Declarations about `onFinset` -/


section OnFinset

variable [Zero M]

private irreducible_def onFinset_support (s : Finset α) (f : α → M) : Finset α :=
  haveI := Classical.decEq M
  {a ∈ s | f a ≠ 0}

/-- `Finsupp.onFinset s f hf` is the finsupp function representing `f` restricted to the finset `s`.
The function must be `0` outside of `s`. Use this when the set needs to be filtered anyways,
otherwise a better set representation is often available. -/
def onFinset (s : Finset α) (f : α → M) (hf : ∀ a, f a ≠ 0 → a ∈ s) : α →₀ M where
  support := onFinset_support s f
  toFun := f
  mem_support_toFun := by classical simpa [onFinset_support_def]

@[simp, norm_cast] lemma coe_onFinset (s : Finset α) (f : α → M) (hf) : onFinset s f hf = f := rfl

@[simp]
theorem onFinset_apply {s : Finset α} {f : α → M} {hf a} : (onFinset s f hf : α →₀ M) a = f a :=
  rfl

theorem support_onFinset [DecidableEq M] {s : Finset α} {f : α → M}
    (hf : ∀ a : α, f a ≠ 0 → a ∈ s) :
    (Finsupp.onFinset s f hf).support = {a ∈ s | f a ≠ 0} := by
  dsimp [onFinset]; rw [onFinset_support]; congr

@[simp]
theorem support_onFinset_subset {s : Finset α} {f : α → M} {hf} :
    (onFinset s f hf).support ⊆ s := by
  classical
  rw [support_onFinset]
  exact filter_subset (f · ≠ 0) s

theorem mem_support_onFinset {s : Finset α} {f : α → M} (hf : ∀ a : α, f a ≠ 0 → a ∈ s) {a : α} :
    a ∈ (Finsupp.onFinset s f hf).support ↔ f a ≠ 0 := by
  rw [Finsupp.mem_support_iff, Finsupp.onFinset_apply]

end OnFinset

section OfSupportFinite

variable [Zero M]

/-- The natural `Finsupp` induced by the function `f` given that it has finite support. -/
noncomputable def ofSupportFinite (f : α → M) (hf : (Function.support f).Finite) : α →₀ M where
  support := hf.toFinset
  toFun := f
  mem_support_toFun _ := hf.mem_toFinset

theorem ofSupportFinite_coe {f : α → M} {hf : (Function.support f).Finite} :
    (ofSupportFinite f hf : α → M) = f :=
  rfl

theorem ofSupportFinite_support {f : α → M} (hf : f.support.Finite) :
    (ofSupportFinite f hf).support = hf.toFinset := by
  ext; simp [ofSupportFinite_coe]

instance instCanLift : CanLift (α → M) (α →₀ M) (⇑) fun f => (Function.support f).Finite where
  prf f hf := ⟨ofSupportFinite f hf, rfl⟩

end OfSupportFinite

/-! ### Declarations about `mapRange` -/


section MapRange

variable [Zero M] [Zero N] [Zero P]

/-- The composition of `f : M → N` and `g : α →₀ M` is `mapRange f hf g : α →₀ N`,
which is well-defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled (defined in `Mathlib/Data/Finsupp/Basic.lean`):

* `Finsupp.mapRange.equiv`
* `Finsupp.mapRange.zeroHom`
* `Finsupp.mapRange.addMonoidHom`
* `Finsupp.mapRange.addEquiv`
* `Finsupp.mapRange.linearMap`
* `Finsupp.mapRange.linearEquiv`
-/
def mapRange (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
  onFinset g.support (f ∘ g) fun a => by
    rw [mem_support_iff, not_imp_not]; exact fun H => (congr_arg f H).trans hf

@[simp]
theorem mapRange_apply {f : M → N} {hf : f 0 = 0} {g : α →₀ M} {a : α} :
    mapRange f hf g a = f (g a) :=
  rfl

@[simp]
theorem mapRange_zero {f : M → N} {hf : f 0 = 0} : mapRange f hf (0 : α →₀ M) = 0 :=
  ext fun _ => by simp only [hf, zero_apply, mapRange_apply]

@[simp]
theorem mapRange_id (g : α →₀ M) : mapRange id rfl g = g :=
  ext fun _ => rfl

theorem mapRange_comp (f : N → P) (hf : f 0 = 0) (f₂ : M → N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0)
    (g : α →₀ M) : mapRange (f ∘ f₂) h g = mapRange f hf (mapRange f₂ hf₂ g) :=
  ext fun _ => rfl

@[simp]
lemma mapRange_mapRange (e₁ : N → P) (e₂ : M → N) (he₁ he₂) (f : α →₀ M) :
    mapRange e₁ he₁ (mapRange e₂ he₂ f) = mapRange (e₁ ∘ e₂) (by simp [*]) f := ext fun _ ↦ rfl

theorem support_mapRange {f : M → N} {hf : f 0 = 0} {g : α →₀ M} :
    (mapRange f hf g).support ⊆ g.support :=
  support_onFinset_subset

theorem support_mapRange_of_injective {e : M → N} (he0 : e 0 = 0) (f : ι →₀ M)
    (he : Function.Injective e) : (Finsupp.mapRange e he0 f).support = f.support := by
  ext
  simp only [Finsupp.mem_support_iff, Ne, Finsupp.mapRange_apply]
  exact he.ne_iff' he0

lemma range_mapRange (e : M → N) (he₀ : e 0 = 0) :
    Set.range (Finsupp.mapRange (α := α) e he₀) = {g | ∀ i, g i ∈ Set.range e} := by
  ext g
  simp only [Set.mem_range, Set.mem_setOf]
  constructor
  · rintro ⟨g, rfl⟩ i
    simp
  · intro h
    classical
    choose f h using h
    use onFinset g.support (fun x ↦ if x ∈ g.support then f x else 0) (by simp_all)
    ext i
    simp only [mapRange_apply, onFinset_apply]
    split_ifs <;> simp_all

/-- `Finsupp.mapRange` of a injective function is injective. -/
lemma mapRange_injective (e : M → N) (he₀ : e 0 = 0) (he : Injective e) :
    Injective (Finsupp.mapRange (α := α) e he₀) := by
  intro a b h
  rw [Finsupp.ext_iff] at h ⊢
  simpa only [mapRange_apply, he.eq_iff] using h

/-- `Finsupp.mapRange` of a surjective function is surjective. -/
lemma mapRange_surjective (e : M → N) (he₀ : e 0 = 0) (he : Surjective e) :
    Surjective (Finsupp.mapRange (α := α) e he₀) := by
  rw [← Set.range_eq_univ, range_mapRange, he.range_eq]
  simp

end MapRange

/-! ### Declarations about `embDomain` -/


section EmbDomain

variable [Zero M] [Zero N]

/-- Given `f : α ↪ β` and `v : α →₀ M`, `Finsupp.embDomain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero. -/
def embDomain (f : α ↪ β) (v : α →₀ M) : β →₀ M where
  support := v.support.map f
  toFun a₂ :=
    haveI := Classical.decEq β
    if h : a₂ ∈ v.support.map f then
      v
        (v.support.choose (fun a₁ => f a₁ = a₂)
          (by
            rcases Finset.mem_map.1 h with ⟨a, ha, rfl⟩
            exact ExistsUnique.intro a ⟨ha, rfl⟩ fun b ⟨_, hb⟩ => f.injective hb))
    else 0
  mem_support_toFun a₂ := by
    dsimp
    split_ifs with h
    · simp only [h, true_iff]
      rw [← notMem_support_iff, not_not]
      classical apply Finset.choose_mem
    · simp only [h, not_true_eq_false]

@[simp]
theorem support_embDomain (f : α ↪ β) (v : α →₀ M) : (embDomain f v).support = v.support.map f :=
  rfl

@[simp]
theorem embDomain_zero (f : α ↪ β) : (embDomain f 0 : β →₀ M) = 0 :=
  rfl

@[simp]
theorem embDomain_apply (f : α ↪ β) (v : α →₀ M) (a : α) : embDomain f v (f a) = v a := by
  classical
    simp_rw [embDomain, coe_mk, mem_map']
    split_ifs with h
    · refine congr_arg (v : α → M) (f.inj' ?_)
      exact Finset.choose_property (fun a₁ => f a₁ = f a) _ _
    · exact (notMem_support_iff.1 h).symm

theorem embDomain_notin_range (f : α ↪ β) (v : α →₀ M) (a : β) (h : a ∉ Set.range f) :
    embDomain f v a = 0 := by
  classical
    refine dif_neg (mt (fun h => ?_) h)
    rcases Finset.mem_map.1 h with ⟨a, _h, rfl⟩
    exact Set.mem_range_self a

theorem embDomain_injective (f : α ↪ β) : Function.Injective (embDomain f : (α →₀ M) → β →₀ M) :=
  fun l₁ l₂ h => ext fun a => by simpa only [embDomain_apply] using DFunLike.ext_iff.1 h (f a)

@[simp]
theorem embDomain_inj {f : α ↪ β} {l₁ l₂ : α →₀ M} : embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂ :=
  (embDomain_injective f).eq_iff

@[simp]
theorem embDomain_eq_zero {f : α ↪ β} {l : α →₀ M} : embDomain f l = 0 ↔ l = 0 :=
  (embDomain_injective f).eq_iff' <| embDomain_zero f

theorem embDomain_mapRange (f : α ↪ β) (g : M → N) (p : α →₀ M) (hg : g 0 = 0) :
    embDomain f (mapRange g hg p) = mapRange g hg (embDomain f p) := by
  ext a
  by_cases h : a ∈ Set.range f
  · rcases h with ⟨a', rfl⟩
    rw [mapRange_apply, embDomain_apply, embDomain_apply, mapRange_apply]
  · rw [mapRange_apply, embDomain_notin_range, embDomain_notin_range, ← hg] <;> assumption

end EmbDomain

/-! ### Declarations about `zipWith` -/


section ZipWith

variable [Zero M] [Zero N] [Zero P]

/-- Given finitely supported functions `g₁ : α →₀ M` and `g₂ : α →₀ N` and function `f : M → N → P`,
`Finsupp.zipWith f hf g₁ g₂` is the finitely supported function `α →₀ P` satisfying
`zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, which is well-defined when `f 0 0 = 0`. -/
def zipWith (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ P :=
  onFinset
    (haveI := Classical.decEq α; g₁.support ∪ g₂.support)
    (fun a => f (g₁ a) (g₂ a))
    fun a (H : f _ _ ≠ 0) => by
      classical
      rw [mem_union, mem_support_iff, mem_support_iff, ← not_and_or]
      rintro ⟨h₁, h₂⟩; rw [h₁, h₂] at H; exact H hf

@[simp]
theorem zipWith_apply {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} {a : α} :
    zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl

theorem support_zipWith [D : DecidableEq α] {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M}
    {g₂ : α →₀ N} : (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  convert support_onFinset_subset

end ZipWith

section Restrict

variable [Zero α] (f g : ι → α) (s : Finset ι)
  [DecidablePred fun i ↦ i ∈ s] [DecidablePred fun i ↦ f i ≠ 0]

/-- The restriction of a finitely supported map `ι →₀ α` to `s : Finset ι`. -/
def restrict : ι →₀ α where
  toFun i := if i ∈ s then f i else 0
  support := {i ∈ s | f i ≠ 0}
  mem_support_toFun i := by simp

variable {f g s}

theorem restrict_apply {i : ι} : restrict f s i = if i ∈ s then f i else 0 := rfl

theorem restrict_support_le : (restrict f s).support ⊆ s := fun i hi ↦ by
  simp only [mem_support_iff, restrict_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at hi
  exact hi.1

theorem restrict_restrict [DecidableEq ι] {t : Finset ι} [DecidablePred fun i ↦ i ∈ t]
    [DecidablePred fun i ↦ i ∈ s ∩ t] [DecidablePred fun i ↦ (restrict f s) i ≠ 0] :
    restrict (restrict f s) t = restrict f (s ∩ t) := by
  ext i
  simp only [restrict_apply]
  by_cases ht : i ∈ t
  · rw [if_pos ht]
    by_cases hs : i ∈ s
    · rw [if_pos hs, if_pos (mem_inter_of_mem hs ht)]
    · rw [if_neg hs, if_neg (fun hs' ↦ hs (Finset.inter_subset_left hs'))]
  · rw [if_neg ht, if_neg (fun ht' ↦ ht (Finset.inter_subset_right ht'))]

theorem eq_restrict_iff :
    g = restrict f s ↔ g.support ⊆ s ∧ ∀ i, i ∈ s → f i = g i := by
  suffices g.support ⊆ s ∧ (∀ i, i ∈ s → f i = g i) ↔
      ∀ i, (i ∈ s → g i = f i) ∧ (i ∉ s → g i = 0) by
    rw [this, funext_iff]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ s <;> simp [restrict_apply, hi]
  rw [Set.subset_def, and_comm, forall_and]
  apply and_congr
  · simp_rw [eq_comm]
  · simp [not_imp_comm]

theorem self_eq_restrict_iff : f = restrict f s ↔ f.support ⊆ s := by
  simp [eq_restrict_iff]

end Restrict

end Finsupp
