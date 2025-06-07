/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Rat.BigOperators

/-!
# Miscellaneous definitions, lemmas, and constructions using finsupp

## Main declarations

* `Finsupp.graph`: the finset of input and output pairs with non-zero outputs.
* `Finsupp.mapRange.equiv`: `Finsupp.mapRange` as an equiv.
* `Finsupp.mapDomain`: maps the domain of a `Finsupp` by a function and by summing.
* `Finsupp.comapDomain`: postcomposition of a `Finsupp` with a function injective on the preimage
  of its support.
* `Finsupp.some`: restrict a finitely supported function on `Option α` to a finitely supported
  function on `α`.
* `Finsupp.filter`: `filter p f` is the finitely supported function that is `f a` if `p a` is true
  and 0 otherwise.
* `Finsupp.frange`: the image of a finitely supported function on its support.
* `Finsupp.subtype_domain`: the restriction of a finitely supported function `f` to a subtype.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* This file is currently ~1600 lines long and is quite a miscellany of definitions and lemmas,
  so it should be divided into smaller pieces.

* Expand the list of definitions and important lemmas to the module docstring.

-/


noncomputable section

open Finset Function

variable {α β γ ι M M' N P G H R S : Type*}

namespace Finsupp

/-! ### Declarations about `graph` -/


section Graph

variable [Zero M]

/-- The graph of a finitely supported function over its support, i.e. the finset of input and output
pairs with non-zero outputs. -/
def graph (f : α →₀ M) : Finset (α × M) :=
  f.support.map ⟨fun a => Prod.mk a (f a), fun _ _ h => (Prod.mk.inj h).1⟩

theorem mk_mem_graph_iff {a : α} {m : M} {f : α →₀ M} : (a, m) ∈ f.graph ↔ f a = m ∧ m ≠ 0 := by
  simp_rw [graph, mem_map, mem_support_iff]
  constructor
  · rintro ⟨b, ha, rfl, -⟩
    exact ⟨rfl, ha⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

@[simp]
theorem mem_graph_iff {c : α × M} {f : α →₀ M} : c ∈ f.graph ↔ f c.1 = c.2 ∧ c.2 ≠ 0 := by
  cases c
  exact mk_mem_graph_iff

theorem mk_mem_graph (f : α →₀ M) {a : α} (ha : a ∈ f.support) : (a, f a) ∈ f.graph :=
  mk_mem_graph_iff.2 ⟨rfl, mem_support_iff.1 ha⟩

theorem apply_eq_of_mem_graph {a : α} {m : M} {f : α →₀ M} (h : (a, m) ∈ f.graph) : f a = m :=
  (mem_graph_iff.1 h).1

@[simp 1100] -- Higher priority shortcut instance for `mem_graph_iff`.
theorem notMem_graph_snd_zero (a : α) (f : α →₀ M) : (a, (0 : M)) ∉ f.graph := fun h =>
  (mem_graph_iff.1 h).2.irrefl

@[deprecated (since := "2025-05-23")] alias not_mem_graph_snd_zero := notMem_graph_snd_zero

@[simp]
theorem image_fst_graph [DecidableEq α] (f : α →₀ M) : f.graph.image Prod.fst = f.support := by
  classical
  simp only [graph, map_eq_image, image_image, Embedding.coeFn_mk, Function.comp_def, image_id']

theorem graph_injective (α M) [Zero M] : Injective (@graph α M _) := by
  intro f g h
  classical
    have hsup : f.support = g.support := by rw [← image_fst_graph, h, image_fst_graph]
    refine ext_iff'.2 ⟨hsup, fun x hx => apply_eq_of_mem_graph <| h.symm ▸ ?_⟩
    exact mk_mem_graph _ (hsup ▸ hx)

@[simp]
theorem graph_inj {f g : α →₀ M} : f.graph = g.graph ↔ f = g :=
  (graph_injective α M).eq_iff

@[simp]
theorem graph_zero : graph (0 : α →₀ M) = ∅ := by simp [graph]

@[simp]
theorem graph_eq_empty {f : α →₀ M} : f.graph = ∅ ↔ f = 0 :=
  (graph_injective α M).eq_iff' graph_zero

end Graph

end Finsupp

/-! ### Declarations about `mapRange` -/


section MapRange

namespace Finsupp

section Equiv

variable [Zero M] [Zero N] [Zero P]

/-- `Finsupp.mapRange` as an equiv. -/
@[simps apply]
def mapRange.equiv (f : M ≃ N) (hf : f 0 = 0) (hf' : f.symm 0 = 0) : (α →₀ M) ≃ (α →₀ N) where
  toFun := (mapRange f hf : (α →₀ M) → α →₀ N)
  invFun := (mapRange f.symm hf' : (α →₀ N) → α →₀ M)
  left_inv x := by
    rw [← mapRange_comp _ _ _ _] <;> simp_rw [Equiv.symm_comp_self]
    · exact mapRange_id _
    · rfl
  right_inv x := by
    rw [← mapRange_comp _ _ _ _] <;> simp_rw [Equiv.self_comp_symm]
    · exact mapRange_id _
    · rfl

@[simp]
theorem mapRange.equiv_refl : mapRange.equiv (Equiv.refl M) rfl rfl = Equiv.refl (α →₀ M) :=
  Equiv.ext mapRange_id

theorem mapRange.equiv_trans (f : M ≃ N) (hf : f 0 = 0) (hf') (f₂ : N ≃ P) (hf₂ : f₂ 0 = 0) (hf₂') :
    (mapRange.equiv (f.trans f₂) (by rw [Equiv.trans_apply, hf, hf₂])
          (by rw [Equiv.symm_trans_apply, hf₂', hf']) :
        (α →₀ _) ≃ _) =
      (mapRange.equiv f hf hf').trans (mapRange.equiv f₂ hf₂ hf₂') :=
  Equiv.ext <| mapRange_comp f₂ hf₂ f hf ((congrArg f₂ hf).trans hf₂)

@[simp]
theorem mapRange.equiv_symm (f : M ≃ N) (hf hf') :
    ((mapRange.equiv f hf hf').symm : (α →₀ _) ≃ _) = mapRange.equiv f.symm hf' hf :=
  Equiv.ext fun _ => rfl

end Equiv

section ZeroHom

variable [Zero M] [Zero N] [Zero P]

/-- Composition with a fixed zero-preserving homomorphism is itself a zero-preserving homomorphism
on functions. -/
@[simps]
def mapRange.zeroHom (f : ZeroHom M N) : ZeroHom (α →₀ M) (α →₀ N) where
  toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
  map_zero' := mapRange_zero

@[simp]
theorem mapRange.zeroHom_id : mapRange.zeroHom (ZeroHom.id M) = ZeroHom.id (α →₀ M) :=
  ZeroHom.ext mapRange_id

theorem mapRange.zeroHom_comp (f : ZeroHom N P) (f₂ : ZeroHom M N) :
    (mapRange.zeroHom (f.comp f₂) : ZeroHom (α →₀ _) _) =
      (mapRange.zeroHom f).comp (mapRange.zeroHom f₂) :=
  ZeroHom.ext <| mapRange_comp f (map_zero f) f₂ (map_zero f₂) (by simp only [comp_apply, map_zero])

end ZeroHom

section AddMonoidHom

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N]

/-- Composition with a fixed additive homomorphism is itself an additive homomorphism on functions.
-/
@[simps]
def mapRange.addMonoidHom (f : M →+ N) : (α →₀ M) →+ α →₀ N where
  toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
  map_zero' := mapRange_zero
  -- Porting note: need either `dsimp only` or to specify `hf`:
  -- see also: https://github.com/leanprover-community/mathlib4/issues/12129
  map_add' := mapRange_add (hf := f.map_zero) f.map_add

@[simp]
theorem mapRange.addMonoidHom_id :
    mapRange.addMonoidHom (AddMonoidHom.id M) = AddMonoidHom.id (α →₀ M) :=
  AddMonoidHom.ext mapRange_id

theorem mapRange.addMonoidHom_comp (f : N →+ P) (f₂ : M →+ N) :
    (mapRange.addMonoidHom (f.comp f₂) : (α →₀ _) →+ _) =
      (mapRange.addMonoidHom f).comp (mapRange.addMonoidHom f₂) :=
  AddMonoidHom.ext <|
    mapRange_comp f (map_zero f) f₂ (map_zero f₂) (by simp only [comp_apply, map_zero])

@[simp]
theorem mapRange.addMonoidHom_toZeroHom (f : M →+ N) :
    (mapRange.addMonoidHom f).toZeroHom = (mapRange.zeroHom f.toZeroHom : ZeroHom (α →₀ _) _) :=
  ZeroHom.ext fun _ => rfl

theorem mapRange_multiset_sum (f : F) (m : Multiset (α →₀ M)) :
    mapRange f (map_zero f) m.sum = (m.map fun x => mapRange f (map_zero f) x).sum :=
  (mapRange.addMonoidHom (f : M →+ N) : (α →₀ _) →+ _).map_multiset_sum _

theorem mapRange_finset_sum (f : F) (s : Finset ι) (g : ι → α →₀ M) :
    mapRange f (map_zero f) (∑ x ∈ s, g x) = ∑ x ∈ s, mapRange f (map_zero f) (g x) :=
  map_sum (mapRange.addMonoidHom (f : M →+ N)) _ _

/-- `Finsupp.mapRange.AddMonoidHom` as an equiv. -/
@[simps apply]
def mapRange.addEquiv (f : M ≃+ N) : (α →₀ M) ≃+ (α →₀ N) :=
  { mapRange.addMonoidHom f.toAddMonoidHom with
    toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
    invFun := (mapRange f.symm f.symm.map_zero : (α →₀ N) → α →₀ M)
    left_inv := fun x => by
      rw [← mapRange_comp _ _ _ _] <;> simp_rw [AddEquiv.symm_comp_self]
      · exact mapRange_id _
      · rfl
    right_inv := fun x => by
      rw [← mapRange_comp _ _ _ _] <;> simp_rw [AddEquiv.self_comp_symm]
      · exact mapRange_id _
      · rfl }

@[simp]
theorem mapRange.addEquiv_refl : mapRange.addEquiv (AddEquiv.refl M) = AddEquiv.refl (α →₀ M) :=
  AddEquiv.ext mapRange_id

theorem mapRange.addEquiv_trans (f : M ≃+ N) (f₂ : N ≃+ P) :
    (mapRange.addEquiv (f.trans f₂) : (α →₀ M) ≃+ (α →₀ P)) =
      (mapRange.addEquiv f).trans (mapRange.addEquiv f₂) :=
  AddEquiv.ext (mapRange_comp _ f₂.map_zero _ f.map_zero (by simp))

@[simp]
theorem mapRange.addEquiv_symm (f : M ≃+ N) :
    ((mapRange.addEquiv f).symm : (α →₀ _) ≃+ _) = mapRange.addEquiv f.symm :=
  AddEquiv.ext fun _ => rfl

@[simp]
theorem mapRange.addEquiv_toAddMonoidHom (f : M ≃+ N) :
    ((mapRange.addEquiv f : (α →₀ _) ≃+ _) : _ →+ _) =
      (mapRange.addMonoidHom f.toAddMonoidHom : (α →₀ _) →+ _) :=
  AddMonoidHom.ext fun _ => rfl

@[simp]
theorem mapRange.addEquiv_toEquiv (f : M ≃+ N) :
    ↑(mapRange.addEquiv f : (α →₀ _) ≃+ _) =
      (mapRange.equiv (f : M ≃ N) f.map_zero f.symm.map_zero : (α →₀ _) ≃ _) :=
  Equiv.ext fun _ => rfl

end AddMonoidHom

end Finsupp

end MapRange

/-! ### Declarations about `equivCongrLeft` -/


section EquivCongrLeft

variable [Zero M]

namespace Finsupp

/-- Given `f : α ≃ β`, we can map `l : α →₀ M` to `equivMapDomain f l : β →₀ M` (computably)
by mapping the support forwards and the function backwards. -/
def equivMapDomain (f : α ≃ β) (l : α →₀ M) : β →₀ M where
  support := l.support.map f.toEmbedding
  toFun a := l (f.symm a)
  mem_support_toFun a := by simp only [Finset.mem_map_equiv, mem_support_toFun]; rfl

@[simp]
theorem equivMapDomain_apply (f : α ≃ β) (l : α →₀ M) (b : β) :
    equivMapDomain f l b = l (f.symm b) :=
  rfl

theorem equivMapDomain_symm_apply (f : α ≃ β) (l : β →₀ M) (a : α) :
    equivMapDomain f.symm l a = l (f a) :=
  rfl

@[simp]
theorem equivMapDomain_refl (l : α →₀ M) : equivMapDomain (Equiv.refl _) l = l := by ext x; rfl

theorem equivMapDomain_refl' : equivMapDomain (Equiv.refl _) = @id (α →₀ M) := by ext x; rfl

theorem equivMapDomain_trans (f : α ≃ β) (g : β ≃ γ) (l : α →₀ M) :
    equivMapDomain (f.trans g) l = equivMapDomain g (equivMapDomain f l) := by ext x; rfl

theorem equivMapDomain_trans' (f : α ≃ β) (g : β ≃ γ) :
    @equivMapDomain _ _ M _ (f.trans g) = equivMapDomain g ∘ equivMapDomain f := by ext x; rfl

@[simp]
theorem equivMapDomain_single (f : α ≃ β) (a : α) (b : M) :
    equivMapDomain f (single a b) = single (f a) b := by
  classical
    ext x
    simp only [single_apply, Equiv.apply_eq_iff_eq_symm_apply, equivMapDomain_apply]

@[simp]
theorem equivMapDomain_zero {f : α ≃ β} : equivMapDomain f (0 : α →₀ M) = (0 : β →₀ M) := by
  ext; simp only [equivMapDomain_apply, coe_zero, Pi.zero_apply]

@[to_additive (attr := simp)]
theorem prod_equivMapDomain [CommMonoid N] (f : α ≃ β) (l : α →₀ M) (g : β → M → N) :
    prod (equivMapDomain f l) g = prod l (fun a m => g (f a) m) := by
  simp [prod, equivMapDomain]

/-- Given `f : α ≃ β`, the finitely supported function spaces are also in bijection:
`(α →₀ M) ≃ (β →₀ M)`.

This is the finitely-supported version of `Equiv.piCongrLeft`. -/
def equivCongrLeft (f : α ≃ β) : (α →₀ M) ≃ (β →₀ M) := by
  refine ⟨equivMapDomain f, equivMapDomain f.symm, fun f => ?_, fun f => ?_⟩ <;> ext x <;>
    simp only [equivMapDomain_apply, Equiv.symm_symm, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]

@[simp]
theorem equivCongrLeft_apply (f : α ≃ β) (l : α →₀ M) : equivCongrLeft f l = equivMapDomain f l :=
  rfl

@[simp]
theorem equivCongrLeft_symm (f : α ≃ β) :
    (@equivCongrLeft _ _ M _ f).symm = equivCongrLeft f.symm :=
  rfl

end Finsupp

end EquivCongrLeft

section CastFinsupp

variable [Zero M] (f : α →₀ M)

namespace Nat

@[simp, norm_cast]
theorem cast_finsuppProd [CommSemiring R] (g : α → M → ℕ) :
    (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b) :=
  Nat.cast_prod _ _

@[deprecated (since := "2025-04-06")] alias cast_finsupp_prod := cast_finsuppProd

@[simp, norm_cast]
theorem cast_finsupp_sum [AddCommMonoidWithOne R] (g : α → M → ℕ) :
    (↑(f.sum g) : R) = f.sum fun a b => ↑(g a b) :=
  Nat.cast_sum _ _

end Nat

namespace Int

@[simp, norm_cast]
theorem cast_finsuppProd [CommRing R] (g : α → M → ℤ) :
    (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b) :=
  Int.cast_prod _ _

@[deprecated (since := "2025-04-06")] alias cast_finsupp_prod := cast_finsuppProd

@[simp, norm_cast]
theorem cast_finsupp_sum [AddCommGroupWithOne R] (g : α → M → ℤ) :
    (↑(f.sum g) : R) = f.sum fun a b => ↑(g a b) :=
  Int.cast_sum _ _

end Int

namespace Rat

@[simp, norm_cast]
theorem cast_finsupp_sum [DivisionRing R] [CharZero R] (g : α → M → ℚ) :
    (↑(f.sum g) : R) = f.sum fun a b => ↑(g a b) :=
  cast_sum _ _

@[simp, norm_cast]
theorem cast_finsuppProd [Field R] [CharZero R] (g : α → M → ℚ) :
    (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b) :=
  cast_prod _ _

@[deprecated (since := "2025-04-06")] alias cast_finsupp_prod := cast_finsuppProd

end Rat

end CastFinsupp

/-! ### Declarations about `mapDomain` -/


namespace Finsupp

section MapDomain

variable [AddCommMonoid M] {v v₁ v₂ : α →₀ M}

/-- Given `f : α → β` and `v : α →₀ M`, `mapDomain f v : β →₀ M`
  is the finitely supported function whose value at `a : β` is the sum
  of `v x` over all `x` such that `f x = a`. -/
def mapDomain (f : α → β) (v : α →₀ M) : β →₀ M :=
  v.sum fun a => single (f a)

theorem mapDomain_apply {f : α → β} (hf : Function.Injective f) (x : α →₀ M) (a : α) :
    mapDomain f x (f a) = x a := by
  rw [mapDomain, sum_apply, sum_eq_single a, single_eq_same]
  · intro b _ hba
    exact single_eq_of_ne (hf.ne hba)
  · intro _
    rw [single_zero, coe_zero, Pi.zero_apply]

theorem mapDomain_notin_range {f : α → β} (x : α →₀ M) (a : β) (h : a ∉ Set.range f) :
    mapDomain f x a = 0 := by
  rw [mapDomain, sum_apply, sum]
  exact Finset.sum_eq_zero fun a' _ => single_eq_of_ne fun eq => h <| eq ▸ Set.mem_range_self _

@[simp]
theorem mapDomain_id : mapDomain id v = v :=
  sum_single _

theorem mapDomain_comp {f : α → β} {g : β → γ} :
    mapDomain (g ∘ f) v = mapDomain g (mapDomain f v) := by
  refine ((sum_sum_index ?_ ?_).trans ?_).symm
  · intro
    exact single_zero _
  · intro
    exact single_add _
  refine sum_congr fun _ _ => sum_single_index ?_
  exact single_zero _

@[simp]
theorem mapDomain_single {f : α → β} {a : α} {b : M} : mapDomain f (single a b) = single (f a) b :=
  sum_single_index <| single_zero _

@[simp]
theorem mapDomain_zero {f : α → β} : mapDomain f (0 : α →₀ M) = (0 : β →₀ M) :=
  sum_zero_index

theorem mapDomain_congr {f g : α → β} (h : ∀ x ∈ v.support, f x = g x) :
    v.mapDomain f = v.mapDomain g :=
  Finset.sum_congr rfl fun _ H => by simp only [h _ H]

theorem mapDomain_add {f : α → β} : mapDomain f (v₁ + v₂) = mapDomain f v₁ + mapDomain f v₂ :=
  sum_add_index' (fun _ => single_zero _) fun _ => single_add _

@[simp]
theorem mapDomain_equiv_apply {f : α ≃ β} (x : α →₀ M) (a : β) :
    mapDomain f x a = x (f.symm a) := by
  conv_lhs => rw [← f.apply_symm_apply a]
  exact mapDomain_apply f.injective _ _

/-- `Finsupp.mapDomain` is an `AddMonoidHom`. -/
@[simps]
def mapDomain.addMonoidHom (f : α → β) : (α →₀ M) →+ β →₀ M where
  toFun := mapDomain f
  map_zero' := mapDomain_zero
  map_add' _ _ := mapDomain_add

@[simp]
theorem mapDomain.addMonoidHom_id : mapDomain.addMonoidHom id = AddMonoidHom.id (α →₀ M) :=
  AddMonoidHom.ext fun _ => mapDomain_id

theorem mapDomain.addMonoidHom_comp (f : β → γ) (g : α → β) :
    (mapDomain.addMonoidHom (f ∘ g) : (α →₀ M) →+ γ →₀ M) =
      (mapDomain.addMonoidHom f).comp (mapDomain.addMonoidHom g) :=
  AddMonoidHom.ext fun _ => mapDomain_comp

theorem mapDomain_finset_sum {f : α → β} {s : Finset ι} {v : ι → α →₀ M} :
    mapDomain f (∑ i ∈ s, v i) = ∑ i ∈ s, mapDomain f (v i) :=
  map_sum (mapDomain.addMonoidHom f) _ _

theorem mapDomain_sum [Zero N] {f : α → β} {s : α →₀ N} {v : α → N → α →₀ M} :
    mapDomain f (s.sum v) = s.sum fun a b => mapDomain f (v a b) :=
  map_finsuppSum (mapDomain.addMonoidHom f : (α →₀ M) →+ β →₀ M) _ _

theorem mapDomain_support [DecidableEq β] {f : α → β} {s : α →₀ M} :
    (s.mapDomain f).support ⊆ s.support.image f :=
  Finset.Subset.trans support_sum <|
    Finset.Subset.trans (Finset.biUnion_mono fun _ _ => support_single_subset) <| by
      rw [Finset.biUnion_singleton]

theorem mapDomain_apply' (S : Set α) {f : α → β} (x : α →₀ M) (hS : (x.support : Set α) ⊆ S)
    (hf : Set.InjOn f S) {a : α} (ha : a ∈ S) : mapDomain f x (f a) = x a := by
  classical
    rw [mapDomain, sum_apply, sum]
    simp_rw [single_apply]
    by_cases hax : a ∈ x.support
    · rw [← Finset.add_sum_erase _ _ hax, if_pos rfl]
      convert add_zero (x a)
      refine Finset.sum_eq_zero fun i hi => if_neg ?_
      exact (hf.mono hS).ne (Finset.mem_of_mem_erase hi) hax (Finset.ne_of_mem_erase hi)
    · rw [notMem_support_iff.1 hax]
      refine Finset.sum_eq_zero fun i hi => if_neg ?_
      exact hf.ne (hS hi) ha (ne_of_mem_of_not_mem hi hax)

theorem mapDomain_support_of_injOn [DecidableEq β] {f : α → β} (s : α →₀ M)
    (hf : Set.InjOn f s.support) : (mapDomain f s).support = Finset.image f s.support :=
  Finset.Subset.antisymm mapDomain_support <| by
    intro x hx
    simp only [mem_image, exists_prop, mem_support_iff, Ne] at hx
    rcases hx with ⟨hx_w, hx_h_left, rfl⟩
    simp only [mem_support_iff, Ne]
    rw [mapDomain_apply' (↑s.support : Set _) _ _ hf]
    · exact hx_h_left
    · simp only [mem_coe, mem_support_iff, Ne]
      exact hx_h_left
    · exact Subset.refl _

theorem mapDomain_support_of_injective [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (s : α →₀ M) : (mapDomain f s).support = Finset.image f s.support :=
  mapDomain_support_of_injOn s hf.injOn

@[to_additive]
theorem prod_mapDomain_index [CommMonoid N] {f : α → β} {s : α →₀ M} {h : β → M → N}
    (h_zero : ∀ b, h b 0 = 1) (h_add : ∀ b m₁ m₂, h b (m₁ + m₂) = h b m₁ * h b m₂) :
    (mapDomain f s).prod h = s.prod fun a m => h (f a) m :=
  (prod_sum_index h_zero h_add).trans <| prod_congr fun _ _ => prod_single_index (h_zero _)

-- Note that in `prod_mapDomain_index`, `M` is still an additive monoid,
-- so there is no analogous version in terms of `MonoidHom`.
/-- A version of `sum_mapDomain_index` that takes a bundled `AddMonoidHom`,
rather than separate linearity hypotheses.
-/
@[simp]
theorem sum_mapDomain_index_addMonoidHom [AddCommMonoid N] {f : α → β} {s : α →₀ M}
    (h : β → M →+ N) : ((mapDomain f s).sum fun b m => h b m) = s.sum fun a m => h (f a) m :=
  sum_mapDomain_index (fun b => (h b).map_zero) (fun b _ _ => (h b).map_add _ _)

theorem embDomain_eq_mapDomain (f : α ↪ β) (v : α →₀ M) : embDomain f v = mapDomain f v := by
  ext a
  by_cases h : a ∈ Set.range f
  · rcases h with ⟨a, rfl⟩
    rw [mapDomain_apply f.injective, embDomain_apply]
  · rw [mapDomain_notin_range, embDomain_notin_range] <;> assumption

@[to_additive]
theorem prod_mapDomain_index_inj [CommMonoid N] {f : α → β} {s : α →₀ M} {h : β → M → N}
    (hf : Function.Injective f) : (s.mapDomain f).prod h = s.prod fun a b => h (f a) b := by
  rw [← Function.Embedding.coeFn_mk f hf, ← embDomain_eq_mapDomain, prod_embDomain]

theorem mapDomain_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (mapDomain f : (α →₀ M) → β →₀ M) := by
  intro v₁ v₂ eq
  ext a
  have : mapDomain f v₁ (f a) = mapDomain f v₂ (f a) := by rw [eq]
  rwa [mapDomain_apply hf, mapDomain_apply hf] at this

theorem mapDomain_surjective {f : α → β} (hf : f.Surjective) :
    (mapDomain (M := M) f).Surjective := by
  intro x
  use mapDomain (surjInv hf) x
  rw [← mapDomain_comp, (rightInverse_surjInv hf).id, mapDomain_id]

/-- When `f` is an embedding we have an embedding `(α →₀ ℕ) ↪ (β →₀ ℕ)` given by `mapDomain`. -/
@[simps]
def mapDomainEmbedding {α β : Type*} (f : α ↪ β) : (α →₀ ℕ) ↪ β →₀ ℕ :=
  ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective f.injective⟩

theorem mapDomain.addMonoidHom_comp_mapRange [AddCommMonoid N] (f : α → β) (g : M →+ N) :
    (mapDomain.addMonoidHom f).comp (mapRange.addMonoidHom g) =
      (mapRange.addMonoidHom g).comp (mapDomain.addMonoidHom f) := by
  ext
  simp only [AddMonoidHom.coe_comp, Finsupp.mapRange_single, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.singleAddHom_apply, eq_self_iff_true, Function.comp_apply, Finsupp.mapDomain_single,
    Finsupp.mapRange.addMonoidHom_apply]

/-- When `g` preserves addition, `mapRange` and `mapDomain` commute. -/
theorem mapDomain_mapRange [AddCommMonoid N] (f : α → β) (v : α →₀ M) (g : M → N) (h0 : g 0 = 0)
    (hadd : ∀ x y, g (x + y) = g x + g y) :
    mapDomain f (mapRange g h0 v) = mapRange g h0 (mapDomain f v) :=
  let g' : M →+ N :=
    { toFun := g
      map_zero' := h0
      map_add' := hadd }
  DFunLike.congr_fun (mapDomain.addMonoidHom_comp_mapRange f g') v

theorem sum_update_add [AddZeroClass α] [AddCommMonoid β] (f : ι →₀ α) (i : ι) (a : α)
    (g : ι → α → β) (hg : ∀ i, g i 0 = 0)
    (hgg : ∀ (j : ι) (a₁ a₂ : α), g j (a₁ + a₂) = g j a₁ + g j a₂) :
    (f.update i a).sum g + g i (f i) = f.sum g + g i a := by
  rw [update_eq_erase_add_single, sum_add_index' hg hgg]
  conv_rhs => rw [← Finsupp.update_self f i]
  rw [update_eq_erase_add_single, sum_add_index' hg hgg, add_assoc, add_assoc]
  congr 1
  rw [add_comm, sum_single_index (hg _), sum_single_index (hg _)]

theorem mapDomain_injOn (S : Set α) {f : α → β} (hf : Set.InjOn f S) :
    Set.InjOn (mapDomain f : (α →₀ M) → β →₀ M) { w | (w.support : Set α) ⊆ S } := by
  intro v₁ hv₁ v₂ hv₂ eq
  ext a
  classical
    by_cases h : a ∈ v₁.support ∪ v₂.support
    · rw [← mapDomain_apply' S _ hv₁ hf _, ← mapDomain_apply' S _ hv₂ hf _, eq] <;>
        · apply Set.union_subset hv₁ hv₂
          exact mod_cast h
    · simp only [not_or, mem_union, not_not, mem_support_iff] at h
      simp [h]

theorem equivMapDomain_eq_mapDomain {M} [AddCommMonoid M] (f : α ≃ β) (l : α →₀ M) :
    equivMapDomain f l = mapDomain f l := by ext x; simp [mapDomain_equiv_apply]

end MapDomain

/-! ### Declarations about `comapDomain` -/


section ComapDomain

/-- Given `f : α → β`, `l : β →₀ M` and a proof `hf` that `f` is injective on
the preimage of `l.support`, `comapDomain f l hf` is the finitely supported function
from `α` to `M` given by composing `l` with `f`. -/
@[simps support]
def comapDomain [Zero M] (f : α → β) (l : β →₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support)) :
    α →₀ M where
  support := l.support.preimage f hf
  toFun a := l (f a)
  mem_support_toFun := by
    intro a
    simp only [Finset.mem_def.symm, Finset.mem_preimage]
    exact l.mem_support_toFun (f a)

@[simp]
theorem comapDomain_apply [Zero M] (f : α → β) (l : β →₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support))
    (a : α) : comapDomain f l hf a = l (f a) :=
  rfl

theorem sum_comapDomain [Zero M] [AddCommMonoid N] (f : α → β) (l : β →₀ M) (g : β → M → N)
    (hf : Set.BijOn f (f ⁻¹' ↑l.support) ↑l.support) :
    (comapDomain f l hf.injOn).sum (g ∘ f) = l.sum g := by
  simp only [sum, comapDomain_apply, (· ∘ ·), comapDomain]
  exact Finset.sum_preimage_of_bij f _ hf fun x => g x (l x)

theorem eq_zero_of_comapDomain_eq_zero [Zero M] (f : α → β) (l : β →₀ M)
    (hf : Set.BijOn f (f ⁻¹' ↑l.support) ↑l.support) : comapDomain f l hf.injOn = 0 → l = 0 := by
  rw [← support_eq_empty, ← support_eq_empty, comapDomain]
  simp only [Finset.ext_iff, Finset.notMem_empty, iff_false, mem_preimage]
  intro h a ha
  obtain ⟨b, hb⟩ := hf.2.2 ha
  exact h b (hb.2.symm ▸ ha)

section FInjective

section Zero

variable [Zero M]

lemma embDomain_comapDomain {f : α ↪ β} {g : β →₀ M} (hg : ↑g.support ⊆ Set.range f) :
    embDomain f (comapDomain f g f.injective.injOn) = g := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [embDomain_apply, comapDomain_apply]
  · replace hg : g b = 0 := notMem_support_iff.mp <| mt (hg ·) hb
    rw [embDomain_notin_range _ _ _ hb, hg]

/-- Note the `hif` argument is needed for this to work in `rw`. -/
@[simp]
theorem comapDomain_zero (f : α → β)
    (hif : Set.InjOn f (f ⁻¹' ↑(0 : β →₀ M).support) := Finset.coe_empty ▸ (Set.injOn_empty f)) :
    comapDomain f (0 : β →₀ M) hif = (0 : α →₀ M) := by
  ext
  rfl

@[simp]
theorem comapDomain_single (f : α → β) (a : α) (m : M)
    (hif : Set.InjOn f (f ⁻¹' (single (f a) m).support)) :
    comapDomain f (Finsupp.single (f a) m) hif = Finsupp.single a m := by
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp only [single_zero, comapDomain_zero]
  · rw [eq_single_iff, comapDomain_apply, comapDomain_support, ← Finset.coe_subset, coe_preimage,
      support_single_ne_zero _ hm, coe_singleton, coe_singleton, single_eq_same]
    rw [support_single_ne_zero _ hm, coe_singleton] at hif
    exact ⟨fun x hx => hif hx rfl hx, rfl⟩

end Zero

section AddZeroClass

variable [AddZeroClass M] {f : α → β}

theorem comapDomain_add (v₁ v₂ : β →₀ M) (hv₁ : Set.InjOn f (f ⁻¹' ↑v₁.support))
    (hv₂ : Set.InjOn f (f ⁻¹' ↑v₂.support)) (hv₁₂ : Set.InjOn f (f ⁻¹' ↑(v₁ + v₂).support)) :
    comapDomain f (v₁ + v₂) hv₁₂ = comapDomain f v₁ hv₁ + comapDomain f v₂ hv₂ := by
  ext
  simp only [comapDomain_apply, coe_add, Pi.add_apply]

/-- A version of `Finsupp.comapDomain_add` that's easier to use. -/
theorem comapDomain_add_of_injective (hf : Function.Injective f) (v₁ v₂ : β →₀ M) :
    comapDomain f (v₁ + v₂) hf.injOn =
      comapDomain f v₁ hf.injOn + comapDomain f v₂ hf.injOn :=
  comapDomain_add _ _ _ _ _

/-- `Finsupp.comapDomain` is an `AddMonoidHom`. -/
@[simps]
def comapDomain.addMonoidHom (hf : Function.Injective f) : (β →₀ M) →+ α →₀ M where
  toFun x := comapDomain f x hf.injOn
  map_zero' := comapDomain_zero f
  map_add' := comapDomain_add_of_injective hf

end AddZeroClass

variable [AddCommMonoid M] (f : α → β)

theorem mapDomain_comapDomain (hf : Function.Injective f) (l : β →₀ M)
    (hl : ↑l.support ⊆ Set.range f) :
    mapDomain f (comapDomain f l hf.injOn) = l := by
  conv_rhs => rw [← embDomain_comapDomain (f := ⟨f, hf⟩) hl (M := M), embDomain_eq_mapDomain]
  rfl

theorem comapDomain_mapDomain (hf : Function.Injective f) (l : α →₀ M) :
    comapDomain f (mapDomain f l) hf.injOn = l := by
  ext; rw [comapDomain_apply, mapDomain_apply hf]

end FInjective

end ComapDomain

/-! ### Declarations about finitely supported functions whose support is an `Option` type -/


section Option

/-- Restrict a finitely supported function on `Option α` to a finitely supported function on `α`. -/
def some [Zero M] (f : Option α →₀ M) : α →₀ M :=
  f.comapDomain Option.some fun _ => by simp

@[simp]
theorem some_apply [Zero M] (f : Option α →₀ M) (a : α) : f.some a = f (Option.some a) :=
  rfl

@[simp]
theorem some_zero [Zero M] : (0 : Option α →₀ M).some = 0 := by
  ext
  simp

@[simp]
theorem some_add [AddZeroClass M] (f g : Option α →₀ M) : (f + g).some = f.some + g.some := by
  ext
  simp

@[simp]
theorem some_single_none [Zero M] (m : M) : (single none m : Option α →₀ M).some = 0 := by
  ext
  simp

@[simp]
theorem some_single_some [Zero M] (a : α) (m : M) :
    (single (Option.some a) m : Option α →₀ M).some = single a m := by
  classical
    ext b
    simp [single_apply]

@[simp]
theorem embDomain_some_some [Zero M] (f : α →₀ M) (x) : f.embDomain .some (.some x) = f x := by
  simp [← Function.Embedding.some_apply]

@[simp]
theorem some_update_none [Zero M] (f : Option α →₀ M) (a : M) :
    (f.update .none a).some = f.some := by
  ext
  simp [Finsupp.update]

/-- `Finsupp`s from `Option` are equivalent to
pairs of an element and a `Finsupp` on the original type. -/
@[simps]
noncomputable
def optionEquiv [Zero M] : (Option α →₀ M) ≃ M × (α →₀ M) where
  toFun P := (P .none, P.some)
  invFun P := (P.2.embDomain .some).update .none P.1
  left_inv P := by ext (_|a) <;> simp [Finsupp.update]
  right_inv P := by ext <;> simp [Finsupp.update]

@[to_additive]
theorem prod_option_index [AddZeroClass M] [CommMonoid N] (f : Option α →₀ M)
    (b : Option α → M → N) (h_zero : ∀ o, b o 0 = 1)
    (h_add : ∀ o m₁ m₂, b o (m₁ + m₂) = b o m₁ * b o m₂) :
    f.prod b = b none (f none) * f.some.prod fun a => b (Option.some a) := by
  classical
    induction f using induction_linear with
    | zero => simp [some_zero, h_zero]
    | add f₁ f₂ h₁ h₂ =>
      rw [Finsupp.prod_add_index, h₁, h₂, some_add, Finsupp.prod_add_index]
      · simp only [h_add, Pi.add_apply, Finsupp.coe_add]
        rw [mul_mul_mul_comm]
      all_goals simp [h_zero, h_add]
    | single a m => cases a <;> simp [h_zero, h_add]

theorem sum_option_index_smul [Semiring R] [AddCommMonoid M] [Module R M] (f : Option α →₀ R)
    (b : Option α → M) :
    (f.sum fun o r => r • b o) = f none • b none + f.some.sum fun a r => r • b (Option.some a) :=
  f.sum_option_index _ (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem eq_option_embedding_update_none_iff [Zero M] {n : Option α →₀ M} {m : α →₀ M} {i : M} :
    (n = (embDomain Embedding.some m).update none i) ↔
      n none = i ∧ n.some = m := by
  classical
  rw [Finsupp.ext_iff, Option.forall, Finsupp.ext_iff]
  apply and_congr
  · simp
  · apply forall_congr'
    intro
    simp only [coe_update, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, some_apply]
    rw [← Embedding.some_apply, embDomain_apply, Embedding.some_apply]

@[simp] lemma some_embDomain_some [Zero M] (f : α →₀ M) : (f.embDomain .some).some = f := by
  ext; rw [some_apply]; exact embDomain_apply _ _ _

@[simp] lemma embDomain_some_none [Zero M] (f : α →₀ M) : f.embDomain .some .none = 0 :=
  embDomain_notin_range _ _ _ (by simp)

end Option

/-! ### Declarations about `Finsupp.filter` -/


section Filter

section Zero

variable [Zero M] (p : α → Prop) [DecidablePred p] (f : α →₀ M)

/--
`Finsupp.filter p f` is the finitely supported function that is `f a` if `p a` is true and `0`
otherwise. -/
def filter (p : α → Prop) [DecidablePred p] (f : α →₀ M) : α →₀ M where
  toFun a := if p a then f a else 0
  support := f.support.filter p
  mem_support_toFun a := by
    split_ifs with h <;>
      · simp only [h, mem_filter, mem_support_iff]
        tauto

theorem filter_apply (a : α) : f.filter p a = if p a then f a else 0 := rfl

theorem filter_eq_indicator : ⇑(f.filter p) = Set.indicator { x | p x } f := by
  ext
  simp [filter_apply, Set.indicator_apply]

theorem filter_eq_zero_iff : f.filter p = 0 ↔ ∀ x, p x → f x = 0 := by
  simp only [DFunLike.ext_iff, filter_eq_indicator, zero_apply, Set.indicator_apply_eq_zero,
    Set.mem_setOf_eq]

theorem filter_eq_self_iff : f.filter p = f ↔ ∀ x, f x ≠ 0 → p x := by
  simp only [DFunLike.ext_iff, filter_eq_indicator, Set.indicator_apply_eq_self, Set.mem_setOf_eq,
    not_imp_comm]

@[simp]
theorem filter_apply_pos {a : α} (h : p a) : f.filter p a = f a := if_pos h

@[simp]
theorem filter_apply_neg {a : α} (h : ¬p a) : f.filter p a = 0 := if_neg h

@[simp]
theorem support_filter : (f.filter p).support = {x ∈ f.support | p x} := rfl

theorem filter_zero : (0 : α →₀ M).filter p = 0 := by
  classical rw [← support_eq_empty, support_filter, support_zero, Finset.filter_empty]

@[simp]
theorem filter_single_of_pos {a : α} {b : M} (h : p a) : (single a b).filter p = single a b :=
  (filter_eq_self_iff _ _).2 fun _ hx => (single_apply_ne_zero.1 hx).1.symm ▸ h

@[simp]
theorem filter_single_of_neg {a : α} {b : M} (h : ¬p a) : (single a b).filter p = 0 :=
  (filter_eq_zero_iff _ _).2 fun _ hpx =>
    single_apply_eq_zero.2 fun hxa => absurd hpx (hxa.symm ▸ h)

@[to_additive]
theorem prod_filter_index [CommMonoid N] (g : α → M → N) :
    (f.filter p).prod g = ∏ x ∈ (f.filter p).support, g x (f x) := by
  classical
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [support_filter, Finset.mem_filter] at hx
    rw [filter_apply_pos _ _ hx.2]

@[to_additive (attr := simp)]
theorem prod_filter_mul_prod_filter_not [CommMonoid N] (g : α → M → N) :
    (f.filter p).prod g * (f.filter fun a => ¬p a).prod g = f.prod g := by
  classical simp_rw [prod_filter_index, support_filter, Finset.prod_filter_mul_prod_filter_not,
    Finsupp.prod]

@[to_additive (attr := simp)]
theorem prod_div_prod_filter [CommGroup G] (g : α → M → G) :
    f.prod g / (f.filter p).prod g = (f.filter fun a => ¬p a).prod g :=
  div_eq_of_eq_mul' (prod_filter_mul_prod_filter_not _ _ _).symm

end Zero

theorem filter_pos_add_filter_neg [AddZeroClass M] (f : α →₀ M) (p : α → Prop) [DecidablePred p] :
    (f.filter p + f.filter fun a => ¬p a) = f :=
  DFunLike.coe_injective <| by
    simp only [coe_add, filter_eq_indicator]
    exact Set.indicator_self_add_compl { x | p x } f

end Filter

/-! ### Declarations about `frange` -/


section Frange

variable [Zero M]

/-- `frange f` is the image of `f` on the support of `f`. -/
def frange (f : α →₀ M) : Finset M :=
  haveI := Classical.decEq M
  Finset.image f f.support

theorem mem_frange {f : α →₀ M} {y : M} : y ∈ f.frange ↔ y ≠ 0 ∧ ∃ x, f x = y := by
  rw [frange, @Finset.mem_image _ _ (Classical.decEq _) _ f.support]
  exact ⟨fun ⟨x, hx1, hx2⟩ => ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩, fun ⟨hy, x, hx⟩ =>
    ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩

theorem zero_notMem_frange {f : α →₀ M} : (0 : M) ∉ f.frange := fun H => (mem_frange.1 H).1 rfl

@[deprecated (since := "2025-05-23")] alias zero_not_mem_frange := zero_notMem_frange

theorem frange_single {x : α} {y : M} : frange (single x y) ⊆ {y} := fun r hr =>
  let ⟨t, ht1, ht2⟩ := mem_frange.1 hr
  ht2 ▸ by
    classical
      rw [single_apply] at ht2 ⊢
      split_ifs at ht2 ⊢
      · exact Finset.mem_singleton_self _
      · exact (t ht2.symm).elim

end Frange

/-! ### Declarations about `Finsupp.subtypeDomain` -/


section SubtypeDomain

section Zero

variable [Zero M] {p : α → Prop}

/--
`subtypeDomain p f` is the restriction of the finitely supported function `f` to subtype `p`. -/
def subtypeDomain (p : α → Prop) (f : α →₀ M) : Subtype p →₀ M where
  support :=
    haveI := Classical.decPred p
    f.support.subtype p
  toFun := f ∘ Subtype.val
  mem_support_toFun a := by simp only [@mem_subtype _ _ (Classical.decPred p), mem_support_iff]; rfl

@[simp]
theorem support_subtypeDomain [D : DecidablePred p] {f : α →₀ M} :
    (subtypeDomain p f).support = f.support.subtype p := by rw [Subsingleton.elim D] <;> rfl

@[simp]
theorem subtypeDomain_apply {a : Subtype p} {v : α →₀ M} : (subtypeDomain p v) a = v a.val :=
  rfl

@[simp]
theorem subtypeDomain_zero : subtypeDomain p (0 : α →₀ M) = 0 :=
  rfl

theorem subtypeDomain_eq_iff_forall {f g : α →₀ M} :
    f.subtypeDomain p = g.subtypeDomain p ↔ ∀ x, p x → f x = g x := by
  simp_rw [DFunLike.ext_iff, subtypeDomain_apply, Subtype.forall]

theorem subtypeDomain_eq_iff {f g : α →₀ M}
    (hf : ∀ x ∈ f.support, p x) (hg : ∀ x ∈ g.support, p x) :
    f.subtypeDomain p = g.subtypeDomain p ↔ f = g :=
  subtypeDomain_eq_iff_forall.trans
    ⟨fun H ↦ Finsupp.ext fun _a ↦ (em _).elim (H _ <| hf _ ·) fun haf ↦ (em _).elim (H _ <| hg _ ·)
        fun hag ↦ (notMem_support_iff.mp haf).trans (notMem_support_iff.mp hag).symm,
      fun H _ _ ↦ congr($H _)⟩

theorem subtypeDomain_eq_zero_iff' {f : α →₀ M} : f.subtypeDomain p = 0 ↔ ∀ x, p x → f x = 0 :=
  subtypeDomain_eq_iff_forall (g := 0)

theorem subtypeDomain_eq_zero_iff {f : α →₀ M} (hf : ∀ x ∈ f.support, p x) :
    f.subtypeDomain p = 0 ↔ f = 0 :=
  subtypeDomain_eq_iff (g := 0) hf (by simp)

@[to_additive]
theorem prod_subtypeDomain_index [CommMonoid N] {v : α →₀ M} {h : α → M → N}
    (hp : ∀ x ∈ v.support, p x) : (v.subtypeDomain p).prod (fun a b ↦ h a b) = v.prod h := by
  refine Finset.prod_bij (fun p _ ↦ p) ?_ ?_ ?_ ?_ <;> aesop

end Zero

section AddZeroClass

variable [AddZeroClass M] {p : α → Prop} {v v' : α →₀ M}

@[simp]
theorem subtypeDomain_add {v v' : α →₀ M} :
    (v + v').subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p :=
  ext fun _ => rfl

/-- `subtypeDomain` but as an `AddMonoidHom`. -/
def subtypeDomainAddMonoidHom : (α →₀ M) →+ Subtype p →₀ M where
  toFun := subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' _ _ := subtypeDomain_add

/-- `Finsupp.filter` as an `AddMonoidHom`. -/
def filterAddHom (p : α → Prop) [DecidablePred p] : (α →₀ M) →+ α →₀ M where
  toFun := filter p
  map_zero' := filter_zero p
  map_add' f g := DFunLike.coe_injective <| by
    simp only [filter_eq_indicator, coe_add]
    exact Set.indicator_add { x | p x } f g

@[simp]
theorem filter_add [DecidablePred p] {v v' : α →₀ M} :
    (v + v').filter p = v.filter p + v'.filter p :=
  (filterAddHom p).map_add v v'

end AddZeroClass

section CommMonoid

variable [AddCommMonoid M] {p : α → Prop}

theorem subtypeDomain_sum {s : Finset ι} {h : ι → α →₀ M} :
    (∑ c ∈ s, h c).subtypeDomain p = ∑ c ∈ s, (h c).subtypeDomain p :=
  map_sum subtypeDomainAddMonoidHom _ s

theorem subtypeDomain_finsupp_sum [Zero N] {s : β →₀ N} {h : β → N → α →₀ M} :
    (s.sum h).subtypeDomain p = s.sum fun c d => (h c d).subtypeDomain p :=
  subtypeDomain_sum

theorem filter_sum [DecidablePred p] (s : Finset ι) (f : ι → α →₀ M) :
    (∑ a ∈ s, f a).filter p = ∑ a ∈ s, filter p (f a) :=
  map_sum (filterAddHom p) f s

theorem filter_eq_sum (p : α → Prop) [DecidablePred p] (f : α →₀ M) :
    f.filter p = ∑ i ∈ f.support.filter p, single i (f i) :=
  (f.filter p).sum_single.symm.trans <|
    Finset.sum_congr rfl fun x hx => by
      rw [filter_apply_pos _ _ (mem_filter.1 hx).2]

end CommMonoid

section Group

variable [AddGroup G] {p : α → Prop} {v v' : α →₀ G}

@[simp]
theorem subtypeDomain_neg : (-v).subtypeDomain p = -v.subtypeDomain p :=
  ext fun _ => rfl

@[simp]
theorem subtypeDomain_sub : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p :=
  ext fun _ => rfl

@[simp]
theorem filter_neg (p : α → Prop) [DecidablePred p] (f : α →₀ G) : filter p (-f) = -filter p f :=
  (filterAddHom p : (_ →₀ G) →+ _).map_neg f

@[simp]
theorem filter_sub (p : α → Prop) [DecidablePred p] (f₁ f₂ : α →₀ G) :
    filter p (f₁ - f₂) = filter p f₁ - filter p f₂ :=
  (filterAddHom p : (_ →₀ G) →+ _).map_sub f₁ f₂

end Group

end SubtypeDomain

theorem mem_support_multiset_sum [AddCommMonoid M] {s : Multiset (α →₀ M)} (a : α) :
    a ∈ s.sum.support → ∃ f ∈ s, a ∈ (f : α →₀ M).support :=
  Multiset.induction_on s (fun h => False.elim (by simp at h))
    (by
      intro f s ih ha
      by_cases h : a ∈ f.support
      · exact ⟨f, Multiset.mem_cons_self _ _, h⟩
      · simp only [Multiset.sum_cons, mem_support_iff, add_apply, notMem_support_iff.1 h,
          zero_add] at ha
        rcases ih (mem_support_iff.2 ha) with ⟨f', h₀, h₁⟩
        exact ⟨f', Multiset.mem_cons_of_mem h₀, h₁⟩)

theorem mem_support_finset_sum [AddCommMonoid M] {s : Finset ι} {h : ι → α →₀ M} (a : α)
    (ha : a ∈ (∑ c ∈ s, h c).support) : ∃ c ∈ s, a ∈ (h c).support :=
  let ⟨_, hf, hfa⟩ := mem_support_multiset_sum a ha
  let ⟨c, hc, Eq⟩ := Multiset.mem_map.1 hf
  ⟨c, hc, Eq.symm ▸ hfa⟩

/-! ### Declarations about `curry` and `uncurry` -/


section Uncurry

variable [Zero M]

/-- Given a finitely supported function `f` from `α` to the type of
finitely supported functions from `β` to `M`,
`uncurry f` is the "uncurried" finitely supported function from `α × β` to `M`. -/
protected def uncurry (f : α →₀ β →₀ M) : α × β →₀ M where
  toFun x := f x.1 x.2
  support := f.support.disjiUnion (fun a ↦ (f a).support.map <| .sectR a _) <| by
    intro a₁ _ a₂ _ hne
    simp [Finset.disjoint_iff_ne, hne]
  mem_support_toFun := by aesop

protected theorem uncurry_apply (f : α →₀ β →₀ M) (x : α × β) : f.uncurry x = f x.1 x.2 := rfl

@[simp]
protected theorem uncurry_apply_pair (f : α →₀ β →₀ M) (a : α) (b : β) :
    f.uncurry (a, b) = f a b :=
  rfl

@[simp]
lemma uncurry_single (a : α) (b : β) (m : M) :
    (single a (single b m)).uncurry = single (a, b) m := by
  ext ⟨x, y⟩
  rcases eq_or_ne a x with rfl | hne <;> classical simp [single_apply, *]

theorem sum_uncurry_index [AddCommMonoid N] (f : α →₀ β →₀ M) (g : α × β → M → N) :
    f.uncurry.sum (fun p c => g p c) = f.sum fun a f => f.sum fun b ↦ g (a, b) := by
  simp only [Finsupp.sum, Finsupp.uncurry, Finset.sum_disjiUnion]
  simp

theorem sum_uncurry_index' [AddCommMonoid N] (f : α →₀ β →₀ M) (g : α → β → M → N) :
    f.uncurry.sum (fun p c => g p.1 p.2 c) = f.sum fun a f => f.sum (g a) :=
  sum_uncurry_index ..

end Uncurry

section Curry

variable [DecidableEq α] [Zero M]

/-- Given a finitely supported function `f` from a product type `α × β` to `γ`,
`curry f` is the "curried" finitely supported function from `α` to the type of
finitely supported functions from `β` to `γ`. -/
protected def curry (f : α × β →₀ M) : α →₀ β →₀ M where
  toFun a :=
    { toFun b := f (a, b)
      support := f.support.filterMap (fun x ↦ if x.1 = a then x.2 else none) <| by simp +contextual
      mem_support_toFun := by simp }
  support := f.support.image Prod.fst
  mem_support_toFun := by simp [DFunLike.ext_iff]

@[simp]
theorem curry_apply (f : α × β →₀ M) (x : α) (y : β) : f.curry x y = f (x, y) := rfl

@[simp]
theorem support_curry (f : α × β →₀ M) : f.curry.support = f.support.image Prod.fst :=
  rfl

@[simp]
theorem curry_uncurry (f : α →₀ β →₀ M) : f.uncurry.curry = f := by
  ext a b
  simp

@[simp]
theorem uncurry_curry (f : α × β →₀ M) : f.curry.uncurry = f := by
  ext ⟨a, b⟩
  simp

@[simp]
lemma curry_single (a : α × β) (m : M) :
    (single a m).curry = single a.1 (single a.2 m) := by
  rw [← curry_uncurry (single _ _), uncurry_single]

theorem sum_curry_index [AddCommMonoid N] (f : α × β →₀ M) (g : α → β → M → N) :
    (f.curry.sum fun a f => f.sum (g a)) = f.sum fun p c => g p.1 p.2 c := by
  rw [← sum_uncurry_index', uncurry_curry]

/-- `finsuppProdEquiv` defines the `Equiv` between `((α × β) →₀ M)` and `(α →₀ (β →₀ M))` given by
currying and uncurrying. -/
@[simps]
def finsuppProdEquiv : (α × β →₀ M) ≃ (α →₀ β →₀ M) where
  toFun := Finsupp.curry
  invFun := Finsupp.uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

theorem filter_curry (f : α × β →₀ M) (p : α → Prop) [DecidablePred p] :
    (f.filter fun a : α × β => p a.1).curry = f.curry.filter p := by
  ext a b
  simp [filter_apply, apply_ite (DFunLike.coe · b)]

end Curry

/-! ### Declarations about finitely supported functions whose support is a `Sum` type -/


section Sum

/-- `Finsupp.sumElim f g` maps `inl x` to `f x` and `inr y` to `g y`. -/
@[simps support]
def sumElim {α β γ : Type*} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) : α ⊕ β →₀ γ where
  support := f.support.disjSum g.support
  toFun := Sum.elim f g
  mem_support_toFun := by simp

@[simp, norm_cast]
theorem coe_sumElim {α β γ : Type*} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) :
    ⇑(sumElim f g) = Sum.elim f g :=
  rfl

theorem sumElim_apply {α β γ : Type*} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) (x : α ⊕ β) :
    sumElim f g x = Sum.elim f g x :=
  rfl

theorem sumElim_inl {α β γ : Type*} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) (x : α) :
    sumElim f g (Sum.inl x) = f x :=
  rfl

theorem sumElim_inr {α β γ : Type*} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) (x : β) :
    sumElim f g (Sum.inr x) = g x :=
  rfl

@[to_additive]
lemma prod_sumElim {ι₁ ι₂ α M : Type*} [Zero α] [CommMonoid M]
    (f₁ : ι₁ →₀ α) (f₂ : ι₂ →₀ α) (g : ι₁ ⊕ ι₂ → α → M) :
    (f₁.sumElim f₂).prod g = f₁.prod (g ∘ Sum.inl) * f₂.prod (g ∘ Sum.inr) := by
  simp [Finsupp.prod, Finset.prod_disj_sum]

/-- The equivalence between `(α ⊕ β) →₀ γ` and `(α →₀ γ) × (β →₀ γ)`.

This is the `Finsupp` version of `Equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symm_apply]
def sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] : (α ⊕ β →₀ γ) ≃ (α →₀ γ) × (β →₀ γ) where
  toFun f :=
    ⟨f.comapDomain Sum.inl Sum.inl_injective.injOn,
      f.comapDomain Sum.inr Sum.inr_injective.injOn⟩
  invFun fg := sumElim fg.1 fg.2
  left_inv f := by
    ext ab
    rcases ab with a | b <;> simp
  right_inv fg := by ext <;> simp

theorem fst_sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] (f : α ⊕ β →₀ γ) (x : α) :
    (sumFinsuppEquivProdFinsupp f).1 x = f (Sum.inl x) :=
  rfl

theorem snd_sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] (f : α ⊕ β →₀ γ) (y : β) :
    (sumFinsuppEquivProdFinsupp f).2 y = f (Sum.inr y) :=
  rfl

theorem sumFinsuppEquivProdFinsupp_symm_inl {α β γ : Type*} [Zero γ] (fg : (α →₀ γ) × (β →₀ γ))
    (x : α) : (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl

theorem sumFinsuppEquivProdFinsupp_symm_inr {α β γ : Type*} [Zero γ] (fg : (α →₀ γ) × (β →₀ γ))
    (y : β) : (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl

variable [AddMonoid M]

/-- The additive equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `Finsupp` version of `Equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps! apply symm_apply]
def sumFinsuppAddEquivProdFinsupp {α β : Type*} : (α ⊕ β →₀ M) ≃+ (α →₀ M) × (β →₀ M) :=
  { sumFinsuppEquivProdFinsupp with
    map_add' := by
      intros
      ext <;>
        simp only [Equiv.toFun_as_coe, Prod.fst_add, Prod.snd_add, add_apply,
          snd_sumFinsuppEquivProdFinsupp, fst_sumFinsuppEquivProdFinsupp] }

theorem fst_sumFinsuppAddEquivProdFinsupp {α β : Type*} (f : α ⊕ β →₀ M) (x : α) :
    (sumFinsuppAddEquivProdFinsupp f).1 x = f (Sum.inl x) :=
  rfl

theorem snd_sumFinsuppAddEquivProdFinsupp {α β : Type*} (f : α ⊕ β →₀ M) (y : β) :
    (sumFinsuppAddEquivProdFinsupp f).2 y = f (Sum.inr y) :=
  rfl

theorem sumFinsuppAddEquivProdFinsupp_symm_inl {α β : Type*} (fg : (α →₀ M) × (β →₀ M)) (x : α) :
    (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl

theorem sumFinsuppAddEquivProdFinsupp_symm_inr {α β : Type*} (fg : (α →₀ M) × (β →₀ M)) (y : β) :
    (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl

end Sum

section

variable [Zero R]

/-- The `Finsupp` version of `Pi.unique`. -/
instance uniqueOfRight [Subsingleton R] : Unique (α →₀ R) :=
  DFunLike.coe_injective.unique

/-- The `Finsupp` version of `Pi.uniqueOfIsEmpty`. -/
instance uniqueOfLeft [IsEmpty α] : Unique (α →₀ R) :=
  DFunLike.coe_injective.unique

end

section
variable {M : Type*} [Zero M] {P : α → Prop} [DecidablePred P]

/-- Combine finitely supported functions over `{a // P a}` and `{a // ¬P a}`, by case-splitting on
`P a`. -/
@[simps]
def piecewise (f : Subtype P →₀ M) (g : {a // ¬ P a} →₀ M) : α →₀ M where
  toFun a := if h : P a then f ⟨a, h⟩ else g ⟨a, h⟩
  support := (f.support.map (.subtype _)).disjUnion (g.support.map (.subtype _)) <| by
    simp_rw [Finset.disjoint_left, mem_map, forall_exists_index, Embedding.coe_subtype,
      Subtype.forall, Subtype.exists]
    rintro _ a ha ⟨-, rfl⟩ ⟨b, hb, -, rfl⟩
    exact hb ha
  mem_support_toFun a := by
    by_cases ha : P a <;> simp [ha]

@[simp]
theorem subtypeDomain_piecewise (f : Subtype P →₀ M) (g : {a // ¬ P a} →₀ M) :
    subtypeDomain P (f.piecewise g) = f :=
  Finsupp.ext fun a => dif_pos a.prop

@[simp]
theorem subtypeDomain_not_piecewise (f : Subtype P →₀ M) (g : {a // ¬ P a} →₀ M) :
    subtypeDomain (¬P ·) (f.piecewise g) = g :=
  Finsupp.ext fun a => dif_neg a.prop

/-- Extend the domain of a `Finsupp` by using `0` where `P x` does not hold. -/
@[simps! support toFun]
def extendDomain (f : Subtype P →₀ M) : α →₀ M := piecewise f 0

theorem extendDomain_eq_embDomain_subtype (f : Subtype P →₀ M) :
    extendDomain f = embDomain (.subtype _) f := by
  ext a
  by_cases h : P a
  · refine Eq.trans ?_ (embDomain_apply (.subtype P) f (Subtype.mk a h)).symm
    simp [h]
  · rw [embDomain_notin_range, extendDomain_toFun, dif_neg h]
    simp [h]

theorem support_extendDomain_subset (f : Subtype P →₀ M) :
    ↑(f.extendDomain).support ⊆ {x | P x} := by
  intro x
  rw [extendDomain_support, mem_coe, mem_map, Embedding.coe_subtype]
  rintro ⟨x, -, rfl⟩
  exact x.prop

@[simp]
theorem subtypeDomain_extendDomain (f : Subtype P →₀ M) :
    subtypeDomain P f.extendDomain = f :=
  subtypeDomain_piecewise _ _

theorem extendDomain_subtypeDomain (f : α →₀ M) (hf : ∀ a ∈ f.support, P a) :
    (subtypeDomain P f).extendDomain = f := by
  ext a
  by_cases h : P a
  · exact dif_pos h
  · dsimp [extendDomain_toFun]
    rw [if_neg h, eq_comm, ← notMem_support_iff]
    refine mt ?_ h
    exact @hf _

@[simp]
theorem extendDomain_single (a : Subtype P) (m : M) :
    (single a m).extendDomain = single a.val m := by
  ext a'
  dsimp only [extendDomain_toFun]
  obtain rfl | ha := eq_or_ne a.val a'
  · simp_rw [single_eq_same, dif_pos a.prop]
  · simp_rw [single_eq_of_ne ha, dite_eq_right_iff]
    intro h
    rw [single_eq_of_ne]
    simp [Subtype.ext_iff, ha]

end

/-- Given an `AddCommMonoid M` and `s : Set α`, `restrictSupportEquiv s M` is the `Equiv`
between the subtype of finitely supported functions with support contained in `s` and
the type of finitely supported functions from `s`. -/
-- TODO: add [DecidablePred (· ∈ s)] as an assumption
@[simps] def restrictSupportEquiv (s : Set α) (M : Type*) [AddCommMonoid M] :
    { f : α →₀ M // ↑f.support ⊆ s } ≃ (s →₀ M) where
  toFun f := subtypeDomain (· ∈ s) f.1
  invFun f := letI := Classical.decPred (· ∈ s); ⟨f.extendDomain, support_extendDomain_subset _⟩
  left_inv f :=
    letI := Classical.decPred (· ∈ s); Subtype.ext <| extendDomain_subtypeDomain f.1 f.prop
  right_inv _ := letI := Classical.decPred (· ∈ s); subtypeDomain_extendDomain _

/-- Given `AddCommMonoid M` and `e : α ≃ β`, `domCongr e` is the corresponding `Equiv` between
`α →₀ M` and `β →₀ M`.

This is `Finsupp.equivCongrLeft` as an `AddEquiv`. -/
@[simps apply]
protected def domCongr [AddCommMonoid M] (e : α ≃ β) : (α →₀ M) ≃+ (β →₀ M) where
  toFun := equivMapDomain e
  invFun := equivMapDomain e.symm
  left_inv v := by
    simp only [← equivMapDomain_trans, Equiv.self_trans_symm]
    exact equivMapDomain_refl _
  right_inv := by
    intro v
    simp only [← equivMapDomain_trans, Equiv.symm_trans_self]
    exact equivMapDomain_refl _
  map_add' a b := by simp only [equivMapDomain_eq_mapDomain]; exact mapDomain_add

@[simp]
theorem domCongr_refl [AddCommMonoid M] :
    Finsupp.domCongr (Equiv.refl α) = AddEquiv.refl (α →₀ M) :=
  AddEquiv.ext fun _ => equivMapDomain_refl _

@[simp]
theorem domCongr_symm [AddCommMonoid M] (e : α ≃ β) :
    (Finsupp.domCongr e).symm = (Finsupp.domCongr e.symm : (β →₀ M) ≃+ (α →₀ M)) :=
  AddEquiv.ext fun _ => rfl

@[simp]
theorem domCongr_trans [AddCommMonoid M] (e : α ≃ β) (f : β ≃ γ) :
    (Finsupp.domCongr e).trans (Finsupp.domCongr f) =
      (Finsupp.domCongr (e.trans f) : (α →₀ M) ≃+ _) :=
  AddEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm

end Finsupp

namespace Finsupp

/-! ### Declarations about sigma types -/


section Sigma

variable {αs : ι → Type*} [Zero M] (l : (Σ i, αs i) →₀ M)

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `M` and
an index element `i : ι`, `split l i` is the `i`th component of `l`,
a finitely supported function from `as i` to `M`.

This is the `Finsupp` version of `Sigma.curry`.
-/
def split (i : ι) : αs i →₀ M :=
  l.comapDomain (Sigma.mk i) fun _ _ _ _ hx => heq_iff_eq.1 (Sigma.mk.inj hx).2

theorem split_apply (i : ι) (x : αs i) : split l i x = l ⟨i, x⟩ := by
  dsimp only [split]
  rw [comapDomain_apply]

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `β`,
`split_support l` is the finset of indices in `ι` that appear in the support of `l`. -/
def splitSupport (l : (Σ i, αs i) →₀ M) : Finset ι :=
  haveI := Classical.decEq ι
  l.support.image Sigma.fst

theorem mem_splitSupport_iff_nonzero (i : ι) : i ∈ splitSupport l ↔ split l i ≠ 0 := by
  classical rw [splitSupport, mem_image, Ne, ← support_eq_empty, ← Ne,
    ← Finset.nonempty_iff_ne_empty, split, comapDomain, Finset.Nonempty]
  simp only [exists_prop, Finset.mem_preimage, exists_and_right, exists_eq_right, mem_support_iff,
    Sigma.exists, Ne]

/-- Given `l`, a finitely supported function from the sigma type `Σ i, αs i` to `β` and
an `ι`-indexed family `g` of functions from `(αs i →₀ β)` to `γ`, `split_comp` defines a
finitely supported function from the index type `ι` to `γ` given by composing `g i` with
`split l i`. -/
def splitComp [Zero N] (g : ∀ i, (αs i →₀ M) → N) (hg : ∀ i x, x = 0 ↔ g i x = 0) : ι →₀ N where
  support := splitSupport l
  toFun i := g i (split l i)
  mem_support_toFun := by
    intro i
    rw [mem_splitSupport_iff_nonzero, not_iff_not, hg]

theorem sigma_support : l.support = l.splitSupport.sigma fun i => (l.split i).support := by
  simp only [Finset.ext_iff, splitSupport, split, comapDomain, mem_image, mem_preimage,
    Sigma.forall, mem_sigma]
  tauto

theorem sigma_sum [AddCommMonoid N] (f : (Σ i : ι, αs i) → M → N) :
    l.sum f = ∑ i ∈ splitSupport l, (split l i).sum fun (a : αs i) b => f ⟨i, a⟩ b := by
  simp only [sum, sigma_support, sum_sigma, split_apply]

variable {η : Type*} [Fintype η] {ιs : η → Type*} [Zero α]

/-- On a `Fintype η`, `Finsupp.split` is an equivalence between `(Σ (j : η), ιs j) →₀ α`
and `Π j, (ιs j →₀ α)`.

This is the `Finsupp` version of `Equiv.Pi_curry`. -/
noncomputable def sigmaFinsuppEquivPiFinsupp : ((Σ j, ιs j) →₀ α) ≃ ∀ j, ιs j →₀ α where
  toFun := split
  invFun f :=
    onFinset (Finset.univ.sigma fun j => (f j).support) (fun ji => f ji.1 ji.2) fun _ hg =>
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, mem_support_iff.mpr hg⟩
  left_inv f := by
    ext
    simp [split]
  right_inv f := by
    ext
    simp [split]

@[simp]
theorem sigmaFinsuppEquivPiFinsupp_apply (f : (Σ j, ιs j) →₀ α) (j i) :
    sigmaFinsuppEquivPiFinsupp f j i = f ⟨j, i⟩ :=
  rfl

/-- On a `Fintype η`, `Finsupp.split` is an additive equivalence between
`(Σ (j : η), ιs j) →₀ α` and `Π j, (ιs j →₀ α)`.

This is the `AddEquiv` version of `Finsupp.sigmaFinsuppEquivPiFinsupp`.
-/
noncomputable def sigmaFinsuppAddEquivPiFinsupp {α : Type*} {ιs : η → Type*} [AddMonoid α] :
    ((Σ j, ιs j) →₀ α) ≃+ ∀ j, ιs j →₀ α :=
  { sigmaFinsuppEquivPiFinsupp with
    map_add' := fun f g => by
      ext
      simp }

@[simp]
theorem sigmaFinsuppAddEquivPiFinsupp_apply {α : Type*} {ιs : η → Type*} [AddMonoid α]
    (f : (Σ j, ιs j) →₀ α) (j i) : sigmaFinsuppAddEquivPiFinsupp f j i = f ⟨j, i⟩ :=
  rfl

end Sigma

end Finsupp

set_option linter.style.longFile 1700
