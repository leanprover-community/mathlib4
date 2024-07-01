/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison
-/
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Regular.SMul
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Rat.BigOperators
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Data.Set.Subsingleton

#align_import data.finsupp.basic from "leanprover-community/mathlib"@"f69db8cecc668e2d5894d7e9bfc491da60db3b9f"

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
#align finsupp.graph Finsupp.graph

theorem mk_mem_graph_iff {a : α} {m : M} {f : α →₀ M} : (a, m) ∈ f.graph ↔ f a = m ∧ m ≠ 0 := by
  simp_rw [graph, mem_map, mem_support_iff]
  constructor
  · rintro ⟨b, ha, rfl, -⟩
    exact ⟨rfl, ha⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩
#align finsupp.mk_mem_graph_iff Finsupp.mk_mem_graph_iff

@[simp]
theorem mem_graph_iff {c : α × M} {f : α →₀ M} : c ∈ f.graph ↔ f c.1 = c.2 ∧ c.2 ≠ 0 := by
  cases c
  exact mk_mem_graph_iff
#align finsupp.mem_graph_iff Finsupp.mem_graph_iff

theorem mk_mem_graph (f : α →₀ M) {a : α} (ha : a ∈ f.support) : (a, f a) ∈ f.graph :=
  mk_mem_graph_iff.2 ⟨rfl, mem_support_iff.1 ha⟩
#align finsupp.mk_mem_graph Finsupp.mk_mem_graph

theorem apply_eq_of_mem_graph {a : α} {m : M} {f : α →₀ M} (h : (a, m) ∈ f.graph) : f a = m :=
  (mem_graph_iff.1 h).1
#align finsupp.apply_eq_of_mem_graph Finsupp.apply_eq_of_mem_graph

@[simp 1100] -- Porting note: change priority to appease `simpNF`
theorem not_mem_graph_snd_zero (a : α) (f : α →₀ M) : (a, (0 : M)) ∉ f.graph := fun h =>
  (mem_graph_iff.1 h).2.irrefl
#align finsupp.not_mem_graph_snd_zero Finsupp.not_mem_graph_snd_zero

@[simp]
theorem image_fst_graph [DecidableEq α] (f : α →₀ M) : f.graph.image Prod.fst = f.support := by
  classical simp only [graph, map_eq_image, image_image, Embedding.coeFn_mk, (· ∘ ·), image_id']
#align finsupp.image_fst_graph Finsupp.image_fst_graph

theorem graph_injective (α M) [Zero M] : Injective (@graph α M _) := by
  intro f g h
  classical
    have hsup : f.support = g.support := by rw [← image_fst_graph, h, image_fst_graph]
    refine ext_iff'.2 ⟨hsup, fun x hx => apply_eq_of_mem_graph <| h.symm ▸ ?_⟩
    exact mk_mem_graph _ (hsup ▸ hx)
#align finsupp.graph_injective Finsupp.graph_injective

@[simp]
theorem graph_inj {f g : α →₀ M} : f.graph = g.graph ↔ f = g :=
  (graph_injective α M).eq_iff
#align finsupp.graph_inj Finsupp.graph_inj

@[simp]
theorem graph_zero : graph (0 : α →₀ M) = ∅ := by simp [graph]
#align finsupp.graph_zero Finsupp.graph_zero

@[simp]
theorem graph_eq_empty {f : α →₀ M} : f.graph = ∅ ↔ f = 0 :=
  (graph_injective α M).eq_iff' graph_zero
#align finsupp.graph_eq_empty Finsupp.graph_eq_empty

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
#align finsupp.map_range.equiv Finsupp.mapRange.equiv

@[simp]
theorem mapRange.equiv_refl : mapRange.equiv (Equiv.refl M) rfl rfl = Equiv.refl (α →₀ M) :=
  Equiv.ext mapRange_id
#align finsupp.map_range.equiv_refl Finsupp.mapRange.equiv_refl

theorem mapRange.equiv_trans (f : M ≃ N) (hf : f 0 = 0) (hf') (f₂ : N ≃ P) (hf₂ : f₂ 0 = 0) (hf₂') :
    (mapRange.equiv (f.trans f₂) (by rw [Equiv.trans_apply, hf, hf₂])
          (by rw [Equiv.symm_trans_apply, hf₂', hf']) :
        (α →₀ _) ≃ _) =
      (mapRange.equiv f hf hf').trans (mapRange.equiv f₂ hf₂ hf₂') :=
  Equiv.ext <| mapRange_comp f₂ hf₂ f hf ((congrArg f₂ hf).trans hf₂)
#align finsupp.map_range.equiv_trans Finsupp.mapRange.equiv_trans

@[simp]
theorem mapRange.equiv_symm (f : M ≃ N) (hf hf') :
    ((mapRange.equiv f hf hf').symm : (α →₀ _) ≃ _) = mapRange.equiv f.symm hf' hf :=
  Equiv.ext fun _ => rfl
#align finsupp.map_range.equiv_symm Finsupp.mapRange.equiv_symm

end Equiv

section ZeroHom

variable [Zero M] [Zero N] [Zero P]

/-- Composition with a fixed zero-preserving homomorphism is itself a zero-preserving homomorphism
on functions. -/
@[simps]
def mapRange.zeroHom (f : ZeroHom M N) : ZeroHom (α →₀ M) (α →₀ N) where
  toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
  map_zero' := mapRange_zero
#align finsupp.map_range.zero_hom Finsupp.mapRange.zeroHom

@[simp]
theorem mapRange.zeroHom_id : mapRange.zeroHom (ZeroHom.id M) = ZeroHom.id (α →₀ M) :=
  ZeroHom.ext mapRange_id
#align finsupp.map_range.zero_hom_id Finsupp.mapRange.zeroHom_id

theorem mapRange.zeroHom_comp (f : ZeroHom N P) (f₂ : ZeroHom M N) :
    (mapRange.zeroHom (f.comp f₂) : ZeroHom (α →₀ _) _) =
      (mapRange.zeroHom f).comp (mapRange.zeroHom f₂) :=
  ZeroHom.ext <| mapRange_comp f (map_zero f) f₂ (map_zero f₂) (by simp only [comp_apply, map_zero])
#align finsupp.map_range.zero_hom_comp Finsupp.mapRange.zeroHom_comp

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
  map_add' a b := by dsimp only; exact mapRange_add f.map_add _ _; -- Porting note: `dsimp` needed
#align finsupp.map_range.add_monoid_hom Finsupp.mapRange.addMonoidHom

@[simp]
theorem mapRange.addMonoidHom_id :
    mapRange.addMonoidHom (AddMonoidHom.id M) = AddMonoidHom.id (α →₀ M) :=
  AddMonoidHom.ext mapRange_id
#align finsupp.map_range.add_monoid_hom_id Finsupp.mapRange.addMonoidHom_id

theorem mapRange.addMonoidHom_comp (f : N →+ P) (f₂ : M →+ N) :
    (mapRange.addMonoidHom (f.comp f₂) : (α →₀ _) →+ _) =
      (mapRange.addMonoidHom f).comp (mapRange.addMonoidHom f₂) :=
  AddMonoidHom.ext <|
    mapRange_comp f (map_zero f) f₂ (map_zero f₂) (by simp only [comp_apply, map_zero])
#align finsupp.map_range.add_monoid_hom_comp Finsupp.mapRange.addMonoidHom_comp

@[simp]
theorem mapRange.addMonoidHom_toZeroHom (f : M →+ N) :
    (mapRange.addMonoidHom f).toZeroHom = (mapRange.zeroHom f.toZeroHom : ZeroHom (α →₀ _) _) :=
  ZeroHom.ext fun _ => rfl
#align finsupp.map_range.add_monoid_hom_to_zero_hom Finsupp.mapRange.addMonoidHom_toZeroHom

theorem mapRange_multiset_sum (f : F) (m : Multiset (α →₀ M)) :
    mapRange f (map_zero f) m.sum = (m.map fun x => mapRange f (map_zero f) x).sum :=
  (mapRange.addMonoidHom (f : M →+ N) : (α →₀ _) →+ _).map_multiset_sum _
#align finsupp.map_range_multiset_sum Finsupp.mapRange_multiset_sum

theorem mapRange_finset_sum (f : F) (s : Finset ι) (g : ι → α →₀ M) :
    mapRange f (map_zero f) (∑ x ∈ s, g x) = ∑ x ∈ s, mapRange f (map_zero f) (g x) :=
  map_sum (mapRange.addMonoidHom (f : M →+ N)) _ _
#align finsupp.map_range_finset_sum Finsupp.mapRange_finset_sum

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
#align finsupp.map_range.add_equiv Finsupp.mapRange.addEquiv

@[simp]
theorem mapRange.addEquiv_refl : mapRange.addEquiv (AddEquiv.refl M) = AddEquiv.refl (α →₀ M) :=
  AddEquiv.ext mapRange_id
#align finsupp.map_range.add_equiv_refl Finsupp.mapRange.addEquiv_refl

theorem mapRange.addEquiv_trans (f : M ≃+ N) (f₂ : N ≃+ P) :
    (mapRange.addEquiv (f.trans f₂) : (α →₀ M) ≃+ (α →₀ P)) =
      (mapRange.addEquiv f).trans (mapRange.addEquiv f₂) :=
  AddEquiv.ext (mapRange_comp _ f₂.map_zero _ f.map_zero (by simp))
#align finsupp.map_range.add_equiv_trans Finsupp.mapRange.addEquiv_trans

@[simp]
theorem mapRange.addEquiv_symm (f : M ≃+ N) :
    ((mapRange.addEquiv f).symm : (α →₀ _) ≃+ _) = mapRange.addEquiv f.symm :=
  AddEquiv.ext fun _ => rfl
#align finsupp.map_range.add_equiv_symm Finsupp.mapRange.addEquiv_symm

@[simp]
theorem mapRange.addEquiv_toAddMonoidHom (f : M ≃+ N) :
    ((mapRange.addEquiv f : (α →₀ _) ≃+ _) : _ →+ _) =
      (mapRange.addMonoidHom f.toAddMonoidHom : (α →₀ _) →+ _) :=
  AddMonoidHom.ext fun _ => rfl
#align finsupp.map_range.add_equiv_to_add_monoid_hom Finsupp.mapRange.addEquiv_toAddMonoidHom

@[simp]
theorem mapRange.addEquiv_toEquiv (f : M ≃+ N) :
    ↑(mapRange.addEquiv f : (α →₀ _) ≃+ _) =
      (mapRange.equiv (f : M ≃ N) f.map_zero f.symm.map_zero : (α →₀ _) ≃ _) :=
  Equiv.ext fun _ => rfl
#align finsupp.map_range.add_equiv_to_equiv Finsupp.mapRange.addEquiv_toEquiv

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
#align finsupp.equiv_map_domain Finsupp.equivMapDomain

@[simp]
theorem equivMapDomain_apply (f : α ≃ β) (l : α →₀ M) (b : β) :
    equivMapDomain f l b = l (f.symm b) :=
  rfl
#align finsupp.equiv_map_domain_apply Finsupp.equivMapDomain_apply

theorem equivMapDomain_symm_apply (f : α ≃ β) (l : β →₀ M) (a : α) :
    equivMapDomain f.symm l a = l (f a) :=
  rfl
#align finsupp.equiv_map_domain_symm_apply Finsupp.equivMapDomain_symm_apply

@[simp]
theorem equivMapDomain_refl (l : α →₀ M) : equivMapDomain (Equiv.refl _) l = l := by ext x; rfl
#align finsupp.equiv_map_domain_refl Finsupp.equivMapDomain_refl

theorem equivMapDomain_refl' : equivMapDomain (Equiv.refl _) = @id (α →₀ M) := by ext x; rfl
#align finsupp.equiv_map_domain_refl' Finsupp.equivMapDomain_refl'

theorem equivMapDomain_trans (f : α ≃ β) (g : β ≃ γ) (l : α →₀ M) :
    equivMapDomain (f.trans g) l = equivMapDomain g (equivMapDomain f l) := by ext x; rfl
#align finsupp.equiv_map_domain_trans Finsupp.equivMapDomain_trans

theorem equivMapDomain_trans' (f : α ≃ β) (g : β ≃ γ) :
    @equivMapDomain _ _ M _ (f.trans g) = equivMapDomain g ∘ equivMapDomain f := by ext x; rfl
#align finsupp.equiv_map_domain_trans' Finsupp.equivMapDomain_trans'

@[simp]
theorem equivMapDomain_single (f : α ≃ β) (a : α) (b : M) :
    equivMapDomain f (single a b) = single (f a) b := by
  classical
    ext x
    simp only [single_apply, Equiv.apply_eq_iff_eq_symm_apply, equivMapDomain_apply]
#align finsupp.equiv_map_domain_single Finsupp.equivMapDomain_single

@[simp]
theorem equivMapDomain_zero {f : α ≃ β} : equivMapDomain f (0 : α →₀ M) = (0 : β →₀ M) := by
  ext; simp only [equivMapDomain_apply, coe_zero, Pi.zero_apply]
#align finsupp.equiv_map_domain_zero Finsupp.equivMapDomain_zero

@[to_additive (attr := simp)]
theorem prod_equivMapDomain [CommMonoid N] (f : α ≃ β) (l : α →₀ M) (g : β → M → N):
    prod (equivMapDomain f l) g = prod l (fun a m => g (f a) m) := by
  simp [prod, equivMapDomain]

/-- Given `f : α ≃ β`, the finitely supported function spaces are also in bijection:
`(α →₀ M) ≃ (β →₀ M)`.

This is the finitely-supported version of `Equiv.piCongrLeft`. -/
def equivCongrLeft (f : α ≃ β) : (α →₀ M) ≃ (β →₀ M) := by
  refine ⟨equivMapDomain f, equivMapDomain f.symm, fun f => ?_, fun f => ?_⟩ <;> ext x <;>
    simp only [equivMapDomain_apply, Equiv.symm_symm, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]
#align finsupp.equiv_congr_left Finsupp.equivCongrLeft

@[simp]
theorem equivCongrLeft_apply (f : α ≃ β) (l : α →₀ M) : equivCongrLeft f l = equivMapDomain f l :=
  rfl
#align finsupp.equiv_congr_left_apply Finsupp.equivCongrLeft_apply

@[simp]
theorem equivCongrLeft_symm (f : α ≃ β) :
    (@equivCongrLeft _ _ M _ f).symm = equivCongrLeft f.symm :=
  rfl
#align finsupp.equiv_congr_left_symm Finsupp.equivCongrLeft_symm

end Finsupp

end EquivCongrLeft

section CastFinsupp

variable [Zero M] (f : α →₀ M)

namespace Nat

@[simp, norm_cast]
theorem cast_finsupp_prod [CommSemiring R] (g : α → M → ℕ) :
    (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b) :=
  Nat.cast_prod _ _
#align nat.cast_finsupp_prod Nat.cast_finsupp_prod

@[simp, norm_cast]
theorem cast_finsupp_sum [CommSemiring R] (g : α → M → ℕ) :
    (↑(f.sum g) : R) = f.sum fun a b => ↑(g a b) :=
  Nat.cast_sum _ _
#align nat.cast_finsupp_sum Nat.cast_finsupp_sum

end Nat

namespace Int

@[simp, norm_cast]
theorem cast_finsupp_prod [CommRing R] (g : α → M → ℤ) :
    (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b) :=
  Int.cast_prod _ _
#align int.cast_finsupp_prod Int.cast_finsupp_prod

@[simp, norm_cast]
theorem cast_finsupp_sum [CommRing R] (g : α → M → ℤ) :
    (↑(f.sum g) : R) = f.sum fun a b => ↑(g a b) :=
  Int.cast_sum _ _
#align int.cast_finsupp_sum Int.cast_finsupp_sum

end Int

namespace Rat

@[simp, norm_cast]
theorem cast_finsupp_sum [DivisionRing R] [CharZero R] (g : α → M → ℚ) :
    (↑(f.sum g) : R) = f.sum fun a b => ↑(g a b) :=
  cast_sum _ _
#align rat.cast_finsupp_sum Rat.cast_finsupp_sum

@[simp, norm_cast]
theorem cast_finsupp_prod [Field R] [CharZero R] (g : α → M → ℚ) :
    (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b) :=
  cast_prod _ _
#align rat.cast_finsupp_prod Rat.cast_finsupp_prod

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
#align finsupp.map_domain Finsupp.mapDomain

theorem mapDomain_apply {f : α → β} (hf : Function.Injective f) (x : α →₀ M) (a : α) :
    mapDomain f x (f a) = x a := by
  rw [mapDomain, sum_apply, sum_eq_single a, single_eq_same]
  · intro b _ hba
    exact single_eq_of_ne (hf.ne hba)
  · intro _
    rw [single_zero, coe_zero, Pi.zero_apply]
#align finsupp.map_domain_apply Finsupp.mapDomain_apply

theorem mapDomain_notin_range {f : α → β} (x : α →₀ M) (a : β) (h : a ∉ Set.range f) :
    mapDomain f x a = 0 := by
  rw [mapDomain, sum_apply, sum]
  exact Finset.sum_eq_zero fun a' _ => single_eq_of_ne fun eq => h <| eq ▸ Set.mem_range_self _
#align finsupp.map_domain_notin_range Finsupp.mapDomain_notin_range

@[simp]
theorem mapDomain_id : mapDomain id v = v :=
  sum_single _
#align finsupp.map_domain_id Finsupp.mapDomain_id

theorem mapDomain_comp {f : α → β} {g : β → γ} :
    mapDomain (g ∘ f) v = mapDomain g (mapDomain f v) := by
  refine ((sum_sum_index ?_ ?_).trans ?_).symm
  · intro
    exact single_zero _
  · intro
    exact single_add _
  refine sum_congr fun _ _ => sum_single_index ?_
  exact single_zero _
#align finsupp.map_domain_comp Finsupp.mapDomain_comp

@[simp]
theorem mapDomain_single {f : α → β} {a : α} {b : M} : mapDomain f (single a b) = single (f a) b :=
  sum_single_index <| single_zero _
#align finsupp.map_domain_single Finsupp.mapDomain_single

@[simp]
theorem mapDomain_zero {f : α → β} : mapDomain f (0 : α →₀ M) = (0 : β →₀ M) :=
  sum_zero_index
#align finsupp.map_domain_zero Finsupp.mapDomain_zero

theorem mapDomain_congr {f g : α → β} (h : ∀ x ∈ v.support, f x = g x) :
    v.mapDomain f = v.mapDomain g :=
  Finset.sum_congr rfl fun _ H => by simp only [h _ H]
#align finsupp.map_domain_congr Finsupp.mapDomain_congr

theorem mapDomain_add {f : α → β} : mapDomain f (v₁ + v₂) = mapDomain f v₁ + mapDomain f v₂ :=
  sum_add_index' (fun _ => single_zero _) fun _ => single_add _
#align finsupp.map_domain_add Finsupp.mapDomain_add

@[simp]
theorem mapDomain_equiv_apply {f : α ≃ β} (x : α →₀ M) (a : β) :
    mapDomain f x a = x (f.symm a) := by
  conv_lhs => rw [← f.apply_symm_apply a]
  exact mapDomain_apply f.injective _ _
#align finsupp.map_domain_equiv_apply Finsupp.mapDomain_equiv_apply

/-- `Finsupp.mapDomain` is an `AddMonoidHom`. -/
@[simps]
def mapDomain.addMonoidHom (f : α → β) : (α →₀ M) →+ β →₀ M where
  toFun := mapDomain f
  map_zero' := mapDomain_zero
  map_add' _ _ := mapDomain_add
#align finsupp.map_domain.add_monoid_hom Finsupp.mapDomain.addMonoidHom

@[simp]
theorem mapDomain.addMonoidHom_id : mapDomain.addMonoidHom id = AddMonoidHom.id (α →₀ M) :=
  AddMonoidHom.ext fun _ => mapDomain_id
#align finsupp.map_domain.add_monoid_hom_id Finsupp.mapDomain.addMonoidHom_id

theorem mapDomain.addMonoidHom_comp (f : β → γ) (g : α → β) :
    (mapDomain.addMonoidHom (f ∘ g) : (α →₀ M) →+ γ →₀ M) =
      (mapDomain.addMonoidHom f).comp (mapDomain.addMonoidHom g) :=
  AddMonoidHom.ext fun _ => mapDomain_comp
#align finsupp.map_domain.add_monoid_hom_comp Finsupp.mapDomain.addMonoidHom_comp

theorem mapDomain_finset_sum {f : α → β} {s : Finset ι} {v : ι → α →₀ M} :
    mapDomain f (∑ i ∈ s, v i) = ∑ i ∈ s, mapDomain f (v i) :=
  map_sum (mapDomain.addMonoidHom f) _ _
#align finsupp.map_domain_finset_sum Finsupp.mapDomain_finset_sum

theorem mapDomain_sum [Zero N] {f : α → β} {s : α →₀ N} {v : α → N → α →₀ M} :
    mapDomain f (s.sum v) = s.sum fun a b => mapDomain f (v a b) :=
  map_finsupp_sum (mapDomain.addMonoidHom f : (α →₀ M) →+ β →₀ M) _ _
#align finsupp.map_domain_sum Finsupp.mapDomain_sum

theorem mapDomain_support [DecidableEq β] {f : α → β} {s : α →₀ M} :
    (s.mapDomain f).support ⊆ s.support.image f :=
  Finset.Subset.trans support_sum <|
    Finset.Subset.trans (Finset.biUnion_mono fun a _ => support_single_subset) <| by
      rw [Finset.biUnion_singleton]
#align finsupp.map_domain_support Finsupp.mapDomain_support

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
    · rw [not_mem_support_iff.1 hax]
      refine Finset.sum_eq_zero fun i hi => if_neg ?_
      exact hf.ne (hS hi) ha (ne_of_mem_of_not_mem hi hax)
#align finsupp.map_domain_apply' Finsupp.mapDomain_apply'

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
#align finsupp.map_domain_support_of_inj_on Finsupp.mapDomain_support_of_injOn

theorem mapDomain_support_of_injective [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (s : α →₀ M) : (mapDomain f s).support = Finset.image f s.support :=
  mapDomain_support_of_injOn s hf.injOn
#align finsupp.map_domain_support_of_injective Finsupp.mapDomain_support_of_injective

@[to_additive]
theorem prod_mapDomain_index [CommMonoid N] {f : α → β} {s : α →₀ M} {h : β → M → N}
    (h_zero : ∀ b, h b 0 = 1) (h_add : ∀ b m₁ m₂, h b (m₁ + m₂) = h b m₁ * h b m₂) :
    (mapDomain f s).prod h = s.prod fun a m => h (f a) m :=
  (prod_sum_index h_zero h_add).trans <| prod_congr fun _ _ => prod_single_index (h_zero _)
#align finsupp.prod_map_domain_index Finsupp.prod_mapDomain_index
#align finsupp.sum_map_domain_index Finsupp.sum_mapDomain_index

-- Note that in `prod_mapDomain_index`, `M` is still an additive monoid,
-- so there is no analogous version in terms of `MonoidHom`.
/-- A version of `sum_mapDomain_index` that takes a bundled `AddMonoidHom`,
rather than separate linearity hypotheses.
-/
@[simp]
theorem sum_mapDomain_index_addMonoidHom [AddCommMonoid N] {f : α → β} {s : α →₀ M}
    (h : β → M →+ N) : ((mapDomain f s).sum fun b m => h b m) = s.sum fun a m => h (f a) m :=
  sum_mapDomain_index (fun b => (h b).map_zero) (fun b _ _ => (h b).map_add _ _)
#align finsupp.sum_map_domain_index_add_monoid_hom Finsupp.sum_mapDomain_index_addMonoidHom

theorem embDomain_eq_mapDomain (f : α ↪ β) (v : α →₀ M) : embDomain f v = mapDomain f v := by
  ext a
  by_cases h : a ∈ Set.range f
  · rcases h with ⟨a, rfl⟩
    rw [mapDomain_apply f.injective, embDomain_apply]
  · rw [mapDomain_notin_range, embDomain_notin_range] <;> assumption
#align finsupp.emb_domain_eq_map_domain Finsupp.embDomain_eq_mapDomain

@[to_additive]
theorem prod_mapDomain_index_inj [CommMonoid N] {f : α → β} {s : α →₀ M} {h : β → M → N}
    (hf : Function.Injective f) : (s.mapDomain f).prod h = s.prod fun a b => h (f a) b := by
  rw [← Function.Embedding.coeFn_mk f hf, ← embDomain_eq_mapDomain, prod_embDomain]
#align finsupp.prod_map_domain_index_inj Finsupp.prod_mapDomain_index_inj
#align finsupp.sum_map_domain_index_inj Finsupp.sum_mapDomain_index_inj

theorem mapDomain_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (mapDomain f : (α →₀ M) → β →₀ M) := by
  intro v₁ v₂ eq
  ext a
  have : mapDomain f v₁ (f a) = mapDomain f v₂ (f a) := by rw [eq]
  rwa [mapDomain_apply hf, mapDomain_apply hf] at this
#align finsupp.map_domain_injective Finsupp.mapDomain_injective

/-- When `f` is an embedding we have an embedding `(α →₀ ℕ) ↪ (β →₀ ℕ)` given by `mapDomain`. -/
@[simps]
def mapDomainEmbedding {α β : Type*} (f : α ↪ β) : (α →₀ ℕ) ↪ β →₀ ℕ :=
  ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective f.injective⟩
#align finsupp.map_domain_embedding Finsupp.mapDomainEmbedding

theorem mapDomain.addMonoidHom_comp_mapRange [AddCommMonoid N] (f : α → β) (g : M →+ N) :
    (mapDomain.addMonoidHom f).comp (mapRange.addMonoidHom g) =
      (mapRange.addMonoidHom g).comp (mapDomain.addMonoidHom f) := by
  ext
  simp only [AddMonoidHom.coe_comp, Finsupp.mapRange_single, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.singleAddHom_apply, eq_self_iff_true, Function.comp_apply, Finsupp.mapDomain_single,
    Finsupp.mapRange.addMonoidHom_apply]
#align finsupp.map_domain.add_monoid_hom_comp_map_range Finsupp.mapDomain.addMonoidHom_comp_mapRange

/-- When `g` preserves addition, `mapRange` and `mapDomain` commute. -/
theorem mapDomain_mapRange [AddCommMonoid N] (f : α → β) (v : α →₀ M) (g : M → N) (h0 : g 0 = 0)
    (hadd : ∀ x y, g (x + y) = g x + g y) :
    mapDomain f (mapRange g h0 v) = mapRange g h0 (mapDomain f v) :=
  let g' : M →+ N :=
    { toFun := g
      map_zero' := h0
      map_add' := hadd }
  DFunLike.congr_fun (mapDomain.addMonoidHom_comp_mapRange f g') v
#align finsupp.map_domain_map_range Finsupp.mapDomain_mapRange

theorem sum_update_add [AddCommMonoid α] [AddCommMonoid β] (f : ι →₀ α) (i : ι) (a : α)
    (g : ι → α → β) (hg : ∀ i, g i 0 = 0)
    (hgg : ∀ (j : ι) (a₁ a₂ : α), g j (a₁ + a₂) = g j a₁ + g j a₂) :
    (f.update i a).sum g + g i (f i) = f.sum g + g i a := by
  rw [update_eq_erase_add_single, sum_add_index' hg hgg]
  conv_rhs => rw [← Finsupp.update_self f i]
  rw [update_eq_erase_add_single, sum_add_index' hg hgg, add_assoc, add_assoc]
  congr 1
  rw [add_comm, sum_single_index (hg _), sum_single_index (hg _)]
#align finsupp.sum_update_add Finsupp.sum_update_add

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
#align finsupp.map_domain_inj_on Finsupp.mapDomain_injOn

theorem equivMapDomain_eq_mapDomain {M} [AddCommMonoid M] (f : α ≃ β) (l : α →₀ M) :
    equivMapDomain f l = mapDomain f l := by ext x; simp [mapDomain_equiv_apply]
#align finsupp.equiv_map_domain_eq_map_domain Finsupp.equivMapDomain_eq_mapDomain

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
#align finsupp.comap_domain Finsupp.comapDomain

@[simp]
theorem comapDomain_apply [Zero M] (f : α → β) (l : β →₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support))
    (a : α) : comapDomain f l hf a = l (f a) :=
  rfl
#align finsupp.comap_domain_apply Finsupp.comapDomain_apply

theorem sum_comapDomain [Zero M] [AddCommMonoid N] (f : α → β) (l : β →₀ M) (g : β → M → N)
    (hf : Set.BijOn f (f ⁻¹' ↑l.support) ↑l.support) :
    (comapDomain f l hf.injOn).sum (g ∘ f) = l.sum g := by
  simp only [sum, comapDomain_apply, (· ∘ ·), comapDomain]
  exact Finset.sum_preimage_of_bij f _ hf fun x => g x (l x)
#align finsupp.sum_comap_domain Finsupp.sum_comapDomain

theorem eq_zero_of_comapDomain_eq_zero [AddCommMonoid M] (f : α → β) (l : β →₀ M)
    (hf : Set.BijOn f (f ⁻¹' ↑l.support) ↑l.support) : comapDomain f l hf.injOn = 0 → l = 0 := by
  rw [← support_eq_empty, ← support_eq_empty, comapDomain]
  simp only [Finset.ext_iff, Finset.not_mem_empty, iff_false_iff, mem_preimage]
  intro h a ha
  cases' hf.2.2 ha with b hb
  exact h b (hb.2.symm ▸ ha)
#align finsupp.eq_zero_of_comap_domain_eq_zero Finsupp.eq_zero_of_comapDomain_eq_zero

section FInjective

section Zero

variable [Zero M]

lemma embDomain_comapDomain {f : α ↪ β} {g : β →₀ M} (hg : ↑g.support ⊆ Set.range f) :
    embDomain f (comapDomain f g f.injective.injOn) = g := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [embDomain_apply, comapDomain_apply]
  · replace hg : g b = 0 := not_mem_support_iff.mp <| mt (hg ·) hb
    rw [embDomain_notin_range _ _ _ hb, hg]

/-- Note the `hif` argument is needed for this to work in `rw`. -/
@[simp]
theorem comapDomain_zero (f : α → β)
    (hif : Set.InjOn f (f ⁻¹' ↑(0 : β →₀ M).support) := Finset.coe_empty ▸ (Set.injOn_empty f)) :
    comapDomain f (0 : β →₀ M) hif = (0 : α →₀ M) := by
  ext
  rfl
#align finsupp.comap_domain_zero Finsupp.comapDomain_zero

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
#align finsupp.comap_domain_single Finsupp.comapDomain_single

end Zero

section AddZeroClass

variable [AddZeroClass M] {f : α → β}

theorem comapDomain_add (v₁ v₂ : β →₀ M) (hv₁ : Set.InjOn f (f ⁻¹' ↑v₁.support))
    (hv₂ : Set.InjOn f (f ⁻¹' ↑v₂.support)) (hv₁₂ : Set.InjOn f (f ⁻¹' ↑(v₁ + v₂).support)) :
    comapDomain f (v₁ + v₂) hv₁₂ = comapDomain f v₁ hv₁ + comapDomain f v₂ hv₂ := by
  ext
  simp only [comapDomain_apply, coe_add, Pi.add_apply]
#align finsupp.comap_domain_add Finsupp.comapDomain_add

/-- A version of `Finsupp.comapDomain_add` that's easier to use. -/
theorem comapDomain_add_of_injective (hf : Function.Injective f) (v₁ v₂ : β →₀ M) :
    comapDomain f (v₁ + v₂) hf.injOn =
      comapDomain f v₁ hf.injOn + comapDomain f v₂ hf.injOn :=
  comapDomain_add _ _ _ _ _
#align finsupp.comap_domain_add_of_injective Finsupp.comapDomain_add_of_injective

/-- `Finsupp.comapDomain` is an `AddMonoidHom`. -/
@[simps]
def comapDomain.addMonoidHom (hf : Function.Injective f) : (β →₀ M) →+ α →₀ M where
  toFun x := comapDomain f x hf.injOn
  map_zero' := comapDomain_zero f
  map_add' := comapDomain_add_of_injective hf
#align finsupp.comap_domain.add_monoid_hom Finsupp.comapDomain.addMonoidHom

end AddZeroClass

variable [AddCommMonoid M] (f : α → β)

theorem mapDomain_comapDomain (hf : Function.Injective f) (l : β →₀ M)
    (hl : ↑l.support ⊆ Set.range f) :
    mapDomain f (comapDomain f l hf.injOn) = l := by
  conv_rhs => rw [← embDomain_comapDomain (f := ⟨f, hf⟩) hl (M := M), embDomain_eq_mapDomain]
  rfl
#align finsupp.map_domain_comap_domain Finsupp.mapDomain_comapDomain

end FInjective

end ComapDomain

/-! ### Declarations about finitely supported functions whose support is an `Option` type -/


section Option

/-- Restrict a finitely supported function on `Option α` to a finitely supported function on `α`. -/
def some [Zero M] (f : Option α →₀ M) : α →₀ M :=
  f.comapDomain Option.some fun _ => by simp
#align finsupp.some Finsupp.some

@[simp]
theorem some_apply [Zero M] (f : Option α →₀ M) (a : α) : f.some a = f (Option.some a) :=
  rfl
#align finsupp.some_apply Finsupp.some_apply

@[simp]
theorem some_zero [Zero M] : (0 : Option α →₀ M).some = 0 := by
  ext
  simp
#align finsupp.some_zero Finsupp.some_zero

@[simp]
theorem some_add [AddCommMonoid M] (f g : Option α →₀ M) : (f + g).some = f.some + g.some := by
  ext
  simp
#align finsupp.some_add Finsupp.some_add

@[simp]
theorem some_single_none [Zero M] (m : M) : (single none m : Option α →₀ M).some = 0 := by
  ext
  simp
#align finsupp.some_single_none Finsupp.some_single_none

@[simp]
theorem some_single_some [Zero M] (a : α) (m : M) :
    (single (Option.some a) m : Option α →₀ M).some = single a m := by
  classical
    ext b
    simp [single_apply]
#align finsupp.some_single_some Finsupp.some_single_some

@[to_additive]
theorem prod_option_index [AddCommMonoid M] [CommMonoid N] (f : Option α →₀ M)
    (b : Option α → M → N) (h_zero : ∀ o, b o 0 = 1)
    (h_add : ∀ o m₁ m₂, b o (m₁ + m₂) = b o m₁ * b o m₂) :
    f.prod b = b none (f none) * f.some.prod fun a => b (Option.some a) := by
  classical
    apply induction_linear f
    · simp [some_zero, h_zero]
    · intro f₁ f₂ h₁ h₂
      rw [Finsupp.prod_add_index, h₁, h₂, some_add, Finsupp.prod_add_index]
      · simp only [h_add, Pi.add_apply, Finsupp.coe_add]
        rw [mul_mul_mul_comm]
      all_goals simp [h_zero, h_add]
    · rintro (_ | a) m <;> simp [h_zero, h_add]
#align finsupp.prod_option_index Finsupp.prod_option_index
#align finsupp.sum_option_index Finsupp.sum_option_index

theorem sum_option_index_smul [Semiring R] [AddCommMonoid M] [Module R M] (f : Option α →₀ R)
    (b : Option α → M) :
    (f.sum fun o r => r • b o) = f none • b none + f.some.sum fun a r => r • b (Option.some a) :=
  f.sum_option_index _ (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _
#align finsupp.sum_option_index_smul Finsupp.sum_option_index_smul

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
    beta_reduce -- Porting note(#12129): additional beta reduction needed to activate `split_ifs`
    split_ifs with h <;>
      · simp only [h, mem_filter, mem_support_iff]
        tauto
#align finsupp.filter Finsupp.filter

theorem filter_apply (a : α) : f.filter p a = if p a then f a else 0 := rfl
#align finsupp.filter_apply Finsupp.filter_apply

theorem filter_eq_indicator : ⇑(f.filter p) = Set.indicator { x | p x } f := by
  ext
  simp [filter_apply, Set.indicator_apply]
#align finsupp.filter_eq_indicator Finsupp.filter_eq_indicator

theorem filter_eq_zero_iff : f.filter p = 0 ↔ ∀ x, p x → f x = 0 := by
  simp only [DFunLike.ext_iff, filter_eq_indicator, zero_apply, Set.indicator_apply_eq_zero,
    Set.mem_setOf_eq]
#align finsupp.filter_eq_zero_iff Finsupp.filter_eq_zero_iff

theorem filter_eq_self_iff : f.filter p = f ↔ ∀ x, f x ≠ 0 → p x := by
  simp only [DFunLike.ext_iff, filter_eq_indicator, Set.indicator_apply_eq_self, Set.mem_setOf_eq,
    not_imp_comm]
#align finsupp.filter_eq_self_iff Finsupp.filter_eq_self_iff

@[simp]
theorem filter_apply_pos {a : α} (h : p a) : f.filter p a = f a := if_pos h
#align finsupp.filter_apply_pos Finsupp.filter_apply_pos

@[simp]
theorem filter_apply_neg {a : α} (h : ¬p a) : f.filter p a = 0 := if_neg h
#align finsupp.filter_apply_neg Finsupp.filter_apply_neg

@[simp]
theorem support_filter : (f.filter p).support = f.support.filter p := rfl
#align finsupp.support_filter Finsupp.support_filter

theorem filter_zero : (0 : α →₀ M).filter p = 0 := by
  classical rw [← support_eq_empty, support_filter, support_zero, Finset.filter_empty]
#align finsupp.filter_zero Finsupp.filter_zero

@[simp]
theorem filter_single_of_pos {a : α} {b : M} (h : p a) : (single a b).filter p = single a b :=
  (filter_eq_self_iff _ _).2 fun _ hx => (single_apply_ne_zero.1 hx).1.symm ▸ h
#align finsupp.filter_single_of_pos Finsupp.filter_single_of_pos

@[simp]
theorem filter_single_of_neg {a : α} {b : M} (h : ¬p a) : (single a b).filter p = 0 :=
  (filter_eq_zero_iff _ _).2 fun _ hpx =>
    single_apply_eq_zero.2 fun hxa => absurd hpx (hxa.symm ▸ h)
#align finsupp.filter_single_of_neg Finsupp.filter_single_of_neg

@[to_additive]
theorem prod_filter_index [CommMonoid N] (g : α → M → N) :
    (f.filter p).prod g = ∏ x ∈ (f.filter p).support, g x (f x) := by
  classical
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [support_filter, Finset.mem_filter] at hx
    rw [filter_apply_pos _ _ hx.2]
#align finsupp.prod_filter_index Finsupp.prod_filter_index
#align finsupp.sum_filter_index Finsupp.sum_filter_index

@[to_additive (attr := simp)]
theorem prod_filter_mul_prod_filter_not [CommMonoid N] (g : α → M → N) :
    (f.filter p).prod g * (f.filter fun a => ¬p a).prod g = f.prod g := by
  classical simp_rw [prod_filter_index, support_filter, Finset.prod_filter_mul_prod_filter_not,
    Finsupp.prod]
#align finsupp.prod_filter_mul_prod_filter_not Finsupp.prod_filter_mul_prod_filter_not
#align finsupp.sum_filter_add_sum_filter_not Finsupp.sum_filter_add_sum_filter_not

@[to_additive (attr := simp)]
theorem prod_div_prod_filter [CommGroup G] (g : α → M → G) :
    f.prod g / (f.filter p).prod g = (f.filter fun a => ¬p a).prod g :=
  div_eq_of_eq_mul' (prod_filter_mul_prod_filter_not _ _ _).symm
#align finsupp.prod_div_prod_filter Finsupp.prod_div_prod_filter
#align finsupp.sum_sub_sum_filter Finsupp.sum_sub_sum_filter

end Zero

theorem filter_pos_add_filter_neg [AddZeroClass M] (f : α →₀ M) (p : α → Prop) [DecidablePred p] :
    (f.filter p + f.filter fun a => ¬p a) = f :=
  DFunLike.coe_injective <| by
    simp only [coe_add, filter_eq_indicator]
    exact Set.indicator_self_add_compl { x | p x } f
#align finsupp.filter_pos_add_filter_neg Finsupp.filter_pos_add_filter_neg

end Filter

/-! ### Declarations about `frange` -/


section Frange

variable [Zero M]

/-- `frange f` is the image of `f` on the support of `f`. -/
def frange (f : α →₀ M) : Finset M :=
  haveI := Classical.decEq M
  Finset.image f f.support
#align finsupp.frange Finsupp.frange

theorem mem_frange {f : α →₀ M} {y : M} : y ∈ f.frange ↔ y ≠ 0 ∧ ∃ x, f x = y := by
  rw [frange, @Finset.mem_image _ _ (Classical.decEq _) _ f.support]
  exact ⟨fun ⟨x, hx1, hx2⟩ => ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩, fun ⟨hy, x, hx⟩ =>
    ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩
  -- Porting note: maybe there is a better way to fix this, but (1) it wasn't seeing past `frange`
  -- the definition, and (2) it needed the `Classical.decEq` instance again.
#align finsupp.mem_frange Finsupp.mem_frange

theorem zero_not_mem_frange {f : α →₀ M} : (0 : M) ∉ f.frange := fun H => (mem_frange.1 H).1 rfl
#align finsupp.zero_not_mem_frange Finsupp.zero_not_mem_frange

theorem frange_single {x : α} {y : M} : frange (single x y) ⊆ {y} := fun r hr =>
  let ⟨t, ht1, ht2⟩ := mem_frange.1 hr
  ht2 ▸ by
    classical
      rw [single_apply] at ht2 ⊢
      split_ifs at ht2 ⊢
      · exact Finset.mem_singleton_self _
      · exact (t ht2.symm).elim
#align finsupp.frange_single Finsupp.frange_single

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
#align finsupp.subtype_domain Finsupp.subtypeDomain

@[simp]
theorem support_subtypeDomain [D : DecidablePred p] {f : α →₀ M} :
    (subtypeDomain p f).support = f.support.subtype p := by rw [Subsingleton.elim D] <;> rfl
#align finsupp.support_subtype_domain Finsupp.support_subtypeDomain

@[simp]
theorem subtypeDomain_apply {a : Subtype p} {v : α →₀ M} : (subtypeDomain p v) a = v a.val :=
  rfl
#align finsupp.subtype_domain_apply Finsupp.subtypeDomain_apply

@[simp]
theorem subtypeDomain_zero : subtypeDomain p (0 : α →₀ M) = 0 :=
  rfl
#align finsupp.subtype_domain_zero Finsupp.subtypeDomain_zero

theorem subtypeDomain_eq_zero_iff' {f : α →₀ M} : f.subtypeDomain p = 0 ↔ ∀ x, p x → f x = 0 := by
  classical simp_rw [← support_eq_empty, support_subtypeDomain, subtype_eq_empty,
      not_mem_support_iff]
#align finsupp.subtype_domain_eq_zero_iff' Finsupp.subtypeDomain_eq_zero_iff'

theorem subtypeDomain_eq_zero_iff {f : α →₀ M} (hf : ∀ x ∈ f.support, p x) :
    f.subtypeDomain p = 0 ↔ f = 0 :=
  subtypeDomain_eq_zero_iff'.trans
    ⟨fun H =>
      ext fun x => by
        classical exact if hx : p x then H x hx else not_mem_support_iff.1 <| mt (hf x) hx,
      fun H x _ => by simp [H]⟩
#align finsupp.subtype_domain_eq_zero_iff Finsupp.subtypeDomain_eq_zero_iff

@[to_additive]
theorem prod_subtypeDomain_index [CommMonoid N] {v : α →₀ M} {h : α → M → N}
    (hp : ∀ x ∈ v.support, p x) : (v.subtypeDomain p).prod (fun a b ↦ h a b) = v.prod h := by
  refine Finset.prod_bij (fun p _ ↦ p) ?_ ?_ ?_ ?_ <;> aesop
#align finsupp.prod_subtype_domain_index Finsupp.prod_subtypeDomain_index
#align finsupp.sum_subtype_domain_index Finsupp.sum_subtypeDomain_index

end Zero

section AddZeroClass

variable [AddZeroClass M] {p : α → Prop} {v v' : α →₀ M}

@[simp]
theorem subtypeDomain_add {v v' : α →₀ M} :
    (v + v').subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p :=
  ext fun _ => rfl
#align finsupp.subtype_domain_add Finsupp.subtypeDomain_add

/-- `subtypeDomain` but as an `AddMonoidHom`. -/
def subtypeDomainAddMonoidHom : (α →₀ M) →+ Subtype p →₀ M where
  toFun := subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' _ _ := subtypeDomain_add
#align finsupp.subtype_domain_add_monoid_hom Finsupp.subtypeDomainAddMonoidHom

/-- `Finsupp.filter` as an `AddMonoidHom`. -/
def filterAddHom (p : α → Prop) [DecidablePred p]: (α →₀ M) →+ α →₀ M where
  toFun := filter p
  map_zero' := filter_zero p
  map_add' f g := DFunLike.coe_injective <| by
    simp only [filter_eq_indicator, coe_add]
    exact Set.indicator_add { x | p x } f g
#align finsupp.filter_add_hom Finsupp.filterAddHom

@[simp]
theorem filter_add [DecidablePred p] {v v' : α →₀ M} :
    (v + v').filter p = v.filter p + v'.filter p :=
  (filterAddHom p).map_add v v'
#align finsupp.filter_add Finsupp.filter_add

end AddZeroClass

section CommMonoid

variable [AddCommMonoid M] {p : α → Prop}

theorem subtypeDomain_sum {s : Finset ι} {h : ι → α →₀ M} :
    (∑ c ∈ s, h c).subtypeDomain p = ∑ c ∈ s, (h c).subtypeDomain p :=
  map_sum subtypeDomainAddMonoidHom _ s
#align finsupp.subtype_domain_sum Finsupp.subtypeDomain_sum

theorem subtypeDomain_finsupp_sum [Zero N] {s : β →₀ N} {h : β → N → α →₀ M} :
    (s.sum h).subtypeDomain p = s.sum fun c d => (h c d).subtypeDomain p :=
  subtypeDomain_sum
#align finsupp.subtype_domain_finsupp_sum Finsupp.subtypeDomain_finsupp_sum

theorem filter_sum [DecidablePred p] (s : Finset ι) (f : ι → α →₀ M) :
    (∑ a ∈ s, f a).filter p = ∑ a ∈ s, filter p (f a) :=
  map_sum (filterAddHom p) f s
#align finsupp.filter_sum Finsupp.filter_sum

theorem filter_eq_sum (p : α → Prop) [DecidablePred p] (f : α →₀ M) :
    f.filter p = ∑ i ∈ f.support.filter p, single i (f i) :=
  (f.filter p).sum_single.symm.trans <|
    Finset.sum_congr rfl fun x hx => by
      rw [filter_apply_pos _ _ (mem_filter.1 hx).2]
#align finsupp.filter_eq_sum Finsupp.filter_eq_sum

end CommMonoid

section Group

variable [AddGroup G] {p : α → Prop} {v v' : α →₀ G}

@[simp]
theorem subtypeDomain_neg : (-v).subtypeDomain p = -v.subtypeDomain p :=
  ext fun _ => rfl
#align finsupp.subtype_domain_neg Finsupp.subtypeDomain_neg

@[simp]
theorem subtypeDomain_sub : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p :=
  ext fun _ => rfl
#align finsupp.subtype_domain_sub Finsupp.subtypeDomain_sub

@[simp]
theorem single_neg (a : α) (b : G) : single a (-b) = -single a b :=
  (singleAddHom a : G →+ _).map_neg b
#align finsupp.single_neg Finsupp.single_neg

@[simp]
theorem single_sub (a : α) (b₁ b₂ : G) : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
  (singleAddHom a : G →+ _).map_sub b₁ b₂
#align finsupp.single_sub Finsupp.single_sub

@[simp]
theorem erase_neg (a : α) (f : α →₀ G) : erase a (-f) = -erase a f :=
  (eraseAddHom a : (_ →₀ G) →+ _).map_neg f
#align finsupp.erase_neg Finsupp.erase_neg

@[simp]
theorem erase_sub (a : α) (f₁ f₂ : α →₀ G) : erase a (f₁ - f₂) = erase a f₁ - erase a f₂ :=
  (eraseAddHom a : (_ →₀ G) →+ _).map_sub f₁ f₂
#align finsupp.erase_sub Finsupp.erase_sub

@[simp]
theorem filter_neg (p : α → Prop) [DecidablePred p] (f : α →₀ G) : filter p (-f) = -filter p f :=
  (filterAddHom p : (_ →₀ G) →+ _).map_neg f
#align finsupp.filter_neg Finsupp.filter_neg

@[simp]
theorem filter_sub (p : α → Prop) [DecidablePred p] (f₁ f₂ : α →₀ G) :
    filter p (f₁ - f₂) = filter p f₁ - filter p f₂ :=
  (filterAddHom p : (_ →₀ G) →+ _).map_sub f₁ f₂
#align finsupp.filter_sub Finsupp.filter_sub

end Group

end SubtypeDomain

theorem mem_support_multiset_sum [AddCommMonoid M] {s : Multiset (α →₀ M)} (a : α) :
    a ∈ s.sum.support → ∃ f ∈ s, a ∈ (f : α →₀ M).support :=
  Multiset.induction_on s (fun h => False.elim (by simp at h))
    (by
      intro f s ih ha
      by_cases h : a ∈ f.support
      · exact ⟨f, Multiset.mem_cons_self _ _, h⟩
      · simp only [Multiset.sum_cons, mem_support_iff, add_apply, not_mem_support_iff.1 h,
          zero_add] at ha
        rcases ih (mem_support_iff.2 ha) with ⟨f', h₀, h₁⟩
        exact ⟨f', Multiset.mem_cons_of_mem h₀, h₁⟩)
#align finsupp.mem_support_multiset_sum Finsupp.mem_support_multiset_sum

theorem mem_support_finset_sum [AddCommMonoid M] {s : Finset ι} {h : ι → α →₀ M} (a : α)
    (ha : a ∈ (∑ c ∈ s, h c).support) : ∃ c ∈ s, a ∈ (h c).support :=
  let ⟨_, hf, hfa⟩ := mem_support_multiset_sum a ha
  let ⟨c, hc, Eq⟩ := Multiset.mem_map.1 hf
  ⟨c, hc, Eq.symm ▸ hfa⟩
#align finsupp.mem_support_finset_sum Finsupp.mem_support_finset_sum

/-! ### Declarations about `curry` and `uncurry` -/


section CurryUncurry

variable [AddCommMonoid M] [AddCommMonoid N]

/-- Given a finitely supported function `f` from a product type `α × β` to `γ`,
`curry f` is the "curried" finitely supported function from `α` to the type of
finitely supported functions from `β` to `γ`. -/
protected def curry (f : α × β →₀ M) : α →₀ β →₀ M :=
  f.sum fun p c => single p.1 (single p.2 c)
#align finsupp.curry Finsupp.curry

@[simp]
theorem curry_apply (f : α × β →₀ M) (x : α) (y : β) : f.curry x y = f (x, y) := by
  classical
    have : ∀ b : α × β, single b.fst (single b.snd (f b)) x y = if b = (x, y) then f b else 0 := by
      rintro ⟨b₁, b₂⟩
      simp only [ne_eq, single_apply, Prod.ext_iff, ite_and]
      split_ifs <;> simp [single_apply, *]
    rw [Finsupp.curry, sum_apply, sum_apply, sum_eq_single, this, if_pos rfl]
    · intro b _ b_ne
      rw [this b, if_neg b_ne]
    · intro _
      rw [single_zero, single_zero, coe_zero, Pi.zero_apply, coe_zero, Pi.zero_apply]
#align finsupp.curry_apply Finsupp.curry_apply

theorem sum_curry_index (f : α × β →₀ M) (g : α → β → M → N) (hg₀ : ∀ a b, g a b 0 = 0)
    (hg₁ : ∀ a b c₀ c₁, g a b (c₀ + c₁) = g a b c₀ + g a b c₁) :
    (f.curry.sum fun a f => f.sum (g a)) = f.sum fun p c => g p.1 p.2 c := by
  rw [Finsupp.curry]
  trans
  · exact
      sum_sum_index (fun a => sum_zero_index) fun a b₀ b₁ =>
        sum_add_index' (fun a => hg₀ _ _) fun c d₀ d₁ => hg₁ _ _ _ _
  congr; funext p c
  trans
  · exact sum_single_index sum_zero_index
  exact sum_single_index (hg₀ _ _)
#align finsupp.sum_curry_index Finsupp.sum_curry_index

/-- Given a finitely supported function `f` from `α` to the type of
finitely supported functions from `β` to `M`,
`uncurry f` is the "uncurried" finitely supported function from `α × β` to `M`. -/
protected def uncurry (f : α →₀ β →₀ M) : α × β →₀ M :=
  f.sum fun a g => g.sum fun b c => single (a, b) c
#align finsupp.uncurry Finsupp.uncurry

/-- `finsuppProdEquiv` defines the `Equiv` between `((α × β) →₀ M)` and `(α →₀ (β →₀ M))` given by
currying and uncurrying. -/
def finsuppProdEquiv : (α × β →₀ M) ≃ (α →₀ β →₀ M) where
  toFun := Finsupp.curry
  invFun := Finsupp.uncurry
  left_inv f := by
    rw [Finsupp.uncurry, sum_curry_index]
    · simp_rw [Prod.mk.eta, sum_single]
    · intros
      apply single_zero
    · intros
      apply single_add
  right_inv f := by
    simp only [Finsupp.curry, Finsupp.uncurry, sum_sum_index, sum_zero_index, sum_add_index,
      sum_single_index, single_zero, single_add, eq_self_iff_true, forall_true_iff,
      forall₃_true_iff, (single_sum _ _ _).symm, sum_single]
#align finsupp.finsupp_prod_equiv Finsupp.finsuppProdEquiv

theorem filter_curry (f : α × β →₀ M) (p : α → Prop) [DecidablePred p] :
    (f.filter fun a : α × β => p a.1).curry = f.curry.filter p := by
  classical
    rw [Finsupp.curry, Finsupp.curry, Finsupp.sum, Finsupp.sum, filter_sum, support_filter,
      sum_filter]
    refine Finset.sum_congr rfl ?_
    rintro ⟨a₁, a₂⟩ _
    split_ifs with h
    · rw [filter_apply_pos, filter_single_of_pos] <;> exact h
    · rwa [filter_single_of_neg]
#align finsupp.filter_curry Finsupp.filter_curry

theorem support_curry [DecidableEq α] (f : α × β →₀ M) :
    f.curry.support ⊆ f.support.image Prod.fst := by
  rw [← Finset.biUnion_singleton]
  refine Finset.Subset.trans support_sum ?_
  exact Finset.biUnion_mono fun a _ => support_single_subset
#align finsupp.support_curry Finsupp.support_curry

end CurryUncurry

/-! ### Declarations about finitely supported functions whose support is a `Sum` type -/


section Sum

/-- `Finsupp.sumElim f g` maps `inl x` to `f x` and `inr y` to `g y`. -/
def sumElim {α β γ : Type*} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) : Sum α β →₀ γ :=
  onFinset
    (by
      haveI := Classical.decEq α
      haveI := Classical.decEq β
      exact f.support.map ⟨_, Sum.inl_injective⟩ ∪ g.support.map ⟨_, Sum.inr_injective⟩)
    (Sum.elim f g) fun ab h => by
    cases' ab with a b <;>
    letI := Classical.decEq α <;> letI := Classical.decEq β <;>
    -- porting note (#10754): had to add these `DecidableEq` instances
    simp only [Sum.elim_inl, Sum.elim_inr] at h <;>
    simpa
#align finsupp.sum_elim Finsupp.sumElim

@[simp, norm_cast]
theorem coe_sumElim {α β γ : Type*} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) :
    ⇑(sumElim f g) = Sum.elim f g :=
  rfl
#align finsupp.coe_sum_elim Finsupp.coe_sumElim

theorem sumElim_apply {α β γ : Type*} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) (x : Sum α β) :
    sumElim f g x = Sum.elim f g x :=
  rfl
#align finsupp.sum_elim_apply Finsupp.sumElim_apply

theorem sumElim_inl {α β γ : Type*} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) (x : α) :
    sumElim f g (Sum.inl x) = f x :=
  rfl
#align finsupp.sum_elim_inl Finsupp.sumElim_inl

theorem sumElim_inr {α β γ : Type*} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) (x : β) :
    sumElim f g (Sum.inr x) = g x :=
  rfl
#align finsupp.sum_elim_inr Finsupp.sumElim_inr

/-- The equivalence between `(α ⊕ β) →₀ γ` and `(α →₀ γ) × (β →₀ γ)`.

This is the `Finsupp` version of `Equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symm_apply]
def sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] : (Sum α β →₀ γ) ≃ (α →₀ γ) × (β →₀ γ) where
  toFun f :=
    ⟨f.comapDomain Sum.inl Sum.inl_injective.injOn,
      f.comapDomain Sum.inr Sum.inr_injective.injOn⟩
  invFun fg := sumElim fg.1 fg.2
  left_inv f := by
    ext ab
    cases' ab with a b <;> simp
  right_inv fg := by ext <;> simp
#align finsupp.sum_finsupp_equiv_prod_finsupp Finsupp.sumFinsuppEquivProdFinsupp

theorem fst_sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] (f : Sum α β →₀ γ) (x : α) :
    (sumFinsuppEquivProdFinsupp f).1 x = f (Sum.inl x) :=
  rfl
#align finsupp.fst_sum_finsupp_equiv_prod_finsupp Finsupp.fst_sumFinsuppEquivProdFinsupp

theorem snd_sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] (f : Sum α β →₀ γ) (y : β) :
    (sumFinsuppEquivProdFinsupp f).2 y = f (Sum.inr y) :=
  rfl
#align finsupp.snd_sum_finsupp_equiv_prod_finsupp Finsupp.snd_sumFinsuppEquivProdFinsupp

theorem sumFinsuppEquivProdFinsupp_symm_inl {α β γ : Type*} [Zero γ] (fg : (α →₀ γ) × (β →₀ γ))
    (x : α) : (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl
#align finsupp.sum_finsupp_equiv_prod_finsupp_symm_inl Finsupp.sumFinsuppEquivProdFinsupp_symm_inl

theorem sumFinsuppEquivProdFinsupp_symm_inr {α β γ : Type*} [Zero γ] (fg : (α →₀ γ) × (β →₀ γ))
    (y : β) : (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl
#align finsupp.sum_finsupp_equiv_prod_finsupp_symm_inr Finsupp.sumFinsuppEquivProdFinsupp_symm_inr

variable [AddMonoid M]

/-- The additive equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `Finsupp` version of `Equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps! apply symm_apply]
def sumFinsuppAddEquivProdFinsupp {α β : Type*} : (Sum α β →₀ M) ≃+ (α →₀ M) × (β →₀ M) :=
  { sumFinsuppEquivProdFinsupp with
    map_add' := by
      intros
      ext <;>
        simp only [Equiv.toFun_as_coe, Prod.fst_add, Prod.snd_add, add_apply,
          snd_sumFinsuppEquivProdFinsupp, fst_sumFinsuppEquivProdFinsupp] }
#align finsupp.sum_finsupp_add_equiv_prod_finsupp Finsupp.sumFinsuppAddEquivProdFinsupp

theorem fst_sumFinsuppAddEquivProdFinsupp {α β : Type*} (f : Sum α β →₀ M) (x : α) :
    (sumFinsuppAddEquivProdFinsupp f).1 x = f (Sum.inl x) :=
  rfl
#align finsupp.fst_sum_finsupp_add_equiv_prod_finsupp Finsupp.fst_sumFinsuppAddEquivProdFinsupp

theorem snd_sumFinsuppAddEquivProdFinsupp {α β : Type*} (f : Sum α β →₀ M) (y : β) :
    (sumFinsuppAddEquivProdFinsupp f).2 y = f (Sum.inr y) :=
  rfl
#align finsupp.snd_sum_finsupp_add_equiv_prod_finsupp Finsupp.snd_sumFinsuppAddEquivProdFinsupp

theorem sumFinsuppAddEquivProdFinsupp_symm_inl {α β : Type*} (fg : (α →₀ M) × (β →₀ M)) (x : α) :
    (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl
#align finsupp.sum_finsupp_add_equiv_prod_finsupp_symm_inl Finsupp.sumFinsuppAddEquivProdFinsupp_symm_inl

theorem sumFinsuppAddEquivProdFinsupp_symm_inr {α β : Type*} (fg : (α →₀ M) × (β →₀ M)) (y : β) :
    (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl
#align finsupp.sum_finsupp_add_equiv_prod_finsupp_symm_inr Finsupp.sumFinsuppAddEquivProdFinsupp_symm_inr

end Sum

/-! ### Declarations about scalar multiplication -/


section

variable [Zero M] [MonoidWithZero R] [MulActionWithZero R M]

@[simp, nolint simpNF] -- `simpNF` incorrectly complains the LHS doesn't simplify.
theorem single_smul (a b : α) (f : α → M) (r : R) : single a r b • f a = single a (r • f b) b := by
  by_cases h : a = b <;> simp [h]
#align finsupp.single_smul Finsupp.single_smul

end

section

variable [Monoid G] [MulAction G α] [AddCommMonoid M]

/-- Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the `instance_diamonds` test for examples of such conflicts. -/
def comapSMul : SMul G (α →₀ M) where smul g := mapDomain (g • ·)
#align finsupp.comap_has_smul Finsupp.comapSMul

attribute [local instance] comapSMul

theorem comapSMul_def (g : G) (f : α →₀ M) : g • f = mapDomain (g • ·) f :=
  rfl
#align finsupp.comap_smul_def Finsupp.comapSMul_def

@[simp]
theorem comapSMul_single (g : G) (a : α) (b : M) : g • single a b = single (g • a) b :=
  mapDomain_single
#align finsupp.comap_smul_single Finsupp.comapSMul_single

/-- `Finsupp.comapSMul` is multiplicative -/
def comapMulAction : MulAction G (α →₀ M) where
  one_smul f := by rw [comapSMul_def, one_smul_eq_id, mapDomain_id]
  mul_smul g g' f := by
    rw [comapSMul_def, comapSMul_def, comapSMul_def, ← comp_smul_left, mapDomain_comp]
#align finsupp.comap_mul_action Finsupp.comapMulAction

attribute [local instance] comapMulAction

/-- `Finsupp.comapSMul` is distributive -/
def comapDistribMulAction : DistribMulAction G (α →₀ M) where
  smul_zero g := by
    ext a
    simp only [comapSMul_def]
    simp
  smul_add g f f' := by
    ext
    simp only [comapSMul_def]
    simp [mapDomain_add]
#align finsupp.comap_distrib_mul_action Finsupp.comapDistribMulAction

end

section

variable [Group G] [MulAction G α] [AddCommMonoid M]

attribute [local instance] comapSMul comapMulAction comapDistribMulAction

/-- When `G` is a group, `Finsupp.comapSMul` acts by precomposition with the action of `g⁻¹`.
-/
@[simp]
theorem comapSMul_apply (g : G) (f : α →₀ M) (a : α) : (g • f) a = f (g⁻¹ • a) := by
  conv_lhs => rw [← smul_inv_smul g a]
  exact mapDomain_apply (MulAction.injective g) _ (g⁻¹ • a)
#align finsupp.comap_smul_apply Finsupp.comapSMul_apply

end

section

instance smulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass R (α →₀ M) where
  smul a v := v.mapRange (a • ·) (smul_zero _)
  smul_zero a := by
    ext
    apply smul_zero
#align finsupp.smul_zero_class Finsupp.smulZeroClass

/-!
Throughout this section, some `Monoid` and `Semiring` arguments are specified with `{}` instead of
`[]`. See note [implicit instance arguments].
-/

@[simp, norm_cast]
theorem coe_smul [Zero M] [SMulZeroClass R M] (b : R) (v : α →₀ M) : ⇑(b • v) = b • ⇑v :=
  rfl
#align finsupp.coe_smul Finsupp.coe_smul

theorem smul_apply [Zero M] [SMulZeroClass R M] (b : R) (v : α →₀ M) (a : α) :
    (b • v) a = b • v a :=
  rfl
#align finsupp.smul_apply Finsupp.smul_apply

theorem _root_.IsSMulRegular.finsupp [Zero M] [SMulZeroClass R M] {k : R}
    (hk : IsSMulRegular M k) : IsSMulRegular (α →₀ M) k :=
  fun _ _ h => ext fun i => hk (DFunLike.congr_fun h i)
#align is_smul_regular.finsupp IsSMulRegular.finsupp

instance faithfulSMul [Nonempty α] [Zero M] [SMulZeroClass R M] [FaithfulSMul R M] :
    FaithfulSMul R (α →₀ M) where
  eq_of_smul_eq_smul h :=
    let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun m : M => by simpa using DFunLike.congr_fun (h (single a m)) a
#align finsupp.faithful_smul Finsupp.faithfulSMul

instance instSMulWithZero [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (α →₀ M) where
  zero_smul f := by ext i; exact zero_smul _ _

variable (α M)

instance distribSMul [AddZeroClass M] [DistribSMul R M] : DistribSMul R (α →₀ M) where
  smul := (· • ·)
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
  smul_zero _ := ext fun _ => smul_zero _
#align finsupp.distrib_smul Finsupp.distribSMul

instance distribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction R (α →₀ M) :=
  { Finsupp.distribSMul _ _ with
    one_smul := fun x => ext fun y => one_smul R (x y)
    mul_smul := fun r s x => ext fun y => mul_smul r s (x y) }
#align finsupp.distrib_mul_action Finsupp.distribMulAction

instance isScalarTower [Zero M] [SMulZeroClass R M] [SMulZeroClass S M] [SMul R S]
  [IsScalarTower R S M] : IsScalarTower R S (α →₀ M) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

instance smulCommClass [Zero M] [SMulZeroClass R M] [SMulZeroClass S M] [SMulCommClass R S M] :
  SMulCommClass R S (α →₀ M) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _
#align finsupp.smul_comm_class Finsupp.smulCommClass

instance isCentralScalar [Zero M] [SMulZeroClass R M] [SMulZeroClass Rᵐᵒᵖ M] [IsCentralScalar R M] :
  IsCentralScalar R (α →₀ M) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _
#align finsupp.is_central_scalar Finsupp.isCentralScalar

instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module R (α →₀ M) :=
  { toDistribMulAction := Finsupp.distribMulAction α M
    zero_smul := fun _ => ext fun _ => zero_smul _ _
    add_smul := fun _ _ _ => ext fun _ => add_smul _ _ _ }
#align finsupp.module Finsupp.module

variable {α M}

theorem support_smul [AddMonoid M] [SMulZeroClass R M] {b : R} {g : α →₀ M} :
    (b • g).support ⊆ g.support := fun a => by
  simp only [smul_apply, mem_support_iff, Ne]
  exact mt fun h => h.symm ▸ smul_zero _
#align finsupp.support_smul Finsupp.support_smul

@[simp]
theorem support_smul_eq [Semiring R] [AddCommMonoid M] [Module R M] [NoZeroSMulDivisors R M] {b : R}
    (hb : b ≠ 0) {g : α →₀ M} : (b • g).support = g.support :=
  Finset.ext fun a => by simp [Finsupp.smul_apply, hb]
#align finsupp.support_smul_eq Finsupp.support_smul_eq

section

variable {p : α → Prop} [DecidablePred p]

@[simp]
theorem filter_smul {_ : Monoid R} [AddMonoid M] [DistribMulAction R M] {b : R} {v : α →₀ M} :
    (b • v).filter p = b • v.filter p :=
  DFunLike.coe_injective <| by
    simp only [filter_eq_indicator, coe_smul]
    exact Set.indicator_const_smul { x | p x } b v
#align finsupp.filter_smul Finsupp.filter_smul

end

theorem mapDomain_smul {_ : Monoid R} [AddCommMonoid M] [DistribMulAction R M] {f : α → β} (b : R)
    (v : α →₀ M) : mapDomain f (b • v) = b • mapDomain f v :=
  mapDomain_mapRange _ _ _ _ (smul_add b)
#align finsupp.map_domain_smul Finsupp.mapDomain_smul

@[simp]
theorem smul_single [Zero M] [SMulZeroClass R M] (c : R) (a : α) (b : M) :
    c • Finsupp.single a b = Finsupp.single a (c • b) :=
  mapRange_single
#align finsupp.smul_single Finsupp.smul_single

-- Porting note: removed `simp` because `simpNF` can prove it.
theorem smul_single' {_ : Semiring R} (c : R) (a : α) (b : R) :
    c • Finsupp.single a b = Finsupp.single a (c * b) :=
  smul_single _ _ _
#align finsupp.smul_single' Finsupp.smul_single'

theorem mapRange_smul {_ : Monoid R} [AddMonoid M] [DistribMulAction R M] [AddMonoid N]
    [DistribMulAction R N] {f : M → N} {hf : f 0 = 0} (c : R) (v : α →₀ M)
    (hsmul : ∀ x, f (c • x) = c • f x) : mapRange f hf (c • v) = c • mapRange f hf v := by
  erw [← mapRange_comp]
  · have : f ∘ (c • ·) = (c • ·) ∘ f := funext hsmul
    simp_rw [this]
    apply mapRange_comp
  simp only [Function.comp_apply, smul_zero, hf]
#align finsupp.map_range_smul Finsupp.mapRange_smul

theorem smul_single_one [Semiring R] (a : α) (b : R) : b • single a (1 : R) = single a b := by
  rw [smul_single, smul_eq_mul, mul_one]
#align finsupp.smul_single_one Finsupp.smul_single_one

theorem comapDomain_smul [AddMonoid M] [Monoid R] [DistribMulAction R M] {f : α → β} (r : R)
    (v : β →₀ M) (hfv : Set.InjOn f (f ⁻¹' ↑v.support))
    (hfrv : Set.InjOn f (f ⁻¹' ↑(r • v).support) :=
      hfv.mono <| Set.preimage_mono <| Finset.coe_subset.mpr support_smul) :
    comapDomain f (r • v) hfrv = r • comapDomain f v hfv := by
  ext
  rfl
#align finsupp.comap_domain_smul Finsupp.comapDomain_smul

/-- A version of `Finsupp.comapDomain_smul` that's easier to use. -/
theorem comapDomain_smul_of_injective [AddMonoid M] [Monoid R] [DistribMulAction R M] {f : α → β}
    (hf : Function.Injective f) (r : R) (v : β →₀ M) :
    comapDomain f (r • v) hf.injOn = r • comapDomain f v hf.injOn :=
  comapDomain_smul _ _ _ _
#align finsupp.comap_domain_smul_of_injective Finsupp.comapDomain_smul_of_injective

end

theorem sum_smul_index [Semiring R] [AddCommMonoid M] {g : α →₀ R} {b : R} {h : α → R → M}
    (h0 : ∀ i, h i 0 = 0) : (b • g).sum h = g.sum fun i a => h i (b * a) :=
  Finsupp.sum_mapRange_index h0
#align finsupp.sum_smul_index Finsupp.sum_smul_index

theorem sum_smul_index' [AddMonoid M] [DistribSMul R M] [AddCommMonoid N] {g : α →₀ M} {b : R}
    {h : α → M → N} (h0 : ∀ i, h i 0 = 0) : (b • g).sum h = g.sum fun i c => h i (b • c) :=
  Finsupp.sum_mapRange_index h0
#align finsupp.sum_smul_index' Finsupp.sum_smul_index'

/-- A version of `Finsupp.sum_smul_index'` for bundled additive maps. -/
theorem sum_smul_index_addMonoidHom [AddMonoid M] [AddCommMonoid N] [DistribSMul R M] {g : α →₀ M}
    {b : R} {h : α → M →+ N} : ((b • g).sum fun a => h a) = g.sum fun i c => h i (b • c) :=
  sum_mapRange_index fun i => (h i).map_zero
#align finsupp.sum_smul_index_add_monoid_hom Finsupp.sum_smul_index_addMonoidHom

instance noZeroSMulDivisors [Semiring R] [AddCommMonoid M] [Module R M] {ι : Type*}
    [NoZeroSMulDivisors R M] : NoZeroSMulDivisors R (ι →₀ M) :=
  ⟨fun h =>
    or_iff_not_imp_left.mpr fun hc =>
      Finsupp.ext fun i => (smul_eq_zero.mp (DFunLike.ext_iff.mp h i)).resolve_left hc⟩
#align finsupp.no_zero_smul_divisors Finsupp.noZeroSMulDivisors

section DistribMulActionSemiHom

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [DistribMulAction R M] [DistribMulAction R N]

/-- `Finsupp.single` as a `DistribMulActionSemiHom`.

See also `Finsupp.lsingle` for the version as a linear map. -/
def DistribMulActionHom.single (a : α) : M →+[R] α →₀ M :=
  { singleAddHom a with
    map_smul' := fun k m => by
      simp only
      show singleAddHom a (k • m) = k • singleAddHom a m
      change Finsupp.single a (k • m) = k • (Finsupp.single a m)
      -- Porting note: because `singleAddHom_apply` is missing
      simp only [smul_single] }
#align finsupp.distrib_mul_action_hom.single Finsupp.DistribMulActionHom.single

theorem distribMulActionHom_ext {f g : (α →₀ M) →+[R] N}
    (h : ∀ (a : α) (m : M), f (single a m) = g (single a m)) : f = g :=
  DistribMulActionHom.toAddMonoidHom_injective <| addHom_ext h
#align finsupp.distrib_mul_action_hom_ext Finsupp.distribMulActionHom_ext

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem distribMulActionHom_ext' {f g : (α →₀ M) →+[R] N}
    (h : ∀ a : α, f.comp (DistribMulActionHom.single a) = g.comp (DistribMulActionHom.single a)) :
    f = g :=
  distribMulActionHom_ext fun a => DistribMulActionHom.congr_fun (h a)
#align finsupp.distrib_mul_action_hom_ext' Finsupp.distribMulActionHom_ext'

end DistribMulActionSemiHom

section

variable [Zero R]

/-- The `Finsupp` version of `Pi.unique`. -/
instance uniqueOfRight [Subsingleton R] : Unique (α →₀ R) :=
  DFunLike.coe_injective.unique
#align finsupp.unique_of_right Finsupp.uniqueOfRight

/-- The `Finsupp` version of `Pi.uniqueOfIsEmpty`. -/
instance uniqueOfLeft [IsEmpty α] : Unique (α →₀ R) :=
  DFunLike.coe_injective.unique
#align finsupp.unique_of_left Finsupp.uniqueOfLeft

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
  · #adaptation_note
    /-- Prior to nightly-2024-06-18, this `rw` was done by `dsimp`. -/
    rw [extendDomain_toFun]
    dsimp
    rw [if_neg h, eq_comm, ← not_mem_support_iff]
    refine mt ?_ h
    exact @hf _

@[simp]
theorem extendDomain_single (a : Subtype P) (m : M) :
    (single a m).extendDomain = single a.val m := by
  ext a'
  #adaptation_note
  /-- Prior to nightly-2024-06-18, this `rw` was instead `dsimp only`. -/
  rw [extendDomain_toFun]
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
def restrictSupportEquiv (s : Set α) (M : Type*) [AddCommMonoid M] :
    { f : α →₀ M // ↑f.support ⊆ s } ≃ (s →₀ M) where
  toFun f := subtypeDomain (· ∈ s) f.1
  invFun f := letI := Classical.decPred (· ∈ s); ⟨f.extendDomain, support_extendDomain_subset _⟩
  left_inv f :=
    letI := Classical.decPred (· ∈ s); Subtype.ext <| extendDomain_subtypeDomain f.1 f.prop
  right_inv _ := letI := Classical.decPred (· ∈ s); subtypeDomain_extendDomain _
#align finsupp.restrict_support_equiv Finsupp.restrictSupportEquiv

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
#align finsupp.dom_congr Finsupp.domCongr

@[simp]
theorem domCongr_refl [AddCommMonoid M] :
    Finsupp.domCongr (Equiv.refl α) = AddEquiv.refl (α →₀ M) :=
  AddEquiv.ext fun _ => equivMapDomain_refl _
#align finsupp.dom_congr_refl Finsupp.domCongr_refl

@[simp]
theorem domCongr_symm [AddCommMonoid M] (e : α ≃ β) :
    (Finsupp.domCongr e).symm = (Finsupp.domCongr e.symm : (β →₀ M) ≃+ (α →₀ M)) :=
  AddEquiv.ext fun _ => rfl
#align finsupp.dom_congr_symm Finsupp.domCongr_symm

@[simp]
theorem domCongr_trans [AddCommMonoid M] (e : α ≃ β) (f : β ≃ γ) :
    (Finsupp.domCongr e).trans (Finsupp.domCongr f) =
      (Finsupp.domCongr (e.trans f) : (α →₀ M) ≃+ _) :=
  AddEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm
#align finsupp.dom_congr_trans Finsupp.domCongr_trans

end Finsupp

namespace Finsupp

/-! ### Declarations about sigma types -/


section Sigma

variable {αs : ι → Type*} [Zero M] (l : (Σi, αs i) →₀ M)

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `M` and
an index element `i : ι`, `split l i` is the `i`th component of `l`,
a finitely supported function from `as i` to `M`.

This is the `Finsupp` version of `Sigma.curry`.
-/
def split (i : ι) : αs i →₀ M :=
  l.comapDomain (Sigma.mk i) fun _ _ _ _ hx => heq_iff_eq.1 (Sigma.mk.inj_iff.mp hx).2
  -- Porting note: it seems like Lean 4 never generated the `Sigma.mk.inj` lemma?
#align finsupp.split Finsupp.split

theorem split_apply (i : ι) (x : αs i) : split l i x = l ⟨i, x⟩ := by
  dsimp only [split]
  rw [comapDomain_apply]
#align finsupp.split_apply Finsupp.split_apply

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `β`,
`split_support l` is the finset of indices in `ι` that appear in the support of `l`. -/
def splitSupport (l : (Σi, αs i) →₀ M) : Finset ι :=
  haveI := Classical.decEq ι
  l.support.image Sigma.fst
#align finsupp.split_support Finsupp.splitSupport

theorem mem_splitSupport_iff_nonzero (i : ι) : i ∈ splitSupport l ↔ split l i ≠ 0 := by
  rw [splitSupport, @mem_image _ _ (Classical.decEq _), Ne, ← support_eq_empty, ← Ne, ←
    Finset.nonempty_iff_ne_empty, split, comapDomain, Finset.Nonempty]
  -- porting note (#10754): had to add the `Classical.decEq` instance manually
  simp only [exists_prop, Finset.mem_preimage, exists_and_right, exists_eq_right, mem_support_iff,
    Sigma.exists, Ne]
#align finsupp.mem_split_support_iff_nonzero Finsupp.mem_splitSupport_iff_nonzero

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
#align finsupp.split_comp Finsupp.splitComp

theorem sigma_support : l.support = l.splitSupport.sigma fun i => (l.split i).support := by
  simp only [Finset.ext_iff, splitSupport, split, comapDomain, @mem_image _ _ (Classical.decEq _),
    mem_preimage, Sigma.forall, mem_sigma]
  -- porting note (#10754): had to add the `Classical.decEq` instance manually
  tauto
#align finsupp.sigma_support Finsupp.sigma_support

theorem sigma_sum [AddCommMonoid N] (f : (Σi : ι, αs i) → M → N) :
    l.sum f = ∑ i ∈ splitSupport l, (split l i).sum fun (a : αs i) b => f ⟨i, a⟩ b := by
  simp only [sum, sigma_support, sum_sigma, split_apply]
#align finsupp.sigma_sum Finsupp.sigma_sum

variable {η : Type*} [Fintype η] {ιs : η → Type*} [Zero α]

/-- On a `Fintype η`, `Finsupp.split` is an equivalence between `(Σ (j : η), ιs j) →₀ α`
and `Π j, (ιs j →₀ α)`.

This is the `Finsupp` version of `Equiv.Pi_curry`. -/
noncomputable def sigmaFinsuppEquivPiFinsupp : ((Σj, ιs j) →₀ α) ≃ ∀ j, ιs j →₀ α where
  toFun := split
  invFun f :=
    onFinset (Finset.univ.sigma fun j => (f j).support) (fun ji => f ji.1 ji.2) fun g hg =>
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, mem_support_iff.mpr hg⟩
  left_inv f := by
    ext
    simp [split]
  right_inv f := by
    ext
    simp [split]
#align finsupp.sigma_finsupp_equiv_pi_finsupp Finsupp.sigmaFinsuppEquivPiFinsupp

@[simp]
theorem sigmaFinsuppEquivPiFinsupp_apply (f : (Σj, ιs j) →₀ α) (j i) :
    sigmaFinsuppEquivPiFinsupp f j i = f ⟨j, i⟩ :=
  rfl
#align finsupp.sigma_finsupp_equiv_pi_finsupp_apply Finsupp.sigmaFinsuppEquivPiFinsupp_apply

/-- On a `Fintype η`, `Finsupp.split` is an additive equivalence between
`(Σ (j : η), ιs j) →₀ α` and `Π j, (ιs j →₀ α)`.

This is the `AddEquiv` version of `Finsupp.sigmaFinsuppEquivPiFinsupp`.
-/
noncomputable def sigmaFinsuppAddEquivPiFinsupp {α : Type*} {ιs : η → Type*} [AddMonoid α] :
    ((Σj, ιs j) →₀ α) ≃+ ∀ j, ιs j →₀ α :=
  { sigmaFinsuppEquivPiFinsupp with
    map_add' := fun f g => by
      ext
      simp }
#align finsupp.sigma_finsupp_add_equiv_pi_finsupp Finsupp.sigmaFinsuppAddEquivPiFinsupp

@[simp]
theorem sigmaFinsuppAddEquivPiFinsupp_apply {α : Type*} {ιs : η → Type*} [AddMonoid α]
    (f : (Σj, ιs j) →₀ α) (j i) : sigmaFinsuppAddEquivPiFinsupp f j i = f ⟨j, i⟩ :=
  rfl
#align finsupp.sigma_finsupp_add_equiv_pi_finsupp_apply Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply

end Sigma

end Finsupp
