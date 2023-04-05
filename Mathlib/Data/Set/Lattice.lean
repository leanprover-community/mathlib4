/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.set.lattice
! leanprover-community/mathlib commit b86832321b586c6ac23ef8cdef6a7a27e42b13bd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Directed
import Mathlib.Order.GaloisConnection

/-!
# The set lattice

This file provides usual set notation for unions and intersections, a `CompleteLattice` instance
for `Set α`, and some more set constructions.

## Main declarations

* `Set.unionᵢ`: **i**ndexed **union**. Union of an indexed family of sets.
* `Set.interᵢ`: **i**ndexed **inter**section. Intersection of an indexed family of sets.
* `Set.interₛ`: **s**et **inter**section. Intersection of sets belonging to a set of sets.
* `Set.unionₛ`: **s**et **union**. Union of sets belonging to a set of sets.
* `Set.interₛ_eq_binterᵢ`, `Set.unionₛ_eq_binterᵢ`: Shows that `⋂₀ s = ⋂ x ∈ s, x` and
  `⋃₀ s = ⋃ x ∈ s, x`.
* `Set.completeBooleanAlgebra`: `Set α` is a `CompleteBooleanAlgebra` with `≤ = ⊆`, `< = ⊂`,
  `⊓ = ∩`, `⊔ = ∪`, `⨅ = ⋂`, `⨆ = ⋃` and `\` as the set difference. See `Set.BooleanAlgebra`.
* `Set.kern_image`: For a function `f : α → β`, `s.kern_image f` is the set of `y` such that
  `f ⁻¹ y ⊆ s`.
* `Set.seq`: Union of the image of a set under a **seq**uence of functions. `seq s t` is the union
  of `f '' t` over all `f ∈ s`, where `t : Set α` and `s : Set (α → β)`.
* `Set.unionᵢ_eq_sigma_of_disjoint`: Equivalence between `⋃ i, t i` and `Σ i, t i`, where `t` is an
  indexed family of disjoint sets.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `unionᵢ`
* `⋂ i, s i` is called `interᵢ`
* `⋃ i j, s i j` is called `unionᵢ₂`. This is a `unionᵢ` inside a `unionᵢ`.
* `⋂ i j, s i j` is called `interᵢ₂`. This is an `interᵢ` inside an `interᵢ`.
* `⋃ i ∈ s, t i` is called `bunionᵢ` for "bounded `unionᵢ`". This is the special case of `unionᵢ₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `binterᵢ` for "bounded `interᵢ`". This is the special case of `interᵢ₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `Set.unionᵢ`
* `⋂`: `Set.interᵢ`
* `⋃₀`: `Set.unionₛ`
* `⋂₀`: `Set.interₛ`
-/


open Function Tactic Set

universe u

variable {α β γ : Type _} {ι ι' ι₂ : Sort _} {κ κ₁ κ₂ : ι → Sort _} {κ' : ι' → Sort _}

namespace Set

/-! ### Complete lattice and complete Boolean algebra instances -/


instance : InfSet (Set α) :=
  ⟨fun s => { a | ∀ t ∈ s, a ∈ t }⟩

instance : SupSet (Set α) :=
  ⟨fun s => { a | ∃ t ∈ s, a ∈ t }⟩

/-- Intersection of a set of sets. -/
def interₛ (S : Set (Set α)) : Set α :=
  infₛ S
#align set.sInter Set.interₛ

/-- Notation for `Set.interₛ` Intersection of a set of sets. -/
prefix:110 "⋂₀ " => interₛ

/-- Intersection of a set of sets. -/
def unionₛ (S : Set (Set α)) : Set α :=
  supₛ S
#align set.sUnion Set.unionₛ

/-- Notation for Set.unionₛ`. Union of a set of sets. -/
prefix:110 "⋃₀ " => unionₛ

@[simp]
theorem mem_interₛ {x : α} {S : Set (Set α)} : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t :=
  Iff.rfl
#align set.mem_sInter Set.mem_interₛ

@[simp]
theorem mem_unionₛ {x : α} {S : Set (Set α)} : x ∈ ⋃₀S ↔ ∃ t ∈ S, x ∈ t :=
  Iff.rfl
#align set.mem_sUnion Set.mem_unionₛ

/-- Indexed union of a family of sets -/
def unionᵢ (s : ι → Set β) : Set β :=
  supᵢ s
#align set.Union Set.unionᵢ

/-- Indexed intersection of a family of sets -/
def interᵢ (s : ι → Set β) : Set β :=
  infᵢ s
#align set.Inter Set.interᵢ

/-- Notation for `Set.unionᵢ`. Indexed union of a family of sets -/
notation3"⋃ "(...)", "r:(scoped f => unionᵢ f) => r

/-- Notation for `Set.interᵢ`. Indexed intersection of a family of sets -/
notation3"⋂ "(...)", "r:(scoped f => interᵢ f) => r

@[simp]
theorem supₛ_eq_unionₛ (S : Set (Set α)) : supₛ S = ⋃₀S :=
  rfl
#align set.Sup_eq_sUnion Set.supₛ_eq_unionₛ

@[simp]
theorem infₛ_eq_interₛ (S : Set (Set α)) : infₛ S = ⋂₀ S :=
  rfl
#align set.Inf_eq_sInter Set.infₛ_eq_interₛ

@[simp]
theorem supᵢ_eq_unionᵢ (s : ι → Set α) : supᵢ s = unionᵢ s :=
  rfl
#align set.supr_eq_Union Set.supᵢ_eq_unionᵢ

@[simp]
theorem infᵢ_eq_interᵢ (s : ι → Set α) : infᵢ s = interᵢ s :=
  rfl
#align set.infi_eq_Inter Set.infᵢ_eq_interᵢ

@[simp]
theorem mem_unionᵢ {x : α} {s : ι → Set α} : (x ∈ ⋃ i, s i) ↔ ∃ i, x ∈ s i :=
  ⟨fun ⟨_, ⟨⟨a, (t_eq : s a = _)⟩, (h : x ∈ _)⟩⟩ => ⟨a, t_eq.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩
#align set.mem_Union Set.mem_unionᵢ

@[simp]
theorem mem_interᵢ {x : α} {s : ι → Set α} : (x ∈ ⋂ i, s i) ↔ ∀ i, x ∈ s i :=
  ⟨fun (h : ∀ a ∈ { a : Set α | ∃ i, s i = a }, x ∈ a) a => h (s a) ⟨a, rfl⟩,
    fun h _ ⟨a, (eq : s a = _)⟩ => eq ▸ h a⟩
#align set.mem_Inter Set.mem_interᵢ

theorem mem_unionᵢ₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋃ (i) (j), s i j) ↔ ∃ i j, x ∈ s i j := by
  simp_rw [mem_unionᵢ]
#align set.mem_Union₂ Set.mem_unionᵢ₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_interᵢ₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋂ (i) (j), s i j) ↔ ∀ i j, x ∈ s i j := by
  simp_rw [mem_interᵢ]
#align set.mem_Inter₂ Set.mem_interᵢ₂

theorem mem_unionᵢ_of_mem {s : ι → Set α} {a : α} (i : ι) (ha : a ∈ s i) : a ∈ ⋃ i, s i :=
  mem_unionᵢ.2 ⟨i, ha⟩
#align set.mem_Union_of_mem Set.mem_unionᵢ_of_mem

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_unionᵢ₂_of_mem {s : ∀ i, κ i → Set α} {a : α} {i : ι} (j : κ i) (ha : a ∈ s i j) :
    a ∈ ⋃ (i) (j), s i j :=
  mem_unionᵢ₂.2 ⟨i, j, ha⟩
#align set.mem_Union₂_of_mem Set.mem_unionᵢ₂_of_mem

theorem mem_interᵢ_of_mem {s : ι → Set α} {a : α} (h : ∀ i, a ∈ s i) : a ∈ ⋂ i, s i :=
  mem_interᵢ.2 h
#align set.mem_Inter_of_mem Set.mem_interᵢ_of_mem

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_interᵢ₂_of_mem {s : ∀ i, κ i → Set α} {a : α} (h : ∀ i j, a ∈ s i j) :
    a ∈ ⋂ (i) (j), s i j :=
  mem_interᵢ₂.2 h
#align set.mem_Inter₂_of_mem Set.mem_interᵢ₂_of_mem

instance : CompleteBooleanAlgebra (Set α) :=
  { instBooleanAlgebraSet with
    le_supₛ := fun s t t_in a a_in => ⟨t, t_in, a_in⟩
    supₛ_le := fun s t h a ⟨t', ⟨t'_in, a_in⟩⟩ => h t' t'_in a_in
    le_infₛ := fun s t h a a_in t' t'_in => h t' t'_in a_in
    infₛ_le := fun s t t_in a h => h _ t_in
    infᵢ_sup_le_sup_infₛ := fun s S x => Iff.mp <| by simp [forall_or_left]
    inf_supₛ_le_supᵢ_inf := fun s S x => Iff.mp <| by simp [exists_and_left] }

section GaloisConnection

variable {f : α → β}

protected theorem image_preimage : GaloisConnection (image f) (preimage f) := fun _ _ =>
  image_subset_iff
#align set.image_preimage Set.image_preimage

/-- `kernImage f s` is the set of `y` such that `f ⁻¹ y ⊆ s`. -/
def kernImage (f : α → β) (s : Set α) : Set β :=
  { y | ∀ ⦃x⦄, f x = y → x ∈ s }
#align set.kern_image Set.kernImage

protected theorem preimage_kernImage : GaloisConnection (preimage f) (kernImage f) := fun a _ =>
  ⟨fun h _ hx y hy =>
    have : f y ∈ a := hy.symm ▸ hx
    h this,
    fun h x (hx : f x ∈ a) => h hx rfl⟩
#align set.preimage_kern_image Set.preimage_kernImage

end GaloisConnection

/-! ### Union and intersection over an indexed family of sets -/


instance : OrderTop (Set α) where
  top := univ
  le_top := by simp

@[congr]
theorem unionᵢ_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : unionᵢ f₁ = unionᵢ f₂ :=
  supᵢ_congr_Prop pq f
#align set.Union_congr_Prop Set.unionᵢ_congr_Prop

@[congr]
theorem interᵢ_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : interᵢ f₁ = interᵢ f₂ :=
  infᵢ_congr_Prop pq f
#align set.Inter_congr_Prop Set.interᵢ_congr_Prop

theorem unionᵢ_plift_up (f : PLift ι → Set α) : (⋃ i, f (PLift.up i)) = ⋃ i, f i :=
  supᵢ_plift_up _
#align set.Union_plift_up Set.unionᵢ_plift_up

theorem unionᵢ_plift_down (f : ι → Set α) : (⋃ i, f (PLift.down i)) = ⋃ i, f i :=
  supᵢ_plift_down _
#align set.Union_plift_down Set.unionᵢ_plift_down

theorem interᵢ_plift_up (f : PLift ι → Set α) : (⋂ i, f (PLift.up i)) = ⋂ i, f i :=
  infᵢ_plift_up _
#align set.Inter_plift_up Set.interᵢ_plift_up

theorem interᵢ_plift_down (f : ι → Set α) : (⋂ i, f (PLift.down i)) = ⋂ i, f i :=
  infᵢ_plift_down _
#align set.Inter_plift_down Set.interᵢ_plift_down

theorem unionᵢ_eq_if {p : Prop} [Decidable p] (s : Set α) : (⋃ _h : p, s) = if p then s else ∅ :=
  supᵢ_eq_if _
#align set.Union_eq_if Set.unionᵢ_eq_if

theorem unionᵢ_eq_dif {p : Prop} [Decidable p] (s : p → Set α) :
    (⋃ h : p, s h) = if h : p then s h else ∅ :=
  supᵢ_eq_dif _
#align set.Union_eq_dif Set.unionᵢ_eq_dif

theorem interᵢ_eq_if {p : Prop} [Decidable p] (s : Set α) : (⋂ _h : p, s) = if p then s else univ :=
  infᵢ_eq_if _
#align set.Inter_eq_if Set.interᵢ_eq_if

theorem infᵢ_eq_dif {p : Prop} [Decidable p] (s : p → Set α) :
    (⋂ h : p, s h) = if h : p then s h else univ :=
  _root_.infᵢ_eq_dif _
#align set.Infi_eq_dif Set.infᵢ_eq_dif

theorem exists_set_mem_of_union_eq_top {ι : Type _} (t : Set ι) (s : ι → Set β)
    (w : (⋃ i ∈ t, s i) = ⊤) (x : β) : ∃ i ∈ t, x ∈ s i := by
  have p : x ∈ ⊤ := Set.mem_univ x
  rw [← w, Set.mem_unionᵢ] at p
  simpa using p
#align set.exists_set_mem_of_union_eq_top Set.exists_set_mem_of_union_eq_top

theorem nonempty_of_union_eq_top_of_nonempty {ι : Type _} (t : Set ι) (s : ι → Set α)
    (H : Nonempty α) (w : (⋃ i ∈ t, s i) = ⊤) : t.Nonempty := by
  obtain ⟨x, m, -⟩ := exists_set_mem_of_union_eq_top t s w H.some
  exact ⟨x, m⟩
#align set.nonempty_of_union_eq_top_of_nonempty Set.nonempty_of_union_eq_top_of_nonempty

theorem setOf_exists (p : ι → β → Prop) : { x | ∃ i, p i x } = ⋃ i, { x | p i x } :=
  ext fun _ => mem_unionᵢ.symm
#align set.set_of_exists Set.setOf_exists

theorem setOf_forall (p : ι → β → Prop) : { x | ∀ i, p i x } = ⋂ i, { x | p i x } :=
  ext fun _ => mem_interᵢ.symm
#align set.set_of_forall Set.setOf_forall

theorem unionᵢ_subset {s : ι → Set α} {t : Set α} (h : ∀ i, s i ⊆ t) : (⋃ i, s i) ⊆ t :=
  supᵢ_le h
#align set.Union_subset Set.unionᵢ_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ₂_subset {s : ∀ i, κ i → Set α} {t : Set α} (h : ∀ i j, s i j ⊆ t) :
    (⋃ (i) (j), s i j) ⊆ t :=
  unionᵢ_subset fun x => unionᵢ_subset (h x)
#align set.Union₂_subset Set.unionᵢ₂_subset

theorem subset_interᵢ {t : Set β} {s : ι → Set β} (h : ∀ i, t ⊆ s i) : t ⊆ ⋂ i, s i :=
  le_infᵢ h
#align set.subset_Inter Set.subset_interᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem subset_interᵢ₂ {s : Set α} {t : ∀ i, κ i → Set α} (h : ∀ i j, s ⊆ t i j) :
    s ⊆ ⋂ (i) (j), t i j :=
  subset_interᵢ fun x => subset_interᵢ <| h x
#align set.subset_Inter₂ Set.subset_interᵢ₂

@[simp]
theorem unionᵢ_subset_iff {s : ι → Set α} {t : Set α} : (⋃ i, s i) ⊆ t ↔ ∀ i, s i ⊆ t :=
  ⟨fun h _ => Subset.trans (le_supᵢ s _) h, unionᵢ_subset⟩
#align set.Union_subset_iff Set.unionᵢ_subset_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ₂_subset_iff {s : ∀ i, κ i → Set α} {t : Set α} :
    (⋃ (i) (j), s i j) ⊆ t ↔ ∀ i j, s i j ⊆ t := by simp_rw [unionᵢ_subset_iff]
#align set.Union₂_subset_iff Set.unionᵢ₂_subset_iff

@[simp]
theorem subset_interᵢ_iff {s : Set α} {t : ι → Set α} : (s ⊆ ⋂ i, t i) ↔ ∀ i, s ⊆ t i :=
  le_infᵢ_iff
#align set.subset_Inter_iff Set.subset_interᵢ_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
--Porting note: removing `simp`. `simp` can prove it
theorem subset_interᵢ₂_iff {s : Set α} {t : ∀ i, κ i → Set α} :
    (s ⊆ ⋂ (i) (j), t i j) ↔ ∀ i j, s ⊆ t i j := by simp_rw [subset_interᵢ_iff]
#align set.subset_Inter₂_iff Set.subset_interᵢ₂_iff

theorem subset_unionᵢ : ∀ (s : ι → Set β) (i : ι), s i ⊆ ⋃ i, s i :=
  le_supᵢ
#align set.subset_Union Set.subset_unionᵢ

theorem interᵢ_subset : ∀ (s : ι → Set β) (i : ι), (⋂ i, s i) ⊆ s i :=
  infᵢ_le
#align set.Inter_subset Set.interᵢ_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem subset_unionᵢ₂ {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : s i j ⊆ ⋃ (i') (j'), s i' j' :=
  le_supᵢ₂ i j
#align set.subset_Union₂ Set.subset_unionᵢ₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem interᵢ₂_subset {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : (⋂ (i) (j), s i j) ⊆ s i j :=
  infᵢ₂_le i j
#align set.Inter₂_subset Set.interᵢ₂_subset

/-- This rather trivial consequence of `subset_unionᵢ`is convenient with `apply`, and has `i`
explicit for this purpose. -/
theorem subset_unionᵢ_of_subset {s : Set α} {t : ι → Set α} (i : ι) (h : s ⊆ t i) : s ⊆ ⋃ i, t i :=
  le_supᵢ_of_le i h
#align set.subset_Union_of_subset Set.subset_unionᵢ_of_subset

/-- This rather trivial consequence of `interᵢ_subset`is convenient with `apply`, and has `i`
explicit for this purpose. -/
theorem interᵢ_subset_of_subset {s : ι → Set α} {t : Set α} (i : ι) (h : s i ⊆ t) :
    (⋂ i, s i) ⊆ t :=
  infᵢ_le_of_le i h
#align set.Inter_subset_of_subset Set.interᵢ_subset_of_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- This rather trivial consequence of `subset_unionᵢ₂` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
theorem subset_unionᵢ₂_of_subset {s : Set α} {t : ∀ i, κ i → Set α} (i : ι) (j : κ i)
    (h : s ⊆ t i j) : s ⊆ ⋃ (i) (j), t i j :=
  le_supᵢ₂_of_le i j h
#align set.subset_Union₂_of_subset Set.subset_unionᵢ₂_of_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- This rather trivial consequence of `interᵢ₂_subset` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
theorem interᵢ₂_subset_of_subset {s : ∀ i, κ i → Set α} {t : Set α} (i : ι) (j : κ i)
    (h : s i j ⊆ t) : (⋂ (i) (j), s i j) ⊆ t :=
  infᵢ₂_le_of_le i j h
#align set.Inter₂_subset_of_subset Set.interᵢ₂_subset_of_subset

theorem unionᵢ_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : (⋃ i, s i) ⊆ ⋃ i, t i :=
  supᵢ_mono h
#align set.Union_mono Set.unionᵢ_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) :
    (⋃ (i) (j), s i j) ⊆ ⋃ (i) (j), t i j :=
  supᵢ₂_mono h
#align set.Union₂_mono Set.unionᵢ₂_mono

theorem interᵢ_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : (⋂ i, s i) ⊆ ⋂ i, t i :=
  infᵢ_mono h
#align set.Inter_mono Set.interᵢ_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem interᵢ₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) :
    (⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), t i j :=
  infᵢ₂_mono h
#align set.Inter₂_mono Set.interᵢ₂_mono

theorem unionᵢ_mono' {s : ι → Set α} {t : ι₂ → Set α} (h : ∀ i, ∃ j, s i ⊆ t j) :
    (⋃ i, s i) ⊆ ⋃ i, t i :=
  supᵢ_mono' h
#align set.Union_mono' Set.unionᵢ_mono'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' j') -/
theorem unionᵢ₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α}
    (h : ∀ i j, ∃ i' j', s i j ⊆ t i' j') : (⋃ (i) (j), s i j) ⊆ ⋃ (i') (j'), t i' j' :=
  supᵢ₂_mono' h
#align set.Union₂_mono' Set.unionᵢ₂_mono'

theorem interᵢ_mono' {s : ι → Set α} {t : ι' → Set α} (h : ∀ j, ∃ i, s i ⊆ t j) :
    (⋂ i, s i) ⊆ ⋂ j, t j :=
  Set.subset_interᵢ fun j =>
    let ⟨i, hi⟩ := h j
    interᵢ_subset_of_subset i hi
#align set.Inter_mono' Set.interᵢ_mono'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' j') -/
theorem interᵢ₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α}
    (h : ∀ i' j', ∃ i j, s i j ⊆ t i' j') : (⋂ (i) (j), s i j) ⊆ ⋂ (i') (j'), t i' j' :=
  subset_interᵢ₂_iff.2 fun i' j' =>
    let ⟨_, _, hst⟩ := h i' j'
    (interᵢ₂_subset _ _).trans hst
#align set.Inter₂_mono' Set.interᵢ₂_mono'

theorem unionᵢ₂_subset_unionᵢ (κ : ι → Sort _) (s : ι → Set α) :
    (⋃ (i) (_j : κ i), s i) ⊆ ⋃ i, s i :=
  unionᵢ_mono fun _ => unionᵢ_subset fun _ => Subset.rfl
#align set.Union₂_subset_Union Set.unionᵢ₂_subset_unionᵢ

theorem interᵢ_subset_interᵢ₂ (κ : ι → Sort _) (s : ι → Set α) :
    (⋂ i, s i) ⊆ ⋂ (i) (_j : κ i), s i :=
  interᵢ_mono fun _ => subset_interᵢ fun _ => Subset.rfl
#align set.Inter_subset_Inter₂ Set.interᵢ_subset_interᵢ₂

theorem unionᵢ_setOf (P : ι → α → Prop) : (⋃ i, { x : α | P i x }) = { x : α | ∃ i, P i x } := by
  ext
  exact mem_unionᵢ
#align set.Union_set_of Set.unionᵢ_setOf

theorem interᵢ_setOf (P : ι → α → Prop) : (⋂ i, { x : α | P i x }) = { x : α | ∀ i, P i x } := by
  ext
  exact mem_interᵢ
#align set.Inter_set_of Set.interᵢ_setOf

theorem unionᵢ_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⋃ x, f x) = ⋃ y, g y :=
  h1.supᵢ_congr h h2
#align set.Union_congr_of_surjective Set.unionᵢ_congr_of_surjective

theorem interᵢ_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⋂ x, f x) = ⋂ y, g y :=
  h1.infᵢ_congr h h2
#align set.Inter_congr_of_surjective Set.interᵢ_congr_of_surjective

lemma unionᵢ_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : (⋃ i, s i) = ⋃ i, t i := supᵢ_congr h
#align set.Union_congr Set.unionᵢ_congr
lemma interᵢ_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : (⋂ i, s i) = ⋂ i, t i := infᵢ_congr h
#align set.Inter_congr Set.interᵢ_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
lemma unionᵢ₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) :
    (⋃ (i) (j), s i j) = ⋃ (i) (j), t i j :=
  unionᵢ_congr fun i => unionᵢ_congr <| h i
#align set.Union₂_congr Set.unionᵢ₂_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
lemma interᵢ₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) :
    (⋂ (i) (j), s i j) = ⋂ (i) (j), t i j :=
  interᵢ_congr fun i => interᵢ_congr <| h i
#align set.Inter₂_congr Set.interᵢ₂_congr

section Nonempty
variable [Nonempty ι] {f : ι → Set α} {s : Set α}

lemma unionᵢ_const (s : Set β) : (⋃ _i : ι, s) = s := supᵢ_const
#align set.Union_const Set.unionᵢ_const
lemma interᵢ_const (s : Set β) : (⋂ _i : ι, s) = s := infᵢ_const
#align set.Inter_const Set.interᵢ_const

lemma unionᵢ_eq_const (hf : ∀ i, f i = s) : (⋃ i, f i) = s :=
(unionᵢ_congr hf).trans $ unionᵢ_const _
#align set.Union_eq_const Set.unionᵢ_eq_const

lemma interᵢ_eq_const (hf : ∀ i, f i = s) : (⋂ i, f i) = s :=
(interᵢ_congr hf).trans $ interᵢ_const _
#align set.Inter_eq_const Set.interᵢ_eq_const

end Nonempty

@[simp]
theorem compl_unionᵢ (s : ι → Set β) : (⋃ i, s i)ᶜ = ⋂ i, s iᶜ :=
  compl_supᵢ
#align set.compl_Union Set.compl_unionᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem compl_unionᵢ₂ (s : ∀ i, κ i → Set α) : (⋃ (i) (j), s i j)ᶜ = ⋂ (i) (j), s i jᶜ := by
  simp_rw [compl_unionᵢ]
#align set.compl_Union₂ Set.compl_unionᵢ₂

@[simp]
theorem compl_interᵢ (s : ι → Set β) : (⋂ i, s i)ᶜ = ⋃ i, s iᶜ :=
  compl_infᵢ
#align set.compl_Inter Set.compl_interᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem compl_interᵢ₂ (s : ∀ i, κ i → Set α) : (⋂ (i) (j), s i j)ᶜ = ⋃ (i) (j), s i jᶜ := by
  simp_rw [compl_interᵢ]
#align set.compl_Inter₂ Set.compl_interᵢ₂

-- classical -- complete_boolean_algebra
theorem unionᵢ_eq_compl_interᵢ_compl (s : ι → Set β) : (⋃ i, s i) = (⋂ i, s iᶜ)ᶜ := by
  simp only [compl_interᵢ, compl_compl]
#align set.Union_eq_compl_Inter_compl Set.unionᵢ_eq_compl_interᵢ_compl

-- classical -- complete_boolean_algebra
theorem interᵢ_eq_compl_unionᵢ_compl (s : ι → Set β) : (⋂ i, s i) = (⋃ i, s iᶜ)ᶜ := by
  simp only [compl_unionᵢ, compl_compl]
#align set.Inter_eq_compl_Union_compl Set.interᵢ_eq_compl_unionᵢ_compl

theorem inter_unionᵢ (s : Set β) (t : ι → Set β) : (s ∩ ⋃ i, t i) = ⋃ i, s ∩ t i :=
  inf_supᵢ_eq _ _
#align set.inter_Union Set.inter_unionᵢ

theorem unionᵢ_inter (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∩ s = ⋃ i, t i ∩ s :=
  supᵢ_inf_eq _ _
#align set.Union_inter Set.unionᵢ_inter

theorem unionᵢ_union_distrib (s : ι → Set β) (t : ι → Set β) :
    (⋃ i, s i ∪ t i) = (⋃ i, s i) ∪ ⋃ i, t i :=
  supᵢ_sup_eq
#align set.Union_union_distrib Set.unionᵢ_union_distrib

theorem interᵢ_inter_distrib (s : ι → Set β) (t : ι → Set β) :
    (⋂ i, s i ∩ t i) = (⋂ i, s i) ∩ ⋂ i, t i :=
  infᵢ_inf_eq
#align set.Inter_inter_distrib Set.interᵢ_inter_distrib

theorem union_unionᵢ [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∪ ⋃ i, t i) = ⋃ i, s ∪ t i :=
  sup_supᵢ
#align set.union_Union Set.union_unionᵢ

theorem unionᵢ_union [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∪ s = ⋃ i, t i ∪ s :=
  supᵢ_sup
#align set.Union_union Set.unionᵢ_union

theorem inter_interᵢ [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∩ ⋂ i, t i) = ⋂ i, s ∩ t i :=
  inf_infᵢ
#align set.inter_Inter Set.inter_interᵢ

theorem interᵢ_inter [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋂ i, t i) ∩ s = ⋂ i, t i ∩ s :=
  infᵢ_inf
#align set.Inter_inter Set.interᵢ_inter

-- classical
theorem union_interᵢ (s : Set β) (t : ι → Set β) : (s ∪ ⋂ i, t i) = ⋂ i, s ∪ t i :=
  sup_infᵢ_eq _ _
#align set.union_Inter Set.union_interᵢ

theorem interᵢ_union (s : ι → Set β) (t : Set β) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  infᵢ_sup_eq _ _
#align set.Inter_union Set.interᵢ_union

theorem unionᵢ_diff (s : Set β) (t : ι → Set β) : (⋃ i, t i) \ s = ⋃ i, t i \ s :=
  unionᵢ_inter _ _
#align set.Union_diff Set.unionᵢ_diff

theorem diff_unionᵢ [Nonempty ι] (s : Set β) (t : ι → Set β) : (s \ ⋃ i, t i) = ⋂ i, s \ t i := by
  rw [diff_eq, compl_unionᵢ, inter_interᵢ]; rfl
#align set.diff_Union Set.diff_unionᵢ

theorem diff_interᵢ (s : Set β) (t : ι → Set β) : (s \ ⋂ i, t i) = ⋃ i, s \ t i := by
  rw [diff_eq, compl_interᵢ, inter_unionᵢ]; rfl
#align set.diff_Inter Set.diff_interᵢ

theorem directed_on_unionᵢ {r} {f : ι → Set α} (hd : Directed (· ⊆ ·) f)
    (h : ∀ x, DirectedOn r (f x)) : DirectedOn r (⋃ x, f x) := by
  simp only [DirectedOn, exists_prop, mem_unionᵢ, exists_imp]
  exact fun a₁ b₁ fb₁ a₂ b₂ fb₂ =>
    let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂
    let ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
    ⟨x, ⟨z, xf⟩, xa₁, xa₂⟩
#align set.directed_on_Union Set.directed_on_unionᵢ

theorem unionᵢ_inter_subset {ι α} {s t : ι → Set α} : (⋃ i, s i ∩ t i) ⊆ (⋃ i, s i) ∩ ⋃ i, t i :=
  le_supᵢ_inf_supᵢ s t
#align set.Union_inter_subset Set.unionᵢ_inter_subset

theorem unionᵢ_inter_of_monotone {ι α} [Preorder ι] [IsDirected ι (· ≤ ·)] {s t : ι → Set α}
    (hs : Monotone s) (ht : Monotone t) : (⋃ i, s i ∩ t i) = (⋃ i, s i) ∩ ⋃ i, t i :=
  supᵢ_inf_of_monotone hs ht
#align set.Union_inter_of_monotone Set.unionᵢ_inter_of_monotone

theorem unionᵢ_inter_of_antitone {ι α} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {s t : ι → Set α}
    (hs : Antitone s) (ht : Antitone t) : (⋃ i, s i ∩ t i) = (⋃ i, s i) ∩ ⋃ i, t i :=
  supᵢ_inf_of_antitone hs ht
#align set.Union_inter_of_antitone Set.unionᵢ_inter_of_antitone

theorem interᵢ_union_of_monotone {ι α} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {s t : ι → Set α}
    (hs : Monotone s) (ht : Monotone t) : (⋂ i, s i ∪ t i) = (⋂ i, s i) ∪ ⋂ i, t i :=
  infᵢ_sup_of_monotone hs ht
#align set.Inter_union_of_monotone Set.interᵢ_union_of_monotone

theorem interᵢ_union_of_antitone {ι α} [Preorder ι] [IsDirected ι (· ≤ ·)] {s t : ι → Set α}
    (hs : Antitone s) (ht : Antitone t) : (⋂ i, s i ∪ t i) = (⋂ i, s i) ∪ ⋂ i, t i :=
  infᵢ_sup_of_antitone hs ht
#align set.Inter_union_of_antitone Set.interᵢ_union_of_antitone

/-- An equality version of this lemma is `unionᵢ_interᵢ_of_monotone` in `Data.Set.Finite`. -/
theorem unionᵢ_interᵢ_subset {s : ι → ι' → Set α} : (⋃ j, ⋂ i, s i j) ⊆ ⋂ i, ⋃ j, s i j :=
  supᵢ_infᵢ_le_infᵢ_supᵢ (flip s)
#align set.Union_Inter_subset Set.unionᵢ_interᵢ_subset

theorem unionᵢ_option {ι} (s : Option ι → Set α) : (⋃ o, s o) = s none ∪ ⋃ i, s (some i) :=
  supᵢ_option s
#align set.Union_option Set.unionᵢ_option

theorem interᵢ_option {ι} (s : Option ι → Set α) : (⋂ o, s o) = s none ∩ ⋂ i, s (some i) :=
  infᵢ_option s
#align set.Inter_option Set.interᵢ_option

section

variable (p : ι → Prop) [DecidablePred p]

theorem unionᵢ_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    (⋃ i, if h : p i then f i h else g i h) = (⋃ (i) (h : p i), f i h) ∪ ⋃ (i) (h : ¬p i), g i h :=
  supᵢ_dite _ _ _
#align set.Union_dite Set.unionᵢ_dite

theorem unionᵢ_ite (f g : ι → Set α) :
    (⋃ i, if p i then f i else g i) = (⋃ (i) (_h : p i), f i) ∪ ⋃ (i) (_h : ¬p i), g i :=
  unionᵢ_dite _ _ _
#align set.Union_ite Set.unionᵢ_ite

theorem interᵢ_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    (⋂ i, if h : p i then f i h else g i h) = (⋂ (i) (h : p i), f i h) ∩ ⋂ (i) (h : ¬p i), g i h :=
  infᵢ_dite _ _ _
#align set.Inter_dite Set.interᵢ_dite

theorem interᵢ_ite (f g : ι → Set α) :
    (⋂ i, if p i then f i else g i) = (⋂ (i) (_h : p i), f i) ∩ ⋂ (i) (_h : ¬p i), g i :=
  interᵢ_dite _ _ _
#align set.Inter_ite Set.interᵢ_ite

end

theorem image_projection_prod {ι : Type _} {α : ι → Type _} {v : ∀ i : ι, Set (α i)}
    (hv : (pi univ v).Nonempty) (i : ι) :
    ((fun x : ∀ i : ι, α i => x i) '' ⋂ k, (fun x : ∀ j : ι, α j => x k) ⁻¹' v k) = v i := by
  classical
    apply Subset.antisymm
    · simp [interᵢ_subset]
    · intro y y_in
      simp only [mem_image, mem_interᵢ, mem_preimage]
      rcases hv with ⟨z, hz⟩
      refine' ⟨Function.update z i y, _, update_same i y z⟩
      rw [@forall_update_iff ι α _ z i y fun i t => t ∈ v i]
      exact ⟨y_in, fun j _ => by simpa using hz j⟩
#align set.image_projection_prod Set.image_projection_prod

/-! ### Unions and intersections indexed by `Prop` -/


theorem interᵢ_false {s : False → Set α} : interᵢ s = univ :=
  infᵢ_false
#align set.Inter_false Set.interᵢ_false

theorem unionᵢ_false {s : False → Set α} : unionᵢ s = ∅ :=
  supᵢ_false
#align set.Union_false Set.unionᵢ_false

@[simp]
theorem interᵢ_true {s : True → Set α} : interᵢ s = s trivial :=
  infᵢ_true
#align set.Inter_true Set.interᵢ_true

@[simp]
theorem unionᵢ_true {s : True → Set α} : unionᵢ s = s trivial :=
  supᵢ_true
#align set.Union_true Set.unionᵢ_true

@[simp]
theorem interᵢ_exists {p : ι → Prop} {f : Exists p → Set α} :
    (⋂ x, f x) = ⋂ (i) (h : p i), f ⟨i, h⟩ :=
  infᵢ_exists
#align set.Inter_exists Set.interᵢ_exists

@[simp]
theorem unionᵢ_exists {p : ι → Prop} {f : Exists p → Set α} :
    (⋃ x, f x) = ⋃ (i) (h : p i), f ⟨i, h⟩ :=
  supᵢ_exists
#align set.Union_exists Set.unionᵢ_exists

@[simp]
theorem unionᵢ_empty : (⋃ _i : ι, ∅ : Set α) = ∅ :=
  supᵢ_bot
#align set.Union_empty Set.unionᵢ_empty

@[simp]
theorem interᵢ_univ : (⋂ _i : ι, univ : Set α) = univ :=
  infᵢ_top
#align set.Inter_univ Set.interᵢ_univ

section

variable {s : ι → Set α}

@[simp]
theorem unionᵢ_eq_empty : (⋃ i, s i) = ∅ ↔ ∀ i, s i = ∅ :=
  supᵢ_eq_bot
#align set.Union_eq_empty Set.unionᵢ_eq_empty

@[simp]
theorem interᵢ_eq_univ : (⋂ i, s i) = univ ↔ ∀ i, s i = univ :=
  infᵢ_eq_top
#align set.Inter_eq_univ Set.interᵢ_eq_univ

@[simp]
theorem nonempty_unionᵢ : (⋃ i, s i).Nonempty ↔ ∃ i, (s i).Nonempty := by
  simp [nonempty_iff_ne_empty]
#align set.nonempty_Union Set.nonempty_unionᵢ

--Porting note: removing `simp`. `simp` can prove it
theorem nonempty_bunionᵢ {t : Set α} {s : α → Set β} :
    (⋃ i ∈ t, s i).Nonempty ↔ ∃ i ∈ t, (s i).Nonempty := by simp
#align set.nonempty_bUnion Set.nonempty_bunionᵢ

theorem unionᵢ_nonempty_index (s : Set α) (t : s.Nonempty → Set β) :
    (⋃ h, t h) = ⋃ x ∈ s, t ⟨x, ‹_›⟩ :=
  supᵢ_exists
#align set.Union_nonempty_index Set.unionᵢ_nonempty_index

end

@[simp]
theorem interᵢ_interᵢ_eq_left {b : β} {s : ∀ x : β, x = b → Set α} :
    (⋂ (x) (h : x = b), s x h) = s b rfl :=
  infᵢ_infᵢ_eq_left
#align set.Inter_Inter_eq_left Set.interᵢ_interᵢ_eq_left

@[simp]
theorem interᵢ_interᵢ_eq_right {b : β} {s : ∀ x : β, b = x → Set α} :
    (⋂ (x) (h : b = x), s x h) = s b rfl :=
  infᵢ_infᵢ_eq_right
#align set.Inter_Inter_eq_right Set.interᵢ_interᵢ_eq_right

@[simp]
theorem unionᵢ_unionᵢ_eq_left {b : β} {s : ∀ x : β, x = b → Set α} :
    (⋃ (x) (h : x = b), s x h) = s b rfl :=
  supᵢ_supᵢ_eq_left
#align set.Union_Union_eq_left Set.unionᵢ_unionᵢ_eq_left

@[simp]
theorem unionᵢ_unionᵢ_eq_right {b : β} {s : ∀ x : β, b = x → Set α} :
    (⋃ (x) (h : b = x), s x h) = s b rfl :=
  supᵢ_supᵢ_eq_right
#align set.Union_Union_eq_right Set.unionᵢ_unionᵢ_eq_right

theorem interᵢ_or {p q : Prop} (s : p ∨ q → Set α) :
    (⋂ h, s h) = (⋂ h : p, s (Or.inl h)) ∩ ⋂ h : q, s (Or.inr h) :=
  infᵢ_or
#align set.Inter_or Set.interᵢ_or

theorem unionᵢ_or {p q : Prop} (s : p ∨ q → Set α) :
    (⋃ h, s h) = (⋃ i, s (Or.inl i)) ∪ ⋃ j, s (Or.inr j) :=
  supᵢ_or
#align set.Union_or Set.unionᵢ_or

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (hp hq) -/
theorem unionᵢ_and {p q : Prop} (s : p ∧ q → Set α) : (⋃ h, s h) = ⋃ (hp) (hq), s ⟨hp, hq⟩ :=
  supᵢ_and
#align set.Union_and Set.unionᵢ_and

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (hp hq) -/
theorem interᵢ_and {p q : Prop} (s : p ∧ q → Set α) : (⋂ h, s h) = ⋂ (hp) (hq), s ⟨hp, hq⟩ :=
  infᵢ_and
#align set.Inter_and Set.interᵢ_and

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i i') -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' i) -/
theorem unionᵢ_comm (s : ι → ι' → Set α) : (⋃ (i) (i'), s i i') = ⋃ (i') (i), s i i' :=
  supᵢ_comm
#align set.Union_comm Set.unionᵢ_comm

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i i') -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' i) -/
theorem interᵢ_comm (s : ι → ι' → Set α) : (⋂ (i) (i'), s i i') = ⋂ (i') (i), s i i' :=
  infᵢ_comm
#align set.Inter_comm Set.interᵢ_comm

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem unionᵢ₂_comm (s : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Set α) :
    (⋃ (i₁) (j₁) (i₂) (j₂), s i₁ j₁ i₂ j₂) = ⋃ (i₂) (j₂) (i₁) (j₁), s i₁ j₁ i₂ j₂ :=
  supᵢ₂_comm _
#align set.Union₂_comm Set.unionᵢ₂_comm

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem interᵢ₂_comm (s : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Set α) :
    (⋂ (i₁) (j₁) (i₂) (j₂), s i₁ j₁ i₂ j₂) = ⋂ (i₂) (j₂) (i₁) (j₁), s i₁ j₁ i₂ j₂ :=
  infᵢ₂_comm _
#align set.Inter₂_comm Set.interᵢ₂_comm

@[simp]
theorem bunionᵢ_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    (⋃ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h) =
      ⋃ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ :=
  by simp only [unionᵢ_and, @unionᵢ_comm _ ι']
#align set.bUnion_and Set.bunionᵢ_and

@[simp]
theorem bunionᵢ_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    (⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h) =
      ⋃ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ :=
  by simp only [unionᵢ_and, @unionᵢ_comm _ ι]
#align set.bUnion_and' Set.bunionᵢ_and'

@[simp]
theorem binterᵢ_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    (⋂ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h) =
      ⋂ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ :=
  by simp only [interᵢ_and, @interᵢ_comm _ ι']
#align set.bInter_and Set.binterᵢ_and

@[simp]
theorem binterᵢ_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    (⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h) =
      ⋂ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ :=
  by simp only [interᵢ_and, @interᵢ_comm _ ι]
#align set.bInter_and' Set.binterᵢ_and'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x h) -/
@[simp]
theorem unionᵢ_unionᵢ_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    (⋃ (x) (h), s x h) = s b (Or.inl rfl) ∪ ⋃ (x) (h : p x), s x (Or.inr h) := by
  simp only [unionᵢ_or, unionᵢ_union_distrib, unionᵢ_unionᵢ_eq_left]
#align set.Union_Union_eq_or_left Set.unionᵢ_unionᵢ_eq_or_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x h) -/
@[simp]
theorem interᵢ_interᵢ_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    (⋂ (x) (h), s x h) = s b (Or.inl rfl) ∩ ⋂ (x) (h : p x), s x (Or.inr h) := by
  simp only [interᵢ_or, interᵢ_inter_distrib, interᵢ_interᵢ_eq_left]
#align set.Inter_Inter_eq_or_left Set.interᵢ_interᵢ_eq_or_left

/-! ### Bounded unions and intersections -/


/-- A specialization of `mem_unionᵢ₂`. -/
theorem mem_bunionᵢ {s : Set α} {t : α → Set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) :
    y ∈ ⋃ x ∈ s, t x :=
  mem_unionᵢ₂_of_mem xs ytx
#align set.mem_bUnion Set.mem_bunionᵢ

/-- A specialization of `mem_interᵢ₂`. -/
theorem mem_binterᵢ {s : Set α} {t : α → Set β} {y : β} (h : ∀ x ∈ s, y ∈ t x) :
    y ∈ ⋂ x ∈ s, t x :=
  mem_interᵢ₂_of_mem h
#align set.mem_bInter Set.mem_binterᵢ

/-- A specialization of `subset_unionᵢ₂`. -/
theorem subset_bunionᵢ_of_mem {s : Set α} {u : α → Set β} {x : α} (xs : x ∈ s) :
    u x ⊆ ⋃ x ∈ s, u x :=
--Porting note: Why is this not just `subset_unionᵢ₂ x xs`?
  @subset_unionᵢ₂ β α (. ∈ s) (fun i _ => u i) x xs
#align set.subset_bUnion_of_mem Set.subset_bunionᵢ_of_mem

/-- A specialization of `interᵢ₂_subset`. -/
theorem binterᵢ_subset_of_mem {s : Set α} {t : α → Set β} {x : α} (xs : x ∈ s) :
    (⋂ x ∈ s, t x) ⊆ t x :=
  interᵢ₂_subset x xs
#align set.bInter_subset_of_mem Set.binterᵢ_subset_of_mem

theorem bunionᵢ_subset_bunionᵢ_left {s s' : Set α} {t : α → Set β} (h : s ⊆ s') :
    (⋃ x ∈ s, t x) ⊆ ⋃ x ∈ s', t x :=
  unionᵢ₂_subset fun _ hx => subset_bunionᵢ_of_mem <| h hx
#align set.bUnion_subset_bUnion_left Set.bunionᵢ_subset_bunionᵢ_left

theorem binterᵢ_subset_binterᵢ_left {s s' : Set α} {t : α → Set β} (h : s' ⊆ s) :
    (⋂ x ∈ s, t x) ⊆ ⋂ x ∈ s', t x :=
  subset_interᵢ₂ fun _ hx => binterᵢ_subset_of_mem <| h hx
#align set.bInter_subset_bInter_left Set.binterᵢ_subset_binterᵢ_left

theorem bunionᵢ_mono {s s' : Set α} {t t' : α → Set β} (hs : s' ⊆ s) (h : ∀ x ∈ s, t x ⊆ t' x) :
    (⋃ x ∈ s', t x) ⊆ ⋃ x ∈ s, t' x :=
  (bunionᵢ_subset_bunionᵢ_left hs).trans <| unionᵢ₂_mono h
#align set.bUnion_mono Set.bunionᵢ_mono

theorem binterᵢ_mono {s s' : Set α} {t t' : α → Set β} (hs : s ⊆ s') (h : ∀ x ∈ s, t x ⊆ t' x) :
    (⋂ x ∈ s', t x) ⊆ ⋂ x ∈ s, t' x :=
  (binterᵢ_subset_binterᵢ_left hs).trans <| interᵢ₂_mono h
#align set.bInter_mono Set.binterᵢ_mono

theorem bunionᵢ_eq_unionᵢ (s : Set α) (t : ∀ x ∈ s, Set β) :
    (⋃ x ∈ s, t x ‹_›) = ⋃ x : s, t x x.2 :=
  supᵢ_subtype'
#align set.bUnion_eq_Union Set.bunionᵢ_eq_unionᵢ

theorem binterᵢ_eq_interᵢ (s : Set α) (t : ∀ x ∈ s, Set β) :
    (⋂ x ∈ s, t x ‹_›) = ⋂ x : s, t x x.2 :=
  infᵢ_subtype'
#align set.bInter_eq_Inter Set.binterᵢ_eq_interᵢ

theorem unionᵢ_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    (⋃ x : { x // p x }, s x) = ⋃ (x) (hx : p x), s ⟨x, hx⟩ :=
  supᵢ_subtype
#align set.Union_subtype Set.unionᵢ_subtype

theorem interᵢ_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    (⋂ x : { x // p x }, s x) = ⋂ (x) (hx : p x), s ⟨x, hx⟩ :=
  infᵢ_subtype
#align set.Inter_subtype Set.interᵢ_subtype

theorem binterᵢ_empty (u : α → Set β) : (⋂ x ∈ (∅ : Set α), u x) = univ :=
  infᵢ_emptyset
#align set.bInter_empty Set.binterᵢ_empty

theorem binterᵢ_univ (u : α → Set β) : (⋂ x ∈ @univ α, u x) = ⋂ x, u x :=
  infᵢ_univ
#align set.bInter_univ Set.binterᵢ_univ

@[simp]
theorem bunionᵢ_self (s : Set α) : (⋃ x ∈ s, s) = s :=
  Subset.antisymm (unionᵢ₂_subset fun _ _ => Subset.refl s) fun _ hx => mem_bunionᵢ hx hx
#align set.bUnion_self Set.bunionᵢ_self

@[simp]
theorem unionᵢ_nonempty_self (s : Set α) : (⋃ _h : s.Nonempty, s) = s := by
  rw [unionᵢ_nonempty_index, bunionᵢ_self]
#align set.Union_nonempty_self Set.unionᵢ_nonempty_self

theorem binterᵢ_singleton (a : α) (s : α → Set β) : (⋂ x ∈ ({a} : Set α), s x) = s a :=
  infᵢ_singleton
#align set.bInter_singleton Set.binterᵢ_singleton

theorem binterᵢ_union (s t : Set α) (u : α → Set β) :
    (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  infᵢ_union
#align set.bInter_union Set.binterᵢ_union

theorem binterᵢ_insert (a : α) (s : Set α) (t : α → Set β) :
    (⋂ x ∈ insert a s, t x) = t a ∩ ⋂ x ∈ s, t x := by simp
#align set.bInter_insert Set.binterᵢ_insert

theorem binterᵢ_pair (a b : α) (s : α → Set β) : (⋂ x ∈ ({a, b} : Set α), s x) = s a ∩ s b := by
  rw [binterᵢ_insert, binterᵢ_singleton]
#align set.bInter_pair Set.binterᵢ_pair

theorem binterᵢ_inter {ι α : Type _} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    (⋂ i ∈ s, f i ∩ t) = (⋂ i ∈ s, f i) ∩ t := by
  haveI : Nonempty s := hs.to_subtype
  simp [binterᵢ_eq_interᵢ, ← interᵢ_inter]
#align set.bInter_inter Set.binterᵢ_inter

theorem inter_binterᵢ {ι α : Type _} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    (⋂ i ∈ s, t ∩ f i) = t ∩ ⋂ i ∈ s, f i := by
  rw [inter_comm, ← binterᵢ_inter hs]
  simp [inter_comm]
#align set.inter_bInter Set.inter_binterᵢ

theorem bunionᵢ_empty (s : α → Set β) : (⋃ x ∈ (∅ : Set α), s x) = ∅ :=
  supᵢ_emptyset
#align set.bUnion_empty Set.bunionᵢ_empty

theorem bunionᵢ_univ (s : α → Set β) : (⋃ x ∈ @univ α, s x) = ⋃ x, s x :=
  supᵢ_univ
#align set.bUnion_univ Set.bunionᵢ_univ

theorem bunionᵢ_singleton (a : α) (s : α → Set β) : (⋃ x ∈ ({a} : Set α), s x) = s a :=
  supᵢ_singleton
#align set.bUnion_singleton Set.bunionᵢ_singleton

@[simp]
theorem bunionᵢ_of_singleton (s : Set α) : (⋃ x ∈ s, {x}) = s :=
  ext <| by simp
#align set.bUnion_of_singleton Set.bunionᵢ_of_singleton

theorem bunionᵢ_union (s t : Set α) (u : α → Set β) :
    (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  supᵢ_union
#align set.bUnion_union Set.bunionᵢ_union

@[simp]
theorem unionᵢ_coe_set {α β : Type _} (s : Set α) (f : s → Set β) :
    (⋃ i, f i) = ⋃ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  unionᵢ_subtype _ _
#align set.Union_coe_set Set.unionᵢ_coe_set

@[simp]
theorem interᵢ_coe_set {α β : Type _} (s : Set α) (f : s → Set β) :
    (⋂ i, f i) = ⋂ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  interᵢ_subtype _ _
#align set.Inter_coe_set Set.interᵢ_coe_set

theorem bunionᵢ_insert (a : α) (s : Set α) (t : α → Set β) :
    (⋃ x ∈ insert a s, t x) = t a ∪ ⋃ x ∈ s, t x := by simp
#align set.bUnion_insert Set.bunionᵢ_insert

theorem bunionᵢ_pair (a b : α) (s : α → Set β) : (⋃ x ∈ ({a, b} : Set α), s x) = s a ∪ s b :=
  by simp
#align set.bUnion_pair Set.bunionᵢ_pair

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem inter_unionᵢ₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∩ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ∩ t i j := by simp only [inter_unionᵢ]
#align set.inter_Union₂ Set.inter_unionᵢ₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ₂_inter (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) ∩ t = ⋃ (i) (j), s i j ∩ t := by simp_rw [unionᵢ_inter]
#align set.Union₂_inter Set.unionᵢ₂_inter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem union_interᵢ₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_interᵢ]
#align set.union_Inter₂ Set.union_interᵢ₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem interᵢ₂_union (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [interᵢ_union]
#align set.Inter₂_union Set.interᵢ₂_union

theorem mem_unionₛ_of_mem {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∈ t) (ht : t ∈ S) :
    x ∈ ⋃₀S :=
  ⟨t, ht, hx⟩
#align set.mem_sUnion_of_mem Set.mem_unionₛ_of_mem

-- is this theorem really necessary?
theorem not_mem_of_not_mem_unionₛ {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∉ ⋃₀S)
    (ht : t ∈ S) : x ∉ t := fun h => hx ⟨t, ht, h⟩
#align set.not_mem_of_not_mem_sUnion Set.not_mem_of_not_mem_unionₛ

theorem interₛ_subset_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : ⋂₀ S ⊆ t :=
  infₛ_le tS
#align set.sInter_subset_of_mem Set.interₛ_subset_of_mem

theorem subset_unionₛ_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : t ⊆ ⋃₀S :=
  le_supₛ tS
#align set.subset_sUnion_of_mem Set.subset_unionₛ_of_mem

theorem subset_unionₛ_of_subset {s : Set α} (t : Set (Set α)) (u : Set α) (h₁ : s ⊆ u)
    (h₂ : u ∈ t) : s ⊆ ⋃₀t :=
  Subset.trans h₁ (subset_unionₛ_of_mem h₂)
#align set.subset_sUnion_of_subset Set.subset_unionₛ_of_subset

theorem unionₛ_subset {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t' ⊆ t) : ⋃₀S ⊆ t :=
  supₛ_le h
#align set.sUnion_subset Set.unionₛ_subset

@[simp]
theorem unionₛ_subset_iff {s : Set (Set α)} {t : Set α} : ⋃₀s ⊆ t ↔ ∀ t' ∈ s, t' ⊆ t :=
  supₛ_le_iff
#align set.sUnion_subset_iff Set.unionₛ_subset_iff

theorem subset_interₛ {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t ⊆ t') : t ⊆ ⋂₀ S :=
  le_infₛ h
#align set.subset_sInter Set.subset_interₛ

@[simp]
theorem subset_interₛ_iff {S : Set (Set α)} {t : Set α} : t ⊆ ⋂₀ S ↔ ∀ t' ∈ S, t ⊆ t' :=
  le_infₛ_iff
#align set.subset_sInter_iff Set.subset_interₛ_iff

theorem unionₛ_subset_unionₛ {S T : Set (Set α)} (h : S ⊆ T) : ⋃₀S ⊆ ⋃₀T :=
  unionₛ_subset fun _ hs => subset_unionₛ_of_mem (h hs)
#align set.sUnion_subset_sUnion Set.unionₛ_subset_unionₛ

theorem interₛ_subset_interₛ {S T : Set (Set α)} (h : S ⊆ T) : ⋂₀ T ⊆ ⋂₀ S :=
  subset_interₛ fun _ hs => interₛ_subset_of_mem (h hs)
#align set.sInter_subset_sInter Set.interₛ_subset_interₛ

@[simp]
theorem unionₛ_empty : ⋃₀∅ = (∅ : Set α) :=
  supₛ_empty
#align set.sUnion_empty Set.unionₛ_empty

@[simp]
theorem interₛ_empty : ⋂₀ ∅ = (univ : Set α) :=
  infₛ_empty
#align set.sInter_empty Set.interₛ_empty

@[simp]
theorem unionₛ_singleton (s : Set α) : ⋃₀{s} = s :=
  supₛ_singleton
#align set.sUnion_singleton Set.unionₛ_singleton

@[simp]
theorem interₛ_singleton (s : Set α) : ⋂₀ {s} = s :=
  infₛ_singleton
#align set.sInter_singleton Set.interₛ_singleton

@[simp]
theorem unionₛ_eq_empty {S : Set (Set α)} : ⋃₀S = ∅ ↔ ∀ s ∈ S, s = ∅ :=
  supₛ_eq_bot
#align set.sUnion_eq_empty Set.unionₛ_eq_empty

@[simp]
theorem interₛ_eq_univ {S : Set (Set α)} : ⋂₀ S = univ ↔ ∀ s ∈ S, s = univ :=
  infₛ_eq_top
#align set.sInter_eq_univ Set.interₛ_eq_univ

/-- If all sets in a collection are either `∅` or `Set.univ`, then so is their union. -/
theorem unionₛ_mem_empty_univ {S : Set (Set α)} (h : S ⊆ {∅, univ}) :
    ⋃₀ S ∈ ({∅, univ} :Set (Set α)) := by
  simp only [mem_insert_iff, mem_singleton_iff, or_iff_not_imp_left, unionₛ_eq_empty, not_forall]
  rintro ⟨s, hs, hne⟩
  obtain rfl : s = univ := (h hs).resolve_left hne
  exact univ_subset_iff.1 <| subset_unionₛ_of_mem hs

@[simp]
theorem nonempty_unionₛ {S : Set (Set α)} : (⋃₀S).Nonempty ↔ ∃ s ∈ S, Set.Nonempty s := by
  simp [nonempty_iff_ne_empty]
#align set.nonempty_sUnion Set.nonempty_unionₛ

theorem Nonempty.of_unionₛ {s : Set (Set α)} (h : (⋃₀s).Nonempty) : s.Nonempty :=
  let ⟨s, hs, _⟩ := nonempty_unionₛ.1 h
  ⟨s, hs⟩
#align set.nonempty.of_sUnion Set.Nonempty.of_unionₛ

theorem Nonempty.of_unionₛ_eq_univ [Nonempty α] {s : Set (Set α)} (h : ⋃₀s = univ) : s.Nonempty :=
  Nonempty.of_unionₛ <| h.symm ▸ univ_nonempty
#align set.nonempty.of_sUnion_eq_univ Set.Nonempty.of_unionₛ_eq_univ

theorem unionₛ_union (S T : Set (Set α)) : ⋃₀(S ∪ T) = ⋃₀S ∪ ⋃₀T :=
  supₛ_union
#align set.sUnion_union Set.unionₛ_union

theorem interₛ_union (S T : Set (Set α)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T :=
  infₛ_union
#align set.sInter_union Set.interₛ_union

@[simp]
theorem unionₛ_insert (s : Set α) (T : Set (Set α)) : ⋃₀insert s T = s ∪ ⋃₀T :=
  supₛ_insert
#align set.sUnion_insert Set.unionₛ_insert

@[simp]
theorem interₛ_insert (s : Set α) (T : Set (Set α)) : ⋂₀ insert s T = s ∩ ⋂₀ T :=
  infₛ_insert
#align set.sInter_insert Set.interₛ_insert

@[simp]
theorem unionₛ_diff_singleton_empty (s : Set (Set α)) : ⋃₀(s \ {∅}) = ⋃₀s :=
  supₛ_diff_singleton_bot s
#align set.sUnion_diff_singleton_empty Set.unionₛ_diff_singleton_empty

@[simp]
theorem interₛ_diff_singleton_univ (s : Set (Set α)) : ⋂₀ (s \ {univ}) = ⋂₀ s :=
  infₛ_diff_singleton_top s
#align set.sInter_diff_singleton_univ Set.interₛ_diff_singleton_univ

theorem unionₛ_pair (s t : Set α) : ⋃₀{s, t} = s ∪ t :=
  supₛ_pair
#align set.sUnion_pair Set.unionₛ_pair

theorem interₛ_pair (s t : Set α) : ⋂₀ {s, t} = s ∩ t :=
  infₛ_pair
#align set.sInter_pair Set.interₛ_pair

@[simp]
theorem unionₛ_image (f : α → Set β) (s : Set α) : ⋃₀(f '' s) = ⋃ x ∈ s, f x :=
  supₛ_image
#align set.sUnion_image Set.unionₛ_image

@[simp]
theorem interₛ_image (f : α → Set β) (s : Set α) : ⋂₀ (f '' s) = ⋂ x ∈ s, f x :=
  infₛ_image
#align set.sInter_image Set.interₛ_image

@[simp]
theorem unionₛ_range (f : ι → Set β) : ⋃₀range f = ⋃ x, f x :=
  rfl
#align set.sUnion_range Set.unionₛ_range

@[simp]
theorem interₛ_range (f : ι → Set β) : ⋂₀ range f = ⋂ x, f x :=
  rfl
#align set.sInter_range Set.interₛ_range

theorem unionᵢ_eq_univ_iff {f : ι → Set α} : (⋃ i, f i) = univ ↔ ∀ x, ∃ i, x ∈ f i := by
  simp only [eq_univ_iff_forall, mem_unionᵢ]
#align set.Union_eq_univ_iff Set.unionᵢ_eq_univ_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ₂_eq_univ_iff {s : ∀ i, κ i → Set α} :
    (⋃ (i) (j), s i j) = univ ↔ ∀ a, ∃ i j, a ∈ s i j :=
  by simp only [unionᵢ_eq_univ_iff, mem_unionᵢ]
#align set.Union₂_eq_univ_iff Set.unionᵢ₂_eq_univ_iff

theorem unionₛ_eq_univ_iff {c : Set (Set α)} : ⋃₀c = univ ↔ ∀ a, ∃ b ∈ c, a ∈ b := by
  simp only [eq_univ_iff_forall, mem_unionₛ]
#align set.sUnion_eq_univ_iff Set.unionₛ_eq_univ_iff

-- classical
theorem interᵢ_eq_empty_iff {f : ι → Set α} : (⋂ i, f i) = ∅ ↔ ∀ x, ∃ i, x ∉ f i := by
  simp [Set.eq_empty_iff_forall_not_mem]
#align set.Inter_eq_empty_iff Set.interᵢ_eq_empty_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
-- classical
theorem interᵢ₂_eq_empty_iff {s : ∀ i, κ i → Set α} :
    (⋂ (i) (j), s i j) = ∅ ↔ ∀ a, ∃ i j, a ∉ s i j := by
  simp only [eq_empty_iff_forall_not_mem, mem_interᵢ, not_forall]
#align set.Inter₂_eq_empty_iff Set.interᵢ₂_eq_empty_iff

-- classical
theorem interₛ_eq_empty_iff {c : Set (Set α)} : ⋂₀ c = ∅ ↔ ∀ a, ∃ b ∈ c, a ∉ b := by
  simp [Set.eq_empty_iff_forall_not_mem]
#align set.sInter_eq_empty_iff Set.interₛ_eq_empty_iff

-- classical
@[simp]
theorem nonempty_interᵢ {f : ι → Set α} : (⋂ i, f i).Nonempty ↔ ∃ x, ∀ i, x ∈ f i := by
  simp [nonempty_iff_ne_empty, interᵢ_eq_empty_iff]
#align set.nonempty_Inter Set.nonempty_interᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
-- classical
--Porting note: removing `simp`. `simp` can prove it
theorem nonempty_interᵢ₂ {s : ∀ i, κ i → Set α} :
    (⋂ (i) (j), s i j).Nonempty ↔ ∃ a, ∀ i j, a ∈ s i j := by
  simp
#align set.nonempty_Inter₂ Set.nonempty_interᵢ₂

-- classical
@[simp]
theorem nonempty_interₛ {c : Set (Set α)} : (⋂₀ c).Nonempty ↔ ∃ a, ∀ b ∈ c, a ∈ b := by
  simp [nonempty_iff_ne_empty, interₛ_eq_empty_iff]
#align set.nonempty_sInter Set.nonempty_interₛ

-- classical
theorem compl_unionₛ (S : Set (Set α)) : (⋃₀S)ᶜ = ⋂₀ (compl '' S) :=
  ext fun x => by simp
#align set.compl_sUnion Set.compl_unionₛ

-- classical
theorem unionₛ_eq_compl_interₛ_compl (S : Set (Set α)) : ⋃₀S = (⋂₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋃₀S), compl_unionₛ]
#align set.sUnion_eq_compl_sInter_compl Set.unionₛ_eq_compl_interₛ_compl

-- classical
theorem compl_interₛ (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀(compl '' S) := by
  rw [unionₛ_eq_compl_interₛ_compl, compl_compl_image]
#align set.compl_sInter Set.compl_interₛ

-- classical
theorem interₛ_eq_compl_unionₛ_compl (S : Set (Set α)) : ⋂₀ S = (⋃₀(compl '' S))ᶜ := by
  rw [← compl_compl (⋂₀ S), compl_interₛ]
#align set.sInter_eq_compl_sUnion_compl Set.interₛ_eq_compl_unionₛ_compl

theorem inter_empty_of_inter_unionₛ_empty {s t : Set α} {S : Set (Set α)} (hs : t ∈ S)
    (h : s ∩ ⋃₀S = ∅) : s ∩ t = ∅ :=
  eq_empty_of_subset_empty <| by
    rw [← h]; exact inter_subset_inter_right _ (subset_unionₛ_of_mem hs)
#align set.inter_empty_of_inter_sUnion_empty Set.inter_empty_of_inter_unionₛ_empty

theorem range_sigma_eq_unionᵢ_range {γ : α → Type _} (f : Sigma γ → β) :
    range f = ⋃ a, range fun b => f ⟨a, b⟩ :=
  Set.ext <| by simp
#align set.range_sigma_eq_Union_range Set.range_sigma_eq_unionᵢ_range

theorem unionᵢ_eq_range_sigma (s : α → Set β) : (⋃ i, s i) = range fun a : Σi, s i => a.2 := by
  simp [Set.ext_iff]
#align set.Union_eq_range_sigma Set.unionᵢ_eq_range_sigma

theorem unionᵢ_eq_range_psigma (s : ι → Set β) : (⋃ i, s i) = range fun a : Σ'i, s i => a.2 := by
  simp [Set.ext_iff]
#align set.Union_eq_range_psigma Set.unionᵢ_eq_range_psigma

theorem unionᵢ_image_preimage_sigma_mk_eq_self {ι : Type _} {σ : ι → Type _} (s : Set (Sigma σ)) :
    (⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' s)) = s := by
  ext x
  simp only [mem_unionᵢ, mem_image, mem_preimage]
  constructor
  · rintro ⟨i, a, h, rfl⟩
    exact h
  · intro h
    cases' x with i a
    exact ⟨i, a, h, rfl⟩
#align set.Union_image_preimage_sigma_mk_eq_self Set.unionᵢ_image_preimage_sigma_mk_eq_self

theorem Sigma.univ (X : α → Type _) : (Set.univ : Set (Σa, X a)) = ⋃ a, range (Sigma.mk a) :=
  Set.ext fun x =>
    iff_of_true trivial ⟨range (Sigma.mk x.1), Set.mem_range_self _, x.2, Sigma.eta x⟩
#align set.sigma.univ Set.Sigma.univ

theorem unionₛ_mono {s t : Set (Set α)} (h : s ⊆ t) : ⋃₀s ⊆ ⋃₀t :=
  unionₛ_subset fun _' ht' => subset_unionₛ_of_mem <| h ht'
#align set.sUnion_mono Set.unionₛ_mono

theorem unionᵢ_subset_unionᵢ_const {s : Set α} (h : ι → ι₂) : (⋃ _i : ι, s) ⊆ ⋃ _j : ι₂, s :=
  @supᵢ_const_mono (Set α) ι ι₂ _ s h
#align set.Union_subset_Union_const Set.unionᵢ_subset_unionᵢ_const

@[simp]
theorem unionᵢ_singleton_eq_range {α β : Type _} (f : α → β) : (⋃ x : α, {f x}) = range f := by
  ext x
  simp [@eq_comm _ x]
#align set.Union_singleton_eq_range Set.unionᵢ_singleton_eq_range

theorem unionᵢ_of_singleton (α : Type _) : (⋃ x, {x} : Set α) = univ := by simp [Set.ext_iff]
#align set.Union_of_singleton Set.unionᵢ_of_singleton

theorem unionᵢ_of_singleton_coe (s : Set α) : (⋃ i : s, ({(i : α)} : Set α)) = s := by simp
#align set.Union_of_singleton_coe Set.unionᵢ_of_singleton_coe

theorem unionₛ_eq_bunionᵢ {s : Set (Set α)} : ⋃₀s = ⋃ (i : Set α) (_h : i ∈ s), i := by
  rw [← unionₛ_image, image_id']
#align set.sUnion_eq_bUnion Set.unionₛ_eq_bunionᵢ

theorem interₛ_eq_binterᵢ {s : Set (Set α)} : ⋂₀ s = ⋂ (i : Set α) (_h : i ∈ s), i := by
  rw [← interₛ_image, image_id']
#align set.sInter_eq_bInter Set.interₛ_eq_binterᵢ

theorem unionₛ_eq_unionᵢ {s : Set (Set α)} : ⋃₀s = ⋃ i : s, i := by
  simp only [← unionₛ_range, Subtype.range_coe]
#align set.sUnion_eq_Union Set.unionₛ_eq_unionᵢ

theorem interₛ_eq_interᵢ {s : Set (Set α)} : ⋂₀ s = ⋂ i : s, i := by
  simp only [← interₛ_range, Subtype.range_coe]
#align set.sInter_eq_Inter Set.interₛ_eq_interᵢ

@[simp]
theorem unionᵢ_of_empty [IsEmpty ι] (s : ι → Set α) : (⋃ i, s i) = ∅ :=
  supᵢ_of_empty _
#align set.Union_of_empty Set.unionᵢ_of_empty

@[simp]
theorem interᵢ_of_empty [IsEmpty ι] (s : ι → Set α) : (⋂ i, s i) = univ :=
  infᵢ_of_empty _
#align set.Inter_of_empty Set.interᵢ_of_empty

theorem union_eq_unionᵢ {s₁ s₂ : Set α} : s₁ ∪ s₂ = ⋃ b : Bool, cond b s₁ s₂ :=
  sup_eq_supᵢ s₁ s₂
#align set.union_eq_Union Set.union_eq_unionᵢ

theorem inter_eq_interᵢ {s₁ s₂ : Set α} : s₁ ∩ s₂ = ⋂ b : Bool, cond b s₁ s₂ :=
  inf_eq_infᵢ s₁ s₂
#align set.inter_eq_Inter Set.inter_eq_interᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem interₛ_union_interₛ {S T : Set (Set α)} :
    ⋂₀ S ∪ ⋂₀ T = ⋂ p ∈ S ×ˢ T, (p : Set α × Set α).1 ∪ p.2 :=
  infₛ_sup_infₛ
#align set.sInter_union_sInter Set.interₛ_union_interₛ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionₛ_inter_unionₛ {s t : Set (Set α)} :
    ⋃₀s ∩ ⋃₀t = ⋃ p ∈ s ×ˢ t, (p : Set α × Set α).1 ∩ p.2 :=
  supₛ_inf_supₛ
#align set.sUnion_inter_sUnion Set.unionₛ_inter_unionₛ

theorem bunionᵢ_unionᵢ (s : ι → Set α) (t : α → Set β) :
    (⋃ x ∈ ⋃ i, s i, t x) = ⋃ (i) (x ∈ s i), t x := by simp [@unionᵢ_comm _ ι]
#align set.bUnion_Union Set.bunionᵢ_unionᵢ

theorem binterᵢ_unionᵢ (s : ι → Set α) (t : α → Set β) :
    (⋂ x ∈ ⋃ i, s i, t x) = ⋂ (i) (x ∈ s i), t x := by simp [@interᵢ_comm _ ι]
#align set.bInter_Union Set.binterᵢ_unionᵢ

theorem unionₛ_unionᵢ (s : ι → Set (Set α)) : (⋃₀⋃ i, s i) = ⋃ i, ⋃₀s i := by
  simp only [unionₛ_eq_bunionᵢ, bunionᵢ_unionᵢ]
#align set.sUnion_Union Set.unionₛ_unionᵢ

theorem interₛ_unionᵢ (s : ι → Set (Set α)) : (⋂₀ ⋃ i, s i) = ⋂ i, ⋂₀ s i := by
  simp only [interₛ_eq_binterᵢ, binterᵢ_unionᵢ]
#align set.sInter_Union Set.interₛ_unionᵢ

theorem unionᵢ_range_eq_unionₛ {α β : Type _} (C : Set (Set α)) {f : ∀ s : C, β → (s : Type _)}
    (hf : ∀ s : C, Surjective (f s)) : (⋃ y : β, range fun s : C => (f s y).val) = ⋃₀C := by
  ext x; constructor
  · rintro ⟨s, ⟨y, rfl⟩, ⟨s, hs⟩, rfl⟩
    refine' ⟨_, hs, _⟩
    exact (f ⟨s, hs⟩ y).2
  · rintro ⟨s, hs, hx⟩
    cases' hf ⟨s, hs⟩ ⟨x, hx⟩ with y hy
    refine' ⟨_, ⟨y, rfl⟩, ⟨s, hs⟩, _⟩
    exact congr_arg Subtype.val hy
#align set.Union_range_eq_sUnion Set.unionᵢ_range_eq_unionₛ

theorem unionᵢ_range_eq_unionᵢ (C : ι → Set α) {f : ∀ x : ι, β → C x}
    (hf : ∀ x : ι, Surjective (f x)) : (⋃ y : β, range fun x : ι => (f x y).val) = ⋃ x, C x := by
  ext x; rw [mem_unionᵢ, mem_unionᵢ]; constructor
  · rintro ⟨y, i, rfl⟩
    exact ⟨i, (f i y).2⟩
  · rintro ⟨i, hx⟩
    cases' hf i ⟨x, hx⟩ with y hy
    exact ⟨y, i, congr_arg Subtype.val hy⟩
#align set.Union_range_eq_Union Set.unionᵢ_range_eq_unionᵢ

theorem union_distrib_interᵢ_left (s : ι → Set α) (t : Set α) : (t ∪ ⋂ i, s i) = ⋂ i, t ∪ s i :=
  sup_infᵢ_eq _ _
#align set.union_distrib_Inter_left Set.union_distrib_interᵢ_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem union_distrib_interᵢ₂_left (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_distrib_interᵢ_left]
#align set.union_distrib_Inter₂_left Set.union_distrib_interᵢ₂_left

theorem union_distrib_interᵢ_right (s : ι → Set α) (t : Set α) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  infᵢ_sup_eq _ _
#align set.union_distrib_Inter_right Set.union_distrib_interᵢ_right

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem union_distrib_interᵢ₂_right (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [union_distrib_interᵢ_right]
#align set.union_distrib_Inter₂_right Set.union_distrib_interᵢ₂_right

section Function

/-! ### `mapsTo` -/


theorem mapsTo_unionₛ {S : Set (Set α)} {t : Set β} {f : α → β} (H : ∀ s ∈ S, MapsTo f s t) :
    MapsTo f (⋃₀S) t := fun _ ⟨s, hs, hx⟩ => H s hs hx
#align set.maps_to_sUnion Set.mapsTo_unionₛ

theorem mapsTo_unionᵢ {s : ι → Set α} {t : Set β} {f : α → β} (H : ∀ i, MapsTo f (s i) t) :
    MapsTo f (⋃ i, s i) t :=
  mapsTo_unionₛ <| forall_range_iff.2 H
#align set.maps_to_Union Set.mapsTo_unionᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mapsTo_unionᵢ₂ {s : ∀ i, κ i → Set α} {t : Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) t) : MapsTo f (⋃ (i) (j), s i j) t :=
  mapsTo_unionᵢ fun i => mapsTo_unionᵢ (H i)
#align set.maps_to_Union₂ Set.mapsTo_unionᵢ₂

theorem mapsTo_unionᵢ_unionᵢ {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, MapsTo f (s i) (t i)) : MapsTo f (⋃ i, s i) (⋃ i, t i) :=
  mapsTo_unionᵢ fun i => (H i).mono (Subset.refl _) (subset_unionᵢ t i)
#align set.maps_to_Union_Union Set.mapsTo_unionᵢ_unionᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mapsTo_unionᵢ₂_unionᵢ₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  mapsTo_unionᵢ_unionᵢ fun i => mapsTo_unionᵢ_unionᵢ (H i)
#align set.maps_to_Union₂_Union₂ Set.mapsTo_unionᵢ₂_unionᵢ₂

theorem mapsTo_interₛ {s : Set α} {T : Set (Set β)} {f : α → β} (H : ∀ t ∈ T, MapsTo f s t) :
    MapsTo f s (⋂₀ T) := fun _ hx t ht => H t ht hx
#align set.maps_to_sInter Set.mapsTo_interₛ

theorem mapsTo_interᵢ {s : Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, MapsTo f s (t i)) :
    MapsTo f s (⋂ i, t i) := fun _ hx => mem_interᵢ.2 fun i => H i hx
#align set.maps_to_Inter Set.mapsTo_interᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mapsTo_interᵢ₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f s (t i j)) : MapsTo f s (⋂ (i) (j), t i j) :=
  mapsTo_interᵢ fun i => mapsTo_interᵢ (H i)
#align set.maps_to_Inter₂ Set.mapsTo_interᵢ₂

theorem mapsTo_interᵢ_interᵢ {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, MapsTo f (s i) (t i)) : MapsTo f (⋂ i, s i) (⋂ i, t i) :=
  mapsTo_interᵢ fun i => (H i).mono (interᵢ_subset s i) (Subset.refl _)
#align set.maps_to_Inter_Inter Set.mapsTo_interᵢ_interᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mapsTo_interᵢ₂_interᵢ₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋂ (i) (j), s i j) (⋂ (i) (j), t i j) :=
  mapsTo_interᵢ_interᵢ fun i => mapsTo_interᵢ_interᵢ (H i)
#align set.maps_to_Inter₂_Inter₂ Set.mapsTo_interᵢ₂_interᵢ₂

theorem image_interᵢ_subset (s : ι → Set α) (f : α → β) : (f '' ⋂ i, s i) ⊆ ⋂ i, f '' s i :=
  (mapsTo_interᵢ_interᵢ fun i => mapsTo_image f (s i)).image_subset
#align set.image_Inter_subset Set.image_interᵢ_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image_interᵢ₂_subset (s : ∀ i, κ i → Set α) (f : α → β) :
    (f '' ⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), f '' s i j :=
  (mapsTo_interᵢ₂_interᵢ₂ fun i hi => mapsTo_image f (s i hi)).image_subset
#align set.image_Inter₂_subset Set.image_interᵢ₂_subset

theorem image_interₛ_subset (S : Set (Set α)) (f : α → β) : f '' ⋂₀ S ⊆ ⋂ s ∈ S, f '' s := by
  rw [interₛ_eq_binterᵢ]
  apply image_interᵢ₂_subset
#align set.image_sInter_subset Set.image_interₛ_subset

/-! ### `restrictPreimage` -/


section

open Function

variable (s : Set β) {f : α → β} {U : ι → Set β} (hU : unionᵢ U = univ)

theorem injective_iff_injective_of_unionᵢ_eq_univ :
    Injective f ↔ ∀ i, Injective ((U i).restrictPreimage f) := by
  refine' ⟨fun H i => (U i).restrictPreimage_injective H, fun H x y e => _⟩
  obtain ⟨i, hi⟩ := Set.mem_unionᵢ.mp
      (show f x ∈ Set.unionᵢ U by rw [hU]; triv)
  injection @H i ⟨x, hi⟩ ⟨y, show f y ∈ U i from e ▸ hi⟩ (Subtype.ext e)
#align set.injective_iff_injective_of_Union_eq_univ Set.injective_iff_injective_of_unionᵢ_eq_univ

theorem surjective_iff_surjective_of_unionᵢ_eq_univ :
    Surjective f ↔ ∀ i, Surjective ((U i).restrictPreimage f) := by
  refine' ⟨fun H i => (U i).restrictPreimage_surjective H, fun H x => _⟩
  obtain ⟨i, hi⟩ :=
    Set.mem_unionᵢ.mp
      (show x ∈ Set.unionᵢ U by rw [hU]; triv)
  exact ⟨_, congr_arg Subtype.val (H i ⟨x, hi⟩).choose_spec⟩
#align set.surjective_iff_surjective_of_Union_eq_univ Set.surjective_iff_surjective_of_unionᵢ_eq_univ

theorem bijective_iff_bijective_of_unionᵢ_eq_univ :
    Bijective f ↔ ∀ i, Bijective ((U i).restrictPreimage f) := by
  rw [Bijective, injective_iff_injective_of_unionᵢ_eq_univ hU,
    surjective_iff_surjective_of_unionᵢ_eq_univ hU]
  simp [Bijective, forall_and]
#align set.bijective_iff_bijective_of_Union_eq_univ Set.bijective_iff_bijective_of_unionᵢ_eq_univ

end

/-! ### `InjOn` -/


theorem InjOn.image_interᵢ_eq [Nonempty ι] {s : ι → Set α} {f : α → β} (h : InjOn f (⋃ i, s i)) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  inhabit ι
  refine' Subset.antisymm (image_interᵢ_subset s f) fun y hy => _
  simp only [mem_interᵢ, mem_image_iff_bex] at hy
  choose x hx hy using hy
  refine' ⟨x default, mem_interᵢ.2 fun i => _, hy _⟩
  suffices x default = x i by
    rw [this]
    apply hx
  replace hx : ∀ i, x i ∈ ⋃ j, s j := fun i => (subset_unionᵢ _ _) (hx i)
  apply h (hx _) (hx _)
  simp only [hy]
#align set.inj_on.image_Inter_eq Set.InjOn.image_interᵢ_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem InjOn.image_binterᵢ_eq {p : ι → Prop} {s : ∀ (i) (_ : p i), Set α} (hp : ∃ i, p i)
    {f : α → β} (h : InjOn f (⋃ (i) (hi), s i hi)) :
    (f '' ⋂ (i) (hi), s i hi) = ⋂ (i) (hi), f '' s i hi := by
  simp only [interᵢ, infᵢ_subtype']
  haveI : Nonempty { i // p i } := nonempty_subtype.2 hp
  apply InjOn.image_interᵢ_eq
  simpa only [unionᵢ, supᵢ_subtype'] using h
#align set.inj_on.image_bInter_eq Set.InjOn.image_binterᵢ_eq

theorem image_interᵢ {f : α → β} (hf : Bijective f) (s : ι → Set α) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  cases isEmpty_or_nonempty ι
  · simp_rw [interᵢ_of_empty, image_univ_of_surjective hf.surjective]
  · exact (hf.injective.injOn _).image_interᵢ_eq
#align set.image_Inter Set.image_interᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image_interᵢ₂ {f : α → β} (hf : Bijective f) (s : ∀ i, κ i → Set α) :
    (f '' ⋂ (i) (j), s i j) = ⋂ (i) (j), f '' s i j := by simp_rw [image_interᵢ hf]
#align set.image_Inter₂ Set.image_interᵢ₂

theorem inj_on_unionᵢ_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {f : α → β}
    (hf : ∀ i, InjOn f (s i)) : InjOn f (⋃ i, s i) := by
  intro x hx y hy hxy
  rcases mem_unionᵢ.1 hx with ⟨i, hx⟩
  rcases mem_unionᵢ.1 hy with ⟨j, hy⟩
  rcases hs i j with ⟨k, hi, hj⟩
  exact hf k (hi hx) (hj hy) hxy
#align set.inj_on_Union_of_directed Set.inj_on_unionᵢ_of_directed

/-! ### `SurjOn` -/


theorem surjOn_unionₛ {s : Set α} {T : Set (Set β)} {f : α → β} (H : ∀ t ∈ T, SurjOn f s t) :
    SurjOn f s (⋃₀T) := fun _ ⟨t, ht, hx⟩ => H t ht hx
#align set.surj_on_sUnion Set.surjOn_unionₛ

theorem surjOn_unionᵢ {s : Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, SurjOn f s (t i)) :
    SurjOn f s (⋃ i, t i) :=
  surjOn_unionₛ <| forall_range_iff.2 H
#align set.surj_on_Union Set.surjOn_unionᵢ

theorem surjOn_unionᵢ_unionᵢ {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) : SurjOn f (⋃ i, s i) (⋃ i, t i) :=
  surjOn_unionᵢ fun i => (H i).mono (subset_unionᵢ _ _) (Subset.refl _)
#align set.surj_on_Union_Union Set.surjOn_unionᵢ_unionᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem surjOn_unionᵢ₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f s (t i j)) : SurjOn f s (⋃ (i) (j), t i j) :=
  surjOn_unionᵢ fun i => surjOn_unionᵢ (H i)
#align set.surj_on_Union₂ Set.surjOn_unionᵢ₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem surjOn_unionᵢ₂_unionᵢ₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f (s i j) (t i j)) : SurjOn f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  surjOn_unionᵢ_unionᵢ fun i => surjOn_unionᵢ_unionᵢ (H i)
#align set.surj_on_Union₂_Union₂ Set.surjOn_unionᵢ₂_unionᵢ₂

theorem surjOn_interᵢ [Nonempty ι] {s : ι → Set α} {t : Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) t) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) t := by
  intro y hy
  rw [Hinj.image_interᵢ_eq, mem_interᵢ]
  exact fun i => H i hy
#align set.surj_on_Inter Set.surjOn_interᵢ

theorem surjOn_interᵢ_interᵢ [Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) (⋂ i, t i) :=
  surjOn_interᵢ (fun i => (H i).mono (Subset.refl _) (interᵢ_subset _ _)) Hinj
#align set.surj_on_Inter_Inter Set.surjOn_interᵢ_interᵢ

/-! ### `BijOn` -/


theorem bijOn_unionᵢ {s : ι → Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i))
    (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  ⟨mapsTo_unionᵢ_unionᵢ fun i => (H i).mapsTo, Hinj, surjOn_unionᵢ_unionᵢ fun i => (H i).surjOn⟩
#align set.bij_on_Union Set.bijOn_unionᵢ

theorem bijOn_interᵢ [hi : Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, BijOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  ⟨mapsTo_interᵢ_interᵢ fun i => (H i).mapsTo,
    hi.elim fun i => (H i).injOn.mono (interᵢ_subset _ _),
    surjOn_interᵢ_interᵢ (fun i => (H i).surjOn) Hinj⟩
#align set.bij_on_Inter Set.bijOn_interᵢ

theorem bijOn_unionᵢ_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {t : ι → Set β}
    {f : α → β} (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  bijOn_unionᵢ H <| inj_on_unionᵢ_of_directed hs fun i => (H i).injOn
#align set.bij_on_Union_of_directed Set.bijOn_unionᵢ_of_directed

theorem bijOn_interᵢ_of_directed [Nonempty ι] {s : ι → Set α} (hs : Directed (· ⊆ ·) s)
    {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  bijOn_interᵢ H <| inj_on_unionᵢ_of_directed hs fun i => (H i).injOn
#align set.bij_on_Inter_of_directed Set.bijOn_interᵢ_of_directed

end Function

/-! ### `image`, `preimage` -/


section Image

theorem image_unionᵢ {f : α → β} {s : ι → Set α} : (f '' ⋃ i, s i) = ⋃ i, f '' s i := by
  ext1 x
  simp only [mem_image, mem_unionᵢ, ← exists_and_right, ← exists_and_left]
  --Porting note: `exists_swap` causes a `simp` loop in Lean4 so we use `rw` instead.
  rw [exists_swap]
#align set.image_Union Set.image_unionᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image_unionᵢ₂ (f : α → β) (s : ∀ i, κ i → Set α) :
    (f '' ⋃ (i) (j), s i j) = ⋃ (i) (j), f '' s i j := by simp_rw [image_unionᵢ]
#align set.image_Union₂ Set.image_unionᵢ₂

theorem univ_subtype {p : α → Prop} : (univ : Set (Subtype p)) = ⋃ (x) (h : p x), {⟨x, h⟩} :=
  Set.ext fun ⟨x, h⟩ => by simp [h]
#align set.univ_subtype Set.univ_subtype

theorem range_eq_unionᵢ {ι} (f : ι → α) : range f = ⋃ i, {f i} :=
  Set.ext fun a => by simp [@eq_comm α a]
#align set.range_eq_Union Set.range_eq_unionᵢ

theorem image_eq_unionᵢ (f : α → β) (s : Set α) : f '' s = ⋃ i ∈ s, {f i} :=
  Set.ext fun b => by simp [@eq_comm β b]
#align set.image_eq_Union Set.image_eq_unionᵢ

theorem bunionᵢ_range {f : ι → α} {g : α → Set β} : (⋃ x ∈ range f, g x) = ⋃ y, g (f y) :=
  supᵢ_range
#align set.bUnion_range Set.bunionᵢ_range

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
@[simp]
theorem unionᵢ_unionᵢ_eq' {f : ι → α} {g : α → Set β} :
    (⋃ (x) (y) (_h : f y = x), g x) = ⋃ y, g (f y) := by simpa using bunionᵢ_range
#align set.Union_Union_eq' Set.unionᵢ_unionᵢ_eq'

theorem binterᵢ_range {f : ι → α} {g : α → Set β} : (⋂ x ∈ range f, g x) = ⋂ y, g (f y) :=
  infᵢ_range
#align set.bInter_range Set.binterᵢ_range

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
@[simp]
theorem interᵢ_interᵢ_eq' {f : ι → α} {g : α → Set β} :
    (⋂ (x) (y) (_h : f y = x), g x) = ⋂ y, g (f y) := by simpa using binterᵢ_range
#align set.Inter_Inter_eq' Set.interᵢ_interᵢ_eq'

variable {s : Set γ} {f : γ → α} {g : α → Set β}

theorem bunionᵢ_image : (⋃ x ∈ f '' s, g x) = ⋃ y ∈ s, g (f y) :=
  supᵢ_image
#align set.bUnion_image Set.bunionᵢ_image

theorem binterᵢ_image : (⋂ x ∈ f '' s, g x) = ⋂ y ∈ s, g (f y) :=
  infᵢ_image
#align set.bInter_image Set.binterᵢ_image

end Image

section Preimage

theorem monotone_preimage {f : α → β} : Monotone (preimage f) := fun _ _ h => preimage_mono h
#align set.monotone_preimage Set.monotone_preimage

@[simp]
theorem preimage_unionᵢ {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i :=
  Set.ext <| by simp [preimage]
#align set.preimage_Union Set.preimage_unionᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem preimage_unionᵢ₂ {f : α → β} {s : ∀ i, κ i → Set β} :
    (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_unionᵢ]
#align set.preimage_Union₂ Set.preimage_unionᵢ₂

@[simp]
theorem preimage_unionₛ {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋃₀s = ⋃ t ∈ s, f ⁻¹' t := by
  rw [unionₛ_eq_bunionᵢ, preimage_unionᵢ₂]
#align set.preimage_sUnion Set.preimage_unionₛ

theorem preimage_interᵢ {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i := by
  ext; simp
#align set.preimage_Inter Set.preimage_interᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem preimage_interᵢ₂ {f : α → β} {s : ∀ i, κ i → Set β} :
    (f ⁻¹' ⋂ (i) (j), s i j) = ⋂ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_interᵢ]
#align set.preimage_Inter₂ Set.preimage_interᵢ₂

@[simp]
theorem preimage_interₛ {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋂₀ s = ⋂ t ∈ s, f ⁻¹' t := by
  rw [interₛ_eq_binterᵢ, preimage_interᵢ₂]
#align set.preimage_sInter Set.preimage_interₛ

@[simp]
theorem bunionᵢ_preimage_singleton (f : α → β) (s : Set β) : (⋃ y ∈ s, f ⁻¹' {y}) = f ⁻¹' s := by
  rw [← preimage_unionᵢ₂, bunionᵢ_of_singleton]
#align set.bUnion_preimage_singleton Set.bunionᵢ_preimage_singleton

theorem bunionᵢ_range_preimage_singleton (f : α → β) : (⋃ y ∈ range f, f ⁻¹' {y}) = univ := by
  rw [bunionᵢ_preimage_singleton, preimage_range]
#align set.bUnion_range_preimage_singleton Set.bunionᵢ_range_preimage_singleton

end Preimage

section Prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_unionᵢ {s : Set α} {t : ι → Set β} : (s ×ˢ ⋃ i, t i) = ⋃ i, s ×ˢ t i := by
  ext
  simp
#align set.prod_Union Set.prod_unionᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_unionᵢ₂ {s : Set α} {t : ∀ i, κ i → Set β} :
    (s ×ˢ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ×ˢ t i j := by simp_rw [prod_unionᵢ]
#align set.prod_Union₂ Set.prod_unionᵢ₂

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_unionₛ {s : Set α} {C : Set (Set β)} : s ×ˢ ⋃₀C = ⋃₀((fun t => s ×ˢ t) '' C) := by
  simp_rw [unionₛ_eq_bunionᵢ, bunionᵢ_image, prod_unionᵢ₂]
#align set.prod_sUnion Set.prod_unionₛ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionᵢ_prod_const {s : ι → Set α} {t : Set β} : (⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t := by
  ext
  simp
#align set.Union_prod_const Set.unionᵢ_prod_const

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionᵢ₂_prod_const {s : ∀ i, κ i → Set α} {t : Set β} :
    (⋃ (i) (j), s i j) ×ˢ t = ⋃ (i) (j), s i j ×ˢ t := by simp_rw [unionᵢ_prod_const]
#align set.Union₂_prod_const Set.unionᵢ₂_prod_const

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionₛ_prod_const {C : Set (Set α)} {t : Set β} :
    ⋃₀C ×ˢ t = ⋃₀((fun s : Set α => s ×ˢ t) '' C) := by
  simp only [unionₛ_eq_bunionᵢ, unionᵢ₂_prod_const, bunionᵢ_image]
#align set.sUnion_prod_const Set.unionₛ_prod_const

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionᵢ_prod {ι ι' α β} (s : ι → Set α) (t : ι' → Set β) :
    (⋃ x : ι × ι', s x.1 ×ˢ t x.2) = (⋃ i : ι, s i) ×ˢ ⋃ i : ι', t i := by
  ext
  simp
#align set.Union_prod Set.unionᵢ_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionᵢ_prod_of_monotone [SemilatticeSup α] {s : α → Set β} {t : α → Set γ} (hs : Monotone s)
    (ht : Monotone t) : (⋃ x, s x ×ˢ t x) = (⋃ x, s x) ×ˢ ⋃ x, t x := by
  ext ⟨z, w⟩; simp only [mem_prod, mem_unionᵢ, exists_imp, and_imp, iff_def]; constructor
  · intro x hz hw
    exact ⟨⟨x, hz⟩, x, hw⟩
  · intro x hz x' hw
    exact ⟨x ⊔ x', hs le_sup_left hz, ht le_sup_right hw⟩
#align set.Union_prod_of_monotone Set.unionᵢ_prod_of_monotone

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem interₛ_prod_interₛ_subset (S : Set (Set α)) (T : Set (Set β)) :
    ⋂₀ S ×ˢ ⋂₀ T ⊆ ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 :=
  subset_interᵢ₂ fun x hx _ hy => ⟨hy.1 x.1 hx.1, hy.2 x.2 hx.2⟩
#align set.sInter_prod_sInter_subset Set.interₛ_prod_interₛ_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem interₛ_prod_interₛ {S : Set (Set α)} {T : Set (Set β)} (hS : S.Nonempty) (hT : T.Nonempty) :
    ⋂₀ S ×ˢ ⋂₀ T = ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 := by
  obtain ⟨s₁, h₁⟩ := hS
  obtain ⟨s₂, h₂⟩ := hT
  refine' Set.Subset.antisymm (interₛ_prod_interₛ_subset S T) fun x hx => _
  rw [mem_interᵢ₂] at hx
  exact ⟨fun s₀ h₀ => (hx (s₀, s₂) ⟨h₀, h₂⟩).1, fun s₀ h₀ => (hx (s₁, s₀) ⟨h₁, h₀⟩).2⟩
#align set.sInter_prod_sInter Set.interₛ_prod_interₛ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem interₛ_prod {S : Set (Set α)} (hS : S.Nonempty) (t : Set β) :
    ⋂₀ S ×ˢ t = ⋂ s ∈ S, s ×ˢ t := by
  rw [← interₛ_singleton t, interₛ_prod_interₛ hS (singleton_nonempty t), interₛ_singleton]
  simp_rw [prod_singleton, mem_image, interᵢ_exists, binterᵢ_and', interᵢ_interᵢ_eq_right]
#align set.sInter_prod Set.interₛ_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_interₛ {T : Set (Set β)} (hT : T.Nonempty) (s : Set α) :
    s ×ˢ ⋂₀ T = ⋂ t ∈ T, s ×ˢ t := by
  rw [← interₛ_singleton s, interₛ_prod_interₛ (singleton_nonempty s) hT, interₛ_singleton]
  simp_rw [singleton_prod, mem_image, interᵢ_exists, binterᵢ_and', interᵢ_interᵢ_eq_right]
#align set.prod_sInter Set.prod_interₛ

end Prod

section Image2

variable (f : α → β → γ) {s : Set α} {t : Set β}

theorem unionᵢ_image_left : (⋃ a ∈ s, f a '' t) = image2 f s t := by
  ext y
  constructor <;> simp only [mem_unionᵢ] <;> rintro ⟨a, ha, x, hx, ax⟩ <;> exact ⟨a, x, ha, hx, ax⟩
#align set.Union_image_left Set.unionᵢ_image_left

theorem unionᵢ_image_right : (⋃ b ∈ t, (fun a => f a b) '' s) = image2 f s t := by
  ext y
  constructor <;> simp only [mem_unionᵢ] <;> rintro ⟨a, b, c, d, e⟩
  exact ⟨c, a, d, b, e⟩
  exact ⟨b, d, a, c, e⟩
#align set.Union_image_right Set.unionᵢ_image_right

theorem image2_unionᵢ_left (s : ι → Set α) (t : Set β) :
    image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t := by
  simp only [← image_prod, unionᵢ_prod_const, image_unionᵢ]
#align set.image2_Union_left Set.image2_unionᵢ_left

theorem image2_unionᵢ_right (s : Set α) (t : ι → Set β) :
    image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i) := by
  simp only [← image_prod, prod_unionᵢ, image_unionᵢ]
#align set.image2_Union_right Set.image2_unionᵢ_right

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_unionᵢ₂_left (s : ∀ i, κ i → Set α) (t : Set β) :
    image2 f (⋃ (i) (j), s i j) t = ⋃ (i) (j), image2 f (s i j) t := by simp_rw [image2_unionᵢ_left]
#align set.image2_Union₂_left Set.image2_unionᵢ₂_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_unionᵢ₂_right (s : Set α) (t : ∀ i, κ i → Set β) :
    image2 f s (⋃ (i) (j), t i j) = ⋃ (i) (j), image2 f s (t i j) :=
  by simp_rw [image2_unionᵢ_right]
#align set.image2_Union₂_right Set.image2_unionᵢ₂_right

theorem image2_interᵢ_subset_left (s : ι → Set α) (t : Set β) :
    image2 f (⋂ i, s i) t ⊆ ⋂ i, image2 f (s i) t := by
  simp_rw [image2_subset_iff, mem_interᵢ]
  exact fun x hx y hy i => mem_image2_of_mem (hx _) hy
#align set.image2_Inter_subset_left Set.image2_interᵢ_subset_left

theorem image2_interᵢ_subset_right (s : Set α) (t : ι → Set β) :
    image2 f s (⋂ i, t i) ⊆ ⋂ i, image2 f s (t i) := by
  simp_rw [image2_subset_iff, mem_interᵢ]
  exact fun x hx y hy i => mem_image2_of_mem hx (hy _)
#align set.image2_Inter_subset_right Set.image2_interᵢ_subset_right

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_interᵢ₂_subset_left (s : ∀ i, κ i → Set α) (t : Set β) :
    image2 f (⋂ (i) (j), s i j) t ⊆ ⋂ (i) (j), image2 f (s i j) t := by
  simp_rw [image2_subset_iff, mem_interᵢ]
  exact fun x hx y hy i j => mem_image2_of_mem (hx _ _) hy
#align set.image2_Inter₂_subset_left Set.image2_interᵢ₂_subset_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_interᵢ₂_subset_right (s : Set α) (t : ∀ i, κ i → Set β) :
    image2 f s (⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), image2 f s (t i j) := by
  simp_rw [image2_subset_iff, mem_interᵢ]
  exact fun x hx y hy i j => mem_image2_of_mem hx (hy _ _)
#align set.image2_Inter₂_subset_right Set.image2_interᵢ₂_subset_right

/-- The `Set.image2` version of `Set.image_eq_unionᵢ` -/
theorem image2_eq_unionᵢ (s : Set α) (t : Set β) : image2 f s t = ⋃ (i ∈ s) (j ∈ t), {f i j} := by
  simp_rw [← image_eq_unionᵢ, unionᵢ_image_left]
#align set.image2_eq_Union Set.image2_eq_unionᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_bunionᵢ_left : s ×ˢ t = ⋃ a ∈ s, (fun b => (a, b)) '' t := by
  rw [unionᵢ_image_left, image2_mk_eq_prod]
#align set.prod_eq_bUnion_left Set.prod_eq_bunionᵢ_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_bunionᵢ_right : s ×ˢ t = ⋃ b ∈ t, (fun a => (a, b)) '' s := by
  rw [unionᵢ_image_right, image2_mk_eq_prod]
#align set.prod_eq_bUnion_right Set.prod_eq_bunionᵢ_right

end Image2

section Seq

/-- Given a set `s` of functions `α → β` and `t : Set α`, `seq s t` is the union of `f '' t` over
all `f ∈ s`. -/
def seq (s : Set (α → β)) (t : Set α) : Set β :=
  { b | ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b }
#align set.seq Set.seq

theorem seq_def {s : Set (α → β)} {t : Set α} : seq s t = ⋃ f ∈ s, f '' t :=
  Set.ext <| by simp [seq]
#align set.seq_def Set.seq_def

@[simp]
theorem mem_seq_iff {s : Set (α → β)} {t : Set α} {b : β} :
    b ∈ seq s t ↔ ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b :=
  Iff.rfl
#align set.mem_seq_iff Set.mem_seq_iff

theorem seq_subset {s : Set (α → β)} {t : Set α} {u : Set β} :
    seq s t ⊆ u ↔ ∀ f ∈ s, ∀ a ∈ t, (f : α → β) a ∈ u :=
  Iff.intro (fun h f hf a ha => h ⟨f, hf, a, ha, rfl⟩) fun h _ ⟨f, hf, a, ha, eq⟩ =>
    eq ▸ h f hf a ha
#align set.seq_subset Set.seq_subset

theorem seq_mono {s₀ s₁ : Set (α → β)} {t₀ t₁ : Set α} (hs : s₀ ⊆ s₁) (ht : t₀ ⊆ t₁) :
    seq s₀ t₀ ⊆ seq s₁ t₁ := fun _  ⟨f, hf, a, ha, eq⟩ => ⟨f, hs hf, a, ht ha, eq⟩
#align set.seq_mono Set.seq_mono

theorem singleton_seq {f : α → β} {t : Set α} : Set.seq ({f} : Set (α → β)) t = f '' t :=
  Set.ext <| by simp
#align set.singleton_seq Set.singleton_seq

theorem seq_singleton {s : Set (α → β)} {a : α} : Set.seq s {a} = (fun f : α → β => f a) '' s :=
  Set.ext <| by simp
#align set.seq_singleton Set.seq_singleton

theorem seq_seq {s : Set (β → γ)} {t : Set (α → β)} {u : Set α} :
    seq s (seq t u) = seq (seq ((· ∘ ·) '' s) t) u := by
  refine' Set.ext fun c => Iff.intro _ _
  · rintro ⟨f, hfs, b, ⟨g, hg, a, hau, rfl⟩, rfl⟩
    exact ⟨f ∘ g, ⟨(· ∘ ·) f, mem_image_of_mem _ hfs, g, hg, rfl⟩, a, hau, rfl⟩
  · rintro ⟨fg, ⟨fc, ⟨f, hfs, rfl⟩, g, hgt, rfl⟩, a, ha, rfl⟩
    exact ⟨f, hfs, g a, ⟨g, hgt, a, ha, rfl⟩, rfl⟩
#align set.seq_seq Set.seq_seq

theorem image_seq {f : β → γ} {s : Set (α → β)} {t : Set α} :
    f '' seq s t = seq ((· ∘ ·) f '' s) t := by
  rw [← singleton_seq, ← singleton_seq, seq_seq, image_singleton]
#align set.image_seq Set.image_seq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_seq {s : Set α} {t : Set β} : s ×ˢ t = (Prod.mk '' s).seq t := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨Prod.mk a, ⟨a, ha, rfl⟩, b, hb, rfl⟩
  · rintro ⟨f, ⟨x, hx, rfl⟩, y, hy, eq⟩
    rw [← eq]
    exact ⟨hx, hy⟩
#align set.prod_eq_seq Set.prod_eq_seq

theorem prod_image_seq_comm (s : Set α) (t : Set β) :
    (Prod.mk '' s).seq t = seq ((fun b a => (a, b)) '' t) s := by
  rw [← prod_eq_seq, ← image_swap_prod, prod_eq_seq, image_seq, ← image_comp]; rfl
#align set.prod_image_seq_comm Set.prod_image_seq_comm

theorem image2_eq_seq (f : α → β → γ) (s : Set α) (t : Set β) : image2 f s t = seq (f '' s) t := by
  ext
  simp
#align set.image2_eq_seq Set.image2_eq_seq

end Seq

section Pi

variable {π : α → Type _}

theorem pi_def (i : Set α) (s : ∀ a, Set (π a)) : pi i s = ⋂ a ∈ i, eval a ⁻¹' s a := by
  ext
  simp
#align set.pi_def Set.pi_def

theorem univ_pi_eq_interᵢ (t : ∀ i, Set (π i)) : pi univ t = ⋂ i, eval i ⁻¹' t i := by
  simp only [pi_def, interᵢ_true, mem_univ]
#align set.univ_pi_eq_Inter Set.univ_pi_eq_interᵢ

theorem pi_diff_pi_subset (i : Set α) (s t : ∀ a, Set (π a)) :
    pi i s \ pi i t ⊆ ⋃ a ∈ i, eval a ⁻¹' (s a \ t a) := by
  refine' diff_subset_comm.2 fun x hx a ha => _
  simp only [mem_diff, mem_pi, mem_unionᵢ, not_exists, mem_preimage, not_and, not_not,
    eval_apply] at hx
  exact hx.2 _ ha (hx.1 _ ha)
#align set.pi_diff_pi_subset Set.pi_diff_pi_subset

theorem unionᵢ_univ_pi (t : ∀ i, ι → Set (π i)) :
    (⋃ x : α → ι, pi univ fun i => t i (x i)) = pi univ fun i => ⋃ j : ι, t i j := by
  ext
  simp [Classical.skolem]
#align set.Union_univ_pi Set.unionᵢ_univ_pi

end Pi

end Set

namespace Function

namespace Surjective

theorem unionᵢ_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : (⋃ x, g (f x)) = ⋃ y, g y :=
  hf.supᵢ_comp g
#align function.surjective.Union_comp Function.Surjective.unionᵢ_comp

theorem interᵢ_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : (⋂ x, g (f x)) = ⋂ y, g y :=
  hf.infᵢ_comp g
#align function.surjective.Inter_comp Function.Surjective.interᵢ_comp

end Surjective

end Function

/-!
### Disjoint sets
-/


section Disjoint

variable {s t u : Set α} {f : α → β}

namespace Set

@[simp]
theorem disjoint_unionᵢ_left {ι : Sort _} {s : ι → Set α} :
    Disjoint (⋃ i, s i) t ↔ ∀ i, Disjoint (s i) t :=
  supᵢ_disjoint_iff
#align set.disjoint_Union_left Set.disjoint_unionᵢ_left

@[simp]
theorem disjoint_unionᵢ_right {ι : Sort _} {s : ι → Set α} :
    Disjoint t (⋃ i, s i) ↔ ∀ i, Disjoint t (s i) :=
  disjoint_supᵢ_iff
#align set.disjoint_Union_right Set.disjoint_unionᵢ_right

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
--Porting note: removing `simp`. `simp` can prove it
theorem disjoint_unionᵢ₂_left {s : ∀ i, κ i → Set α} {t : Set α} :
    Disjoint (⋃ (i) (j), s i j) t ↔ ∀ i j, Disjoint (s i j) t :=
  supᵢ₂_disjoint_iff
#align set.disjoint_Union₂_left Set.disjoint_unionᵢ₂_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
--Porting note: removing `simp`. `simp` can prove it
theorem disjoint_unionᵢ₂_right {s : Set α} {t : ∀ i, κ i → Set α} :
    Disjoint s (⋃ (i) (j), t i j) ↔ ∀ i j, Disjoint s (t i j) :=
  disjoint_supᵢ₂_iff
#align set.disjoint_Union₂_right Set.disjoint_unionᵢ₂_right

@[simp]
theorem disjoint_unionₛ_left {S : Set (Set α)} {t : Set α} :
    Disjoint (⋃₀S) t ↔ ∀ s ∈ S, Disjoint s t :=
  supₛ_disjoint_iff
#align set.disjoint_sUnion_left Set.disjoint_unionₛ_left

@[simp]
theorem disjoint_unionₛ_right {s : Set α} {S : Set (Set α)} :
    Disjoint s (⋃₀S) ↔ ∀ t ∈ S, Disjoint s t :=
  disjoint_supₛ_iff
#align set.disjoint_sUnion_right Set.disjoint_unionₛ_right

end Set

end Disjoint

/-! ### Intervals -/


namespace Set

variable [CompleteLattice α]

theorem Ici_supᵢ (f : ι → α) : Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  ext fun _ => by simp only [mem_Ici, supᵢ_le_iff, mem_interᵢ]
#align set.Ici_supr Set.Ici_supᵢ

theorem Iic_infᵢ (f : ι → α) : Iic (⨅ i, f i) = ⋂ i, Iic (f i) :=
  ext fun _ => by simp only [mem_Iic, le_infᵢ_iff, mem_interᵢ]
#align set.Iic_infi Set.Iic_infᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Ici_supᵢ₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⋂ (i) (j), Ici (f i j) := by
  simp_rw [Ici_supᵢ]
#align set.Ici_supr₂ Set.Ici_supᵢ₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Iic_infᵢ₂ (f : ∀ i, κ i → α) : Iic (⨅ (i) (j), f i j) = ⋂ (i) (j), Iic (f i j) := by
  simp_rw [Iic_infᵢ]
#align set.Iic_infi₂ Set.Iic_infᵢ₂

theorem Ici_supₛ (s : Set α) : Ici (supₛ s) = ⋂ a ∈ s, Ici a := by rw [supₛ_eq_supᵢ, Ici_supᵢ₂]
#align set.Ici_Sup Set.Ici_supₛ

theorem Iic_infₛ (s : Set α) : Iic (infₛ s) = ⋂ a ∈ s, Iic a := by rw [infₛ_eq_infᵢ, Iic_infᵢ₂]
#align set.Iic_Inf Set.Iic_infₛ

end Set

namespace Set

variable (t : α → Set β)

theorem bunionᵢ_diff_bunionᵢ_subset (s₁ s₂ : Set α) :
    ((⋃ x ∈ s₁, t x) \ ⋃ x ∈ s₂, t x) ⊆ ⋃ x ∈ s₁ \ s₂, t x := by
  simp only [diff_subset_iff, ← bunionᵢ_union]
  apply bunionᵢ_subset_bunionᵢ_left
  rw [union_diff_self]
  apply subset_union_right
#align set.bUnion_diff_bUnion_subset Set.bunionᵢ_diff_bunionᵢ_subset

/-- If `t` is an indexed family of sets, then there is a natural map from `Σ i, t i` to `⋃ i, t i`
sending `⟨i, x⟩` to `x`. -/
def sigmaToUnionᵢ (x : Σi, t i) : ⋃ i, t i :=
  ⟨x.2, mem_unionᵢ.2 ⟨x.1, x.2.2⟩⟩
#align set.sigma_to_Union Set.sigmaToUnionᵢ

theorem sigmaToUnionᵢ_surjective : Surjective (sigmaToUnionᵢ t)
  | ⟨b, hb⟩ =>
    have : ∃ a, b ∈ t a := by simpa using hb
    let ⟨a, hb⟩ := this
    ⟨⟨a, b, hb⟩, rfl⟩
#align set.sigma_to_Union_surjective Set.sigmaToUnionᵢ_surjective

theorem sigmaToUnionᵢ_injective (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) :
    Injective (sigmaToUnionᵢ t)
  | ⟨a₁, b₁, h₁⟩, ⟨a₂, b₂, h₂⟩, eq =>
    have b_eq : b₁ = b₂ := congr_arg Subtype.val eq
    have a_eq : a₁ = a₂ :=
      by_contradiction fun ne =>
        have : b₁ ∈ t a₁ ∩ t a₂ := ⟨h₁, b_eq.symm ▸ h₂⟩
        (h _ _ ne).le_bot this
    Sigma.eq a_eq <| Subtype.eq <| by subst b_eq; subst a_eq; rfl
#align set.sigma_to_Union_injective Set.sigmaToUnionᵢ_injective

theorem sigmaToUnionᵢ_bijective (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) :
    Bijective (sigmaToUnionᵢ t) :=
  ⟨sigmaToUnionᵢ_injective t h, sigmaToUnionᵢ_surjective t⟩
#align set.sigma_to_Union_bijective Set.sigmaToUnionᵢ_bijective

/-- Equivalence between a disjoint union and a dependent sum. -/
noncomputable def unionEqSigmaOfDisjoint {t : α → Set β} (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) :
    (⋃ i, t i) ≃ Σi, t i :=
  (Equiv.ofBijective _ <| sigmaToUnionᵢ_bijective t h).symm
#align set.Union_eq_sigma_of_disjoint Set.unionEqSigmaOfDisjoint

theorem unionᵢ_ge_eq_unionᵢ_nat_add (u : ℕ → Set α) (n : ℕ) : (⋃ i ≥ n, u i) = ⋃ i, u (i + n) :=
  supᵢ_ge_eq_supᵢ_nat_add u n
#align set.Union_ge_eq_Union_nat_add Set.unionᵢ_ge_eq_unionᵢ_nat_add

theorem interᵢ_ge_eq_interᵢ_nat_add (u : ℕ → Set α) (n : ℕ) : (⋂ i ≥ n, u i) = ⋂ i, u (i + n) :=
  infᵢ_ge_eq_infᵢ_nat_add u n
#align set.Inter_ge_eq_Inter_nat_add Set.interᵢ_ge_eq_interᵢ_nat_add

theorem _root_.Monotone.unionᵢ_nat_add {f : ℕ → Set α} (hf : Monotone f) (k : ℕ) :
    (⋃ n, f (n + k)) = ⋃ n, f n :=
  hf.supᵢ_nat_add k
#align monotone.Union_nat_add Monotone.unionᵢ_nat_add

theorem _root_.Antitone.interᵢ_nat_add {f : ℕ → Set α} (hf : Antitone f) (k : ℕ) :
    (⋂ n, f (n + k)) = ⋂ n, f n :=
  hf.infᵢ_nat_add k
#align antitone.Inter_nat_add Antitone.interᵢ_nat_add

/-Porting note: removing `simp`. LHS does not simplify. Possible linter bug. Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/complete_lattice.20and.20has_sup/near/316497982
-/
theorem unionᵢ_interᵢ_ge_nat_add (f : ℕ → Set α) (k : ℕ) :
    (⋃ n, ⋂ i ≥ n, f (i + k)) = ⋃ n, ⋂ i ≥ n, f i :=
  supᵢ_infᵢ_ge_nat_add f k
#align set.Union_Inter_ge_nat_add Set.unionᵢ_interᵢ_ge_nat_add

theorem union_unionᵢ_nat_succ (u : ℕ → Set α) : (u 0 ∪ ⋃ i, u (i + 1)) = ⋃ i, u i :=
  sup_supᵢ_nat_succ u
#align set.union_Union_nat_succ Set.union_unionᵢ_nat_succ

theorem inter_interᵢ_nat_succ (u : ℕ → Set α) : (u 0 ∩ ⋂ i, u (i + 1)) = ⋂ i, u i :=
  inf_infᵢ_nat_succ u
#align set.inter_Inter_nat_succ Set.inter_interᵢ_nat_succ

end Set

open Set

variable [CompleteLattice β]

theorem supᵢ_unionᵢ (s : ι → Set α) (f : α → β) : (⨆ a ∈ ⋃ i, s i, f a) = ⨆ (i) (a ∈ s i), f a := by
  rw [supᵢ_comm]
  simp_rw [mem_unionᵢ, supᵢ_exists]
#align supr_Union supᵢ_unionᵢ

theorem infᵢ_unionᵢ (s : ι → Set α) (f : α → β) : (⨅ a ∈ ⋃ i, s i, f a) = ⨅ (i) (a ∈ s i), f a :=
  @supᵢ_unionᵢ α βᵒᵈ _ _ s f
#align infi_Union infᵢ_unionᵢ

theorem supₛ_unionₛ (s : Set (Set β)) : supₛ (⋃₀s) = ⨆ t ∈ s, supₛ t := by
  simp only [unionₛ_eq_bunionᵢ, supₛ_eq_supᵢ, supᵢ_unionᵢ]
#align Sup_sUnion supₛ_unionₛ

theorem infₛ_unionₛ (s : Set (Set β)) : infₛ (⋃₀s) = ⨅ t ∈ s, infₛ t :=
  @supₛ_unionₛ βᵒᵈ _ _
#align Inf_sUnion infₛ_unionₛ
