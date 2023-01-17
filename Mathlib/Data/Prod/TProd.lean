/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module data.prod.tprod
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.List.Nodup
set_option autoImplicit false
/-!
# Finite products of types

This file defines the product of types over a list. For `l : list ι` and `α : ι → Type*` we define
`list.TProd α l = l.foldr (λ i β, α i × β) PUnit`.
This type should not be used if `Π i, α i` or `Π i ∈ l, α i` can be used instead
(in the last expression, we could also replace the list `l` by a set or a finset).
This type is used as an intermediary between binary products and finitary products.
The application of this type is finitary product measures, but it could be used in any
construction/theorem that is easier to define/prove on binary products than on finitary products.

* Once we have the construction on binary products (like binary product measures in
  `MeasureTheory.prod`), we can easily define a finitary version on the type `TProd l α`
  by iterating. Properties can also be easily extended from the binary case to the finitary case
  by iterating.
* Then we can use the equivalence `List.TProd.pi_equiv_tprod` below (or enhanced versions of it,
  like a `MeasurableEquiv` for product measures) to get the construction on `Π i : ι, α i`, at
  least when assuming `[Fintype ι] [Encodable ι]` (using `Encodable.sorted_univ`).
  Using `local attribute [instance] Fintype.toEncodable` we can get rid of the argument
  `[Encodable ι]`.

## Main definitions

* We have the equivalence `TProd.pi_equiv_tprod : (Π i, α i) ≃ TProd α l`
  if `l` contains every element of `ι` exactly once.
* The product of sets is `Set.TProd : (Π i, set (α i)) → set (TProd α l)`.
-/


open List Function
universe u v
variable {ι : Type u} {α : ι → Type v} {i j : ι} {l : List ι} {f : ∀ i, α i}

namespace List

variable (α)

/-- The product of a family of types over a list. -/
def TProd (l : List ι) : Type v :=
  l.foldr (fun i β => α i × β) PUnit
#align list.tprod List.TProd

variable {α}

namespace TProd

open List

/- warning: list.tprod.mk -> List.TProd.mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} (l : List.{u1} ι), (forall (i : ι), α i) -> (List.TProd.{u1, u2, u3} ι α l)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u3}} (l : List.{u2} ι), (forall (i : ι), α i) -> (List.TProd.{u2, u3, u1} ι α l)
Case conversion may be inaccurate. Consider using '#align list.tprod.mk List.TProd.mkₓ'. -/
/-- Turning a function `f : ∀ i, α i` into an element of the iterated product `TProd α l`. -/
protected def mk : ∀ (l : List ι) (_f : ∀ i, α i), TProd α l
  | [] => fun _ => PUnit.unit
  | i :: is => fun f => (f i, TProd.mk is f)
#align list.tprod.mk List.TProd.mk

instance [∀ i, Inhabited (α i)] : Inhabited (TProd α l) :=
  ⟨TProd.mk l default⟩

@[simp]
theorem fst_mk (i : ι) (l : List ι) (f : ∀ i, α i) : (TProd.mk (i :: l) f).1 = f i :=
  rfl
#align list.tprod.fst_mk List.TProd.fst_mk

@[simp]
theorem snd_mk (i : ι) (l : List ι) (f : ∀ i, α i) : (TProd.mk.{u,v} (i :: l) f).2 = TProd.mk.{u,v} l f :=
  rfl
#align list.tprod.snd_mk List.TProd.snd_mk

variable [DecidableEq ι]

/- warning: list.tprod.elim -> List.TProd.elim is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] {l : List.{u1} ι}, (List.TProd.{u1, u2, u3} ι α l) -> (forall {i : ι}, (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (α i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u3}} [_inst_1 : DecidableEq.{succ u2} ι] {l : List.{u2} ι}, (List.TProd.{u2, u3, u1} ι α l) -> (forall {i : ι}, (Membership.Mem.{u2, u2} ι (List.{u2} ι) (List.hasMem.{u2} ι) i l) -> (α i))
Case conversion may be inaccurate. Consider using '#align list.tprod.elim List.TProd.elimₓ'. -/
/-- Given an element of the iterated product `l.Prod α`, take a projection into direction `i`.
  If `i` appears multiple times in `l`, this chooses the first component in direction `i`. -/
protected def elim : ∀ {l : List ι} (_ : TProd α l) {i : ι} (_ : i ∈ l), α i
  | i :: is, v, j, hj =>
    if hji : j = i then by
      subst hji
      exact v.1
    else TProd.elim v.2 ((List.mem_cons.mp hj).resolve_left hji)
#align list.tprod.elim List.TProd.elim

@[simp]
theorem elim_self (v : TProd α (i :: l)) : v.elim (l.mem_cons_self i) = v.1 := by simp [TProd.elim]
#align list.tprod.elim_self List.TProd.elim_self

@[simp]
theorem elim_of_ne (hj : j ∈ i :: l) (hji : j ≠ i) (v : TProd α (i :: l)) :
    v.elim hj = TProd.elim v.2 ((List.mem_cons.mp hj).resolve_left hji) := by simp [TProd.elim, hji]
#align list.tprod.elim_of_ne List.TProd.elim_of_ne

@[simp]
theorem elim_of_mem (hl : (i :: l).Nodup) (hj : j ∈ l) (v : TProd α (i :: l)) :
    v.elim (mem_cons_of_mem _ hj) = TProd.elim v.2 hj :=
  by
  apply elim_of_ne
  rintro rfl
  exact hl.not_mem hj
#align list.tprod.elim_of_mem List.TProd.elim_of_mem

theorem elim_mk : ∀ (l : List ι) (f : ∀ i, α i) {i : ι} (hi : i ∈ l), (TProd.mk l f).elim hi = f i
  | i :: is, f, j, hj => by
    by_cases hji : j = i
    · subst hji
      simp
    · rw [TProd.elim_of_ne _ hji, snd_mk, elim_mk]
#align list.tprod.elim_mk List.TProd.elim_mk

@[ext]
theorem ext :
    ∀ {l : List ι} (hl : l.Nodup) {v w : TProd α l}
      (hvw : ∀ (i) (hi : i ∈ l), v.elim hi = w.elim hi), v = w
  | [], hl, v, w, hvw => PUnit.ext v w
  | i :: is, hl, v, w, hvw => by
    ext; rw [← elim_self v, hvw, elim_self]
    refine' ext (nodup_cons.mp hl).2 fun j hj => _
    rw [← elim_of_mem hl, hvw, elim_of_mem hl]
#align list.tprod.ext List.TProd.ext

/-- A version of `TProd.elim` when `l` contains all elements. In this case we get a function into
  `Π i, α i`. -/
@[simp]
protected def elim' (h : ∀ i, i ∈ l) (v : TProd α l) (i : ι) : α i :=
  v.elim (h i)
#align list.tprod.elim' List.TProd.elim'

theorem mk_elim (hnd : l.Nodup) (h : ∀ i, i ∈ l) (v : TProd α l) : TProd.mk l (v.elim' h) = v :=
  TProd.ext hnd fun i hi => by simp [elim_mk]
#align list.tprod.mk_elim List.TProd.mk_elim

/-- Pi-types are equivalent to iterated products. -/
def piEquivTProd (hnd : l.Nodup) (h : ∀ i, i ∈ l) : (∀ i, α i) ≃ TProd α l :=
  ⟨TProd.mk l, TProd.elim' h, fun f => funext fun i => elim_mk l f (h i), mk_elim hnd h⟩
#align list.tprod.pi_equiv_tprod List.TProd.piEquivTProd

end TProd

end List

namespace Set

open List

/- warning: set.tprod -> Set.tprod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} (l : List.{u1} ι), (forall (i : ι), Set.{u2} (α i)) -> (Set.{max u2 u3} (List.TProd.{u1, u2, u3} ι α l))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u3}} (l : List.{u2} ι), (forall (i : ι), Set.{u3} (α i)) -> (Set.{max u3 u1} (List.TProd.{u2, u3, u1} ι α l))
Case conversion may be inaccurate. Consider using '#align set.tprod Set.tprodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A product of sets in `TProd α l`. -/
@[simp]
protected def TProd : ∀ (l : List ι) (_t : ∀ i, Set (α i)), Set (TProd α l)
  | [], _ => univ
  | i :: is, t => t i ×ˢ Set.TProd is t
#align set.tprod Set.TProd

theorem mk_preimage_tprod :
    ∀ (l : List ι) (t : ∀ i, Set (α i)), TProd.mk l ⁻¹' Set.TProd l t = { i | i ∈ l }.pi t
  | [], t => by simp [Set.TProd]
  | i :: l, t => by
    ext f
    have h : f ∈ TProd.mk l ⁻¹' Set.TProd l t ↔ f ∈ { x | x ∈ l }.pi t := by
      rw [mk_preimage_tprod l t]

    change (TProd.mk l f ∈ Set.TProd l t ↔ ∀ i : ι, i ∈ l → f i ∈ t i) at h

    -- `simp [Set.TProd, TProd.mk, this]` can close this goal but is slow.
    rw [Set.tprod, tprod.mk, mem_preimage, mem_pi, prod_mk_mem_set_prod_eq]
    simp_rw [mem_set_of_eq, mem_cons_iff]
    rw [forall_eq_or_imp, and_congr_right_iff]
    exact fun _ => this
#align set.mk_preimage_tprod Set.mk_preimage_tprod

theorem elim_preimage_pi [DecidableEq ι] {l : List ι} (hnd : l.Nodup) (h : ∀ i, i ∈ l)
    (t : ∀ i, Set (α i)) : TProd.elim' h ⁻¹' pi univ t = Set.TProd l t :=
  by
  have : { i | i ∈ l } = univ := by
    ext i
    simp [h]
  rw [← this, ← mk_preimage_tprod, preimage_preimage]
  convert @preimage_id
  simp [TProd.mk_elim hnd h, id_def]
#align set.elim_preimage_pi Set.elim_preimage_pi

end Set
