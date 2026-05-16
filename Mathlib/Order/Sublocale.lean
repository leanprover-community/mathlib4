/-
Copyright (c) 2025 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
module

public import Mathlib.Order.Nucleus
public import Mathlib.Order.SupClosed

/-!
# Sublocale

Locales are the dual concept to frames. Locale theory is a branch of point-free topology, where
intuitively locales are like topological spaces which may or may not have enough points.
Sublocales of a locale generalize the concept of subspaces in topology to the point-free setting.

## TODO

Create separate definitions for `sInf_mem` and `HImpClosed` (also useful for `CompleteSublattice`)

## References

* [J. Picada A. Pultr, *Frames and Locales*][picado2012]
* https://ncatlab.org/nlab/show/sublocale
* https://ncatlab.org/nlab/show/nucleus
-/

@[expose] public section

variable {X : Type*} [Order.Frame X]
open Set

/-- A sublocale of a locale `X` is a set `S` which is closed under all meets and such that
`x ⇨ s ∈ S` for all `x : X` and `s ∈ S`.

Note that locales are the same thing as frames, but with reverse morphisms, which is why we assume
`Frame X`. We only need to define locales categorically. See `Locale`. -/
structure Sublocale (X : Type*) [Order.Frame X] where
  /-- The set corresponding to the sublocale. -/
  carrier : Set X
  /-- A sublocale is closed under all meets.

  Do NOT use directly. Use `Sublocale.sInf_mem` instead. -/
  sInf_mem' : ∀ s ⊆ carrier, sInf s ∈ carrier
  /-- A sublocale is closed under heyting implication.

  Do NOT use directly. Use `Sublocale.himp_mem` instead. -/
  himp_mem' : ∀ a b, b ∈ carrier → a ⇨ b ∈ carrier

namespace Sublocale

variable {ι : Sort*} {S T : Sublocale X} {s : Set X} {f : ι → X} {a b : X}

instance instSetLike : SetLike (Sublocale X) X where
  coe x := x.carrier
  coe_injective' s1 s2 h := by cases s1; congr

instance : PartialOrder (Sublocale X) := .ofSetLike (Sublocale X) X

@[simp] lemma mem_carrier : a ∈ S.carrier ↔ a ∈ S := .rfl

@[simp] lemma mem_mk (carrier : Set X) (sInf_mem' himp_mem') :
    a ∈ mk carrier sInf_mem' himp_mem' ↔ a ∈ carrier := .rfl

@[simp, gcongr]
lemma mk_le_mk (carrier₁ carrier₂ : Set X) (sInf_mem'₁ sInf_mem'₂ himp_mem'₁ himp_mem'₂) :
    mk carrier₁ sInf_mem'₁ himp_mem'₁ ≤ mk carrier₂ sInf_mem'₂ himp_mem'₂ ↔ carrier₁ ⊆ carrier₂ :=
  .rfl

initialize_simps_projections Sublocale (carrier → coe, as_prefix coe)

@[ext] lemma ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

lemma sInf_mem (hs : s ⊆ S) : sInf s ∈ S := S.sInf_mem' _ hs
lemma iInf_mem (hf : ∀ i, f i ∈ S) : ⨅ i, f i ∈ S := S.sInf_mem <| by simpa [range_subset_iff]

lemma infClosed : InfClosed (S : Set X) := by
  rintro a ha b hb; rw [← sInf_pair]; exact S.sInf_mem (pair_subset ha hb)

lemma inf_mem (ha : a ∈ S) (hb : b ∈ S) : a ⊓ b ∈ S := S.infClosed ha hb

lemma top_mem : ⊤ ∈ S := by simpa using S.sInf_mem <| empty_subset _

lemma himp_mem (hb : b ∈ S) : a ⇨ b ∈ S := S.himp_mem' _ _ hb

instance carrier.instSemilatticeInf : SemilatticeInf S := Subtype.semilatticeInf fun _ _ ↦ inf_mem

instance carrier.instOrderTop : OrderTop S := Subtype.orderTop top_mem

instance carrier.instHImp : HImp S where himp a b := ⟨a ⇨ b, S.himp_mem b.2⟩

instance carrier.instInfSet : InfSet S where
  sInf x := ⟨sInf (Subtype.val '' x), S.sInf_mem' _
    (by simp_rw [image_subset_iff, subset_def]; simp)⟩

@[simp, norm_cast] lemma coe_inf (a b : S) : (a ⊓ b).val = ↑a ⊓ ↑b := rfl
@[simp, norm_cast] lemma coe_sInf (s : Set S) : (sInf s).val = sInf (Subtype.val '' s) := rfl
@[simp, norm_cast] lemma coe_iInf (f : ι → S) : (⨅ i, f i).val = ⨅ i, (f i).val := by
  simp [iInf, ← range_comp, Function.comp_def]

instance carrier.instCompleteLattice : CompleteLattice S where
  __ := instSemilatticeInf
  __ := instOrderTop
  __ := completeLatticeOfInf S <| by simp [isGLB_iff_le_iff, lowerBounds, ← Subtype.coe_le_coe]

@[simp, norm_cast] lemma coe_himp (a b : S) : (a ⇨ b).val = a.val ⇨ b.val := rfl

instance carrier.instHeytingAlgebra : HeytingAlgebra S where
  le_himp_iff a b c := by simp [← Subtype.coe_le_coe, ← @Sublocale.coe_inf, himp]
  compl a := a ⇨ ⊥
  himp_bot _ := rfl

instance carrier.instFrame : Order.Frame S where
  __ := carrier.instHeytingAlgebra
  __ := carrier.instCompleteLattice

set_option backward.privateInPublic true in
/-- See `Sublocale.restrict` for the public-facing version. -/
private def restrictAux (S : Sublocale X) (a : X) : S := sInf {s : S | a ≤ s}

private lemma le_restrictAux : a ≤ S.restrictAux a := by simp +contextual [restrictAux]

set_option backward.privateInPublic true in
/-- See `Sublocale.giRestrict` for the public-facing version. -/
private def giAux (S : Sublocale X) : GaloisInsertion S.restrictAux Subtype.val where
  choice x hx := ⟨x, by
    rw [le_antisymm le_restrictAux hx]
    exact S.sInf_mem <| by simp +contextual [Set.subset_def]⟩
  gc a b := by
    constructor <;> intro h
    · exact le_trans (by simp +contextual [restrictAux]) h
    · exact sInf_le (by simp [h])
  le_l_u x := by simp [restrictAux]
  choice_eq a h := by simp [le_antisymm_iff, restrictAux, sInf_le]

/-- The restriction from a locale X into the sublocale S. -/
def restrict (S : Sublocale X) : FrameHom X S where
  toFun x := sInf {s : S | x ≤ s}
  map_inf' a b := by
    change Sublocale.restrictAux S (a ⊓ b) = Sublocale.restrictAux S a ⊓ Sublocale.restrictAux S b
    refine eq_of_forall_ge_iff (fun s ↦ Iff.symm ?_)
    calc
      _ ↔ S.restrictAux a ≤ S.restrictAux b ⇨ s := by simp
      _ ↔ S.restrictAux b ≤ a ⇨ s := by rw [S.giAux.gc.le_iff_le, @le_himp_comm, coe_himp]
      _ ↔ b ≤ a ⇨ s := by
        set c : S := ⟨a ⇨ s, S.himp_mem s.coe_prop⟩
        change Sublocale.restrictAux S b ≤ c.val ↔ b ≤ c
        rw [S.giAux.u_le_u_iff, S.giAux.gc.le_iff_le]
      _ ↔ S.restrictAux (a ⊓ b) ≤ s := by simp [inf_comm, S.giAux.gc.le_iff_le]
  map_sSup' s := by
    change Sublocale.restrictAux S (sSup s) = _
    rw [S.giAux.gc.l_sSup, sSup_image]
    rfl
  map_top' := by
    refine le_antisymm le_top ?_
    change _ ≤ restrictAux S ⊤
    rw [← Subtype.coe_le_coe, S.giAux.gc.u_top]
    simp [restrictAux, sInf]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The restriction corresponding to a sublocale forms a Galois insertion with the forgetful map
from the sublocale to the original locale. -/
def giRestrict (S : Sublocale X) : GaloisInsertion S.restrict Subtype.val := S.giAux

@[simp] lemma restrict_of_mem (ha : a ∈ S) : S.restrict a = ⟨a, ha⟩ := S.giRestrict.l_u_eq ⟨a, ha⟩

end Sublocale

/-- The nuclei on a frame corresponds exactly to the sublocales on this frame.
The sublocales are ordered dually to the nuclei. -/
@[simps] def nucleusIsoSublocale : (Nucleus X)ᵒᵈ ≃o Sublocale X where
  -- The range of a nucleus is a sublocale.
  toFun n := {
    carrier := range n.ofDual,
    sInf_mem' a h := (by
    rw [Nucleus.mem_range]
    refine le_antisymm (le_sInf_iff.mpr (fun b h1 ↦ ?_)) Nucleus.le_apply
    simp_rw [subset_def, Nucleus.mem_range] at h
    rw [← h b h1]
    exact n.monotone (sInf_le h1)),
    himp_mem' a b h := by rw [Nucleus.mem_range, ← h, Nucleus.map_himp_apply] at *
  }
  -- The restriction from the locale X into a sublocale is a nucleus.
  invFun s := .toDual {
    toFun x := s.restrict x
    map_inf' _ _ := by simp [s.giRestrict.gc.u_inf]
    idempotent' _ := by rw [s.giRestrict.gc.l_u_l_eq_l]
    le_apply' _ := s.giRestrict.gc.le_u_l _
  }
  left_inv n := by
    simp only [OrderDual.ext_iff, OrderDual.ofDual_toDual, Nucleus.ext_iff, Nucleus.coe_mk,
      InfHom.coe_mk]
    intro x
    simpa [Sublocale.restrict, sInf_image, le_antisymm_iff (a := iInf _)] using
      ⟨iInf₂_le_of_le ⟨n.ofDual x, x, rfl⟩ n.ofDual.le_apply le_rfl,
        fun y hxy ↦ by simpa using n.ofDual.monotone hxy⟩
  right_inv S := by ext x; simpa using ⟨by simp +contextual [eq_comm], fun hx ↦ ⟨x, by simp [hx]⟩⟩
  map_rel_iff' := by simp


namespace Sublocale

/-- The restriction from the locale X into a sublocale is a nucleus· -/
abbrev toNucleus (S : Sublocale X) : Nucleus X := (nucleusIsoSublocale.symm S).ofDual

variable {S T : Sublocale X}

@[simp] lemma coe_nucleusIsoSublocale_apply {i : X} :
  (nucleusIsoSublocale.symm S).ofDual i = S.restrict i := rfl

@[simp] lemma range_toNucleus : range S.toNucleus = S := by
  ext x
  constructor
  · simp +contextual [eq_comm]
  · intro hx
    exact ⟨x, by simp_all⟩

lemma toNucleus_le_toNucleus : S.toNucleus ≤ T.toNucleus ↔ T ≤ S := by
  simp [↓← Nucleus.range_subset_range]

lemma mem_iff_mem_range_toNucleus {i : X} : i ∈ S ↔ i ∈ range S.toNucleus := by simp

end Sublocale

namespace Nucleus

/-- The range of a nucleus is a sublocale. -/
abbrev toSublocale (n : Nucleus X) : Sublocale X := nucleusIsoSublocale (OrderDual.toDual n)

@[simp]
lemma mem_toSublocale {n : Nucleus X} {x : X} : x ∈ n.toSublocale ↔ ∃ y, n y = x := .rfl

@[simp, gcongr] lemma toSublocale_le_toSublocale {m n : Nucleus X} :
    m.toSublocale ≤ n.toSublocale ↔ n ≤ m := by simp [← SetLike.coe_subset_coe]

@[simp] lemma restrict_toSublocale (n : Nucleus X) (x : X) :
    n.toSublocale.restrict x = ⟨n x, x, rfl⟩ := by
  ext
  simpa [Sublocale.restrict, sInf_image, le_antisymm_iff (a := iInf _)] using
    ⟨iInf₂_le_of_le ⟨n x, x, rfl⟩ n.le_apply le_rfl, fun y hxy ↦ by simpa using n.monotone hxy⟩

end Nucleus

instance Sublocale.instCompleteLattice : CompleteLattice (Sublocale X) where
  top := ⟨univ, fun _ _ ↦ mem_univ _, fun _ _ a ↦ a⟩
  le_top x := (mk_le_mk _ _ _ _ _ _).mpr <| subset_univ x.carrier
  bot := ⟨{⊤}, by simp , by simp⟩
  bot_le x := (mk_le_mk _ _ _ _ _ _).mpr <| singleton_subset_iff.mpr <| mem_carrier.mpr top_mem
  __ := nucleusIsoSublocale.toGaloisInsertion.liftCompleteLattice

lemma Sublocale.univ_eq_top :
  (⟨univ, fun _ _ ↦ mem_univ _, fun _ _ a ↦ a⟩ : Sublocale X) = ⊤ := rfl

lemma Sublocale.singleton_top_eq_bot : (⟨{⊤}, by simp, by simp⟩ : Sublocale X) = ⊥ := rfl

set_option backward.isDefEq.respectTransparency false in
lemma Sublocale.inf_carrier {A B : Sublocale X} : A ⊓ B =
    ⟨A.carrier ⊓ B.carrier, (by simp; grind [sInf_mem]), by simp; grind [himp_mem]⟩ := by
  apply le_antisymm
  · simp only [inf_eq_inter, ← toNucleus_le_toNucleus, toNucleus, nucleusIsoSublocale,
    OrderIso.symm_mk, RelIso.coe_fn_mk, Equiv.coe_fn_symm_mk, OrderDual.ofDual_toDual, map_inf,
    ofDual_inf, ← Nucleus.coe_le_coe, Nucleus.coe_mk, InfHom.coe_mk, Pi.le_def]
    rw [Sublocale.restrict, ← sSup_pair,  ← sInf_upperBounds_eq_sSup]
    simp only [FrameHom.coe_mk, InfTopHom.coe_mk, InfHom.coe_mk, coe_sInf, ↓Nucleus.sInf_apply,
      upperBounds_insert, upperBounds_singleton, Ici_inter_Ici, mem_Ici, sup_le_iff,
      ← Nucleus.coe_le_coe, Nucleus.coe_mk, Pi.le_def, le_iInf_iff, sInf_le_iff, lowerBounds,
      mem_image, mem_setOf_eq, Subtype.exists, mem_mk, mem_inter_iff, mem_carrier, exists_and_left,
      exists_prop, exists_eq_right_right, and_imp]
    refine fun i n h1 h2 _ h3 ↦ h3 Nucleus.le_apply ?_ ?_
    <;> rw [mem_iff_mem_range_toNucleus, Nucleus.mem_range]
    · exact le_antisymm (le_trans (h1 (n i)) (le_of_eq (n.idempotent i))) Nucleus.le_apply
    · exact le_antisymm (le_trans (h2 (n i)) (le_of_eq (n.idempotent i))) Nucleus.le_apply
  · simp only [↓le_inf_iff, inf_eq_inter, SetLike.le_def, mem_mk, mem_inter_iff, mem_carrier,
    and_imp, imp_self, implies_true, and_true]
    grind

instance Sublocale.instCoframeMinimalAxioms : Order.Coframe.MinimalAxioms (Sublocale X) where
  iInf_sup_le_sup_sInf a s := by simp [← toNucleus_le_toNucleus,
  nucleusIsoSublocale.symm.map_sup,
    nucleusIsoSublocale.symm.map_sInf, sup_iInf_eq, nucleusIsoSublocale.symm.map_iInf]

instance Sublocale.instCoframe : Order.Coframe (Sublocale X) :=
  .ofMinimalAxioms Sublocale.instCoframeMinimalAxioms

/--
An open sublocale is defined by an element of the locale.
-/
@[ext]
structure Open (X : Type*) [Order.Frame X] where
  /-- The element of an open sublocale· Do not use this directly, use `Open.getElement` instead· -/
  element : X

namespace Open

instance : PartialOrder (Open X) where
  le x y := x.element ≤ y.element
  le_refl _ := le_refl _
  le_trans _ _ _ h1 h2 := le_trans h1 h2
  le_antisymm _ _ h1 h2 := by ext; exact le_antisymm h1 h2

variable {U V : Open X}

/--
The order of open sublocales is determined by their element.
-/
def getElement : Open X ≃o X where
  toFun x := x.element
  invFun x := ⟨x⟩
  left_inv x := rfl
  right_inv x := rfl
  map_rel_iff' := by aesop

instance : CoeOut (Open X) X where
  coe U := U.getElement

lemma le_def : U ≤ V ↔ U.getElement ≤ V.getElement := ge_iff_le

/--
The nucleus corresponding to an open Sublocale with the Element `U` has the function
`fun x ↦ U ⇨ x`.
-/
def toNucleus (U : Open X) : Nucleus X where
  toFun x := U ⇨ x
  map_inf' _ _ := himp_inf_distrib _ _ _
  idempotent' _ := le_of_eq himp_idem
  le_apply' _ := le_himp

instance : Coe (Open X) (Nucleus X) where
  coe U := U.toNucleus

instance : CompleteLattice (Open X) := getElement.symm.toGaloisInsertion.liftCompleteLattice

instance : Order.Frame (Open X) := .ofMinimalAxioms ⟨fun a s  ↦ by
  simp [Open.le_def, OrderIso.map_inf, OrderIso.map_sSup, OrderIso.map_iSup, inf_iSup_eq]⟩

set_option backward.isDefEq.respectTransparency false in
/--
The map from open sublocales to their corresponding sublocale is a `FrameHom`· It preserves finite
meets and arbitrary joins.
-/
def toSublocale : FrameHom (Open X) (Sublocale X) where
  toFun U := U.toNucleus.toSublocale
  map_sSup' s := by
    simp only [Nucleus.toSublocale, ← image_image, ← map_sSup, EmbeddingLike.apply_eq_iff_eq]
    ext x
    simp only [toNucleus, map_sSup, OrderDual.ofDual_toDual, Nucleus.coe_mk, InfHom.coe_mk,
      ofDual_sSup, Equiv.preimage_image, Nucleus.sInf_apply, mem_image, iInf_exists]
    apply le_antisymm
    · simp only [le_iInf_iff, and_imp, forall_apply_eq_imp_iff₂, Nucleus.coe_mk, InfHom.coe_mk]
      exact fun _ h ↦ himp_le_himp (le_sSup (by simp [h])) (le_refl _)
    · simp [↓iInf_le_iff, inf_sSup_eq]
  map_inf' a b := by
    rw [Nucleus.toSublocale, ← map_inf]
    congr
    ext x
    simp only [OrderDual.ofDual_toDual, ofDual_inf, ← sSup_pair, ← sInf_upperBounds_eq_sSup,
      toNucleus, map_inf, Nucleus.coe_mk, InfHom.coe_mk, upperBounds_insert, Nucleus.sInf_apply,
      mem_inter_iff, mem_Ici]
    apply le_antisymm
    · simp only [upperBounds_singleton, mem_Ici, le_iInf_iff, and_imp]
      intro i h1 h2
      rw [← himp_himp, ← @i.idempotent _ _ x]
      exact le_trans (h1 (getElement b ⇨ x)) (le_trans Nucleus.map_himp_le (h2 (i x)))
    · simp only [← Nucleus.coe_le_coe, Nucleus.coe_mk, InfHom.coe_mk, Pi.le_def,
        upperBounds_singleton, mem_Ici, le_himp_iff, iInf_inf, iInf_le_iff, le_inf_iff, le_iInf_iff,
        and_imp]
      intro _ h
      specialize h (a ⊓ b).toNucleus
      simp only [toNucleus, map_inf, Nucleus.coe_mk, InfHom.coe_mk, le_himp_iff] at h
      refine le_trans' (h.left (fun _ ↦ ?_) ?_) (le_inf (by rfl) (le_inf_iff.mpr h.right))
      · rw [← inf_assoc]
        exact inf_le_of_left_le himp_inf_le
      · rw [inf_comm]
        intro _
        rw [← inf_assoc]
        exact inf_le_of_left_le himp_inf_le
  map_top' := by simpa [Open.toNucleus] using by rfl

end Open

/--
A closed sublocale is defined by an element of the locale.
-/
@[ext]
structure Closed (X : Type*) [Order.Frame X] where
  /-- The element of a closed sublocale.
  Do not use this directly, use `Closed.getElement` instead· -/
  element : X

namespace Closed

instance : PartialOrder (Closed X) where
  le x y := y.element ≤ x.element
  le_refl _ := le_refl _
  le_trans _ _ _ h1 h2 := le_trans h2 h1
  le_antisymm _ _ h1 h2 := by ext; exact le_antisymm h2 h1

variable {C D : Closed X}

/-- The order of the closed sublocales is dual to the order of the underlying frame. -/
def closedIsoDual : (Closed X) ≃o Xᵒᵈ where
  toFun c := OrderDual.toDual c.element
  invFun x := ⟨x.ofDual⟩
  map_rel_iff' := by aesop

/-- The element of a closed sublocale. -/
abbrev getElement (C : Closed X) := C.closedIsoDual.ofDual

lemma le_def : C ≤ D ↔ D.getElement ≤ C.getElement:= by simp [getElement, closedIsoDual]; rfl

instance : CompleteLattice (Closed X) := closedIsoDual.symm.toGaloisInsertion.liftCompleteLattice

instance : Order.Coframe (Closed X) := .ofMinimalAxioms ⟨by
  simp [le_def, OrderIso.map_sup, OrderIso.map_sInf, sup_iInf_eq, OrderIso.map_iInf]⟩

@[simp] lemma top.getElement : (⊤ : Closed X).getElement = ⊥ := rfl

@[simp] lemma bot.getElement : (⊥ : Closed X).getElement = ⊤ := rfl

@[simp] lemma getElement_mk {x : X} : ({element := x} : Closed X).getElement = x := rfl

/-- The nucleus corresponding to a closed sublocale with the element `C` has the function:
  `fun x ↦ x ⊔ C`. -/
def toNucleus (c : Closed X) : Nucleus X where
  toFun x := c.getElement ⊔ x
  map_inf' a b := by
    simpa [getElement, inf_sup_left, inf_sup_right] using le_antisymm (by gcongr; simp) (by simp)
  idempotent' := by simp
  le_apply' := by simp

/-- The map from closed sublocales into sublocales is a `CoframeHom`. It preserves arbitrary meets
  and finite joins. -/
def toSublocale : CoframeHom (Closed X) (Sublocale X) where
  toFun c := c.toNucleus.toSublocale
  map_bot' := by simp [Closed.toNucleus, Sublocale.ext_iff, ←Sublocale.singleton_top_eq_bot]; grind
  map_sup' a b := by
    simp only [Nucleus.toSublocale, ← OrderIso.map_sup, EmbeddingLike.apply_eq_iff_eq]
    change _ = (OrderDual.instSup (Nucleus X)).max _ _  -- Weird why this is needed
    rw [← toDual_inf] -- set option backwards transparency false would also work
    congr
    simp only [toNucleus, getElement, OrderIso.map_sup, Nucleus.ext_iff, Nucleus.coe_mk,
      InfHom.coe_mk, Nucleus.inf_apply]
    change ∀ _, OrderDual.ofDual ((OrderDual.instSup X).max _ _) ⊔ _ = _ -- weird
    rw [ofDual_sup]
    refine fun _ ↦ le_antisymm ?_ (by rw [sup_inf_right])
    · simpa [inf_sup_left] using le_sup_of_le_left (by simp)
  map_sInf' s := by
    simp_rw [Nucleus.toSublocale, ← image_image, sInf_image, ← OrderIso.map_sInf]
    simpa [OrderDual.ext_iff, ofDual_sInf] using le_antisymm
      (by simpa [le_sSup_iff, upperBounds, toNucleus, ← Nucleus.coe_le_coe, Pi.le_def, getElement,
      OrderIso.map_sInf, Nucleus.le_apply] using fun _ h i c hc ↦ h c hc i)
      <| by simpa [toNucleus, getElement, sSup_le_iff, Pi.le_def, le_sup_right, OrderIso.map_sInf,
       ofDual_iInf] using fun _ _ _ ↦ le_sup_of_le_left (by simp [le_iSup_iff]; grind)

/-- The complement of a closed sublocale is the open sublocale with the same element. -/
def compl (c : Closed X) : Open X := ⟨c.getElement⟩

end Closed

namespace Open
open Sublocale

/-- The complement of an open sublocale is the closed sublocale with the same element. -/
def compl (u : Open X) : Closed X := ⟨u.getElement⟩

variable {U V : Open X}

@[simp] lemma compl_compl : U.compl.compl = U := rfl

set_option backward.isDefEq.respectTransparency false in
lemma sup_compl_eq_top : U.toSublocale ⊔ U.compl.toSublocale = ⊤ := by
  rw [eq_top_iff, ← toNucleus_le_toNucleus, Sublocale.toNucleus]
  simp only [toSublocale, toNucleus, FrameHom.coe_mk, InfTopHom.coe_mk, InfHom.coe_mk,
    Closed.toSublocale, Closed.toNucleus, compl, CoframeHom.coe_mk, SupBotHom.coe_mk, SupHom.coe_mk,
    Closed.getElement_mk, map_sup, OrderIso.symm_apply_apply, ofDual_sup, OrderDual.ofDual_toDual,
    Sublocale.toNucleus, map_top, OrderDual.ofDual_top, le_bot_iff]
  ext i
  simp [inf_sup_left]

lemma inf_compl_eq_bot : U.toSublocale ⊓ U.compl.toSublocale = ⊥ := by
  simp only [inf_carrier, inf_eq_inter, ← singleton_top_eq_bot, Sublocale.ext_iff, mem_mk,
    mem_inter_iff, mem_carrier, mem_singleton_iff]
  refine fun _ ↦ ⟨?_, by grind [top_mem]⟩
  · simp only [toSublocale, toNucleus, FrameHom.coe_mk, InfTopHom.coe_mk, InfHom.coe_mk,
    Nucleus.mem_toSublocale, Nucleus.coe_mk, Closed.toSublocale, Closed.toNucleus, compl,
    CoframeHom.coe_mk, SupBotHom.coe_mk, SupHom.coe_mk, Closed.getElement_mk, and_imp,
    forall_exists_index]
    intro _ h1 _ h2
    rw [← h1] at h2
    subst h1
    let h2 := le_himp_iff.mp <| le_of_eq h2
    simp only [le_sup_left, inf_of_le_right] at h2
    exact himp_eq_top_iff.mpr h2

lemma compl_le_compl_iff : U.compl ≤ V.compl ↔ V ≤ U := by rfl

end Open

namespace Closed

variable {C D : Closed X}

@[simp] lemma compl_compl : C.compl.compl = C := rfl

lemma compl_le_compl_iff : C.compl ≤ D.compl ↔ D ≤ C := by rfl

lemma sup_compl_eq_top : C.toSublocale ⊔ C.compl.toSublocale = ⊤ := by
  rw [← @compl_compl _ _ C, sup_comm]
  exact Open.sup_compl_eq_top

lemma inf_compl_eq_bot : C.toSublocale ⊓ C.compl.toSublocale = ⊥ := by
  rw [← @compl_compl _ _ C, inf_comm]
  exact Open.inf_compl_eq_bot

end Closed
