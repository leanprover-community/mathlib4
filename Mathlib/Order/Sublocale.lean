/-
Copyright (c) 2025 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.Nucleus
import Mathlib.Order.SupClosed

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

variable {X : Type*} [Order.Frame X]
open Set

/--
A sublocale is a subset S of a locale X, which is closed under all meets and for any
s ∈ S and x ∈ X, we have x ⇨ s ∈ S [picado2012].
-/
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

@[simp] lemma mem_carrier : a ∈ S.carrier ↔ a ∈ S := .rfl

@[simp] lemma mem_mk (carrier : Set X) (sInf_mem' himp_mem') :
    a ∈ mk carrier sInf_mem' himp_mem' ↔ a ∈ carrier := .rfl

@[simp] lemma mk_le_mk (carrier₁ carrier₂ : Set X) (sInf_mem'₁ sInf_mem'₂ himp_mem'₁ himp_mem'₂) :
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
  compl a :=  a ⇨ ⊥
  himp_bot _ := rfl

instance carrier.instFrame : Order.Frame S where
  __ := carrier.instHeytingAlgebra
  __ := carrier.instCompleteLattice

/-- See `Sublocale.restrict` for the public-facing version. -/
private def restrictAux (S : Sublocale X) (a : X) : S := sInf {s : S | a ≤ s}

private lemma le_restrictAux : a ≤ S.restrictAux a := by simp +contextual [restrictAux]

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

/-- The restriction corresponding to a sublocale forms a Galois insertion with the forgetful map
from the sublcoale to the original locale. -/
def giRestrict (S : Sublocale X) : GaloisInsertion S.restrict Subtype.val := S.giAux

@[simp] lemma restrict_of_mem (ha : a ∈ S) : S.restrict a = ⟨a, ha⟩ := S.giRestrict.l_u_eq ⟨a, ha⟩

/-- The restriction from the locale X into a sublocale is a nucleus. -/
@[simps]
def toNucleus (S : Sublocale X) : Nucleus X where
  toFun x := S.restrict x
  map_inf' _ _ := by simp [S.giRestrict.gc.u_inf]
  idempotent' _ := by rw [S.giRestrict.gc.l_u_l_eq_l]
  le_apply' _ := S.giRestrict.gc.le_u_l _

@[simp] lemma range_toNucleus : range S.toNucleus = S := by
  ext x
  constructor
  · simp +contextual [eq_comm]
  · intro hx
    exact ⟨x, by simp_all⟩

@[simp] lemma toNucleus_le_toNucleus : S.toNucleus ≤ T.toNucleus ↔ T ≤ S := by
  simp [← Nucleus.range_subset_range]

end Sublocale

namespace Nucleus

/-- The range of a nucleus is a sublocale. -/
@[simps]
def toSublocale (n : Nucleus X) : Sublocale X where
  carrier := range n
  sInf_mem' a h := by
    rw [mem_range]
    refine le_antisymm (le_sInf_iff.mpr (fun b h1 ↦ ?_)) le_apply
    simp_rw [subset_def, mem_range] at h
    rw [← h b h1]
    exact n.monotone (sInf_le h1)
  himp_mem' a b h := by rw [mem_range, ← h, map_himp_apply] at *

@[simp]
lemma mem_toSublocale {n : Nucleus X} {x : X} : x ∈ n.toSublocale ↔ ∃ y, n y = x := .rfl

@[simp] lemma toSublocale_le_toSublocale {m n : Nucleus X} :
    m.toSublocale ≤ n.toSublocale ↔ n ≤ m := by simp [← SetLike.coe_subset_coe]

@[simp] lemma restrict_toSublocale (n : Nucleus X) (x : X) :
    n.toSublocale.restrict x = ⟨n x, x, rfl⟩ := by
  ext
  simpa [Sublocale.restrict, sInf_image, le_antisymm_iff (a := iInf _)] using
    ⟨iInf₂_le_of_le ⟨n x, x, rfl⟩ n.le_apply le_rfl, fun y hxy ↦ by simpa using n.monotone hxy⟩

end Nucleus

/-- The nuclei on a frame corresponds exactly to the sublocales on this frame.
The sublocales are ordered dually to the nuclei. -/
def nucleusIsoSublocale : (Nucleus X)ᵒᵈ ≃o Sublocale X where
  toFun n := n.ofDual.toSublocale
  invFun s := .toDual s.toNucleus
  left_inv := by simp [Function.LeftInverse, Nucleus.ext_iff]
  right_inv S := by ext x; simpa using ⟨by simp +contextual [eq_comm], fun hx ↦ ⟨x, by simp [hx]⟩⟩
  map_rel_iff' := by simp

lemma nucleusIsoSublocale.eq_toSublocale : Nucleus.toSublocale = @nucleusIsoSublocale X _ := rfl
lemma nucleusIsoSublocale.symm_eq_toNucleus :
  Sublocale.toNucleus = (@nucleusIsoSublocale X _).symm := rfl

namespace Sublocale

instance instCompleteLattice : CompleteLattice (Sublocale X) :=
  nucleusIsoSublocale.toGaloisInsertion.liftCompleteLattice

instance instCoframeMinimalAxioms : Order.Coframe.MinimalAxioms (Sublocale X) where
  iInf_sup_le_sup_sInf a s := by simp [← toNucleus_le_toNucleus,
    nucleusIsoSublocale.symm_eq_toNucleus, nucleusIsoSublocale.symm.map_sup,
    nucleusIsoSublocale.symm.map_sInf, sup_iInf_eq, nucleusIsoSublocale.symm.map_iInf]

instance instCoframe : Order.Coframe (Sublocale X) :=
  .ofMinimalAxioms instCoframeMinimalAxioms

lemma univ_eq_top : (⟨univ, fun _ _ ↦ trivial, fun _ _ a ↦ a⟩ : Sublocale X) = ⊤ :=
  le_antisymm le_top (fun _ _ ↦ trivial)

lemma singleton_top_eq_bot : (⟨{⊤}, by simp, by simp⟩ : Sublocale X) = ⊥ :=
  le_antisymm (fun i h ↦ by simp_all [top_mem]) bot_le

/--
An open sublocale is defined by an element of the locale.
-/
@[ext]
structure Open (X : Type*) [Order.Frame X] where
  /-- The element of an open sublocale. Do not use this directly, use `Open.get_element` instead. -/
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
def get_element : Open X ≃o X where
  toFun x := x.element
  invFun x := ⟨x⟩
  left_inv x := rfl
  right_inv x := rfl
  map_rel_iff' := by aesop

instance : Coe (Open X) X where
  coe U := U.get_element

lemma le_def : U ≤ V ↔ U.get_element ≤ V.get_element := ge_iff_le

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

instance : CompleteLattice (Open X) := get_element.symm.toGaloisInsertion.liftCompleteLattice

instance : Order.Frame (Open X) := .ofMinimalAxioms ⟨fun a s ↦ by
  simp_rw [Open.le_def]; simp [inf_sSup_eq, le_iSup_iff]⟩

/--
The map from open sublocales to their corresponding sublocale is a `FrameHom`. It preserves finite
meets and arbitrary joins.
-/
def toSublocale : FrameHom (Open X) (Sublocale X) where
  toFun U := U.toNucleus.toSublocale
  map_sSup' s := by
    simp_rw [← Set.image_image]
    change _ = sSup (⇑nucleusIsoSublocale '' (toNucleus '' s))
    rw [← map_sSup]
    congr
    ext x
    change _ = (sInf (toNucleus '' s)) x
    simp only [toNucleus, map_sSup, Nucleus.coe_mk, InfHom.coe_mk, ofDual_sSup, Nucleus.sInf_apply,
      mem_preimage, mem_image, iInf_exists]
    apply le_antisymm
    · simp only [le_iInf_iff, and_imp, forall_apply_eq_imp_iff₂, Nucleus.coe_mk, InfHom.coe_mk]
      exact fun _ h ↦ himp_le_himp (le_sSup (by simp [h])) (le_refl _)
    · simp only [iInf_le_iff, le_iInf_iff, and_imp, forall_apply_eq_imp_iff₂, Nucleus.coe_mk,
      InfHom.coe_mk]
      intro b h
      simpa [inf_sSup_eq] using fun a h1 ↦ h a h1
  map_inf' a b := by
    change nucleusIsoSublocale _ = nucleusIsoSublocale _ ⊓ nucleusIsoSublocale _
    rw [← map_inf]
    congr
    ext x
    simp only [map_inf, mem_setOf_eq]
    apply le_antisymm
    · simp only [← Nucleus.coe_le_coe, Nucleus.coe_mk, InfHom.coe_mk, Pi.le_def, le_iInf_iff,
      and_imp]
      intro i h1 h2
      rw [← himp_himp, ← @i.idempotent _ _ x]
      exact le_trans (h1 (get_element b ⇨ x)) (le_trans Nucleus.map_himp_le (h2 (i x)))
    · simp only [← Nucleus.coe_le_coe, Nucleus.coe_mk, InfHom.coe_mk, Pi.le_def, le_himp_iff,
      iInf_inf, iInf_le_iff, le_inf_iff, le_iInf_iff, and_imp]
      intro y h1
      let h2 := h1 (a ⊓ b).toNucleus
      simp only [toNucleus, map_inf, Nucleus.coe_mk, InfHom.coe_mk, le_himp_iff] at h2
      rcases h2 with ⟨h2, h3⟩
      refine le_trans' (h2 ?_ ?_) (le_inf (by rfl) (le_inf_iff.mpr h3))
      · intro i
        rw [← inf_assoc]
        exact inf_le_of_left_le himp_inf_le
      · rw [inf_comm]
        intro i
        rw [← inf_assoc]
        exact inf_le_of_left_le himp_inf_le
  map_top' := by simp [Nucleus.toSublocale, Open.toNucleus, ← Sublocale.univ_eq_top]

end Open
end Sublocale
