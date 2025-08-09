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

@[simp] lemma mem_carrier : a ∈ S.carrier ↔ a ∈ S := .rfl

@[simp] lemma mem_mk (carrier : Set X) (sInf_mem' himp_mem') :
    a ∈ mk carrier sInf_mem' himp_mem' ↔ a ∈ carrier := .rfl

@[simp] lemma mk_le_mk (carrier₁ carrier₂ : Set X) (sInf_mem'₁ sInf_mem'₂ himp_mem'₁ himp_mem'₂) :
    mk carrier₁ sInf_mem'₁ himp_mem'₁ ≤ mk carrier₂ sInf_mem'₂ himp_mem'₂ ↔ carrier₁ ⊆ carrier₂ :=
  .rfl

@[gcongr]
alias ⟨_, _root_.GCongr.Sublocale.mk_le_mk⟩ := mk_le_mk

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
from the sublocale to the original locale. -/
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

@[gcongr]
alias ⟨_, _root_.GCongr.Nucleus.toSublocale_le_toSublocale⟩ := toSublocale_le_toSublocale

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

instance Sublocale.instCompleteLattice : CompleteLattice (Sublocale X) :=
  nucleusIsoSublocale.toGaloisInsertion.liftCompleteLattice

instance Sublocale.instCoframeMinimalAxioms : Order.Coframe.MinimalAxioms (Sublocale X) where
  iInf_sup_le_sup_sInf a s := by simp [← toNucleus_le_toNucleus,
    nucleusIsoSublocale.symm_eq_toNucleus, nucleusIsoSublocale.symm.map_sup,
    nucleusIsoSublocale.symm.map_sInf, sup_iInf_eq, nucleusIsoSublocale.symm.map_iInf]

instance Sublocale.instCoframe : Order.Coframe (Sublocale X) :=
  .ofMinimalAxioms instCoframeMinimalAxioms
