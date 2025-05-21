/-
Copyright (c) 2025 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.Nucleus

/-!
# Nucleus

Locales are the dual concept to frames. Locale theory is a branch of point-free topology, where
intuitively locales are like topological spaces which may or may not have enough points.
Sublocales of a locale generalize the concept of subspaces in topology to the point-free setting.

## References
https://ncatlab.org/nlab/show/sublocale
https://ncatlab.org/nlab/show/nucleus
-/

variable {X : Type*} [Order.Frame X]
open Set

--TODO create separate Defintions for sInfClosed and HImpClosed (also useful for CompleteSublattice)
/--
A sublocale is a subset S of a locale X, which is closed under all meets and for any
s ∈ S and x ∈ X, we have x ⇨ s ∈ S.
-/
structure Sublocale (X : Type*) [Order.Frame X] where
  carrier : Set X
  sInfClosed' : ∀ a ⊆ carrier , sInf a ∈ carrier
  HImpClosed' : ∀ a b, b ∈ carrier → a ⇨ b ∈ carrier

namespace Sublocale

variable {S : Sublocale X}

instance instSetLike : SetLike (Sublocale X) X where
  coe x := x.carrier
  coe_injective' s1 s2 h := by cases s1; congr

lemma inf_mem (a b : X) (h1 : a ∈ S) (h2 : b ∈ S) : a ⊓ b ∈ S := by
  rw [← sInf_pair]
  exact S.sInfClosed' _ (pair_subset h1 h2)

instance : InfSet S where
  sInf x := ⟨sInf (Subtype.val '' x), S.sInfClosed' _ (by simp; simp [@subset_def])⟩

instance carrier.instCompleteLattice : CompleteLattice S where
  inf x y := ⟨x.val ⊓ y.val, S.inf_mem ↑x ↑y (SetLike.coe_mem x) (SetLike.coe_mem y)⟩
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ h1 h2 := le_inf h1 h2
  -- squeezed simp for performance
  __ := completeLatticeOfInf S <| by simp_all only [IsGLB, IsGreatest, lowerBounds, Subtype.forall,
    sInf, mem_setOf_eq, Subtype.mk_le_mk, sInf_le_iff, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, forall_exists_index, implies_true, upperBounds, le_sInf_iff, and_self]

lemma coe_inf (a b : S) : (a ⊓ b).val = ↑a ⊓ ↑b :=  rfl

lemma coe_sInf (a : Set S) : (sInf a).val = sInf (Subtype.val '' a) := rfl

instance instHImp : HImp S where
  himp a b := ⟨a ⇨ b, (S.HImpClosed' a b (Subtype.coe_prop b))⟩

lemma coe_himp (a b : S) : a.val ⇨ b.val = (a ⇨ b).val := rfl

lemma coe_himp' (a : X) (b : S) : a ⇨ b.val =
    (⟨(a ⇨ b.val), (S.HImpClosed' _ _ b.coe_prop)⟩ : S).val := rfl

instance carrier.instHeytingAlgebra : HeytingAlgebra S where
  le_himp_iff a b c := by simp [← Subtype.coe_le_coe, ← @Sublocale.coe_inf, himp]
  compl a :=  a ⇨ ⊥
  himp_bot _ := rfl

instance carrrier.instFrame : Order.Frame S where
  __ := carrier.instHeytingAlgebra
  __ := carrier.instCompleteLattice

/-- See `Sublocale.embedding` for the public-facing version. -/
private def embeddingAux (S : Sublocale X) (x : X) : S := sInf {s : S | x ≤ s}

/-- See `Sublocale.giEmbedding` for the public-facing version. -/
private def giAux(S : Sublocale X) : GaloisInsertion S.embeddingAux Subtype.val where
  choice x _ := S.embeddingAux x
  gc a b := by
    rw [embeddingAux]
    refine Iff.intro (fun h ↦ ?_) (fun h ↦ sInf_le (by simp [h]))
    · rw [← Subtype.coe_le_coe] at h
      apply le_trans' h
      simpa [coe_sInf] using fun _ a _ ↦ a
  le_l_u x := by simp [embeddingAux]
  choice_eq a h := rfl

/-- The embedding from a locale X into the sublocale S. -/
def embedding (S : Sublocale X) : FrameHom X S where
  toFun x := sInf {s : S | x ≤ s}
  map_inf' a b := by
    repeat rw [← embeddingAux]
    refine eq_of_forall_ge_iff (fun s ↦ Iff.symm (iff_eq_eq.mpr ?_))
    calc
      _ = (S.embeddingAux a ≤ S.embeddingAux b ⇨ s) := by simp
      _ = (S.embeddingAux b ≤ a ⇨ s) := by rw [S.giAux.gc.le_iff_le, @le_himp_comm, coe_himp]
      _ = ( b ≤ a ⇨ s) := by rw [coe_himp', S.giAux.u_le_u_iff, S.giAux.gc.le_iff_le]
      _ = (S.embeddingAux (a ⊓ b) ≤ s) := by simp [inf_comm, S.giAux.gc.le_iff_le]
  map_sSup' s := by rw [← embeddingAux, S.giAux.gc.l_sSup, sSup_image]; simp_rw [embeddingAux]
  map_top' := by
    refine le_antisymm (by simp) ?_
    rw [← Subtype.coe_le_coe, ← embeddingAux, S.giAux.gc.u_top]
    simp [embeddingAux, sInf]

/-- The embedding corresponding to a sublocale forms a Galois insertion with the forgetful map from
 the sublcoale to the original locale. -/
def giEmbedding (S : Sublocale X) : GaloisInsertion S.embedding Subtype.val where
  choice x _ := S.embedding x
  __ := S.giAux

/-- The embedding into a sublocale is a nucleus. -/
def toNucleus (S : Sublocale X) : Nucleus X where
  toFun x := S.embedding x
  map_inf' _ _ := by simp [S.giEmbedding.gc.u_inf]
  idempotent' _ := by rw [S.giEmbedding.gc.l_u_l_eq_l]
  le_apply' _ := S.giEmbedding.gc.le_u_l _

lemma toNucleus.range : range S.toNucleus = S.carrier := by
  ext x
  constructor
  · rw [Sublocale.toNucleus]
    aesop
  · intro hx
    obtain ⟨x', hx'⟩ := S.giAux.l_surjective ⟨x, hx⟩
    simp_all [hx', @Subtype.ext_iff_val]
    exact Exists.intro x' hx'

lemma mem_iff (x : X) : x ∈ S ↔ x ∈ S.carrier := Eq.to_iff rfl

lemma le_iff' (s1 s2 : Sublocale X) : s1 ≤ s2 ↔ s1.carrier ⊆ s2.carrier where
  mp h := h
  mpr h := h

end Sublocale

/-- The range of a nucleus is a sublcoale. -/
def Nucleus.toSublocale (n : Nucleus X) : Sublocale X where
  carrier := range n
  sInfClosed' a h := by
    rw [@mem_range]
    refine le_antisymm (le_sInf_iff.mpr (fun b h1 ↦ ?_)) le_apply
    simp_rw [@subset_def, mem_range] at h
    rw [← h b h1]
    exact n.monotone (sInf_le h1)
  HImpClosed' a b h := by rw [mem_range, ← h, @map_himp_apply] at *

/-- The nuclei on a frame corresponds exactly to the sublocales on this frame.
The subloacles are ordered dually to the nuclei. -/
def orderiso : (Nucleus X)ᵒᵈ ≃o Sublocale X where
  toFun n := n.toSublocale
  invFun s := s.toNucleus
  left_inv n := by
    rw [Nucleus.ext_iff]
    simp only [Sublocale.toNucleus, Nucleus.toSublocale, Sublocale.embedding, FrameHom.coe_mk,
      InfTopHom.coe_mk, InfHom.coe_mk, Sublocale.coe_sInf, Nucleus.coe_mk]
    refine fun a ↦ le_antisymm (sInf_le ?_) ?_
    · simp [Nucleus.le_apply, Sublocale.instSetLike,← @SetLike.mem_coe]
    · simp only [le_sInf_iff, mem_image, mem_setOf_eq, Subtype.exists, Sublocale.mem_iff,
      mem_range, exists_and_left, exists_prop, exists_eq_right_right, and_imp, forall_exists_index]
      intro b h1 c h2
      subst h2
      rw [← @n.idempotent _ _ c]
      exact n.monotone h1
  right_inv S := by
    simp only [Nucleus.toSublocale, Sublocale.toNucleus, Nucleus.coe_mk, InfHom.coe_mk]
    apply le_antisymm <;> simp only [SetLike.le_def, Sublocale.mem_iff, mem_range,
      forall_exists_index, forall_apply_eq_imp_iff, Subtype.coe_prop, implies_true]
    intro x h
    obtain ⟨x', hx'⟩ := S.giAux.l_surjective ⟨x, h⟩
    rw [@Subtype.ext_iff_val] at hx'
    exact Exists.intro x' hx'
  map_rel_iff' := by simpa [Sublocale.le_iff', ← Nucleus.range_subset_iff] using fun _ _ ↦ (by rfl)

lemma orderiso.eq_toSublocale : Nucleus.toSublocale = (@orderiso X _) := rfl
lemma orderiso.symm_eq_toNucleus : Sublocale.toNucleus = (@orderiso X _).symm := rfl

lemma Sublocale.le_iff (s1 s2 : Sublocale X) : s1 ≤ s2 ↔ s2.toNucleus ≤ s1.toNucleus := by
  rw [← orderiso.symm.le_iff_le]
  rfl

instance Sublocale.instCompleteLattice : CompleteLattice (Sublocale X) :=
  orderiso.toGaloisInsertion.liftCompleteLattice

instance Sublocale.instCoframeMinimalAxioms : Order.Coframe.MinimalAxioms (Sublocale X) where
  iInf_sup_le_sup_sInf a s := by simp [Sublocale.le_iff, orderiso.symm_eq_toNucleus,
    orderiso.symm.map_sup, orderiso.symm.map_sInf, orderiso.symm.map_iInf, sup_iInf_eq]

instance Sublocale.instCoframe : Order.Coframe (Sublocale X) :=
  .ofMinimalAxioms instCoframeMinimalAxioms
