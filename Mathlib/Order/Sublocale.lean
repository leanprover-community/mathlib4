import Mathlib.Order.Nucleus

variable {X : Type*} [Order.Frame X]
open Set

--TODO create separate Defintions for sInfClosed and HImpClosed (also useful for CompleteSublattice)
structure Sublocale (X : Type*) [Order.Frame X] where
  carrier : Set X
  sInfClosed' : ∀ a ⊆ carrier , sInf a ∈ carrier
  HImpClosed' : ∀ a b, b ∈ carrier → a ⇨ b ∈ carrier

namespace Sublocale

variable {S : Sublocale X}

instance : SetLike (Sublocale X) X where
  coe x := x.carrier
  coe_injective' s1 s2 h := by cases s1; congr

lemma sInfClosed {s : Set X} (h : s ⊆ S) : sInf s ∈ S := S.sInfClosed' s h

lemma inf_mem (a b : X) (h1 : a ∈ S) (h2 : b ∈ S) : a ⊓ b ∈ S := by
  rw [← sInf_pair]
  exact S.sInfClosed (pair_subset h1 h2)

instance : InfSet S where
  sInf x := ⟨sInf (Subtype.val '' x), S.sInfClosed (by simp; simp [@subset_def])⟩

instance instCompleteLattice : CompleteLattice S where
  inf x y := ⟨x.val ⊓ y.val, S.inf_mem ↑x ↑y (SetLike.coe_mem x) (SetLike.coe_mem y)⟩
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ h1 h2 := le_inf h1 h2
  __ := completeLatticeOfInf S (by simp_all only [IsGLB, IsGreatest, lowerBounds, Subtype.forall,
    sInf, mem_setOf_eq, Subtype.mk_le_mk, sInf_le_iff, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, forall_exists_index, implies_true, upperBounds, le_sInf_iff, and_self])

lemma coe_inf (a b : S) : (a ⊓ b).val = ↑a ⊓ ↑b :=  rfl

lemma coe_sInf (a : Set S) : (sInf a).val = sInf (Subtype.val '' a) := rfl

instance instHImp : HImp S where
  himp a b := ⟨a ⇨ b, (S.HImpClosed' a b (Subtype.coe_prop b))⟩

lemma coe_himp (a b : S) : a.val ⇨ b.val = (a ⇨ b).val := rfl

instance instHeytingAlgebra : HeytingAlgebra S where
  le_himp_iff a b c := by
    simp [← Subtype.coe_le_coe, ← @Sublocale.coe_inf, himp]
  compl a :=  a ⇨ ⊥
  himp_bot _ := rfl

instance : Order.Frame S where
  __ := instHeytingAlgebra
  __ := instCompleteLattice

private def embeddingAux (S : Sublocale X) (x : X) : S := sInf {s : S | x ≤ s}

private def gcAux (S : Sublocale X) : GaloisConnection S.embeddingAux Subtype.val := by
  intro a b
  apply Iff.intro
  · simp [embeddingAux]
    intro h
    rw [← Subtype.coe_le_coe] at h
    apply le_trans' h
    rw [coe_sInf]
    simp only [le_sInf_iff, mem_image, mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop,
      exists_eq_right_right, and_imp]
    exact fun b a a_1 ↦ a
  · simp [embeddingAux]
    intro h
    apply sInf_le
    simp [h]

lemma coeEmbedding (S : Sublocale X) (x : X) (h : x ∈ S) : embeddingAux S x = x := by
  simp [Sublocale.embeddingAux, sInf]
  apply le_antisymm
  . apply sInf_le
    simp [h]
  . simp_all


lemma test2 (a b: X) : a = b ↔ (∀ c, a ≤ c ↔ b ≤ c) := by
  apply Iff.intro
  . intro h
    subst h
    simp
  . intro h
    apply le_antisymm
    . apply (h b).mpr
      simp
    . apply (h a).mp
      simp


def embedding (S : Sublocale X) : FrameHom X S where
  toFun x := sInf {s : S | x ≤ s}
  map_inf' a b := by
    repeat rw [← embeddingAux]
    rw [test2]
    intro s
    symm
    rw [@iff_eq_eq]
    calc  (S.embeddingAux a ⊓ S.embeddingAux b ≤ s)
      _ = (S.embeddingAux a ≤ S.embeddingAux b ⇨ s) := by simp
      _ = (a ≤ S.embeddingAux b ⇨ s ) := by rw [S.gcAux.le_iff_le]
      _ = (S.embeddingAux b ≤ a ⇨ s ) := by
        rw [@le_himp_comm, coe_himp]

      _ = ( b ≤ a ⇨ s) := by
        sorry
      _ = ( a ⊓ b ≤ s ) := by simp [inf_comm]
      _ = (S.embeddingAux (a ⊓ b) ≤ s) := sorry
  map_sSup' s := by rw [← embeddingAux, S.gcAux.l_sSup, sSup_image]; simp_rw [embeddingAux]
  map_top' := by
    refine le_antisymm (by simp) ?_
    rw [← Subtype.coe_le_coe, ← embeddingAux, S.gcAux.u_top]
    simp [embeddingAux, sInf]


def giEmbedding (S : Sublocale X) : GaloisInsertion S.embedding Subtype.val :=
  GaloisInsertion.monotoneIntro S.gcAux.monotone_u S.gcAux.monotone_l S.gcAux.le_u_l (by
    simp [embedding]
    exact fun a b ↦ le_antisymm (sInf_le (by simp)) (le_sInf (fun _ a ↦ a)))

def toNucleus (S : Sublocale X) : Nucleus X where
  toFun x := S.embedding x
  map_inf' _ _ := by simp [S.giEmbedding.gc.u_inf]
  idempotent' _ := by rw [S.giEmbedding.gc.l_u_l_eq_l]
  le_apply' _ := S.giEmbedding.gc.le_u_l _

end Sublocale
