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

lemma test (s_1 : Set ↥S) : IsGLB s_1 (sInf s_1) := by
  simp only [IsGLB, IsGreatest, lowerBounds, Subtype.forall, sInf, mem_setOf_eq, Subtype.mk_le_mk,
    upperBounds, le_sInf_iff, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
    forall_exists_index, imp_self, implies_true, and_true]
  intro a b c
  apply sInf_le
  simp_all only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const]

instance instCompleteLattice : CompleteLattice S where
  inf x y := ⟨x.val ⊓ y.val, s.inf_mem ↑x ↑y (SetLike.coe_mem x) (SetLike.coe_mem y)⟩
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ h1 h2 := le_inf h1 h2
  __ := completeLatticeOfInf s (test)

lemma coe_inf (a b : s) : (a ⊓ b).val = ↑a ⊓ ↑b :=  rfl

lemma coe_sInf (a : Set s) : (sInf a).val = sInf (Subtype.val '' a) := rfl

instance : HImp s where
  himp a b := ⟨a ⇨ b, (s.HimpClosed' a b (Subtype.coe_prop b))⟩

instance instHeytingAlgebra : HeytingAlgebra s where
  le_himp_iff a b c := by
    simp [← Subtype.coe_le_coe, ← @Sublocale.coe_inf, himp]
  compl a :=  a ⇨ ⊥
  himp_bot _ := rfl

instance : Order.Frame s where
  __ := instHeytingAlgebra
  __ := instCompleteLattice

def embedding (S : Sublocale X) (x : X) : S := sInf {s : S | x ≤ s}

def gc (S : Sublocale X) : GaloisConnection S.embedding Subtype.val := by
  intro a b
  apply Iff.intro
  · simp [embedding]
    intro h
    rw [← Subtype.coe_le_coe] at h
    apply le_trans' h
    rw [coe_sInf]
    simp only [le_sInf_iff, mem_image, mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop,
      exists_eq_right_right, and_imp]
    exact fun b a a_1 ↦ a
  · simp [embedding]
    intro h
    apply sInf_le
    simp [h]


lemma embedding.le_apply (S : Sublocale X) {x : X} : x ≤ S.embedding x := S.gc.le_u_l _

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

def embedding_frameHom (S : Sublocale X) : FrameHom X S where
  toFun x := S.embedding x
  map_inf' a b := by
    apply le_antisymm
    . simp only [le_inf_iff]
      apply And.intro
      . apply S.gc.monotone_l
        simp
      . apply S.gc.monotone_l
        simp
    .
      apply le_himp_iff.mp
      sorry
  map_sSup' s := by rw [S.gc.l_sSup, sSup_image]
  map_top' := by
    apply le_antisymm
    . simp
    . rw [← Subtype.coe_le_coe, S.gc.u_top]
      exact embedding.le_apply S

def gi (S : Sublocale X) : GaloisInsertion S.embedding_frameHom Subtype.val where



def toNucleus (S : Sublocale X) : Nucleus X where
  toFun x := S.embedding_frameHom x
  map_inf' a b := by simp [S.gc.u_inf]
  idempotent' a := by
    rw [S.gc.l_u_l]




/-
/-

    rw [test2]
    intro s
    symm
    rw [@iff_eq_eq]
    calc  (S.embedding a ⊓ S.embedding b ≤ s)
      _ = (S.embedding a ≤ S.embedding b ⇨ s) := by simp
      _ = (a ≤ S.embedding b ⇨ s ) := by
        rw [← Subtype.coe_le_coe]
        simp only [Subtype.coe_le_coe, le_himp_iff, eq_iff_iff]

      _ = (S.embedding b ≤ a ⇨ s ) := by sorry
      _ = ( b ≤ a ⇨ s) := by sorry
      _ = ( a ⊓ b ≤ s ) := by sorry
      _ = (S.embedding (a ⊓ b) ≤ s) := by sorry

    have h1 (s : S) : S.embedding a ⊓ S.embedding b ≤ s ↔ S.embedding a ≤ S.embedding b ⇨ s := by
      simp

    have h2 (s : S) : S.embedding a ≤ S.embedding b ⇨ s ↔ a ≤ S.embedding b ⇨ s := by
      sorry

    have h3 (s : S) :  a ≤ S.embedding b ⇨ s ↔ S.embedding b ≤ a ⇨ s := by sorry

    have h4 (s : S) : S.embedding b ≤ a ⇨ s ↔ b ≤ a ⇨ s := by sorry

    have h5 (s : S) : b ≤ a ⇨ s  ↔ a ⊓ b ≤ s  := by sorry

    have h6 (s : S) :  a ⊓ b ≤ s  ↔ S.embedding (a ⊓ b) ≤ s := by sorry




def toNucleus (S : Sublocale X) : Nucleus X where
  toFun x := S.embedding x



end Sublocale
-/-/
