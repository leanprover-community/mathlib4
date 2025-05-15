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

instance instSetLike : SetLike (Sublocale X) X where
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

private def giAux(S : Sublocale X) : GaloisInsertion S.embeddingAux Subtype.val :=
    GaloisInsertion.monotoneIntro S.gcAux.monotone_u S.gcAux.monotone_l S.gcAux.le_u_l (by
    simp [embeddingAux]
    exact fun a b ↦ le_antisymm (sInf_le (by simp)) (le_sInf (fun _ a ↦ a)))

def embedding (S : Sublocale X) : FrameHom X S where
  toFun x := sInf {s : S | x ≤ s}
  map_inf' a b := by
    repeat rw [← embeddingAux]
    refine eq_of_forall_ge_iff (fun s ↦ Iff.symm (iff_eq_eq.mpr ?_))
    calc
      _ = (S.embeddingAux a ≤ S.embeddingAux b ⇨ s) := by simp
      _ = (S.embeddingAux b ≤ a ⇨ s) := by rw [S.gcAux.le_iff_le, @le_himp_comm, coe_himp]
      _ = ( b ≤ a ⇨ s) := by rw [coe_himp', S.giAux.u_le_u_iff, S.gcAux.le_iff_le]
      _ = (S.embeddingAux (a ⊓ b) ≤ s) := by simp [inf_comm, S.gcAux.le_iff_le]
  map_sSup' s := by rw [← embeddingAux, S.gcAux.l_sSup, sSup_image]; simp_rw [embeddingAux]
  map_top' := by
    refine le_antisymm (by simp) ?_
    rw [← Subtype.coe_le_coe, ← embeddingAux, S.gcAux.u_top]
    simp [embeddingAux, sInf]

def giEmbedding (S : Sublocale X) : GaloisInsertion S.embedding Subtype.val := giAux S

def toNucleus (S : Sublocale X) : Nucleus X where
  toFun x := S.embedding x
  map_inf' _ _ := by simp [S.giEmbedding.gc.u_inf]
  idempotent' _ := by rw [S.giEmbedding.gc.l_u_l_eq_l]
  le_apply' _ := S.giEmbedding.gc.le_u_l _

lemma toNucleus.range : range S.toNucleus = S.carrier := by
  simp [Sublocale.toNucleus]
  ext x
  apply Iff.intro
  . simp
    intro x h
    rw [← h]
    simp
  . simp
    intro hx
    obtain ⟨x', hx'⟩ := S.giAux.l_surjective ⟨x, hx⟩
    simp [@Subtype.ext_iff_val] at hx'
    use x'
    exact hx'

lemma mem_iff (x : X) : x ∈ S ↔ x ∈ S.carrier := by exact Eq.to_iff rfl

lemma le_iff' (s1 s2 : Sublocale X) : s1 ≤ s2 ↔ s1.carrier ⊆ s2.carrier where
  mp h := h
  mpr h := h

end Sublocale

def Nucleus.toSublocale (n : Nucleus X) : Sublocale X where
  carrier := range n
  sInfClosed' a h := by
    rw [@mem_range]
    refine le_antisymm ?_ le_apply
    simp only [le_sInf_iff]
    intro b h1
    rw [@subset_def] at h
    simp_rw [mem_range] at h
    rw [← h b h1]
    apply n.monotone
    exact sInf_le h1
  HImpClosed' a b h := by rw [mem_range, ← h, @map_himp_apply] at *

def orderiso : (Nucleus X)ᵒᵈ ≃o Sublocale X where
  toFun n := n.toSublocale
  invFun s := s.toNucleus
  left_inv n := by
    rw [Nucleus.ext_iff]
    intro a
    simp [Nucleus.toSublocale, Sublocale.toNucleus, Sublocale.embedding, Sublocale.coe_sInf]
    apply le_antisymm
    . apply sInf_le
      simp only [mem_image, mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right]
      apply And.intro
      . exact Nucleus.le_apply
      . simp [Sublocale.instSetLike,← @SetLike.mem_coe, mem_range, exists_apply_eq_apply]
    . simp [Sublocale.mem_iff]
      intro b h1 c h2
      subst h2
      rw [← @n.idempotent _ _ c]
      exact n.monotone h1
  right_inv S := by
    simp [Nucleus.toSublocale, Sublocale.toNucleus]
    apply le_antisymm
    . simp [SetLike.le_def, Sublocale.mem_iff]
    . simp [SetLike.le_def, Sublocale.mem_iff]
      intro x h
      obtain ⟨x', hx'⟩ := S.giAux.l_surjective ⟨x, h⟩
      simp [@Subtype.ext_iff_val] at hx'
      use x'
      exact hx'
  map_rel_iff' := by
    simp
    intro a b
    apply Iff.intro
    . intro h
      rw [Sublocale.le_iff'] at h
      rw [← @Nucleus.range_subset_iff]
      exact h
    . intro h
      rw [← Nucleus.range_subset_iff] at h
      rw [Sublocale.le_iff']
      apply h

#check orderiso.injective
instance : Order.Coframe (Nucleus X)ᵒᵈ := OrderDual.instCoframe

instance : Order.Coframe (Sublocale X) where
  __ := orderiso.injective

lemma Sublocale.le_iff (s1 s2 : Sublocale X) : s1 ≤ s2 ↔ s2.toNucleus ≤ s1.toNucleus := by
  apply Iff.intro
  . intro h
    rw [← @Nucleus.range_subset_iff]
    rw [Sublocale.le_iff'] at h
    repeat rw [Sublocale.toNucleus.range]
    exact h
  . intro h
    rw [← @Nucleus.range_subset_iff] at h
    rw [Sublocale.le_iff']
    repeat rw [Sublocale.toNucleus.range] at h
    exact h

@[ext]
structure Open (X : Type*) [Order.Frame X] where
  element : X

instance : Coe (Open X) X where
  coe U := U.element

namespace Open

def toNucleus (U : Open X) : Nucleus X where
  toFun x := U ⇨ x
  map_inf' _ _ := himp_inf_distrib _ _ _
  idempotent' _ := le_of_eq himp_idem
  le_apply' _ := le_himp

instance : Coe (Open X) (Nucleus X) where
  coe U := U.toNucleus

def toSublocale (U : Open X) : Sublocale X := U.toNucleus.toSublocale

instance : Coe (Open X) (Sublocale X) where
  coe U := U.toSublocale

instance : PartialOrder (Open X) where
  le x y := x.element ≤ y.element
  le_refl _ := le_refl _
  le_trans _ _ _ h1 h2 := le_trans h1 h2
  le_antisymm _ _ h1 h2 := Open.ext_iff.mpr (le_antisymm h1 h2)

variable {U V : Open X}

lemma le_def : U ≤ V ↔ U.element ≤ V.element := ge_iff_le

instance : BoundedOrder (Open X) where
  top := ⟨⊤⟩
  le_top _ := le_def.mpr le_top
  bot := ⟨⊥⟩
  bot_le _ := le_def.mpr bot_le

instance : CompleteSemilatticeSup (Open X) where
  sSup s := ⟨sSup s⟩

end Open
