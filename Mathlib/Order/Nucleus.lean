/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.Closure
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Hom.Lattice

/-!
# Nucleus

Locales are the dual concept to frames. Locale theory is a branch of point-free topology, where
intuitively locales are like topological spaces which may or may not have enough points.
Sublocales of a locale generalize the concept of subspaces in topology to the point-free setting.

A nucleus is an endomorphism of a frame which corresponds to a sublocale.

## References
https://ncatlab.org/nlab/show/sublocale
https://ncatlab.org/nlab/show/nucleus
-/

open Order InfHom

variable {X : Type*} [Order.Frame X]

/-- A nucleus is an inflationary idempotent `inf`-preserving endomorphism of a semilattice.
In a frame, nuclei correspond to sublocales. -/ -- TODO: Formalise that claim
structure Nucleus (X : Type*) [SemilatticeInf X] extends InfHom X X where
  /-- A `Nucleus` is idempotent.

  Do not use this directly. Instead use `NucleusClass.idempotent`. -/
  idempotent' (x : X) : toFun (toFun x) ≤ toFun x
  /-- A `Nucleus` is increasing.

  Do not use this directly. Instead use `NucleusClass.le_apply`. -/
  le_apply' (x : X) : x ≤ toFun x

/-- `NucleusClass F X` states that F is a type of nuclei. -/
class NucleusClass (F X : Type*) [SemilatticeInf X] [FunLike F X X] extends InfHomClass F X X :
    Prop where
  /-- A nucleus is idempotent. -/
  idempotent (x : X) (f : F) : f (f x) ≤ f x
  /-- A nucleus is inflationary. -/
  le_apply (x : X) (f : F) : x ≤ f x

namespace Nucleus

variable {n m : Nucleus X} {x y : X}

instance : FunLike (Nucleus X) X X where
  coe x := x.toFun
  coe_injective' f g h := by  obtain ⟨⟨_, _⟩, _⟩ := f; congr!

lemma toFun_eq_coe (n : Nucleus X) : n.toFun = n := rfl
@[simp] lemma coe_toInfHom (n : Nucleus X) : ⇑n.toInfHom = n := rfl
@[simp] lemma coe_mk (f : InfHom X X) (h1 h2) : ⇑(mk f h1 h2) = f := rfl

instance : NucleusClass (Nucleus X) X where
  idempotent _ _ := idempotent' ..
  le_apply _ _ := le_apply' ..
  map_inf _ _ _ := map_inf' ..

/-- Every `Nucleus` is a `ClosureOperator`. -/
def toClosureOperator (n : Nucleus X) : ClosureOperator X :=
   ClosureOperator.mk' n (OrderHomClass.mono n) n.le_apply' n.idempotent'

lemma idempotent : n (n x) = n x :=
  n.toClosureOperator.idempotent x

lemma le_apply : x ≤ n x :=
  n.toClosureOperator.le_closure x

lemma monotone : Monotone n := n.toClosureOperator.monotone

lemma map_inf : n (x ⊓ y) = n x ⊓ n y :=
  InfHomClass.map_inf n x y

@[ext] lemma ext {m n : Nucleus X} (h : ∀ a, m a = n a) : m = n :=
  DFunLike.ext m n h

/-- A `Nucleus` preserves ⊤. -/
instance : TopHomClass (Nucleus X) X X where
  map_top _ := eq_top_iff.mpr le_apply

instance : PartialOrder (Nucleus X) := .lift (⇑) DFunLike.coe_injective

@[simp, norm_cast] lemma coe_le_coe : ⇑m ≤ n ↔ m ≤ n := .rfl
@[simp, norm_cast] lemma coe_lt_coe : ⇑m < n ↔ m < n := .rfl

/-- The smallest `Nucleus` is the identity. -/
instance instBot : Bot (Nucleus X) where
  bot.toFun x := x
  bot.idempotent' := by simp
  bot.le_apply' := by simp
  bot.map_inf' := by simp

/-- The biggest `Nucleus` sends everything to `⊤`. -/
instance instTop : Top (Nucleus X) where
  top.toFun := ⊤
  top.idempotent' := by simp
  top.le_apply' := by simp
  top.map_inf' := by simp

@[simp, norm_cast] lemma coe_bot : ⇑(⊥ : Nucleus X) = id := rfl
@[simp, norm_cast] lemma coe_top : ⇑(⊤ : Nucleus X) = ⊤ := rfl

@[simp] lemma bot_apply (x : X) : (⊥ : Nucleus X) x = x := rfl
@[simp] lemma top_apply (x : X) : (⊤ : Nucleus X) x = ⊤ := rfl

instance : BoundedOrder (Nucleus X) where
  bot_le _ _ := le_apply
  le_top _ _ := by simp

instance : InfSet (Nucleus X) where
  sInf s :=
  { toFun x := ⨅ f ∈ s, f x,
    map_inf' x y := by
      simp only [InfHomClass.map_inf, le_antisymm_iff, le_inf_iff, le_iInf_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rintro f hf
      · exact iInf₂_le_of_le f hf inf_le_left
      · exact iInf₂_le_of_le f hf inf_le_right
      · exact ⟨inf_le_of_left_le <| iInf₂_le f hf, inf_le_of_right_le <| iInf₂_le f hf⟩
    idempotent' x := iInf₂_mono fun f hf ↦ (f.monotone <| iInf₂_le f hf).trans_eq f.idempotent
    le_apply' x := by simp [le_apply] }

@[simp] theorem sInf_apply (s : Set (Nucleus X)) (x : X) : sInf s x = ⨅ j ∈ s, j x := rfl

@[simp] theorem iInf_apply {ι : Type*} (f : ι → (Nucleus X)) (x : X) : iInf f x = ⨅ j, f j x := by
  rw [iInf, sInf_apply, iInf_range]

instance : CompleteSemilatticeInf (Nucleus X) where
  sInf_le := by simp +contextual [← coe_le_coe, Pi.le_def, iInf_le_iff]
  le_sInf := by simp +contextual [← coe_le_coe, Pi.le_def]

instance : CompleteLattice (Nucleus X) := completeLatticeOfCompleteSemilatticeInf (Nucleus X)

def himp_toFun (x y : Nucleus E) (a : E) :=
  ⨅ b ≥ a, x b ⇨ y b

/-
Johnstone:
(i): map_inf
(ii): le_apply
(iii): idempotent
-/
def himp_idempotent (x y : Nucleus E) (a : E) :
    himp_toFun x y (himp_toFun x y a) ≤  himp_toFun x y a := by
  have h_0 : ∀ a, ∀ b ≥ a, himp_toFun x y a ≤ x b ⇨ y b := by
    simp [himp_toFun]
    intro a b h
    rw [iInf_inf]
    rw [iInf_le_iff]
    simp only [le_inf_iff, le_iInf_iff, le_himp_iff]
    intro c h1
    rcases h1 b with ⟨h1, h2⟩
    let h1 := h1 h
    apply le_trans' h1
    simp only [le_inf_iff, le_refl, true_and]
    exact h2

  have h : ∀ b ≥ a, (x (x b ⇨ y b)) ⇨ (y (x b ⇨ y b)) = x b ⇨ y b := by
    intro b h
    have h_fixpoint : y (x b ⇨ y b) = x b ⇨ y b := by
      apply le_antisymm
      .
        simp
        rw [himp_eq_sSup]
        have h : y (sSup {w | w ⊓ x b ≤ y b}) ⊓ x b ≤ y (sSup {w | w ⊓ x b ≤ y b}) ⊓ y (x b) := by
          simp
          apply inf_le_of_right_le
          exact Nucleus.le_apply
        apply le_trans h
        rw [← y.map_inf]
        rw [sSup_inf_eq]
        conv =>
          enter [2]
          rw [← y.idempotent]
        apply OrderHomClass.mono
        simp only [Set.mem_setOf_eq, iSup_le_iff]
        exact fun i i => i
      . exact Nucleus.le_apply

    rw [h_fixpoint]
    rw [himp_himp]

    rw [← x.map_inf]
    have h2 : b ≤ x b ⇨ y b := by
      apply le_trans y.le_apply
      simp only [le_himp_iff, inf_le_left]
    rw [inf_of_le_right h2]

  have h1 : himp_toFun x y a = ⨅ b ≥ a, x b ⇨ y b  := by
    simp [himp_toFun]
  conv =>
    enter [2]
    rw [h1]
  conv =>
    enter [2, 1, b, 1]
    intro h1
    rw [← h b h1]
  exact le_iInf₂ fun i j => h_0 (himp_toFun x y a) (x i ⇨ y i) (h_0 a i j)


def himp_le_apply (x y : Nucleus E) (a : E) :
    a ≤ himp_toFun x y a := by
  simp [himp_toFun]
  intro i hi
  refine inf_le_of_left_le ?_
  apply le_trans hi y.le_apply

lemma himp_map_inf (x y : Nucleus E) :
    ∀ (a b : E), himp_toFun x y (a ⊓ b) = himp_toFun x y a ⊓ himp_toFun x y b := by
  intro a b
  apply le_antisymm
  . simp [himp_toFun]
    apply And.intro
    . intro i hi
      rw [iInf_inf]
      rw [iInf_le_iff]
      simp only [le_inf_iff, le_iInf_iff, le_himp_iff]
      intro c h1
      rcases (h1 i) with ⟨h1, h2⟩
      let h1 := h1 (by exact inf_le_of_left_le hi)
      apply le_trans' h1
      rw [inf_of_le_left]
      exact h2
    . intro i hi
      rw [iInf_inf]
      rw [iInf_le_iff]
      simp only [le_inf_iff, le_iInf_iff, le_himp_iff]
      intro c h1
      rcases (h1 i) with ⟨h1, h2⟩
      let h1 := h1 (by exact inf_le_of_right_le hi)
      apply le_trans' h1
      rw [inf_of_le_left]
      exact h2

  . have h : ∀ c ≥ a ⊓ b, c = (a ⊔ c) ⊓ (b ⊔ c) := by
      intro c h
      rw [@inf_sup_left]
      simp only [le_sup_right, inf_of_le_right, right_eq_sup]
      simp at h
      rw [inf_sup_right]
      simp only [sup_le_iff, inf_le_left, and_true]
      exact h
    simp only [himp_toFun]
    conv =>
      enter [2, 1, c, 1]
      intro h1
      rw [h c h1]
      rw [y.map_inf]
      rw [himp_inf_distrib]
      simp

    rw [@le_iInf₂_iff]
    intro i hi
    rw [le_inf_iff]
    apply And.intro
    . apply inf_le_of_left_le
      simp only [ge_iff_le, le_inf_iff]
      . rw [iInf_le_iff]
        have h : x (a ⊔ i) ⇨ y (a ⊔ i) ≤ (x (a ⊔ i) ⊓ x (b ⊔ i)) ⇨ y (a ⊔ i) := by
          simp only [le_himp_iff]
          rw [himp_eq_sSup]
          rw [sSup_inf_eq]
          simp only [Set.mem_setOf_eq, iSup_le_iff]
          intro j h1
          apply le_trans' h1
          simp only [le_inf_iff, inf_le_left, true_and]
          apply inf_le_of_right_le
          exact inf_le_left

        intro c h1
        apply le_trans' h
        simp at h1
        simp
        apply h1
        exact le_sup_left
    . apply inf_le_of_right_le
      simp only [ge_iff_le, le_inf_iff]
      . rw [iInf_le_iff]
        have h : x (b ⊔ i) ⇨ y (b ⊔ i) ≤ (x (a ⊔ i) ⊓ x (b ⊔ i)) ⇨ y (b ⊔ i) := by
          simp only [le_himp_iff]
          rw [himp_eq_sSup]
          rw [sSup_inf_eq]
          simp only [Set.mem_setOf_eq, iSup_le_iff]
          intro j h1
          apply le_trans' h1
          simp only [le_inf_iff, inf_le_left, true_and]
          apply inf_le_of_right_le
          exact inf_le_right

        intro c h1
        apply le_trans' h
        simp at h1
        simp
        apply h1
        exact le_sup_left

instance : HImp (Nucleus X) where
  himp a b :=
  { toFun x :=   ⨅ y ≥ x, a y ⇨ b y
    idempotent' := sorry
    map_inf' c d := by



      /--/
      apply le_antisymm
      . simp [iInf_inf, iInf_le_iff]




        apply And.intro
        . intro i hi
          rw [iInf_inf]
          rw [iInf_le_iff]
          simp only [le_inf_iff, le_iInf_iff, le_himp_iff]
          intro c h1
          rcases (h1 i) with ⟨h1, h2⟩
          let h1 := h1 (by exact inf_le_of_left_le hi)
          apply le_trans' h1
          rw [inf_of_le_left]
          exact h2
        . intro i hi
          rw [iInf_inf]
          rw [iInf_le_iff]
          simp only [le_inf_iff, le_iInf_iff, le_himp_iff]
          intro c h1
          rcases (h1 i) with ⟨h1, h2⟩
          let h1 := h1 (by exact inf_le_of_right_le hi)
          apply le_trans' h1
          rw [inf_of_le_left]
          exact h2

      . have h : ∀ c ≥ a ⊓ b, c = (a ⊔ c) ⊓ (b ⊔ c) := by
          intro c h
          rw [@inf_sup_left]
          simp only [le_sup_right, inf_of_le_right, right_eq_sup]
          simp at h
          rw [inf_sup_right]
          simp only [sup_le_iff, inf_le_left, and_true]
          exact h
        simp only [himp_toFun]
        conv =>
          enter [2, 1, c, 1]
          intro h1
          rw [h c h1]
          rw [y.map_inf]
          rw [himp_inf_distrib]
          simp

        rw [@le_iInf₂_iff]
        intro i hi
        rw [le_inf_iff]
        apply And.intro
        . apply inf_le_of_left_le
          simp only [ge_iff_le, le_inf_iff]
          . rw [iInf_le_iff]
            have h : x (a ⊔ i) ⇨ y (a ⊔ i) ≤ (x (a ⊔ i) ⊓ x (b ⊔ i)) ⇨ y (a ⊔ i) := by
              simp only [le_himp_iff]
              rw [himp_eq_sSup]
              rw [sSup_inf_eq]
              simp only [Set.mem_setOf_eq, iSup_le_iff]
              intro j h1
              apply le_trans' h1
              simp only [le_inf_iff, inf_le_left, true_and]
              apply inf_le_of_right_le
              exact inf_le_left

            intro c h1
            apply le_trans' h
            simp at h1
            simp
            apply h1
            exact le_sup_left
        . apply inf_le_of_right_le
          simp only [ge_iff_le, le_inf_iff]
          . rw [iInf_le_iff]
            have h : x (b ⊔ i) ⇨ y (b ⊔ i) ≤ (x (a ⊔ i) ⊓ x (b ⊔ i)) ⇨ y (b ⊔ i) := by
              simp only [le_himp_iff]
              rw [himp_eq_sSup]
              rw [sSup_inf_eq]
              simp only [Set.mem_setOf_eq, iSup_le_iff]
              intro j h1
              apply le_trans' h1
              simp only [le_inf_iff, inf_le_left, true_and]
              apply inf_le_of_right_le
              exact inf_le_right

            intro c h1
            apply le_trans' h
            simp at h1
            simp
            apply h1
            exact le_sup_left
    le_apply' := sorry

  }

end Nucleus
