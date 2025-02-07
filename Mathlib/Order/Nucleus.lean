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

section

variable {X : Type*} [CompleteLattice X]

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

end

namespace Nucleus

section

variable {X : Type*} [CompleteLattice X] {n m : Nucleus X} {x y : X}

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

@[simp] theorem inf_aply (m n : Nucleus X) (x : X) : (m ⊓ n) x = m x ⊓ n x := by
  rw [← sInf_pair, sInf_apply, iInf_pair]

end
section

variable {X : Type*} [Order.Frame X]

instance : HImp (Nucleus X) where
  himp m n :=
  { toFun x := ⨅ y ≥ x, m y ⇨ n y
    idempotent' i := by
      apply le_iInf₂
      intro j hj
      have h : (m (m j ⇨ n j)) ⇨ (n (m j ⇨ n j)) = m j ⇨ n j := by
        have h_fix : n (m j ⇨ n j) = m j ⇨ n j := by
          refine le_antisymm ?_ le_apply
          rw [le_himp_iff, himp_eq_sSup]
          have h1 : n (sSup {w | w ⊓ m j ≤ n j}) ⊓ m j ≤
              n (sSup {w | w ⊓ m j ≤ n j}) ⊓  n (m j) := by
            simp only [le_inf_iff, inf_le_left, true_and]
            exact inf_le_of_right_le le_apply
          apply le_trans h1
          rw [← map_inf, sSup_inf_eq, ← @idempotent _ _ n j]
          gcongr
          apply iSup₂_le
          simp [idempotent]
        rw [h_fix, himp_himp, ← map_inf, inf_of_le_right (le_trans n.le_apply le_himp)]
      rw [← h]
      refine iInf₂_le (m j ⇨ n j) ?_
      simp only [ge_iff_le, le_himp_iff, iInf_inf, iInf_le_iff, le_inf_iff, le_iInf_iff]
      intro b1 h2
      rcases h2 j with ⟨h3, h4⟩
      exact le_trans (by simp[h4]) (h3 (by exact hj))
    map_inf' i j := by
      apply le_antisymm
      · simp only [ge_iff_le, iInf_inf, le_iInf_iff, le_inf_iff, le_himp_iff, iInf_le_iff]
        refine fun k ↦ ⟨fun h1 f h2 ↦ ?_, fun k h1 f h2 ↦ ?_⟩
        all_goals rcases h2 k with ⟨h2_1, h2_2⟩;
        all_goals refine le_trans (inf_of_le_left h2_2).ge (h2_1 ?_)
        · exact inf_le_of_left_le h1
        · exact inf_le_of_right_le h1
      · simp only [ge_iff_le, iInf_inf, le_iInf_iff, le_himp_iff, iInf_le_iff, le_inf_iff]
        intro k h2 l h3
        have h8 : k = (i ⊔ k) ⊓ (j ⊔ k) := by simp [inf_sup_left, inf_sup_right, h2]
        rw [h8, map_inf, le_inf_iff]
        rcases h3 (i ⊔ k) with ⟨⟨h4, h5⟩, h7⟩
        apply And.intro
        · apply le_trans' (h4 le_sup_left)
          simp only [le_inf_iff, le_refl, true_and]
          exact Preorder.le_trans _ _ _ h7 (by gcongr; simp)
        · apply le_trans' (h5 (j ⊔ k) le_sup_left)
          simp only [le_inf_iff, le_refl, true_and]
          exact Preorder.le_trans _ _ _ h7 (by gcongr; simp)
    le_apply' := by
      simp only [ge_iff_le, le_iInf_iff, le_himp_iff]
      refine fun _ _ h ↦ inf_le_of_left_le (le_trans h n.le_apply)}

@[simp] theorem himp_apply (m n : Nucleus X) (x : X) : (m ⇨ n) x = ⨅ y ≥ x, m y ⇨ n y := rfl

instance : HeytingAlgebra (Nucleus X) where
  le_himp_iff _ n _ := by
    simp [← coe_le_coe, Pi.le_def]
    exact ⟨fun h i ↦ h i i le_rfl,
      fun h1 i j _ ↦ le_trans (inf_le_inf_right (n j) (by gcongr)) (h1 j)⟩
  compl m := m ⇨ ⊥
  himp_bot m := rfl

instance : Order.Frame (Nucleus X) where
   __ := Nucleus.instHeytingAlgebra
   __ := Nucleus.instCompleteLattice

end
end Nucleus
