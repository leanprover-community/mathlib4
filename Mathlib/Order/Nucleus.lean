/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.Closure
import Mathlib.Order.Hom.Bounded
import Mathlib.Order.Hom.CompleteLattice

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

variable {X : Type*}

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
class NucleusClass (F X : Type*) [SemilatticeInf X] [FunLike F X X] : Prop
    extends InfHomClass F X X where
  /-- A nucleus is idempotent. -/
  idempotent (x : X) (f : F) : f (f x) ≤ f x
  /-- A nucleus is inflationary. -/
  le_apply (x : X) (f : F) : x ≤ f x

namespace Nucleus

section CompleteLattice

variable [CompleteLattice X] {n m : Nucleus X} {x y : X}

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

@[simp] theorem inf_apply (m n : Nucleus X) (x : X) : (m ⊓ n) x = m x ⊓ n x := by
  rw [← sInf_pair, sInf_apply, iInf_pair]

end CompleteLattice
section Frame
variable [Order.Frame X] {n : Nucleus X} {x y : X}

lemma map_himp_le : n (x ⇨ y) ≤ x ⇨ n y := by
  rw [le_himp_iff]
  calc
    n (x ⇨ y) ⊓ x
    _ ≤ n (x ⇨ y) ⊓ n x := by gcongr; exact n.le_apply
    _ = n (y ⊓ x) := by rw [← map_inf, himp_inf_self]
    _ ≤ n y := by gcongr; exact inf_le_left

lemma map_himp_apply (n : Nucleus X) (x y : X) : n (x ⇨ n y) = x ⇨ n y :=
  le_antisymm (map_himp_le.trans_eq <| by rw [n.idempotent]) n.le_apply

instance : HImp (Nucleus X) where
  himp m n :=
  { toFun x := ⨅ y ≥ x, m y ⇨ n y
    idempotent' x := le_iInf₂ fun y hy ↦
      calc
        ⨅ z ≥ ⨅ w ≥ x, m w ⇨ n w, m z ⇨ n z
        _ ≤ m (m y ⇨ n y) ⇨ n (m y ⇨ n y) := iInf₂_le _ <| biInf_le _ hy
        _ = m y ⇨ n y := by
          rw [map_himp_apply, himp_himp, ← map_inf, inf_of_le_right (le_trans n.le_apply le_himp)]
    map_inf' x y := by
      simp only [and_assoc, le_antisymm_iff, le_inf_iff, le_iInf_iff]
      refine ⟨fun z hxz ↦ iInf₂_le _ <| inf_le_of_left_le hxz,
        fun z hyz ↦ iInf₂_le _ <| inf_le_of_right_le hyz, ?_⟩
      have : Nonempty X := ⟨x⟩
      simp only [iInf_inf, le_iInf_iff, le_himp_iff, iInf_le_iff, le_inf_iff, forall_and,
        forall_const, and_imp]
      intro k hxyk l hlx hly hlk
      calc
        l = (l ⊓ m (x ⊔ k)) ⊓ (l ⊓ m (y ⊔ k)) := by
          rw [← inf_inf_distrib_left, ← map_inf, ← sup_inf_right, sup_eq_right.2 hxyk,
            inf_eq_left.2 hlk]
        _ ≤ n (x ⊔ k) ⊓ n (y ⊔ k) := by
          gcongr; exacts [hlx (x ⊔ k) le_sup_left, hly (y ⊔ k) le_sup_left]
        _ = n k := by rw [← map_inf, ← sup_inf_right, sup_eq_right.2 hxyk]
    le_apply' := by
      simpa using fun _ _ h ↦ inf_le_of_left_le <| h.trans n.le_apply }

@[simp] theorem himp_apply (m n : Nucleus X) (x : X) : (m ⇨ n) x = ⨅ y ≥ x, m y ⇨ n y := rfl

instance : HeytingAlgebra (Nucleus X) where
  compl m := m ⇨ ⊥
  le_himp_iff _ n _ := by
    simpa [← coe_le_coe, Pi.le_def]
      using ⟨fun h i ↦ h i i le_rfl, fun h i j _ ↦ (h j).trans' <| by gcongr⟩
  himp_bot m := rfl

instance : Order.Frame (Nucleus X) where
   __ := Nucleus.instHeytingAlgebra
   __ := Nucleus.instCompleteLattice

end Frame
open Set

variable [Order.Frame X] {n : Nucleus X}

/--
A Nucleus is a surjective morphism of frames.
-/
abbrev embedding (n : Nucleus X) := codRestrict n (range n) (by simp)

lemma range_fixpoint (x : range n) : n x = x := by
  obtain ⟨y, ⟨z, hy⟩⟩ := x
  simp [← hy, idempotent]

instance range_instBoundedOrder : BoundedOrder (range n) where
  top := n.embedding ⊤
  le_top := by simp [← Subtype.coe_le_coe]
  bot := n.embedding ⊥
  bot_le := by
    simp only [← Subtype.coe_le_coe, val_codRestrict_apply, Subtype.forall, mem_range,
      forall_exists_index, forall_apply_eq_imp_iff]
    exact fun _ ↦ n.monotone bot_le

instance range_instCompleteLattice : CompleteLattice (range n) where
  sup a b := n.embedding (a ⊔ b)
  le_sup_left a b := by
    simp only [← Subtype.coe_le_coe, val_codRestrict_apply]
    exact le_trans le_sup_left n.le_apply
  le_sup_right a b := by
    simp only [← Subtype.coe_le_coe, val_codRestrict_apply]
    exact le_trans le_sup_right n.le_apply
  sup_le a b c h1 h2 := by
    simp only [← Subtype.coe_le_coe, val_codRestrict_apply]
    rw [← range_fixpoint c]
    exact n.monotone (sup_le h1 h2)
  inf a b := n.embedding (a ⊓ b)
  inf_le_left a b := by
    simp only [← Subtype.coe_le_coe, val_codRestrict_apply, InfHomClass.map_inf]
    rw [← map_inf, ← range_fixpoint a]
    apply n.monotone
    rw [range_fixpoint]
    exact inf_le_left
  inf_le_right a b := by
    simp only [← Subtype.coe_le_coe, val_codRestrict_apply, InfHomClass.map_inf]
    rw [← map_inf, ← range_fixpoint b]
    apply n.monotone
    rw [range_fixpoint]
    exact inf_le_right
  le_inf a b := by
    simp_all only [← Subtype.coe_le_coe, val_codRestrict_apply, InfHomClass.map_inf, le_inf_iff,
      Subtype.forall, mem_range, forall_exists_index, forall_apply_eq_imp_iff, idempotent, and_true]
    intro c h1 h2
    exact le_trans h1 n.le_apply
  sSup s := n.embedding (⨆ x ∈ s, x)
  le_sSup s x h := by
    simp only [← Subtype.coe_le_coe, val_codRestrict_apply]
    rw [← range_fixpoint x]
    exact n.monotone (le_biSup Subtype.val h)
  sSup_le s x h := by
    simp only [← Subtype.coe_le_coe, val_codRestrict_apply]
    rw [← range_fixpoint x]
    exact n.monotone (iSup₂_le_iff.mpr h)
  sInf s := n.embedding (⨅ x ∈ s, x)
  le_sInf s x h := by
    simp only [← Subtype.coe_le_coe, val_codRestrict_apply]
    rw [← range_fixpoint x]
    exact n.monotone (le_iInf₂ h)
  sInf_le s x h := by
    simp only [← Subtype.coe_le_coe, val_codRestrict_apply]
    rw [← range_fixpoint x]
    exact n.monotone (biInf_le Subtype.val h)
  __ := Nucleus.range_instBoundedOrder

-- TODO is there a better way to expand these definitions than defining these lemmas?
-- Or should I include them for all the other operations as well?
lemma range_sSup_def (s : Set (range n)) : sSup s = n.embedding (⨆ x ∈ s, x) := rfl

lemma range_top_def : (⊤ : range n) = n.embedding ⊤ := rfl

lemma coe_range_map_inf (a b : range n) : ↑(a ⊓ b) = (↑a : X) ⊓ ↑b := by
  simp_rw [min, SemilatticeInf.inf, Lattice.inf]
  simp [range_fixpoint]
  exact rfl

instance range_instMinAx : Order.Frame.MinimalAxioms (range n) where
  inf_sSup_le_iSup_inf a s := by
    rw [← Subtype.coe_le_coe, iSup_subtype', iSup, range_sSup_def,range_sSup_def]
    repeat rw [iSup_subtype']
    rw [coe_range_map_inf, val_codRestrict_apply, ← range_fixpoint a, ← map_inf]
    apply n.monotone
    rw [inf_iSup_eq, iSup_range']
    gcongr
    rw [coe_range_map_inf]

instance : Order.Frame (range n) := Order.Frame.ofMinimalAxioms range_instMinAx

def embedding_frameHom (n : Nucleus X) : FrameHom X (range n) where
  toFun := n.embedding
  map_inf' a b := by
    ext
    simp [coe_range_map_inf]
  map_top' := by
    ext
    simp [range_top_def]
  map_sSup' s := by
    ext
    simp only [val_codRestrict_apply, range_sSup_def]
    apply le_antisymm
    · apply n.monotone
      simp only [mem_image, iSup_exists, le_iSup_iff, iSup_le_iff, and_imp,
        forall_apply_eq_imp_iff₂, val_codRestrict_apply, sSup_le_iff]
      exact fun _ h1 c h2 ↦ le_trans n.le_apply (h1 c h2)
    · rw [← @n.idempotent _ _ (sSup _)]
      apply n.monotone
      simp only [mem_image, iSup_exists, iSup_le_iff, and_imp, forall_apply_eq_imp_iff₂,
        val_codRestrict_apply]
      exact fun a h ↦ n.monotone (CompleteLattice.le_sSup s a h)

end Nucleus
