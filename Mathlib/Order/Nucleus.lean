/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.Closure
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

open Order InfHom Set

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
variable [Order.Frame X] {n m : Nucleus X} {x y : X}

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

lemma mem_range : x ∈ range n ↔ n x = x where
  mp := by rintro ⟨x, rfl⟩; exact idempotent
  mpr h := ⟨x, h⟩

/-- See `Nucleus.giRestrict` for the public-facing version. -/
private def giAux (n : Nucleus X) : GaloisInsertion (rangeFactorization n) Subtype.val where
  choice x hx := ⟨x, mem_range.2 <| hx.antisymm n.le_apply⟩
  gc x y := ClosureOperator.IsClosed.closure_le_iff (c := n.toClosureOperator) <| mem_range.1 y.2
  le_l_u x := le_apply
  choice_eq x hx := by ext; exact le_apply.antisymm hx

instance : CompleteLattice (range n) := n.giAux.liftCompleteLattice

instance range.instFrameMinimalAxioms : Frame.MinimalAxioms (range n) where
  inf_sSup_le_iSup_inf a s := by
    simp_rw [← Subtype.coe_le_coe, iSup_subtype', iSup, sSup, n.giAux.gc.u_inf]
    rw [rangeFactorization_coe, ← mem_range.1 a.prop, ← map_inf]
    apply n.monotone
    simp_rw [inf_sSup_eq, sSup_image, iSup_range, iSup_image, iSup_subtype', n.giAux.gc.u_inf,
      le_rfl]

instance : Frame (range n) := .ofMinimalAxioms range.instFrameMinimalAxioms

/-- Restrict a nucleus to its range. -/
@[simps] def restrict (n : Nucleus X) : FrameHom X (range n) where
  toFun := rangeFactorization n
  map_inf' a b := by ext; exact map_inf
  map_top' := by ext; exact map_top n
  map_sSup' s := by rw [n.giAux.gc.l_sSup, sSup_image]

/-- The restriction of a nucleus to its range forms a Galois insertion with the forgetful map from
the range to the original frame. -/
def giRestrict (n : Nucleus X) : GaloisInsertion n.restrict Subtype.val := n.giAux

lemma comp_eq_right_iff_le : n ∘ m = m ↔ n ≤ m where
  mpr h := funext_iff.mpr <| fun _ ↦ le_antisymm (le_trans (h (m _)) (m.idempotent' _)) le_apply
  mp h := by
    rw [← coe_le_coe, ← h]
    exact fun _ ↦ monotone le_apply

@[simp] lemma range_subset_range : range m ⊆ range n ↔ n ≤ m where
  mp h x := by
    rw [← mem_range.mp (Set.range_subset_iff.mp h x)]
    exact n.monotone m.le_apply
  mpr h :=
    range_subset_range_iff_exists_comp.mpr ⟨m, (comp_eq_right_iff_le.mpr h).symm⟩

end Frame
end Nucleus
