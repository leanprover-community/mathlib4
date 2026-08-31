/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Product of convex spaces

This file defines the cartesian product of convex spaces.

We also show that products, `Pi` types and `Finsupp` types of cancellative convex spaces are
cancellative.
-/

open Convexity Finsupp

public noncomputable section

variable {I R S : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [Semiring S] [PartialOrder S] [IsStrictOrderedRing S]

namespace Prod
variable {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]

instance : ConvexSpace R (X × Y) := .mk
  (fun w ↦ (w.iConvexComb fst, w.iConvexComb snd))
  (by simp)
  (by simp [iConvexComb_assoc])

@[simp]
lemma fst_sConvexComb (w : StdSimplex R (X × Y)) : w.sConvexComb.fst = w.iConvexComb fst := rfl

@[simp]
lemma snd_sConvexComb (w : StdSimplex R (X × Y)) : w.sConvexComb.snd = w.iConvexComb snd := rfl

@[fun_prop]
lemma isAffineMap_fst : IsAffineMap R (fst : X × Y → X) where map_sConvexComb := fst_sConvexComb

@[fun_prop]
lemma isAffineMap_snd : IsAffineMap R (snd : X × Y → Y) where map_sConvexComb := snd_sConvexComb

@[simp]
lemma fst_iConvexComb (w : StdSimplex R I) (f : I → X × Y) :
    (w.iConvexComb f).fst = w.iConvexComb (fun i ↦ (f i).fst) :=
  isAffineMap_fst.map_iConvexComb ..

@[simp]
lemma snd_iConvexComb (w : StdSimplex R I) (f : I → X × Y) :
    (w.iConvexComb f).snd = w.iConvexComb (fun i ↦ (f i).snd) :=
  isAffineMap_snd.map_iConvexComb ..

@[simp]
lemma fst_convexCombPair (a b : R) (ha hb hab) (x y : X × Y) :
    (convexCombPair a b ha hb hab x y).fst = convexCombPair a b ha hb hab x.fst y.fst :=
  isAffineMap_fst.map_convexCombPair ..

@[simp]
lemma snd_convexCombPair (a b : R) (ha hb hab) (x y : X × Y) :
    (convexCombPair a b ha hb hab x y).snd = convexCombPair a b ha hb hab x.snd y.snd :=
  isAffineMap_snd.map_convexCombPair ..

instance [ConvexSpace S X] [ConvexSpace S Y] [IsConvexCombComm R S X]
    [IsConvexCombComm R S Y] : IsConvexCombComm R S (X × Y) where
  iConvexComb_comm' f g := by
    ext
    · simpa using iConvexComb_comm f g fun e k ↦ (e k).fst
    · simpa using iConvexComb_comm f g fun e k ↦ (e k).snd

instance [IsCancelConvexSpace R X] [IsCancelConvexSpace R Y] : IsCancelConvexSpace R (X × Y) where
  convexCombPair_left_injective a b ha hb hab y x₁ x₂ := by simp [Prod.ext_iff, *]

end Prod

namespace Pi
variable {ι : Type*} {X : ι → Type*} [∀ i, ConvexSpace R (X i)] {i : ι}

instance : ConvexSpace R (∀ i, X i) := .mk
  (fun w i ↦ w.iConvexComb (· i))
  (by simp)
  (by simp [iConvexComb_assoc])

@[simp]
lemma sConvexComb_apply (w : StdSimplex R (∀ i, X i)) (i : ι) :
    w.sConvexComb i = w.iConvexComb (· i) := rfl

@[fun_prop]
lemma isAffineMap_eval : IsAffineMap R (· i : (∀ i, X i) → X i) where
  map_sConvexComb _ := sConvexComb_apply ..

@[simp]
lemma iConvexComb_apply (w : StdSimplex R I) (f : I → ∀ i, X i) (i : ι) :
    w.iConvexComb f i = w.iConvexComb (fun j ↦ f j i) := isAffineMap_eval.map_iConvexComb ..

@[simp]
lemma convexCombPair_apply (a b : R) (ha hb hab) (f g : ∀ i, X i) (i : ι) :
    convexCombPair a b ha hb hab f g i = convexCombPair a b ha hb hab (f i) (g i) :=
  isAffineMap_eval.map_convexCombPair ..

instance [∀ i, ConvexSpace S (X i)] [∀ i, IsConvexCombComm R S (X i)] :
    IsConvexCombComm R S (∀ i, X i) where
  iConvexComb_comm' f g := by ext i; simpa using iConvexComb_comm f g fun e k ↦ e k i

instance [∀ i, IsCancelConvexSpace R (X i)] : IsCancelConvexSpace R (∀ i, X i) where
  convexCombPair_left_injective a b ha hb hab g f₁ f₂ := by simp [funext_iff, *]

end Pi

namespace Finsupp
variable {ι : Type*} {X : Type*} [Zero X] [ConvexSpace R X] {i : ι}

instance : ConvexSpace R (ι →₀ X) := .mk
  (fun w ↦ by
    classical
    refine .onFinset (w.weights.support.biUnion Finsupp.support) (fun i ↦ w.iConvexComb (· i)) ?_
    rintro i hi
    contrapose! hi
    simp_all)
  (by simp)
  (fun w ↦ by ext; simp [iConvexComb_assoc])

@[simp]
lemma sConvexComb_apply (w : StdSimplex R (ι →₀ X)) (i : ι) :
    w.sConvexComb i = w.iConvexComb (· i) := rfl

@[fun_prop]
lemma isAffineMap_eval : IsAffineMap R (· i : (ι →₀ X) → X) where
  map_sConvexComb _ := sConvexComb_apply ..

@[simp]
lemma iConvexComb_apply (w : StdSimplex R I) (f : I → ι →₀ X) (i : ι) :
    w.iConvexComb f i = w.iConvexComb (fun j ↦ f j i) := isAffineMap_eval.map_iConvexComb ..

@[simp]
lemma convexCombPair_apply (a b : R) (ha hb hab) (f g : ι →₀ X) (i : ι) :
    convexCombPair a b ha hb hab f g i = convexCombPair a b ha hb hab (f i) (g i) :=
  isAffineMap_eval.map_convexCombPair ..

instance [ConvexSpace S X] [IsConvexCombComm R S X] : IsConvexCombComm R S (ι →₀ X) where
  iConvexComb_comm' f g := by ext i; simpa using iConvexComb_comm f g fun e k ↦ e k i

instance [IsCancelConvexSpace R X] : IsCancelConvexSpace R (ι →₀ X) where
  convexCombPair_left_injective a b ha hb hab g f₁ f₂ := by simp [Finsupp.ext_iff, *]

end Finsupp

namespace Convexity
variable {ι X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]

section Prod
variable {Z : Type*} [ConvexSpace R Z]

@[fun_prop]
lemma IsAffineMap.prodMk {f : X → Y} {g : X → Z} (hf : IsAffineMap R f) (hg : IsAffineMap R g) :
    IsAffineMap R fun x ↦ (f x, g x) where
  map_sConvexComb w := by ext <;> simp [hf.map_sConvexComb, hg.map_sConvexComb, sConvexComb_map]

@[fun_prop]
protected lemma IsAffineMap.fst {f : X → Y × Z} (hf : IsAffineMap R f) :
    IsAffineMap R fun x ↦ (f x).1 := Prod.isAffineMap_fst.comp hf

@[fun_prop]
protected lemma IsAffineMap.snd {f : X → Y × Z} (hf : IsAffineMap R f) :
    IsAffineMap R fun x ↦ (f x).2 := Prod.isAffineMap_snd.comp hf

lemma isAffineMap_prod_iff {f : X → Y × Z} :
    IsAffineMap R f ↔ (IsAffineMap R fun x ↦ (f x).1) ∧ IsAffineMap R fun x ↦ (f x).2 :=
  ⟨fun hf ↦ ⟨hf.fst, hf.snd⟩, fun hf ↦ hf.1.prodMk hf.2⟩

@[simp]
lemma isAffineMap_prodMk_iff {f : X → Y} {g : X → Z} :
    (IsAffineMap R fun x ↦ (f x, g x)) ↔ IsAffineMap R f ∧ IsAffineMap R g := isAffineMap_prod_iff

end Prod

section Pi
variable {Y : ι → Type*} [∀ i, ConvexSpace R (Y i)] {f : X → ∀ i, Y i}

@[fun_prop]
lemma IsAffineMap.pi (hf : ∀ i, IsAffineMap R (f · i)) : IsAffineMap R f where
  map_sConvexComb w := by ext; simp [(hf _).map_sConvexComb, sConvexComb_map]

lemma IsAffineMap.eval (hf : IsAffineMap R f) (i : ι) : IsAffineMap R (f · i) :=
  Pi.isAffineMap_eval.comp hf

lemma isAffineMap_pi_iff : IsAffineMap R f ↔ ∀ i, IsAffineMap R (f · i) :=
  ⟨fun hf ↦ hf.eval, .pi⟩

end Pi

section Finsupp
variable [Zero Y] {f : X → ι →₀ Y}

@[fun_prop]
lemma IsAffineMap.finsupp (hf : ∀ i, IsAffineMap R (f · i)) : IsAffineMap R f where
  map_sConvexComb w := by ext; simp [(hf _).map_sConvexComb, sConvexComb_map]

lemma IsAffineMap.finsuppEval (hf : IsAffineMap R f) (i : ι) : IsAffineMap R (f · i) :=
  Finsupp.isAffineMap_eval.comp hf

lemma isAffineMap_finsupp_iff : IsAffineMap R f ↔ ∀ i, IsAffineMap R (f · i) :=
  ⟨fun hf ↦ hf.finsuppEval, .finsupp⟩

end Finsupp
end Convexity
