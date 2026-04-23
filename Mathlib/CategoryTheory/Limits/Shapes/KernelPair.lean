/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-!
# Kernel pairs

This file defines what it means for a parallel pair of morphisms `a b : R ⟶ X` to be the kernel pair
for a morphism `f`.
Some properties of kernel pairs are given, namely allowing one to transfer between
the kernel pair of `f₁ ≫ f₂` to the kernel pair of `f₁`.
It is also proved that if `f` is a coequalizer of some pair, and `a`,`b` is a kernel pair for `f`
then it is a coequalizer of `a`,`b`.

## Implementation

The definition is essentially just a wrapper for `IsLimit (PullbackCone.mk _ _ _)`, but the
constructions given here are useful, yet awkward to present in that language, so a basic API
is developed here.

## TODO

- Internal equivalence relations (or congruences) and the fact that every kernel pair induces one,
  and the converse in an effective regular category (WIP by b-mehta).

-/

@[expose] public section


universe v u u₂

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {R X Y Z : C} (f : X ⟶ Y) (a b : R ⟶ X)

/-- `IsKernelPair f a b` expresses that `(a, b)` is a kernel pair for `f`, i.e. `a ≫ f = b ≫ f`
and the square
  R → X
  ↓   ↓
  X → Y
is a pullback square.
This is just an abbreviation for `IsPullback a b f f`.
-/
abbrev IsKernelPair :=
  IsPullback a b f f

namespace IsKernelPair

/-- The data expressing that `(a, b)` is a kernel pair is subsingleton. -/
instance : Subsingleton (IsKernelPair f a b) :=
  ⟨fun P Q => by constructor⟩

/-- If `f` is a monomorphism, then `(𝟙 _, 𝟙 _)` is a kernel pair for `f`. -/
theorem id_of_mono [Mono f] : IsKernelPair f (𝟙 _) (𝟙 _) :=
  ⟨⟨rfl⟩, ⟨PullbackCone.isLimitMkIdId _⟩⟩

instance [Mono f] : Inhabited (IsKernelPair f (𝟙 _) (𝟙 _)) :=
  ⟨id_of_mono f⟩

variable {f a b}

/--
Given a pair of morphisms `p`, `q` to `X` which factor through `f`, they factor through any kernel
pair of `f`.
-/
noncomputable def lift {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    S ⟶ R :=
  PullbackCone.IsLimit.lift k.isLimit _ _ w

@[reassoc (attr := simp)]
lemma lift_fst {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    k.lift p q w ≫ a = p :=
  PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma lift_snd {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    k.lift p q w ≫ b = q :=
  PullbackCone.IsLimit.lift_snd _ _ _ _

/--
Given a pair of morphisms `p`, `q` to `X` which factor through `f`, they factor through any kernel
pair of `f`.
-/
noncomputable def lift' {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    { t : S ⟶ R // t ≫ a = p ∧ t ≫ b = q } :=
  ⟨k.lift p q w, by simp⟩

/--
If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `a ≫ f₁ = b ≫ f₁`, then `(a,b)` is a kernel pair for
just `f₁`.
That is, to show that `(a,b)` is a kernel pair for `f₁` it suffices to only show the square
commutes, rather than to additionally show it's a pullback.
-/
theorem cancel_right {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁)
    (big_k : IsKernelPair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b :=
  { w := comm
    isLimit' :=
      ⟨PullbackCone.isLimitAux' _ fun s => by
        let s' : PullbackCone (f₁ ≫ f₂) (f₁ ≫ f₂) :=
          PullbackCone.mk s.fst s.snd (s.condition_assoc _)
        refine ⟨big_k.isLimit.lift s', big_k.isLimit.fac _ WalkingCospan.left,
          big_k.isLimit.fac _ WalkingCospan.right, fun m₁ m₂ => ?_⟩
        apply big_k.isLimit.hom_ext
        refine (PullbackCone.mk a b ?_ : PullbackCone (f₁ ≫ f₂) _).equalizer_ext ?_ ?_
        · apply reassoc_of% comm
        · apply m₁.trans (big_k.isLimit.fac s' WalkingCospan.left).symm
        · apply m₂.trans (big_k.isLimit.fac s' WalkingCospan.right).symm⟩ }

/-- If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `f₂` is mono, then `(a,b)` is a kernel pair for
just `f₁`.
The converse of `comp_of_mono`.
-/
theorem cancel_right_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂]
    (big_k : IsKernelPair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b :=
  cancel_right (by rw [← cancel_mono f₂, assoc, assoc, big_k.w]) big_k

set_option backward.isDefEq.respectTransparency false in
/--
If `(a,b)` is a kernel pair for `f₁` and `f₂` is mono, then `(a,b)` is a kernel pair for `f₁ ≫ f₂`.
The converse of `cancel_right_of_mono`.
-/
theorem comp_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂] (small_k : IsKernelPair f₁ a b) :
    IsKernelPair (f₁ ≫ f₂) a b :=
  { w := by rw [small_k.w_assoc]
    isLimit' := ⟨by
      refine PullbackCone.isLimitAux _
        (fun s => small_k.lift s.fst s.snd (by rw [← cancel_mono f₂, assoc, s.condition, assoc]))
        (by simp) (by simp) ?_
      intro s m hm
      apply small_k.isLimit.hom_ext
      apply PullbackCone.equalizer_ext small_k.cone _ _
      · exact (hm WalkingCospan.left).trans (by simp)
      · exact (hm WalkingCospan.right).trans (by simp)⟩ }

set_option backward.isDefEq.respectTransparency false in
/--
If `(a,b)` is the kernel pair of `f`, and `f` is a coequalizer morphism for some parallel pair, then
`f` is a coequalizer morphism of `a` and `b`.
-/
noncomputable def toCoequalizer (k : IsKernelPair f a b) (r : RegularEpi f) :
    IsColimit (Cofork.ofπ f k.w) := by
  let t := k.isLimit.lift (PullbackCone.mk _ _ r.w)
  have ht : t ≫ a = r.left := k.isLimit.fac _ WalkingCospan.left
  have kt : t ≫ b = r.right := k.isLimit.fac _ WalkingCospan.right
  refine Cofork.IsColimit.mk _
    (fun s => Cofork.IsColimit.desc r.isColimit s.π
      (by rw [← ht, assoc, s.condition, reassoc_of% kt]))
    (fun s => ?_) (fun s m w => ?_)
  · apply Cofork.IsColimit.π_desc' r.isColimit
  · apply Cofork.IsColimit.hom_ext r.isColimit
    exact w.trans (Cofork.IsColimit.π_desc' r.isColimit _ _).symm

/--
If `(a,b)` is the kernel pair of `f`, and `f` is a regular epimorphism, then
`f` is a coequalizer morphism of `a` and `b`.
-/
noncomputable def toCoequalizer' (k : IsKernelPair f a b) [IsRegularEpi f] :
    IsColimit (Cofork.ofπ f k.w) :=
  toCoequalizer k <| IsRegularEpi.getStruct f

set_option backward.isDefEq.respectTransparency false in
/-- If `a₁ a₂ : A ⟶ Y` is a kernel pair for `g : Y ⟶ Z`, then `a₁ ×[Z] X` and `a₂ ×[Z] X`
(`A ×[Z] X ⟶ Y ×[Z] X`) is a kernel pair for `Y ×[Z] X ⟶ X`. -/
protected theorem pullback {X Y Z A : C} {g : Y ⟶ Z} {a₁ a₂ : A ⟶ Y} (h : IsKernelPair g a₁ a₂)
    (f : X ⟶ Z) [HasPullback f g] [HasPullback f (a₁ ≫ g)] :
    IsKernelPair (pullback.fst f g)
      (pullback.map f _ f _ (𝟙 X) a₁ (𝟙 Z) (by simp) <| Category.comp_id _)
      (pullback.map _ _ _ _ (𝟙 X) a₂ (𝟙 Z) (by simp) <| (Category.comp_id _).trans h.1.1) := by
  refine ⟨⟨by rw [pullback.lift_fst, pullback.lift_fst]⟩, ⟨PullbackCone.isLimitAux _
    (fun s => pullback.lift (s.fst ≫ pullback.fst _ _)
      (h.lift (s.fst ≫ pullback.snd _ _) (s.snd ≫ pullback.snd _ _) ?_ ) ?_) (fun s => ?_)
        (fun s => ?_) (fun s (m : _ ⟶ pullback f (a₁ ≫ g)) hm => ?_)⟩⟩
  · simp_rw [Category.assoc, ← pullback.condition, ← Category.assoc, s.condition]
  · simp only [assoc, lift_fst_assoc, pullback.condition]
  · ext <;> simp
  · ext
    · simp [s.condition]
    · simp
  · apply pullback.hom_ext
    · simpa using hm WalkingCospan.left =≫ pullback.fst f g
    · apply PullbackCone.IsLimit.hom_ext h.isLimit
      · simpa using hm WalkingCospan.left =≫ pullback.snd f g
      · simpa using hm WalkingCospan.right =≫ pullback.snd f g

set_option backward.isDefEq.respectTransparency false in
theorem mono_of_isIso_fst (h : IsKernelPair f a b) [IsIso a] : Mono f := by
  obtain ⟨l, h₁, h₂⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit (𝟙 _) (𝟙 _) (by simp)
  rw [IsPullback.cone_fst, ← IsIso.eq_comp_inv, Category.id_comp] at h₁
  rw [h₁, IsIso.inv_comp_eq, Category.comp_id] at h₂
  constructor
  intro Z g₁ g₂ e
  obtain ⟨l', rfl, rfl⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit _ _ e
  rw [IsPullback.cone_fst, h₂]

theorem mono_of_eq_fst_snd' (h : IsKernelPair f a a) : Mono f :=
  ⟨fun g₁ g₂ e ↦ (lift_fst h g₁ g₂ e).symm.trans <| lift_snd h g₁ g₂ e⟩

theorem mono_of_eq_fst_snd (h : IsKernelPair f a b) (e : a = b) : Mono f := by
  induction e; exact h.mono_of_eq_fst_snd'

theorem isIso_of_mono (h : IsKernelPair f a b) [Mono f] : IsIso a := by
  rw [←
    show _ = a from
      (Category.comp_id _).symm.trans
        ((IsKernelPair.id_of_mono f).isLimit.conePointUniqueUpToIso_inv_comp h.isLimit
          WalkingCospan.left)]
  infer_instance

theorem of_isIso_of_mono [IsIso a] [Mono f] : IsKernelPair f a a := by
  change IsPullback _ _ _ _
  convert (IsPullback.of_horiz_isIso ⟨(rfl : a ≫ 𝟙 X = _ )⟩).paste_vert (IsKernelPair.id_of_mono f)
  all_goals { simp }

/-- The kernel pair provided by `HasPullback f f` fits into an `IsKernelPair`. -/
theorem of_hasPullback (f : X ⟶ Y) [HasPullback f f] :
    IsKernelPair f (pullback.fst f f) (pullback.snd f f) :=
  IsPullback.of_hasPullback f f

end IsKernelPair

lemma IsRegularEpi.exists_of_isKernelPair {X Y : C} (π : X ⟶ Y) [IsRegularEpi π] {Z : C}
    {fst snd : Z ⟶ X} (h : IsKernelPair π fst snd) {W : C} (f : X ⟶ W) (w : fst ≫ f = snd ≫ f) :
    ∃ (g : Y ⟶ W), π ≫ g = f :=
  ⟨h.toCoequalizer'.desc (Cofork.ofπ f w), Cofork.IsColimit.π_desc h.toCoequalizer'⟩

end CategoryTheory
