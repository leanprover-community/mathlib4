/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.shapes.kernel_pair
! leanprover-community/mathlib commit f6bab67886fb92c3e2f539cc90a83815f69a189d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.CommSq
import Mathbin.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Kernel pairs

This file defines what it means for a parallel pair of morphisms `a b : R ⟶ X` to be the kernel pair
for a morphism `f`.
Some properties of kernel pairs are given, namely allowing one to transfer between
the kernel pair of `f₁ ≫ f₂` to the kernel pair of `f₁`.
It is also proved that if `f` is a coequalizer of some pair, and `a`,`b` is a kernel pair for `f`
then it is a coequalizer of `a`,`b`.

## Implementation

The definition is essentially just a wrapper for `is_limit (pullback_cone.mk _ _ _)`, but the
constructions given here are useful, yet awkward to present in that language, so a basic API
is developed here.

## TODO

- Internal equivalence relations (or congruences) and the fact that every kernel pair induces one,
  and the converse in an effective regular category (WIP by b-mehta).

-/


universe v u u₂

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {R X Y Z : C} (f : X ⟶ Y) (a b : R ⟶ X)

/-- `is_kernel_pair f a b` expresses that `(a, b)` is a kernel pair for `f`, i.e. `a ≫ f = b ≫ f`
and the square
  R → X
  ↓   ↓
  X → Y
is a pullback square.
This is just an abbreviation for `is_pullback a b f f`.
-/
abbrev IsKernelPair :=
  IsPullback a b f f
#align category_theory.is_kernel_pair CategoryTheory.IsKernelPair

namespace IsKernelPair

/-- The data expressing that `(a, b)` is a kernel pair is subsingleton. -/
instance : Subsingleton (IsKernelPair f a b) :=
  ⟨fun P Q => by
    cases P
    cases Q
    congr ⟩

/-- If `f` is a monomorphism, then `(𝟙 _, 𝟙 _)`  is a kernel pair for `f`. -/
theorem id_of_mono [Mono f] : IsKernelPair f (𝟙 _) (𝟙 _) :=
  ⟨⟨rfl⟩, ⟨PullbackCone.isLimitMkIdId _⟩⟩
#align category_theory.is_kernel_pair.id_of_mono CategoryTheory.IsKernelPair.id_of_mono

instance [Mono f] : Inhabited (IsKernelPair f (𝟙 _) (𝟙 _)) :=
  ⟨id_of_mono f⟩

variable {f a b}

/--
Given a pair of morphisms `p`, `q` to `X` which factor through `f`, they factor through any kernel
pair of `f`.
-/
noncomputable def lift' {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    { t : S ⟶ R // t ≫ a = p ∧ t ≫ b = q } :=
  PullbackCone.IsLimit.lift' k.IsLimit _ _ w
#align category_theory.is_kernel_pair.lift' CategoryTheory.IsKernelPair.lift'

/--
If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `a ≫ f₁ = b ≫ f₁`, then `(a,b)` is a kernel pair for
just `f₁`.
That is, to show that `(a,b)` is a kernel pair for `f₁` it suffices to only show the square
commutes, rather than to additionally show it's a pullback.
-/
theorem cancel_right {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁)
    (big_k : IsKernelPair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b :=
  { w := comm
    is_limit' :=
      ⟨PullbackCone.isLimitAux' _ fun s =>
          by
          let s' : pullback_cone (f₁ ≫ f₂) (f₁ ≫ f₂) :=
            pullback_cone.mk s.fst s.snd (s.condition_assoc _)
          refine'
            ⟨big_k.is_limit.lift s', big_k.is_limit.fac _ walking_cospan.left,
              big_k.is_limit.fac _ walking_cospan.right, fun m m₁ m₂ => _⟩
          apply big_k.is_limit.hom_ext
          refine' (pullback_cone.mk a b _ : pullback_cone (f₁ ≫ f₂) _).equalizer_ext _ _
          apply m₁.trans (big_k.is_limit.fac s' walking_cospan.left).symm
          apply m₂.trans (big_k.is_limit.fac s' walking_cospan.right).symm⟩ }
#align category_theory.is_kernel_pair.cancel_right CategoryTheory.IsKernelPair.cancel_right

/-- If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `f₂` is mono, then `(a,b)` is a kernel pair for
just `f₁`.
The converse of `comp_of_mono`.
-/
theorem cancel_right_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂]
    (big_k : IsKernelPair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b :=
  cancel_right (by rw [← cancel_mono f₂, assoc, assoc, big_k.w]) big_k
#align category_theory.is_kernel_pair.cancel_right_of_mono CategoryTheory.IsKernelPair.cancel_right_of_mono

/--
If `(a,b)` is a kernel pair for `f₁` and `f₂` is mono, then `(a,b)` is a kernel pair for `f₁ ≫ f₂`.
The converse of `cancel_right_of_mono`.
-/
theorem comp_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂] (small_k : IsKernelPair f₁ a b) :
    IsKernelPair (f₁ ≫ f₂) a b :=
  { w := by rw [small_k.w_assoc]
    is_limit' :=
      ⟨PullbackCone.isLimitAux' _ fun s => by
          refine' ⟨_, _, _, _⟩
          apply (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).1
          rw [← cancel_mono f₂, assoc, s.condition, assoc]
          apply (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.1
          apply (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.2
          intro m m₁ m₂
          apply small_k.is_limit.hom_ext
          refine' (pullback_cone.mk a b _ : pullback_cone f₁ _).equalizer_ext _ _
          · exact m₁.trans (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.1.symm
          · exact m₂.trans (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.2.symm⟩ }
#align category_theory.is_kernel_pair.comp_of_mono CategoryTheory.IsKernelPair.comp_of_mono

/--
If `(a,b)` is the kernel pair of `f`, and `f` is a coequalizer morphism for some parallel pair, then
`f` is a coequalizer morphism of `a` and `b`.
-/
def toCoequalizer (k : IsKernelPair f a b) [r : RegularEpi f] : IsColimit (Cofork.ofπ f k.w) :=
  by
  let t := k.is_limit.lift (pullback_cone.mk _ _ r.w)
  have ht : t ≫ a = r.left := k.is_limit.fac _ walking_cospan.left
  have kt : t ≫ b = r.right := k.is_limit.fac _ walking_cospan.right
  apply cofork.is_colimit.mk _ _ _ _
  · intro s
    apply (cofork.is_colimit.desc' r.is_colimit s.π _).1
    rw [← ht, assoc, s.condition, reassoc_of kt]
  · intro s
    apply (cofork.is_colimit.desc' r.is_colimit s.π _).2
  · intro s m w
    apply r.is_colimit.hom_ext
    rintro ⟨⟩
    change (r.left ≫ f) ≫ m = (r.left ≫ f) ≫ _
    rw [assoc, assoc]
    congr 1
    erw [(cofork.is_colimit.desc' r.is_colimit s.π _).2]
    apply w
    erw [(cofork.is_colimit.desc' r.is_colimit s.π _).2]
    apply w
#align category_theory.is_kernel_pair.to_coequalizer CategoryTheory.IsKernelPair.toCoequalizer

/-- If `a₁ a₂ : A ⟶ Y` is a kernel pair for `g : Y ⟶ Z`, then `a₁ ×[Z] X` and `a₂ ×[Z] X`
(`A ×[Z] X ⟶ Y ×[Z] X`) is a kernel pair for `Y ×[Z] X ⟶ X`. -/
protected theorem pullback {X Y Z A : C} {g : Y ⟶ Z} {a₁ a₂ : A ⟶ Y} (h : IsKernelPair g a₁ a₂)
    (f : X ⟶ Z) [HasPullback f g] [HasPullback f (a₁ ≫ g)] :
    IsKernelPair (pullback.fst : pullback f g ⟶ X)
      (pullback.map f _ f _ (𝟙 X) a₁ (𝟙 Z) (by simp) <| Category.comp_id _)
      (pullback.map _ _ _ _ (𝟙 X) a₂ (𝟙 Z) (by simp) <| (Category.comp_id _).trans h.1.1) :=
  by
  refine' ⟨⟨_⟩, ⟨_⟩⟩
  · rw [pullback.lift_fst, pullback.lift_fst]
  · fapply pullback_cone.is_limit_aux'
    intro s
    refine'
      ⟨pullback.lift (s.fst ≫ pullback.fst)
          (h.lift' (s.fst ≫ pullback.snd) (s.snd ≫ pullback.snd) _).1 _,
        _, _, _⟩
    · simp_rw [category.assoc, ← pullback.condition, ← category.assoc, s.condition]
    · rw [← category.assoc, (h.lift' _ _ _).2.1, category.assoc, category.assoc, pullback.condition]
    · rw [limits.pullback_cone.mk_fst]
      ext <;>
        simp only [category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc,
          category.comp_id, (h.lift' _ _ _).2.1]
    · rw [limits.pullback_cone.mk_snd]
      ext <;>
        simp only [category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc,
          category.comp_id, (h.lift' _ _ _).2.2, s.condition]
    · intro m h₁ h₂
      ext
      · rw [pullback.lift_fst]
        conv_rhs => rw [← h₁, category.assoc, pullback_cone.mk_fst]
        congr 1
        refine' ((pullback.lift_fst _ _ _).trans <| category.comp_id _).symm
      · rw [pullback.lift_snd]
        apply pullback_cone.is_limit.hom_ext h.is_limit <;>
            dsimp only [is_pullback.cone, comm_sq.cone] <;>
          simp only [pullback_cone.mk_fst, pullback_cone.mk_snd, category.assoc,
            (h.lift' _ _ _).2.1, (h.lift' _ _ _).2.2]
        · conv_rhs => rw [← h₁, category.assoc, pullback_cone.mk_fst, pullback.lift_snd]
        · conv_rhs => rw [← h₂, category.assoc, pullback_cone.mk_snd, pullback.lift_snd]
#align category_theory.is_kernel_pair.pullback CategoryTheory.IsKernelPair.pullback

theorem mono_of_isIso_fst (h : IsKernelPair f a b) [IsIso a] : Mono f :=
  by
  obtain ⟨l, h₁, h₂⟩ := limits.pullback_cone.is_limit.lift' h.is_limit (𝟙 _) (𝟙 _) (by simp [h.w])
  rw [is_pullback.cone_fst, ← is_iso.eq_comp_inv, category.id_comp] at h₁
  rw [h₁, is_iso.inv_comp_eq, category.comp_id] at h₂
  constructor
  intro Z g₁ g₂ e
  obtain ⟨l', rfl, rfl⟩ := limits.pullback_cone.is_limit.lift' h.is_limit _ _ e
  rw [is_pullback.cone_fst, h₂]
#align category_theory.is_kernel_pair.mono_of_is_iso_fst CategoryTheory.IsKernelPair.mono_of_isIso_fst

theorem isIso_of_mono (h : IsKernelPair f a b) [Mono f] : IsIso a :=
  by
  rw [←
    show _ = a from
      (category.comp_id _).symm.trans
        ((is_kernel_pair.id_of_mono f).IsLimit.conePointUniqueUpToIso_inv_comp h.is_limit
          walking_cospan.left)]
  infer_instance
#align category_theory.is_kernel_pair.is_iso_of_mono CategoryTheory.IsKernelPair.isIso_of_mono

theorem of_isIso_of_mono [IsIso a] [Mono f] : IsKernelPair f a a :=
  by
  delta is_kernel_pair
  convert_to is_pullback a (a ≫ 𝟙 X) (𝟙 X ≫ f) f
  · rw [category.comp_id]; · rw [category.id_comp]
  exact (is_pullback.of_horiz_is_iso ⟨rfl⟩).paste_vert (is_kernel_pair.id_of_mono f)
#align category_theory.is_kernel_pair.of_is_iso_of_mono CategoryTheory.IsKernelPair.of_isIso_of_mono

end IsKernelPair

end CategoryTheory

