/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Relation between pullback/pushout squares and kernel/cokernel sequences

Consider a commutative square in a preadditive category:

```
X₁ ⟶ X₂
|    |
v    v
X₃ ⟶ X₄
```

In this file, we show that this is a pushout square iff the object `X₄`
identifies to the cokernel of the difference map `X₁ ⟶ X₂ ⊞ X₃`
via the obvious map `X₂ ⊞ X₃ ⟶ X₄`.

Similarly, it is a pullback square iff the object `X₁`
identifies to the kernel of the difference map `X₂ ⊞ X₃ ⟶ X₄`
via the obvious map `X₁ ⟶ X₂ ⊞ X₃`.

-/

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] [Preadditive C]
  {X₁ X₂ X₃ X₄ : C} [HasBinaryBiproduct X₂ X₃]

section Pushout

variable {f : X₁ ⟶ X₂} {g : X₁ ⟶ X₃} {inl : X₂ ⟶ X₄} {inr : X₃ ⟶ X₄}
/-- The cokernel cofork attached to a commutative square in a preadditive category. -/
noncomputable abbrev CommSq.cokernelCofork (sq : CommSq f g inl inr) :
    CokernelCofork (biprod.lift f (-g)) :=
  CokernelCofork.ofπ (biprod.desc inl inr) (by simp [sq.w])

/-- The short complex attached to the cokernel cofork of a commutative square. -/
@[simps]
noncomputable def CommSq.shortComplex (sq : CommSq f g inl inr) : ShortComplex C where
  f := biprod.lift f (-g)
  g := biprod.desc inl inr
  zero := by simp [sq.w]

/-- A commutative square in a preadditive category is a pushout square iff
the corresponding diagram `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` makes `X₄` a cokernel. -/
noncomputable def CommSq.isColimitEquivIsColimitCokernelCofork (sq : CommSq f g inl inr) :
    IsColimit (PushoutCocone.mk _ _ sq.w) ≃ IsColimit sq.cokernelCofork where
  toFun h :=
    Cofork.IsColimit.mk _
      (fun s ↦ PushoutCocone.IsColimit.desc h
        (biprod.inl ≫ s.π) (biprod.inr ≫ s.π) (by
          rw [← sub_eq_zero, ← assoc, ← assoc, ← Preadditive.sub_comp]
          convert s.condition <;> aesop_cat))
      (fun s ↦ by
        dsimp
        ext
        · simp only [biprod.inl_desc_assoc]
          apply PushoutCocone.IsColimit.inl_desc h
        · simp only [biprod.inr_desc_assoc]
          apply PushoutCocone.IsColimit.inr_desc h)
      (fun s m hm ↦ by
        apply PushoutCocone.IsColimit.hom_ext h
        · replace hm := biprod.inl ≫= hm
          dsimp at hm ⊢
          simp only [biprod.inl_desc_assoc] at hm
          rw [hm]
          symm
          apply PushoutCocone.IsColimit.inl_desc h
        · replace hm := biprod.inr ≫= hm
          dsimp at hm ⊢
          simp only [biprod.inr_desc_assoc] at hm
          rw [hm]
          symm
          apply PushoutCocone.IsColimit.inr_desc h)
  invFun h :=
    PushoutCocone.IsColimit.mk _
      (fun s ↦ h.desc (CokernelCofork.ofπ (biprod.desc s.inl s.inr)
          (by simp [s.condition])))
      (fun s ↦ by simpa using biprod.inl ≫=
                h.fac (CokernelCofork.ofπ (biprod.desc s.inl s.inr)
                  (by simp [s.condition])) .one)
      (fun s ↦ by simpa using biprod.inr ≫=
                h.fac (CokernelCofork.ofπ (biprod.desc s.inl s.inr)
                  (by simp [s.condition])) .one)
      (fun s m hm₁ hm₂ ↦ by
        apply Cofork.IsColimit.hom_ext h
        convert (h.fac (CokernelCofork.ofπ (biprod.desc s.inl s.inr)
          (by simp [s.condition])) .one).symm
        aesop_cat)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- The colimit cokernel cofork attached to a pushout square. -/
noncomputable def IsPushout.isColimitCokernelCofork (h : IsPushout f g inl inr) :
    IsColimit h.cokernelCofork :=
  h.isColimitEquivIsColimitCokernelCofork h.isColimit

lemma IsPushout.epi_shortComplex_g (h : IsPushout f g inl inr) :
    Epi h.shortComplex.g := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro _ b hb
  exact Cofork.IsColimit.hom_ext h.isColimitCokernelCofork (by simpa using hb)

end Pushout

section Pullback

variable {fst : X₁ ⟶ X₂} {snd : X₁ ⟶ X₃} {f : X₂ ⟶ X₄} {g : X₃ ⟶ X₄}

/-- The kernel fork attached to a commutative square in a preadditive category. -/
noncomputable abbrev CommSq.kernelFork (sq : CommSq fst snd f g) :
    KernelFork (biprod.desc f (-g)) :=
  KernelFork.ofι (biprod.lift fst snd) (by simp [sq.w])

/-- The short complex attached to the kernel fork of a commutative square.
(This is similar to `CommSq.shortComplex`, but with different signs.) -/
@[simps]
noncomputable def CommSq.shortComplex' (sq : CommSq fst snd f g) : ShortComplex C where
  f := biprod.lift fst snd
  g := biprod.desc f (-g)
  zero := by simp [sq.w]

/-- A commutative square in a preadditive category is a pullback square iff
the corresponding diagram `0 ⟶ X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` makes `X₁` a kernel. -/
noncomputable def CommSq.isLimitEquivIsLimitKernelFork (sq : CommSq fst snd f g) :
    IsLimit (PullbackCone.mk _ _ sq.w) ≃ IsLimit sq.kernelFork where
  toFun h :=
    Fork.IsLimit.mk _
      (fun s ↦ PullbackCone.IsLimit.lift h
        (s.ι ≫ biprod.fst) (s.ι ≫ biprod.snd) (by
          rw [← sub_eq_zero, assoc, assoc, ← Preadditive.comp_sub]
          convert s.condition <;> aesop_cat))
      (fun s ↦ by
        dsimp
        ext
        · simp only [assoc, biprod.lift_fst]
          apply PullbackCone.IsLimit.lift_fst h
        · simp only [assoc, biprod.lift_snd]
          apply PullbackCone.IsLimit.lift_snd h)
      (fun s m hm ↦ by
        apply PullbackCone.IsLimit.hom_ext h
        · replace hm := hm =≫ biprod.fst
          dsimp at hm ⊢
          simp only [assoc, biprod.lift_fst] at hm
          rw [hm]
          symm
          apply PullbackCone.IsLimit.lift_fst h
        · replace hm := hm =≫ biprod.snd
          dsimp at hm ⊢
          simp only [assoc, biprod.lift_snd] at hm
          rw [hm]
          symm
          apply PullbackCone.IsLimit.lift_snd h)
  invFun h :=
    PullbackCone.IsLimit.mk _
      (fun s ↦ h.lift (KernelFork.ofι (biprod.lift s.fst s.snd)
          (by simp [s.condition])))
      (fun s ↦ by simpa using h.fac (KernelFork.ofι (biprod.lift s.fst s.snd)
        (by simp [s.condition])) .zero =≫ biprod.fst)
      (fun s ↦ by simpa using h.fac (KernelFork.ofι (biprod.lift s.fst s.snd)
        (by simp [s.condition])) .zero =≫ biprod.snd)
      (fun s m hm₁ hm₂ ↦ by
        apply Fork.IsLimit.hom_ext h
        convert (h.fac (KernelFork.ofι (biprod.lift s.fst s.snd)
          (by simp [s.condition])) .zero).symm
        aesop_cat)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- The limit kernel fork attached to a pullback square. -/
noncomputable def IsPullback.isLimitKernelFork (h : IsPullback fst snd f g) :
    IsLimit h.kernelFork :=
  h.isLimitEquivIsLimitKernelFork h.isLimit

lemma IsPullback.mono_shortComplex'_f (h : IsPullback fst snd f g) :
    Mono h.shortComplex'.f := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro _ b hb
  exact Fork.IsLimit.hom_ext h.isLimitKernelFork (by simpa using hb)

end Pullback

end CategoryTheory
