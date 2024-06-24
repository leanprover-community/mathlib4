/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.CommSq

/-!
# Relation between mono/epi and pullback/pushout squares

In this file, monomorphisms and epimorphisms are characterized in terms
of pullback and pushout squares. For example, we obtain `mono_iff_isPullback`
which asserts that a morphism `f : X ⟶ Y` is a monomorphism iff the obvious
square

```
X ⟶ X
|   |
v   v
X ⟶ Y
```

is a pullback square.


-/

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y}

section Mono

variable {c : PullbackCone f f} (hc : IsLimit c)

lemma mono_iff_fst_eq_snd : Mono f ↔ c.fst = c.snd := by
  constructor
  · intro hf
    simpa only [← cancel_mono f] using c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hc g g' h
    rw [hf]

lemma mono_iff_isIso_fst : Mono f ↔ IsIso c.fst := by
  rw [mono_iff_fst_eq_snd hc]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PullbackCone.IsLimit.lift' hc (𝟙 X) (𝟙 X) (by simp)
    refine ⟨φ, PullbackCone.IsLimit.hom_ext hc ?_ ?_, hφ₁⟩
    · dsimp
      simp only [assoc, hφ₁, id_comp, comp_id]
    · dsimp
      simp only [assoc, hφ₂, id_comp, comp_id, h]
  · intro
    obtain ⟨φ, hφ₁, hφ₂⟩ := PullbackCone.IsLimit.lift' hc (𝟙 X) (𝟙 X) (by simp)
    have : IsSplitEpi φ := IsSplitEpi.mk ⟨SplitEpi.mk c.fst (by
      rw [← cancel_mono c.fst, assoc, id_comp, hφ₁, comp_id])⟩
    rw [← cancel_epi φ, hφ₁, hφ₂]

lemma mono_iff_isIso_snd : Mono f ↔ IsIso c.snd :=
  mono_iff_isIso_fst (PullbackCone.flipIsLimit hc)

variable (f)

lemma mono_iff_isPullback : Mono f ↔ IsPullback (𝟙 X) (𝟙 X) f f := by
  constructor
  · intro
    exact IsPullback.of_isLimit (PullbackCone.isLimitMkIdId f)
  · intro hf
    exact (mono_iff_fst_eq_snd hf.isLimit).2 rfl

end Mono

section Epi

variable {c : PushoutCocone f f} (hc : IsColimit c)

lemma epi_iff_inl_eq_inr : Epi f ↔ c.inl = c.inr := by
  constructor
  · intro hf
    simpa only [← cancel_epi f] using c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := PushoutCocone.IsColimit.desc' hc g g' h
    rw [hf]

lemma epi_iff_isIso_inl : Epi f ↔ IsIso c.inl := by
  rw [epi_iff_inl_eq_inr hc]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' hc (𝟙 Y) (𝟙 Y) (by simp)
    refine ⟨φ, hφ₁, PushoutCocone.IsColimit.hom_ext hc ?_ ?_⟩
    · dsimp
      simp only [comp_id, reassoc_of% hφ₁]
    · dsimp
      simp only [comp_id, h, reassoc_of% hφ₂]
  · intro
    obtain ⟨φ, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' hc (𝟙 Y) (𝟙 Y) (by simp)
    have : IsSplitMono φ := IsSplitMono.mk ⟨SplitMono.mk c.inl (by
      rw [← cancel_epi c.inl, reassoc_of% hφ₁, comp_id])⟩
    rw [← cancel_mono φ, hφ₁, hφ₂]

lemma epi_iff_isIso_inr : Epi f ↔ IsIso c.inr :=
  epi_iff_isIso_inl (PushoutCocone.flipIsColimit hc)

variable (f)

lemma epi_iff_isPushout : Epi f ↔ IsPushout f f (𝟙 Y) (𝟙 Y) := by
  constructor
  · intro
    exact IsPushout.of_isColimit (PushoutCocone.isColimitMkIdId f)
  · intro hf
    exact (epi_iff_inl_eq_inr hf.isColimit).2 rfl

end Epi

end CategoryTheory
