/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.FintypeCat

/-!
# `Over S` when `S : FintypeCat`

-/

-- to be moved

@[expose] public section

universe w v u

open CategoryTheory

namespace FintypeCat

variable {S : FintypeCat.{w}} (s : S)

/-- Given `S : FintypeCat` and `s : S`, this is the functor `Over S ⥤ FintypeCat`
which sends `f : X ⟶ S` to `f ⁻¹' {s}`. -/
@[implicit_reducible, simps]
def overFiber : Over S ⥤ FintypeCat.{w} where
  obj X := of (X.hom ⁻¹' {s})
  map f := homMk (fun x ↦ ⟨f.left x, by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff,
      ← ConcreteCategory.comp_apply, f.w] using x.prop⟩)

/-- The left adjoint to `FintypeCat.overFiber`. -/
@[implicit_reducible, simps]
def overFiberLeftAdjoint : FintypeCat.{w} ⥤ Over S where
  obj Y := Over.mk (Y := Y) (homMk (fun _ ↦ s))
  map f := Over.homMk f

/-- The functor `FintypeCat.overFiber` has a left adjoint. -/
def overFiberLeftAdjunction :
    overFiberLeftAdjoint s ⊣ overFiber s where
  unit.app Y := homMk (fun y ↦ ⟨y, by simp⟩)
  counit.app X := Over.homMk (homMk (fun x ↦ x.val))
    (by ext ⟨_, _⟩; simpa)


/-- The right adjoint to `FintypeCat.overFiber`. -/
@[implicit_reducible, simps]
def overFiberRightAdjoint : FintypeCat.{w} ⥤ Over S where
  obj X :=
    Over.mk (Y := of (Σ (t : S), (Subtype.val (p := (· ∈ Set.singleton s))) ⁻¹' {t} → X))
      (homMk Sigma.fst)
  map f := Over.homMk (homMk (fun ⟨t, g⟩ ↦ ⟨t, f ∘ g⟩))

private lemma overFiberRightAdjunction_obj_left_ext_iff (X : FintypeCat.{w})
    (a b : Σ (t : S), (Subtype.val (p := (· ∈ Set.singleton s))) ⁻¹' {t} → X) :
    a = b ↔ ∃ (h : a.1 = b.1),
      ∀ (h' : a.1 = s), a.2 ⟨⟨s, by aesop⟩, by aesop⟩ = b.2 ⟨⟨s, by aesop⟩, by aesop⟩ := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨rfl, fun _ ↦ rfl⟩
  · rintro ⟨eq, h⟩
    obtain ⟨a, a'⟩ := a
    obtain ⟨b, b'⟩ := b
    obtain rfl : a = b := eq
    obtain rfl : a' = b' := by ext ⟨⟨t, rfl⟩, rfl⟩; exact h rfl
    rfl

/-- The functor `FintypeCat.overFiber` has a right adjoint. -/
def overFiberRightAdjunction :
    overFiber s ⊣ overFiberRightAdjoint s where
  unit.app X :=
    Over.homMk (homMk (fun x ↦ ⟨X.hom x, fun h ↦ ⟨x, by aesop⟩⟩)) (by aesop)
  unit.naturality X X' f := by
    ext x
    rw [overFiberRightAdjunction_obj_left_ext_iff]
    exact ⟨ConcreteCategory.congr_hom f.w x, fun _ ↦ rfl⟩
  counit.app Y :=
    homMk (fun y ↦ y.val.2 ⟨⟨s, Set.mem_singleton _⟩, y.prop.symm⟩)
  right_triangle_components X := by
    ext ⟨x, hx⟩
    rw [overFiberRightAdjunction_obj_left_ext_iff]
    exact ⟨rfl, fun _ ↦ rfl⟩

instance : (overFiber s).IsRightAdjoint :=
  (overFiberLeftAdjunction s).isRightAdjoint

instance : (overFiber s).IsLeftAdjoint :=
  (overFiberRightAdjunction s).isLeftAdjoint

instance : SplitEpiCategory FintypeCat.{w} where
  isSplitEpi_of_epi f hf := by
    replace hf : Function.Surjective f := by
      change Function.Surjective (FintypeCat.incl.map f)
      rw [← CategoryTheory.epi_iff_surjective]
      infer_instance
    exact ⟨⟨ SplitEpi.mk (FintypeCat.homMk (Function.surjInv hf)) (by
      ext x
      simp [Function.rightInverse_surjInv hf x])⟩⟩

end FintypeCat
