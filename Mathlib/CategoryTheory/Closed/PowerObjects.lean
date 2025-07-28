/-
Copyright (c) 2025 Klaus Gy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Klaus Gy
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Topos.Classifier
/-!
# Elementary Topos (in Elementary Form)

This ongoing work formalizes the elementary definition of a topos and the direct consequences.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/

universe u v

open CategoryTheory Category Functor Limits MonoidalCategory Opposite

variable {ℰ : Type u} [Category.{v} ℰ] [CartesianMonoidalCategory ℰ]

/-- The covariant functor `B ⊗ [] ⟶ C` from `ℰᵒᵖ` to `Type`. -/
def WhiskeredHom (B C : ℰ) : ℰᵒᵖ ⥤ Type v :=
  ⟨ ⟨ fun A ↦ B ⊗ unop A ⟶ C, fun f g ↦ (B ◁ unop f) ≫ g ⟩,
    fun A ↦ by
      have : unop (𝟙 A) = 𝟙 (unop A) := by rfl
      ext; simp[this],
    fun f f' ↦ by
      have : B ◁ unop (f ≫ f') = B ◁ unop f' ≫ B ◁ unop f := by aesop_cat
      ext; simp[this] ⟩

/-- `P` is a power object of `B` if it represents the functor `WhiskeredHom B hc.Ω`. -/
def IsPowerObjectOf (sc : Classifier ℰ (𝟙_ ℰ)) (B P : ℰ) :=
  (WhiskeredHom B sc.Ω).RepresentableBy P

namespace PowerObject

variable {sc : Classifier ℰ (𝟙_ ℰ)} {B PB : ℰ} (hPB : IsPowerObjectOf sc B PB)

/-- The P-transpose of a morphism `g : A ⟶ P B`. -/
def hat {A : ℰ} (g : A ⟶ PB) : B ⊗ A ⟶ sc.Ω :=
  hPB.homEquiv.toFun g

/-- The P-transpose of a morphism `f : B × A ⟶ Ω`. -/
def unhat {A : ℰ} (f : B ⊗ A ⟶ sc.Ω) : (A ⟶ PB) :=
  hPB.homEquiv.invFun f

@[simp]
lemma hat_unhat {A : ℰ} (f : B ⊗ A ⟶ sc.Ω) :
  hat hPB (unhat hPB f) = f := hPB.homEquiv.apply_symm_apply f

@[simp]
lemma unhat_hat {A : ℰ} (g : A ⟶ PB) :
  unhat hPB (hat hPB g) = g := hPB.homEquiv.symm_apply_apply g

/-- The element relation as a subobject of `B ⨯ (P B)`. -/
def ε : B ⊗ (PB) ⟶ sc.Ω := hPB.homEquiv.toFun (𝟙 (PB))

lemma hatAsComp {A : ℰ} (g : A ⟶ PB) : hat hPB g = B ◁ g ≫ ε hPB := hPB.homEquiv_eq g

@[simp]
lemma comm {A : ℰ} (f : B ⊗ A ⟶ sc.Ω) : B ◁ (unhat hPB f) ≫ ε hPB = f := by
  have : hPB.homEquiv (unhat hPB f) = f := by unfold unhat; simp
  simpa [this] using Eq.symm (RepresentableBy.homEquiv_eq hPB (unhat hPB f))

lemma uniq {A : ℰ} (f : B ⊗ A ⟶ sc.Ω) (g : A ⟶ PB)
    (h : f = B ◁ g ≫ ε hPB) : g = unhat hPB f := by
  have : hat hPB g = f := by rw [← comm hPB (hat hPB g)]; simp [h]
  simpa using congr(unhat hPB $this)

variable {C PC : ℰ} (hPC : IsPowerObjectOf sc C PC)

/-- The morphism `map h` is the functorial action on a morphism `h : B ⟶ C`,
    defined as the P-transpose of `εC ∘ (h ⨯ 𝟙)`. -/
def map (h : B ⟶ C) : PC ⟶ PB := unhat hPB ((h ▷ PC) ≫ ε hPC)

/-- Naturality (dinaturality) of `ε`. This corresponds to the naturality square of ε
    in MM92 diagram (5). -/
lemma dinaturality (h : B ⟶ C) : h ▷ PC ≫ ε hPC = B ◁ map hPB hPC h ≫ ε hPB :=
  Eq.symm (comm hPB _)

/-- `P` covariantly preserves composition, shown by stacking dinaturality squares. -/
lemma compose {D PD : ℰ} (hPD : IsPowerObjectOf sc D PD) (h : B ⟶ C) (h' : C ⟶ D) :
    map hPB hPD (h ≫ h') = map hPC hPD h' ≫ map hPB hPC h := by
  let comm_outer : h ▷ PD ≫ h' ▷ PD ≫ ε hPD =
      B ◁ (map _ _ h') ≫ B ◁ (map _ _ h) ≫ ε _ := by
    rw [dinaturality hPC hPD, ← reassoc_of% whisker_exchange h, dinaturality hPB hPC]
  rw [map]; simp
  rw[comm_outer, ← uniq _ _ (map hPC hPD h' ≫ map hPB hPC h) (by aesop_cat)]

/-- A function `P` assigning power objects, turns into a functor `P : ℰᵒᵖ ⥤ ℰ`. -/
def functor (P : ℰ → ℰ) (hP : ∀ B : ℰ, IsPowerObjectOf sc B (P B)) : ℰᵒᵖ ⥤ ℰ :=
    { obj B := P B.unop,
      map {B C} (h : B ⟶ C) := map (hP C.unop) (hP B.unop) h.unop,
      map_id _ := Eq.symm (uniq (hP _) _ _ (by simp)),
      map_comp {B C D} _ _ := compose (hP D.unop) (hP C.unop) (hP B.unop) _ _ }

end PowerObject
