/-
Copyright (c) 2025 Klaus Gy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Klaus Gy
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Topos.Classifier
/-!
# Elementary Topos (in Elementary Form)

This ongoing work formalizes the elementary definition of a topos and the direct consequences.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/

universe u v

open CategoryTheory
open CartesianMonoidalCategory Functor Limits MonoidalCategory Opposite

variable {ℰ : Type u} [Category.{v} ℰ] [CartesianMonoidalCategory ℰ]

private lemma isPullback_equalizer_prod' {X Y : ℰ}
      (f g : X ⟶ Y) {e : Fork f g} (he : IsLimit e) :
    IsPullback e.ι (e.ι ≫ f) (lift f g) (CartesianMonoidalCategory.diag Y) :=
  isPullback_equalizer_prod_exp _ f g _ he

private lemma pullback_of_diag {B X : ℰ} (b : X ⟶ B) :
    IsPullback b (lift b (𝟙 X)) (CartesianMonoidalCategory.diag B) (B ◁ b) :=
  let eq : lift b (𝟙 X) ≫ fst B X = lift b (𝟙 X) ≫ snd B X ≫ b := by simp
  let lim : IsLimit (Fork.ofι (lift b (𝟙 X)) eq) :=
    Fork.IsLimit.mk _
      (fun s => s.ι ≫ (snd B X))
      (fun s => by simp[← s.condition])
      (fun s m eq => by simp[← eq])
  IsPullback.flip
    (by simpa using isPullback_equalizer_prod' (fst B X) (snd B X ≫ b) lim)

variable [HasPullbacks ℰ]

noncomputable def subobjTensorLeft (B : ℰ) : ℰᵒᵖ ⥤ Type (max u v) where
  obj A := Subobject (B ⊗ unop A)
  map f := (Subobject.pullback (B ◁ unop f)).obj
  map_id A := by
    ext1 x
    simp [show unop (𝟙 A) = 𝟙 (unop _) from rfl, Subobject.pullback_id]
  map_comp f f' := by
    ext1 x
    simp [show unop (f ≫ f') = unop f' ≫ unop f from rfl, Subobject.pullback_comp]

/-- `P` is a power object of `B` if it represents the functor `WhiskeredHom B hc.Ω`. -/
def IsPowerObjectOf (B P : ℰ) :=
  (subobjTensorLeft B).RepresentableBy P

namespace PowerObject

variable {B PB : ℰ} (hPB : IsPowerObjectOf B PB)

def diagSubobject (B : ℰ) := Subobject.mk (CartesianMonoidalCategory.diag B)

/-- The singleton morphism from `B` to `PB`. -/
def singleton : B ⟶ PB :=
  hPB.homEquiv.invFun (diagSubobject B)

noncomputable instance singleton_is_mono : Mono (singleton hPB) :=
  ⟨ fun {X} (f f' : X ⟶ B) eq ↦ by
    let P : Subobject (B ⊗ X) := hPB.homEquiv (f ≫ singleton hPB)
    let P' : Subobject (B ⊗ X) := hPB.homEquiv (f' ≫ singleton hPB)
    have : P = P' := by unfold P; rw[eq]
    have : P = (Subobject.pullback (B ◁ f)).obj (diagSubobject B) := sorry
    have : P = (subobjTensorLeft B).map f.op (diagSubobject B) := by
      unfold P; rw[hPB.homEquiv_comp f (singleton hPB)]; unfold singleton; simp

    sorry ⟩

variable {C PC : ℰ} (hPC : IsPowerObjectOf C PC)

/-- The morphism `map h` is the functorial action on a morphism `h : B ⟶ C`,
    defined as the P-transpose of `εC ∘ (h ⨯ 𝟙)`. -/
def map (h : B ⟶ C) : PC ⟶ PB := hPB.homEquiv.invFun (Subobject.mk ((𝟙 B) ⊗ₘ (singleton hPB)))

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
