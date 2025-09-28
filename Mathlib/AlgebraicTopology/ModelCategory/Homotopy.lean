/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy

/-!
# Homotopies in model categories

In this file, we relate left and right homotopies between
morphisms `X ⟶ Y` in model categories. In particular, if `X` is cofibrant
and `Y` is fibrant, these notions coincide (for arbitrary choices of good
cylinders or good path objects).

Using the factorization lemma by K. S. Brown, we deduce versions of the Whitehead
theorem (`LeftHomotopyClass.whitehead` and `RightHomotopyClass.whitehead`)
which assert that when both `X` and `Y` are fibrant and cofibrant,
then any weak equivalence `X ⟶ Y` is a homotopy equivalence.

## References
* [Daniel G. Quillen, Homotopical algebra, section I.1][Quillen1967]

-/

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y Z : C}

namespace LeftHomotopyRel

variable {f g : X ⟶ Y} [IsCofibrant X]

/-- When two morphisms `X ⟶ Y` with `X` cofibrant are related by a left homotopy,
this is a choice of a right homotopy relative to any good path object for `Y`. -/
noncomputable def rightHomotopy (h : LeftHomotopyRel f g) (Q : PathObject Y) [Q.IsGood] :
    Q.RightHomotopy f g :=
  let P := h.exists_good_cylinder.choose
  have h := h.exists_good_cylinder.choose_spec.2.some
  have h' := h.exists_good_cylinder.choose_spec.1
  have sq : CommSq (f ≫ Q.ι) P.i₀ Q.p (prod.lift (P.π ≫ f) h.h) := { }
  { h := P.i₁ ≫ sq.lift
    h₀ := by
      have := sq.fac_right =≫ prod.fst
      rw [Category.assoc, Q.p_fst, prod.lift_fst] at this
      simp [this]
    h₁ := by
      have := sq.fac_right =≫ prod.snd
      rw [Category.assoc, Q.p_snd, prod.lift_snd] at this
      simp [this] }

lemma rightHomotopyRel (h : LeftHomotopyRel f g) : RightHomotopyRel f g := by
  obtain ⟨P, _⟩ := PathObject.exists_very_good Y
  exact ⟨_, ⟨h.rightHomotopy P⟩⟩

end LeftHomotopyRel

namespace RightHomotopyRel

variable {f g : X ⟶ Y} [IsFibrant Y]

/-- When two morphisms `X ⟶ Y` with `Y` fibrant are related by a right homotopy,
this is a choice of a left homotopy relative to any good cylinder object for `X`. -/
noncomputable def leftHomotopy (h : RightHomotopyRel f g) (Q : Cylinder X) [Q.IsGood] :
    Q.LeftHomotopy f g :=
  let P := h.exists_good_pathObject.choose
  have h := h.exists_good_pathObject.choose_spec.2.some
  have h' := h.exists_good_pathObject.choose_spec.1
  have sq : CommSq (coprod.desc (f ≫ P.ι) h.h) Q.i P.p₀ (Q.π ≫ f) := { }
  { h := sq.lift ≫ P.p₁
    h₀ := by
      have := coprod.inl ≫= sq.fac_left
      rw [Q.inl_i_assoc, coprod.inl_desc] at this
      simp [reassoc_of% this]
    h₁ := by
      have := coprod.inr ≫= sq.fac_left
      rw [Q.inr_i_assoc, coprod.inr_desc] at this
      simp [reassoc_of% this, P] }

lemma leftHomotopyRel (h : RightHomotopyRel f g) : LeftHomotopyRel f g := by
  obtain ⟨P, _⟩ := Cylinder.exists_very_good X
  exact ⟨P, ⟨h.leftHomotopy P⟩⟩

end RightHomotopyRel

lemma leftHomotopyRel_iff_rightHomotopyRel {X Y : C} (f g : X ⟶ Y)
    [IsCofibrant X] [IsFibrant Y] :
    LeftHomotopyRel f g ↔ RightHomotopyRel f g :=
  ⟨fun h ↦ h.rightHomotopyRel, fun h ↦ h.leftHomotopyRel⟩

namespace LeftHomotopyClass

variable (X)

lemma postcomp_bijective_of_fibration_of_weakEquivalence
    [IsCofibrant X] (g : Y ⟶ Z) [Fibration g] [WeakEquivalence g] :
    Function.Bijective (fun (f : LeftHomotopyClass X Y) ↦ f.postcomp g) := by
  constructor
  · intro f₀ f₁ h
    obtain ⟨f₀, rfl⟩ := f₀.mk_surjective
    obtain ⟨f₁, rfl⟩ := f₁.mk_surjective
    simp only [postcomp_mk, mk_eq_mk_iff] at h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_cylinder
    have sq : CommSq (coprod.desc f₀ f₁) P.i g h.h := { }
    rw [mk_eq_mk_iff]
    exact ⟨P,
      ⟨{h := sq.lift
        h₀ := by
          have := coprod.inl ≫= sq.fac_left
          rwa [P.inl_i_assoc, coprod.inl_desc] at this
        h₁ := by
          have := coprod.inr ≫= sq.fac_left
          rwa [P.inr_i_assoc, coprod.inr_desc] at this }⟩⟩
  · intro φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    have sq : CommSq (initial.to Y) (initial.to X) g φ := { }
    exact ⟨mk sq.lift, by simp⟩

lemma postcomp_bijective_of_weakEquivalence
    [IsCofibrant X] (g : Y ⟶ Z) [IsFibrant Y] [IsFibrant Z] [WeakEquivalence g] :
    Function.Bijective (fun (f : LeftHomotopyClass X Y) ↦ f.postcomp g) := by
  let h : FibrantBrownFactorization g := Classical.arbitrary _
  have hi : Function.Bijective (fun (f : LeftHomotopyClass X Y) ↦ f.postcomp h.i) := by
    rw [← Function.Bijective.of_comp_iff'
      (postcomp_bijective_of_fibration_of_weakEquivalence X h.r)]
    convert Function.bijective_id
    ext φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    simp
  convert (postcomp_bijective_of_fibration_of_weakEquivalence X h.p).comp hi using 1
  ext φ
  obtain ⟨φ, rfl⟩ := φ.mk_surjective
  simp

end LeftHomotopyClass

namespace RightHomotopyClass

variable (Z)

lemma precomp_bijective_of_cofibration_of_weakEquivalence
    [IsFibrant Z] (f : X ⟶ Y) [Cofibration f] [WeakEquivalence f] :
    Function.Bijective (fun (g : RightHomotopyClass Y Z) ↦ g.precomp f) := by
  constructor
  · intro f₀ f₁ h
    obtain ⟨f₀, rfl⟩ := f₀.mk_surjective
    obtain ⟨f₁, rfl⟩ := f₁.mk_surjective
    simp only [precomp_mk, mk_eq_mk_iff] at h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_pathObject
    have sq : CommSq h.h f P.p (prod.lift f₀ f₁) := { }
    rw [mk_eq_mk_iff]
    exact ⟨P,
      ⟨{h := sq.lift
        h₀ := by
          have := sq.fac_right =≫ prod.fst
          rwa [Category.assoc, P.p_fst, prod.lift_fst] at this
        h₁ := by
          have := sq.fac_right =≫ prod.snd
          rwa [Category.assoc, P.p_snd, prod.lift_snd] at this }⟩⟩
  · intro φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    have sq : CommSq φ f (terminal.from _) (terminal.from _) := { }
    exact ⟨mk sq.lift, by simp⟩

lemma precomp_bijective_of_weakEquivalence
    [IsFibrant Z] (f : X ⟶ Y) [IsCofibrant X] [IsCofibrant Y] [WeakEquivalence f] :
    Function.Bijective (fun (g : RightHomotopyClass Y Z) ↦ g.precomp f) := by
  let h : CofibrantBrownFactorization f := Classical.arbitrary _
  have hj : Function.Bijective (fun (g : RightHomotopyClass Y Z) ↦ g.precomp h.p) := by
    rw [← Function.Bijective.of_comp_iff'
      (precomp_bijective_of_cofibration_of_weakEquivalence Z h.s)]
    convert Function.bijective_id
    ext φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    simp
  convert (precomp_bijective_of_cofibration_of_weakEquivalence Z h.i).comp hj using 1
  ext φ
  obtain ⟨φ, rfl⟩ := φ.mk_surjective
  simp

lemma whitehead [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] :
    ∃ (g : Y ⟶ X), RightHomotopyRel (f ≫ g) (𝟙 X) ∧ RightHomotopyRel (g ≫ f) (𝟙 Y) := by
  obtain ⟨g, hg⟩ := (precomp_bijective_of_weakEquivalence X f).2 (.mk (𝟙 X))
  obtain ⟨g, rfl⟩ := g.mk_surjective
  dsimp at hg
  refine ⟨g, by rwa [← mk_eq_mk_iff], ?_⟩
  rw [← mk_eq_mk_iff]
  apply (precomp_bijective_of_weakEquivalence Y f).1
  simp only [precomp_mk, Category.comp_id]
  rw [mk_eq_mk_iff, ← leftHomotopyRel_iff_rightHomotopyRel] at hg ⊢
  simpa using hg.postcomp f

end RightHomotopyClass

lemma LeftHomotopyClass.whitehead [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] :
    ∃ (g : Y ⟶ X), LeftHomotopyRel (f ≫ g) (𝟙 X) ∧ LeftHomotopyRel (g ≫ f) (𝟙 Y) := by
  simp only [leftHomotopyRel_iff_rightHomotopyRel]
  apply RightHomotopyClass.whitehead

section

variable [IsCofibrant X] [IsFibrant Y]

/-- Left homotopy classes of maps `X ⟶ Y` identify to right homotopy classes
when `X` is cofibrant and `Y` is fibrant. -/
def leftHomotopyClassEquivRightHomotopyClass :
    LeftHomotopyClass X Y ≃ RightHomotopyClass X Y where
  toFun := Quot.lift (fun f ↦ .mk f) (fun _ _ h ↦ by
    dsimp
    rw [RightHomotopyClass.mk_eq_mk_iff]
    exact h.rightHomotopyRel)
  invFun := Quot.lift (fun f ↦ .mk f) (fun _ _ h ↦ by
    dsimp
    rw [LeftHomotopyClass.mk_eq_mk_iff]
    exact h.leftHomotopyRel)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]
lemma leftHomotopyClassEquivRightHomotopyClass_mk (f : X ⟶ Y) :
    leftHomotopyClassEquivRightHomotopyClass (.mk f) = .mk f := rfl

@[simp]
lemma leftHomotopyClassEquivRightHomotopyClass_symm_mk (f : X ⟶ Y) :
    leftHomotopyClassEquivRightHomotopyClass.symm (.mk f) = .mk f := rfl

end

end HomotopicalAlgebra
