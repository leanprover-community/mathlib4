/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Preadditive.Comma

/-!
# Homotopies in the arrow category

We define left and right homotopies between morphisms of `Arrow V`, where `V` is
a preadditive category.

TODO: Define the preadditive categories `LeftFreyd V` (resp. `RightFreyd V`) obtained by
taking the quotient of `Arrow V` by the left (resp. right) homotopy relation. If `V`
has binary biproducts, this will have all kernels (resp. cokernels) and will be the
category obtained by freely adjoining kernels (resp. cokernels) to `V`.

-/

@[expose] public section

noncomputable section

open CategoryTheory Category

variable {V : Type*} [Category* V] [Preadditive V]

namespace CategoryTheory.Arrow

variable {u v w : Arrow V} (f g : u ⟶ v)

/-- A left homotopy on morphisms in the category of arrows of a preadditive category. -/
@[ext]
structure LeftHomotopy where
/-- A "diagonal" morphism from the right object of `u` to the left object of `v`. -/
  hom : u.right ⟶ v.left
/-- The difference of the left morphisms factors through `hom`. -/
  comm : f.left - g.left = u.hom ≫ hom := by cat_disch

/-- A right homotopy on morphisms in the category of arrows of a preadditive category. -/
@[ext]
structure RightHomotopy where
  /-- A "diagonal" morphism from the right object of `u` to the left object of `v`. -/
  hom : u.right ⟶ v.left
  /-- The difference of the right morphisms factors through `hom`. -/
  comm : f.right - g.right = hom ≫ v.hom := by cat_disch

variable {f g}

namespace LeftHomotopy

/-- `f` is left homotopic to `g` iff `f - g` is left homotopic to `0`. -/
def equivSubZero : LeftHomotopy f g ≃ LeftHomotopy (f - g) 0 where
  toFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  invFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Equal maps of arrows are left homotopic. -/
@[simps]
def ofEq (h : f = g) : LeftHomotopy f g where
  hom := 0

/-- Every map of arrows is left homotopic to itself. -/
@[simps!, refl]
def refl (f : u ⟶ v) : LeftHomotopy f f :=
  ofEq (rfl : f = f)

/-- `f` is left homotopic to `g` iff `g` is left homotopic to `f`. -/
@[simps!, symm]
def symm {f g : u ⟶ v} (h : LeftHomotopy f g) : LeftHomotopy g f where
  hom := -h.hom
  comm := by simp [← h.comm]

/-- Left homotopy is a transitive relation. -/
@[simps!, trans]
def trans {e f g : u ⟶ v} (h : LeftHomotopy e f) (k : LeftHomotopy f g) : LeftHomotopy e g where
  hom := h.hom + k.hom
  comm := by simp [← h.comm, ← k.comm]

/-- The sum of two left homotopies is a left homotopy between the sum of the respective
morphisms. -/
@[simps!]
def add {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : LeftHomotopy f₁ g₁) (h₂ : LeftHomotopy f₂ g₂) :
    LeftHomotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  comm := by simp [← h₁.comm, ← h₂.comm, add_sub_add_comm]

/-- Left homotopy is closed under composition (on the right). -/
@[simps]
def compRight {e f : u ⟶ v} (h : LeftHomotopy e f) (g : v ⟶ w) :
    LeftHomotopy (e ≫ g) (f ≫ g) where
  hom := h.hom ≫ g.left
  comm := by simp [← reassoc_of% h.comm]

/-- Left homotopy is closed under composition (on the left). -/
@[simps]
def compLeft {f g : v ⟶ w} (h : LeftHomotopy f g) (e : u ⟶ v) :
    LeftHomotopy (e ≫ f) (e ≫ g) where
  hom := e.right ≫ h.hom
  comm := by simp [← reassoc_of% e.w, ← h.comm]

/-- Left homotopy is closed under composition. -/
@[simps!]
def comp {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w}
    (h₁ : LeftHomotopy f₁ g₁) (h₂ : LeftHomotopy f₂ g₂) : LeftHomotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight _).trans (h₂.compLeft _)

/-- A variant of `LeftHomotopy.compRight` useful for dealing with homotopy equivalences. -/
@[simps!]
def compRightId {f : u ⟶ u} (h : LeftHomotopy f (𝟙 u)) (g : u ⟶ v) : LeftHomotopy (f ≫ g) g :=
  (h.compRight g).trans (ofEq <| id_comp _)

/-- A variant of `LeftHomotopy.compLeft` useful for dealing with homotopy equivalences. -/
@[simps!]
def compLeftId {f : v ⟶ v} (h : LeftHomotopy f (𝟙 v)) (g : u ⟶ v) : LeftHomotopy (g ≫ f) g :=
  (h.compLeft g).trans (ofEq <| comp_id _)

end LeftHomotopy

namespace RightHomotopy

/-- `f` is right homotopic to `g` iff `f - g` is righthomotopic to `0`. -/
def equivSubZero : RightHomotopy f g ≃ RightHomotopy (f - g) 0 where
  toFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  invFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Equal maps of arrows are right homotopic. -/
@[simps]
def ofEq (h : f = g) : RightHomotopy f g where
  hom := 0

/-- Every map of arrows is right homotopic to itself. -/
@[simps!, refl]
def refl (f : u ⟶ v) : RightHomotopy f f :=
  ofEq (rfl : f = f)

/-- `f` is right homotopic to `g` iff `g` is right homotopic to `f`. -/
@[simps!, symm]
def symm {f g : u ⟶ v} (h : RightHomotopy f g) : RightHomotopy g f where
  hom := -h.hom
  comm := by simp [← h.comm]

/-- Right homotopy is a transitive relation. -/
@[simps!, trans]
def trans {e f g : u ⟶ v} (h : RightHomotopy e f) (k : RightHomotopy f g) : RightHomotopy e g where
  hom := h.hom + k.hom
  comm := by simp [← h.comm, ← k.comm]

/-- The sum of two right homotopies is a right homotopy between the sum of the respective
morphisms. -/
@[simps!]
def add {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : RightHomotopy f₁ g₁) (h₂ : RightHomotopy f₂ g₂) :
    RightHomotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  comm := by simp [← h₁.comm, ← h₂.comm, add_sub_add_comm]

/-- Right homotopy is closed under composition (on the right). -/
@[simps]
def compRight {e f : u ⟶ v} (h : RightHomotopy e f) (g : v ⟶ w) :
    RightHomotopy (e ≫ g) (f ≫ g) where
  hom := h.hom ≫ g.left
  comm := by simp [← reassoc_of% h.comm]

/-- Right homotopy is closed under composition (on the left). -/
@[simps]
def compLeft {f g : v ⟶ w} (h : RightHomotopy f g) (e : u ⟶ v) :
    RightHomotopy (e ≫ f) (e ≫ g) where
  hom := e.right ≫ h.hom
  comm := by simp [← h.comm]

/-- Right homotopy is closed under composition. -/
@[simps!]
def comp {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w}
    (h₁ : RightHomotopy f₁ g₁) (h₂ : RightHomotopy f₂ g₂) : RightHomotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight _).trans (h₂.compLeft _)

/-- A variant of `RightHomotopy.compRight` useful for dealing with homotopy equivalences. -/
@[simps!]
def compRightId {f : u ⟶ u} (h : RightHomotopy f (𝟙 u)) (g : u ⟶ v) : RightHomotopy (f ≫ g) g :=
  (h.compRight g).trans (ofEq <| id_comp _)

/-- A variant of `RightHomotopy.compLeft` useful for dealing with homotopy equivalences. -/
@[simps!]
def compLeftId {f : v ⟶ v} (h : RightHomotopy f (𝟙 v)) (g : u ⟶ v) : RightHomotopy (g ≫ f) g :=
  (h.compLeft g).trans (ofEq <| comp_id _)

end RightHomotopy

variable (V)

/-- The left homotopy relation on morphisms of `Arrow V`. -/
def leftHomotopic : HomRel (Arrow V) := fun _ _ f g => Nonempty (LeftHomotopy f g)

instance leftHomotopy_congruence : Congruence (leftHomotopic V) where
  equivalence :=
    { refl := fun C => ⟨LeftHomotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

/-- The left homotopy relation on morphisms of `Arrow V`. -/
def rightHomotopic : HomRel (Arrow V) := fun _ _ f g => Nonempty (RightHomotopy f g)

instance rightHomotopy_congruence : Congruence (rightHomotopic V) where
  equivalence :=
    { refl := fun C => ⟨RightHomotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

end CategoryTheory.Arrow
