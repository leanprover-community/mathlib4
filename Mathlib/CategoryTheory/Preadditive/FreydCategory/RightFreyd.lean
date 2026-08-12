/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Preadditive.FreydCategory.Homotopy
public import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# The right Freyd category

Let `V` be a preadditive category. The right Freyd category of `V` is the quotient of
`Arrow V` by the right homotopy relation. (This is simply called "Freyd category"
in the reference.) This is a preadditive category with a fully
faithful additive functor `RightFreyd.functor : V ⥤ RightFreyd V`.

We also show that, if `V` has binary biproducts, then `RightFreyd V` has cokernels. In fact
we construct, given a morphism `f : u ⟶ v` in `Arrow V`, a morphism
`Candidate.π f : v ⟶ Candidate.cokernel f` in `Arrow V` such that
`f ≫ Candidate.π f` is right homotopic to `0` (see `Candidate.condition`).
This allows us to define a cokernel cofork for `(quotient V).map f` (see
`Candidate.cokernelCofork`), and we show in `Candidate.isColimitCokernelCofork` that this is
a cokernel cofork.

## References
* [Posur, S., *A constructive approach to Freyd categories*][posur2021Freyd]

-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Arrow

variable (V : Type*) [Category* V] [Preadditive V]

namespace CategoryTheory.Preadditive

/-- If `V` is a preadditive category, then `RightFreyd V` is the category of arrows in `V`,
with morphisms identified when they are right homotopic. -/
def RightFreyd :=
  CategoryTheory.Quotient (rightHomotopic V)

instance : Category (RightFreyd V) :=
  inferInstanceAs <| Category (CategoryTheory.Quotient (rightHomotopic V))

/-- The category `RightFreyd V` is preadditive. -/
instance : Preadditive (RightFreyd V) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨RightHomotopy.add h h'⟩)

namespace RightFreyd

/-- The quotient functor from `Arrow V` to `RightFreyd V`. -/
def quotient : Arrow V ⥤ RightFreyd V :=
  CategoryTheory.Quotient.functor _

instance : (quotient V).Full := Quotient.full_functor _

instance : (quotient V).EssSurj := Quotient.essSurj_functor _

instance : (quotient V).Additive where

variable {V}

/-- If two morphisms in `Arrow V` are right homotopic, then they become equal in the right
Freyd category. -/
theorem eq_of_rightHomotopy {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g) :
    (quotient V).map f = (quotient V).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- If two morphisms of `Arrow V` become equal in the right Freyd category,
then they are right homotopic. -/
def homotopyOfEq {u v : Arrow V} (f g : u ⟶ v)
    (w : (quotient V).map f = (quotient V).map g) : RightHomotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some

variable {u v : Arrow V} (f g : u ⟶ v)

/-- Two morphisms in `Arrow V` have the same image in `RightFreyd V` if and only if there
exists a right homotopy between them. -/
lemma quotient_map_eq_iff :
    (quotient V).map f = (quotient V).map g ↔ Nonempty (RightHomotopy f g) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_rightHomotopy _ _ h⟩

/-- A morphism `f` in `Arrow V` is sent to `0` in `RightFreyd V` if and only if there
exists a right homotopy between `f` and `0`. -/
lemma quotient_map_eq_zero_iff : (quotient V).map f = 0 ↔ Nonempty (RightHomotopy f 0) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_rightHomotopy _ _ h⟩

/-- If `f` is a morphism of `Arrow V` such that `f.right` is an isomorphism, then the image of `f`
in the right Freyd category is an epimorphism. -/
lemma epi_of_isIso_right [IsIso f.right] : Epi ((quotient V).map f) where
  left_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    set h : RightHomotopy (f ≫ g₁) (f ≫ g₂) := homotopyOfEq _ _ eq
    exact eq_of_rightHomotopy _ _ ⟨inv f.right ≫ h.hom, by simp [dsimp% h.comm]⟩

section Functor

variable [HasZeroObject V]

variable (V)

open ZeroObject in
set_option backward.defeqAttrib.useBackward true in
/-- If `V` has a zero object, this is the functor from `V` to `Arrow V`
that sends an object `X` to the arrow `0 ⟶ X`. -/
@[simps]
def rightFunctor : V ⥤ Arrow V where
  obj X := Arrow.mk (0 : 0 ⟶ X)
  map f := Arrow.homMk 0 f

set_option backward.defeqAttrib.useBackward true in
instance : (rightFunctor V).Additive where
  map_add {_ _ _ _} := by cat_disch

/-- The fully faithful additive functor from  `V` to `RightFreyd V` sending an object `X` of `V`
to the class of the arrow `0 ⟶ X`. -/
abbrev functor : V ⥤ RightFreyd V := rightFunctor V ⋙ quotient V

instance : (functor V).Additive := by dsimp [functor]; infer_instance

set_option backward.defeqAttrib.useBackward true in
instance : (functor V).Full where
  map_surjective a := by
    obtain ⟨u, rfl⟩ := (quotient V).map_surjective a
    exact ⟨u.right, (quotient V).congr_map (by cat_disch)⟩

set_option backward.defeqAttrib.useBackward true in
instance : (functor V).Faithful where
  map_injective {_ _} f g eq := by
    dsimp at eq
    rw [quotient_map_eq_iff] at eq
    simpa [← sub_eq_zero] using! eq.some.comm

end Functor

variable [HasBinaryBiproducts V]

variable {u v : Arrow V} (f : u ⟶ v)

namespace Candidate

/-- If `f` is a morphism of `Arrow V`, this is a "candidate cokernel" of `f`, i.e. an object
in `Arrow V` whose image in `RightFreyd V` will be a cokernel of the image of `f`. -/
abbrev cokernel := Arrow.mk (biprod.desc v.hom f.right)

set_option backward.isDefEq.respectTransparency false in
/-- For `f : u ⟶ v` a morphism in `Arrow V`, this is the morphism `v ⟶ cokernel f` from `v` to
the "candidate cokernel" of `f`, whose image in `RightFreyd V` will be the projection to
the cokernel of the image of `f`. -/
def π : v ⟶ cokernel f := Arrow.homMk biprod.inl (𝟙 v.right)

set_option backward.isDefEq.respectTransparency false in
/-- The right homotopy expressing that `f ≫ π f` is sent to `0` in `RightFreyd V`. -/
def condition : RightHomotopy (f ≫ π f) 0 where
  hom := biprod.inr
  comm := by simp [π]

set_option backward.isDefEq.respectTransparency false in
instance : Epi ((quotient V).map (π f)) :=
  have : IsIso ((π f).right) := by simp only [π, homMk_right]; infer_instance
  epi_of_isIso_right _

variable {w : Arrow V} (g : v ⟶ w) (h : RightHomotopy (f ≫ g) 0)

set_option backward.isDefEq.respectTransparency false in
/-- If `f : u ⟶ v` and `g : v ⟶ w` are morphisms in `Arrow V` such that `f ≫ g` is right
homotopic to `0`, this is the morphism from the "candidate cokernel" of `f` to `w` defined
from the right homotopy. -/
def desc : cokernel f ⟶ w :=
  Arrow.homMk (biprod.desc g.left h.hom) g.right (biprod.hom_ext' _ _ (by simp)
    (by simp [← h.comm]))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma π_desc : π f ≫ desc f g h = g := by ext <;> simp [π, desc]

/-- For `f` a morphism in `Arrow V`, this is a cokernel cofork of `(quotient V).map f`. -/
def cokernelCofork : CokernelCofork ((quotient V).map f) :=
  CokernelCofork.ofπ ((quotient V).map (Candidate.π f))
    (eq_of_rightHomotopy _ _ (Candidate.condition f))

set_option backward.isDefEq.respectTransparency false in
/-- For `f` a morphism in `Arrow V`, the cokernel cofork of `(quotient V).map f` constructed
in `cokernelCofork` is a colimit cofork. -/
def isColimitCokernelCofork : IsColimit (cokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ' _
    (eq_of_rightHomotopy _ _ (Candidate.condition f))
    (fun g hg ↦ Nonempty.some (by
      obtain ⟨g, rfl⟩ := (quotient V).map_surjective g
      exact ⟨(quotient V).map (desc f g (homotopyOfEq _ _ hg)),
        by simp [← Functor.map_comp]⟩))

end Candidate

/-- The category `RightFreyd V` has all cokernels if `V` has binary biproducts. -/
instance : HasCokernels (RightFreyd V) where
  has_colimit f := ⟨by
    obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
    exact ⟨_, Candidate.isColimitCokernelCofork f⟩⟩

end RightFreyd

end CategoryTheory.Preadditive
