/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Preadditive.FreydCategory.Homotopy
public import Mathlib.CategoryTheory.Quotient.Preadditive
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Limits.Comma

/-!
# The right Freyd category

Let `V` be a preadditive category. The right Freyd category `RightFreyd V` of `V` is the quotient
of `Arrow V` by the right homotopy relation. This is a preadditive category with a fully
faithful additive functor `RightFreyd.functor : V ⥤ RightFreyd V`.

We also show that, if `V` has finite products, then `RightFreyd V` has cokernels. In fact
we construct, given a morphism `f : u ⟶ v` in `Arrow V`, a morphism
`CandidateCokernel.π f : v ⟶ CandidateCokernel.cokernel f` in `Arrow V` such that
`f ≫ CandidateCokernel.π f` is right homotopic to `0`. This allows us to define a
cokernel cofork for `(quotient V).map f` (see `CandidateCokernelCofork`), and we show
in `candidateCokernelCoforkIsCokernel` that this is a cokernel cofork.

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
lemma isEpi_of_right_iso [IsIso f.right] : Epi ((quotient V).map f) where
  left_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    set h : RightHomotopy (f ≫ g₁) (f ≫ g₂) := homotopyOfEq _ _ eq
    exact eq_of_rightHomotopy _ _ ⟨inv f.right ≫ h.hom, by simp [dsimp% h.comm]⟩

section Functor

variable [HasZeroObject V]

variable (V)

/-- If `V` has a zero object, the functor from `V` to `Arrow V` that sends an object `X`
to the arrow `0 ⟶ X`. -/
def rightFunctor : V ⥤ Arrow V where
  obj X := Arrow.mk 0
  map f := Arrow.homMk 0 f (HasZeroObject.from_zero_ext _ _)
  map_id _ := by
    ext
    · exact HasZeroObject.from_zero_ext _ _
    · rfl

instance : (rightFunctor V).Additive where
  map_add {_ _ _ _} := by
    ext
    · exact HasZeroObject.from_zero_ext _ _
    · rfl

/-- The fully faithful additive functor from  `V` to `RightFreyd V` sending an object `X` of `V`
to the class of the arrow `0 ⟶ X`. -/
def functor : V ⥤ RightFreyd V := rightFunctor V ⋙ quotient V

instance : (functor V).Additive := by dsimp [functor]; infer_instance

instance : (functor V).Full where
  map_surjective a := by
    obtain ⟨u, rfl⟩ := (quotient V).map_surjective a
    use u.right
    apply congrArg (quotient V).map
    ext
    · exact HasZeroObject.from_zero_ext _ _
    · rfl

instance : (functor V).Faithful where
  map_injective {_ _} _ _ eq := by
    refine eq_of_sub_eq_zero (((quotient_map_eq_iff _ _).mp eq).some.comm.trans ?_)
    convert comp_zero
    · exact HasZeroObject.from_zero_ext _ _
    · rfl

end Functor

variable [HasFiniteProducts V]

local instance : HasBinaryBiproducts V := HasBinaryBiproducts.of_hasBinaryProducts

variable {u v : Arrow V} (f : u ⟶ v)

namespace CandidateCokernel

/-- If `f` is a morphism of `Arrow V`, this is a "candidate cokernel" of `f`, i.e. an object
in `Arrow V` whose image in `RightFreyd V` will be a cokernel of the image of `f`. -/
abbrev cokernel : Arrow V := Arrow.mk (biprod.desc v.hom f.right)

/-- For `f : u ⟶ v` a morphism in `Arrow V`, this is the morphism `v ⟶ cokernel f` from `v` to
the "candidate cokernel" of `f`, whose image in `RightFreyd V` will be the projection to
the cokernel of the image of `f`. -/
def π : v ⟶ cokernel f :=
  Arrow.homMk biprod.inl (𝟙 v.right) ((biprod.inl_desc _ _).trans (comp_id _).symm)

/-- The right homotopy expressing that `f ≫ π f` is sent to `0` in `RightFreyd V`. -/
def condition : RightHomotopy (f ≫ π f) 0 where
  hom := biprod.inr
  comm := by
    simp only [π, comp_right, homMk_right, Hom.zero_right]
    refine Eq.trans ?_ (biprod.inr_desc _ _).symm
    rw [sub_zero]
    exact comp_id _

set_option backward.isDefEq.respectTransparency false in
instance isEpi_π : Epi ((quotient V).map (π f)) :=
  have : IsIso ((π f).right) := by simp only [π, homMk_right]; infer_instance
  isEpi_of_right_iso _

variable {w : Arrow V} (g : v ⟶ w) (h : RightHomotopy (f ≫ g) 0)

/--
If `f : u ⟶ v` and `g : v ⟶ w` are morphisms in `Arrow V` such that `f ≫ g` is right homotopic
to `0`, this is the morphism from the "candidate cokernel" of `f` to `w` defined from the
right homotopy. -/
def desc : cokernel f ⟶ w := by
  refine Arrow.homMk (biprod.desc g.left h.hom) g.right ?_
  simp only [mk_hom]
  apply biprod.hom_ext'
  · convert (biprod.inl_desc_assoc _ _ _).trans
      (Eq.trans g.w (biprod.inl_desc_assoc _ _ _).symm) <;> rfl
  · convert (biprod.inr_desc_assoc g.left h.hom w.hom).trans
      (Eq.trans (by simp [h.comm.symm]) (biprod.inr_desc_assoc v.hom f.right g.right).symm) <;> rfl

@[reassoc]
lemma π_desc : π f ≫ desc f g h = g := by
  simp only [cokernel, π, desc]
  ext
  · simp only [comp_left, homMk_left]
    exact biprod.inl_desc _ _
  · simp only [comp_right, homMk_right]
    exact Category.id_comp _

end CandidateCokernel

variable {X : RightFreyd V} {a : (quotient V).obj v ⟶ X} (eq : (quotient V).map f ≫ a = 0)

/-- Let `f : u ⟶ v` be a morphism in `Arrow V`, and let `a : (quotient V).obj v ⟶ X` be
a morphism in `RightFreyd V` such that `(quotient V).map f ≫ a = 0`. This is the morphism
`(quotient V).obj (cokernel f) ⟶ X` that will serve as `cokernel.desc f`. -/
def desc' : (quotient V).obj (CandidateCokernel.cokernel f) ⟶ X := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  exact (quotient V).map (CandidateCokernel.desc _ _ (homotopyOfEq _ _ eq))

lemma π_desc' : (quotient V).map (CandidateCokernel.π f) ≫ desc' f eq = a := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  conv_rhs => rw [← ((quotient V).map_surjective a).choose_spec,
                      ← CandidateCokernel.π_desc _ _ (homotopyOfEq _ _ eq)]
  rfl

/-- For `f` a morphism in `Arrow V`, construct a cokernel cofork of `(quotient V).map f`. -/
def candidateCokernelCofork : Cocone (parallelPair ((quotient V).map f) 0) := by
  refine CokernelCofork.ofπ ((quotient V).map (CandidateCokernel.π f)) ?_
  rw [← (quotient V).map_comp]
  exact eq_of_rightHomotopy _ _ (CandidateCokernel.condition f)

/-- For `f` a morphism in `Arrow V`, the cokernel cofork of `(quotient V).map f` constructed
in `candidateCokernelCofork` is a colimit cofork. -/
def candidateCokernelCoforkIsCokernel : IsColimit (candidateCokernelCofork f) where
  desc s := desc' f (CokernelCofork.condition s)
  fac s j :=
    match j with
    | WalkingParallelPair.zero => by
      simp only [Cofork.app_zero_eq_comp_π_left, CokernelCofork.condition]
      exact zero_comp
    | WalkingParallelPair.one => π_desc' f (CokernelCofork.condition s)
  uniq s m eq :=
    (cancel_epi ((quotient V).map (CandidateCokernel.π f))).mp ((eq WalkingParallelPair.one).trans
    (π_desc' f (CokernelCofork.condition s)).symm)

/-- The category `RightFreyd V` has all cokernels if `V` has finite products. -/
instance : HasCokernels (RightFreyd V) where
  has_colimit {X Y} f := {
    exists_colimit := by
      obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
      exact Nonempty.intro {
        cocone := candidateCokernelCofork f
        isColimit := candidateCokernelCoforkIsCokernel f}}

end RightFreyd

end CategoryTheory.Preadditive
