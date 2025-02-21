/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Topos.Classifier

/-!
# Power Objects

Defines power objects for a category C with a subobject classifier and pullbacks.

## Main definitions


## Main results


## Notation

* if `f : B ⨯ A ⟶ Ω C` is a morphism in a category with power objects, then
  `f^` denotes the corresponding morphism `A ⟶ Pow B`.
* If `g : A ⟶ Pow B` is a morphism in a category with power objects, then
  `g^` denotes the corresponding morphism `B ⨯ A ⟶ Ω C`.
* To "curry" maps in the other coordinate, put the caret `^` before the function argument
  instead of after.

## References


-/




open CategoryTheory Category Limits Classifier


universe u v
variable {C : Type u} [Category.{v} C] [HasTerminal C] [HasClassifier C] [HasPullbacks C]

namespace CategoryTheory.Power


/-- Having a subobject classifier implies having terminal objects.
    Combined with having pullbacks, this shows that C has binary products.
-/
instance hasBinaryProducts : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C

/-- A category with a terminal object and binary products
has all finite products.
-/
instance hasFiniteProducts : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal

/-- A category with binary products and pullbacks has equalizers. -/
instance hasEqualizers : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products

/-- An object `PB` and a map `in_B : B ⨯ PB ⟶ Ω C` form a power object for `B : C`
if, for any map `f : B ⨯ A ⟶ Ω C`, there is a unique map `f' : A ⟶ PB` such that
the following diagram commutes:
```

        B ⨯ A ---f---> Ω C
          |             ^
          |            /
          |           /
    (𝟙 B) ⨯ f'       /
          |         /
          |       in_B
          |       /
          |      /
          |     /
          |    /
          v   /
        B ⨯ PB
```
-/
class IsPower {B PB : C} (in_B : B ⨯ PB ⟶ Ω C) where
  /-- For each `f`, there is exactly one
  morphism `A ⟶ PB` making the above diagram commute.
  -/
  hat {A : C} (f : B ⨯ A ⟶ Ω C) : Unique { f' : A ⟶ PB // (prod.map (𝟙 _) f') ≫ in_B = f }

/-- What it means for an object B to have a power object. -/
class HasPower (B : C) where
  /-- The power object. -/
  Pow : C
  /-- The membership predicate. -/
  in_ : B ⨯ Pow ⟶ Ω C
  /-- The pair `Pow` and `in_` form a power object for `B`. -/
  is_power : IsPower in_

variable (C)

/-- A category has power objects if each of its objects
has a power object.
-/
class HasPowers where
  /-- Each `B : C` has a power object. -/
  has_power_object (B : C) : HasPower B

variable {C}

attribute [instance] HasPowers.has_power_object

variable [HasPowers C]


/-- Notation for the power object of an object. -/
abbrev Pow (B : C) : C := (HasPowers.has_power_object B).Pow

/-- Notation for the predicate "b ∈ S" as a map `B ⨯ P(B) ⟶ Ω`. -/
abbrev in_ (B : C) : B ⨯ (Pow B) ⟶ Ω C := (HasPowers.has_power_object B).in_

instance Pow_is_power (B : C) : IsPower (in_ B) := (HasPowers.has_power_object B).is_power

/-- The map Hom(B⨯A,Ω) → Hom(A,P(B)).
This is currying the left argument.
-/
def P_transpose {B A} (f : B ⨯ A ⟶ Ω C) : A ⟶ Pow B := ((Pow_is_power B).hat f).default

/-- Shorthand for currying the left argument. -/
notation f "^" => P_transpose f

/-- `P_transpose` satisfies the commutativity of the diagram from `IsPower`. -/
lemma Pow_powerizes (B) {A} (f : B ⨯ A ⟶ Ω C) : prod.map (𝟙 _) (f^) ≫ in_ B = f :=
  (((Pow_is_power B).hat f).default).prop

/-- `P_transpose` is the only map which satisfies the commutativity
of the diagram from `IsPower`.
-/
lemma Pow_unique (B) {A} {f : B ⨯ A ⟶ Ω C} {hat' : A ⟶ Pow B}
(hat'_powerizes : prod.map (𝟙 _) hat' ≫ in_ B = f ) :
    f^ = hat' := by
  have h := ((Pow_is_power B).hat f).uniq ⟨hat', hat'_powerizes⟩
  apply_fun (fun x => x.val) at h
  symm
  assumption

noncomputable section

/-- Un-currying on the left. -/
abbrev P_transpose_inv {B A} (f : A ⟶ Pow B) : B ⨯ A ⟶ Ω C := (prod.map (𝟙 _) f) ≫ in_ B

/-- Shorthand for un-currying on the left. -/
notation f "^" => P_transpose_inv f

/-- Equivalence between Hom(B⨯A,Ω) and Hom(A,P(B)). -/
def transposeEquiv (A B : C) : (B ⨯ A ⟶ Ω C) ≃ (A ⟶ Pow B) where
  toFun := P_transpose
  invFun := P_transpose_inv
  left_inv := fun f => Pow_powerizes _ _
  right_inv := by
    intro g
    apply Pow_unique
    rfl

/-- `P_transpose_inv` is a left inverse of
`P_transpose`.
-/
@[simp]
lemma P_transpose_left_inv {B A} (f : B ⨯ A ⟶ Ω C) : (f^)^ = f :=
  (transposeEquiv _ _).left_inv _

/-- `P_transpose_inv` is a right inverse of
`P_transpose`.
-/
@[simp]
lemma P_transpose_right_inv {B A : C} (f : A ⟶ Pow B) : (f^)^ = f :=
  (transposeEquiv _ _).right_inv _

/-- The map Hom(B⨯A,Ω) → Hom(B,P(A)).
This is currying the right argument.
-/
def P_transpose_symm {B A} (f : B ⨯ A ⟶ Ω C) : B ⟶ Pow A :=
  P_transpose ((prod.braiding A B).hom ≫ f)

/-- Shorthand for currying the right argument. -/
notation "^" f => P_transpose_symm f

/-- Un-currying on the right. -/
abbrev P_transpose_symm_inv {B A} (f : B ⟶ Pow A) : B ⨯ A ⟶ Ω C :=
  (prod.braiding A B).inv ≫ (P_transpose_inv f)

/-- Shorthand for un-currying on the right. -/
notation "^" f => P_transpose_symm_inv f

/-- Equivalence between Hom(B⨯A,Ω) and Hom(B,P(A)). -/
def transposeEquivSymm (A B : C) : (B ⨯ A ⟶ Ω C) ≃ (B ⟶ Pow A) where
  toFun := P_transpose_symm
  invFun := P_transpose_symm_inv
  left_inv := by
    intro f
    dsimp only [P_transpose_symm, P_transpose_inv, P_transpose_symm_inv]
    rw [Pow_powerizes, ←assoc, Iso.inv_hom_id, id_comp]
  right_inv := by
    intro g
    apply Pow_unique
    rw [←assoc, Iso.hom_inv_id, id_comp]

/-- `P_transpose_symm_inv` is the left inverse
of `P_transpose_symm`.
-/
@[simp]
lemma P_transpose_symm_left_inv {B A} (f : B ⨯ A ⟶ Ω C) :
    (^(^f)) = f :=
  (transposeEquivSymm _ _).left_inv _

/-- `P_transpose_symm_inv` is the right inverse
of `P_transpose_symm`.
-/
@[simp]
lemma P_transpose_symm_right_inv {B A : C} (f : B ⟶ Pow A) :
    (^(^f)) = f :=
  (transposeEquivSymm _ _).right_inv _

/-- Equivalence between Hom(A,P(B)) and Hom(B, P(A)).
This is just the composition of `transposeEquiv` and `transposeEquivSymm`.
-/
def transpose_transpose_Equiv (A B : C) : (B ⟶ Pow A) ≃ (A ⟶ Pow B) :=
  -- (transposeEquivSymm A B).symm.trans (transposeEquiv A B)
  Equiv.trans (transposeEquivSymm A B).symm (transposeEquiv A B)


/--
  The power object functor's action on arrows.
  Sends `h : A ⟶ B` to the P-transpose of the map `h⨯1 ≫ ∈_B : A ⨯ Pow B ⟶ B ⨯ Pow B ⟶ Ω`.
-/
def Pow_map {B A : C} (h : A ⟶ B) : Pow B ⟶ Pow A :=
  P_transpose ((prod.map h (𝟙 (Pow B))) ≫ (in_ B))

/-- The following diagram commutes:
```
    A ⨯ Pow B ----(𝟙 A) ⨯ Pow_map h----> A ⨯ Pow A
      |                                    |
      |                                    |
    h ⨯ (𝟙 (Pow B))                      in_ A
      |                                    |
      v                                    v
    B ⨯ Pow B ----------in_ B-----------> Ω C
```
-/
lemma Pow_map_Powerizes {A B : C} (h : A ⟶ B) :
    (prod.map (𝟙 A) (Pow_map h)) ≫ in_ A = (prod.map h (𝟙 (Pow B))) ≫ (in_ B) := by
  dsimp [Pow_map]
  apply Pow_powerizes

/-- `Pow_map` sends the identity on an object `X` to the identity on `Pow X`. -/
@[simp]
lemma Pow_map_id {B : C} : Pow_map (𝟙 B) = 𝟙 (Pow B) := by
  apply Pow_unique; rfl


variable (C)

/--
  The power object functor.
  Sends objects `B` to their power objects `Pow B`.
  Sends arrows `h : A ⟶ B` to the P-transpose of the map `h⨯1 ≫ ∈_B : A ⨯ Pow B ⟶ B ⨯ Pow B ⟶ Ω`,
  which is the "preimage" morphism `P(h) : Pow B ⟶ Pow A`.
-/
def PowFunctor : Cᵒᵖ ⥤ C where
  obj := fun ⟨B⟩ ↦ Pow B
  map := fun ⟨h⟩ ↦ Pow_map h
  map_id := by
    intro _
    apply Pow_unique
    rfl
  map_comp := by
    intro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩
    apply Pow_unique
    dsimp [Pow_map]
    symm
    calc
      prod.map (g ≫ f)  (𝟙 (Pow X)) ≫ in_ X
        = (prod.map g (𝟙 (Pow X))) ≫ (prod.map f  (𝟙 (Pow X))) ≫ in_ X  := by
        rw [←assoc, ←prod.map_comp_id]
      _ = (prod.map g (𝟙 (Pow X))) ≫ (prod.map (𝟙 Y) (Pow_map f)) ≫ in_ Y := by
        rw [Pow_map_Powerizes]
      _ = (prod.map (𝟙 Z) (Pow_map f)) ≫ (prod.map g (𝟙 (Pow Y))) ≫ in_ Y := by
        repeat rw [prod.map_map_assoc, comp_id, id_comp]
      _ = (prod.map (𝟙 Z) (Pow_map f)) ≫ (prod.map (𝟙 Z) (Pow_map g)) ≫ in_ Z := by
        rw [Pow_map_Powerizes]
      _ = prod.map (𝟙 Z) (Pow_map f ≫ Pow_map g ) ≫ in_ Z  := by
        rw [←assoc, prod.map_id_comp]

/-- The power object functor, treated as a functor `C ⥤ Cᵒᵖ`. -/
def PowFunctorOp : C ⥤ Cᵒᵖ where
  obj := fun B ↦ ⟨Pow B⟩
  map := fun h ↦ ⟨Pow_map h⟩
  map_id := by
    intro _
    apply congrArg Opposite.op
    apply (PowFunctor C).map_id
  map_comp := by
    intros
    apply congrArg Opposite.op
    apply (PowFunctor C).map_comp

/-- exhibiting that the pow functor is adjoint to itself on the right. -/
def PowSelfAdj : PowFunctorOp C ⊣ PowFunctor C := by
  apply Adjunction.mkOfHomEquiv
  fapply Adjunction.CoreHomEquiv.mk

  -- homEquiv step
  · exact fun X ⟨Y⟩ => {
      toFun := fun ⟨f⟩ => (transpose_transpose_Equiv X Y).toFun f
      invFun := fun g => ⟨(transpose_transpose_Equiv X Y).invFun g⟩
      left_inv := fun ⟨f⟩ => by simp
      right_inv := fun g => by simp
    }

  -- homEquiv_naturality_left_symm step
  · intro X' X ⟨Y⟩ f g
    simp
    congr
    show (transpose_transpose_Equiv X' Y).symm (f ≫ g) =
      (transpose_transpose_Equiv X Y).symm g ≫ Pow_map f
    dsimp only [transpose_transpose_Equiv, transposeEquivSymm, transposeEquiv]
    simp
    dsimp only [P_transpose_symm, P_transpose_inv, Pow_map]
    apply Pow_unique
    rw [prod.map_id_comp _ (P_transpose _), assoc _ _ (in_ X'), Pow_powerizes, ←assoc _ _ (in_ X),
      prod.map_map, id_comp, comp_id, ←comp_id f, ←id_comp (P_transpose _), ←prod.map_map,
      assoc, Pow_powerizes]
    have h : prod.map f (𝟙 Y) ≫ (prod.braiding X Y).hom
    = (prod.braiding _ _).hom ≫ prod.map (𝟙 _) f := by simp
    rw [←assoc (prod.map f (𝟙 _)), h]
    simp

  -- homEquiv_naturality_right step
  · intro X ⟨Y⟩ ⟨Y'⟩ ⟨f⟩ ⟨g⟩
    dsimp only [transpose_transpose_Equiv, transposeEquiv, transposeEquivSymm]
    simp only [prod.lift_map_assoc, comp_id, Equiv.toFun_as_coe, Equiv.trans_apply,
      Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Equiv.invFun_as_coe, Equiv.symm_trans_apply,
      Equiv.symm_symm]
    show P_transpose ((prod.braiding X Y').inv ≫ prod.map (𝟙 X) (g ≫ f) ≫ in_ X) =
      P_transpose ((prod.braiding X Y).inv ≫ prod.map (𝟙 X) f ≫ in_ X) ≫ Pow_map g
    dsimp only [P_transpose_inv, Pow_map]
    apply Pow_unique
    rw [prod.map_id_comp (P_transpose _), assoc, Pow_powerizes, ←assoc _ _ (in_ Y),
      prod.map_map, id_comp, comp_id, ←comp_id g]
    have h : prod.map g (𝟙 X) ≫ (prod.braiding X Y).inv
    = (prod.braiding _ _).inv ≫ prod.map (𝟙 _) g := by simp
    rw [←id_comp (P_transpose _), ←prod.map_map, assoc, Pow_powerizes, ←assoc (prod.map g _), h]
    simp only [prod.braiding_inv, prod.lift_map_assoc, comp_id, prod.lift_map, assoc]


end
end CategoryTheory.Power
