/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.ConeCategory

/-!

# Multi-(co)equalizers

A *multiequalizer* is an equalizer of two morphisms between two products.
Since both products and equalizers are limits, such an object is again a limit.
This file provides the diagram whose limit is indeed such an object.
In fact, it is well-known that any limit can be obtained as a multiequalizer.
The dual construction (multicoequalizers) is also provided.

## Projects

Prove that a multiequalizer can be identified with
an equalizer between products (and analogously for multicoequalizers).

Prove that the limit of any diagram is a multiequalizer (and similarly for colimits).

-/


namespace CategoryTheory.Limits

open CategoryTheory

universe w w' v u

/-- The shape of a multiequalizer diagram. It involves two types `L` and `R`,
and two maps `R → L`. -/
@[nolint checkUnivs]
structure MulticospanShape where
  /-- the left type -/
  L : Type w
  /-- the right type -/
  R : Type w'
  /-- the first map `R → L` -/
  fst : R → L
  /-- the second map `R → L` -/
  snd : R → L

/-- Given a type `ι`, this is the shape of multiequalizer diagrams corresponding
to situations where we want to equalize two families of maps `U i ⟶ V ⟨i, j⟩`
and `U j ⟶ V ⟨i, j⟩` with `i : ι` and `j : ι`. -/
@[simps]
def MulticospanShape.prod (ι : Type w) : MulticospanShape where
  L := ι
  R := ι × ι
  fst := _root_.Prod.fst
  snd := _root_.Prod.snd

/-- The shape of a multicoequalizer diagram. It involves two types `L` and `R`,
and two maps `L → R`. -/
@[nolint checkUnivs]
structure MultispanShape where
  /-- the left type -/
  L : Type w
  /-- the right type -/
  R : Type w'
  /-- the first map `L → R` -/
  fst : L → R
  /-- the second map `L → R` -/
  snd : L → R

/-- Given a type `ι`, this is the shape of multicoequalizer diagrams corresponding
to situations where we want to coequalize two families of maps `V ⟨i, j⟩ ⟶ U i`
and `V ⟨i, j⟩ ⟶ U j` with `i : ι` and `j : ι`. -/
@[simps]
def MultispanShape.prod (ι : Type w) : MultispanShape where
  L := ι × ι
  R := ι
  fst := _root_.Prod.fst
  snd := _root_.Prod.snd

/-- The type underlying the multiequalizer diagram. -/
inductive WalkingMulticospan (J : MulticospanShape.{w, w'}) : Type max w w'
  | left : J.L → WalkingMulticospan J
  | right : J.R → WalkingMulticospan J

/-- The type underlying the multiecoqualizer diagram. -/
inductive WalkingMultispan (J : MultispanShape.{w, w'}) : Type max w w'
  | left : J.L → WalkingMultispan J
  | right : J.R → WalkingMultispan J

namespace WalkingMulticospan

variable {J : MulticospanShape.{w, w'}}

instance [Inhabited J.L] : Inhabited (WalkingMulticospan J) :=
  ⟨left default⟩

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- Morphisms for `WalkingMulticospan`. -/
inductive Hom : ∀ _ _ : WalkingMulticospan J, Type max w w'
  | id (A) : Hom A A
  | fst (b) : Hom (left (J.fst b)) (right b)
  | snd (b) : Hom (left (J.snd b)) (right b)

instance {a : WalkingMulticospan J} : Inhabited (Hom a a) :=
  ⟨Hom.id _⟩

/-- Composition of morphisms for `WalkingMulticospan`. -/
def Hom.comp : ∀ {A B C : WalkingMulticospan J} (_ : Hom A B) (_ : Hom B C), Hom A C
  | _, _, _, Hom.id X, f => f
  | _, _, _, Hom.fst b, Hom.id _ => Hom.fst b
  | _, _, _, Hom.snd b, Hom.id _ => Hom.snd b

instance : SmallCategory (WalkingMulticospan J) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  comp_id := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  assoc := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) (_ | _ | _) <;> rfl

@[simp]
lemma Hom.id_eq_id (X : WalkingMulticospan J) :
    Hom.id X = 𝟙 X := rfl

@[simp]
lemma Hom.comp_eq_comp {X Y Z : WalkingMulticospan J}
    (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.comp f g = f ≫ g := rfl

end WalkingMulticospan

namespace WalkingMultispan

variable {J : MultispanShape.{w, w'}}

instance [Inhabited J.L] : Inhabited (WalkingMultispan J) :=
  ⟨left default⟩

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- Morphisms for `WalkingMultispan`. -/
inductive Hom : ∀ _ _ : WalkingMultispan J, Type max w w'
  | id (A) : Hom A A
  | fst (a) : Hom (left a) (right (J.fst a))
  | snd (a) : Hom (left a) (right (J.snd a))

instance {a : WalkingMultispan J} : Inhabited (Hom a a) :=
  ⟨Hom.id _⟩

/-- Composition of morphisms for `WalkingMultispan`. -/
def Hom.comp : ∀ {A B C : WalkingMultispan J} (_ : Hom A B) (_ : Hom B C), Hom A C
  | _, _, _, Hom.id X, f => f
  | _, _, _, Hom.fst a, Hom.id _ => Hom.fst a
  | _, _, _, Hom.snd a, Hom.id _ => Hom.snd a

instance : SmallCategory (WalkingMultispan J) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  comp_id := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  assoc := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) (_ | _ | _) <;> rfl

@[simp]
lemma Hom.id_eq_id (X : WalkingMultispan J) : Hom.id X = 𝟙 X := rfl

@[simp]
lemma Hom.comp_eq_comp {X Y Z : WalkingMultispan J}
    (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.comp f g = f ≫ g := rfl

end WalkingMultispan

/-- This is a structure encapsulating the data necessary to define a `Multicospan`. -/
@[nolint checkUnivs]
structure MulticospanIndex (J : MulticospanShape.{w, w'})
    (C : Type u) [Category.{v} C] where
  left : J.L → C
  right : J.R → C
  fst : ∀ b, left (J.fst b) ⟶ right b
  snd : ∀ b, left (J.snd b) ⟶ right b

/-- This is a structure encapsulating the data necessary to define a `Multispan`. -/
@[nolint checkUnivs]
structure MultispanIndex (J : MultispanShape.{w, w'})
    (C : Type u) [Category.{v} C] where
  left : J.L → C
  right : J.R → C
  fst : ∀ a, left a ⟶ right (J.fst a)
  snd : ∀ a, left a ⟶ right (J.snd a)

namespace MulticospanIndex

variable {C : Type u} [Category.{v} C] {J : MulticospanShape.{w, w'}}
  (I : MulticospanIndex J C)

/-- The multicospan associated to `I : MulticospanIndex`. -/
@[simps]
def multicospan : WalkingMulticospan J ⥤ C where
  obj x :=
    match x with
    | WalkingMulticospan.left a => I.left a
    | WalkingMulticospan.right b => I.right b
  map {x y} f :=
    match x, y, f with
    | _, _, WalkingMulticospan.Hom.id x => 𝟙 _
    | _, _, WalkingMulticospan.Hom.fst b => I.fst _
    | _, _, WalkingMulticospan.Hom.snd b => I.snd _
  map_id := by
    rintro (_ | _) <;> rfl
  map_comp := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) <;> aesop_cat

variable [HasProduct I.left] [HasProduct I.right]

/-- The induced map `∏ᶜ I.left ⟶ ∏ᶜ I.right` via `I.fst`. -/
noncomputable def fstPiMap : ∏ᶜ I.left ⟶ ∏ᶜ I.right :=
  Pi.lift fun b => Pi.π I.left (J.fst b) ≫ I.fst b

/-- The induced map `∏ᶜ I.left ⟶ ∏ᶜ I.right` via `I.snd`. -/
noncomputable def sndPiMap : ∏ᶜ I.left ⟶ ∏ᶜ I.right :=
  Pi.lift fun b => Pi.π I.left (J.snd b) ≫ I.snd b

@[reassoc (attr := simp)]
theorem fstPiMap_π (b) : I.fstPiMap ≫ Pi.π I.right b = Pi.π I.left _ ≫ I.fst b := by
  simp [fstPiMap]

@[reassoc (attr := simp)]
theorem sndPiMap_π (b) : I.sndPiMap ≫ Pi.π I.right b = Pi.π I.left _ ≫ I.snd b := by
  simp [sndPiMap]

/-- Taking the multiequalizer over the multicospan index is equivalent to taking the equalizer over
the two morphisms `∏ᶜ I.left ⇉ ∏ᶜ I.right`. This is the diagram of the latter.
-/
@[simps!]
protected noncomputable def parallelPairDiagram :=
  parallelPair I.fstPiMap I.sndPiMap

end MulticospanIndex

namespace MultispanIndex

variable {C : Type u} [Category.{v} C] {J : MultispanShape.{w, w'}}
    (I : MultispanIndex J C)

/-- The multispan associated to `I : MultispanIndex`. -/
def multispan : WalkingMultispan J ⥤ C where
  obj x :=
    match x with
    | WalkingMultispan.left a => I.left a
    | WalkingMultispan.right b => I.right b
  map {x y} f :=
    match x, y, f with
    | _, _, WalkingMultispan.Hom.id x => 𝟙 _
    | _, _, WalkingMultispan.Hom.fst b => I.fst _
    | _, _, WalkingMultispan.Hom.snd b => I.snd _
  map_id := by
    rintro (_ | _) <;> rfl
  map_comp := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) <;> aesop_cat

@[simp]
theorem multispan_obj_left (a) : I.multispan.obj (WalkingMultispan.left a) = I.left a :=
  rfl

@[simp]
theorem multispan_obj_right (b) : I.multispan.obj (WalkingMultispan.right b) = I.right b :=
  rfl

@[simp]
theorem multispan_map_fst (a) : I.multispan.map (WalkingMultispan.Hom.fst a) = I.fst a :=
  rfl

@[simp]
theorem multispan_map_snd (a) : I.multispan.map (WalkingMultispan.Hom.snd a) = I.snd a :=
  rfl

variable [HasCoproduct I.left] [HasCoproduct I.right]

/-- The induced map `∐ I.left ⟶ ∐ I.right` via `I.fst`. -/
noncomputable def fstSigmaMap : ∐ I.left ⟶ ∐ I.right :=
  Sigma.desc fun b => I.fst b ≫ Sigma.ι _ (J.fst b)

/-- The induced map `∐ I.left ⟶ ∐ I.right` via `I.snd`. -/
noncomputable def sndSigmaMap : ∐ I.left ⟶ ∐ I.right :=
  Sigma.desc fun b => I.snd b ≫ Sigma.ι _ (J.snd b)

@[reassoc (attr := simp)]
theorem ι_fstSigmaMap (b) : Sigma.ι I.left b ≫ I.fstSigmaMap = I.fst b ≫ Sigma.ι I.right _ := by
  simp [fstSigmaMap]

@[reassoc (attr := simp)]
theorem ι_sndSigmaMap (b) : Sigma.ι I.left b ≫ I.sndSigmaMap = I.snd b ≫ Sigma.ι I.right _ := by
  simp [sndSigmaMap]

/--
Taking the multicoequalizer over the multispan index is equivalent to taking the coequalizer over
the two morphsims `∐ I.left ⇉ ∐ I.right`. This is the diagram of the latter.
-/
protected noncomputable abbrev parallelPairDiagram :=
  parallelPair I.fstSigmaMap I.sndSigmaMap

end MultispanIndex

variable {C : Type u} [Category.{v} C]

/-- A multifork is a cone over a multicospan. -/
abbrev Multifork {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) :=
  Cone I.multicospan

/-- A multicofork is a cocone over a multispan. -/
abbrev Multicofork {J : MultispanShape.{w, w'}} (I : MultispanIndex J C) :=
  Cocone I.multispan

namespace Multifork

variable {J : MulticospanShape.{w, w'}} {I : MulticospanIndex J C} (K : Multifork I)

/-- The maps from the cone point of a multifork to the objects on the left. -/
def ι (a : J.L) : K.pt ⟶ I.left a :=
  K.π.app (WalkingMulticospan.left _)

@[simp]
theorem app_left_eq_ι (a) : K.π.app (WalkingMulticospan.left a) = K.ι a :=
  rfl

@[simp]
theorem app_right_eq_ι_comp_fst (b) :
    K.π.app (WalkingMulticospan.right b) = K.ι (J.fst b) ≫ I.fst b := by
  rw [← K.w (WalkingMulticospan.Hom.fst b)]
  rfl

@[reassoc]
theorem app_right_eq_ι_comp_snd (b) :
    K.π.app (WalkingMulticospan.right b) = K.ι (J.snd b) ≫ I.snd b := by
  rw [← K.w (WalkingMulticospan.Hom.snd b)]
  rfl

@[reassoc (attr := simp)]
theorem hom_comp_ι (K₁ K₂ : Multifork I) (f : K₁ ⟶ K₂) (j : J.L) : f.hom ≫ K₂.ι j = K₁.ι j :=
  f.w _

/-- Construct a multifork using a collection `ι` of morphisms. -/
@[simps]
def ofι {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
    (P : C) (ι : ∀ a, P ⟶ I.left a)
    (w : ∀ b, ι (J.fst b) ≫ I.fst b = ι (J.snd b) ≫ I.snd b) : Multifork I where
  pt := P
  π :=
    { app := fun x =>
        match x with
        | WalkingMulticospan.left _ => ι _
        | WalkingMulticospan.right b => ι (J.fst b) ≫ I.fst b
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _) <;>
          dsimp <;> simp only [Category.id_comp, Category.comp_id]
        apply w }

@[reassoc (attr := simp)]
theorem condition (b) : K.ι (J.fst b) ≫ I.fst b = K.ι (J.snd b) ≫ I.snd b := by
  rw [← app_right_eq_ι_comp_fst, ← app_right_eq_ι_comp_snd]

/-- This definition provides a convenient way to show that a multifork is a limit. -/
@[simps]
def IsLimit.mk (lift : ∀ E : Multifork I, E.pt ⟶ K.pt)
    (fac : ∀ (E : Multifork I) (i : J.L), lift E ≫ K.ι i = E.ι i)
    (uniq : ∀ (E : Multifork I) (m : E.pt ⟶ K.pt), (∀ i : J.L, m ≫ K.ι i = E.ι i) → m = lift E) :
    IsLimit K :=
  { lift
    fac := by
      rintro E (a | b)
      · apply fac
      · rw [← E.w (WalkingMulticospan.Hom.fst b), ← K.w (WalkingMulticospan.Hom.fst b), ←
          Category.assoc]
        congr 1
        apply fac
    uniq := by
      rintro E m hm
      apply uniq
      intro i
      apply hm }

variable {K}

lemma IsLimit.hom_ext (hK : IsLimit K) {T : C} {f g : T ⟶ K.pt}
    (h : ∀ a, f ≫ K.ι a = g ≫ K.ι a) : f = g := by
  apply hK.hom_ext
  rintro (_|b)
  · apply h
  · dsimp
    rw [app_right_eq_ι_comp_fst, reassoc_of% h]

/-- Constructor for morphisms to the point of a limit multifork. -/
def IsLimit.lift (hK : IsLimit K) {T : C} (k : ∀ a, T ⟶ I.left a)
    (hk : ∀ b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) :
    T ⟶ K.pt :=
  hK.lift (Multifork.ofι _ _ k hk)

@[reassoc (attr := simp)]
lemma IsLimit.fac (hK : IsLimit K) {T : C} (k : ∀ a, T ⟶ I.left a)
    (hk : ∀ b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (a : J.L) :
    IsLimit.lift hK k hk ≫ K.ι a = k a :=
  hK.fac _ _

variable (K)

variable [HasProduct I.left] [HasProduct I.right]

@[reassoc (attr := simp)]
theorem pi_condition : Pi.lift K.ι ≫ I.fstPiMap = Pi.lift K.ι ≫ I.sndPiMap := by
  ext
  simp

/-- Given a multifork, we may obtain a fork over `∏ᶜ I.left ⇉ ∏ᶜ I.right`. -/
@[simps pt]
noncomputable def toPiFork (K : Multifork I) : Fork I.fstPiMap I.sndPiMap where
  pt := K.pt
  π :=
    { app := fun x =>
        match x with
        | WalkingParallelPair.zero => Pi.lift K.ι
        | WalkingParallelPair.one => Pi.lift K.ι ≫ I.fstPiMap
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _) <;>
          dsimp <;>
          simp only [Category.id_comp, Functor.map_id, parallelPair_obj_zero, Category.comp_id,
            pi_condition, parallelPair_obj_one] }

@[simp]
theorem toPiFork_π_app_zero : K.toPiFork.ι = Pi.lift K.ι :=
  rfl

@[simp]
theorem toPiFork_π_app_one : K.toPiFork.π.app WalkingParallelPair.one = Pi.lift K.ι ≫ I.fstPiMap :=
  rfl

variable (I)

/-- Given a fork over `∏ᶜ I.left ⇉ ∏ᶜ I.right`, we may obtain a multifork. -/
@[simps pt]
noncomputable def ofPiFork (c : Fork I.fstPiMap I.sndPiMap) : Multifork I where
  pt := c.pt
  π :=
    { app := fun x =>
        match x with
        | WalkingMulticospan.left _ => c.ι ≫ Pi.π _ _
        | WalkingMulticospan.right _ => c.ι ≫ I.fstPiMap ≫ Pi.π _ _
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _)
        · simp
        · simp
        · dsimp; rw [c.condition_assoc]; simp
        · simp }

@[simp]
theorem ofPiFork_π_app_left (c : Fork I.fstPiMap I.sndPiMap) (a) :
    (ofPiFork I c).ι a = c.ι ≫ Pi.π _ _ :=
  rfl

@[simp]
theorem ofPiFork_π_app_right (c : Fork I.fstPiMap I.sndPiMap) (a) :
    (ofPiFork I c).π.app (WalkingMulticospan.right a) = c.ι ≫ I.fstPiMap ≫ Pi.π _ _ :=
  rfl

end Multifork

namespace MulticospanIndex

variable {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
    [HasProduct I.left] [HasProduct I.right]

/-- `Multifork.toPiFork` as a functor. -/
@[simps]
noncomputable def toPiForkFunctor : Multifork I ⥤ Fork I.fstPiMap I.sndPiMap where
  obj := Multifork.toPiFork
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by
        rintro (_ | _)
        · apply limit.hom_ext
          simp
        · apply limit.hom_ext
          intros j
          simp only [Multifork.toPiFork_π_app_one, Multifork.pi_condition, Category.assoc]
          dsimp [sndPiMap]
          simp }

/-- `Multifork.ofPiFork` as a functor. -/
@[simps]
noncomputable def ofPiForkFunctor : Fork I.fstPiMap I.sndPiMap ⥤ Multifork I where
  obj := Multifork.ofPiFork I
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by rintro (_ | _) <;> simp }

/-- The category of multiforks is equivalent to the category of forks over `∏ᶜ I.left ⇉ ∏ᶜ I.right`.
It then follows from `CategoryTheory.IsLimit.ofPreservesConeTerminal` (or `reflects`) that it
preserves and reflects limit cones.
-/
@[simps]
noncomputable def multiforkEquivPiFork : Multifork I ≌ Fork I.fstPiMap I.sndPiMap where
  functor := toPiForkFunctor I
  inverse := ofPiForkFunctor I
  unitIso :=
    NatIso.ofComponents fun K =>
      Cones.ext (Iso.refl _) (by
        rintro (_ | _) <;> simp [← Fork.app_one_eq_ι_comp_left])
  counitIso :=
    NatIso.ofComponents fun K => Fork.ext (Iso.refl _)

end MulticospanIndex

namespace Multicofork

variable {J : MultispanShape.{w, w'}} {I : MultispanIndex J C} (K : Multicofork I)

/-- The maps to the cocone point of a multicofork from the objects on the right. -/
def π (b : J.R) : I.right b ⟶ K.pt :=
  K.ι.app (WalkingMultispan.right _)

@[simp]
theorem π_eq_app_right (b) : K.ι.app (WalkingMultispan.right _) = K.π b :=
  rfl

@[simp]
theorem fst_app_right (a) : K.ι.app (WalkingMultispan.left a) = I.fst a ≫ K.π _ := by
  rw [← K.w (WalkingMultispan.Hom.fst a)]
  rfl

@[reassoc]
theorem snd_app_right (a) : K.ι.app (WalkingMultispan.left a) = I.snd a ≫ K.π _ := by
  rw [← K.w (WalkingMultispan.Hom.snd a)]
  rfl

@[reassoc (attr := simp)]
lemma π_comp_hom (K₁ K₂ : Multicofork I) (f : K₁ ⟶ K₂) (b : J.R) : K₁.π b ≫ f.hom = K₂.π b :=
  f.w _

/-- Construct a multicofork using a collection `π` of morphisms. -/
@[simps]
def ofπ {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
    (P : C) (π : ∀ b, I.right b ⟶ P)
    (w : ∀ a, I.fst a ≫ π (J.fst a) = I.snd a ≫ π (J.snd a)) : Multicofork I where
  pt := P
  ι :=
    { app := fun x =>
        match x with
        | WalkingMultispan.left a => I.fst a ≫ π _
        | WalkingMultispan.right _ => π _
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _) <;> dsimp <;>
          simp only [Functor.map_id, MultispanIndex.multispan_obj_left,
            Category.id_comp, Category.comp_id, MultispanIndex.multispan_obj_right]
        symm
        apply w }

@[reassoc (attr := simp)]
theorem condition (a) : I.fst a ≫ K.π (J.fst a) = I.snd a ≫ K.π (J.snd a) := by
  rw [← K.snd_app_right, ← K.fst_app_right]

/-- This definition provides a convenient way to show that a multicofork is a colimit. -/
@[simps]
def IsColimit.mk (desc : ∀ E : Multicofork I, K.pt ⟶ E.pt)
    (fac : ∀ (E : Multicofork I) (i : J.R), K.π i ≫ desc E = E.π i)
    (uniq : ∀ (E : Multicofork I) (m : K.pt ⟶ E.pt), (∀ i : J.R, K.π i ≫ m = E.π i) → m = desc E) :
    IsColimit K :=
  { desc
    fac := by
      rintro S (a | b)
      · rw [← K.w (WalkingMultispan.Hom.fst a), ← S.w (WalkingMultispan.Hom.fst a),
          Category.assoc]
        congr 1
        apply fac
      · apply fac
    uniq := by
      intro S m hm
      apply uniq
      intro i
      apply hm }

variable [HasCoproduct I.left] [HasCoproduct I.right]

@[reassoc (attr := simp)]
theorem sigma_condition : I.fstSigmaMap ≫ Sigma.desc K.π = I.sndSigmaMap ≫ Sigma.desc K.π := by
  ext
  simp

/-- Given a multicofork, we may obtain a cofork over `∐ I.left ⇉ ∐ I.right`. -/
@[simps pt]
noncomputable def toSigmaCofork (K : Multicofork I) : Cofork I.fstSigmaMap I.sndSigmaMap where
  pt := K.pt
  ι :=
    { app := fun x =>
        match x with
        | WalkingParallelPair.zero => I.fstSigmaMap ≫ Sigma.desc K.π
        | WalkingParallelPair.one => Sigma.desc K.π
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _) <;> dsimp <;>
          simp only [Functor.map_id, parallelPair_obj_zero,
            parallelPair_obj_one, sigma_condition, Category.id_comp, Category.comp_id] }

@[simp]
theorem toSigmaCofork_π : K.toSigmaCofork.π = Sigma.desc K.π :=
  rfl

variable (I)

/-- Given a cofork over `∐ I.left ⇉ ∐ I.right`, we may obtain a multicofork. -/
@[simps pt]
noncomputable def ofSigmaCofork (c : Cofork I.fstSigmaMap I.sndSigmaMap) : Multicofork I where
  pt := c.pt
  ι :=
    { app := fun x =>
        match x with
        | WalkingMultispan.left a => (Sigma.ι I.left a :) ≫ I.fstSigmaMap ≫ c.π
        | WalkingMultispan.right b => (Sigma.ι I.right b :) ≫ c.π
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _)
        · simp
        · simp
        · simp [c.condition]
        · simp }

@[simp]
theorem ofSigmaCofork_ι_app_left (c : Cofork I.fstSigmaMap I.sndSigmaMap) (a) :
    (ofSigmaCofork I c).ι.app (WalkingMultispan.left a) =
      (Sigma.ι I.left a :) ≫ I.fstSigmaMap ≫ c.π :=
  rfl

-- LHS simplifies; `(d)simp`-normal form is `ofSigmaCofork_ι_app_right'`
theorem ofSigmaCofork_ι_app_right (c : Cofork I.fstSigmaMap I.sndSigmaMap) (b) :
    (ofSigmaCofork I c).ι.app (WalkingMultispan.right b) = (Sigma.ι I.right b :) ≫ c.π :=
  rfl

@[simp]
theorem ofSigmaCofork_ι_app_right' (c : Cofork I.fstSigmaMap I.sndSigmaMap) (b) :
    π (ofSigmaCofork I c) b = (Sigma.ι I.right b :) ≫ c.π :=
  rfl

variable {I} in
/-- Constructor for isomorphisms between multicoforks. -/
@[simps!]
def ext {K K' : Multicofork I}
    (e : K.pt ≅ K'.pt) (h : ∀ (i : J.R), K.π i ≫ e.hom = K'.π i := by aesop_cat) :
    K ≅ K' :=
  Cocones.ext e (by rintro (i | j) <;> simp [h])

end Multicofork

namespace MultispanIndex

variable {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
  [HasCoproduct I.left] [HasCoproduct I.right]

/-- `Multicofork.toSigmaCofork` as a functor. -/
@[simps]
noncomputable def toSigmaCoforkFunctor : Multicofork I ⥤ Cofork I.fstSigmaMap I.sndSigmaMap where
  obj := Multicofork.toSigmaCofork
  map {K₁ K₂} f :=
  { hom := f.hom
    w := by
      rintro (_|_)
      all_goals {
        apply colimit.hom_ext
        rintro ⟨j⟩
        simp } }

/-- `Multicofork.ofSigmaCofork` as a functor. -/
@[simps]
noncomputable def ofSigmaCoforkFunctor : Cofork I.fstSigmaMap I.sndSigmaMap ⥤ Multicofork I where
  obj := Multicofork.ofSigmaCofork I
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by --sorry --by rintro (_ | _) <;> simp
        rintro (_ | _)
        -- porting note; in mathlib3, `simp` worked. What seems to be happening is that
        -- the `simp` set is not confluent, and mathlib3 found
        -- `Multicofork.ofSigmaCofork_ι_app_left` before `Multicofork.fst_app_right`,
        -- but mathlib4 finds `Multicofork.fst_app_right` first.
        { simp [-Multicofork.fst_app_right] }
        -- Porting note: similarly here, the `simp` set seems to be non-confluent
        { simp [-Multicofork.ofSigmaCofork_pt] } }

/--
The category of multicoforks is equivalent to the category of coforks over `∐ I.left ⇉ ∐ I.right`.
It then follows from `CategoryTheory.IsColimit.ofPreservesCoconeInitial` (or `reflects`) that
it preserves and reflects colimit cocones.
-/
@[simps]
noncomputable def multicoforkEquivSigmaCofork :
    Multicofork I ≌ Cofork I.fstSigmaMap I.sndSigmaMap where
  functor := toSigmaCoforkFunctor I
  inverse := ofSigmaCoforkFunctor I
  unitIso := NatIso.ofComponents fun K => Cocones.ext (Iso.refl _) (by
      rintro (_ | _) <;> simp)
  counitIso := NatIso.ofComponents fun K =>
    Cofork.ext (Iso.refl _)
      (by
        -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): in mathlib3 this was just `ext` and I don't know why it's not here
        apply Limits.colimit.hom_ext
        rintro ⟨j⟩
        dsimp
        simp only [Category.comp_id, colimit.ι_desc, Cofan.mk_ι_app]
        rfl)

end MultispanIndex

/-- For `I : MulticospanIndex J C`, we say that it has a multiequalizer if the associated
  multicospan has a limit. -/
abbrev HasMultiequalizer {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) :=
  HasLimit I.multicospan

noncomputable section

/-- The multiequalizer of `I : MulticospanIndex J C`. -/
abbrev multiequalizer {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
    [HasMultiequalizer I] : C :=
  limit I.multicospan

/-- For `I : MultispanIndex J C`, we say that it has a multicoequalizer if
  the associated multicospan has a limit. -/
abbrev HasMulticoequalizer {J : MultispanShape.{w, w'}} (I : MultispanIndex J C) :=
  HasColimit I.multispan

/-- The multiecoqualizer of `I : MultispanIndex J C`. -/
abbrev multicoequalizer {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
    [HasMulticoequalizer I] : C :=
  colimit I.multispan

namespace Multiequalizer

variable {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) [HasMultiequalizer I]

/-- The canonical map from the multiequalizer to the objects on the left. -/
abbrev ι (a : J.L) : multiequalizer I ⟶ I.left a :=
  limit.π _ (WalkingMulticospan.left a)

/-- The multifork associated to the multiequalizer. -/
abbrev multifork : Multifork I :=
  limit.cone _

@[simp]
theorem multifork_ι (a) : (Multiequalizer.multifork I).ι a = Multiequalizer.ι I a :=
  rfl

@[simp]
theorem multifork_π_app_left (a) :
    (Multiequalizer.multifork I).π.app (WalkingMulticospan.left a) = Multiequalizer.ι I a :=
  rfl

@[reassoc]
theorem condition (b) :
    Multiequalizer.ι I (J.fst b) ≫ I.fst b = Multiequalizer.ι I (J.snd b) ≫ I.snd b :=
  Multifork.condition _ _

/-- Construct a morphism to the multiequalizer from its universal property. -/
abbrev lift (W : C) (k : ∀ a, W ⟶ I.left a)
    (h : ∀ b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) : W ⟶ multiequalizer I :=
  limit.lift _ (Multifork.ofι I _ k h)

@[reassoc]
theorem lift_ι (W : C) (k : ∀ a, W ⟶ I.left a)
    (h : ∀ b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (a) :
    Multiequalizer.lift I _ k h ≫ Multiequalizer.ι I a = k _ :=
  limit.lift_π _ _

@[ext]
theorem hom_ext {W : C} (i j : W ⟶ multiequalizer I)
    (h : ∀ a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.ι I a) : i = j :=
  Multifork.IsLimit.hom_ext (limit.isLimit _) h

variable [HasProduct I.left] [HasProduct I.right]

instance : HasEqualizer I.fstPiMap I.sndPiMap :=
  ⟨⟨⟨_, IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.functor (limit.isLimit _)⟩⟩⟩

/-- The multiequalizer is isomorphic to the equalizer of `∏ᶜ I.left ⇉ ∏ᶜ I.right`. -/
def isoEqualizer : multiequalizer I ≅ equalizer I.fstPiMap I.sndPiMap :=
  limit.isoLimitCone
    ⟨_, IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.inverse (limit.isLimit _)⟩

/-- The canonical injection `multiequalizer I ⟶ ∏ᶜ I.left`. -/
def ιPi : multiequalizer I ⟶ ∏ᶜ I.left :=
  (isoEqualizer I).hom ≫ equalizer.ι I.fstPiMap I.sndPiMap

@[reassoc (attr := simp)]
theorem ιPi_π (a) : ιPi I ≫ Pi.π I.left a = ι I a := by
  rw [ιPi, Category.assoc, ← Iso.eq_inv_comp, isoEqualizer]
  simp

instance : Mono (ιPi I) := mono_comp _ _

end Multiequalizer

namespace Multicoequalizer

variable {J : MultispanShape.{w, w'}} (I : MultispanIndex J C) [HasMulticoequalizer I]

/-- The canonical map from the multiequalizer to the objects on the left. -/
abbrev π (b : J.R) : I.right b ⟶ multicoequalizer I :=
  colimit.ι I.multispan (WalkingMultispan.right _)

/-- The multicofork associated to the multicoequalizer. -/
abbrev multicofork : Multicofork I :=
  colimit.cocone _

@[simp]
theorem multicofork_π (b) : (Multicoequalizer.multicofork I).π b = Multicoequalizer.π I b :=
  rfl

-- @[simp] -- Porting note: LHS simplifies to obtain the normal form below
theorem multicofork_ι_app_right (b) :
    (Multicoequalizer.multicofork I).ι.app (WalkingMultispan.right b) = Multicoequalizer.π I b :=
  rfl

@[simp]
theorem multicofork_ι_app_right' (b) :
    colimit.ι (MultispanIndex.multispan I) (WalkingMultispan.right b) = π I b :=
  rfl

@[reassoc]
theorem condition (a) :
    I.fst a ≫ Multicoequalizer.π I (J.fst a) = I.snd a ≫ Multicoequalizer.π I (J.snd a) :=
  Multicofork.condition _ _

/-- Construct a morphism from the multicoequalizer from its universal property. -/
abbrev desc (W : C) (k : ∀ b, I.right b ⟶ W)
    (h : ∀ a, I.fst a ≫ k (J.fst a) = I.snd a ≫ k (J.snd a)) : multicoequalizer I ⟶ W :=
  colimit.desc _ (Multicofork.ofπ I _ k h)

@[reassoc]
theorem π_desc (W : C) (k : ∀ b, I.right b ⟶ W)
    (h : ∀ a, I.fst a ≫ k (J.fst a) = I.snd a ≫ k (J.snd a)) (b) :
    Multicoequalizer.π I b ≫ Multicoequalizer.desc I _ k h = k _ :=
  colimit.ι_desc _ _

@[ext]
theorem hom_ext {W : C} (i j : multicoequalizer I ⟶ W)
    (h : ∀ b, Multicoequalizer.π I b ≫ i = Multicoequalizer.π I b ≫ j) : i = j :=
  colimit.hom_ext
    (by
      rintro (a | b)
      · simp_rw [← colimit.w I.multispan (WalkingMultispan.Hom.fst a), Category.assoc, h]
      · apply h)

variable [HasCoproduct I.left] [HasCoproduct I.right]

instance : HasCoequalizer I.fstSigmaMap I.sndSigmaMap :=
  ⟨⟨⟨_,
      IsColimit.ofPreservesCoconeInitial
        I.multicoforkEquivSigmaCofork.functor (colimit.isColimit _)⟩⟩⟩

/-- The multicoequalizer is isomorphic to the coequalizer of `∐ I.left ⇉ ∐ I.right`. -/
def isoCoequalizer : multicoequalizer I ≅ coequalizer I.fstSigmaMap I.sndSigmaMap :=
  colimit.isoColimitCocone
    ⟨_,
      IsColimit.ofPreservesCoconeInitial I.multicoforkEquivSigmaCofork.inverse
        (colimit.isColimit _)⟩

/-- The canonical projection `∐ I.right ⟶ multicoequalizer I`. -/
def sigmaπ : ∐ I.right ⟶ multicoequalizer I :=
  coequalizer.π I.fstSigmaMap I.sndSigmaMap ≫ (isoCoequalizer I).inv

@[reassoc (attr := simp)]
theorem ι_sigmaπ (b) : Sigma.ι I.right b ≫ sigmaπ I = π I b := by
  rw [sigmaπ, ← Category.assoc, Iso.comp_inv_eq, isoCoequalizer]
  simp only [MultispanIndex.multicoforkEquivSigmaCofork_inverse,
    MultispanIndex.ofSigmaCoforkFunctor_obj, colimit.isoColimitCocone_ι_hom,
    Multicofork.ofSigmaCofork_pt, colimit.cocone_x, Multicofork.π_eq_app_right]
  rfl

instance : Epi (sigmaπ I) := epi_comp _ _

end Multicoequalizer

end

end CategoryTheory.Limits
