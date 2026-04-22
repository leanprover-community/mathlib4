/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.ConeCategory

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

@[expose] public section


namespace CategoryTheory.Limits

universe t w w' v u

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

/-- Given a linearly ordered type `ι`, this is the shape of multicoequalizer diagrams
corresponding to situations where we want to coequalize two families of maps
`V ⟨i, j⟩ ⟶ U i` and `V ⟨i, j⟩ ⟶ U j` with `i < j`. -/
@[simps]
def MultispanShape.ofLinearOrder (ι : Type w) [LinearOrder ι] : MultispanShape where
  L := {x : ι × ι | x.1 < x.2}
  R := ι
  fst x := x.1.1
  snd x := x.1.2

instance : Unique (MultispanShape.ofLinearOrder Bool).L where
  default := ⟨⟨False, True⟩, by simp⟩
  uniq := by rintro ⟨⟨(_ | _), (_ | _)⟩, _⟩ <;> tauto

/-- The type underlying the multiequalizer diagram. -/
inductive WalkingMulticospan (J : MulticospanShape.{w, w'}) : Type max w w'
  | left : J.L → WalkingMulticospan J
  | right : J.R → WalkingMulticospan J

/-- The type underlying the multicoequalizer diagram. -/
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

/-- Construct a natural isomorphism between functors out of a walking multicospan from its
components. -/
@[simps!]
def functorExt {C : Type*} [Category* C] {F G : WalkingMulticospan J ⥤ C}
    (left : ∀ i, F.obj (.left i) ≅ G.obj (.left i))
    (right : ∀ i, F.obj (.right i) ≅ G.obj (.right i))
    (wl : ∀ i, F.map (WalkingMulticospan.Hom.fst i) ≫ (right i).hom =
      (left _).hom ≫ G.map (WalkingMulticospan.Hom.fst i) := by cat_disch)
    (wr : ∀ i, F.map (WalkingMulticospan.Hom.snd i) ≫ (right i).hom =
      (left _).hom ≫ G.map (WalkingMulticospan.Hom.snd i) := by cat_disch) :
    F ≅ G :=
  NatIso.ofComponents (fun j ↦ match j with | .left i => left i | .right i => right i) <| by
    rintro _ _ ⟨_⟩ <;> simp [wl, wr]

lemma functor_ext {C : Type*} [Category* C] {F G : WalkingMulticospan J ⥤ C}
    (left : ∀ i, F.obj (.left i) = G.obj (.left i))
    (right : ∀ i, F.obj (.right i) = G.obj (.right i))
    (wl : ∀ i, F.map (Hom.fst i) ≫ eqToHom (right i) = eqToHom (left _) ≫ G.map (Hom.fst i))
    (wr : ∀ i, F.map (Hom.snd i) ≫ eqToHom (right i) = eqToHom (left _) ≫ G.map (Hom.snd i)) :
    F = G :=
  Functor.ext_of_iso
    (functorExt (fun _ ↦ eqToIso (left _)) (fun _ ↦ eqToIso (right _)) wl wr)
    (by rintro (_ | _) <;> grind) (by rintro (_ | _) <;> simp)

end WalkingMulticospan

namespace WalkingMultispan

variable {J : MultispanShape.{w, w'}}

instance [Inhabited J.L] : Inhabited (WalkingMultispan J) :=
  ⟨left default⟩

instance [Small.{t} J.L] [Small.{t} J.R] : Small.{t} (WalkingMultispan J) :=
  small_of_surjective (f := Sum.elim WalkingMultispan.left WalkingMultispan.right)
    (by rintro (_ | _) <;> aesop)

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

/-- Construct a natural isomorphism between functors out of a walking multispan from its
components. -/
@[simps!]
def functorExt {C : Type*} [Category* C] {F G : WalkingMultispan J ⥤ C}
    (left : ∀ i, F.obj (.left i) ≅ G.obj (.left i))
    (right : ∀ i, F.obj (.right i) ≅ G.obj (.right i))
    (wl : ∀ i, F.map (WalkingMultispan.Hom.fst i) ≫ (right _).hom =
      (left i).hom ≫ G.map (WalkingMultispan.Hom.fst _) := by cat_disch)
    (wr : ∀ i, F.map (WalkingMultispan.Hom.snd i) ≫ (right _).hom =
      (left i).hom ≫ G.map (WalkingMultispan.Hom.snd _) := by cat_disch) :
    F ≅ G :=
  NatIso.ofComponents (fun j ↦ match j with | .left i => left i | .right i => right i) <| by
    rintro _ _ ⟨_⟩ <;> simp [wl, wr]

instance (a : WalkingMultispan J) : Unique (a ⟶ a) where
  default := 𝟙 _
  uniq := by rintro ⟨⟩; rfl

instance (a b : J.L) : Subsingleton (left a ⟶ left b) := by
  by_cases h : a = b
  · subst h
    infer_instance
  · have : IsEmpty (left a ⟶ left b) := ⟨by rintro ⟨⟩; simp at h⟩
    infer_instance

instance (a b : J.R) : Subsingleton (right a ⟶ right b) := by
  by_cases h : a = b
  · subst h
    infer_instance
  · have : IsEmpty (right a ⟶ right b) := ⟨by rintro ⟨⟩; simp at h⟩
    infer_instance

instance (a : J.R) (b : J.L) : IsEmpty (right a ⟶ left b) := ⟨by rintro ⟨⟩⟩

instance : LocallySmall.{t} (WalkingMultispan J) where
  hom_small := by
    rintro (l | r) (l' | r')
    · infer_instance
    · let T₁ := { u : Unit // J.fst l = r' }
      let T₂ := { u : Unit // J.snd l = r' }
      let f : T₁ ⊕ T₂ → (left l ⟶ right r') :=
        Sum.elim (fun ⟨_, h⟩ ↦ by subst h; exact Hom.fst l)
          (fun ⟨_, h⟩ ↦ by subst h; exact Hom.snd l)
      refine small_of_surjective (f := f) ?_
      rintro (_ | _)
      · exact ⟨Sum.inl ⟨⟨⟩, rfl⟩, rfl⟩
      · exact ⟨Sum.inr ⟨⟨⟩, rfl⟩, rfl⟩
    · infer_instance
    · infer_instance

variable (J) in
/-- The bijection `WalkingMultispan J ≃ J.L ⊕ J.R`. -/
def equiv : WalkingMultispan J ≃ J.L ⊕ J.R where
  toFun x := match x with
    | left a => Sum.inl a
    | right b => Sum.inr b
  invFun := Sum.elim left right
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

variable (J) in
/-- The bijection `Arrow (WalkingMultispan J) ≃ WalkingMultispan J ⊕ J.L ⊕ J.L`. -/
def arrowEquiv :
    Arrow (WalkingMultispan J) ≃ WalkingMultispan J ⊕ J.L ⊕ J.L where
  toFun f := match f.hom with
    | .id x => Sum.inl x
    | .fst a => Sum.inr (Sum.inl a)
    | .snd a => Sum.inr (Sum.inr a)
  invFun :=
    Sum.elim (fun X ↦ Arrow.mk (𝟙 X))
      (Sum.elim (fun a ↦ Arrow.mk (Hom.fst a : left _ ⟶ right _))
        (fun a ↦ Arrow.mk (Hom.snd a : left _ ⟶ right _)))
  left_inv := by rintro ⟨_, _, (_ | _ | _)⟩ <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

end WalkingMultispan

/-- This is a structure encapsulating the data necessary to define a `Multicospan`. -/
@[nolint checkUnivs]
structure MulticospanIndex (J : MulticospanShape.{w, w'})
    (C : Type u) [Category.{v} C] where
  /-- Left map, from `J.L` to `C` -/
  left : J.L → C
  /-- Right map, from `J.R` to `C` -/
  right : J.R → C
  /-- A family of maps from `left (J.fst b)` to `right b` -/
  fst : ∀ b, left (J.fst b) ⟶ right b
  /-- A family of maps from `left (J.snd b)` to `right b` -/
  snd : ∀ b, left (J.snd b) ⟶ right b

/-- This is a structure encapsulating the data necessary to define a `Multispan`. -/
@[nolint checkUnivs]
structure MultispanIndex (J : MultispanShape.{w, w'})
    (C : Type u) [Category.{v} C] where
  /-- Left map, from `J.L` to `C` -/
  left : J.L → C
  /-- Right map, from `J.R` to `C` -/
  right : J.R → C
  /-- A family of maps from `left a` to `right (J.fst a)` -/
  fst : ∀ a, left a ⟶ right (J.fst a)
  /-- A family of maps from `left a` to `right (J.snd a)` -/
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
    rintro (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) <;> cat_disch

/-- The induced map `c.pt ⟶ d.pt` via `I.fst`, when `d` is limiting. -/
def fstPiMapOfIsLimit (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) : c.pt ⟶ d.pt :=
  Fan.IsLimit.lift hd fun i ↦ c.proj _ ≫ I.fst i

/-- The induced map `c.pt ⟶ d.pt` via `I.snd`, when `d` is limiting. -/
def sndPiMapOfIsLimit (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) : c.pt ⟶ d.pt :=
  Fan.IsLimit.lift hd fun i ↦ c.proj _ ≫ I.snd i

@[reassoc (attr := simp)]
lemma fstPiMapOfIsLimit_proj (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) (i) :
    fstPiMapOfIsLimit I c hd ≫ d.proj i = c.proj _ ≫ I.fst i := by
  simp [fstPiMapOfIsLimit]

@[reassoc (attr := simp)]
lemma sndPiMapOfIsLimit_proj (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) (i) :
    sndPiMapOfIsLimit I c hd ≫ d.proj i = c.proj _ ≫ I.snd i := by
  simp [sndPiMapOfIsLimit]

/-- Taking the multiequalizer over the multicospan index is equivalent to taking the equalizer over
the two induced morphisms `c.pt ⇉ d.pt`. This is the diagram of the latter when `d` is limiting. -/
@[simps!]
protected noncomputable def parallelPairDiagramOfIsLimit
    (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) : WalkingParallelPair ⥤ C :=
  parallelPair (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)

variable [HasProduct I.left] [HasProduct I.right]

/-- The induced map `∏ᶜ I.left ⟶ ∏ᶜ I.right` via `I.fst`. -/
noncomputable def fstPiMap : ∏ᶜ I.left ⟶ ∏ᶜ I.right :=
  I.fstPiMapOfIsLimit _ <| limit.isLimit (Discrete.functor I.right)

/-- The induced map `∏ᶜ I.left ⟶ ∏ᶜ I.right` via `I.snd`. -/
noncomputable def sndPiMap : ∏ᶜ I.left ⟶ ∏ᶜ I.right :=
  I.sndPiMapOfIsLimit _ <| limit.isLimit (Discrete.functor I.right)

@[reassoc (attr := simp)]
theorem fstPiMap_π (b) : I.fstPiMap ≫ Pi.π I.right b = Pi.π I.left _ ≫ I.fst b :=
  fstPiMapOfIsLimit_proj ..

@[reassoc (attr := simp)]
theorem sndPiMap_π (b) : I.sndPiMap ≫ Pi.π I.right b = Pi.π I.left _ ≫ I.snd b :=
  sndPiMapOfIsLimit_proj ..

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
    rintro (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) <;> cat_disch

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

/-- The induced map `c.pt ⟶ d.pt` via `I.fst`, when `c` is colimiting. -/
def fstSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) :
    c.pt ⟶ d.pt :=
  Cofan.IsColimit.desc hc fun i ↦ I.fst i ≫ d.inj _

/-- The induced map `c.pt ⟶ d.pt` via `I.snd`, when `c` is colimiting. -/
def sndSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) :
    c.pt ⟶ d.pt :=
  Cofan.IsColimit.desc hc fun i ↦ I.snd i ≫ d.inj _

@[reassoc (attr := simp)]
lemma inj_fstSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) (i) :
    c.inj _ ≫ fstSigmaMapOfIsColimit I d hc = I.fst i ≫ d.inj _ := by
  simp [fstSigmaMapOfIsColimit]

@[reassoc (attr := simp)]
lemma inj_sndSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) (i) :
    c.inj _ ≫ sndSigmaMapOfIsColimit I d hc = I.snd i ≫ d.inj _ := by
  simp [sndSigmaMapOfIsColimit]

/-- Taking the multicoequalizer over the multispan index is equivalent to taking the coequalizer
over the two induced morphisms `c.pt ⇉ d.pt`. This is the diagram of the latter when `c` is
colimiting. -/
@[simps!]
protected noncomputable def parallelPairDiagramOfIsColimit
    {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) : WalkingParallelPair ⥤ C :=
  parallelPair (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)

variable [HasCoproduct I.left] [HasCoproduct I.right]

/-- The induced map `∐ I.left ⟶ ∐ I.right` via `I.fst`. -/
noncomputable def fstSigmaMap : ∐ I.left ⟶ ∐ I.right :=
  I.fstSigmaMapOfIsColimit _ <| colimit.isColimit _

/-- The induced map `∐ I.left ⟶ ∐ I.right` via `I.snd`. -/
noncomputable def sndSigmaMap : ∐ I.left ⟶ ∐ I.right :=
  I.sndSigmaMapOfIsColimit _ <| colimit.isColimit _

@[reassoc (attr := simp)]
theorem ι_fstSigmaMap (b) : Sigma.ι I.left b ≫ I.fstSigmaMap = I.fst b ≫ Sigma.ι I.right _ :=
  inj_fstSigmaMapOfIsColimit ..

@[reassoc (attr := simp)]
theorem ι_sndSigmaMap (b) : Sigma.ι I.left b ≫ I.sndSigmaMap = I.snd b ≫ Sigma.ι I.right _ :=
  inj_sndSigmaMapOfIsColimit ..

/--
Taking the multicoequalizer over the multispan index is equivalent to taking the coequalizer over
the two morphisms `∐ I.left ⇉ ∐ I.right`. This is the diagram of the latter.
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

@[simp]
lemma ι_ofι {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
    (P : C) (ι : ∀ a, P ⟶ I.left a)
    (w : ∀ b, ι (J.fst b) ≫ I.fst b = ι (J.snd b) ≫ I.snd b) (i) :
    (ofι I P ι w).ι i = ι i :=
  rfl

@[reassoc (attr := simp)]
theorem condition (b) : K.ι (J.fst b) ≫ I.fst b = K.ι (J.snd b) ≫ I.snd b := by
  rw [← app_right_eq_ι_comp_fst, ← app_right_eq_ι_comp_snd]

/-- Constructor for isomorphisms between multiforks. -/
@[simps!]
def ext {t s : Multifork I} (e : t.pt ≅ s.pt)
    (h : ∀ i : J.L, e.hom ≫ s.ι i = t.ι i := by cat_disch) : t ≅ s :=
  Cone.ext e (by rintro (i | j) <;> simp [← h])

/-- Every multifork is isomorphic to one of the form `Multifork.ofι`. -/
@[simps!]
def isoOfι (t : Multifork I) : t ≅ ofι _ t.pt t.ι t.condition :=
  ext (Iso.refl _)

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
  rintro (_ | b)
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

/-- Given two multiforks with isomorphic components in such a way that the natural diagrams
commute, then one is a limit if and only if the other one is. -/
def isLimitEquivOfIsos {I I' : MulticospanIndex J C} (c : Multifork I) (c' : Multifork I')
    (e : c.pt ≅ c'.pt) (el : ∀ i, I.left i ≅ I'.left i) (er : ∀ i, I.right i ≅ I'.right i)
    (hl : ∀ (i : J.R), I.fst i ≫ (er i).hom = (el (J.fst i)).hom ≫ I'.fst i := by cat_disch)
    (hr : ∀ (i : J.R), I.snd i ≫ (er i).hom = (el (J.snd i)).hom ≫ I'.snd i := by cat_disch)
    (he : ∀ (i : J.L), e.hom ≫ c'.ι i = c.ι i ≫ (el i).hom := by cat_disch) :
    IsLimit c ≃ IsLimit c' :=
  letI i : I.multicospan ≅ I'.multicospan :=
    WalkingMulticospan.functorExt el er hl hr
  IsLimit.equivOfNatIsoOfIso i _ _ (Multifork.ext e he)

variable (K)
variable {c : Fan I.left} (hc : IsLimit c) {d : Fan I.right} (hd : IsLimit d)

@[reassoc (attr := simp)]
theorem pi_condition :
    Fan.IsLimit.lift hc K.ι ≫ I.fstPiMapOfIsLimit c hd =
      Fan.IsLimit.lift hc K.ι ≫ I.sndPiMapOfIsLimit c hd := by
  apply Fan.IsLimit.hom_ext hd
  simp

/-- Given a multifork, we may obtain a fork over `c.pt ⇉ d.pt`. -/
@[simps! pt]
def toPiFork (K : Multifork I) :
    Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd) :=
  .ofι (Fan.IsLimit.lift hc K.ι) (by simp)

@[simp]
theorem toPiFork_π_app_zero :
    (K.toPiFork hc hd).ι = Fan.IsLimit.lift hc K.ι :=
  rfl

@[simp]
theorem toPiFork_π_app_one :
    (K.toPiFork hc hd).π.app WalkingParallelPair.one =
      Fan.IsLimit.lift hc K.ι ≫ I.fstPiMapOfIsLimit c hd :=
  rfl

variable {hd} in
/-- Given a fork over `c.pt ⇉ d.pt`, we may obtain a multifork. -/
@[simps pt]
def ofPiFork
    (a : Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)) :
    Multifork I where
  pt := a.pt
  π.app
    | WalkingMulticospan.left _ => a.ι ≫ c.proj _
    | WalkingMulticospan.right _ => a.ι ≫ I.fstPiMapOfIsLimit c hd ≫ d.proj _
  π.naturality := by
    rintro (_ | _) (_ | _) (_ | _ | _)
    · simp
    · simp
    · dsimp; rw [a.condition_assoc]; simp
    · simp

@[simp]
theorem ofPiFork_ι (a : Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)) (i) :
    (ofPiFork a).ι i = a.ι ≫ c.proj _ :=
  rfl

@[deprecated (since := "2025-12-08")]
alias ofPiFork_π_app_left := ofPiFork_ι

@[simp]
theorem ofPiFork_π_app_right
    (a : Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)) (i) :
    (ofPiFork a).π.app (WalkingMulticospan.right i) =
      a.ι ≫ I.fstPiMapOfIsLimit c hd ≫ d.proj _ :=
  rfl

end Multifork

namespace MulticospanIndex

variable {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
variable {c : Fan I.left} (hc : IsLimit c) {d : Fan I.right} (hd : IsLimit d)

/-- `Multifork.toPiFork` as a functor. -/
@[simps]
def toPiForkFunctor :
    Multifork I ⥤ Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd) where
  obj := Multifork.toPiFork hc hd
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by
        rintro (_ | _)
        · apply Fan.IsLimit.hom_ext hc
          simp
        · apply Fan.IsLimit.hom_ext hd
          simp }

/-- `Multifork.ofPiFork` as a functor. -/
@[simps]
def ofPiForkFunctor :
    Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd) ⥤ Multifork I where
  obj := Multifork.ofPiFork
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by rintro (_ | _) <;> simp }

/-- The category of multiforks is equivalent to the category of forks over `c.pt ⇉ d.pt`. It then
follows from `CategoryTheory.IsLimit.ofPreservesConeTerminal` (or `reflects`) that it preserves
and reflects limit cones. -/
@[simps]
def multiforkEquivPiForkOfIsLimit :
    Multifork I ≌ Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd) where
  functor := toPiForkFunctor I hc hd
  inverse := ofPiForkFunctor I hd
  unitIso :=
    NatIso.ofComponents fun K =>
      Cone.ext (Iso.refl _) (by
        rintro (_ | _) <;> simp)
  counitIso :=
    NatIso.ofComponents (fun K =>
      Fork.ext (Iso.refl _) <| Fan.IsLimit.hom_ext hc _ _ (by simp))

variable [HasProduct I.left] [HasProduct I.right]

/-- The category of multiforks is equivalent to the category of forks over `∏ᶜ I.left ⇉ ∏ᶜ I.right`.
It then follows from `CategoryTheory.IsLimit.ofPreservesConeTerminal` (or `reflects`) that it
preserves and reflects limit cones.
-/
@[simps!]
noncomputable def multiforkEquivPiFork : Multifork I ≌ Fork I.fstPiMap I.sndPiMap :=
  multiforkEquivPiForkOfIsLimit I (limit.isLimit _) (limit.isLimit _)

/-- The constant `MulticospanIndex` for a pair of parallel morphisms. -/
@[simps]
def ofParallelHoms (J : MulticospanShape) {X Y : C} (f g : X ⟶ Y) : MulticospanIndex J C where
  left _ := X
  right _ := Y
  fst _ := f
  snd _ := g

set_option backward.isDefEq.respectTransparency false in
/-- A fork on a pair of morphisms `f` and `g` is the same as a multifork on the
single point index defined by `f` and `g`. -/
def multiforkOfParallelHomsEquivFork (J : MulticospanShape) [Unique J.L] [Unique J.R] {X Y : C}
    (f g : X ⟶ Y) :
    Multifork (ofParallelHoms J f g) ≌ Fork f g := by
  refine (multiforkEquivPiForkOfIsLimit _
      (Fan.isLimitMkOfUnique (Iso.refl X) _) (Fan.isLimitMkOfUnique (Iso.refl Y) _)).trans
      (Fork.equivOfIsos (.refl _) (.refl _) ?_ ?_)
  · refine Fan.IsLimit.hom_ext (Fan.isLimitMkOfUnique (Iso.refl Y) J.R) _ _ fun _ ↦ ?_
    rw [Category.assoc, Iso.refl_hom ((Fan.mk Y fun x ↦ (Iso.refl Y).hom).pt),
      Category.comp_id, fstPiMapOfIsLimit_proj]
    simp
  · refine Fan.IsLimit.hom_ext (Fan.isLimitMkOfUnique (Iso.refl Y) J.R) _ _ fun _ ↦ ?_
    rw [Category.assoc, Iso.refl_hom ((Fan.mk Y fun x ↦ (Iso.refl Y).hom).pt),
      Category.comp_id, sndPiMapOfIsLimit_proj]
    simp

@[simp]
lemma multiforkOfParallelHomsEquivFork_functor_obj_ι (J : MulticospanShape) [Unique J.L]
    [Unique J.R] {X Y : C} (f g : X ⟶ Y) (c : Multifork (ofParallelHoms J f g)) :
    ((multiforkOfParallelHomsEquivFork J f g).functor.obj c).ι = c.ι default :=
  Fan.IsLimit.fac (Fan.isLimitMkOfUnique (Iso.refl X) J.L) _ default

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma multiforkOfParallelHomsEquivFork_inverse_obj_ι (J : MulticospanShape) [Unique J.L]
    [Unique J.R] {X Y : C} (f g : X ⟶ Y) (c : Fork f g) (a : J.L) :
    ((multiforkOfParallelHomsEquivFork J f g).inverse.obj c).ι a = c.ι := by
  simp [multiforkOfParallelHomsEquivFork]

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

set_option backward.isDefEq.respectTransparency false in
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

variable {K}

lemma IsColimit.hom_ext (hK : IsColimit K) {T : C} {f g : K.pt ⟶ T}
    (h : ∀ a, K.π a ≫ f = K.π a ≫ g) : f = g := by
  apply hK.hom_ext
  rintro (_ | _) <;> simp [h]

/-- Constructor for morphisms from the point of a colimit multicofork. -/
def IsColimit.desc (hK : IsColimit K) {T : C} (k : ∀ a, I.right a ⟶ T)
    (hk : ∀ b, I.fst b ≫ k (J.fst b) = I.snd b ≫ k (J.snd b)) :
    K.pt ⟶ T :=
  hK.desc (Multicofork.ofπ _ _ k hk)

@[reassoc (attr := simp)]
lemma IsColimit.fac (hK : IsColimit K) {T : C} (k : ∀ a, I.right a ⟶ T)
    (hk : ∀ b, I.fst b ≫ k (J.fst b) = I.snd b ≫ k (J.snd b)) (a : J.R) :
    K.π a ≫ IsColimit.desc hK k hk = k a :=
  hK.fac _ _

variable (K)
variable {c : Cofan I.left} (hc : IsColimit c) {d : Cofan I.right} (hd : IsColimit d)

@[reassoc (attr := simp)]
theorem sigma_condition :
    I.fstSigmaMapOfIsColimit d hc ≫ Cofan.IsColimit.desc hd K.π =
      I.sndSigmaMapOfIsColimit d hc ≫ Cofan.IsColimit.desc hd K.π := by
  apply Cofan.IsColimit.hom_ext hc
  simp

/-- Given a multicofork, we may obtain a cofork over `c.pt ⇉ d.pt`. -/
@[simps! pt]
noncomputable def toSigmaCofork (K : Multicofork I) :
    Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc) :=
  .ofπ (Cofan.IsColimit.desc hd K.π) (by simp)

@[simp]
theorem toSigmaCofork_π :
    (K.toSigmaCofork hc hd).π = Cofan.IsColimit.desc hd K.π :=
  rfl

variable {hc} in
/-- Given a cofork over `c.pt ⇉ d.pt`, we may obtain a multicofork. -/
@[simps pt]
noncomputable def ofSigmaCofork
    (a : Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)) :
    Multicofork I where
  pt := a.pt
  ι :=
    { app := fun x =>
        match x with
        | WalkingMultispan.left _ => c.inj _ ≫ I.fstSigmaMapOfIsColimit d hc ≫ a.π
        | WalkingMultispan.right _ => d.inj _ ≫ a.π
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _)
        · simp
        · simp
        · simp [a.condition]
        · simp }

@[simp]
theorem ofSigmaCofork_ι_app_left
    (a : Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)) (i) :
    (ofSigmaCofork a).ι.app (WalkingMultispan.left i) =
      c.inj _ ≫ I.fstSigmaMapOfIsColimit d hc ≫ a.π :=
  rfl

@[simp]
theorem ofSigmaCofork_π
    (a : Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)) (i) :
    (ofSigmaCofork a).π i = d.inj i ≫ a.π :=
  rfl

@[deprecated (since := "2025-12-08")]
alias ofSigmaCofork_ι_app_right := ofSigmaCofork_π

@[deprecated (since := "2025-12-08")]
alias ofSigmaCofork_ι_app_right' := ofSigmaCofork_π

/-- Constructor for isomorphisms between multicoforks. -/
@[simps!]
def ext {K K' : Multicofork I}
    (e : K.pt ≅ K'.pt) (h : ∀ (i : J.R), K.π i ≫ e.hom = K'.π i := by cat_disch) :
    K ≅ K' :=
  Cocone.ext e (by rintro (i | j) <;> simp [h])

/-- Every multicofork is isomorphic to one of the form `Multicofork.ofπ`. -/
@[simps!]
def isoOfπ (t : Multicofork I) : t ≅ ofπ _ t.pt t.π t.condition :=
  ext (Iso.refl _)

end Multicofork

namespace MultispanIndex

variable {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
variable {c : Cofan I.left} (hc : IsColimit c) {d : Cofan I.right} (hd : IsColimit d)

/-- `Multicofork.toSigmaCofork` as a functor. -/
@[simps]
noncomputable def toSigmaCoforkFunctor :
    Multicofork I ⥤ Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc) where
  obj := Multicofork.toSigmaCofork hc hd
  map {K₁ K₂} f :=
  { hom := f.hom
    w := by
      rintro (_ | _)
      · apply Cofan.IsColimit.hom_ext hc
        simp
      · apply Cofan.IsColimit.hom_ext hd
        simp }

/-- `Multicofork.ofSigmaCofork` as a functor. -/
@[simps]
noncomputable def ofSigmaCoforkFunctor :
    Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc) ⥤ Multicofork I where
  obj := Multicofork.ofSigmaCofork
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by rintro (_ | _) <;> simp }

/-- The category of multicoforks is equivalent to the category of coforks over `c.pt ⇉ d.pt`. It
then follows from `CategoryTheory.IsColimit.ofPreservesCoconeInitial` (or `reflects`) that it
preserves and reflects colimit cocones. -/
@[simps]
noncomputable def multicoforkEquivSigmaCoforkOfIsColimit :
    Multicofork I ≌ Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc) where
  functor := toSigmaCoforkFunctor I hc hd
  inverse := ofSigmaCoforkFunctor I hc
  unitIso := NatIso.ofComponents fun K => Cocone.ext (Iso.refl _) (by
      rintro (_ | _) <;> simp)
  counitIso := NatIso.ofComponents fun K =>
    Cofork.ext (Iso.refl _)
      (by
        apply Cofan.IsColimit.hom_ext hd
        simp)

variable [HasCoproduct I.left] [HasCoproduct I.right]

/--
The category of multicoforks is equivalent to the category of coforks over `∐ I.left ⇉ ∐ I.right`.
It then follows from `CategoryTheory.IsColimit.ofPreservesCoconeInitial` (or `reflects`) that
it preserves and reflects colimit cocones.
-/
@[simps!]
noncomputable def multicoforkEquivSigmaCofork :
    Multicofork I ≌ Cofork I.fstSigmaMap I.sndSigmaMap :=
  multicoforkEquivSigmaCoforkOfIsColimit _ (colimit.isColimit _) (colimit.isColimit _)

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

/-- For `I : MultispanIndex J C`, we say that it has a multicoequalizer if the associated
multispan has a colimit. -/
abbrev HasMulticoequalizer {J : MultispanShape.{w, w'}} (I : MultispanIndex J C) :=
  HasColimit I.multispan

/-- The multicoequalizer of `I : MultispanIndex J C`. -/
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

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ιPi_π (a) : ιPi I ≫ Pi.π I.left a = ι I a := by
  rw [ιPi, Category.assoc, ← Iso.eq_inv_comp, isoEqualizer]
  simp only [limit.isoLimitCone_inv_π, MulticospanIndex.multiforkEquivPiFork_inverse_obj_pt,
    limit.cone_x, MulticospanIndex.multiforkEquivPiFork_inverse_obj_π_app]
  rfl

instance : Mono (ιPi I) := mono_comp _ _

end Multiequalizer

namespace Multicoequalizer

variable {J : MultispanShape.{w, w'}} (I : MultispanIndex J C) [HasMulticoequalizer I]

/-- The canonical map from `I.right b` to the multicoequalizer. -/
abbrev π (b : J.R) : I.right b ⟶ multicoequalizer I :=
  colimit.ι I.multispan (WalkingMultispan.right _)

/-- The multicofork associated to the multicoequalizer. -/
abbrev multicofork : Multicofork I :=
  colimit.cocone _

@[simp]
theorem multicofork_π (b) : (Multicoequalizer.multicofork I).π b = Multicoequalizer.π I b :=
  rfl

theorem multicofork_ι_app_right (b) :
    (Multicoequalizer.multicofork I).ι.app (WalkingMultispan.right b) = Multicoequalizer.π I b :=
  rfl

/-- `@[simp]`-normal form of `multicofork_ι_app_right`. -/
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_sigmaπ (b) : Sigma.ι I.right b ≫ sigmaπ I = π I b := by
  rw [sigmaπ, ← Category.assoc, Iso.comp_inv_eq, isoCoequalizer]
  simp
  rfl

instance : Epi (sigmaπ I) := epi_comp _ _

end Multicoequalizer

end

/-- The inclusion functor `WalkingMultispan (.ofLinearOrder ι) ⥤ WalkingMultispan (.prod ι)`. -/
@[simps!]
def WalkingMultispan.inclusionOfLinearOrder (ι : Type w) [LinearOrder ι] :
    WalkingMultispan (.ofLinearOrder ι) ⥤ WalkingMultispan (.prod ι) :=
  MultispanIndex.multispan
    { left j := .left j.1
      right i := .right i
      fst j := WalkingMultispan.Hom.fst (J := .prod ι) j.1
      snd j := WalkingMultispan.Hom.snd (J := .prod ι) j.1 }

section symmetry

namespace MultispanIndex

variable {ι : Type w} (I : MultispanIndex (.prod ι) C)

/-- Structure expressing a symmetry of `I : MultispanIndex (.prod ι) C` which
allows to compare the corresponding multicoequalizer to the multicoequalizer
of `I.toLinearOrder`. -/
structure SymmStruct where
  /-- the symmetry isomorphism -/
  iso (i j : ι) : I.left ⟨i, j⟩ ≅ I.left ⟨j, i⟩
  iso_hom_fst (i j : ι) : (iso i j).hom ≫ I.fst ⟨j, i⟩ = I.snd ⟨i, j⟩
  iso_hom_snd (i j : ι) : (iso i j).hom ≫ I.snd ⟨j, i⟩ = I.fst ⟨i, j⟩
  fst_eq_snd (i : ι) : I.fst ⟨i, i⟩ = I.snd ⟨i, i⟩

attribute [reassoc] SymmStruct.iso_hom_fst SymmStruct.iso_hom_snd

variable [LinearOrder ι]

/-- The multispan index for `MultispanShape.ofLinearOrder ι` deduced from
a multispan index for `MultispanShape.prod ι` when `ι` is linearly ordered. -/
@[simps]
def toLinearOrder : MultispanIndex (.ofLinearOrder ι) C where
  left j := I.left j.1
  right i := I.right i
  fst j := I.fst j.1
  snd j := I.snd j.1

/-- Given a linearly ordered type `ι` and `I : MultispanIndex (.prod ι) C`,
this is the isomorphism of functors between
`WalkingMultispan.inclusionOfLinearOrder ι ⋙ I.multispan`
and `I.toLinearOrder.multispan`. -/
@[simps!]
def toLinearOrderMultispanIso :
    WalkingMultispan.inclusionOfLinearOrder ι ⋙ I.multispan ≅
      I.toLinearOrder.multispan :=
  NatIso.ofComponents (fun i ↦ match i with
    | .left _ => Iso.refl _
    | .right _ => Iso.refl _)

end MultispanIndex

namespace Multicofork

variable {ι : Type w} [LinearOrder ι] {I : MultispanIndex (.prod ι) C}

/-- The multicofork for `I.toLinearOrder` deduced from a multicofork
for `I : MultispanIndex (.prod ι) C` when `ι` is linearly ordered. -/
def toLinearOrder (c : Multicofork I) : Multicofork I.toLinearOrder :=
  Multicofork.ofπ _ c.pt c.π (fun _ ↦ c.condition _)

set_option backward.isDefEq.respectTransparency false in
/-- The multicofork for `I : MultispanIndex (.prod ι) C` deduced from
a multicofork for `I.toLinearOrder` when `ι` is linearly ordered
and `I` is symmetric. -/
def ofLinearOrder (c : Multicofork I.toLinearOrder) (h : I.SymmStruct) :
    Multicofork I :=
  Multicofork.ofπ _ c.pt c.π (by
    rintro ⟨x, y⟩
    obtain hxy | rfl | hxy := lt_trichotomy x y
    · exact c.condition ⟨⟨x, y⟩, hxy⟩
    · simp [h.fst_eq_snd]
    · have := c.condition ⟨⟨y, x⟩, hxy⟩
      dsimp at this ⊢
      rw [← h.iso_hom_fst_assoc, ← h.iso_hom_snd_assoc, this])

set_option backward.isDefEq.respectTransparency false in
/-- If `ι` is a linearly ordered type, `I : MultispanIndex (.prod ι) C`, and
`c` a colimit multicofork for `I`, then `c.toLinearOrder` is a colimit
multicofork for `I.toLinearOrder`. -/
def isColimitToLinearOrder (c : Multicofork I) (hc : IsColimit c) (h : I.SymmStruct) :
    IsColimit c.toLinearOrder :=
  Multicofork.IsColimit.mk _ (fun s ↦ hc.desc (ofLinearOrder s h))
    (fun s _ ↦ hc.fac (ofLinearOrder s h) _)
    (fun s m hm ↦ Multicofork.IsColimit.hom_ext hc (fun i ↦ by
      have := hc.fac (ofLinearOrder s h) (.right i)
      dsimp at this
      rw [this]
      apply hm))

end Multicofork

end symmetry

end CategoryTheory.Limits
