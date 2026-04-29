/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Riccardo Brasca
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Tactic.CategoryTheory.MkConcreteCategory

/-!
# The category of seminormed groups

We define `SemiNormedGrp`, the category of seminormed groups and normed group homs between
them, as well as `SemiNormedGrp₁`, the subcategory of norm non-increasing morphisms.
-/

@[expose] public section


noncomputable section

universe u

open CategoryTheory

/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
structure SemiNormedGrp : Type (u + 1) where
  /-- Construct a bundled `SemiNormedGrp` from the underlying type and typeclass. -/
  of ::
  /-- The underlying seminormed abelian group. -/
  carrier : Type u
  [str : SeminormedAddCommGroup carrier]

attribute [instance] SemiNormedGrp.str

namespace SemiNormedGrp

instance : CoeSort SemiNormedGrp Type* where
  coe X := X.carrier

mk_concrete_category SemiNormedGrp (NormedAddGroupHom · ·)
  NormedAddGroupHom.id NormedAddGroupHom.comp
  with_of_hom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  hom_type (NormedAddGroupHom M N) from (of M) to (of N)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
@[ext]
lemma ext {M N : SemiNormedGrp} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  ConcreteCategory.ext_apply h

/- Provided for rewriting. -/
lemma id_apply (M : SemiNormedGrp) (r : M) :
    (𝟙 M : M ⟶ M) r = r := by simp

/- Provided for rewriting. -/
lemma comp_apply {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O) (r : M) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
lemma hom_ext {M N : SemiNormedGrp} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma ofHom_id {M : Type u} [SeminormedAddCommGroup M] :
    ofHom (NormedAddGroupHom.id M) = 𝟙 (of M) := rfl

@[simp]
lemma ofHom_comp {M N O : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    [SeminormedAddCommGroup O] (f : NormedAddGroupHom M N) (g : NormedAddGroupHom N O) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (r : M) : ofHom f r = f r := rfl

lemma inv_hom_apply {M N : SemiNormedGrp} (e : M ≅ N) (r : M) : e.inv (e.hom r) = r := by
  simp

lemma hom_inv_apply {M N : SemiNormedGrp} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp

theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp.of V : Type u) = V :=
  rfl

theorem coe_id (V : SemiNormedGrp) : (𝟙 V : V → V) = id :=
  rfl

theorem coe_comp {M N K : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M → K) = g ∘ f :=
  rfl

instance : Inhabited SemiNormedGrp :=
  ⟨of PUnit⟩

instance {M N : SemiNormedGrp} : Zero (M ⟶ N) where
  zero := ofHom 0

@[simp]
theorem hom_zero {V W : SemiNormedGrp} : (0 : V ⟶ W).hom = 0 :=
  rfl

theorem zero_apply {V W : SemiNormedGrp} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp where

theorem isZero_of_subsingleton (V : SemiNormedGrp) [Subsingleton V] : Limits.IsZero V := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim

instance hasZeroObject : Limits.HasZeroObject SemiNormedGrp.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

theorem iso_isometry_of_normNoninc {V W : SemiNormedGrp} (i : V ≅ W) (h1 : i.hom.hom.NormNoninc)
    (h2 : i.inv.hom.NormNoninc) : Isometry i.hom := by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymm (h1 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← comp_apply, Iso.hom_inv_id, id_apply]
    _ ≤ ‖i.hom v‖ := h2 _

instance Hom.add {M N : SemiNormedGrp} : Add (M ⟶ N) where
  add f g := ofHom (f.hom + g.hom)

@[simp]
theorem hom_add {V W : SemiNormedGrp} (f g : V ⟶ W) : (f + g).hom = f.hom + g.hom :=
  rfl

instance Hom.neg {M N : SemiNormedGrp} : Neg (M ⟶ N) where
  neg f := ofHom (- f.hom)

@[simp]
theorem hom_neg {V W : SemiNormedGrp} (f : V ⟶ W) : (-f).hom = -f.hom :=
  rfl

instance Hom.sub {M N : SemiNormedGrp} : Sub (M ⟶ N) where
  sub f g := ofHom (f.hom - g.hom)

@[simp]
theorem hom_sub {V W : SemiNormedGrp} (f g : V ⟶ W) : (f - g).hom = f.hom - g.hom :=
  rfl

instance Hom.nsmul {M N : SemiNormedGrp} : SMul ℕ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

@[simp]
theorem hom_nsum {V W : SemiNormedGrp} (n : ℕ) (f : V ⟶ W) : (n • f).hom = n • f.hom :=
  rfl

instance Hom.zsmul {M N : SemiNormedGrp} : SMul ℤ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

@[simp]
theorem hom_zsum {V W : SemiNormedGrp} (n : ℤ) (f : V ⟶ W) : (n • f).hom = n • f.hom :=
  rfl

instance Hom.addCommGroup {V W : SemiNormedGrp} : AddCommGroup (V ⟶ W) :=
  Function.Injective.addCommGroup _ ConcreteCategory.hom_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end SemiNormedGrp

/-- `SemiNormedGrp₁` is a type synonym for `SemiNormedGrp`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
structure SemiNormedGrp₁ : Type (u + 1) where
  /-- Construct a bundled `SemiNormedGrp₁` from the underlying type and typeclass. -/
  of ::
  /-- The underlying seminormed abelian group. -/
  carrier : Type u
  [str : SeminormedAddCommGroup carrier]

attribute [instance] SemiNormedGrp₁.str

namespace SemiNormedGrp₁

instance : CoeSort SemiNormedGrp₁ Type* where
  coe X := X.carrier

/-- The type of morphisms in `SemiNormedGrp₁` -/
@[ext]
structure Hom (M N : SemiNormedGrp₁.{u}) where
  /-- The underlying `NormedAddGroupHom`. -/
  hom' : NormedAddGroupHom M N
  normNoninc : hom'.NormNoninc

instance : LargeCategory.{u} SemiNormedGrp₁ where
  Hom := Hom
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp {_ _ _} f g := ⟨g.1.comp f.1, g.2.comp f.2⟩

instance instFunLike (X Y : SemiNormedGrp₁) :
    FunLike { f : NormedAddGroupHom X Y // f.NormNoninc } X Y where
  coe f := f.1.toFun
  coe_injective' _ _ h := Subtype.val_inj.mp (NormedAddGroupHom.coe_injective h)

instance : ConcreteCategory SemiNormedGrp₁
    fun X Y => { f : NormedAddGroupHom X Y // f.NormNoninc } where
  hom f := ⟨f.1, f.2⟩
  ofHom f := ⟨f.1, f.2⟩

instance (X Y : SemiNormedGrp₁) :
    AddMonoidHomClass { f : NormedAddGroupHom X Y // f.NormNoninc } X Y where
  map_add f := map_add f.1
  map_zero f := map_zero f.1

/-- Turn a morphism in `SemiNormedGrp₁` back into a norm-nonincreasing `NormedAddGroupHom`. -/
abbrev Hom.hom {M N : SemiNormedGrp₁.{u}} (f : Hom M N) :=
  ConcreteCategory.hom (C := SemiNormedGrp₁) f

/-- Promote a `NormedAddGroupHom` to a morphism in `SemiNormedGrp₁`. -/
abbrev mkHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (i : f.NormNoninc) :
    SemiNormedGrp₁.of M ⟶ SemiNormedGrp₁.of N :=
  ConcreteCategory.ofHom ⟨f, i⟩

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (M N : SemiNormedGrp₁.{u}) (f : Hom M N) : NormedAddGroupHom M N :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

instance (X Y : SemiNormedGrp₁) : CoeFun (X ⟶ Y) (fun _ => X → Y) where
  coe f := f.hom.1

theorem mkHom_apply {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (i : f.NormNoninc) (x) :
    mkHom f i x = f x :=
  rfl

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
@[ext]
lemma ext {M N : SemiNormedGrp₁} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  ConcreteCategory.ext_apply h

@[simp]
lemma hom_id {M : SemiNormedGrp₁} : (𝟙 M : M ⟶ M).hom = NormedAddGroupHom.id M := rfl

/- Provided for rewriting. -/
lemma id_apply (M : SemiNormedGrp₁) (r : M) :
    (𝟙 M : M ⟶ M) r = r := by simp

@[simp]
lemma hom_comp {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom.1 = g.hom.1.comp f.hom.1 := rfl

/- Provided for rewriting. -/
lemma comp_apply {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) (r : M) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
lemma hom_ext {M N : SemiNormedGrp₁} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext (congr_arg Subtype.val hf)

@[simp]
lemma hom_mkHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : f.NormNoninc) : (mkHom f hf).hom = f := rfl

@[simp]
lemma mkHom_hom {M N : SemiNormedGrp₁} (f : M ⟶ N) :
    mkHom (Hom.hom f) f.normNoninc = f := rfl

@[simp]
lemma mkHom_id {M : Type u} [SeminormedAddCommGroup M] :
    mkHom (NormedAddGroupHom.id M) NormedAddGroupHom.NormNoninc.id = 𝟙 (of M) := rfl

@[simp]
lemma mkHom_comp {M N O : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    [SeminormedAddCommGroup O] (f : NormedAddGroupHom M N) (g : NormedAddGroupHom N O)
    (hf : f.NormNoninc) (hg : g.NormNoninc) (hgf : (g.comp f).NormNoninc) :
    mkHom (g.comp f) hgf = mkHom f hf ≫ mkHom g hg :=
  rfl

@[simp]
lemma inv_hom_apply {M N : SemiNormedGrp₁} (e : M ≅ N) (r : M) : e.inv (e.hom r) = r := by
  rw [← comp_apply]
  simp

@[simp]
lemma hom_inv_apply {M N : SemiNormedGrp₁} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  rw [← comp_apply]
  simp

instance (M : SemiNormedGrp₁) : SeminormedAddCommGroup M :=
  M.str

/-- Promote an isomorphism in `SemiNormedGrp` to an isomorphism in `SemiNormedGrp₁`. -/
@[simps]
def mkIso {M N : SemiNormedGrp} (f : M ≅ N) (i : f.hom.hom.NormNoninc) (i' : f.inv.hom.NormNoninc) :
    SemiNormedGrp₁.of M ≅ SemiNormedGrp₁.of N where
  hom := mkHom f.hom.hom i
  inv := mkHom f.inv.hom i'

instance : HasForget₂ SemiNormedGrp₁ SemiNormedGrp where
  forget₂ :=
    { obj := fun X => SemiNormedGrp.of X
      map := fun f => SemiNormedGrp.ofHom f.1 }

theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp₁.of V : Type u) = V :=
  rfl

theorem coe_id (V : SemiNormedGrp₁) : ⇑(𝟙 V) = id :=
  rfl

theorem coe_comp {M N K : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M → K) = g ∘ f :=
  rfl

instance : Inhabited SemiNormedGrp₁ :=
  ⟨of PUnit⟩

instance (X Y : SemiNormedGrp₁) : Zero (X ⟶ Y) where
  zero := ⟨0, NormedAddGroupHom.NormNoninc.zero⟩

@[simp]
theorem zero_apply {V W : SemiNormedGrp₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp₁ where

theorem isZero_of_subsingleton (V : SemiNormedGrp₁) [Subsingleton V] : Limits.IsZero V := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim

instance hasZeroObject : Limits.HasZeroObject SemiNormedGrp₁.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

theorem iso_isometry {V W : SemiNormedGrp₁} (i : V ≅ W) : Isometry i.hom := by
  change Isometry (⟨⟨i.hom, map_zero _⟩, fun _ _ => map_add _ _ _⟩ : V →+ W)
  refine AddMonoidHomClass.isometry_of_norm _ ?_
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← comp_apply, Iso.hom_inv_id, id_apply]
    _ ≤ ‖i.hom v‖ := i.inv.2 _

end SemiNormedGrp₁
