/-
Copyright (c) 2025 Markus Himmel, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon_
public import Mathlib.CategoryTheory.ConcreteCategory.Representable

/-!
# Yoneda embedding of `Mon C`

We show that monoid objects in Cartesian monoidal categories are exactly those whose yoneda presheaf
is a presheaf of monoids, by constructing the yoneda embedding `Mon C ⥤ Cᵒᵖ ⥤ MonCat.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory

section SemiCartesianMonoidalCategory

variable {D : Type*} [Category* D] [SemiCartesianMonoidalCategory D]

set_option backward.defeqAttrib.useBackward true in
@[to_additive (attr := simps)]
instance Mon.uniqueHomToTrivial (A : Mon D) : Unique (A ⟶ Mon.trivial D) where
  default.hom := toUnit A.X
  default.isMonHom_hom.mul_hom := toUnit_unique _ _
  uniq f := Mon.Hom.ext (toUnit_unique _ _)

@[deprecated (since := "2026-03-20")] alias uniqueHomToTrivial := Mon.uniqueHomToTrivial

@[to_additive instHasZeroObjectAddMon]
instance : HasZeroObject (Mon D) where
  zero := ⟨Mon.trivial D,
    fun A ↦ nonempty_unique (Mon.trivial D ⟶ A),
    fun A ↦ nonempty_unique (A ⟶ Mon.trivial D)⟩

@[to_additive instHasZeroMorphismsAddMon]
noncomputable instance : HasZeroMorphisms (Mon D) := HasZeroObject.zeroMorphismsOfZeroObject

end SemiCartesianMonoidalCategory

universe w v u
variable {C D : Type*} [Category.{v} C] [CartesianMonoidalCategory C]
  [Category.{w} D] [CartesianMonoidalCategory D]
  {M N O X Y : C} [MonObj M] [MonObj N] [MonObj O]

namespace MonObj

@[to_additive]
instance : IsMonHom (toUnit M) where

@[to_additive]
instance : IsMonHom η[M] where
  mul_hom := by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom]

@[to_additive]
theorem lift_lift_assoc {A : C} {B : C} [MonObj B] (f g h : A ⟶ B) :
    lift (lift f g ≫ μ) h ≫ μ = lift f (lift g h ≫ μ) ≫ μ := by
  have := lift (lift f g) h ≫= mul_assoc B
  rwa [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc] at this

@[to_additive (attr := reassoc (attr := simp))]
theorem lift_comp_one_left {A : C} {B : C} [MonObj B] (f : A ⟶ 𝟙_ C) (g : A ⟶ B) :
    lift (f ≫ η) g ≫ μ = g := by
  have := lift f g ≫= one_mul B
  rwa [lift_whiskerRight_assoc, lift_leftUnitor_hom] at this

@[to_additive (attr := reassoc (attr := simp))]
theorem lift_comp_one_right {A : C} {B : C} [MonObj B] (f : A ⟶ B) (g : A ⟶ 𝟙_ C) :
    lift f (g ≫ η) ≫ μ = f := by
  have := lift f g ≫= mul_one B
  rwa [lift_whiskerLeft_assoc, lift_rightUnitor_hom] at this

variable [BraidedCategory C]

attribute [local simp] tensorObj.one_def tensorObj.mul_def

@[to_additive]
instance : IsMonHom (fst M N) where

@[to_additive]
instance : IsMonHom (snd M N) where

@[to_additive]
instance {f : M ⟶ N} {g : M ⟶ O} [IsMonHom f] [IsMonHom g] : IsMonHom (lift f g) where

@[to_additive]
instance [IsCommMonObj M] : IsMonHom μ[M] where
  one_hom := by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom]

end MonObj

namespace Mon
variable [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] tensorObj.one_def tensorObj.mul_def in
@[to_additive]
instance : CartesianMonoidalCategory (Mon C) where
  isTerminalTensorUnit := .ofUniqueHom (fun M ↦ ⟨toUnit _⟩) fun M f ↦ by ext; exact toUnit_unique ..
  fst M N := .mk (fst M.X N.X)
  snd M N := .mk (snd M.X N.X)
  tensorProductIsBinaryProduct M N :=
    BinaryFan.IsLimit.mk _ (fun {T} f g ↦ ⟨lift f.hom g.hom⟩)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def M N := by ext; simp [fst_def]; congr
  snd_def M N := by ext; simp [snd_def]; congr

variable {M N N₁ N₂ : Mon C}

@[to_additive (attr := simp)]
lemma lift_hom (f : M ⟶ N₁) (g : M ⟶ N₂) : (lift f g).hom = lift f.hom g.hom := rfl

@[to_additive (attr := simp)]
lemma fst_hom (M N : Mon C) : (fst M N).hom = fst M.X N.X := rfl

@[to_additive (attr := simp)]
lemma snd_hom (M N : Mon C) : (snd M N).hom = snd M.X N.X := rfl

/-! ### Comm monoid objects are internal monoid objects -/

/-- A commutative monoid object is a monoid object in the category of monoid objects. -/
@[to_additive
/-- A commutative additive monoid object is an additive monoid object in the category
of additive monoid objects. -/]
instance [IsCommMonObj M.X] : MonObj M where
  one := .mk η[M.X]
  mul := .mk μ[M.X]

@[to_additive (attr := simp)]
lemma hom_one (M : Mon C) [IsCommMonObj M.X] : η[M].hom = η[M.X] := rfl

@[to_additive (attr := simp)]
lemma hom_mul (M : Mon C) [IsCommMonObj M.X] : μ[M].hom = μ[M.X] := rfl

/-- A commutative monoid object is a commutative monoid object in the category of monoid objects. -/
@[to_additive
/-- A commutative additive monoid object is a commutative additive monoid object in the
category of additive monoid objects. -/]
instance [IsCommMonObj M.X] : IsCommMonObj M where

end Mon

variable (X) in
/-- If `X` represents a presheaf of monoids, then `X` is a monoid object. -/
@[to_additive (attr := simps, implicit_reducible)
/-- If `X` represents a presheaf of additive monoids, then `X` is an additive monoid object. -/]
def MonObj.ofRepresentableBy (F : Cᵒᵖ ⥤ MonCat.{w}) (α : (F ⋙ forget _).RepresentableBy X) :
    MonObj X where
  one := α.homEquiv'.symm 1
  mul := α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X))
  one_mul := by
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
    simp only [← α.homEquiv'_comp]
    simp only [whiskerRight_fst, whiskerRight_snd, α.homEquiv'_comp, Equiv.apply_symm_apply]
    simp [leftUnitor_hom, -op_tensorObj, -op_whiskerRight, -op_tensorUnit]
  mul_one := by
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
    simp only [← α.homEquiv'_comp]
    simp only [whiskerLeft_fst, whiskerLeft_snd, α.homEquiv'_comp, Equiv.apply_symm_apply]
    simp [rightUnitor_hom, -op_tensorObj, -op_whiskerRight, -op_tensorUnit]
  mul_assoc := by
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
    simp only [← α.homEquiv'_comp]
    simp only [whiskerRight_fst, whiskerRight_snd, whiskerLeft_fst, associator_hom_fst,
      whiskerLeft_snd, α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul, _root_.mul_assoc]
    simp only [← α.homEquiv'_comp]
    simp

/-- If `M` is a monoid object, then `Hom(X, M)` has a monoid structure. -/
@[to_additive
/-- If `M` is an additive monoid object, then `Hom(X, M)` has an additive monoid structure. -/]
abbrev Hom.monoid : Monoid (X ⟶ M) where
  mul f₁ f₂ := lift f₁ f₂ ≫ μ
  mul_assoc f₁ f₂ f₃ := by
    change lift (lift f₁ f₂ ≫ μ) f₃ ≫ μ = lift f₁ (lift f₂ f₃ ≫ μ) ≫ μ
    trans lift (lift f₁ f₂) f₃ ≫ μ ▷ M ≫ μ
    · rw [← tensorHom_id, lift_map_assoc, Category.comp_id]
    trans lift f₁ (lift f₂ f₃) ≫ M ◁ μ ≫ μ
    · rw [MonObj.mul_assoc]
      simp_rw [← Category.assoc]
      congr 2
      ext <;> simp
    · rw [← id_tensorHom, lift_map_assoc, Category.comp_id]
  one := toUnit X ≫ η
  one_mul f := by
    change lift (toUnit _ ≫ η) f ≫ μ = f
    rw [← Category.comp_id f, ← lift_map_assoc, tensorHom_id, MonObj.one_mul,
      Category.comp_id, leftUnitor_hom]
    exact lift_snd _ _
  mul_one f := by
    change lift f (toUnit _ ≫ η) ≫ μ = f
    rw [← Category.comp_id f, ← lift_map_assoc, id_tensorHom, MonObj.mul_one,
      Category.comp_id, rightUnitor_hom]
    exact lift_fst _ _

scoped[CategoryTheory.MonObj] attribute [instance] Hom.monoid

@[to_additive]
lemma Hom.one_def : (1 : X ⟶ M) = toUnit X ≫ η := rfl
@[to_additive]
lemma Hom.mul_def (f₁ f₂ : X ⟶ M) : f₁ * f₂ = lift f₁ f₂ ≫ μ := rfl

namespace Functor
variable (F : C ⥤ D) [F.Monoidal]

open scoped Obj

@[to_additive map_add']
protected lemma map_mul (f g : X ⟶ M) : F.map (f * g) = F.map f * F.map g := by
  simp [Hom.mul_def]

@[to_additive (attr := simp) map_zero']
protected lemma map_one : F.map (1 : X ⟶ M) = 1 := by simp [Hom.one_def]

/-- `Functor.map` of a monoidal functor as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `Functor.map` of a monoidal functor as a `AddMonoidHom`. -/]
def homMonoidHom : (X ⟶ M) →* (F.obj X ⟶ F.obj M) where
  toFun := F.map
  map_one' := F.map_one
  map_mul' := F.map_mul

/-- `Functor.map` of a fully faithful monoidal functor as a `MulEquiv`. -/
@[to_additive (attr := simps!)
/-- `Functor.map` of a fully faithful monoidal functor as a `AddEquiv`. -/]
def FullyFaithful.homMulEquiv (hF : F.FullyFaithful) : (X ⟶ M) ≃* (F.obj X ⟶ F.obj M) where
  __ := hF.homEquiv
  __ := F.homMonoidHom

end Functor

section BraidedCategory
variable [BraidedCategory C]

/-- If `M` is a commutative monoid object, then `Hom(X, M)` has a commutative monoid structure. -/
@[to_additive
/-- If `M` is a commutative additive monoid object, then `Hom(X, M)` has a commutative additive
monoid structure. -/]
abbrev Hom.commMonoid [IsCommMonObj M] : CommMonoid (X ⟶ M) where
  mul_comm f g := by simpa [-IsCommMonObj.mul_comm] using lift g f ≫= IsCommMonObj.mul_comm M

namespace Mon.Hom
variable {M N : Mon C} [IsCommMonObj N.X]

@[to_additive (attr := simp)]
lemma hom_one : (1 : M ⟶ N).hom = 1 := rfl
@[to_additive (attr := simp)]
lemma hom_mul (f g : M ⟶ N) : (f * g).hom = f.hom * g.hom := rfl
@[to_additive (attr := simp)]
lemma hom_pow (f : M ⟶ N) (n : ℕ) : (f ^ n).hom = f.hom ^ n := by
  induction n <;> simp [pow_succ, *]

end Mon.Hom

scoped[CategoryTheory.MonObj] attribute [instance] Hom.commMonoid Hom.addCommMonoid

end BraidedCategory

variable (M) in
/-- If `M` is a monoid object, then `Hom(-, M)` is a presheaf of monoids. -/
@[to_additive (attr := simps)
/-- If `M` is an additive monoid object, then `Hom(-, M)` is a presheaf of additive monoids. -/]
def yonedaMonObj : Cᵒᵖ ⥤ MonCat.{v} where
  obj X := MonCat.of (unop X ⟶ M)
  map {X Y₂} φ := MonCat.ofHom
    { toFun := (φ.unop ≫ ·)
      map_one' := by
        change φ.unop ≫ toUnit _ ≫ η = toUnit _ ≫ η
        rw [← Category.assoc, toUnit_unique (φ.unop ≫ toUnit _)]
      map_mul' f₁ f₂ := by
        change φ.unop ≫ lift f₁ f₂ ≫ μ = lift (φ.unop ≫ f₁) (φ.unop ≫ f₂) ≫ μ
        rw [← Category.assoc]
        cat_disch }
  map_id _ := MonCat.hom_ext (MonoidHom.ext Category.id_comp)
  map_comp _ _ := MonCat.hom_ext (MonoidHom.ext (Category.assoc _ _))

variable (X) in
/-- If `X` represents a presheaf of monoids `F`, then `Hom(-, X)` is isomorphic to `F` as
a presheaf of monoids. -/
@[to_additive (attr := simps!)
/-- If `X` represents a presheaf of additive monoids `F`, then `Hom(-, X)` is isomorphic
to `F` as a presheaf of additive monoids. -/]
def yonedaMonObjIsoOfRepresentableBy
    (F : Cᵒᵖ ⥤ MonCat.{v}) (α : (F ⋙ forget _).RepresentableBy X) :
    letI := MonObj.ofRepresentableBy X F α
    yonedaMonObj X ≅ F :=
  letI := MonObj.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y ↦ MulEquiv.toMonCatIso
    { toEquiv := α.homEquiv'
      map_mul' f₁ f₂ := by
        change α.homEquiv' (lift f₁ f₂ ≫ α.homEquiv'.symm (α.homEquiv' (fst X X) *
          α.homEquiv' (snd X X))) = α.homEquiv' f₁ * α.homEquiv' f₂
        simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
        simp only [← α.homEquiv'_comp]
        simp }) (fun φ ↦ MonCat.hom_ext (MonoidHom.ext (α.homEquiv'_comp φ.unop)))

/-- The yoneda embedding of `Mon C` into presheaves of monoids. -/
@[to_additive (attr := simps)
/-- The yoneda embedding of `AddMon C` into presheaves of additive monoids. -/]
def yonedaMon : Mon C ⥤ Cᵒᵖ ⥤ MonCat.{v} where
  obj M := yonedaMonObj M.X
  map {M N} ψ :=
  { app Y := MonCat.ofHom
      { toFun := (· ≫ ψ.hom)
        map_one' := by simp [Hom.one_def, Hom.one_def]
        map_mul' φ₁ φ₂ := by simp [Hom.mul_def] }
    naturality {M N} φ := MonCat.hom_ext <| MonoidHom.ext fun f ↦ Category.assoc φ.unop f ψ.hom }
  map_id M := NatTrans.ext <| funext fun _ ↦ MonCat.hom_ext <| MonoidHom.ext Category.comp_id
  map_comp _ _ :=
    NatTrans.ext <| funext fun _ ↦ MonCat.hom_ext <| MonoidHom.ext (.symm <| Category.assoc · _ _)

@[to_additive (attr := reassoc)]
lemma yonedaMon_naturality (α : yonedaMonObj M ⟶ yonedaMonObj N) (f : X ⟶ Y) (g : Y ⟶ M) :
      α.app _ (f ≫ g) = f ≫ α.app _ g := congr($(α.naturality f.op) g)

variable (M) in
/-- If `M` is a monoid object, then `Hom(-, M)` as a presheaf of monoids is represented by `M`. -/
@[to_additive
/-- If `M` is an additive monoid object, then `Hom(-, M)` as a presheaf of additive monoids
is represented by `M`. -/]
def yonedaMonObjRepresentableBy : (yonedaMonObj M ⋙ forget _).RepresentableBy M :=
  Functor.representableByEquiv.symm (.refl _)

variable (M) in
@[to_additive]
lemma MonObj.ofRepresentableBy_yonedaMonObjRepresentableBy :
    ofRepresentableBy M _ (yonedaMonObjRepresentableBy M) = ‹_› := by
  ext; change lift (fst M M) (snd M M) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embedding for `Mon C` is fully faithful. -/
@[to_additive /-- The yoneda embedding for `AddMon C` is fully faithful. -/]
def yonedaMonFullyFaithful : yonedaMon (C := C).FullyFaithful where
  preimage {M N} α :=
    { hom := α.app (op M.X) (𝟙 M.X)
      isMonHom_hom.one_hom := by
          dsimp only [yonedaMon_obj] at α ⊢
          rw [← yonedaMon_naturality, Category.comp_id,
            ← Category.id_comp η[M.X], toUnit_unique (𝟙 _) (toUnit _),
            ← Category.id_comp η[N.X], toUnit_unique (𝟙 _) (toUnit _)]
          exact (α.app _).hom.map_one
      isMonHom_hom.mul_hom := by
        dsimp only [yonedaMon_obj] at α ⊢
        rw [← yonedaMon_naturality, Category.comp_id, ← Category.id_comp μ[M.X], ← lift_fst_snd]
        refine ((α.app _).hom.map_mul _ _).trans ?_
        change lift _ _ ≫ μ[N.X] = _
        congr 1
        ext <;> simp only [lift_fst, tensorHom_fst, lift_snd, tensorHom_snd,
          ← yonedaMon_naturality, Category.comp_id] }
  map_preimage {M N} α := by
    ext Y f
    dsimp only [yonedaMon_obj, yonedaMon_map_app, MonCat.hom_ofHom]
    simp_rw [← yonedaMon_naturality]
    simp
  preimage_map φ := Mon.Hom.ext (Category.id_comp φ.hom)

@[to_additive]
instance : yonedaMon (C := C).Full := yonedaMonFullyFaithful.full
@[to_additive]
instance : yonedaMon (C := C).Faithful := yonedaMonFullyFaithful.faithful

@[to_additive]
lemma essImage_yonedaMon :
    yonedaMon (C := C).essImage = fun F ↦ (F ⋙ forget _).IsRepresentable := by
  ext F
  constructor
  · rintro ⟨M, ⟨α⟩⟩
    exact ⟨M.X, ⟨Functor.representableByEquiv.symm (Functor.isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    letI := MonObj.ofRepresentableBy X F e
    exact ⟨Mon.mk X, ⟨yonedaMonObjIsoOfRepresentableBy X F e⟩⟩

@[to_additive (attr := reassoc (attr := simp))]
lemma MonObj.one_comp (f : M ⟶ N) [IsMonHom f] : (1 : X ⟶ M) ≫ f = 1 := by simp [Hom.one_def]

@[to_additive (attr := reassoc)]
lemma MonObj.mul_comp (f₁ f₂ : X ⟶ M) (g : M ⟶ N) [IsMonHom g] :
    (f₁ * f₂) ≫ g = f₁ ≫ g * f₂ ≫ g := by simp [Hom.mul_def]

@[to_additive (attr := reassoc)]
lemma MonObj.pow_comp (f : X ⟶ M) (n : ℕ) (g : M ⟶ N) [IsMonHom g] :
    (f ^ n) ≫ g = (f ≫ g) ^ n := by
  induction n <;> simp [pow_succ, MonObj.mul_comp, *]

@[to_additive (attr := reassoc (attr := simp))]
lemma MonObj.comp_one (f : X ⟶ Y) : f ≫ (1 : Y ⟶ M) = 1 :=
  ((yonedaMon.obj <| .mk M).map f.op).hom.map_one

@[to_additive (attr := reassoc)]
lemma MonObj.comp_mul (f : X ⟶ Y) (g₁ g₂ : Y ⟶ M) : f ≫ (g₁ * g₂) = f ≫ g₁ * f ≫ g₂ :=
  ((yonedaMon.obj <| .mk M).map f.op).hom.map_mul _ _

@[to_additive (attr := reassoc)]
lemma MonObj.comp_pow (f : X ⟶ M) (n : ℕ) (h : Y ⟶ X) : h ≫ f ^ n = (h ≫ f) ^ n := by
  induction n <;> simp [pow_succ, MonObj.comp_mul, *]

variable (M) in
@[to_additive]
lemma MonObj.one_eq_one : η = (1 : _ ⟶ M) :=
  show _ = _ ≫ _ by rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

variable (M) in
@[to_additive]
lemma MonObj.mul_eq_mul : μ = fst M M * snd _ _ :=
  show _ = _ ≫ _ by rw [lift_fst_snd, Category.id_comp]

namespace Hom

/-- If `M` and `N` are isomorphic as monoid objects, then `X ⟶ M` and `X ⟶ N` are isomorphic
monoids. -/
@[to_additive (attr := simps!)
/-- If `M` and `N` are isomorphic as additive monoid objects, then `X ⟶ M` and `X ⟶ N`
are isomorphic additive monoids. -/]
def mulEquivCongrRight (e : M ≅ N) [IsMonHom e.hom] (X : C) : (X ⟶ M) ≃* (X ⟶ N) :=
  ((yonedaMon.mapIso <| Mon.mkIso' e).app <| .op X).monCatIsoToMulEquiv

end Hom

open scoped IsMulCommutative in
/-- A monoid object `M` is commutative if and only if `X ⟶ M` is commutative for all `X`. -/
@[to_additive]
lemma isCommMonObj_iff_isMulCommutative (M : C) [MonObj M] [BraidedCategory C] :
    IsCommMonObj M ↔ ∀ (X : C), IsMulCommutative (X ⟶ M) := by
  exact ⟨fun h X ↦ ⟨⟨by simp [mul_comm]⟩⟩, fun h ↦ ⟨by simp [mul_eq_mul, comp_mul, mul_comm]⟩⟩

end CategoryTheory
