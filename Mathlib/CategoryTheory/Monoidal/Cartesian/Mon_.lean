/-
Copyright (c) 2025 Markus Himmel, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Andrew Yang
-/
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# Yoneda embedding of `Mon C`

We show that monoid objects in Cartesian monoidal categories are exactly those whose yoneda presheaf
is a presheaf of monoids, by constructing the yoneda embedding `Mon C ⥤ Cᵒᵖ ⥤ MonCat.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.
-/

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

universe w v u
variable {C D : Type*} [Category.{v} C] [CartesianMonoidalCategory C]
  [Category.{w} D] [CartesianMonoidalCategory D]
  {M N O X Y : C} [MonObj M] [MonObj N] [MonObj O]

namespace MonObj

instance : IsMonHom (toUnit M) where

instance : IsMonHom η[M] where
  mul_hom := by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom]

theorem lift_lift_assoc {A : C} {B : C} [MonObj B] (f g h : A ⟶ B) :
    lift (lift f g ≫ μ) h ≫ μ = lift f (lift g h ≫ μ) ≫ μ := by
  have := lift (lift f g) h ≫= mul_assoc B
  rwa [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc] at this

@[reassoc (attr := simp)]
theorem lift_comp_one_left {A : C} {B : C} [MonObj B] (f : A ⟶ 𝟙_ C) (g : A ⟶ B) :
    lift (f ≫ η) g ≫ μ = g := by
  have := lift f g ≫= one_mul B
  rwa [lift_whiskerRight_assoc, lift_leftUnitor_hom] at this

@[reassoc (attr := simp)]
theorem lift_comp_one_right {A : C} {B : C} [MonObj B] (f : A ⟶ B) (g : A ⟶ 𝟙_ C) :
    lift f (g ≫ η) ≫ μ = f := by
  have := lift f g ≫= mul_one B
  rwa [lift_whiskerLeft_assoc, lift_rightUnitor_hom] at this

variable [BraidedCategory C]

attribute [local simp] tensorObj.one_def tensorObj.mul_def

instance : IsMonHom (fst M N) where
instance : IsMonHom (snd M N) where

instance {f : M ⟶ N} {g : M ⟶ O} [IsMonHom f] [IsMonHom g] : IsMonHom (lift f g) where

instance [IsCommMonObj M] : IsMonHom μ[M] where
  one_hom := by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom]

end MonObj

namespace Mon
variable [BraidedCategory C]

attribute [local simp] tensorObj.one_def tensorObj.mul_def

instance : CartesianMonoidalCategory (Mon C) where
  isTerminalTensorUnit := .ofUniqueHom (fun M ↦ ⟨toUnit _⟩) fun M f ↦ by ext; exact toUnit_unique ..
  fst M N := .mk (fst M.X N.X)
  snd M N := .mk (snd M.X N.X)
  tensorProductIsBinaryProduct M N :=
    BinaryFan.IsLimit.mk _ (fun {T} f g ↦ ⟨lift f.hom g.hom⟩)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def M N := by ext; simp [fst_def]; congr
  snd_def M N := by ext; simp [snd_def]; congr

variable {M N₁ N₂ : Mon C}

@[simp] lemma lift_hom (f : M ⟶ N₁) (g : M ⟶ N₂) : (lift f g).hom = lift f.hom g.hom := rfl
@[simp] lemma fst_hom (M N : Mon C) : (fst M N).hom = fst M.X N.X := rfl
@[simp] lemma snd_hom (M N : Mon C) : (snd M N).hom = snd M.X N.X := rfl

end Mon

variable (X) in
/-- If `X` represents a presheaf of monoids, then `X` is a monoid object. -/
@[simps]
def MonObj.ofRepresentableBy (F : Cᵒᵖ ⥤ MonCat.{w}) (α : (F ⋙ forget _).RepresentableBy X) :
    MonObj X where
  one := α.homEquiv.symm 1
  mul := α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X))
  one_mul := by
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp only [whiskerRight_fst, whiskerRight_snd]
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp [leftUnitor_hom]
  mul_one := by
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp only [whiskerLeft_fst, whiskerLeft_snd]
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp [rightUnitor_hom]
  mul_assoc := by
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp only [whiskerRight_fst, whiskerRight_snd, whiskerLeft_fst,
      associator_hom_fst, whiskerLeft_snd]
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_mul, _root_.mul_assoc]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp

@[deprecated (since := "2025-09-09")] alias Mon_Class.ofRepresentableBy := MonObj.ofRepresentableBy

@[deprecated (since := "2025-03-07")]
alias MonObjOfRepresentableBy := MonObj.ofRepresentableBy

@[deprecated (since := "2025-09-09")] alias Mon_ClassOfRepresentableBy := MonObjOfRepresentableBy

/-- If `M` is a monoid object, then `Hom(X, M)` has a monoid structure. -/
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

scoped[MonObj] attribute [instance] Hom.monoid

lemma Hom.one_def : (1 : X ⟶ M) = toUnit X ≫ η := rfl
lemma Hom.mul_def (f₁ f₂ : X ⟶ M) : f₁ * f₂ = lift f₁ f₂ ≫ μ := rfl

namespace CategoryTheory.Functor
variable (F : C ⥤ D) [F.Monoidal]

open scoped Obj

protected lemma map_mul (f g : X ⟶ M) : F.map (f * g) = F.map f * F.map g := by
  simp only [Hom.mul_def, map_comp, obj.μ_def, ← Category.assoc]
  congr 1
  rw [← IsIso.comp_inv_eq]
  ext <;> simp

@[simp] protected lemma map_one : F.map (1 : X ⟶ M) = 1 := by simp [Hom.one_def]

/-- `Functor.map` of a monoidal functor as a `MonoidHom`. -/
@[simps]
def homMonoidHom : (X ⟶ M) →* (F.obj X ⟶ F.obj M) where
  toFun := F.map
  map_one' := F.map_one
  map_mul' := F.map_mul

/-- `Functor.map` of a fully faithful monoidal functor as a `MulEquiv`. -/
@[simps!]
def FullyFaithful.homMulEquiv (hF : F.FullyFaithful) : (X ⟶ M) ≃* (F.obj X ⟶ F.obj M) where
  __ := hF.homEquiv
  __ := F.homMonoidHom

end CategoryTheory.Functor

section BraidedCategory
variable [BraidedCategory C]

/-- If `M` is a commutative monoid object, then `Hom(X, M)` has a commutative monoid structure. -/
abbrev Hom.commMonoid [IsCommMonObj M] : CommMonoid (X ⟶ M) where
  mul_comm f g := by simpa [-IsCommMonObj.mul_comm] using lift g f ≫= IsCommMonObj.mul_comm M

scoped[MonObj] attribute [instance] Hom.commMonoid

end BraidedCategory

variable (M) in
/-- If `M` is a monoid object, then `Hom(-, M)` is a presheaf of monoids. -/
@[simps]
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
@[simps!]
def yonedaMonObjIsoOfRepresentableBy
    (F : Cᵒᵖ ⥤ MonCat.{v}) (α : (F ⋙ forget _).RepresentableBy X) :
    letI := MonObj.ofRepresentableBy X F α
    yonedaMonObj X ≅ F :=
  letI := MonObj.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y ↦ MulEquiv.toMonCatIso
    { toEquiv := α.homEquiv
      map_mul' f₁ f₂ := by
        change α.homEquiv (lift f₁ f₂ ≫ α.homEquiv.symm (α.homEquiv (fst X X) *
          α.homEquiv (snd X X))) = α.homEquiv f₁ * α.homEquiv f₂
        simp only [α.homEquiv_comp, Equiv.apply_symm_apply,
          Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_mul]
        simp only [← Functor.comp_map, ← ConcreteCategory.forget_map_eq_coe, ← α.homEquiv_comp]
        simp }) (fun φ ↦ MonCat.hom_ext (MonoidHom.ext (α.homEquiv_comp φ.unop)))

/-- The yoneda embedding of `Mon_C` into presheaves of monoids. -/
@[simps]
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

@[reassoc]
lemma yonedaMon_naturality (α : yonedaMonObj M ⟶ yonedaMonObj N) (f : X ⟶ Y) (g : Y ⟶ M) :
      α.app _ (f ≫ g) = f ≫ α.app _ g := congr($(α.naturality f.op) g)

variable (M) in
/-- If `M` is a monoid object, then `Hom(-, M)` as a presheaf of monoids is represented by `M`. -/
def yonedaMonObjRepresentableBy : (yonedaMonObj M ⋙ forget _).RepresentableBy M :=
  Functor.representableByEquiv.symm (.refl _)

variable (M) in
lemma MonObj.ofRepresentableBy_yonedaMonObjRepresentableBy :
    ofRepresentableBy M _ (yonedaMonObjRepresentableBy M) = ‹_› := by
  ext; change lift (fst M M) (snd M M) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

@[deprecated (since := "2025-09-09")]
alias Mon_Class.ofRepresentableBy_yonedaMonObjRepresentableBy :=
  MonObj.ofRepresentableBy_yonedaMonObjRepresentableBy

@[deprecated (since := "2025-03-07")]
alias MonObjOfRepresentableBy_yonedaMonObjRepresentableBy :=
  MonObj.ofRepresentableBy_yonedaMonObjRepresentableBy

@[deprecated (since := "2025-09-09")]
alias Mon_ClassOfRepresentableBy_yonedaMonObjRepresentableBy :=
  MonObjOfRepresentableBy_yonedaMonObjRepresentableBy

/-- The yoneda embedding for `Mon_C` is fully faithful. -/
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

instance : yonedaMon (C := C).Full := yonedaMonFullyFaithful.full
instance : yonedaMon (C := C).Faithful := yonedaMonFullyFaithful.faithful

lemma essImage_yonedaMon :
    yonedaMon (C := C).essImage = (· ⋙ forget _) ⁻¹' setOf Functor.IsRepresentable := by
  ext F
  constructor
  · rintro ⟨M, ⟨α⟩⟩
    exact ⟨M.X, ⟨Functor.representableByEquiv.symm (Functor.isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    letI := MonObj.ofRepresentableBy X F e
    exact ⟨Mon.mk X, ⟨yonedaMonObjIsoOfRepresentableBy X F e⟩⟩

@[reassoc (attr := simp)]
lemma MonObj.one_comp (f : M ⟶ N) [IsMonHom f] : (1 : X ⟶ M) ≫ f = 1 := by simp [Hom.one_def]

@[deprecated (since := "2025-09-09")] alias Mon_Class.one_comp := MonObj.one_comp

@[reassoc]
lemma MonObj.mul_comp (f₁ f₂ : X ⟶ M) (g : M ⟶ N) [IsMonHom g] :
    (f₁ * f₂) ≫ g = f₁ ≫ g * f₂ ≫ g := by simp [Hom.mul_def]

@[deprecated (since := "2025-09-09")] alias Mon_Class.mul_comp := MonObj.mul_comp

@[reassoc]
lemma MonObj.pow_comp (f : X ⟶ M) (n : ℕ) (g : M ⟶ N) [IsMonHom g] :
    (f ^ n) ≫ g = (f ≫ g) ^ n := by
  induction n <;> simp [pow_succ, MonObj.mul_comp, *]

@[deprecated (since := "2025-09-09")] alias Mon_Class.pow_comp := MonObj.pow_comp

@[reassoc (attr := simp)]
lemma MonObj.comp_one (f : X ⟶ Y) : f ≫ (1 : Y ⟶ M) = 1 :=
  ((yonedaMon.obj <| .mk M).map f.op).hom.map_one

@[deprecated (since := "2025-09-09")] alias Mon_Class.comp_one := MonObj.comp_one

@[reassoc]
lemma MonObj.comp_mul (f : X ⟶ Y) (g₁ g₂ : Y ⟶ M) : f ≫ (g₁ * g₂) = f ≫ g₁ * f ≫ g₂ :=
  ((yonedaMon.obj <| .mk M).map f.op).hom.map_mul _ _

@[deprecated (since := "2025-09-09")] alias Mon_Class.comp_mul := MonObj.comp_mul

@[reassoc]
lemma MonObj.comp_pow (f : X ⟶ M) (n : ℕ) (h : Y ⟶ X) : h ≫ f ^ n = (h ≫ f) ^ n := by
  induction n <;> simp [pow_succ, MonObj.comp_mul, *]

@[deprecated (since := "2025-09-09")] alias Mon_Class.comp_pow := MonObj.comp_pow

variable (M) in
lemma MonObj.one_eq_one : η = (1 : _ ⟶ M) :=
  show _ = _ ≫ _ by rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

@[deprecated (since := "2025-09-09")] alias Mon_Class.one_eq_one := MonObj.one_eq_one

variable (M) in
lemma MonObj.mul_eq_mul : μ = fst M M * snd _ _ :=
  show _ = _ ≫ _ by rw [lift_fst_snd, Category.id_comp]

@[deprecated (since := "2025-09-09")] alias Mon_Class.mul_eq_mul := MonObj.mul_eq_mul
