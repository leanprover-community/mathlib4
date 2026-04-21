/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# The associated sheaf of a presheaf of modules

In this file, given a presheaf of modules `M₀` over a presheaf of rings `R₀`,
we construct the associated sheaf of `M₀`. More precisely, if `R` is a sheaf of
rings and `α : R₀ ⟶ R.val` is locally bijective, and `A` is the sheafification
of the underlying presheaf of abelian groups of `M₀`, i.e. we have a locally bijective
map `φ : M₀.presheaf ⟶ A.val`, then we endow `A` with the structure of a
sheaf of modules over `R`: this is `PresheafOfModules.sheafify α φ`.

In many applications, the morphism `α` shall be the identity, but this more
general construction allows the sheafification of both the presheaf of rings
and the presheaf of modules.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe w v v₁ u₁ u

open CategoryTheory Functor

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

namespace CategoryTheory

namespace Presieve.FamilyOfElements

section smul

variable {R : Cᵒᵖ ⥤ RingCat.{u}} {M : PresheafOfModules.{v} R} {X : C} {P : Presieve X}
  (r : FamilyOfElements (R ⋙ forget _) P) (m : FamilyOfElements (M.presheaf ⋙ forget _) P)

/-- The scalar multiplication of family of elements of a presheaf of modules `M` over `R`
by a family of elements of `R`. -/
def smul : FamilyOfElements (M.presheaf ⋙ forget _) P := fun Y f hf =>
  HSMul.hSMul (α := R.obj (Opposite.op Y)) (β := M.obj (Opposite.op Y)) (r f hf) (m f hf)

end smul

section

variable {R₀ R : Cᵒᵖ ⥤ RingCat.{u}} (α : R₀ ⟶ R) [Presheaf.IsLocallyInjective J α]
  {M₀ : PresheafOfModules.{v} R₀} {A : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (φ : M₀.presheaf ⟶ A)
  [Presheaf.IsLocallyInjective J φ] (hA : Presheaf.IsSeparated J A)
  {X : C} (r : R.obj (Opposite.op X)) (m : A.obj (Opposite.op X)) {P : Presieve X}
  (r₀ : FamilyOfElements (R₀ ⋙ forget _) P) (m₀ : FamilyOfElements (M₀.presheaf ⋙ forget _) P)
include hA

lemma _root_.PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective
    {Y : C} (r₀ r₀' : R₀.obj (Opposite.op Y))
    (m₀ m₀' : M₀.obj (Opposite.op Y))
    (hr₀ : α.app _ r₀ = α.app _ r₀')
    (hm₀ : φ.app _ m₀ = φ.app _ m₀') :
    φ.app _ (r₀ • m₀) = φ.app _ (r₀' • m₀') := by
  apply hA _ (Presheaf.equalizerSieve r₀ r₀' ⊓
      Presheaf.equalizerSieve (F := M₀.presheaf) m₀ m₀')
  · apply J.intersection_covering
    · exact Presheaf.equalizerSieve_mem J α _ _ hr₀
    · exact Presheaf.equalizerSieve_mem J φ _ _ hm₀
  · intro Z g hg
    rw [← NatTrans.naturality_apply (D := Ab), ← NatTrans.naturality_apply (D := Ab)]
    erw [M₀.map_smul, M₀.map_smul, hg.1, hg.2]
    rfl

set_option backward.isDefEq.respectTransparency false in
lemma isCompatible_map_smul_aux {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y)
    (r₀ : R₀.obj (Opposite.op Y)) (r₀' : R₀.obj (Opposite.op Z))
    (m₀ : M₀.obj (Opposite.op Y)) (m₀' : M₀.obj (Opposite.op Z))
    (hr₀ : α.app _ r₀ = R.map f.op r) (hr₀' : α.app _ r₀' = R.map (f.op ≫ g.op) r)
    (hm₀ : φ.app _ m₀ = A.map f.op m) (hm₀' : φ.app _ m₀' = A.map (f.op ≫ g.op) m) :
    φ.app _ (M₀.map g.op (r₀ • m₀)) = φ.app _ (r₀' • m₀') := by
  rw [← PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective α φ hA (R₀.map g.op r₀) r₀'
    (M₀.map g.op m₀) m₀', M₀.map_smul]
  · rw [hr₀', R.map_comp, RingCat.comp_apply, ← hr₀, ← RingCat.comp_apply, NatTrans.naturality,
      RingCat.comp_apply]
  · rw [hm₀', A.map_comp, AddCommGrpCat.coe_comp, Function.comp_apply, ← hm₀]
    erw [NatTrans.naturality_apply φ]

variable (hr₀ : (r₀.map (whiskerRight α (forget _))).IsAmalgamation r)
  (hm₀ : (m₀.map (whiskerRight φ (forget _))).IsAmalgamation m)

include hr₀ hm₀ in
lemma isCompatible_map_smul : ((r₀.smul m₀).map (whiskerRight φ (forget _))).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
  let a₁ := r₀ f₁ h₁
  let b₁ := m₀ f₁ h₁
  let a₂ := r₀ f₂ h₂
  let b₂ := m₀ f₂ h₂
  let a₀ := R₀.map g₁.op a₁
  let b₀ := M₀.map g₁.op b₁
  have ha₁ : (α.app (Opposite.op Y₁)) a₁ = (R.map f₁.op) r := (hr₀ f₁ h₁).symm
  have ha₂ : (α.app (Opposite.op Y₂)) a₂ = (R.map f₂.op) r := (hr₀ f₂ h₂).symm
  have hb₁ : (φ.app (Opposite.op Y₁)) b₁ = (A.map f₁.op) m := (hm₀ f₁ h₁).symm
  have hb₂ : (φ.app (Opposite.op Y₂)) b₂ = (A.map f₂.op) m := (hm₀ f₂ h₂).symm
  have ha₀ : (α.app (Opposite.op Z)) a₀ = (R.map (f₁.op ≫ g₁.op)) r := by
    rw [← RingCat.comp_apply, NatTrans.naturality, RingCat.comp_apply, ha₁, Functor.map_comp,
      RingCat.comp_apply]
  have hb₀ : (φ.app (Opposite.op Z)) b₀ = (A.map (f₁.op ≫ g₁.op)) m := by
    dsimp [b₀]
    erw [NatTrans.naturality_apply φ, hb₁, Functor.map_comp, ConcreteCategory.comp_apply]
  have ha₀' : (α.app (Opposite.op Z)) a₀ = (R.map (f₂.op ≫ g₂.op)) r := by
    rw [ha₀, ← op_comp, fac, op_comp]
  have hb₀' : (φ.app (Opposite.op Z)) b₀ = (A.map (f₂.op ≫ g₂.op)) m := by
    rw [hb₀, ← op_comp, fac, op_comp]
  dsimp
  erw [← NatTrans.naturality_apply φ, ← NatTrans.naturality_apply φ]
  exact (isCompatible_map_smul_aux α φ hA r m f₁ g₁ a₁ a₀ b₁ b₀ ha₁ ha₀ hb₁ hb₀).trans
    (isCompatible_map_smul_aux α φ hA r m f₂ g₂ a₂ a₀ b₂ b₀ ha₂ ha₀' hb₂ hb₀').symm

end

end Presieve.FamilyOfElements

end CategoryTheory

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

namespace PresheafOfModules

variable {M₀ : PresheafOfModules.{v} R₀} {A : Sheaf J AddCommGrpCat.{v}}
  (φ : M₀.presheaf ⟶ A.obj)
  [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]

namespace Sheafify

variable {X Y : Cᵒᵖ} (π : X ⟶ Y) (r r' : R.obj.obj X) (m m' : A.obj.obj X)

/-- Assuming `α : R₀ ⟶ R.val` is the sheafification map of a presheaf of rings `R₀`
and `φ : M₀.presheaf ⟶ A.val` is the sheafification map of the underlying
sheaf of abelian groups of a presheaf of modules `M₀` over `R₀`, then given
`r : R.val.obj X` and `m : A.val.obj X`, this structure contains the data
of `x : A.val.obj X` along with the property which makes `x` a good candidate
for the definition of the scalar multiplication `r • m`. -/
structure SMulCandidate where
  /-- The candidate for the scalar product `r • m`. -/
  x : A.obj.obj X
  h ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r)
    (m₀ : M₀.obj Y) (hm₀ : φ.app Y m₀ = A.obj.map f m) : A.obj.map f x = φ.app Y (r₀ • m₀)

/-- Constructor for `SMulCandidate`. -/
def SMulCandidate.mk' (S : Sieve X.unop) (hS : S ∈ J X.unop)
    (r₀ : Presieve.FamilyOfElements (R₀ ⋙ forget _) S.arrows)
    (m₀ : Presieve.FamilyOfElements (M₀.presheaf ⋙ forget _) S.arrows)
    (hr₀ : (r₀.map (whiskerRight α (forget _))).IsAmalgamation r)
    (hm₀ : (m₀.map (whiskerRight φ (forget _))).IsAmalgamation m)
    (a : A.obj.obj X)
    (ha : ((r₀.smul m₀).map (whiskerRight φ (forget _))).IsAmalgamation a) :
    SMulCandidate α φ r m where
  x := a
  h Y f a₀ ha₀ b₀ hb₀ := by
    apply A.isSeparated _ _ (J.pullback_stable f.unop hS)
    rintro Z g hg
    dsimp at hg
    rw [← ConcreteCategory.comp_apply, ← A.obj.map_comp, ← NatTrans.naturality_apply (D := Ab)]
    erw [M₀.map_smul] -- Mismatch between `M₀.map` and `M₀.presheaf.map`
    refine (ha _ hg).trans (app_eq_of_isLocallyInjective α φ A.isSeparated _ _ _ _ ?_ ?_)
    · rw [← RingCat.comp_apply, NatTrans.naturality, RingCat.comp_apply, ha₀]
      apply (hr₀ _ hg).symm.trans
      simp
      rfl
    · erw [NatTrans.naturality_apply φ, hb₀]
      apply (hm₀ _ hg).symm.trans
      dsimp
      rw [Functor.map_comp]
      rfl

instance : Nonempty (SMulCandidate α φ r m) := ⟨by
  let S := (Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m)
  have hS : S ∈ J _ := by
    apply J.intersection_covering
    all_goals apply Presheaf.imageSieve_mem
  have h₁ : S ≤ Presheaf.imageSieve α r := fun _ _ h => h.1
  have h₂ : S ≤ Presheaf.imageSieve φ m := fun _ _ h => h.2
  let r₀ := (Presieve.FamilyOfElements.localPreimage (whiskerRight α (forget _)) r).restrict h₁
  let m₀ := (Presieve.FamilyOfElements.localPreimage (whiskerRight φ (forget _)) m).restrict h₂
  have hr₀ : (r₀.map (whiskerRight α (forget _))).IsAmalgamation r := by
    rw [Presieve.FamilyOfElements.restrict_map]
    apply Presieve.isAmalgamation_restrict
    apply Presieve.FamilyOfElements.isAmalgamation_map_localPreimage
  have hm₀ : (m₀.map (whiskerRight φ (forget _))).IsAmalgamation m := by
    rw [Presieve.FamilyOfElements.restrict_map]
    apply Presieve.isAmalgamation_restrict
    apply Presieve.FamilyOfElements.isAmalgamation_map_localPreimage
  exact SMulCandidate.mk' α φ r m S hS r₀ m₀ hr₀ hm₀ _ (Presieve.IsSheafFor.isAmalgamation
    (((sheafCompose J (forget _)).obj A).2.isSheafFor S hS)
    (Presieve.FamilyOfElements.isCompatible_map_smul α φ A.isSeparated r m r₀ m₀ hr₀ hm₀))⟩

instance : Subsingleton (SMulCandidate α φ r m) where
  allEq := by
    rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩
    simp only [SMulCandidate.mk.injEq]
    let S := (Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m)
    have hS : S ∈ J _ := by
      apply J.intersection_covering
      all_goals apply Presheaf.imageSieve_mem
    apply A.isSeparated _ _ hS
    intro Y f ⟨⟨r₀, hr₀⟩, ⟨m₀, hm₀⟩⟩
    rw [h₁ f.op r₀ hr₀ m₀ hm₀, h₂ f.op r₀ hr₀ m₀ hm₀]

noncomputable instance : Unique (SMulCandidate α φ r m) :=
  uniqueOfSubsingleton (Nonempty.some inferInstance)

/-- The (unique) element in `SMulCandidate α φ r m`. -/
noncomputable def smulCandidate : SMulCandidate α φ r m := default

/-- The scalar multiplication on the sheafification of a presheaf of modules. -/
noncomputable def smul : A.obj.obj X := (smulCandidate α φ r m).x

lemma map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r)
    (m₀ : M₀.obj Y) (hm₀ : φ.app Y m₀ = A.obj.map f m) :
    A.obj.map f (smul α φ r m) = φ.app Y (r₀ • m₀) :=
  (smulCandidate α φ r m).h f r₀ hr₀ m₀ hm₀

protected lemma one_smul : smul α φ 1 m = m := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [← hm₀, map_smul_eq α φ 1 m f.op 1 (by simp) m₀ hm₀, one_smul]

set_option backward.isDefEq.respectTransparency false in
protected lemma zero_smul : smul α φ 0 m = 0 := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [map_smul_eq α φ 0 m f.op 0 (by simp) m₀ hm₀, zero_smul, map_zero,
    (A.obj.map f.op).hom.map_zero]

set_option backward.isDefEq.respectTransparency false in
protected lemma smul_zero : smul α φ r 0 = 0 := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J α r)
  rintro Y f ⟨r₀, hr₀⟩
  rw [(A.obj.map f.op).hom.map_zero, map_smul_eq α φ r 0 f.op r₀ hr₀ 0 (by simp),
    smul_zero, map_zero]

set_option backward.isDefEq.respectTransparency false in
protected lemma smul_add : smul α φ r (m + m') = smul α φ r m + smul α φ r m' := by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m ⊓ Presheaf.imageSieve φ m'
  have hS : S ∈ J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀, hr₀⟩, ⟨m₀ : M₀.obj _, hm₀ : (φ.app _) _ = _⟩⟩,
    ⟨m₀' : M₀.obj _, hm₀' : (φ.app _) _ = _⟩⟩
  rw [(A.obj.map f.op).hom.map_add, map_smul_eq α φ r m f.op r₀ hr₀ m₀ hm₀,
    map_smul_eq α φ r m' f.op r₀ hr₀ m₀' hm₀',
    map_smul_eq α φ r (m + m') f.op r₀ hr₀ (m₀ + m₀')
      (by rw [_root_.map_add, _root_.map_add, hm₀, hm₀']),
    smul_add, _root_.map_add]

set_option backward.isDefEq.respectTransparency false in
protected lemma add_smul : smul α φ (r + r') m = smul α φ r m + smul α φ r' m := by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve α r' ⊓ Presheaf.imageSieve φ m
  have hS : S ∈ J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀ : R₀.obj _, (hr₀ : (α.app (Opposite.op Y)) r₀ = (R.obj.map f.op) r)⟩,
    ⟨r₀' : R₀.obj _, (hr₀' : (α.app (Opposite.op Y)) r₀' = (R.obj.map f.op) r')⟩⟩, ⟨m₀, hm₀⟩⟩
  rw [(A.obj.map f.op).hom.map_add, map_smul_eq α φ r m f.op r₀ hr₀ m₀ hm₀,
    map_smul_eq α φ r' m f.op r₀' hr₀' m₀ hm₀,
    map_smul_eq α φ (r + r') m f.op (r₀ + r₀') (by rw [_root_.map_add, _root_.map_add, hr₀, hr₀'])
      m₀ hm₀, add_smul, _root_.map_add]

protected lemma mul_smul : smul α φ (r * r') m = smul α φ r (smul α φ r' m) := by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve α r' ⊓ Presheaf.imageSieve φ m
  have hS : S ∈ J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀ : R₀.obj _, (hr₀ : (α.app (Opposite.op Y)) r₀ = (R.obj.map f.op) r)⟩,
    ⟨r₀' : R₀.obj _, (hr₀' : (α.app (Opposite.op Y)) r₀' = (R.obj.map f.op) r')⟩⟩,
    ⟨m₀ : M₀.obj _, hm₀⟩⟩
  rw [map_smul_eq α φ (r * r') m f.op (r₀ * r₀')
    (by rw [map_mul, map_mul, hr₀, hr₀']) m₀ hm₀, mul_smul,
    map_smul_eq α φ r (smul α φ r' m) f.op r₀ hr₀ (r₀' • m₀)
      (map_smul_eq α φ r' m f.op r₀' hr₀' m₀ hm₀).symm]

variable (X)

/-- The module structure on the sections of the sheafification of the underlying
presheaf of abelian groups of a presheaf of modules. -/
@[implicit_reducible]
noncomputable def module : Module (R.obj.obj X) (A.obj.obj X) where
  smul r m := smul α φ r m
  one_smul := Sheafify.one_smul α φ
  zero_smul := Sheafify.zero_smul α φ
  smul_zero := Sheafify.smul_zero α φ
  smul_add := Sheafify.smul_add α φ
  add_smul := Sheafify.add_smul α φ
  mul_smul := Sheafify.mul_smul α φ

protected lemma map_smul :
    A.obj.map π (smul α φ r m) = smul α φ (R.obj.map π r) (A.obj.map π m) := by
  let S := Presheaf.imageSieve α (R.obj.map π r) ⊓ Presheaf.imageSieve φ (A.obj.map π m)
  have hS : S ∈ J Y.unop := by
    apply J.intersection_covering
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨r₀,
    (hr₀ : (α.app (Opposite.op Y)).hom r₀ = (R.obj.map f.op).hom ((R.obj.map π).hom r))⟩,
    ⟨m₀, (hm₀ : (φ.app _) _ = _)⟩⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    map_smul_eq α φ r m (π ≫ f.op) r₀ (by rw [hr₀, Functor.map_comp, RingCat.comp_apply]) m₀
      (by rw [hm₀, Functor.map_comp, ConcreteCategory.comp_apply]),
    map_smul_eq α φ (R.obj.map π r) (A.obj.map π m) f.op r₀ hr₀ m₀ hm₀]

end Sheafify

/-- Assuming `α : R₀ ⟶ R.obj` is the sheafification map of a presheaf of rings `R₀`
and `φ : M₀.presheaf ⟶ A.obj` is the sheafification map of the underlying
sheaf of abelian groups of a presheaf of modules `M₀` over `R₀`, this is
the sheaf of modules over `R` which is obtained by endowing the sections of
`A.obj` with a scalar multiplication. -/
noncomputable def sheafify : SheafOfModules.{v} R where
  val := letI := Sheafify.module α φ; ofPresheaf A.obj (Sheafify.map_smul _ _)
  isSheaf := A.property

/-- The canonical morphism from a presheaf of modules to its associated sheaf. -/
noncomputable def toSheafify : M₀ ⟶ (restrictScalars α).obj (sheafify α φ).val :=
  homMk φ (fun X r₀ m₀ ↦ by
    simpa using (Sheafify.map_smul_eq α φ (α.app _ r₀) (φ.app _ m₀) (𝟙 _)
      r₀ (by simp) m₀ (by simp)).symm)

lemma toSheafify_app_apply (X : Cᵒᵖ) (x : M₀.obj X) :
    ((toSheafify α φ).app X).hom x = φ.app X x := rfl

/-- `@[simp]`-normal form of `toSheafify_app_apply`. -/
@[simp]
lemma toSheafify_app_apply' (X : Cᵒᵖ) (x : M₀.obj X) :
    DFunLike.coe (F := (_ →ₗ[_] ↑((ModuleCat.restrictScalars (α.app X).hom).obj _)))
    ((toSheafify α φ).app X).hom x = φ.app X x := rfl

@[simp]
lemma toPresheaf_map_toSheafify : (toPresheaf R₀).map (toSheafify α φ) = φ := rfl

set_option backward.isDefEq.respectTransparency false in
instance : IsLocallyInjective J (toSheafify α φ) := by
  dsimp [IsLocallyInjective]; infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : IsLocallySurjective J (toSheafify α φ) := by
  dsimp [IsLocallySurjective]; infer_instance

variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The bijection `((sheafify α φ).val ⟶ F) ≃ (M₀ ⟶ (restrictScalars α).obj F)` which
is part of the universal property of the sheafification of the presheaf of modules `M₀`,
when `F` is a presheaf of modules which is a sheaf. -/
noncomputable def sheafifyHomEquiv' {F : PresheafOfModules.{v} R.obj}
    (hF : Presheaf.IsSheaf J F.presheaf) :
    ((sheafify α φ).val ⟶ F) ≃ (M₀ ⟶ (restrictScalars α).obj F) :=
  (restrictHomEquivOfIsLocallySurjective α hF).trans
    (homEquivOfIsLocallyBijective (f := toSheafify α φ)
      (N := (restrictScalars α).obj F) hF)

lemma comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom {F : PresheafOfModules.{v} R.obj}
    (hF : Presheaf.IsSheaf J F.presheaf) (f : M₀ ⟶ (restrictScalars α).obj F) :
    φ ≫ (toPresheaf R.obj).map ((sheafifyHomEquiv' α φ hF).symm f) = (toPresheaf R₀).map f :=
  (toPresheaf _).congr_map ((sheafifyHomEquiv' α φ hF).apply_symm_apply f)

/-- The bijection
`(sheafify α φ ⟶ F) ≃ (M₀ ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F))`
which is part of the universal property of the sheafification of the presheaf of modules `M₀`,
for any sheaf of modules `F`, see `PresheafOfModules.sheafificationAdjunction` -/
noncomputable def sheafifyHomEquiv {F : SheafOfModules.{v} R} :
    (sheafify α φ ⟶ F) ≃
      (M₀ ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) :=
  (SheafOfModules.fullyFaithfulForget R).homEquiv.trans
    (sheafifyHomEquiv' α φ F.isSheaf)

section

variable {M₀' : PresheafOfModules.{v} R₀} {A' : Sheaf J AddCommGrpCat.{v}}
  (φ' : M₀'.presheaf ⟶ A'.obj)
  [Presheaf.IsLocallyInjective J φ'] [Presheaf.IsLocallySurjective J φ']
  (τ₀ : M₀ ⟶ M₀') (τ : A ⟶ A')

set_option backward.isDefEq.respectTransparency false in
/-- The morphism of sheaves of modules `sheafify α φ ⟶ sheafify α φ'`
induced by morphisms `τ₀ : M₀ ⟶ M₀'` and `τ : A ⟶ A'`
which satisfy `τ₀.hom ≫ φ' = φ ≫ τ.val`. -/
@[simps]
noncomputable def sheafifyMap (fac : (toPresheaf R₀).map τ₀ ≫ φ' = φ ≫ τ.hom) :
    sheafify α φ ⟶ sheafify α φ' where
  val := homMk τ.hom (fun X r m ↦ by
    let f := (sheafifyHomEquiv' α φ (by exact A'.property)).symm (τ₀ ≫ toSheafify α φ')
    suffices τ.hom = (toPresheaf _).map f by simpa only [this] using (f.app X).hom.map_smul r m
    apply ((J.W_of_isLocallyBijective φ).homEquiv _ A'.property).injective
    dsimp [f]
    erw [comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom]
    rw [← fac, Functor.map_comp, toPresheaf_map_toSheafify])

end

end PresheafOfModules
