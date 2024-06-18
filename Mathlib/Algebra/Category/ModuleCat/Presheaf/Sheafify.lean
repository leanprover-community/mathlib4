/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# The associated sheaf of a presheaf of modules

In this file, given a presheaf of modules `M₀` over a presheaf of rings `R₀`,
we construct the associated sheaf of `M₀`. More precisely, if `R` is a sheaf of
rings and `α : R₀ ⟶ R.val` is locally bijective, and `A` is the sheafification
of the underlying presheaf of abelian groups of `M₀`, i.e. we have a locally bijective
map `φ : M₀.presheaf ⟶ A.val`, then we endow `A` with the structure of a
sheaf of modules over `R`: this is `PresheafOfModules.sheafify α φ`.

In many application, the morphism `α` shall be the identity, but this more
general construction allows the sheafification of both the presheaf of rings
and the presheaf of modules.

-/

universe w v v₁ u₁ u

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

namespace CategoryTheory

namespace Presieve.FamilyOfElements

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

section smul

variable {R : Cᵒᵖ ⥤ RingCat.{u}} {M : PresheafOfModules.{v} R} {X : C} {P : Presieve X}
  (r : FamilyOfElements (R ⋙ forget _) P) (m : FamilyOfElements (M.presheaf ⋙ forget _) P)

/-- The scalar multiplication of family of elements of a presheaf of modules `M` over `R`
by a family of elements of `R`. -/
def smul : FamilyOfElements (M.presheaf ⋙ forget _) P := fun Y f hf =>
  HSMul.hSMul (α := R.obj (Opposite.op Y)) (β := M.presheaf.obj (Opposite.op Y)) (r f hf) (m f hf)

end smul

section

variable {R₀ R : Cᵒᵖ ⥤ RingCat.{u}} (α : R₀ ⟶ R) [Presheaf.IsLocallyInjective J α]
  {M₀ : PresheafOfModules.{v} R₀} {A : Cᵒᵖ ⥤ AddCommGroupCat.{v}} (φ : M₀.presheaf ⟶ A)
  [Presheaf.IsLocallyInjective J φ] (hA : Presheaf.IsSeparated J A)
  {X : C} (r : R.obj (Opposite.op X)) (m : A.obj (Opposite.op X)) {P : Presieve X}
  (r₀ : FamilyOfElements (R₀ ⋙ forget _) P) (m₀ : FamilyOfElements (M₀.presheaf ⋙ forget _) P)
  (hr₀ : (r₀.map (whiskerRight α (forget _))).IsAmalgamation r)
  (hm₀ : (m₀.map (whiskerRight φ (forget _))).IsAmalgamation m)

lemma _root_.PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective
    {Y : C} (r₀ r₀' : R₀.obj (Opposite.op Y))
    (m₀ m₀' : M₀.presheaf.obj (Opposite.op Y))
    (hr₀ : α.app _ r₀ = α.app _ r₀')
    (hm₀ : φ.app _ m₀ = φ.app _ m₀') :
    φ.app _ (r₀ • m₀) = φ.app _ (r₀' • m₀') := by
  apply hA _ (Presheaf.equalizerSieve r₀ r₀' ⊓ Presheaf.equalizerSieve (F := M₀.presheaf) m₀ m₀')
  · apply J.intersection_covering
    · exact Presheaf.equalizerSieve_mem J α _ _ hr₀
    · exact Presheaf.equalizerSieve_mem J φ _ _ hm₀
  · intro Z g hg
    erw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, M₀.map_smul, M₀.map_smul,
      hg.1, hg.2]
    rfl

lemma isCompatible_map_smul_aux {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y)
    (r₀ : R₀.obj (Opposite.op Y)) (r₀' : R₀.obj (Opposite.op Z))
    (m₀ : M₀.presheaf.obj (Opposite.op Y)) (m₀' : M₀.presheaf.obj (Opposite.op Z))
    (hr₀ : α.app _ r₀ = R.map f.op r) (hr₀' : α.app _ r₀' = R.map (f.op ≫ g.op) r)
    (hm₀ : φ.app _ m₀ = A.map f.op m) (hm₀' : φ.app _ m₀' = A.map (f.op ≫ g.op) m) :
    φ.app _ (M₀.presheaf.map g.op (r₀ • m₀)) = φ.app _ (r₀' • m₀') := by
  rw [← PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective α φ hA (R₀.map g.op r₀) r₀'
    (M₀.presheaf.map g.op m₀) m₀', M₀.map_smul]
  · rw [hr₀', R.map_comp, comp_apply, ← hr₀, NatTrans.naturality_apply]
  · rw [hm₀', A.map_comp, AddCommGroupCat.coe_comp, Function.comp_apply, ← hm₀]
    erw [NatTrans.naturality_apply]
    rfl

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
    dsimp [a₀]
    rw [NatTrans.naturality_apply, ha₁, Functor.map_comp, comp_apply]
  have hb₀ : (φ.app (Opposite.op Z)) b₀ = (A.map (f₁.op ≫ g₁.op)) m := by
    dsimp [b₀]
    erw [NatTrans.naturality_apply, hb₁, Functor.map_comp, comp_apply]
    rfl
  have ha₀' : (α.app (Opposite.op Z)) a₀ = (R.map (f₂.op ≫ g₂.op)) r := by
    rw [ha₀, ← op_comp, fac, op_comp]
  have hb₀' : (φ.app (Opposite.op Z)) b₀ = (A.map (f₂.op ≫ g₂.op)) m := by
    rw [hb₀, ← op_comp, fac, op_comp]
  dsimp
  erw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  exact (isCompatible_map_smul_aux α φ hA r m f₁ g₁ a₁ a₀ b₁ b₀ ha₁ ha₀ hb₁ hb₀).trans
    (isCompatible_map_smul_aux α φ hA r m f₂ g₂ a₂ a₀ b₂ b₀ ha₂ ha₀' hb₂ hb₀').symm

end

end Presieve.FamilyOfElements

end CategoryTheory

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.val)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

namespace PresheafOfModules

variable {M₀ : PresheafOfModules.{v} R₀} {A : Sheaf J AddCommGroupCat.{v}}
  (φ : M₀.presheaf ⟶ A.val)
  [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]

namespace Sheafify

variable {X Y : Cᵒᵖ} (π : X ⟶ Y) (r r' : R.val.obj X) (m m' : A.val.obj X)

/-- Assuming `α : R₀ ⟶ R.val` is the sheafification map of a presheaf of rings `R₀`
and `φ : M₀.presheaf ⟶ A.val` is the sheafification map of the underlying
sheaf of abelian groups of a presheaf of modules `M₀` over `R₀`, then given
`r : R.val.obj X` and `m : A.val.obj X`, this structure contains the data
of `x : A.val.obj X` along with the property which makes `x` a good candidate
for the definition of the scalar multiplication `r • m`. -/
structure SMulCandidate where
  /-- The candidate for the scalar product `r • m`. -/
  x : A.val.obj X
  h ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.val.map f r)
    (m₀ : M₀.obj Y) (hm₀ : φ.app Y m₀ = A.val.map f m) : A.val.map f x = φ.app Y (r₀ • m₀)

/-- Constructor for `SMulCandidate`. -/
def SMulCandidate.mk' (S : Sieve X.unop) (hS : S ∈ J X.unop)
    (r₀ : Presieve.FamilyOfElements (R₀ ⋙ forget _) S.arrows)
    (m₀ : Presieve.FamilyOfElements (M₀.presheaf ⋙ forget _) S.arrows)
    (hr₀ : (r₀.map (whiskerRight α (forget _))).IsAmalgamation r)
    (hm₀ : (m₀.map (whiskerRight φ (forget _))).IsAmalgamation m)
    (a : A.val.obj X)
    (ha : ((r₀.smul m₀).map (whiskerRight φ (forget _))).IsAmalgamation a) :
    SMulCandidate α φ r m where
  x := a
  h Y f a₀ ha₀ b₀ hb₀ := by
    apply A.isSeparated _ _ (J.pullback_stable f.unop hS)
    rintro Z g hg
    dsimp at hg
    erw [← comp_apply, ← A.val.map_comp, ← NatTrans.naturality_apply, M₀.map_smul]
    refine (ha _ hg).trans (app_eq_of_isLocallyInjective α φ A.isSeparated _ _ _ _ ?_ ?_)
    · rw [NatTrans.naturality_apply, ha₀]
      apply (hr₀ _ hg).symm.trans
      dsimp
      rw [Functor.map_comp, comp_apply]
    · erw [NatTrans.naturality_apply, hb₀]
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
    erw [h₁ f.op r₀ hr₀ m₀ hm₀, h₂ f.op r₀ hr₀ m₀ hm₀]

noncomputable instance : Unique (SMulCandidate α φ r m) :=
  uniqueOfSubsingleton (Nonempty.some inferInstance)

/-- The (unique) element in `SMulCandidate α φ r m`. -/
noncomputable def smulCandidate : SMulCandidate α φ r m := default

/-- The scalar multiplication on the sheafification of a presheaf of modules. -/
noncomputable def smul : A.val.obj X := (smulCandidate α φ r m).x

lemma map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.val.map f r)
    (m₀ : M₀.obj Y) (hm₀ : φ.app Y m₀ = A.val.map f m) :
    A.val.map f (smul α φ r m) = φ.app Y (r₀ • m₀) :=
  (smulCandidate α φ r m).h f r₀ hr₀ m₀ hm₀

protected lemma one_smul : smul α φ 1 m = m := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [← hm₀]
  erw [map_smul_eq α φ 1 m f.op 1 (by simp) m₀ hm₀, one_smul]
  rfl

protected lemma zero_smul : smul α φ 0 m = 0 := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  erw [map_smul_eq α φ 0 m f.op 0 (by simp) m₀ hm₀, zero_smul, map_zero,
    (A.val.map f.op).map_zero]

protected lemma smul_zero : smul α φ r 0 = 0 := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J α r)
  rintro Y f ⟨r₀, hr₀⟩
  erw [(A.val.map f.op).map_zero, map_smul_eq α φ r 0 f.op r₀ hr₀ 0 (by simp),
    smul_zero, map_zero]

protected lemma smul_add : smul α φ r (m + m') = smul α φ r m + smul α φ r m' := by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m ⊓ Presheaf.imageSieve φ m'
  have hS : S ∈ J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀, hr₀⟩, ⟨m₀ : M₀.presheaf.obj _, hm₀⟩⟩, ⟨m₀' : M₀.presheaf.obj _, hm₀'⟩⟩
  erw [(A.val.map f.op).map_add, map_smul_eq α φ r m f.op r₀ hr₀ m₀ hm₀,
    map_smul_eq α φ r m' f.op r₀ hr₀ m₀' hm₀',
    map_smul_eq α φ r (m + m') f.op r₀ hr₀ (m₀ + m₀')
      (by erw [map_add, map_add, hm₀, hm₀']; rfl),
    smul_add, map_add]

protected lemma add_smul : smul α φ (r + r') m = smul α φ r m + smul α φ r' m := by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve α r' ⊓ Presheaf.imageSieve φ m
  have hS : S ∈ J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀ : R₀.obj _, hr₀⟩, ⟨r₀' : R₀.obj _, hr₀'⟩⟩, ⟨m₀, hm₀⟩⟩
  erw [(A.val.map f.op).map_add, map_smul_eq α φ r m f.op r₀ hr₀ m₀ hm₀,
    map_smul_eq α φ r' m f.op r₀' hr₀' m₀ hm₀,
    map_smul_eq α φ (r + r') m f.op (r₀ + r₀') (by rw [map_add, map_add, hr₀, hr₀'])
      m₀ hm₀, add_smul, map_add]

protected lemma mul_smul : smul α φ (r * r') m = smul α φ r (smul α φ r' m) := by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve α r' ⊓ Presheaf.imageSieve φ m
  have hS : S ∈ J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀ : R₀.obj _, hr₀⟩, ⟨r₀' : R₀.obj _, hr₀'⟩⟩, ⟨m₀ : M₀.presheaf.obj _, hm₀⟩⟩
  erw [map_smul_eq α φ (r * r') m f.op (r₀ * r₀')
    (by rw [map_mul, map_mul, hr₀, hr₀']) m₀ hm₀, mul_smul,
    map_smul_eq α φ r (smul α φ r' m) f.op r₀ hr₀ (r₀' • m₀)
      (map_smul_eq α φ r' m f.op r₀' hr₀' m₀ hm₀).symm]

variable (X)

/-- The module structure on the sections of the sheafification of the underlying
presheaf of abelian groups of a presheaf of modules. -/
noncomputable def module : Module (R.val.obj X) (A.val.obj X) where
  smul r m := smul α φ r m
  one_smul := Sheafify.one_smul α φ
  zero_smul := Sheafify.zero_smul α φ
  smul_zero := Sheafify.smul_zero α φ
  smul_add := Sheafify.smul_add α φ
  add_smul := Sheafify.add_smul α φ
  mul_smul := Sheafify.mul_smul α φ

lemma map_smul :
    A.val.map π (smul α φ r m) = smul α φ (R.val.map π r) (A.val.map π m) := by
  let S := Presheaf.imageSieve α (R.val.map π r) ⊓ Presheaf.imageSieve φ (A.val.map π m)
  have hS : S ∈ J Y.unop := by
    apply J.intersection_covering
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨r₀, hr₀⟩, ⟨m₀, hm₀⟩⟩
  erw [← comp_apply, ← Functor.map_comp,
    map_smul_eq α φ r m (π ≫ f.op) r₀ (by rw [hr₀, Functor.map_comp, comp_apply]) m₀
      (by erw [hm₀, Functor.map_comp, comp_apply]; rfl),
    map_smul_eq α φ (R.val.map π r) (A.val.map π m) f.op r₀ hr₀ m₀ hm₀]

end Sheafify

/-- Assuming `α : R₀ ⟶ R.val` is the sheafification map of a presheaf of rings `R₀`
and `φ : M₀.presheaf ⟶ A.val` is the sheafification map of the underlying
sheaf of abelian groups of a presheaf of modules `M₀` over `R₀`, this is
the sheaf of modules over `R` which is obtained by endowing the sections of
`A.val` with a scalar multiplication. -/
noncomputable def sheafify : SheafOfModules.{v} R where
  val :=
    { presheaf := A.val
      module := Sheafify.module α φ
      map_smul := fun _ _ _ => by apply Sheafify.map_smul }
  isSheaf := A.cond

/-- The canonical morphism from a presheaf of modules to its associated sheaf. -/
@[simps]
def toSheafify : M₀ ⟶ (restrictScalars α).obj (sheafify α φ).val where
  hom := φ
  map_smul X r₀ m₀ := by
    simpa using (Sheafify.map_smul_eq α φ (α.app _ r₀) (φ.app _ m₀) (𝟙 _)
      r₀ (by aesop) m₀ (by simp)).symm

instance : Presheaf.IsLocallyInjective J (toSheafify α φ).hom := by
  dsimp; infer_instance

instance : Presheaf.IsLocallySurjective J (toSheafify α φ).hom := by
  dsimp; infer_instance

variable [J.WEqualsLocallyBijective AddCommGroupCat.{v}]

/-- The bijection `((sheafify α φ).val ⟶ F) ≃ (M₀ ⟶ (restrictScalars α).obj F)` which
is part of the universal property of the sheafification of the presheaf of modules `M₀`,
when `F` is a presheaf of modules which is a sheaf. -/
noncomputable def sheafifyHomEquiv' {F : PresheafOfModules.{v} R.val}
    (hF : Presheaf.IsSheaf J F.presheaf) :
    ((sheafify α φ).val ⟶ F) ≃ (M₀ ⟶ (restrictScalars α).obj F) :=
  (restrictHomEquivOfIsLocallySurjective α hF).trans
    (homEquivOfIsLocallyBijective (f := toSheafify α φ)
      (N := (restrictScalars α).obj F) hF)

lemma comp_sheafifyHomEquiv'_symm_hom {F : PresheafOfModules.{v} R.val}
    (hF : Presheaf.IsSheaf J F.presheaf) (f : M₀ ⟶ (restrictScalars α).obj F) :
    φ ≫ ((sheafifyHomEquiv' α φ hF).symm f).hom = f.hom :=
  congr_arg Hom.hom ((sheafifyHomEquiv' α φ hF).apply_symm_apply f)

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

variable {M₀' : PresheafOfModules.{v} R₀} {A' : Sheaf J AddCommGroupCat.{v}}
  (φ' : M₀'.presheaf ⟶ A'.val)
  [Presheaf.IsLocallyInjective J φ'] [Presheaf.IsLocallySurjective J φ']
  (τ₀ : M₀ ⟶ M₀') (τ : A ⟶ A')
  (fac : τ₀.hom ≫ φ' = φ ≫ τ.val)

/-- The morphism of sheaves of modules `sheafify α φ ⟶ sheafify α φ'`
induced by morphisms `τ₀ : M₀ ⟶ M₀'` and `τ : A ⟶ A'`
which satisfy `τ₀.hom ≫ φ' = φ ≫ τ.val`. -/
@[simps]
def sheafifyMap : sheafify α φ ⟶ sheafify α φ' where
  val :=
    { hom := τ.val
      map_smul := by
        let f := (sheafifyHomEquiv' α φ (by exact A'.cond)).symm (τ₀ ≫ toSheafify α φ')
        have eq : τ.val = f.hom := ((J.W_of_isLocallyBijective φ).homEquiv _ A'.cond).injective
          (by
            dsimp [f]
            erw [comp_sheafifyHomEquiv'_symm_hom]
            simp only [← fac, toSheafify_hom, Hom.comp_hom])
        convert f.map_smul }

end

end PresheafOfModules
