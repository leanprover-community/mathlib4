/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.FintypeCat
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryLimits
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-!
# The Galois category `Over` of a connected object

-/

-- to be moved to `CategoryTheory/Galois`

@[expose] public section

universe w v u

namespace CategoryTheory

open PreGaloisCategory Limits

variable {C : Type u} [Category.{v} C]

/-- Let `S : C`, assuming that `Over.forget S : Over S ⥤ C`, this is the bijection
expressing that an object `X : Over S` is initial if and only if `X.left` is. -/
noncomputable def Over.isInitialEquiv {S : C} {X : Over S}
    [PreservesColimit (Functor.empty (Over S)) (Over.forget S)] :
    IsInitial X ≃ IsInitial X.left where
  toFun h := IsInitial.isInitialObj (G := Over.forget S)  _  h
  invFun h :=
    IsInitial.ofUniqueHom (fun Z ↦ Over.homMk (h.to _) (h.hom_ext _ _))
      (fun Z m ↦ by ext; apply h.hom_ext)
  left_inv _ := by subsingleton
  right_inv _ := by subsingleton

namespace PreGaloisCategory

lemma isConnected_over_iff
    {S : C} (X : Over S)
    [(Over.forget S).PreservesMonomorphisms]
    [PreservesColimit (Functor.empty.{0} (Over S)) (Over.forget S)] :
    PreGaloisCategory.IsConnected X ↔
      PreGaloisCategory.IsConnected X.left := by
  refine ⟨fun _ ↦ ⟨fun h ↦ IsConnected.notInitial (Over.isInitialEquiv.symm h),
    fun Y i _ h ↦ ?_⟩,
    fun _ ↦ ⟨fun h ↦ IsConnected.notInitial (Over.isInitialEquiv h), fun Y i _ h ↦ ?_⟩⟩
  · let f : Over.mk (i ≫ X.hom) ⟶ X := Over.homMk i
    have := IsConnected.noTrivialComponent _ f (fun h' ↦ h (Over.isInitialEquiv h'))
    exact inferInstanceAs (IsIso ((Over.forget S).map f))
  · have : Mono i.left := inferInstanceAs (Mono ((Over.forget S).map i))
    have : IsIso ((Over.forget S).map i) :=
      IsConnected.noTrivialComponent Y.left i.left
        (fun h' ↦ h (Over.isInitialEquiv.symm h'))
    exact isIso_of_reflects_iso _ (Over.forget _)

instance {X S : C} (f : X ⟶ S)
    [(Over.forget S).PreservesMonomorphisms]
    [PreservesColimit (Functor.empty.{0} (Over S)) (Over.forget S)]
    [PreGaloisCategory.IsConnected X] :
    PreGaloisCategory.IsConnected (Over.mk f) := by
  rwa [isConnected_over_iff]

instance (S : C)
    [(Over.forget S).PreservesMonomorphisms]
    [PreservesColimit (Functor.empty.{0} (Over S)) (Over.forget S)] :
    PreservesIsConnected (Over.forget S) where
  preserves {X} _ := by
    rw [Over.forget_obj, ← isConnected_over_iff]
    infer_instance

end PreGaloisCategory

namespace GaloisCategory

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (S : C)
  [PreGaloisCategory.IsConnected S]

variable {S} in
lemma exists_aut_of_isConnected
    {X : C} (f : X ⟶ S) (x : F.obj X) (s : F.obj S) :
    ∃ (g : Aut F), F.map f (g.hom.app _ x) = s := by
  obtain ⟨g, hg⟩ :=
    (FiberFunctor.isPretransitive_of_isConnected F S).exists_smul_eq (F.map f x) s
  refine ⟨g, ?_⟩
  rwa [← NatTrans.naturality_apply]

/-- If `F : C ⥤ FintypeCat.{w}` is a fiber functor, and `s : F.obj S` where
`S` is a connected object of `C`, this is the fiber functor
on `Over S` which sends `f : X ⟶ S` to the inverse image of `s` by `F.map f`. -/
@[implicit_reducible, simps]
def fiberFunctorOver (s : F.obj S) : Over S ⥤ FintypeCat.{w} where
  obj X := .of ((F.map X.hom) ⁻¹' {s})
  map f := FintypeCat.homMk (fun x ↦⟨F.map f.left x, by
    simpa only [← ConcreteCategory.comp_apply, ← F.map_comp, f.w,
      Set.mem_preimage, Set.mem_singleton_iff] using x.prop⟩)

instance : PreGaloisCategory (Over S) where
  monoInducesIsoOnDirectSummand {X Y} i _ := by
    have : PreGaloisCategory.IsConnected S := inferInstance
    obtain ⟨Z, u, ⟨h⟩⟩ := monoInducesIsoOnDirectSummand i.left
    exact ⟨Over.mk (u ≫ Y.hom), Over.homMk u,
      ⟨isColimitOfReflects (Over.forget _)
        ((isColimitMapCoconeBinaryCofanEquiv ..).2 h)⟩⟩

instance : PreservesFiniteColimits (Over.post F (X := S)) where
  preservesFiniteColimits J _ _ := by
    have : PreservesColimitsOfShape J (Over.post F ⋙ Over.forget (F.obj S)) :=
      inferInstanceAs (PreservesColimitsOfShape J (Over.forget _ ⋙ F))
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (Over.forget _)

instance (s : F.obj S) : PreservesFiniteColimits (fiberFunctorOver F S s) :=
  inferInstanceAs (PreservesFiniteColimits (Over.post F ⋙ FintypeCat.overFiber s))

instance (s : F.obj S) : PreservesFiniteLimits (fiberFunctorOver F S s) :=
  inferInstanceAs (PreservesFiniteLimits (Over.post F ⋙ FintypeCat.overFiber s))

set_option backward.isDefEq.respectTransparency false in
instance (s : F.obj S) : FiberFunctor (fiberFunctorOver F S s) where
  preservesQuotientsByFiniteGroups G _ _ := by
    obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} G
    exact preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm _
  reflectsIsos := ⟨fun {X Y} f hf ↦ by
    rw [← isIso_iff_of_reflects_iso _ (Over.forget S),
      ← isIso_iff_of_reflects_iso _ F, ConcreteCategory.isIso_iff_bijective]
    rw [ConcreteCategory.isIso_iff_bijective] at hf
    refine ⟨fun x₁ x₂ h ↦ ?_, fun y ↦ ?_⟩
    · dsimp at h
      obtain ⟨g, hg⟩ := exists_aut_of_isConnected F X.hom x₁ s
      refine ConcreteCategory.injective_of_mono_of_preservesPullback (g.hom.app _)
        (Subtype.ext_iff.1 (hf.injective (a₁ := ⟨_, hg⟩) (a₂ := ⟨_, ?_⟩) ?_))
      · simp only [Over.forget_obj, Set.mem_preimage, Set.mem_singleton_iff]
        rwa [← NatTrans.naturality_apply, ← f.w,
          Functor.map_comp, ConcreteCategory.comp_apply, ← h,
          ← Functor.map_comp_apply, f.w, NatTrans.naturality_apply]
      · dsimp
        ext
        change F.map f.left (g.hom.app _ x₁) = F.map f.left (g.hom.app _ x₂)
        simp only [← NatTrans.naturality_apply, h]
    · dsimp at y
      obtain ⟨g, hg⟩ := exists_aut_of_isConnected F Y.hom y s
      obtain ⟨x, hx⟩ := hf.surjective ⟨_, hg⟩
      replace hx : F.map f.left x.val = g.hom.app _ y := by
        simpa [Subtype.ext_iff] using! hx
      refine ⟨g.inv.app _ x.val,
        (ConcreteCategory.injective_of_mono_of_preservesPullback (g.hom.app _) ?_)⟩
      dsimp
      simp only [← hx, ← ConcreteCategory.comp_apply, Category.assoc,
        NatTrans.naturality, Iso.inv_hom_id_app_assoc]⟩

instance : GaloisCategory (Over S) where
  hasFiberFunctor :=
    ⟨fiberFunctorOver (getFiberFunctor C) S (Classical.arbitrary _), inferInstance⟩

end GaloisCategory

end CategoryTheory
