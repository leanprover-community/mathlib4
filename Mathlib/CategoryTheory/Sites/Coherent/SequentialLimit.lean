/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Sites.Coherent.LocallySurjective
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Subcanonical
/-!

# Limits of epimorphisms in coherent topoi

This file proves that a sequential limit of epimorphisms is epimorphic in the category of sheaves
for the coherent topology on a preregular finitary extensive concrete category where the effective
epimorphisms are precisely the surjective ones.

In other words, given epimorphisms of sheaves

`⋯ ⟶ Xₙ₊₁ ⟶ Xₙ ⟶ ⋯ ⟶ X₀`,

the projection map `lim Xₙ ⟶ X₀` is an epimorphism (see `coherentTopology.epi_π_app_zero_of_epi`).

This is deduced from the corresponding statement about locally surjective morphisms of sheaves
(see `coherentTopology.isLocallySurjective_π_app_zero_of_isLocallySurjective_map`).
-/

universe w v u

open CategoryTheory Limits Opposite

attribute [local instance] ConcreteCategory.instFunLike

namespace CategoryTheory.coherentTopology

variable {C : Type u} [Category.{v} C] [Preregular C] [FinitaryExtensive C]

section TransitionMaps

variable {F : ℕᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)} {c : Cone F}
    (hc : IsLimit c)
    (hF : ∀ n, Sheaf.IsLocallySurjective (F.map (homOfLE (Nat.le_succ n)).op))

namespace TransitionMaps

private noncomputable def preimage (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) :
    (n : ℕ) → ((Y : C) × (F.obj ⟨n⟩).val.obj ⟨Y⟩)
  | 0 => ⟨X, y⟩
  | (n+1) => by
    have := hF n
    rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
    specialize this (preimage X y n).1 (preimage X y n).2
    exact ⟨this.choose, this.choose_spec.choose_spec.choose_spec.choose⟩

private noncomputable def preimageTransitionMap (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) (n : ℕ) :
    (preimage hF X y (n + 1)).1 ⟶ (preimage hF X y n).1 := by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
  specialize this (preimage hF X y n).1 (preimage hF X y n).2
  exact this.choose_spec.choose

private lemma preimageTransitionMap_effectiveEpi (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) (n : ℕ) :
    EffectiveEpi (preimageTransitionMap hF X y n) := by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
  specialize this (preimage hF X y n).1 (preimage hF X y n).2
  exact this.choose_spec.choose_spec.choose

private lemma preimage_w (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) (n : ℕ) :
    (F.map (homOfLE (n.le_add_right 1)).op).val.app ⟨(preimage hF X y (n+1)).1⟩
      (preimage hF X y (n+1)).2 = ((F.obj ⟨n⟩).val.map (preimageTransitionMap hF X y n).op)
        (preimage hF X y n).2 := by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
  specialize this (preimage hF X y n).1 (preimage hF X y n).2
  exact this.choose_spec.choose_spec.choose_spec.choose_spec

private noncomputable def preimageDiagram (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun n ↦ (preimage hF X y n).1)
    fun n ↦ preimageTransitionMap hF X y n

end TransitionMaps

end TransitionMaps

section Maps

variable {F G : ℕᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)}
    {c : Cone F} (hc : IsLimit c) {d : Cone G} (hd : IsLimit d)
    (f : F ⟶ G)
    (hF : ∀ n, Sheaf.IsLocallySurjective (f.app n))

namespace Maps

structure AuxStruct (X : C) (y : d.pt.val.obj ⟨X⟩) (n : ℕ) where
  obj : C
  element : (F.obj ⟨n⟩).val.obj ⟨obj⟩
  map : obj ⟶ X
  effectiveEpi : EffectiveEpi map
  w : (f.app ⟨n⟩).val.app ⟨obj⟩ element = (G.obj ⟨n⟩).val.map ⟨map⟩ ((d.π.app ⟨n⟩).val.app ⟨_⟩ y)

private noncomputable def preimageAux (X : C) (y : d.pt.val.obj ⟨X⟩) (n : ℕ) :
    AuxStruct f X y n := by
  have := hF ⟨n⟩
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
  specialize this X ((d.π.app ⟨n⟩).val.app ⟨_⟩ y)
  exact {
    obj := this.choose
    element := this.choose_spec.choose_spec.choose_spec.choose
    map := this.choose_spec.choose
    effectiveEpi := this.choose_spec.choose_spec.choose
    w := this.choose_spec.choose_spec.choose_spec.choose_spec }

private noncomputable def preimage (X : C) (y : d.pt.val.obj ⟨X⟩) : (n : ℕ) → AuxStruct f X y n
  | 0 => preimageAux f hF X y 0
  | n + 1 => by
    obtain ⟨T, _, g, hg, _⟩ := preimage X y n
    obtain ⟨T', x', g', hg', w'⟩ := preimageAux f hF X y (n + 1)
    have := Preregular.exists_fac g g'
    refine {
      obj := this.choose
      element := (F.obj ⟨_⟩).val.map this.choose_spec.choose_spec.choose_spec.choose.op x'
      map := this.choose_spec.choose ≫ g
      effectiveEpi :=
        have := this.choose_spec.choose_spec.choose
        inferInstance
      w := ?_ }
    conv_rhs => rw [← this.choose_spec.choose_spec.choose_spec.choose_spec]
    change ((F.obj ⟨n + 1⟩).val.map _ ≫ _) _ = _
    rw [(f.app _).val.naturality]
    dsimp
    rw [w', ← FunctorToTypes.map_comp_apply]
    rfl

private noncomputable def preimageTransitionMap (X : C) (y : d.pt.val.obj ⟨X⟩) (n : ℕ) :
    (preimage f hF X y (n + 1)).obj ⟶ (preimage f hF X y n).obj := by
  have := (preimageAux f hF X y (n + 1)).effectiveEpi
  have := Preregular.exists_fac (preimage f hF X y n).map (preimageAux f hF X y (n + 1)).map
  exact this.choose_spec.choose

private noncomputable def preimageAuxMap (X : C) (y : d.pt.val.obj ⟨X⟩) (n : ℕ) :
    (preimage f hF X y (n + 1)).obj ⟶ (preimageAux f hF X y (n + 1)).obj := by
  have := (preimageAux f hF X y (n + 1)).effectiveEpi
  have := Preregular.exists_fac (preimage f hF X y n).map (preimageAux f hF X y (n + 1)).map
  exact this.choose_spec.choose_spec.choose_spec.choose

private lemma preimageTransitionMap_effectiveEpi (X : C) (y : d.pt.val.obj ⟨X⟩)
    (n : ℕ) : EffectiveEpi (preimageTransitionMap f hF X y n) := by
  have := (preimageAux f hF X y (n + 1)).effectiveEpi
  have := Preregular.exists_fac (preimage f hF X y n).map (preimageAux f hF X y (n + 1)).map
  exact this.choose_spec.choose_spec.choose

private lemma preimageTransitionMap_commSq (X : C) (y : d.pt.val.obj ⟨X⟩)
    (n : ℕ) : (preimageTransitionMap f hF X y n) ≫ (preimage f hF X y n).map =
      preimageAuxMap f hF X y n  ≫ (preimageAux f hF X y (n + 1)).map := by
  have := (preimageAux f hF X y (n + 1)).effectiveEpi
  have := Preregular.exists_fac (preimage f hF X y n).map (preimageAux f hF X y (n + 1)).map
  exact this.choose_spec.choose_spec.choose_spec.choose_spec.symm

private lemma preimageTransitionMap_w (X : C) (y : d.pt.val.obj ⟨X⟩)
    (n : ℕ) : (F.map (homOfLE (n.le_add_right 1)).op).val.app ⟨(preimage f hF X y (n+1)).obj⟩
      (preimage f hF X y (n+1)).element =
        ((F.obj ⟨n⟩).val.map (preimageTransitionMap f hF X y n).op)
          (preimage f hF X y n).element := by
  have := (preimageAux f hF X y (n + 1)).effectiveEpi
  have := Preregular.exists_fac (preimage f hF X y n).map (preimageAux f hF X y (n + 1)).map
  have h := (preimage f hF X y (n + 1)).w
  have h' := (preimage f hF X y n).w
  sorry


private noncomputable def preimageDiagram (X : C) (y : d.pt.val.obj ⟨X⟩) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun n ↦ (preimage f hF X y n).1)
    fun n ↦ preimageTransitionMap f hF X y n

variable [HasLimitsOfShape ℕᵒᵖ C]

private noncomputable def auxCone (X : C) (y : d.pt.val.obj ⟨X⟩) : Cone F where
  pt := ((coherentTopology C).yoneda).obj (limit (preimageDiagram f hF X y))
  π := NatTrans.ofOpSequence
    (fun n ↦ (coherentTopology C).yoneda.map
      (limit.π _ ⟨n⟩) ≫ ((coherentTopology C).yonedaEquiv).symm (preimage f hF X y n).element) (by
    intro n
    simp only [Functor.const_obj_obj, homOfLE_leOfHom, Functor.const_obj_map, Category.id_comp,
      Category.assoc]
    rw [← limit.w (preimageDiagram f hF X y) (homOfLE (n.le_add_right 1)).op]
    simp only [homOfLE_leOfHom, Functor.map_comp, Category.assoc]
    rw [GrothendieckTopology.yonedaEquiv_symm_naturality_left,
      GrothendieckTopology.yonedaEquiv_symm_naturality_right]
    simp [preimageDiagram]
    congr
    -- congr 1
    -- ext ⟨X⟩ x
    -- simp only [GrothendieckTopology.yoneda_obj_val, GrothendieckTopology.yonedaEquiv_symm_app_apply,
    --   homOfLE_leOfHom]
    have := (F.map ((homOfLE (n.le_add_right 1))).op).val.naturality
    sorry
    )

-- private noncomputable def auxCone (X : C) (y : d.pt.val.obj ⟨X⟩) : Cone F where
--   pt := ((coherentTopology C).yoneda).obj (limit (preimageDiagram f hF X y))
--   π := NatTrans.ofOpSequence
--     (fun n ↦ (coherentTopology C).yoneda.map
--       (limit.π _ ⟨n⟩) ≫ ((coherentTopology C).yonedaEquiv).symm (preimage f hF X y n).element) (by
--     intro n
--     simp only [Functor.const_obj_obj, homOfLE_leOfHom, Functor.const_obj_map, Category.id_comp,
--       Category.assoc]
--     rw [← limit.w (preimageDiagram f hF X y) (homOfLE (n.le_add_right 1)).op]
--     simp only [homOfLE_leOfHom, Functor.map_comp, Category.assoc]
--     rw [GrothendieckTopology.yonedaEquiv_symm_naturality_left,
--       GrothendieckTopology.yonedaEquiv_symm_naturality_right]
--     simp [preimageDiagram, ← preimageTransitionMap_w f hF X y n])

variable [ConcreteCategory C] (h : ∀ {X Y : C} (f : X ⟶ Y), EffectiveEpi f ↔ Function.Surjective f)

variable [PreservesLimitsOfShape ℕᵒᵖ (forget C)]

include hF h hc in
lemma isLocallySurjective_π_app_zero_of_isLocallySurjective_map :
    Sheaf.IsLocallySurjective (hd.map c f) := by
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff]
  intro X y
  have hh : EffectiveEpi (limit.π (preimageDiagram f hF X y) ⟨0⟩) := by
    rw [h]
    refine Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit _) fun n ↦ ?_
    simpa [preimageDiagram, ← h] using preimageTransitionMap_effectiveEpi f hF X y n
  have := (preimage f hF X y 0).effectiveEpi
  refine ⟨limit (preimageDiagram f hF X y),
      limit.π (preimageDiagram f hF X y) ⟨0⟩ ≫ (preimage f hF X y 0).map, inferInstance,
      ?_, ?_⟩
  · change c.pt.val.obj _
    apply (coherentTopology C).yonedaEquiv.toFun
    sorry
  · sorry

include h in
lemma epi_π_app_zero_of_epi [HasSheafify (coherentTopology C) (Type v)]
    [Balanced (Sheaf (coherentTopology C) (Type v))]
    [(coherentTopology C).WEqualsLocallyBijective (Type v)]
    {F : ℕᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)}
    {c : Cone F} (hc : IsLimit c)
    (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op)) : Epi (c.π.app ⟨0⟩) := by
  simp_rw [← Sheaf.isLocallySurjective_iff_epi'] at hF ⊢
  sorry--exact isLocallySurjective_π_app_zero_of_isLocallySurjective_map hc hF h

-- private lemma preimage_w (X : C) (y : d.pt.val.obj ⟨X⟩) (n : ℕ) :
--     True := sorry

-- private noncomputable def preimageTransitionMap (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) (n : ℕ) :
--     (preimage hF X y (n + 1)).1 ⟶ (preimage hF X y n).1 := by
--   have := hF n
--   rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
--   specialize this (preimage hF X y n).1 (preimage hF X y n).2
--   exact this.choose_spec.choose

-- private lemma preimageTransitionMap_effectiveEpi (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) (n : ℕ) :
--     EffectiveEpi (preimageTransitionMap hF X y n) := by
--   have := hF n
--   rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
--   specialize this (preimage hF X y n).1 (preimage hF X y n).2
--   exact this.choose_spec.choose_spec.choose

-- private lemma preimage_w (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) (n : ℕ) :
--     (F.map (homOfLE (n.le_add_right 1)).op).val.app ⟨(preimage hF X y (n+1)).1⟩
--       (preimage hF X y (n+1)).2 = ((F.obj ⟨n⟩).val.map (preimageTransitionMap hF X y n).op)
--         (preimage hF X y n).2 := by
--   have := hF n
--   rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
--   specialize this (preimage hF X y n).1 (preimage hF X y n).2
--   exact this.choose_spec.choose_spec.choose_spec.choose_spec

-- private noncomputable def preimageDiagram (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) : ℕᵒᵖ ⥤ C :=
--   Functor.ofOpSequence (X := fun n ↦ (preimage hF X y n).1)
--     fun n ↦ preimageTransitionMap hF X y n

end Maps

end Maps

open TransitionMaps

variable {F : ℕᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)} {c : Cone F}
    (hc : IsLimit c)
    (hF : ∀ n, Sheaf.IsLocallySurjective (F.map (homOfLE (Nat.le_succ n)).op))

variable [HasLimitsOfShape ℕᵒᵖ C]

private noncomputable def auxCone (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) : Cone F where
  pt := ((coherentTopology C).yoneda).obj (limit (preimageDiagram hF X y))
  π := NatTrans.ofOpSequence
    (fun n ↦ (coherentTopology C).yoneda.map
      (limit.π _ ⟨n⟩) ≫ ((coherentTopology C).yonedaEquiv).symm (preimage hF X y n).2) (by
    intro n
    simp only [Functor.const_obj_obj, homOfLE_leOfHom, Functor.const_obj_map, Category.id_comp,
      Category.assoc, ← limit.w (preimageDiagram hF X y) (homOfLE (n.le_add_right 1)).op,
      Nat.succ_eq_add_one, homOfLE_leOfHom, Functor.map_comp]
    rw [GrothendieckTopology.yonedaEquiv_symm_naturality_left,
      GrothendieckTopology.yonedaEquiv_symm_naturality_right]
    erw [preimage_w hF X y n]
    simp [preimageDiagram] )

variable [ConcreteCategory C] (h : ∀ {X Y : C} (f : X ⟶ Y), EffectiveEpi f ↔ Function.Surjective f)

variable [PreservesLimitsOfShape ℕᵒᵖ (forget C)]

include hF h hc in
lemma isLocallySurjective_π_app_zero_of_isLocallySurjective_map :
    Sheaf.IsLocallySurjective (c.π.app ⟨0⟩) := by
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff]
  intro X y
  have hh : EffectiveEpi (limit.π (preimageDiagram hF X y) ⟨0⟩) := by
    rw [h]
    refine Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit _) fun n ↦ ?_
    simpa [preimageDiagram, ← h] using preimageTransitionMap_effectiveEpi hF X y n
  refine ⟨limit (preimageDiagram hF X y), limit.π (preimageDiagram hF X y) ⟨0⟩, hh,
    (coherentTopology C).yonedaEquiv (hc.lift (auxCone hF X y )),
    (?_ : (c.π.app (op 0)).val.app _ _ = _)⟩
  simp only [← (coherentTopology C).yonedaEquiv_comp, Functor.const_obj_obj, auxCone,
    IsLimit.fac, NatTrans.ofOpSequence_app, (coherentTopology C).yonedaEquiv_comp,
    (coherentTopology C).yonedaEquiv_yoneda_map]
  rfl

include h in
lemma epi_π_app_zero_of_epi [HasSheafify (coherentTopology C) (Type v)]
    [Balanced (Sheaf (coherentTopology C) (Type v))]
    [(coherentTopology C).WEqualsLocallyBijective (Type v)]
    {F : ℕᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)}
    {c : Cone F} (hc : IsLimit c)
    (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op)) : Epi (c.π.app ⟨0⟩) := by
  simp_rw [← Sheaf.isLocallySurjective_iff_epi'] at hF ⊢
  exact isLocallySurjective_π_app_zero_of_isLocallySurjective_map hc hF h

end CategoryTheory.coherentTopology
