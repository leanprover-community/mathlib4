/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Topology.Category.LightProfinite.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.ClopenBox
/-!
# Being light is a property of profinite spaces

We define a class `Profinite.IsLight` which says that a profinite space `S` has countably many
clopen subsets. We prove that a profinite space which `IsLight` gives rise to a `LightProfinite` and
that the underlying profinite space of a `LightProfinite` is light.

## Main results

* `IsLight` is preserved under taking cartesian products

* Given a monomorphism whose target `IsLight`, its sourse is also light: `Profinite.isLight_of_mono`

## Project

* Prove the Stone duality theorem that `Profinite` is equivalent to the opposite category of
  boolean algebras. Then the property of being light says precisely that the corresponding
  boolean algebra is countable. Maybe constructions of limits and colimits in `LightProfinite`
<<<<<<< HEAD
  becomes easier when transporting over this equivalence.
=======
  become easier when transporting over this equivalence.
>>>>>>> d1d17722b8 (feat(LightProfinite): being light is a property of a profinite space (#10391))

-/

universe u

open CategoryTheory Limits FintypeCat Opposite TopologicalSpace

open scoped Classical

<<<<<<< HEAD
/-- A profinite space *is light* if it has countably many clopen subsets.  -/
class Profinite.IsLight (S : Profinite) : Prop where
=======
namespace Profinite

/-- A profinite space *is light* if it has countably many clopen subsets.  -/
class IsLight (S : Profinite) : Prop where
>>>>>>> d1d17722b8 (feat(LightProfinite): being light is a property of a profinite space (#10391))
  /-- The set of clopens is countable -/
  countable_clopens : Countable (Clopens S)

attribute [instance] Profinite.IsLight.countable_clopens

<<<<<<< HEAD
instance (X Y : Profinite) [X.IsLight] [Y.IsLight] : (Profinite.of (X × Y)).IsLight where
  countable_clopens := Clopens.countable_prod

instance (S : Profinite) [S.IsLight] : Countable (DiscreteQuotient S) := by
  refine @Function.Surjective.countable ({t : Finset (Clopens S) //
    (∀ (i j : (Clopens S)), i ∈ t → j ∈ t → i ≠ j → i.1 ∩ j.1 = ∅) ∧
    ∀ (x : S), ∃ i, i ∈ t ∧ x ∈ i.1}) _ _ ?_ ?_
  · intro t
    refine ⟨⟨fun x y ↦ ∃ i, i ∈ t.val ∧ x ∈ i.1 ∧ y ∈ i.1, ⟨by simpa using t.prop.2,
      fun ⟨i, h⟩ ↦ ⟨i, ⟨h.1, h.2.2, h.2.1⟩⟩, ?_⟩⟩, ?_⟩
    · intro x y z ⟨ixy, hxy⟩ ⟨iyz, hyz⟩
      refine ⟨ixy, hxy.1, hxy.2.1, ?_⟩
      convert hyz.2.2
      by_contra h
      have hh := t.prop.1 ixy iyz hxy.1 hyz.1 h
      apply Set.not_mem_empty y
      rw [← hh]
      exact ⟨hxy.2.2, hyz.2.1⟩
    · intro x
      simp only [setOf, Setoid.Rel]
      obtain ⟨i, h⟩ := t.prop.2 x
      convert i.2.1 with z
      refine ⟨fun ⟨j, hh⟩ ↦ ?_, fun hh ↦ ?_⟩
      · suffices i = j by rw [this]; exact hh.2.2
        by_contra hhh
        have hhhh := t.prop.1 i j h.1 hh.1 hhh
        apply Set.not_mem_empty x
        rw [← hhhh]
        exact ⟨h.2, hh.2.1⟩
      · exact ⟨i, h.1, h.2, hh⟩
  · intro d
    have : Fintype d := Fintype.ofFinite _
    refine ⟨⟨(Set.range (fun x ↦ ⟨d.proj ⁻¹' {x}, d.isClopen_preimage _⟩)).toFinset, ?_, ?_⟩, ?_⟩
    · intro i j hi hj hij
      simp only [Set.toFinset_range, Finset.mem_image, Finset.mem_univ, true_and] at hi hj
      obtain ⟨ai, hi⟩ := hi
      obtain ⟨aj, hj⟩ := hj
      rw [← hi, ← hj]
      dsimp
      ext x
      refine ⟨fun ⟨hhi, hhj⟩ ↦ ?_, fun h ↦ by simp at h⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hhi hhj
      exfalso
      apply hij
      rw [← hi, ← hj, ← hhi, ← hhj]
    · intro x
      refine ⟨⟨d.proj ⁻¹' {d.proj x}, d.isClopen_preimage _⟩, ?_⟩
      simp
    · ext x y
      simp only [DiscreteQuotient.proj, Set.toFinset_range, Finset.mem_image, Finset.mem_univ,
        true_and, exists_exists_eq_and, Set.mem_preimage, Set.mem_singleton_iff, exists_eq_left',
        Quotient.eq'']
      exact ⟨d.iseqv.symm , d.iseqv.symm⟩
=======
instance instIsLightProd (X Y : Profinite) [X.IsLight] [Y.IsLight] :
    (Profinite.of (X × Y)).IsLight where
  countable_clopens := Clopens.countable_prod

instance instCountableDiscreteQuotientOfIsLight (S : Profinite) [S.IsLight] :
    Countable (DiscreteQuotient S) := (DiscreteQuotient.finsetClopens_inj S).countable

end Profinite
>>>>>>> d1d17722b8 (feat(LightProfinite): being light is a property of a profinite space (#10391))

namespace LightProfinite

/-- A profinite space which is light gives rise to a light profinite space. -/
noncomputable def ofIsLight (S : Profinite.{u}) [S.IsLight] : LightProfinite.{u} where
  diagram := sequentialFunctor _ ⋙ S.fintypeDiagram
  cone := (Functor.Initial.limitConeComp (sequentialFunctor _) S.lim).cone
  isLimit := (Functor.Initial.limitConeComp (sequentialFunctor _) S.lim).isLimit

instance (S : LightProfinite.{u}) : S.toProfinite.IsLight where
  countable_clopens := by
<<<<<<< HEAD
    refine @Countable.of_equiv _ _ ?_
      ((LocallyConstant.equivClopens (X := S.toProfinite)).trans Clopens.equivSubtype.symm)
=======
    refine @Countable.of_equiv _ _ ?_ (LocallyConstant.equivClopens (X := S.toProfinite))
>>>>>>> d1d17722b8 (feat(LightProfinite): being light is a property of a profinite space (#10391))
    refine @Function.Surjective.countable
      (Σ (n : ℕ), LocallyConstant ((S.diagram ⋙ FintypeCat.toProfinite).obj ⟨n⟩) (Fin 2)) _ ?_ ?_ ?_
    · apply @instCountableSigma _ _ _ ?_
      intro n
      refine @Finite.to_countable _ ?_
      refine @Finite.of_injective _ ((S.diagram ⋙ FintypeCat.toProfinite).obj ⟨n⟩ → (Fin 2)) ?_ _
        LocallyConstant.coe_injective
      refine @Pi.finite _ _ ?_ _
      simp only [Functor.comp_obj, toProfinite_obj_toCompHaus_toTop_α]
      infer_instance
    · exact fun a ↦ a.snd.comap (S.cone.π.app ⟨a.fst⟩).1
    · intro a
      obtain ⟨n, g, h⟩ := Profinite.exists_locallyConstant S.cone S.isLimit a
      exact ⟨⟨unop n, g⟩, h.symm⟩

instance (S : LightProfinite.{u}) : (lightToProfinite.obj S).IsLight :=
  (inferInstance : S.toProfinite.IsLight)

end LightProfinite

section Mono
/-!
Given a monomorphism `f : X ⟶ Y` in `Profinite`, such that `Y.IsLight`, we want to prove that
`X.IsLight`. We do this by regarding `Y` as a `LightProfinite`, and constructing a `LightProfinite`
with `X` as its underlying `Profinite`. The diagram is just the image of `f` in the diagram of `Y`.
-/

namespace Profinite

variable {X : Profinite} {Y : LightProfinite} (f : X ⟶ Y.toProfinite)

/-- The image of `f` in the diagram of `Y` -/
noncomputable def lightProfiniteDiagramOfHom :
    ℕᵒᵖ ⥤ FintypeCat where
  obj := fun n ↦ FintypeCat.of (Set.range (f ≫ Y.cone.π.app n) : Set (Y.diagram.obj n))
  map := fun h ⟨x, hx⟩ ↦ ⟨Y.diagram.map h x, (by
    obtain ⟨y, hx⟩ := hx
    rw [← hx]
    use y
    have := Y.cone.π.naturality h
    simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map, Category.id_comp,
      Functor.comp_map] at this
    rw [this]
    rfl )⟩
  map_id := by -- `aesop` can handle it but is a bit slow
    intro
    simp only [Functor.comp_obj, id_eq, Functor.const_obj_obj, Functor.const_obj_map,
      Functor.comp_map, eq_mp_eq_cast, cast_eq, eq_mpr_eq_cast, CategoryTheory.Functor.map_id,
      FintypeCat.id_apply]
    rfl
  map_comp := by -- `aesop` can handle it but is a bit slow
    intros
    simp only [Functor.comp_obj, id_eq, Functor.const_obj_obj, Functor.const_obj_map,
      Functor.comp_map, eq_mp_eq_cast, cast_eq, eq_mpr_eq_cast, Functor.map_comp,
      FintypeCat.comp_apply]
    rfl

/-- An auxiliary definition to prove continuity in `lightProfiniteConeOfHom_π_app`. -/
def lightProfiniteConeOfHom_π_app' (n : ℕᵒᵖ) :
    C(X, Set.range (f ≫ Y.cone.π.app n)) where
  toFun := fun x ↦ ⟨Y.cone.π.app n (f x), ⟨x, rfl⟩⟩
  continuous_toFun := Continuous.subtype_mk ((Y.cone.π.app n).continuous.comp f.continuous) _

/-- An auxiliary definition for `lightProfiniteConeOfHom`. -/
def lightProfiniteConeOfHom_π_app (n : ℕᵒᵖ) :
    X ⟶ (lightProfiniteDiagramOfHom f ⋙ FintypeCat.toProfinite).obj n where
  toFun x := ⟨Y.cone.π.app n (f x), ⟨x, rfl⟩⟩
  continuous_toFun := by
    convert (lightProfiniteConeOfHom_π_app' f n).continuous_toFun
    change ⊥ = _
    ext U
    rw [isOpen_induced_iff]
    have := discreteTopology_bot
    refine ⟨fun _ ↦ ⟨Subtype.val '' U, isOpen_discrete _,
      Function.Injective.preimage_image Subtype.val_injective _⟩, fun _ ↦ isOpen_discrete U⟩
    -- This is annoying

/-- The cone on `lightProfiniteDiagramOfHom` -/
def lightProfiniteConeOfHom :
<<<<<<< HEAD
    Cone ((lightProfiniteDiagramOfHom f) ⋙ FintypeCat.toProfinite) where
=======
    Cone (lightProfiniteDiagramOfHom f ⋙ FintypeCat.toProfinite) where
>>>>>>> d1d17722b8 (feat(LightProfinite): being light is a property of a profinite space (#10391))
  pt := X
  π := {
    app := fun n ↦ lightProfiniteConeOfHom_π_app f n
    naturality := by
      intro n m h
      have := Y.cone.π.naturality h
      simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map, Category.id_comp,
        Functor.comp_map] at this
      simp only [Functor.comp_obj, toProfinite_obj_toCompHaus_toTop_α, Functor.const_obj_obj,
        Functor.const_obj_map, lightProfiniteConeOfHom_π_app, this, CategoryTheory.comp_apply,
        Category.id_comp, Functor.comp_map]
      rfl }

instance [Mono f] : IsIso ((Profinite.limitConeIsLimit ((lightProfiniteDiagramOfHom f) ⋙
    FintypeCat.toProfinite)).lift (lightProfiniteConeOfHom f)) := by
  apply Profinite.isIso_of_bijective
  refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
  · have hf : Function.Injective f := by rwa [← Profinite.mono_iff_injective]
    suffices f a = f b by exact hf this
    apply LightProfinite.ext
    intro n
    apply_fun fun f : (Profinite.limitCone ((lightProfiniteDiagramOfHom f) ⋙
      FintypeCat.toProfinite)).pt ↦ f.val n at h
    erw [ContinuousMap.coe_mk, Subtype.ext_iff] at h
    exact h
<<<<<<< HEAD
  · suffices : ∃ x, ∀ n, lightProfiniteConeOfHom_π_app f (op n) x = a.val (op n)
    · obtain ⟨x, h⟩ := this
=======
  · suffices ∃ x, ∀ n, lightProfiniteConeOfHom_π_app f (op n) x = a.val (op n) by
      obtain ⟨x, h⟩ := this
>>>>>>> d1d17722b8 (feat(LightProfinite): being light is a property of a profinite space (#10391))
      use x
      apply Subtype.ext
      apply funext
      intro n
      exact h (unop n)
<<<<<<< HEAD
    have : Set.Nonempty (⋂ (n : ℕ), (lightProfiniteConeOfHom_π_app f (op n)) ⁻¹' {a.val (op n)})
    · refine IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed
=======
    have : Set.Nonempty
        (⋂ (n : ℕ), (lightProfiniteConeOfHom_π_app f (op n)) ⁻¹' {a.val (op n)}) := by
      refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
>>>>>>> d1d17722b8 (feat(LightProfinite): being light is a property of a profinite space (#10391))
        (fun n ↦ (lightProfiniteConeOfHom_π_app f (op n)) ⁻¹' {a.val (op n)})
          (directed_of_isDirected_le ?_)
        (fun _ ↦ (Set.singleton_nonempty _).preimage fun ⟨a, ⟨b, hb⟩⟩ ↦ ⟨b, Subtype.ext hb⟩)
        (fun _ ↦ (IsClosed.preimage (lightProfiniteConeOfHom_π_app _ _).continuous
          (T1Space.t1 _)).isCompact)
        (fun _ ↦ IsClosed.preimage (lightProfiniteConeOfHom_π_app _ _).continuous (T1Space.t1 _))
      intro i j h x hx
      simp only [Functor.comp_obj, profiniteToCompHaus_obj, compHausToTop_obj,
        toProfinite_obj_toCompHaus_toTop_α, Functor.comp_map, profiniteToCompHaus_map,
        compHausToTop_map, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      have := (lightProfiniteConeOfHom f).π.naturality (homOfLE h).op
      simp only [lightProfiniteConeOfHom, Functor.const_obj_obj, Functor.comp_obj,
        Functor.const_obj_map, Category.id_comp, Functor.comp_map] at this
      rw [this]
      simp only [CategoryTheory.comp_apply]
      rw [hx, ← a.prop (homOfLE h).op]
      rfl
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Set.mem_iInter.1 hx⟩


/-- When `f` is a monomorphism the cone `lightProfiniteConeOfHom` is limiting. -/
noncomputable
def lightProfiniteIsLimitOfMono [Mono f] : IsLimit (lightProfiniteConeOfHom f) :=
  Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _)
    (Limits.Cones.ext (asIso ((Profinite.limitConeIsLimit ((lightProfiniteDiagramOfHom f) ⋙
      FintypeCat.toProfinite)).lift (lightProfiniteConeOfHom f))) fun _ => rfl).symm

/--
Putting together all of the above, we get a `LightProfinite` whose underlying `Profinite` is `X`
-/
noncomputable def lightProfiniteOfMono [Mono f] : LightProfinite :=
  ⟨lightProfiniteDiagramOfHom f, lightProfiniteConeOfHom f, lightProfiniteIsLimitOfMono f⟩

/-- `lightProfiniteOfMono` phrased in terms of `Profinite.IsLight`. -/
theorem isLight_of_mono {X Y : Profinite} [Y.IsLight] (f : X ⟶ Y) [Mono f] : X.IsLight := by
  change (lightProfiniteOfMono (Y := LightProfinite.ofIsLight Y) f).toProfinite.IsLight
  infer_instance

end Profinite

end Mono
