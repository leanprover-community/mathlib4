import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Topology.Category.LightProfinite.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.ClopenBox

universe u

open CategoryTheory Limits FintypeCat Opposite

class Profinite.IsLight (S : Profinite) : Prop where
  countable_clopens : Countable {s : Set S // IsClopen s}

attribute [instance] Profinite.IsLight.countable_clopens

instance (X Y : Profinite) [X.IsLight] [Y.IsLight] : (Profinite.of (X × Y)).IsLight where
  countable_clopens := countable_clopens_prod

open Classical in
noncomputable
def clopensEquiv (S : Profinite) : {s : Set S // IsClopen s} ≃ LocallyConstant S Bool where
  toFun s := {
    toFun := fun x ↦ decide (x ∈ s.val)
    isLocallyConstant := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro y
      cases y with
      | false => convert s.prop.compl.1; ext; simp
      | true => convert s.prop.1; ext; simp }
  invFun f := {
    val := f ⁻¹' {true}
    property := f.2.isClopen_fiber _ }
  left_inv s := by ext; simp
  right_inv f := by ext; simp

open Classical in
instance (S : Profinite) [S.IsLight] : Countable (DiscreteQuotient S) := by
  have : ∀ d : DiscreteQuotient S, Fintype d := fun d ↦ Fintype.ofFinite _
  refine @Function.Surjective.countable ({t : Finset {s : Set S // IsClopen s} //
    (∀ (i j : {s : Set S // IsClopen s}), i ∈ t → j ∈ t → i ≠ j → i.val ∩ j.val = ∅) ∧
    ∀ (x : S), ∃ i, i ∈ t ∧ x ∈ i.val}) _ _ ?_ ?_
  · intro t
    refine ⟨⟨fun x y ↦ ∃ i, i ∈ t.val ∧ x ∈ i.val ∧ y ∈ i.val, ⟨by simpa using t.prop.2,
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
      convert i.prop.1 with z
      refine ⟨fun ⟨j, hh⟩ ↦ ?_, fun hh ↦ ?_⟩
      · suffices i = j by rw [this]; exact hh.2.2
        by_contra hhh
        have hhhh := t.prop.1 i j h.1 hh.1 hhh
        apply Set.not_mem_empty x
        rw [← hhhh]
        exact ⟨h.2, hh.2.1⟩
      · exact ⟨i, h.1, h.2, hh⟩
  · intro d
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

namespace LightProfinite

noncomputable
def ofIsLight (S : Profinite.{u}) [S.IsLight] : LightProfinite.{u} where
  diagram := sequentialFunctor _ ⋙ S.fintypeDiagram
  cone := (Functor.Initial.limitConeComp (sequentialFunctor _) S.lim).cone
  isLimit := (Functor.Initial.limitConeComp (sequentialFunctor _) S.lim).isLimit

instance (S : LightProfinite.{u}) : S.toProfinite.IsLight where
  countable_clopens := by
    refine @Countable.of_equiv _ _ ?_ (clopensEquiv S.toProfinite).symm
    refine @Function.Surjective.countable
      (Σ (n : ℕ), LocallyConstant ((S.diagram ⋙ FintypeCat.toProfinite).obj ⟨n⟩) Bool) _ ?_ ?_ ?_
    · apply @instCountableSigma _ _ _ ?_
      intro n
      refine @Finite.to_countable _ ?_
      refine @Finite.of_injective _ ((S.diagram ⋙ FintypeCat.toProfinite).obj ⟨n⟩ → Bool) ?_ _
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

open Classical in
noncomputable def monoLight_diagram {X : Profinite} {Y : LightProfinite} (f : X ⟶ Y.toProfinite) :
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

attribute [local instance] FintypeCat.discreteTopology

def monoLight_cone_π_app' (n : ℕᵒᵖ) {X : Profinite} {Y : LightProfinite} (f : X ⟶ Y.toProfinite) :
    C(X, Set.range (f ≫ Y.cone.π.app n)) where
  toFun := fun x ↦ ⟨Y.cone.π.app n (f x), ⟨x, rfl⟩⟩
  continuous_toFun := Continuous.subtype_mk ((Y.cone.π.app n).continuous.comp f.continuous) _

def monoLight_cone_π_app (n : ℕᵒᵖ) {X : Profinite} {Y : LightProfinite} (f : X ⟶ Y.toProfinite) :
    X ⟶ (monoLight_diagram f ⋙ FintypeCat.toProfinite).obj n where
  toFun x := ⟨Y.cone.π.app n (f x), ⟨x, rfl⟩⟩
  continuous_toFun := by
    convert (monoLight_cone_π_app' n f).continuous_toFun
    change ⊥ = _
    ext U
    rw [isOpen_induced_iff]
    have := discreteTopology_bot
    refine ⟨fun _ ↦ ⟨Subtype.val '' U, isOpen_discrete _,
      Function.Injective.preimage_image Subtype.val_injective _⟩, fun _ ↦ isOpen_discrete U⟩
    -- This is annoying

def monoLight_cone {X : Profinite} {Y : LightProfinite.{u}} (f : X ⟶ Y.toProfinite) :
    Cone ((monoLight_diagram f) ⋙ FintypeCat.toProfinite) where
  pt := X
  π := {
    app := fun n ↦ monoLight_cone_π_app n f
    naturality := by
      intro n m h
      have := Y.cone.π.naturality h
      simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map, Category.id_comp,
        Functor.comp_map] at this
      simp only [Functor.comp_obj, toProfinite_obj_toCompHaus_toTop_α, Functor.const_obj_obj,
        Functor.const_obj_map, monoLight_cone_π_app, this, CategoryTheory.comp_apply,
        Category.id_comp, Functor.comp_map]
      rfl }

instance isIso_indexCone_lift {X : Profinite} {Y : LightProfinite.{u}} (f : X ⟶ Y.toProfinite)
    [Mono f] : IsIso ((Profinite.limitConeIsLimit ((monoLight_diagram f) ⋙
    FintypeCat.toProfinite)).lift (monoLight_cone f)) := by
  apply Profinite.isIso_of_bijective
  refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
  · have hf : Function.Injective f := by rwa [← Profinite.mono_iff_injective]
    suffices f a = f b by exact hf this
    apply LightProfinite.ext
    intro n
    apply_fun fun f : (Profinite.limitCone ((monoLight_diagram f) ⋙ FintypeCat.toProfinite)).pt =>
      f.val n at h
    erw [ContinuousMap.coe_mk, Subtype.ext_iff] at h
    exact h
  · suffices : ∃ x, ∀ n, monoLight_cone_π_app (op n) f x = a.val (op n)
    · obtain ⟨x, h⟩ := this
      use x
      apply Subtype.ext
      apply funext
      intro n
      exact h (unop n)
    have : Set.Nonempty (⋂ (n : ℕ), (monoLight_cone_π_app (op n) f) ⁻¹' {a.val (op n)})
    · refine IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed
        (fun n ↦ (monoLight_cone_π_app (op n) f) ⁻¹' {a.val (op n)}) (directed_of_isDirected_le ?_)
        (fun _ ↦ (Set.singleton_nonempty _).preimage fun ⟨a, ⟨b, hb⟩⟩ ↦ ⟨b, Subtype.ext hb⟩)
        (fun _ ↦ (IsClosed.preimage (monoLight_cone_π_app _ _).continuous (T1Space.t1 _)).isCompact)
        (fun _ ↦ IsClosed.preimage (monoLight_cone_π_app _ _).continuous (T1Space.t1 _))
      intro i j h x hx
      simp only [Functor.comp_obj, profiniteToCompHaus_obj, compHausToTop_obj,
        toProfinite_obj_toCompHaus_toTop_α, Functor.comp_map, profiniteToCompHaus_map,
        compHausToTop_map, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      have := (monoLight_cone f).π.naturality (homOfLE h).op
      simp only [monoLight_cone, Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map,
        Category.id_comp, Functor.comp_map] at this
      rw [this]
      simp only [CategoryTheory.comp_apply]
      rw [hx, ← a.prop (homOfLE h).op]
      rfl
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Set.mem_iInter.1 hx⟩


noncomputable
def monoLight_isLimit {X : Profinite} {Y : LightProfinite} (f : X ⟶ Y.toProfinite) [Mono f] :
    IsLimit (monoLight_cone f) := Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _)
    (Limits.Cones.ext (asIso ((Profinite.limitConeIsLimit ((monoLight_diagram f) ⋙
    FintypeCat.toProfinite)).lift (monoLight_cone f))) fun _ => rfl).symm

noncomputable
def mono_lightProfinite {X : Profinite} {Y : LightProfinite} (f : X ⟶ Y.toProfinite) [Mono f] :
    LightProfinite := ⟨monoLight_diagram f, monoLight_cone f, monoLight_isLimit f⟩

theorem mono_light {X Y : Profinite} [Y.IsLight] (f : X ⟶ Y) [Mono f] : X.IsLight := by
  let Y' : LightProfinite := ofIsLight Y
  change (mono_lightProfinite (Y := Y') f).toProfinite.IsLight
  infer_instance

end LightProfinite
