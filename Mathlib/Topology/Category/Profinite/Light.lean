import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Sites.RegularExtensive
import Mathlib.CategoryTheory.Sites.Sheafification

universe u

open CategoryTheory Limits FintypeCat Opposite

structure LightProfinite : Type (u+1) where
  diagram : ℕᵒᵖ ⥤ FintypeCat
  cone : Cone (diagram ⋙ toProfinite.{u})
  isLimit : IsLimit cone

def FintypeCat.toLightProfinite (X : FintypeCat) : LightProfinite where
  diagram := (Functor.const _).obj X
  cone := {
    pt := toProfinite.obj X
    π := eqToHom rfl }
  isLimit := {
    lift := fun s ↦ s.π.app ⟨0⟩
    fac := fun s j ↦ (s.π.naturality (homOfLE (zero_le (unop j))).op)
    uniq := fun _ _ h ↦  h ⟨0⟩ }

noncomputable
def LightProfinite.of (F : ℕᵒᵖ ⥤ FintypeCat) : LightProfinite where
  diagram := F
  isLimit := limit.isLimit (F ⋙ FintypeCat.toProfinite)

class Profinite.IsLight (S : Profinite) : Prop where
  countable_clopens : Countable {s : Set S // IsClopen s}

def clopensEquiv (S : Profinite) : {s : Set S // IsClopen s} ≃ LocallyConstant S (Fin 2) :=
  sorry

attribute [instance] Profinite.IsLight.countable_clopens

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

instance (S : Profinite) : IsCofiltered (DiscreteQuotient S) := inferInstance

noncomputable
def cofinal_sequence (S : Profinite) [S.IsLight] : ℕ → DiscreteQuotient S := fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsCofiltered.toIsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (cofinal_sequence S n)).choose

noncomputable
def cofinal_sequence' (S : Profinite) [S.IsLight] : ℕ → DiscreteQuotient S := fun n ↦ by
  induction n with
  | zero => exact (exists_surjective_nat _).choose 0
  | succ n D => exact
      (IsCofiltered.toIsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n) D).choose

theorem antitone_cofinal_sequence (S : Profinite) [S.IsLight] : Antitone (cofinal_sequence S) :=
  antitone_nat_of_succ_le fun n ↦
    leOfHom (IsCofiltered.toIsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (cofinal_sequence S n)).choose_spec.choose_spec.choose

theorem cofinal_cofinal_sequence (S : Profinite) [S.IsLight] :
    ∀ d, ∃ n, cofinal_sequence S n ≤ d := by
  intro d
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec d
  refine ⟨m + 1, ?_⟩
  rw [← h]
  exact leOfHom (IsCofiltered.toIsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose m)
      (cofinal_sequence S m)).choose_spec.choose

@[simps]
noncomputable def initial_functor (S : Profinite) [S.IsLight] : ℕᵒᵖ ⥤ DiscreteQuotient S where
  obj n := cofinal_sequence S (unop n)
  map h := homOfLE (antitone_cofinal_sequence S (leOfHom h.unop))

instance initial_functor_initial (S : Profinite) [S.IsLight] : (initial_functor S).Initial where
  out d := by
    obtain ⟨n, h⟩ := cofinal_cofinal_sequence S d
    let g : (initial_functor S).obj ⟨n⟩ ⟶ d := eqToHom (by simp) ≫ homOfLE h
    have : Nonempty (CostructuredArrow (initial_functor S) d) := ⟨CostructuredArrow.mk g⟩
    apply isConnected_of_zigzag
    intro i j
    refine ⟨[i, j], ?_⟩
    simp only [List.chain_cons, Zag, or_self, List.Chain.nil, and_true, ne_eq, not_false_eq_true,
      List.getLast_cons, not_true_eq_false, List.getLast_singleton']
    refine ⟨⟨𝟙 _⟩, ?_⟩
    by_cases hnm : unop i.1 ≤ unop j.1
    · right
      refine ⟨CostructuredArrow.homMk (homOfLE hnm).op rfl⟩
    · left
      simp only [not_le] at hnm
      refine ⟨CostructuredArrow.homMk (homOfLE (le_of_lt hnm)).op rfl⟩

namespace LightProfinite

def toProfinite (S : LightProfinite) : Profinite := S.cone.pt

noncomputable
def ofIsLight (S : Profinite) [S.IsLight] : LightProfinite where
  diagram := initial_functor S ⋙ S.fintypeDiagram
  cone := (Functor.Initial.limitConeComp (initial_functor S) S.lim).cone
  isLimit := (Functor.Initial.limitConeComp (initial_functor S) S.lim).isLimit

instance (S : LightProfinite) : S.toProfinite.IsLight where
  countable_clopens := by
    refine @Countable.of_equiv _ _ ?_ (clopensEquiv S.toProfinite).symm
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

@[simps!]
instance : Category LightProfinite := InducedCategory.category toProfinite

@[simps!]
instance concreteCategory : ConcreteCategory LightProfinite := InducedCategory.concreteCategory _

@[simps!]
def lightToProfinite : LightProfinite ⥤ Profinite := inducedFunctor _

instance : Faithful lightToProfinite := show Faithful <| inducedFunctor _ from inferInstance

instance : Full lightToProfinite := show Full <| inducedFunctor _ from inferInstance

instance : lightToProfinite.ReflectsEpimorphisms := inferInstance

instance {X : LightProfinite} : TopologicalSpace ((forget LightProfinite).obj X) :=
  (inferInstance : TopologicalSpace X.cone.pt)

instance {X : LightProfinite} : TotallyDisconnectedSpace ((forget LightProfinite).obj X) :=
  (inferInstance : TotallyDisconnectedSpace X.cone.pt)

instance {X : LightProfinite} : CompactSpace ((forget LightProfinite).obj X) :=
  (inferInstance : CompactSpace X.cone.pt )

instance {X : LightProfinite} : T2Space ((forget LightProfinite).obj X) :=
  (inferInstance : T2Space X.cone.pt )

def fintypeCatToLightProfinite : FintypeCat ⥤ LightProfinite where
  obj X := X.toLightProfinite
  map f := FintypeCat.toProfinite.map f

noncomputable
def EffectiveEpi.struct {B X : LightProfinite.{u}} (π : X ⟶ B) (hπ : Function.Surjective π) :
    EffectiveEpiStruct π where
  desc e h := (QuotientMap.of_surjective_continuous hπ π.continuous).lift e fun a b hab ↦
    FunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a
  fac e h := ((QuotientMap.of_surjective_continuous hπ π.continuous).lift_comp e
    fun a b hab ↦ FunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a)
  uniq e h g hm := by
    suffices g = (QuotientMap.of_surjective_continuous hπ π.continuous).liftEquiv ⟨e,
      fun a b hab ↦ FunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
      (by ext; exact hab)) a⟩ by assumption
    rw [← Equiv.symm_apply_eq (QuotientMap.of_surjective_continuous hπ π.continuous).liftEquiv]
    ext
    simp only [QuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl

theorem epi_iff_surjective {X Y : LightProfinite.{u}} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.continuous).isClosed
    let U := Cᶜ
    have hyU : y ∈ U := by
      refine' Set.mem_compl _
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ nhds y := hC.compl_mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_clopen.mem_nhds_iff.mp hUy
    classical
      let Z := (FintypeCat.of (ULift.{u} <| Fin 2)).toLightProfinite
      let g : Y ⟶ Z := ⟨(LocallyConstant.ofClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        apply ULift.ext
        dsimp [LocallyConstant.ofClopen]
        erw [LightProfinite.instCategoryLightProfinite_comp_apply, ContinuousMap.coe_mk,
          LightProfinite.instCategoryLightProfinite_comp_apply, ContinuousMap.coe_mk,
          Function.comp_apply, if_neg]
        refine' mt (fun α => hVU α) _
        simp only [concreteCategory_forget_obj, Set.mem_compl_iff, Set.mem_range, not_exists,
          not_forall, not_not]
        exact ⟨x, rfl⟩
      apply_fun fun e => (e y).down at H
      dsimp [LocallyConstant.ofClopen] at H
      erw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Function.comp_apply, if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget LightProfinite).epi_of_epi_map

theorem effectiveEpi_iff_surjective {X Y : LightProfinite.{u}} (f : X ⟶ Y) :
    EffectiveEpi f ↔ Function.Surjective f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨EffectiveEpi.struct f h⟩⟩⟩
  rw [← epi_iff_surjective]
  infer_instance

instance : Preregular LightProfinite := sorry

instance : FinitaryExtensive LightProfinite := sorry

end LightProfinite

structure LightProfinite' : Type u where
  diagram : ℕᵒᵖ ⥤ FintypeCat.Skeleton.{u}

namespace LightProfinite'

noncomputable section

def toProfinite (S : LightProfinite') : Profinite :=
  limit (S.diagram  ⋙ FintypeCat.Skeleton.equivalence.functor ⋙ FintypeCat.toProfinite.{u})

instance : Category LightProfinite' := InducedCategory.category toProfinite

instance : SmallCategory LightProfinite' := inferInstance

instance concreteCategory : ConcreteCategory LightProfinite' := InducedCategory.concreteCategory _

@[simps!]
def lightToProfinite' : LightProfinite' ⥤ Profinite := inducedFunctor _

instance : Faithful lightToProfinite' := show Faithful <| inducedFunctor _ from inferInstance

instance : Full lightToProfinite' := show Full <| inducedFunctor _ from inferInstance

end

end LightProfinite'

noncomputable section Equivalence

def smallToLight : LightProfinite' ⥤ LightProfinite where
  obj X := ⟨X.diagram ⋙ Skeleton.equivalence.functor, _, limit.isLimit _⟩
  map f := f

instance : Faithful smallToLight := ⟨id⟩

instance : Full smallToLight := ⟨id, fun _ ↦ rfl⟩

instance : EssSurj smallToLight := by
  constructor
  intro Y
  let i : limit (((Y.diagram ⋙ Skeleton.equivalence.inverse) ⋙ Skeleton.equivalence.functor) ⋙
    toProfinite) ≅ Y.cone.pt := (Limits.lim.mapIso (isoWhiskerRight ((Functor.associator _ _ _) ≪≫
    (isoWhiskerLeft Y.diagram Skeleton.equivalence.counitIso)) toProfinite)) ≪≫
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) Y.isLimit
  exact ⟨⟨Y.diagram ⋙ Skeleton.equivalence.inverse⟩, ⟨⟨i.hom, i.inv, i.hom_inv_id, i.inv_hom_id⟩⟩⟩
  -- why can't I just write `i`?

instance : IsEquivalence smallToLight := Equivalence.ofFullyFaithfullyEssSurj _

def LightProfinite.equivSmall : LightProfinite ≌ LightProfinite' := smallToLight.asEquivalence.symm

instance : EssentiallySmall LightProfinite where
  equiv_smallCategory := ⟨LightProfinite', inferInstance, ⟨LightProfinite.equivSmall⟩⟩

end Equivalence


variable (P : LightProfinite.{0}ᵒᵖ ⥤ Type)

-- #check (coherentTopology LightProfinite.{0}).sheafify P (D := Type)
-- Doesn't work, need a universe bump because `LightProfinite` is large.

instance : Preregular LightProfinite' := sorry

instance : FinitaryExtensive LightProfinite' := sorry

variable (P : LightProfinite'.{0}ᵒᵖ ⥤ Type)

-- #check (coherentTopology LightProfinite'.{0}).sheafify P (D := Type)
-- Works because `LightProfinite'` is actually small.

-- TODO: provide API to sheafify over essentially small categories
