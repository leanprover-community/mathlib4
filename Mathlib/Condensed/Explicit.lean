import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Elementwise
import Mathlib.Topology.Category.Stonean.Limits

universe v v₁ u u₁ w

section isSheafForPullBackSieve

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

variable {C : Type u₁} [Category.{v₁} C]

variable {X : C} (S : Presieve X)

def isPullbackPresieve : Prop :=
  ∀ {Y Z} {f : Y ⟶ X} (_ : S f) {g : Z ⟶ X} (_ : S g),
  HasPullback f g

variable (P : Cᵒᵖ ⥤ Type max v₁ u₁)

variable (hS : isPullbackPresieve S) {S}
namespace Presieve

def FamilyOfElements.PullbackCompatible' (x : FamilyOfElements P S) : Prop :=
  ∀ ⦃Y₁ Y₂⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : S f₁) (h₂ : S f₂),
    have := hS h₁ h₂
    P.map (pullback.fst : Limits.pullback f₁ f₂ ⟶ _).op (x f₁ h₁) = P.map pullback.snd.op (x f₂ h₂)

theorem pullbackCompatible_iff' (x : FamilyOfElements P S) :
    x.Compatible ↔ x.PullbackCompatible' hS := by
  constructor
  · intro t Y₁ Y₂ f₁ f₂ hf₁ hf₂
    apply t
    have := hS hf₁ hf₂
    apply pullback.condition
  · intro t Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    have := hS hf₁ hf₂
    rw [← pullback.lift_fst _ _ comm, op_comp, FunctorToTypes.map_comp_apply, t hf₁ hf₂,
      ← FunctorToTypes.map_comp_apply, ← op_comp, pullback.lift_snd]

end Presieve

namespace Equalizer

namespace Presieve

/-- The rightmost object of the fork diagram of https://stacks.math.columbia.edu/tag/00VM, which
contains the data used to check a family of elements for a presieve is compatible.
-/
@[simp] def SecondObj' : Type max v₁ u₁ :=
  ∏ fun fg : (ΣY, { f : Y ⟶ X // S f }) × ΣZ, { g : Z ⟶ X // S g } =>
    have := hS fg.1.2.2 fg.2.2.2
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

/-- The map `pr₀*` of <https://stacks.math.columbia.edu/tag/00VL>. -/
noncomputable
def firstMap' : FirstObj P S ⟶ SecondObj' P hS :=
    Pi.lift fun fg =>
    have := hS fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map pullback.fst.op

/-- The map `pr₁*` of <https://stacks.math.columbia.edu/tag/00VL>. -/
noncomputable def secondMap' : FirstObj P S ⟶ SecondObj' P hS :=
  Pi.lift fun fg =>
    have := hS fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map pullback.snd.op

theorem w' : forkMap P S ≫ firstMap' P hS = forkMap P S ≫ secondMap' P hS := by
  dsimp
  ext fg
  simp only [firstMap', secondMap', forkMap]
  simp only [limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app]
  have := hS fg.1.2.2 fg.2.2.2
  rw [← P.map_comp, ← op_comp, pullback.condition]
  simp

/--
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap'` and `secondMap'`
map it to the same point.
-/
theorem compatible_iff' (x : FirstObj P S) :
    ((firstObjEqFamily P S).hom x).Compatible ↔ firstMap' P hS x = secondMap' P hS x := by
  rw [Presieve.pullbackCompatible_iff' _ hS]
  constructor
  . intro t
    apply Limits.Types.limit_ext
    rintro ⟨⟨Y, f, hf⟩, Z, g, hg⟩
    simpa [firstMap', secondMap'] using t hf hg
  · intro t Y Z f g hf hg
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap', secondMap'] using t ⟨⟨⟨Y, f, hf⟩, Z, g, hg⟩⟩

/-- `P` is a sheaf for `R`, iff the fork given by `w` is an equalizer.
See <https://stacks.math.columbia.edu/tag/00VM>.
-/
theorem sheaf_condition' : S.IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι _ (w' P hS))) := by
  rw [Types.type_equalizer_iff_unique]
  erw [← Equiv.forall_congr_left (firstObjEqFamily P S).toEquiv.symm]
  simp_rw [← compatible_iff', ← Iso.toEquiv_fun, Equiv.apply_symm_apply]
  apply ball_congr
  intro x _
  apply exists_unique_congr
  intro t
  rw [Equiv.eq_symm_apply]
  constructor
  · intro q
    funext Y f hf
    simpa [forkMap] using q _ _
  · intro q Y f hf
    rw [← q]
    simp [forkMap]

end Presieve

end Equalizer

end CategoryTheory

end isSheafForPullBackSieve

section ProdCoprod

open CategoryTheory Opposite Limits

section ProdToCoprod

variable {C : Type _} [Category C] {α : Type} [Finite α]
  (Z : α → C) [HasFiniteProducts C]

@[simps!]
noncomputable
def oppositeCofan : Cofan (fun z => op (Z z)) :=
  Cofan.mk (op <| ∏ Z) fun i => (Pi.π _ i).op

@[simps]
noncomputable
def isColimitOppositeCofan : IsColimit (oppositeCofan Z) where
  desc := fun S =>
    let e : S.pt.unop ⟶ ∏ Z := Pi.lift fun j => (S.ι.app _).unop
    e.op
  fac := fun S j => by
    dsimp only [oppositeCofan_pt, Functor.const_obj_obj,
      oppositeCofan_ι_app, Discrete.functor_obj]
    simp only [← op_comp, limit.lift_π,
      Fan.mk_pt, Fan.mk_π_app, Quiver.Hom.op_unop]
  uniq := fun S m hm => by
    rw [← m.op_unop]
    congr 1
    apply limit.hom_ext
    intro j
    simpa using congr_arg Quiver.Hom.unop (hm j)

@[simp]
noncomputable
def ProdToCoprod : op (∏ Z) ≅ ∐ (fun z => op (Z z)) :=
  isColimitOppositeCofan Z |>.coconePointUniqueUpToIso <| colimit.isColimit _

end ProdToCoprod

section CoprodToProd

variable {C : Type _} [Category C] {α : Type} [Finite α]
  (Z : α → C) [HasFiniteCoproducts C]

@[simps!]
noncomputable
def oppositeFan : Fan (fun z => op (Z z)) := by
  refine' Fan.mk (op <| ∐ Z) fun i => (Sigma.ι _ i).op

@[simps!]
noncomputable
def isLimitOppositeFan : IsLimit (oppositeFan Z) where
  lift := fun S =>
    let e : ∐ Z ⟶ S.pt.unop := Sigma.desc fun j => (S.π.app _).unop
    e.op
  fac := fun S j => by
    dsimp only [oppositeFan_pt, Functor.const_obj_obj,
      oppositeFan_π_app, Discrete.functor_obj]
    simp only [← op_comp, colimit.ι_desc,
      Cofan.mk_pt, Cofan.mk_ι_app, Quiver.Hom.op_unop]
  uniq := fun S m hm => by
    rw [← m.op_unop]
    congr 1
    apply colimit.hom_ext
    intro j
    simpa using congr_arg Quiver.Hom.unop (hm j)

@[simp]
noncomputable
def CoprodToProd : op (∐ Z) ≅ ∏ (fun z => op (Z z)) :=
  isLimitOppositeFan Z |>.conePointUniqueUpToIso <| limit.isLimit _

lemma CoprodToProdInvComp.ι (b : α) : ((CoprodToProd Z).inv ≫ (Sigma.ι (fun a => Z a) b).op) =
    Pi.π (fun a => op (Z a)) b :=
  IsLimit.conePointUniqueUpToIso_inv_comp (isLimitOppositeFan Z) (limit.isLimit _) ⟨b⟩

variable {X : C} (π : (a : α) → Z a ⟶ X)

lemma descOpCompCoprodToProd {X : C} (π : (a : α) → Z a ⟶ X) :
    (Sigma.desc π).op ≫ (CoprodToProd Z).hom = Pi.lift (fun a => Quiver.Hom.op (π a)) := by
  refine' limit.hom_ext (fun a => _)
  simp only [CoprodToProd, Category.assoc, limit.conePointUniqueUpToIso_hom_comp, oppositeFan_pt,
    oppositeFan_π_app, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, ← op_comp, colimit.ι_desc]
  rfl

end CoprodToProd

end ProdCoprod


section ExtensiveRegular

section HasPullbackOfRightMono

open CategoryTheory Opposite CategoryTheory.Limits Functor

variable (C : Type u) [Category.{v, u} C]

class HasPullbackOfIsIsodesc : Prop where
    HasPullback : ∀ {X Z : C} {α : Type _} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α),
    HasPullback f (i a)

instance [HasPullbackOfIsIsodesc C] {X Z : C} {α : Type _} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α) :
    HasPullback f (i a) := HasPullbackOfIsIsodesc.HasPullback f i a

instance [HasPullbacks C] : HasPullbackOfIsIsodesc C := ⟨fun _ _ _ => inferInstance⟩

end HasPullbackOfRightMono

section Coverage
namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

open Sieve CategoryTheory.Limits Opposite

variable {C}

def ExtensiveSieve [HasFiniteCoproducts C] (B : C) := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C)
  (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }

def RegularSieve (B : C) := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
      (fun (_ : Unit) ↦ f) ∧ Epi f }

variable [HasFiniteCoproducts C] (C)

def Extensivity [HasPullbackOfIsIsodesc C] : Prop :=
  ∀ {α : Type} [Fintype α] {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X)
  {Y : C} (f : Y ⟶ X) (_ : IsIso (Sigma.desc π)),
     IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _))

def EverythingIsProjective : Prop :=
  ∀ X : C, Projective X

def ExtensiveRegularCoverage [HasFiniteCoproducts C] [HasPullbackOfIsIsodesc C]
    (h_proj : EverythingIsProjective C) (h_ext : Extensivity C) : Coverage C where
  covering B :=   (ExtensiveSieve B) ∪ (RegularSieve B)
  pullback := by
    rintro X Y f S (⟨α, hα, Z, π, hS, h_iso⟩ | ⟨Z, π, hπ, h_epi⟩)
    · let Z' : α → C := fun a ↦ pullback f (π a)
      set π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst with hπ'
      set S' := @Presieve.ofArrows C _ _ α Z' π' with hS'
      use S'
      constructor
      · rw [Set.mem_union]
        apply Or.intro_left
        rw [ExtensiveSieve]
        constructor
        refine ⟨hα, Z', π', ⟨by simp only, ?_⟩⟩
        · rw [hπ']
          exact h_ext (fun x => π x) f h_iso
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        rcases hg with ⟨a⟩
        refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
        rw [hS]
        refine Presieve.ofArrows.mk a
    · set S' := Presieve.singleton (𝟙 Y) with hS'
      use S'
      constructor
      · apply Or.intro_right
        rw [RegularSieve]
        refine ⟨Y, 𝟙 _, by {rw [Presieve.ofArrows_pUnit (𝟙 Y)]}, instEpiIdToCategoryStruct Y⟩
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        cases hg
        simp only [Category.id_comp]
        use Z
        use @Projective.factorThru C _ Y X Z ?_ f π h_epi
        · use π
          constructor
          · cases hπ
            rw [Presieve.ofArrows_pUnit]
            exact Presieve.singleton.mk
          · have : Projective Y
            exact h_proj Y
            exact @Projective.factorThru_comp C _ Y X Z this f π h_epi
        · exact h_proj Y

def EpiPullbackOfEpi [HasPullbacks C] : Prop := ∀ {X Y Z : C} (f : Y ⟶ X) (π : Z ⟶ X) [Epi π],
    Epi (@pullback.fst _ _ _ _ _ f π _)

def ExtensiveRegularCoverage' [HasFiniteCoproducts C] [HasPullbacks C] (h_epi_epi : EpiPullbackOfEpi C)
    (h_ext : Extensivity C) : Coverage C where
  covering B := (ExtensiveSieve B) ∪ (RegularSieve B)
  pullback := by
    rintro X Y f S (⟨α, hα, Z, π, hS, h_iso⟩ | ⟨Z, π, hπ, h_epi⟩)
    · let Z' : α → C := fun a ↦ pullback f (π a)
      set π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst with hπ'
      set S' := @Presieve.ofArrows C _ _ α Z' π' with hS'
      use S'
      constructor
      · rw [Set.mem_union]
        apply Or.intro_left
        rw [ExtensiveSieve]
        constructor
        refine ⟨hα, Z', π', ⟨by simp only, ?_⟩⟩
        · rw [hπ']
          exact h_ext (fun x => π x) f h_iso
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        rcases hg with ⟨a⟩
        refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
        rw [hS]
        refine Presieve.ofArrows.mk a
    · set S' := Presieve.singleton (@pullback.fst _ _ _ _ _ f π _) with hS'
      use S'
      constructor
      · right
        rw [RegularSieve]
        refine' ⟨(pullback f π), _, by {rw [Presieve.ofArrows_pUnit _]}, h_epi_epi f π⟩
      · rw [hS', Presieve.FactorsThruAlong]
        rintro _ _ ⟨⟩
        refine' ⟨Z, pullback.snd, π, ⟨_, by rw [pullback.condition]⟩⟩
        rw [hπ]
        exact Presieve.ofArrows.mk ()

variable [HasPullbackOfIsIsodesc C] {C}

lemma isPullbackSieve_ExtensiveSieve {X : C} {S : Presieve X}
    (hS : S ∈ ExtensiveSieve X) : isPullbackPresieve S := by
  rcases hS with ⟨α, _, Z, π, hS, HIso⟩
  intro Y₁ Y₂ f hf g hg
  rw [hS] at hf hg
  cases' hg with b
  apply HasPullbackOfIsIsodesc.HasPullback f

def v {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) : α → Σ(Y : C), { f : Y ⟶ X // S f } :=
  fun a => ⟨Z a, π a, hS ▸ Presieve.ofArrows.mk a⟩

lemma vsurj {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) : Function.Surjective (v hS) := fun ⟨Y, ⟨f, hf⟩⟩ => by
  cases' (hS ▸ hf) with a h
  exact ⟨a, rfl⟩

lemma v.fst {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) (a : α) : (v hS a).1 = Z a := rfl

lemma v.snd {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) (a : α) : (v hS a).2.1 = π a := rfl

noncomputable
def FintypeT {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
     (hS: S = Presieve.ofArrows Z π) : Fintype (Σ(Y : C), { f : Y ⟶ X // S f }) := by
  classical
  exact Fintype.ofSurjective _ (vsurj hS)

lemma HasProductT {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
     (hS: S = Presieve.ofArrows Z π) : HasProduct
     fun (f : (Σ(Y : C), { f : Y ⟶ X // S f })) => (op f.1) := by
  suffices Finite (Σ(Y : C), { f : Y ⟶ X // S f }) by
    · infer_instance
  exact Fintype.finite <| FintypeT hS

noncomputable
def comparisoninv {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) (F : Cᵒᵖ ⥤ Type max u v) :
    haveI := HasProductT hS
    (∏ fun (f : (Σ(Y : C), { f : Y ⟶ X // S f })) => F.obj (op f.1)) ⟶
    ∏ fun a => F.obj (op (Z a)) :=
  haveI := HasProductT hS
  Pi.lift (fun a => Pi.π _ (v hS a) ≫ F.map (𝟙 _))

noncomputable
def fromFirst {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) {F : Cᵒᵖ ⥤ Type max u v} (hF : PreservesFiniteProducts F)
    (HIso : IsIso (Sigma.desc π)) :
    Equalizer.FirstObj F S ⟶ F.obj (op X) :=
  haveI : PreservesLimit (Discrete.functor fun a => op (Z a)) F := by
    haveI := (hF.preserves α); infer_instance
  comparisoninv hS F ≫ ((Limits.PreservesProduct.iso F (fun a => op <| Z a)).inv ≫
    F.map (CoprodToProd Z).inv ≫ F.map (inv (Sigma.desc π).op))

lemma piCompInvdesc {α : Type} [Fintype α] {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X)
    (HIso : IsIso (Sigma.desc π)) (a : α) : π a ≫ inv (Sigma.desc π) = Sigma.ι _ a := by
  simp

lemma PreservesProduct.isoInvCompMap {C : Type u} [Category C] {D : Type v} [Category D] (F : C ⥤ D)
    {J : Type w} {f : J → C} [HasProduct f] [HasProduct (fun j => F.obj (f j))]
    [PreservesLimit (Discrete.functor f) F] (j : J) :
    (PreservesProduct.iso F f).inv ≫ F.map (Pi.π _ j) = Pi.π _ j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (⟨j⟩ : Discrete J)

lemma isSheafForDagurSieveIsIsoFork {X : C} {S : Presieve X} (hS : S ∈ ExtensiveSieve X)
    {F : Cᵒᵖ ⥤ Type max u v}
    (hF : PreservesFiniteProducts F) :
    IsIso (Equalizer.forkMap F S) := by
  rcases hS with ⟨α, _, Z, π, hS, HIso⟩
  haveI : PreservesLimit (Discrete.functor fun a => op (Z a)) F := by
      haveI := (hF.preserves α); infer_instance
  refine' ⟨fromFirst hS hF HIso, _, _⟩
  · unfold fromFirst
    simp only [← Category.assoc]
    rw [Functor.map_inv, IsIso.comp_inv_eq, Category.id_comp, ← Functor.mapIso_inv,
      Iso.comp_inv_eq, Functor.mapIso_hom, Iso.comp_inv_eq, ← Functor.map_comp, descOpCompCoprodToProd]
    have : F.map (Pi.lift fun a => (π a).op) ≫ (PreservesProduct.iso F fun a => op (Z a)).hom =
      Pi.lift (fun a => F.map ((Sigma.ι Z a ≫ (Sigma.desc π)).op)) := by simp --this can be a general lemma
    erw [this]
    refine' funext (fun s => _)
    simp only [types_comp_apply, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    ext a
    rw [Types.Limit.lift_π_apply]
    dsimp [comparisoninv]
    simp_rw [v.fst]
    simp only [Functor.map_id, Category.comp_id]
    rw [Types.Limit.lift_π_apply]
    simp only [Fan.mk_pt, Equalizer.forkMap, Fan.mk_π_app, Types.pi_lift_π_apply, v.snd]
  · refine' Limits.Pi.hom_ext _ _ (fun f => _)
    dsimp [Equalizer.forkMap]
    rw [Category.id_comp, Category.assoc, limit.lift_π, Limits.Fan.mk_π_app]
    simp only
    obtain ⟨a, ha⟩ := vsurj hS f
    unfold fromFirst
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← op_inv, ← op_comp, ← ha, v.snd hS, piCompInvdesc,
      ← Functor.map_comp, CoprodToProdInvComp.ι, @PreservesProduct.isoInvCompMap _ _ _ _ F _ _ _ _ (_) a]
    simp only [comparisoninv, op_id, limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
    erw [F.map_id, Category.comp_id]

lemma isSheafForExtensiveSieve {X : C} {S : Presieve X} (hS : S ∈ ExtensiveSieve X)
    {F : Cᵒᵖ ⥤ Type max u v}
    (hF : PreservesFiniteProducts F) :
    Presieve.IsSheafFor F S := by
  refine' (Equalizer.Presieve.sheaf_condition' F <| isPullbackSieve_ExtensiveSieve hS).2 _
  rw [Limits.Types.type_equalizer_iff_unique]
  dsimp [Equalizer.FirstObj]
  suffices IsIso (Equalizer.forkMap F S) by
    · intro y _
      refine' ⟨inv (Equalizer.forkMap F S) y, _, fun y₁ hy₁ => _⟩
      · change (inv (Equalizer.forkMap F S) ≫ (Equalizer.forkMap F S)) y = y
        rw [IsIso.inv_hom_id, types_id_apply]
      · replace hy₁ := congr_arg (inv (Equalizer.forkMap F S)) hy₁
        change ((Equalizer.forkMap F S) ≫ inv (Equalizer.forkMap F S)) _ = _ at hy₁
        rwa [IsIso.hom_inv_id, types_id_apply] at hy₁
  exact isSheafForDagurSieveIsIsoFork hS hF

end CategoryTheory

end Coverage

end ExtensiveRegular

section StoneanProjective -- This section is PR #5808

open CategoryTheory

namespace Stonean

/-- Every Stonean space is projective in `CompHaus` -/
instance (X : Stonean) : Projective X.compHaus where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected X.compHaus.toTop := X.extrDisc
    have hf : f.1.Surjective
    · rwa [CompHaus.epi_iff_surjective] at *
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.continuous f.continuous hf
    use ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

end Stonean

namespace CompHaus

/-- If `X` is compact Hausdorff, `presentation X` is an extremally disconnected space
  equipped with an epimorphism down to `X`. It is a "constructive" witness to the
  fact that `CompHaus` has enough projectives.  -/
noncomputable
def presentation (X : CompHaus) : Stonean where
  compHaus := (projectivePresentation X).p
  extrDisc := by
    refine' CompactT2.Projective.extremallyDisconnected
      (@fun Y Z _ _ _ _ _ _ f g hfcont hgcont hgsurj => _)
    let g₁ : (CompHaus.of Y) ⟶ (CompHaus.of Z) := ⟨g, hgcont⟩
    let f₁ : (projectivePresentation X).p ⟶ (CompHaus.of Z) := ⟨f, hfcont⟩
    have hg₁ : Epi g₁ := (epi_iff_surjective _).2 hgsurj
    refine' ⟨Projective.factorThru f₁ g₁, (Projective.factorThru f₁ g₁).2, funext (fun _ => _)⟩
    change (Projective.factorThru f₁ g₁ ≫ g₁) _ = f _
    rw [Projective.factorThru_comp]
    rfl

/-- The morphism from `presentation X` to `X`. -/
noncomputable
def presentation.π (X : CompHaus) : X.presentation.compHaus ⟶ X :=
  (projectivePresentation X).f

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
instance presentation.epi_π (X : CompHaus) : Epi (π X) :=
  (projectivePresentation X).epi

/--

               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y

If `Z` is extremally disconnected, X, Y are compact Hausdorff, if `f : X ⟶ Y` is an epi and
`e : Z ⟶ Y` is arbitrary, then `lift e f` is a fixed (but arbitrary) lift of `e` to a morphism
`Z ⟶ X`. It exists because `Z` is a projective object in `CompHaus`.
-/
noncomputable
def lift {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Z.compHaus ⟶ X :=
  Projective.factorThru e f

@[simp, reassoc]
lemma lift_lifts {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    lift e f ≫ f = e := by simp [lift]

lemma Gleason (X : CompHaus.{u}) :
    Projective X ↔ ExtremallyDisconnected X := by
  constructor
  · intro h
    show ExtremallyDisconnected X.toStonean
    infer_instance
  · intro h
    let X' : Stonean := ⟨X⟩
    show Projective X'.compHaus
    apply Stonean.instProjectiveCompHausCategoryCompHaus

end CompHaus

end StoneanProjective

section OpenEmbedding

open CategoryTheory Limits

namespace Stonean

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeoOfIso {X Y : Stonean} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.1
  invFun := f.2
  left_inv x := Iso.hom_inv_id_apply f x -- why doesn't `simp` work?
  right_inv x := Iso.inv_hom_id_apply f x -- why doesn't `simp` work?
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous

/--
A coproduct cocone associated to the explicit finite coproduct with cone point `finiteCoproduct X`.
-/
@[simps]
def finiteCoproduct.explicitCocone {α : Type} [Fintype α] (Z : α → Stonean.{u}) :
    Limits.Cocone (Discrete.functor Z) where
  pt := finiteCoproduct Z
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι Z a

/--
The more explicit finite coproduct cocone is a colimit cocone.
-/
@[simps]
def finiteCoproduct.isColimit' {α : Type} [Fintype α] (Z : α → Stonean.{u})  :
    Limits.IsColimit (finiteCoproduct.explicitCocone Z) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

/-- The isomorphism from the explicit finite coproducts to the abstract coproduct. -/
noncomputable
def coproductIsoCoproduct {α : Type} [Fintype α] (Z : α → Stonean.{u}) :
    finiteCoproduct Z ≅ ∐ Z :=
  Limits.IsColimit.coconePointUniqueUpToIso
    (finiteCoproduct.isColimit' Z) (Limits.colimit.isColimit _)

lemma finiteCoproduct.ιOpenEmbedding {α : Type} [Fintype α] (Z : α → Stonean.{u}) (a : α) :
    OpenEmbedding (finiteCoproduct.ι Z a) := by
  exact openEmbedding_sigmaMk (σ := fun a => (Z a))

lemma openEmbedding_ι {α : Type} [Fintype α] (Z : α → Stonean.{u}) (a : α) :
    OpenEmbedding (Sigma.ι Z a) := by
  refine' OpenEmbedding.of_comp _ (homeoOfIso (coproductIsoCoproduct Z).symm).openEmbedding _
  convert finiteCoproduct.ιOpenEmbedding Z a
  ext x
  change ((Sigma.ι Z a) ≫ (coproductIsoCoproduct Z).inv) x = _
  simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv,
    finiteCoproduct.explicitCocone_pt, finiteCoproduct.explicitCocone_ι, Discrete.natTrans_app]

end Stonean

end OpenEmbedding
