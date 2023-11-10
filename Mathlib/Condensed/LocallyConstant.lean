import Mathlib.Condensed.TopComparison
import Mathlib.Data.Fintype.Small

universe u

noncomputable section

open CategoryTheory Limits Condensed LocallyConstant Opposite

@[simps]
def LC : Type (u+1) ⥤ (CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) where
  obj X := {
    obj := fun ⟨S⟩ => LocallyConstant S X
    map := fun f g => g.comap f.unop
    map_id := fun _ => comap_id
    map_comp := fun f g => (comap_comp g.unop f.unop g.unop.2 f.unop.2).symm }
  map f := {
    app := fun S t => ⟨f ∘ t, IsLocallyConstant.comp t.isLocallyConstant _⟩
    naturality := by
      intro S T g
      ext h x
      simp only [types_comp_apply, coe_mk, Function.comp_apply]
      erw [coe_comap_apply g.unop _ g.unop.2 x, coe_comap_apply g.unop _ g.unop.2 x]
      rfl }

@[simps]
def LC_iso_aux (Y X : Type*) [TopologicalSpace Y] :
    LocallyConstant Y X ≅ C(Y, TopCat.discrete.obj X) :=
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  { hom := fun f ↦ (f : C(Y, X))
    inv := fun f ↦ ⟨f, (IsLocallyConstant.iff_continuous f).mpr f.2⟩ }

def LC_iso (X : Type (u+1)) : LC.obj X ≅ (topCatToCondensed.obj (TopCat.discrete.obj X)).val :=
  NatIso.ofComponents (fun S => LC_iso_aux _ _) (fun f => by
    ext
    apply @ContinuousMap.ext _ (TopCat.discrete.obj X) _ _
    intro a
    erw [coe_comap f.unop _ f.unop.2]
    rfl)

def LC' : Type (u+1) ⥤ CondensedSet.{u} where
  obj X := {
    val := LC.obj X
    cond := by
      rw [Presheaf.isSheaf_of_iso_iff (LC_iso X)]
      exact (topCatToCondensed.obj _).cond
  }
  map f := ⟨LC.map f⟩
  map_id X := by simp only [LC.map_id]; rfl
  map_comp f g := by simp only [LC.map_comp]; rfl

namespace DiscreteAdjunction

variable {S : CompHaus.{u}} {Y : CondensedSet.{u}} (f : LocallyConstant S (Y.val.obj (op (⊤_ _))))

instance indexingSetFintype : Fintype (Set.range f) := sorry

def Z : Set.range f → CompHaus.{u}ᵒᵖ :=
  haveI : ∀ x, CompactSpace (f ⁻¹' {x}) := fun _ =>
    isCompact_iff_compactSpace.mp (f.2.isClosed_fiber _).isCompact
  fun x => op (CompHaus.of (f ⁻¹' {x.val}))

instance indexingSetSmall : Small.{0} (Set.range f) := small_of_fintype _

def indexingSet : Type := (indexingSetSmall f).equiv_small.choose

instance indexingSetFintype' : Fintype (indexingSet f) := sorry

def indexingMap : indexingSet f → CompHaus.{u}ᵒᵖ :=
  haveI : ∀ x, CompactSpace (f ⁻¹' {x}) := fun _ =>
    isCompact_iff_compactSpace.mp (f.2.isClosed_fiber _).isCompact
  fun x => op (CompHaus.of (f ⁻¹' {((indexingSetSmall f).equiv_small.choose_spec.some.symm x).val}))

instance : PreservesLimit (Discrete.functor (Z f)) Y.val := by
  have : PreservesFiniteProducts Y.val := sorry
  have := (this.preserves (indexingSet f))
  let i : Discrete (Set.range f) ≌ Discrete (indexingSet f) := sorry
  exact (preservesLimitsOfShapeOfEquiv i.symm Y.val).1

def isoProduct : op S ≅ ∏ (Z f) := by
  refine (?_ : ∐ (fun i ↦ unop (Z f i)) ≅ S).op ≪≫ opCoproductIsoProduct _
  refine CompHaus.isoOfBijective (Sigma.desc (fun i ↦ (⟨fun x ↦ x.val, by continuity⟩))) ⟨?_, ?_⟩
  · intro a b h
    sorry
    --apply ((forget CompHaus).mapIso (CompHaus.coproductIsoCoproduct _)).hom
  · sorry


def isoProduct' : Y.val.obj (op S) ≅ ∏ fun i => Y.val.obj (Z f i) :=
  Y.val.mapIso (isoProduct f) ≪≫ asIso (piComparison Y.val (Z f))

def component (i : Set.range f) : Y.val.obj (op (⊤_ _)) ⟶ Y.val.obj (Z f i) :=
  Y.val.map (terminal.from _).op

def counit_app_app (S : CompHaus.{u}) (Y : CondensedSet.{u}) :
    LocallyConstant S (Y.val.obj (op (⊤_ _))) ⟶ Y.val.obj (op S) :=
  fun f => (isoProduct' f).inv ((Types.productIso.{u+1, u}
    (fun i => Y.val.obj (Z f i))).inv (fun j => component f j (f j.prop.choose)))

variable (T : CompHaus.{u}) (g : T ⟶ S)

def index_map (i : Set.range (f.comap g)) : Set.range f := ⟨i.val, by
  obtain ⟨y, h⟩ := i.prop
  rw [← h, coe_comap g _ g.2]
  exact Set.mem_range_self _⟩

def Z_map (i : Set.range (f.comap g)) : Z f (index_map f T g i) ⟶ Z (comap (↑g) f) i := sorry

theorem component_map (i : Set.range (f.comap g)) :
  component _ i = component f (index_map f T g i) ≫ Y.val.map (Z_map f T g i) := sorry

def counit_app (Y : CondensedSet.{u}) : LC'.obj (Y.val.obj (op (⊤_ _))) ⟶ Y where
  val := {
    app := fun ⟨S⟩ => counit_app_app S Y
    naturality := by
      intro S T f
      ext g
      simp only [LC', LC, Eq.ndrec, id_eq, eq_mpr_eq_cast, types_comp_apply]
      apply_fun (isoProduct' (g.comap f.unop)).hom using injective_of_mono _
      simp only [op_unop, counit_app_app, inv_hom_id_apply]
      apply_fun (Types.productIso.{u+1, u} (fun i => Y.val.obj (Z (g.comap f.unop) i))).hom
        using injective_of_mono _
      simp only [inv_hom_id_apply]
      ext y
      simp only [component, Types.productIso_hom_comp_eval_apply]
      sorry
  }

end DiscreteAdjunction
