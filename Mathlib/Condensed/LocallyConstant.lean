import Mathlib.Condensed.TopComparison

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

instance indexSetFintype : Fintype (Set.range f) := by
  letI : TopologicalSpace (Y.val.obj (op (⊤_ _))) := ⊥
  haveI : DiscreteTopology (Y.val.obj (op (⊤_ _))) := ⟨rfl⟩
  have := (isCompact_range f.continuous).finite_of_discrete
  rw [Set.Finite] at this
  exact Fintype.ofFinite _

def Z' : Set.range f → CompHaus.{u}ᵒᵖ :=
  haveI : ∀ x, CompactSpace (f ⁻¹' {x}) := fun _ =>
    isCompact_iff_compactSpace.mp (f.2.isClosed_fiber _).isCompact
  fun x => op (CompHaus.of (f ⁻¹' {x.val}))

instance indexSetSmall : Small.{0} (Set.range f) := Countable.toSmall _

def indexSet : Type := (indexSetSmall f).equiv_small.choose

def indexEquiv : indexSet f ≃ Set.range f :=
  (indexSetSmall f).equiv_small.choose_spec.some.symm

instance indexSetFintype' : Fintype (indexSet f) := Fintype.ofEquiv _ (indexEquiv _).symm

def Z : indexSet f → CompHaus.{u}ᵒᵖ :=
  haveI : ∀ x, CompactSpace (f ⁻¹' {x}) := fun _ =>
    isCompact_iff_compactSpace.mp (f.2.isClosed_fiber _).isCompact
  fun x => op (CompHaus.of (f ⁻¹' {(indexEquiv f x).val}))

instance : PreservesLimit (Discrete.functor (Z f)) Y.val := by
  have : PreservesFiniteProducts Y.val := inferInstance
  exact (this.preserves (indexSet f)).1

def homeoSigma {X Y : Type*} [TopologicalSpace X] (f : LocallyConstant X Y)
    (p : Y → Prop) (h : ∀ x, p (f x)) :
    (Σ (y : {y // p y}), f ⁻¹' {y.val}) ≃ₜ X where
      toEquiv := Equiv.sigmaSubtypeFiberEquiv f p h
      continuous_invFun := by
        rw [continuous_def]
        intro U hU
        have : (Equiv.sigmaSubtypeFiberEquiv f p h).invFun ⁻¹' U =
            (Equiv.sigmaSubtypeFiberEquiv f p h).toFun '' U := by ext; simp
        rw [this]
        refine (?_ : IsOpenMap _) U hU
        rw [isOpenMap_sigma]
        exact fun i ↦ IsOpen.isOpenMap_subtype_val (f.2.isOpen_fiber _)

@[simps! apply toEquiv]
def _root_.Homeomorph.sigmaCongrLeft {α₁ α₂ : Type*} {β : α₁ → Type*} [∀ a, TopologicalSpace (β a)]
    (f : α₁ ≃ α₂) : (a : α₁) × β a ≃ₜ (a : α₂) × β (f.symm a) where
  toEquiv := Equiv.sigmaCongrLeft' f
  continuous_toFun := by
    apply continuous_sigma
    rw [f.forall_congr_left']
    intro i
    simp only [Equiv.sigmaCongrLeft', Equiv.sigmaCongrLeft, Equiv.symm_symm_apply,
      Equiv.toFun_as_coe, Equiv.coe_fn_symm_mk]
    convert continuous_sigmaMk (ι := α₂) (σ := fun a ↦ β (f.symm a))
    all_goals simp
  continuous_invFun := by
    apply continuous_sigma
    rw [f.symm.forall_congr_left']
    intro i
    exact continuous_sigmaMk

def extracted_1 :
    CompHaus.finiteCoproduct (fun i ↦ (Z f i).unop) ≃ₜ
    (y : Set.range f) × (f ⁻¹' {y.val}) :=
  (Homeomorph.sigmaCongrLeft (β := fun (a : Set.range f) ↦ f ⁻¹' {a.1}) (indexEquiv f).symm).symm

def homeoExplCopr : (CompHaus.finiteCoproduct fun i ↦ (Z f i).unop) ≃ₜ S :=
  let i := homeoSigma f (· ∈ Set.range f) fun _ ↦ Set.mem_range_self _
  (extracted_1 f).trans i

def isoProduct : op S ≅ ∏ (Z f) :=
  (CompHaus.isoOfHomeo (homeoExplCopr f)).op ≪≫
    opCoproductIsoProduct'
    (CompHaus.finiteCoproduct.isColimit (fun i ↦ unop (Z f i))) (productIsProduct (Z f))

def isoProduct' : Y.val.obj (op S) ≅ ∏ fun i => Y.val.obj (Z f i) :=
  Y.val.mapIso (isoProduct f) ≪≫ asIso (piComparison Y.val (Z f))

def component (i : indexSet f) : Y.val.obj (op (⊤_ _)) ⟶ Y.val.obj (Z f i) :=
  Y.val.map (terminal.from _).op

def counit_app_app (S : CompHaus.{u}) (Y : CondensedSet.{u}) :
    LocallyConstant S (Y.val.obj (op (⊤_ _))) ⟶ Y.val.obj (op S) :=
  fun f => (isoProduct' f).inv ((Types.productIso
    (fun i => Y.val.obj (Z f i))).inv (fun j => component f j (f (indexEquiv f j).prop.choose)))

variable (T : CompHaus.{u}) (g : T ⟶ S)

def range_map (i : Set.range (f.comap g)) : Set.range f := ⟨i.val, by
  obtain ⟨y, h⟩ := i.prop
  rw [← h, coe_comap g _ g.2]
  exact Set.mem_range_self _⟩

def index_map (i : indexSet (f.comap g)) : indexSet f :=
  (indexEquiv _).symm (range_map _ _ _ ((indexEquiv _) i))

-- def Z_map (i : indexSet (f.comap g)) : Z f (index_map f T g i) ⟶ Z (comap (↑g) f) i := sorry

-- theorem component_map (i : indexSet (f.comap g)) :
--   component _ i = component f (index_map f T g i) ≫ Y.val.map (Z_map f T g i) := sorry

def counit_app (Y : CondensedSet.{u}) : LC'.obj (Y.val.obj (op (⊤_ _))) ⟶ Y where
  val := {
    app := fun ⟨S⟩ => counit_app_app S Y
    naturality := by
      intro S T f
      ext g
      simp only [LC', LC, Eq.ndrec, id_eq, eq_mpr_eq_cast, types_comp_apply]
      apply_fun (isoProduct' (g.comap f.unop)).hom using injective_of_mono _
      simp only [op_unop, counit_app_app, inv_hom_id_apply]
      apply_fun (Types.productIso (fun i => Y.val.obj (Z (g.comap f.unop) i))).hom
        using injective_of_mono _
      simp only [inv_hom_id_apply]
      ext y
      simp only [component, Types.productIso_hom_comp_eval_apply]
      simp [isoProduct']
      sorry
  }

end DiscreteAdjunction
