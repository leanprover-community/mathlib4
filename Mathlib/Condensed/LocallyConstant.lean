import Mathlib.Condensed.PreservesProductExplicit
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

def α : Type u := Set.range (fun (x : Set.range f) ↦ f ⁻¹' {x.val})

def α.image (a : α f) : Y.val.obj (op (⊤_ _)) := a.2.choose.1

lemma α.eq_fiber_image (a : α f) : a.1 = f ⁻¹' {a.image} := a.2.choose_spec.symm

def α.mk (s : S) : α f := ⟨f ⁻¹' {f s}, by simp⟩

def α.mkSelf (s : S) : (mk f s).val := ⟨s, rfl⟩

lemma α.map_eq_image (a : α f) (x : a.1) : f x = a.image := by
  have := a.2.choose_spec
  rw [← Set.mem_singleton_iff, ← Set.mem_preimage]
  convert x.prop

lemma α.mk_image (s : S) : (α.mk f s).image = f s :=
  (map_eq_image (x := mkSelf f s)).symm

lemma α.exists_eq_image (a : α f) : ∃ s, f s = a.image := a.2.choose.2

def α.preimage (a : α f) : S := a.2.choose.2.choose

lemma α.map_preimage_eq_image (a : α f) : f a.preimage = a.image := a.2.choose.2.choose_spec

instance : Finite (α f) :=
  have : Finite (Set.range f) := LocallyConstant.range_finite f
  Finite.Set.finite_range _

variable {T : CompHaus.{u}} (g : T ⟶ S)

lemma α.map_eq_image_comap (a : α (f.comap g)) (x : a.1) : f (g x.val) = a.image := by
  rw [← map_eq_image (f.comap g) a x]
  exact (coe_comap_apply _ _ g.continuous _).symm

lemma α.map_preimage_eq_image_comap (a : α (f.comap g)) : f (g a.preimage) = a.image := by
  rw [← map_preimage_eq_image]
  exact (coe_comap_apply _ _ g.continuous _).symm

lemma α.image_eq_image_mk (a : α (f.comap g)) : a.image = (α.mk f (g (a.preimage _))).image := by
  rw [← map_preimage_eq_image_comap, mk_image]

def component_map (a : α (f.comap g)) : C(a.val, (α.mk f (g a.preimage)).val) where
  toFun x := ⟨g x.val, by
    simp only [α.mk, Set.mem_preimage, Set.mem_singleton_iff]
    rw [α.map_eq_image_comap, α.map_preimage_eq_image_comap]
    ⟩
  continuous_toFun := Continuous.subtype_mk (Continuous.comp g.continuous continuous_subtype_val) _

def component_map₂ : C((a : α (f.comap g)) × a.val, (b : α f) × b.val) where
  toFun := fun ⟨a, x⟩ ↦ ⟨α.mk f (g a.preimage), component_map f g a x⟩
  continuous_toFun := continuous_sigma fun _ ↦
    Continuous.comp continuous_sigmaMk (component_map f g _).continuous

def component_map' (a : α (f.comap g)) : C(a.val, S) where
  toFun x := g x.val
  continuous_toFun := g.continuous.comp continuous_subtype_val

def σ : α f → Type u := fun x ↦ x.val

instance (x : α f) : TopologicalSpace (σ f x) := (inferInstance : TopologicalSpace <| Subtype _)

instance (x : α f) : T2Space (σ f x) := (inferInstance : T2Space <| Subtype _)

instance (x : α f) : CompactSpace (σ f x) := by
  obtain ⟨y, hy⟩ := x.prop
  erw [← isCompact_iff_compactSpace, ← hy]
  exact (f.2.isClosed_fiber _).isCompact

instance (x : α f) : CompactSpace x.val := by
  obtain ⟨y, hy⟩ := x.prop
  erw [← isCompact_iff_compactSpace, ← hy]
  exact (f.2.isClosed_fiber _).isCompact

def component_hom (a : α (f.comap g)) :
    CompHaus.of a.val ⟶ CompHaus.of (α.mk f (g a.preimage)).val where
  toFun x := ⟨g x.val, by
    simp only [α.mk, Set.mem_preimage, Set.mem_singleton_iff]
    rw [α.map_eq_image_comap, α.map_preimage_eq_image_comap]
    ⟩
  continuous_toFun := Continuous.subtype_mk (Continuous.comp g.continuous continuous_subtype_val) _

@[simps]
def sigmaToFun : C((x : α f) × x.val, S) where
  toFun := fun ⟨a, x⟩ ↦ x.val

lemma sigmaToFun_inj : Function.Injective (sigmaToFun f) := by
  rintro ⟨⟨_, _, rfl⟩, ⟨_, hx⟩⟩ ⟨⟨_, _, rfl⟩, ⟨_, hy⟩⟩ h
  refine Sigma.subtype_ext ?_ h
  simp only [sigmaToFun_apply] at h
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hy
  simp [← hx, ← hy, h]

lemma sigmaToFun_surj : Function.Surjective (sigmaToFun f) :=
  fun _ ↦ ⟨⟨⟨_, ⟨⟨_, Set.mem_range_self _⟩, rfl⟩⟩, ⟨_, rfl⟩⟩, rfl⟩

@[simps!]
def sigmaIso : (CompHaus.of <| (x : α f) × x.val) ≅ S :=
  CompHaus.isoOfBijective (sigmaToFun f) ⟨sigmaToFun_inj f, sigmaToFun_surj f⟩

@[simps!]
def sigmaIncl (a : α f) : CompHaus.of a.val ⟶ S where
  toFun := fun x ↦ x.val

@[elementwise (attr := simp), reassoc]
lemma sigmaComparison_comp_sigmaIso (a : α f):
    (Y.val.mapIso (sigmaIso f).op).hom ≫ Condensed.sigmaComparison Y (σ f) ≫ (fun g ↦ g a) =
      Y.val.map (sigmaIncl f a).op := by
  ext
  simp only [Functor.mapIso_hom, Iso.op_hom, types_comp_apply, Condensed.sigmaComparison,
    CompHaus.coe_of]
  rw [← FunctorToTypes.map_comp_apply]
  congr

def counit_app_app_image : (a : α f) → Y.val.obj ⟨CompHaus.of <| a.val⟩ :=
  fun a ↦ Y.val.map (terminal.from _).op a.image

def counit_app_app (S : CompHaus.{u}) (Y : CondensedSet.{u}) :
    LocallyConstant S (Y.val.obj (op (⊤_ _))) ⟶ Y.val.obj ⟨S⟩ :=
  fun f ↦ ((inv (Condensed.sigmaComparison Y (σ f))) ≫ (Y.val.mapIso (sigmaIso f).op).inv)
    (counit_app_app_image f)

lemma locallyConstantCondensed_ext (x y : Y.val.obj ⟨S⟩)
    (h : ∀ (a : α f), Y.val.map (sigmaIncl f a).op x = Y.val.map (sigmaIncl f a).op y) : x = y := by
  apply_fun (Y.val.mapIso (sigmaIso f).op).hom using injective_of_mono _
  apply_fun Condensed.sigmaComparison Y (σ f) using injective_of_mono _
  ext a
  specialize h a
  rw [← sigmaComparison_comp_sigmaIso] at h
  exact h

lemma types_iso_inv_comp_apply {X Y : Type _} (i : X ⟶ Y) (y : Y) [IsIso i] :
    i (inv i y) = y :=
  inv_hom_id_apply (asIso i) _

lemma incl_of_counit_app_app (a : α f) :
    Y.val.map (sigmaIncl f a).op (counit_app_app S Y f) = counit_app_app_image f a := by
  simp only [← sigmaComparison_comp_sigmaIso, Functor.mapIso_hom, Iso.op_hom, types_comp_apply]
  simp only [counit_app_app, Functor.mapIso_inv, ← Iso.op_hom, types_comp_apply]
  rw [← FunctorToTypes.map_comp_apply]
  simp only [Iso.inv_hom_id, FunctorToTypes.map_id_apply]
  rw [types_iso_inv_comp_apply (i := Condensed.sigmaComparison _ _)]

lemma incl_comap (a : α (f.comap g)) : sigmaIncl (f.comap g) a ≫ g =
    (component_hom f g a) ≫ sigmaIncl f _ := rfl

lemma incl_comap_op {S T : CompHausᵒᵖ} (f : LocallyConstant S.unop (Y.val.obj (op (⊤_ _))))
    (g : S ⟶ T) (a : α (f.comap g.unop)) : g ≫ (sigmaIncl (f.comap g.unop) a).op =
    (sigmaIncl f _).op ≫ (component_hom f g.unop a).op := by
  rw [← op_comp, ← incl_comap]
  simp

def counit_app (Y : CondensedSet.{u}) : LC'.obj (Y.val.obj (op (⊤_ _))) ⟶ Y where
  val := {
    app := fun ⟨S⟩ ↦ counit_app_app S Y
    naturality := by
      intro S T g
      simp only [LC', LC, id_eq, eq_mpr_eq_cast]
      ext f
      apply locallyConstantCondensed_ext (f.comap g.unop)
      intro a
      simp only [op_unop, types_comp_apply]
      rw [incl_of_counit_app_app, ← FunctorToTypes.map_comp_apply, incl_comap_op]
      simp only [op_unop, FunctorToTypes.map_comp_apply]
      rw [incl_of_counit_app_app]
      simp only [counit_app_app_image, ← FunctorToTypes.map_comp_apply, ← op_comp,
        terminal.comp_from, α.image_eq_image_mk]
  }


end DiscreteAdjunction
