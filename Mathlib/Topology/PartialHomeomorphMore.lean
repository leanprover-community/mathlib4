/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.PartialHomeomorph
import Mathlib.Topology.Sets.Opens

/-!
# Bla

-/

open Function Set Filter Topology


variable {X Y Y' Z Z' : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Y']
[TopologicalSpace Z] [TopologicalSpace Z']

namespace PartialHomeomorph

variable (e : PartialHomeomorph X Y)

/-- Interpret a `Homeomorph` as a `PartialHomeomorph` by restricting it
to an open set `s` in the domain and to `t` in the codomain. -/
@[simps! -fullyApplied apply symm_apply toPartialEquiv,
  simps! -isSimp source target]
def _root_.Homeomorph.toPartialHomeomorphOfImageEq (e : X ≃ₜ Y) (s : Set X) (hs : IsOpen s)
    (t : Set Y) (h : e '' s = t) : PartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquivOfImageEq s t h
  open_source' := hs
  open_target' := by simpa [← h]
  continuousOn_toFun := e.continuous.continuousOn
  continuousOn_invFun := e.symm.continuous.continuousOn

/-- A homeomorphism induces a partial homeomorphism on the whole space -/
@[simps! (config := mfld_cfg)]
def _root_.Homeomorph.toPartialHomeomorph (e : X ≃ₜ Y) : PartialHomeomorph X Y :=
  e.toPartialHomeomorphOfImageEq univ isOpen_univ univ <| by rw [image_univ, e.surjective.range_eq]


/-- A `PartialEquiv` with continuous open forward map and open source is a `PartialHomeomorph`. -/
def ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) (hs : IsOpen e.source) : PartialHomeomorph X Y where
  toPartialEquiv := e
  open_source' := hs
  open_target' := by simpa only [range_restrict, e.image_source_eq_target] using ho.isOpen_range
  continuousOn_toFun := hc
  continuousOn_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.leftInvOn

/-- A `PartialEquiv` with continuous open forward map and open source is a `PartialHomeomorph`. -/
def ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : PartialHomeomorph X Y :=
  ofContinuousOpenRestrict e hc (ho.restrict hs) hs

/-- The homeomorphism obtained by restricting a `PartialHomeomorph` to a subset of the source. -/
@[simps]
def homeomorphOfImageSubsetSource {s : Set X} {t : Set Y} (hs : s ⊆ e.source) (ht : e '' s = t) :
    s ≃ₜ t :=
  have h₁ : MapsTo e s t := mapsTo'.2 ht.subset
  have h₂ : t ⊆ e.target := ht ▸ e.image_source_eq_target ▸ image_subset e hs
  have h₃ : MapsTo e.symm t s := ht ▸ forall_mem_image.2 fun _x hx =>
      (e.left_inv (hs hx)).symm ▸ hx
  { toFun := MapsTo.restrict e s t h₁
    invFun := MapsTo.restrict e.symm t s h₃
    left_inv := fun a => Subtype.ext (e.left_inv (hs a.2))
    right_inv := fun b => Subtype.eq <| e.right_inv (h₂ b.2)
    continuous_toFun := (e.continuousOn.mono hs).restrict_mapsTo h₁
    continuous_invFun := (e.continuousOn_symm.mono h₂).restrict_mapsTo h₃ }

/-- A partial homeomorphism defines a homeomorphism between its source and target. -/
@[simps!]
def toHomeomorphSourceTarget : e.source ≃ₜ e.target :=
  e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target

theorem secondCountableTopology_source [SecondCountableTopology Y] :
    SecondCountableTopology e.source :=
  e.toHomeomorphSourceTarget.secondCountableTopology

theorem nhds_eq_comap_inf_principal {x} (hx : x ∈ e.source) :
    𝓝 x = comap e (𝓝 (e x)) ⊓ 𝓟 e.source := by
  lift x to e.source using hx
  rw [← e.open_source.nhdsWithin_eq x.2, ← map_nhds_subtype_val, ← map_comap_setCoe_val,
    e.toHomeomorphSourceTarget.nhds_eq_comap, nhds_subtype_eq_comap]
  simp only [Function.comp_def, toHomeomorphSourceTarget_apply_coe, comap_comap]

/-- If a partial homeomorphism has source and target equal to univ, then it induces a homeomorphism
between the whole spaces, expressed in this definition. -/
@[simps (config := mfld_cfg) apply symm_apply]
-- TODO: add a `PartialEquiv` version
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set X)) (h' : e.target = univ) :
    X ≃ₜ Y where
  toFun := e
  invFun := e.symm
  left_inv x :=
    e.left_inv <| by
      rw [h]
      exact mem_univ _
  right_inv x :=
    e.right_inv <| by
      rw [h']
      exact mem_univ _
  continuous_toFun := by
    simpa only [continuous_iff_continuousOn_univ, h] using e.continuousOn
  continuous_invFun := by
    simpa only [continuous_iff_continuousOn_univ, h'] using e.continuousOn_symm

theorem isOpenEmbedding_restrict : IsOpenEmbedding (e.source.restrict e) := by
  refine .of_continuous_injective_isOpenMap (e.continuousOn.comp_continuous
    continuous_subtype_val Subtype.prop) e.injOn.injective fun V hV ↦ ?_
  rw [Set.restrict_eq, Set.image_comp]
  exact e.isOpen_image_of_subset_source (e.open_source.isOpenMap_subtype_val V hV)
    fun _ ⟨x, _, h⟩ ↦ h ▸ x.2

@[deprecated (since := "2024-10-18")]
alias openEmbedding_restrict := isOpenEmbedding_restrict

/-- A partial homeomorphism whose source is all of `X` defines an open embedding of `X` into `Y`.
The converse is also true; see `IsOpenEmbedding.toPartialHomeomorph`. -/
theorem to_isOpenEmbedding (h : e.source = Set.univ) : IsOpenEmbedding e :=
  e.isOpenEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ X).symm.isOpenEmbedding

@[deprecated (since := "2024-10-18")]
alias to_openEmbedding := to_isOpenEmbedding

end PartialHomeomorph

namespace Homeomorph

variable (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)

/- Register as simp lemmas that the fields of a partial homeomorphism built from a homeomorphism
correspond to the fields of the original homeomorphism. -/
@[simp, mfld_simps]
theorem refl_toPartialHomeomorph :
    (Homeomorph.refl X).toPartialHomeomorph = PartialHomeomorph.refl X :=
  rfl

@[simp, mfld_simps]
theorem symm_toPartialHomeomorph : e.symm.toPartialHomeomorph = e.toPartialHomeomorph.symm :=
  rfl

@[simp, mfld_simps]
theorem trans_toPartialHomeomorph :
    (e.trans e').toPartialHomeomorph = e.toPartialHomeomorph.trans e'.toPartialHomeomorph :=
  PartialHomeomorph.toPartialEquiv_injective <| Equiv.trans_toPartialEquiv _ _

/-- Precompose a partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! -fullyApplied]
def transPartialHomeomorph (e : X ≃ₜ Y) (f' : PartialHomeomorph Y Z) : PartialHomeomorph X Z where
  toPartialEquiv := e.toEquiv.transPartialEquiv f'.toPartialEquiv
  open_source' := f'.open_source.preimage e.continuous
  open_target' := f'.open_target
  continuousOn_toFun := f'.continuousOn.comp e.continuous.continuousOn fun _ => id
  continuousOn_invFun := e.symm.continuous.comp_continuousOn f'.symm.continuousOn

theorem transPartialHomeomorph_eq_trans (e : X ≃ₜ Y) (f' : PartialHomeomorph Y Z) :
    e.transPartialHomeomorph f' = e.toPartialHomeomorph.trans f' :=
  PartialHomeomorph.toPartialEquiv_injective <| Equiv.transPartialEquiv_eq_trans _ _

@[simp, mfld_simps]
theorem transPartialHomeomorph_trans (e : X ≃ₜ Y) (f : PartialHomeomorph Y Z)
    (f' : PartialHomeomorph Z Z') :
    (e.transPartialHomeomorph f).trans f' = e.transPartialHomeomorph (f.trans f') := by
  simp only [transPartialHomeomorph_eq_trans, PartialHomeomorph.trans_assoc]

@[simp, mfld_simps]
theorem trans_transPartialHomeomorph (e : X ≃ₜ Y) (e' : Y ≃ₜ Z) (f'' : PartialHomeomorph Z Z') :
    (e.trans e').transPartialHomeomorph f'' =
      e.transPartialHomeomorph (e'.transPartialHomeomorph f'') := by
  simp only [transPartialHomeomorph_eq_trans, PartialHomeomorph.trans_assoc,
    trans_toPartialHomeomorph]

end Homeomorph

namespace Topology.IsOpenEmbedding

variable (f : X → Y) (h : IsOpenEmbedding f)

/-- An open embedding of `X` into `Y`, with `X` nonempty, defines a partial homeomorphism
whose source is all of `X`. The converse is also true; see
`PartialHomeomorph.to_isOpenEmbedding`. -/
@[simps! (config := mfld_cfg) apply source target]
noncomputable def toPartialHomeomorph [Nonempty X] : PartialHomeomorph X Y :=
  PartialHomeomorph.ofContinuousOpen (h.isEmbedding.injective.injOn.toPartialEquiv f univ)
    h.continuous.continuousOn h.isOpenMap isOpen_univ

variable [Nonempty X]

lemma toPartialHomeomorph_left_inv {x : X} : (h.toPartialHomeomorph f).symm (f x) = x := by
  rw [← congr_fun (h.toPartialHomeomorph_apply f), PartialHomeomorph.left_inv]
  exact Set.mem_univ _

lemma toPartialHomeomorph_right_inv {x : Y} (hx : x ∈ Set.range f) :
    f ((h.toPartialHomeomorph f).symm x) = x := by
  rw [← congr_fun (h.toPartialHomeomorph_apply f), PartialHomeomorph.right_inv]
  rwa [toPartialHomeomorph_target]

end Topology.IsOpenEmbedding

/-! inclusion of an open set in a topological space -/
namespace TopologicalSpace.Opens

/- `Nonempty s` is not a type class argument because `s`, being a subset, rarely comes with a type
class instance. Then we'd have to manually provide the instance every time we use the following
lemmas, tediously using `haveI := ...` or `@foobar _ _ _ ...`. -/
variable (s : Opens X) (hs : Nonempty s)

/-- The inclusion of an open subset `s` of a space `X` into `X` is a partial homeomorphism from the
subtype `s` to `X`. -/
noncomputable def partialHomeomorphSubtypeCoe : PartialHomeomorph s X :=
  IsOpenEmbedding.toPartialHomeomorph _ s.2.isOpenEmbedding_subtypeVal

@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_coe : (s.partialHomeomorphSubtypeCoe hs : s → X) = (↑) :=
  rfl

@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_source : (s.partialHomeomorphSubtypeCoe hs).source = Set.univ :=
  rfl

@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_target : (s.partialHomeomorphSubtypeCoe hs).target = s := by
  simp only [partialHomeomorphSubtypeCoe, Subtype.range_coe_subtype, mfld_simps]
  rfl

end TopologicalSpace.Opens

namespace PartialHomeomorph

/- post-compose with a partial homeomorphism -/
section transHomeomorph

/-- Postcompose a partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! -fullyApplied]
def transHomeomorph (e : PartialHomeomorph X Y) (f' : Y ≃ₜ Z) : PartialHomeomorph X Z where
  toPartialEquiv := e.toPartialEquiv.transEquiv f'.toEquiv
  open_source' := e.open_source
  open_target' := e.open_target.preimage f'.symm.continuous
  continuousOn_toFun := f'.continuous.comp_continuousOn e.continuousOn
  continuousOn_invFun := e.symm.continuousOn.comp f'.symm.continuous.continuousOn fun _ => id

theorem transHomeomorph_eq_trans (e : PartialHomeomorph X Y) (f' : Y ≃ₜ Z) :
    e.transHomeomorph f' = e.trans f'.toPartialHomeomorph :=
  toPartialEquiv_injective <| PartialEquiv.transEquiv_eq_trans _ _

@[simp, mfld_simps]
theorem transHomeomorph_transHomeomorph (e : PartialHomeomorph X Y) (f' : Y ≃ₜ Z) (f'' : Z ≃ₜ Z') :
    (e.transHomeomorph f').transHomeomorph f'' = e.transHomeomorph (f'.trans f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc, Homeomorph.trans_toPartialHomeomorph]

@[simp, mfld_simps]
theorem trans_transHomeomorph (e : PartialHomeomorph X Y) (e' : PartialHomeomorph Y Z)
    (f'' : Z ≃ₜ Z') :
    (e.trans e').transHomeomorph f'' = e.trans (e'.transHomeomorph f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc, Homeomorph.trans_toPartialHomeomorph]

end transHomeomorph

/-! `subtypeRestr`: restriction to a subtype -/
section subtypeRestr

open TopologicalSpace

variable (e : PartialHomeomorph X Y)
variable {s : Opens X} (hs : Nonempty s)

/-- The restriction of a partial homeomorphism `e` to an open subset `s` of the domain type
produces a partial homeomorphism whose domain is the subtype `s`. -/
noncomputable def subtypeRestr : PartialHomeomorph s Y :=
  (s.partialHomeomorphSubtypeCoe hs).trans e

theorem subtypeRestr_def : e.subtypeRestr hs = (s.partialHomeomorphSubtypeCoe hs).trans e :=
  rfl

@[simp, mfld_simps]
theorem subtypeRestr_coe :
    ((e.subtypeRestr hs : PartialHomeomorph s Y) : s → Y) = Set.restrict ↑s (e : X → Y) :=
  rfl

@[simp, mfld_simps]
theorem subtypeRestr_source : (e.subtypeRestr hs).source = (↑) ⁻¹' e.source := by
  simp only [subtypeRestr_def, mfld_simps]

theorem map_subtype_source {x : s} (hxe : (x : X) ∈ e.source) :
    e x ∈ (e.subtypeRestr hs).target := by
  refine ⟨e.map_source hxe, ?_⟩
  rw [s.partialHomeomorphSubtypeCoe_target, mem_preimage, e.leftInvOn hxe]
  exact x.prop

/-- This lemma characterizes the transition functions of an open subset in terms of the transition
functions of the original space. -/
theorem subtypeRestr_symm_trans_subtypeRestr (f f' : PartialHomeomorph X Y) :
    (f.subtypeRestr hs).symm.trans (f'.subtypeRestr hs) ≈
      (f.symm.trans f').restr (f.target ∩ f.symm ⁻¹' s) := by
  simp only [subtypeRestr_def, trans_symm_eq_symm_trans_symm]
  have openness₁ : IsOpen (f.target ∩ f.symm ⁻¹' s) := f.isOpen_inter_preimage_symm s.2
  rw [← ofSet_trans _ openness₁, ← trans_assoc, ← trans_assoc]
  refine EqOnSource.trans' ?_ (eqOnSource_refl _)
  -- f' has been eliminated !!!
  have set_identity : f.symm.source ∩ (f.target ∩ f.symm ⁻¹' s) = f.symm.source ∩ f.symm ⁻¹' s := by
    mfld_set_tac
  have openness₂ : IsOpen (s : Set X) := s.2
  rw [ofSet_trans', set_identity, ← trans_of_set' _ openness₂, trans_assoc]
  refine EqOnSource.trans' (eqOnSource_refl _) ?_
  -- f has been eliminated !!!
  refine Setoid.trans (symm_trans_self (s.partialHomeomorphSubtypeCoe hs)) ?_
  simp only [mfld_simps, Setoid.refl]

theorem subtypeRestr_symm_eqOn {U : Opens X} (hU : Nonempty U) :
    EqOn e.symm (Subtype.val ∘ (e.subtypeRestr hU).symm) (e.subtypeRestr hU).target := by
  intro y hy
  rw [eq_comm, eq_symm_apply _ _ hy.1]
  · change restrict _ e _ = _
    rw [← subtypeRestr_coe, (e.subtypeRestr hU).right_inv hy]
  · have := map_target _ hy; rwa [subtypeRestr_source] at this

theorem subtypeRestr_symm_eqOn_of_le {U V : Opens X} (hU : Nonempty U) (hV : Nonempty V)
    (hUV : U ≤ V) : EqOn (e.subtypeRestr hV).symm (Set.inclusion hUV ∘ (e.subtypeRestr hU).symm)
      (e.subtypeRestr hU).target := by
  set i := Set.inclusion hUV
  intro y hy
  dsimp [PartialHomeomorph.subtypeRestr_def] at hy ⊢
  have hyV : e.symm y ∈ (V.partialHomeomorphSubtypeCoe hV).target := by
    rw [Opens.partialHomeomorphSubtypeCoe_target] at hy ⊢
    exact hUV hy.2
  refine (V.partialHomeomorphSubtypeCoe hV).injOn ?_ trivial ?_
  · rw [← PartialHomeomorph.symm_target]
    apply PartialHomeomorph.map_source
    rw [PartialHomeomorph.symm_source]
    exact hyV
  · rw [(V.partialHomeomorphSubtypeCoe hV).right_inv hyV]
    show _ = U.partialHomeomorphSubtypeCoe hU _
    rw [(U.partialHomeomorphSubtypeCoe hU).right_inv hy.2]

end subtypeRestr

variable {X X' Z : Type*} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Z]
  [Nonempty Z] {f : X → X'}

/-- Extend a partial homeomorphism `e : X → Z` to `X' → Z`, using an open embedding `ι : X → X'`.
On `ι(X)`, the extension is specified by `e`; its value elsewhere is arbitrary (and uninteresting).
-/
noncomputable def lift_openEmbedding (e : PartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    PartialHomeomorph X' Z where
  toFun := extend f e (fun _ ↦ (Classical.arbitrary Z))
  invFun := f ∘ e.invFun
  source := f '' e.source
  target := e.target
  map_source' := by
    rintro x ⟨x₀, hx₀, hxx₀⟩
    rw [← hxx₀, hf.injective.extend_apply e]
    exact e.map_source' hx₀
  map_target' z hz := mem_image_of_mem f (e.map_target' hz)
  left_inv' := by
    intro x ⟨x₀, hx₀, hxx₀⟩
    rw [← hxx₀, hf.injective.extend_apply e, comp_apply]
    congr
    exact e.left_inv' hx₀
  right_inv' z hz := by simpa only [comp_apply, hf.injective.extend_apply e] using e.right_inv' hz
  open_source' := hf.isOpenMap _ e.open_source
  open_target' := e.open_target
  continuousOn_toFun := by
    by_cases Nonempty X; swap
    · intro x hx; simp_all
    set F := (extend f e (fun _ ↦ (Classical.arbitrary Z))) with F_eq
    have heq : EqOn F (e ∘ (hf.toPartialHomeomorph).symm) (f '' e.source) := by
      intro x ⟨x₀, hx₀, hxx₀⟩
      rw [← hxx₀, F_eq, hf.injective.extend_apply e, comp_apply, hf.toPartialHomeomorph_left_inv]
    have : ContinuousOn (e ∘ (hf.toPartialHomeomorph).symm) (f '' e.source) := by
      apply e.continuousOn.comp; swap
      · intro x' ⟨x, hx, hx'x⟩
        rw [← hx'x, hf.toPartialHomeomorph_left_inv]; exact hx
      have : ContinuousOn (hf.toPartialHomeomorph).symm (f '' univ) :=
        (hf.toPartialHomeomorph).continuousOn_invFun
      exact this.mono <| image_mono <| subset_univ _
    exact ContinuousOn.congr this heq
  continuousOn_invFun := hf.continuous.comp_continuousOn e.continuousOn_invFun

@[simp, mfld_simps]
lemma lift_openEmbedding_toFun (e : PartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf) = extend f e (fun _ ↦ (Classical.arbitrary Z)) := rfl

lemma lift_openEmbedding_apply (e : PartialHomeomorph X Z) (hf : IsOpenEmbedding f) {x : X} :
    (lift_openEmbedding e hf) (f x) = e x := by
  simp_rw [e.lift_openEmbedding_toFun]
  apply hf.injective.extend_apply

@[simp, mfld_simps]
lemma lift_openEmbedding_source (e : PartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).source = f '' e.source := rfl

@[simp, mfld_simps]
lemma lift_openEmbedding_target (e : PartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).target = e.target := rfl

@[simp, mfld_simps]
lemma lift_openEmbedding_symm (e : PartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm = f ∘ e.symm := rfl

@[simp, mfld_simps]
lemma lift_openEmbedding_symm_source (e : PartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm.source = e.target := rfl

@[simp, mfld_simps]
lemma lift_openEmbedding_symm_target (e : PartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm.target = f '' e.source := by
  rw [PartialHomeomorph.symm_target, e.lift_openEmbedding_source]

lemma lift_openEmbedding_trans_apply
    (e e' : PartialHomeomorph X Z) (hf : IsOpenEmbedding f) (z : Z) :
    (e.lift_openEmbedding hf).symm.trans (e'.lift_openEmbedding hf) z = (e.symm.trans e') z := by
  simp [hf.injective.extend_apply e']

@[simp, mfld_simps]
lemma lift_openEmbedding_trans (e e' : PartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm.trans (e'.lift_openEmbedding hf) = e.symm.trans e' := by
  ext z
  · exact e.lift_openEmbedding_trans_apply e' hf z
  · simp [hf.injective.extend_apply e]
  · simp_rw [PartialHomeomorph.trans_source, e.lift_openEmbedding_symm_source, e.symm_source,
      e.lift_openEmbedding_symm, e'.lift_openEmbedding_source]
    refine ⟨fun ⟨hx, ⟨y, hy, hxy⟩⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, hx'⟩ ↦ ⟨hx, mem_image_of_mem f hx'⟩⟩
    rw [mem_preimage]; rw [comp_apply] at hxy
    exact (hf.injective hxy) ▸ hy


/-! product of two partial homeomorphisms -/
section Prod

/-- The product of two partial homeomorphisms, as a partial homeomorphism on the product space. -/
@[simps! (config := mfld_cfg) toPartialEquiv apply,
  simps! -isSimp source target symm_apply]
def prod (eX : PartialHomeomorph X X') (eY : PartialHomeomorph Y Y') :
    PartialHomeomorph (X × Y) (X' × Y') where
  open_source' := eX.open_source.prod eY.open_source
  open_target' := eX.open_target.prod eY.open_target
  continuousOn_toFun := eX.continuousOn.prod_map eY.continuousOn
  continuousOn_invFun := eX.continuousOn_symm.prod_map eY.continuousOn_symm
  toPartialEquiv := eX.toPartialEquiv.prod eY.toPartialEquiv

@[simp] lemma prodWithoutAtlas_eq_prod (eX : PartialHomeomorph X X') (eY : PartialHomeomorph Y Y') :
    (eX.prod_withoutAtlas eY) = (eX.prod' eY) := rfl

@[simp, mfld_simps]
theorem prod_symm (eX : PartialHomeomorph X X') (eY : PartialHomeomorph Y Y') :
    (eX.prod eY).symm = eX.symm.prod eY.symm :=
  rfl

@[simp]
theorem refl_prod_refl :
    (PartialHomeomorph.refl X).prod (PartialHomeomorph.refl Y) = PartialHomeomorph.refl (X × Y) :=
  PartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) univ_prod_univ

@[simp, mfld_simps]
theorem prod_trans (e : PartialHomeomorph X Y) (f : PartialHomeomorph Y Z)
    (e' : PartialHomeomorph X' Y') (f' : PartialHomeomorph Y' Z') :
    (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') :=
  toPartialEquiv_injective <| e.1.prod_trans ..

theorem prod_eq_prod_of_nonempty {eX eX' : PartialHomeomorph X X'} {eY eY' : PartialHomeomorph Y Y'}
    (h : (eX.prod eY).source.Nonempty) : eX.prod eY = eX'.prod eY' ↔ eX = eX' ∧ eY = eY' := by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  haveI : Nonempty X := ⟨x⟩
  haveI : Nonempty X' := ⟨eX x⟩
  haveI : Nonempty Y := ⟨y⟩
  haveI : Nonempty Y' := ⟨eY y⟩
  simp_rw [PartialHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and, Prod.forall, forall_const,
    and_assoc, and_left_comm]

theorem prod_eq_prod_of_nonempty'
    {eX eX' : PartialHomeomorph X X'} {eY eY' : PartialHomeomorph Y Y'}
    (h : (eX'.prod eY').source.Nonempty) : eX.prod eY = eX'.prod eY' ↔ eX = eX' ∧ eY = eY' := by
  rw [eq_comm, prod_eq_prod_of_nonempty h, eq_comm, @eq_comm _ eY']

end Prod

/-! finite product of partial homeomorphisms -/
section Pi

variable {ι : Type*} [Finite ι] {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (Y i)] (ei : ∀ i, PartialHomeomorph (X i) (Y i))

/-- The product of a finite family of `PartialHomeomorph`s. -/
@[simps toPartialEquiv]
def pi : PartialHomeomorph (∀ i, X i) (∀ i, Y i) where
  toPartialEquiv := PartialEquiv.pi fun i => (ei i).toPartialEquiv
  open_source' := isOpen_set_pi finite_univ fun i _ => (ei i).open_source
  open_target' := isOpen_set_pi finite_univ fun i _ => (ei i).open_target
  continuousOn_toFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
  continuousOn_invFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn_symm.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial

end Pi

end PartialHomeomorph
