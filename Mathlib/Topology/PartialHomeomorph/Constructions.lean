/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.PartialHomeomorph.Composition
/-!
# Constructions of new partial homeomorphisms from old

## Main definitions

* `PartialHomeomorph.const`: a partial homeomorphism which is a constant map,
  whose source and target are necessarily singleton sets
* `PartialHomeomorph.subtypeRestr`: restriction to a subtype
* `PartialHomeomorph.prod`: the product of two partial homeomorphisms,
  as a partial homeomorphism on the product space
* `PartialHomeomorph.pi`: the product of a finite family of partial homeomorphisms
* `PartialHomeomorph.disjointUnion`: combine two partial homeomorphisms with disjoint
  sources and disjoint targets
* `PartialHomeomorph.lift_openEmbedding`: extend a partial homeomorphism `X → Y`
  under an embedding `X → X'`, to a partial homeomorphism `X' → Z`.
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace PartialHomeomorph

variable (e : PartialHomeomorph X Y)

/-!
## Constants

`PartialEquiv.const` as an open partial homeomorphism
-/
section const

variable (a : X) (b : Y)

/--
This is `PartialEquiv.single` as a partial homeomorphism: a constant map,
whose source and target are necessarily singleton sets.
-/
def const : PartialHomeomorph X Y where
  toPartialEquiv := PartialEquiv.single a b
  continuousOn_toFun := by simp
  continuousOn_invFun := by simp

@[simp]
lemma const_apply (x : X) : const a b x = b := rfl

@[simp]
lemma const_source : (const a b).source = {a} := rfl

@[simp]
lemma const_target : (const a b).target = {b} := rfl

end const

/-!
## Products

Product of two partial homeomorphisms
-/
section Prod

/-- The product of two partial homeomorphisms, as a partial homeomorphism on the product
space. -/
@[simps! -fullyApplied toPartialEquiv apply, simps! -isSimp source target symm_apply]
def prod (eX : PartialHomeomorph X X') (eY : PartialHomeomorph Y Y') :
    PartialHomeomorph (X × Y) (X' × Y') where
  continuousOn_toFun := eX.continuousOn.prodMap eY.continuousOn
  continuousOn_invFun := eX.continuousOn_symm.prodMap eY.continuousOn_symm
  toPartialEquiv := eX.toPartialEquiv.prod eY.toPartialEquiv

@[simp]
theorem prod_symm (eX : PartialHomeomorph X X') (eY : PartialHomeomorph Y Y') :
    (eX.prod eY).symm = eX.symm.prod eY.symm :=
  rfl

@[simp]
theorem refl_prod_refl : (PartialHomeomorph.refl X).prod (PartialHomeomorph.refl Y) =
    PartialHomeomorph.refl (X × Y) :=
  PartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) univ_prod_univ

@[simp]
theorem prod_trans (e : PartialHomeomorph X Y) (f : PartialHomeomorph Y Z)
    (e' : PartialHomeomorph X' Y') (f' : PartialHomeomorph Y' Z') :
    (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') :=
  toPartialEquiv_injective <| e.1.prod_trans ..

theorem prod_eq_prod_of_nonempty {eX eX' : PartialHomeomorph X X'}
    {eY eY' : PartialHomeomorph Y Y'} (h : (eX.prod eY).source.Nonempty) :
    eX.prod eY = eX'.prod eY' ↔ eX = eX' ∧ eY = eY' := by
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

theorem prod_symm_trans_prod
    (e f : PartialHomeomorph X Y) (e' f' : PartialHomeomorph X' Y') :
    (e.prod e').symm.trans (f.prod f') = (e.symm.trans f).prod (e'.symm.trans f') := by
  simp

end Prod

/-!
## Pi types

Finite indexed products of partial homeomorphisms
-/
section Pi

variable {ι : Type*} [Finite ι] {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (Y i)] (ei : ∀ i, PartialHomeomorph (X i) (Y i))

/-- The product of a finite family of `PartialHomeomorph`s. -/
@[simps! toPartialEquiv apply symm_apply source target]
def pi : PartialHomeomorph (∀ i, X i) (∀ i, Y i) where
  toPartialEquiv := PartialEquiv.pi fun i => (ei i).toPartialEquiv
  continuousOn_toFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
  continuousOn_invFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn_symm.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial

end Pi
/-
## Post-composition

Post-composing a `PartialHomeomorph` with a homeomorphism
-/
section transHomeomorph

/-- Postcompose an partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! -fullyApplied]
def transHomeomorph (e : PartialHomeomorph X Y) (f' : Y ≃ₜ Z) : PartialHomeomorph X Z where
  toPartialEquiv := e.toPartialEquiv.transEquiv f'.toEquiv
  continuousOn_toFun := f'.continuous.comp_continuousOn e.continuousOn
  continuousOn_invFun := e.symm.continuousOn.comp f'.symm.continuous.continuousOn fun _ => id

theorem transHomeomorph_eq_trans (e : PartialHomeomorph X Y) (f' : Y ≃ₜ Z) :
    e.transHomeomorph f' = e.trans f'.toPartialHomeomorph :=
  toPartialEquiv_injective <| PartialEquiv.transEquiv_eq_trans _ _

@[simp, mfld_simps]
theorem transHomeomorph_transHomeomorph (e : PartialHomeomorph X Y) (f' : Y ≃ₜ Z)
    (f'' : Z ≃ₜ Z') :
    (e.transHomeomorph f').transHomeomorph f'' = e.transHomeomorph (f'.trans f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc, Homeomorph.trans_toPartialHomeomorph]

@[simp, mfld_simps]
theorem trans_transHomeomorph (e : PartialHomeomorph X Y) (e' : PartialHomeomorph Y Z)
    (f'' : Z ≃ₜ Z') :
    (e.trans e').transHomeomorph f'' = e.trans (e'.transHomeomorph f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc]

end transHomeomorph

/-!
## Restriction to a subtype

`subtypeRestr`: restriction to a subtype
-/
section subtypeRestr

open TopologicalSpace

variable (e : PartialHomeomorph X Y)
variable {s : Opens X} (hs : Nonempty s)

/-- The restriction of a partial homeomorphism `e` to an open subset `s` of the domain type
produces a partial homeomorphism whose domain is the subtype `s`. -/
noncomputable def subtypeRestr : PartialHomeomorph s Y :=
  (s.partialHomeomorphSubtypeCoe hs).trans e

theorem subtypeRestr_def : e.subtypeRestr hs = (s.openPartialHomeomorphSubtypeCoe hs).trans e :=
  rfl

@[simp, mfld_simps]
theorem subtypeRestr_coe :
    ((e.subtypeRestr hs : OpenPartialHomeomorph s Y) : s → Y) = Set.restrict ↑s (e : X → Y) :=
  rfl

@[simp, mfld_simps]
theorem subtypeRestr_source : (e.subtypeRestr hs).source = (↑) ⁻¹' e.source := by
  simp only [subtypeRestr_def, mfld_simps]

theorem map_subtype_source {x : s} (hxe : (x : X) ∈ e.source) :
    e x ∈ (e.subtypeRestr hs).target := by
  refine ⟨e.map_source hxe, ?_⟩
  rw [s.openPartialHomeomorphSubtypeCoe_target, mem_preimage, e.leftInvOn hxe]
  exact x.prop

lemma subtypeRestr_target_subset (hs : Nonempty s) : (e.subtypeRestr hs).target ⊆ e.target := by
  rw [← e.image_source_eq_target, ← OpenPartialHomeomorph.image_source_eq_target,
    e.subtypeRestr_source]
  rintro z ⟨z₀, hz₀, rfl⟩
  use z₀.val
  simpa

/-- This lemma characterizes the transition functions of an open subset in terms of the transition
functions of the original space. -/
theorem subtypeRestr_symm_trans_subtypeRestr (f f' : OpenPartialHomeomorph X Y) :
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
  refine Setoid.trans (symm_trans_self (s.openPartialHomeomorphSubtypeCoe hs)) ?_
  simp only [mfld_simps, Setoid.refl]

theorem subtypeRestr_symm_apply {U : Opens X} (hU : Nonempty U)
    {y : Y} (hy : y ∈ (e.subtypeRestr hU).target) :
    (Subtype.val ∘ (e.subtypeRestr hU).symm) y = e.symm y := by
  rw [e.eq_symm_apply _ hy.1]
  · change restrict _ e _ = _
    rw [← e.subtypeRestr_coe hU, (e.subtypeRestr hU).right_inv hy]
  · have := OpenPartialHomeomorph.map_target _ hy
    rwa [e.subtypeRestr_source] at this

theorem subtypeRestr_symm_eqOn {U : Opens X} (hU : Nonempty U) :
    EqOn e.symm (Subtype.val ∘ (e.subtypeRestr hU).symm) (e.subtypeRestr hU).target :=
  fun _y hy ↦ (e.subtypeRestr_symm_apply hU hy).symm

theorem subtypeRestr_symm_eqOn_of_le {U V : Opens X} (hU : Nonempty U) (hV : Nonempty V)
    (hUV : U ≤ V) : EqOn (e.subtypeRestr hV).symm (Set.inclusion hUV ∘ (e.subtypeRestr hU).symm)
      (e.subtypeRestr hU).target := by
  set i := Set.inclusion hUV
  intro y hy
  dsimp [OpenPartialHomeomorph.subtypeRestr_def] at hy ⊢
  have hyV : e.symm y ∈ (V.openPartialHomeomorphSubtypeCoe hV).target := by
    rw [Opens.openPartialHomeomorphSubtypeCoe_target] at hy ⊢
    exact hUV hy.2
  refine (V.openPartialHomeomorphSubtypeCoe hV).injOn ?_ trivial ?_
  · simp
  · rw [(V.openPartialHomeomorphSubtypeCoe hV).right_inv hyV]
    change _ = U.openPartialHomeomorphSubtypeCoe hU _
    rw [(U.openPartialHomeomorphSubtypeCoe hU).right_inv hy.2]

end subtypeRestr

/-!
## Extending along an open embedding
-/
section lift_openEmbedding

variable {X X' Z : Type*} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Z]
  [Nonempty Z] {f : X → X'}

/-- Extend an open partial homeomorphism `e : X → Z` to `X' → Z`, using an open embedding
`ι : X → X'`. On `ι(X)`, the extension is specified by `e`; its value elsewhere is arbitrary
(and uninteresting). -/
noncomputable def lift_openEmbedding (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    OpenPartialHomeomorph X' Z where
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
  open_source := hf.isOpenMap _ e.open_source
  open_target := e.open_target
  continuousOn_toFun := by
    by_cases Nonempty X; swap
    · intro x hx; simp_all
    set F := (extend f e (fun _ ↦ (Classical.arbitrary Z))) with F_eq
    have heq : EqOn F (e ∘ (hf.toOpenPartialHomeomorph).symm) (f '' e.source) := by
      intro x ⟨x₀, hx₀, hxx₀⟩
      rw [← hxx₀, F_eq, hf.injective.extend_apply e, comp_apply,
        hf.toOpenPartialHomeomorph_left_inv]
    have : ContinuousOn (e ∘ (hf.toOpenPartialHomeomorph).symm) (f '' e.source) := by
      apply e.continuousOn_toFun.comp; swap
      · intro x' ⟨x, hx, hx'x⟩
        rw [← hx'x, hf.toOpenPartialHomeomorph_left_inv]; exact hx
      have : ContinuousOn (hf.toOpenPartialHomeomorph).symm (f '' univ) :=
        (hf.toOpenPartialHomeomorph).continuousOn_invFun
      exact this.mono <| image_mono <| subset_univ _
    exact ContinuousOn.congr this heq
  continuousOn_invFun := hf.continuous.comp_continuousOn e.continuousOn_invFun

@[simp, mfld_simps]
lemma lift_openEmbedding_toFun (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf) = extend f e (fun _ ↦ (Classical.arbitrary Z)) := rfl

lemma lift_openEmbedding_apply (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) {x : X} :
    (lift_openEmbedding e hf) (f x) = e x := by
  simp_rw [e.lift_openEmbedding_toFun]
  apply hf.injective.extend_apply

@[simp, mfld_simps]
lemma lift_openEmbedding_source (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).source = f '' e.source := rfl

@[simp, mfld_simps]
lemma lift_openEmbedding_target (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).target = e.target := rfl

@[simp, mfld_simps]
lemma lift_openEmbedding_symm (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm = f ∘ e.symm := rfl

@[simp, mfld_simps]
lemma lift_openEmbedding_symm_source (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm.source = e.target := rfl

@[simp, mfld_simps]
lemma lift_openEmbedding_symm_target (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm.target = f '' e.source := by
  rw [OpenPartialHomeomorph.symm_target, e.lift_openEmbedding_source]

lemma lift_openEmbedding_trans_apply
    (e e' : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) (z : Z) :
    (e.lift_openEmbedding hf).symm.trans (e'.lift_openEmbedding hf) z = (e.symm.trans e') z := by
  simp [hf.injective.extend_apply e']

@[simp, mfld_simps]
lemma lift_openEmbedding_trans (e e' : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm.trans (e'.lift_openEmbedding hf) = e.symm.trans e' := by
  ext z
  · exact e.lift_openEmbedding_trans_apply e' hf z
  · simp [hf.injective.extend_apply e]
  · simp_rw [OpenPartialHomeomorph.trans_source, e.lift_openEmbedding_symm_source, e.symm_source,
      e.lift_openEmbedding_symm, e'.lift_openEmbedding_source]
    refine ⟨fun ⟨hx, ⟨y, hy, hxy⟩⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, hx'⟩ ↦ ⟨hx, mem_image_of_mem f hx'⟩⟩
    rw [mem_preimage]; rw [comp_apply] at hxy
    exact (hf.injective hxy) ▸ hy

end lift_openEmbedding

end OpenPartialHomeomorph
