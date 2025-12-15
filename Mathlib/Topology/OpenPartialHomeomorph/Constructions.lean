/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition
/-!
# Constructions of new partial homeomorphisms from old

## Main definitions

* `OpenPartialHomeomorph.const`: an open partial homeomorphism which is a constant map,
  whose source and target are necessarily singleton sets
* `OpenPartialHomeomorph.subtypeRestr`: restriction to a subtype
* `OpenPartialHomeomorph.prod`: the product of two open partial homeomorphisms,
  as an open partial homeomorphism on the product space
* `OpenPartialHomeomorph.pi`: the product of a finite family of open partial homeomorphisms
* `OpenPartialHomeomorph.disjointUnion`: combine two open partial homeomorphisms with disjoint
  sources and disjoint targets
* `OpenPartialHomeomorph.lift_openEmbedding`: extend an open partial homeomorphism `X → Y`
  under an open embedding `X → X'`, to an open partial homeomorphism `X' → Z`.
  (This is used to define the disjoint union of charted spaces.)
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

/-!
## Constants

`PartialEquiv.const` as an open partial homeomorphism
-/
section const

variable {a : X} {b : Y}

/--
This is `PartialEquiv.single` as an open partial homeomorphism: a constant map,
whose source and target are necessarily singleton sets.
-/
def const (ha : IsOpen {a}) (hb : IsOpen {b}) : OpenPartialHomeomorph X Y where
  toPartialEquiv := PartialEquiv.single a b
  open_source := ha
  open_target := hb
  continuousOn_toFun := by simp
  continuousOn_invFun := by simp

@[simp, mfld_simps]
lemma const_apply (ha : IsOpen {a}) (hb : IsOpen {b}) (x : X) : (const ha hb) x = b := rfl

@[simp, mfld_simps]
lemma const_source (ha : IsOpen {a}) (hb : IsOpen {b}) : (const ha hb).source = {a} := rfl

@[simp, mfld_simps]
lemma const_target (ha : IsOpen {a}) (hb : IsOpen {b}) : (const ha hb).target = {b} := rfl

end const

/-!
## Products

Product of two open partial homeomorphisms
-/
section Prod

/-- The product of two open partial homeomorphisms, as an open partial homeomorphism on the product
space. -/
@[simps! (attr := mfld_simps) -fullyApplied toPartialEquiv apply,
  simps! -isSimp source target symm_apply]
def prod (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y') :
    OpenPartialHomeomorph (X × Y) (X' × Y') where
  open_source := eX.open_source.prod eY.open_source
  open_target := eX.open_target.prod eY.open_target
  continuousOn_toFun := eX.continuousOn.prodMap eY.continuousOn
  continuousOn_invFun := eX.continuousOn_symm.prodMap eY.continuousOn_symm
  toPartialEquiv := eX.toPartialEquiv.prod eY.toPartialEquiv

@[simp, mfld_simps]
theorem prod_symm (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y') :
    (eX.prod eY).symm = eX.symm.prod eY.symm :=
  rfl

@[simp]
theorem refl_prod_refl : (OpenPartialHomeomorph.refl X).prod (OpenPartialHomeomorph.refl Y) =
    OpenPartialHomeomorph.refl (X × Y) :=
  OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) univ_prod_univ

@[simp, mfld_simps]
theorem prod_trans (e : OpenPartialHomeomorph X Y) (f : OpenPartialHomeomorph Y Z)
    (e' : OpenPartialHomeomorph X' Y') (f' : OpenPartialHomeomorph Y' Z') :
    (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') :=
  toPartialEquiv_injective <| e.1.prod_trans ..

theorem prod_eq_prod_of_nonempty {eX eX' : OpenPartialHomeomorph X X'}
    {eY eY' : OpenPartialHomeomorph Y Y'} (h : (eX.prod eY).source.Nonempty) :
    eX.prod eY = eX'.prod eY' ↔ eX = eX' ∧ eY = eY' := by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  haveI : Nonempty X := ⟨x⟩
  haveI : Nonempty X' := ⟨eX x⟩
  haveI : Nonempty Y := ⟨y⟩
  haveI : Nonempty Y' := ⟨eY y⟩
  simp_rw [OpenPartialHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and, Prod.forall, forall_const,
    and_assoc, and_left_comm]

theorem prod_eq_prod_of_nonempty'
    {eX eX' : OpenPartialHomeomorph X X'} {eY eY' : OpenPartialHomeomorph Y Y'}
    (h : (eX'.prod eY').source.Nonempty) : eX.prod eY = eX'.prod eY' ↔ eX = eX' ∧ eY = eY' := by
  rw [eq_comm, prod_eq_prod_of_nonempty h, eq_comm, @eq_comm _ eY']

theorem prod_symm_trans_prod
    (e f : OpenPartialHomeomorph X Y) (e' f' : OpenPartialHomeomorph X' Y') :
    (e.prod e').symm.trans (f.prod f') = (e.symm.trans f).prod (e'.symm.trans f') := by
  simp

end Prod

/-!
## Pi types

Finite indexed products of partial homeomorphisms
-/
section Pi

variable {ι : Type*} [Finite ι] {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (Y i)] (ei : ∀ i, OpenPartialHomeomorph (X i) (Y i))

/-- The product of a finite family of `OpenPartialHomeomorph`s. -/
@[simps! toPartialEquiv apply symm_apply source target]
def pi : OpenPartialHomeomorph (∀ i, X i) (∀ i, Y i) where
  toPartialEquiv := PartialEquiv.pi fun i => (ei i).toPartialEquiv
  open_source := isOpen_set_pi finite_univ fun i _ => (ei i).open_source
  open_target := isOpen_set_pi finite_univ fun i _ => (ei i).open_target
  continuousOn_toFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
  continuousOn_invFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn_symm.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial

end Pi

/-!
## Disjoint union

Combining two partial homeomorphisms using `Set.piecewise`
-/
section Piecewise

/-- Combine two `OpenPartialHomeomorph`s using `Set.piecewise`. The source of the new
`OpenPartialHomeomorph` is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly
for target.  The function sends `e.source ∩ s` to `e.target ∩ t` using `e` and
`e'.source \ s` to `e'.target \ t` using `e'`, and similarly for the inverse function.
To ensure the maps `toFun` and `invFun` are inverse of each other on the new `source` and `target`,
the definition assumes that the sets `s` and `t` are related both by `e.is_image` and `e'.is_image`.
To ensure that the new maps are continuous on `source`/`target`, it also assumes that `e.source` and
`e'.source` meet `frontier s` on the same set and `e x = e' x` on this intersection. -/
@[simps! -fullyApplied toPartialEquiv apply]
def piecewise (e e' : OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) : OpenPartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquiv.piecewise e'.toPartialEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target :=
    e.open_target.ite e'.open_target <| H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq
  continuousOn_toFun := continuousOn_piecewise_ite e.continuousOn e'.continuousOn Hs Heq
  continuousOn_invFun :=
    continuousOn_piecewise_ite e.continuousOn_symm e'.continuousOn_symm
      (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
      (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq)

@[simp]
theorem symm_piecewise (e e' : OpenPartialHomeomorph X Y) {s : Set X} {t : Set Y}
    [∀ x, Decidable (x ∈ s)] [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) :
    (e.piecewise e' s t H H' Hs Heq).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm
        (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
        (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq) :=
  rfl

/-- Combine two `OpenPartialHomeomorph`s with disjoint sources and disjoint targets. We reuse
`OpenPartialHomeomorph.piecewise` then override `toPartialEquiv` to `PartialEquiv.disjointUnion`.
This way we have better definitional equalities for `source` and `target`. -/
def disjointUnion (e e' : OpenPartialHomeomorph X Y) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] (Hs : Disjoint e.source e'.source)
    (Ht : Disjoint e.target e'.target) : OpenPartialHomeomorph X Y :=
  (e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eqOn_empty _ _)).replaceEquiv
    (e.toPartialEquiv.disjointUnion e'.toPartialEquiv Hs Ht)
    (PartialEquiv.disjointUnion_eq_piecewise _ _ _ _).symm

end Piecewise

/-
## Post-composition

Post-composing an `OpenPartialHomeomorph` with a homeomorphism
-/
section transHomeomorph

/-- Postcompose an open partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! -fullyApplied]
def transHomeomorph (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z) : OpenPartialHomeomorph X Z where
  toPartialEquiv := e.toPartialEquiv.transEquiv f'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.preimage f'.symm.continuous
  continuousOn_toFun := f'.continuous.comp_continuousOn e.continuousOn
  continuousOn_invFun := e.symm.continuousOn.comp f'.symm.continuous.continuousOn fun _ => id

theorem transHomeomorph_eq_trans (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z) :
    e.transHomeomorph f' = e.trans f'.toOpenPartialHomeomorph :=
  toPartialEquiv_injective <| PartialEquiv.transEquiv_eq_trans _ _

@[simp, mfld_simps]
theorem transHomeomorph_transHomeomorph (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z)
    (f'' : Z ≃ₜ Z') :
    (e.transHomeomorph f').transHomeomorph f'' = e.transHomeomorph (f'.trans f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc, Homeomorph.trans_toOpenPartialHomeomorph]

@[simp, mfld_simps]
theorem trans_transHomeomorph (e : OpenPartialHomeomorph X Y) (e' : OpenPartialHomeomorph Y Z)
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

variable (e : OpenPartialHomeomorph X Y)
variable {s : Opens X} (hs : Nonempty s)

/-- The restriction of an open partial homeomorphism `e` to an open subset `s` of the domain type
produces an open partial homeomorphism whose domain is the subtype `s`. -/
noncomputable def subtypeRestr : OpenPartialHomeomorph s Y :=
  (s.openPartialHomeomorphSubtypeCoe hs).trans e

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
  · rw [← OpenPartialHomeomorph.symm_target]
    apply OpenPartialHomeomorph.map_source
    rw [OpenPartialHomeomorph.symm_source]
    exact hyV
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
