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
  closures of sources and disjoint closures of targets
* `PartialHomeomorph.lift_embedding`: extend a partial homeomorphism `X → Y`
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

`PartialEquiv.const` as a partial homeomorphism
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

/-!
## Disjoint union

Combining two partial homeomorphisms using `Set.piecewise`
-/
section Piecewise

/-- Combine two `PartialHomeomorph`s using `Set.piecewise`. The source of the new
`PartialHomeomorph` is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly
for target.  The function sends `e.source ∩ s` to `e.target ∩ t` using `e` and
`e'.source \ s` to `e'.target \ t` using `e'`, and similarly for the inverse function.
To ensure the maps `toFun` and `invFun` are inverse of each other on the new `source` and `target`,
the definition assumes that the sets `s` and `t` are related both by `e.is_image` and `e'.is_image`.
To ensure that the new maps are continuous on `source`/`target`, it also assumes that `e.source` and
`e'.source` meet `frontier s` on the same set and `e x = e' x` on this intersection. -/
@[simps! -fullyApplied toPartialEquiv apply]
def piecewise (e e' : PartialHomeomorph X Y) (s : Set X) (t : Set Y) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs1 : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Hs2 : e.target ∩ frontier t = e'.target ∩ frontier t)
    (Heq1 : EqOn e e' (e.source ∩ frontier s))
    (Heq2 : EqOn (↑e.symm) (↑e'.symm) (e.target ∩ frontier t)) : PartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquiv.piecewise e'.toPartialEquiv s t H H'
  continuousOn_toFun := continuousOn_piecewise_ite e.continuousOn e'.continuousOn Hs1 Heq1
  continuousOn_invFun :=
    continuousOn_piecewise_ite e.continuousOn_symm e'.continuousOn_symm Hs2 Heq2

@[simp]
theorem symm_piecewise (e e' : PartialHomeomorph X Y) {s : Set X} {t : Set Y}
    [∀ x, Decidable (x ∈ s)] [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs1 : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Hs2 : e.target ∩ frontier t = e'.target ∩ frontier t)
    (Heq1 : EqOn e e' (e.source ∩ frontier s))
    (Heq2 : EqOn (↑e.symm) (↑e'.symm) (e.target ∩ frontier t)) :
    (e.piecewise e' s t H H' Hs1 Hs2 Heq1 Heq2).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm Hs2 Hs1 Heq2 Heq1 :=
  rfl

/-- Combine two `PartialHomeomorph`s with disjoint closures of sources and disjoint closures of
targets. -/
def disjointUnion (e e' : PartialHomeomorph X Y) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] (Hs : Disjoint (closure e.source) (closure e'.source))
    (Ht : Disjoint (closure e.target) (closure e'.target)) : PartialHomeomorph X Y where
  toPartialEquiv := PartialEquiv.disjointUnion e.toPartialEquiv e'.toPartialEquiv
      (Hs.mono subset_closure subset_closure) (Ht.mono subset_closure subset_closure)
  continuousOn_toFun := by
    simp only [PartialEquiv.disjointUnion_apply, toFun_eq_coe, PartialEquiv.disjointUnion_source]
    apply (e.continuousOn.congr (fun _ ↦ piecewise_eq_of_mem _ _ _)).union_of_disjoint_closure _ Hs
    apply e'.continuousOn.congr
    intro x hx
    apply piecewise_eq_of_notMem
    intro hx'
    exact Hs.notMem_of_mem_right (subset_closure hx) (subset_closure hx')
  continuousOn_invFun := by
    simp only [PartialEquiv.invFun_as_coe, PartialEquiv.disjointUnion_symm_apply, coe_coe_symm,
      PartialEquiv.disjointUnion_target]
    apply ContinuousOn.union_of_disjoint_closure _ _ Ht
    · apply e.symm.continuousOn.congr
      intro x hx
      exact piecewise_eq_of_mem _ _ _ (e.symm_source ▸ hx)
    · apply e'.symm.continuousOn.congr
      intro x hx
      apply piecewise_eq_of_notMem
      intro hx'
      exact Ht.notMem_of_mem_right (subset_closure (e'.symm_source ▸ hx)) (subset_closure hx')


end Piecewise

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
variable {s : Set X} (hs : Nonempty s)

/-- The restriction of a partial homeomorphism `e` to a subset `s` of the domain type
produces a partial homeomorphism whose domain is the subtype `s`. -/
noncomputable def subtypeRestr : PartialHomeomorph s Y :=
  (s.partialHomeomorphSubtypeCoe hs).trans e

theorem subtypeRestr_def : e.subtypeRestr hs = (s.partialHomeomorphSubtypeCoe hs).trans e :=
  rfl

@[simp]
theorem subtypeRestr_coe :
    ((e.subtypeRestr hs : PartialHomeomorph s Y) : s → Y) = Set.restrict ↑s (e : X → Y) :=
  rfl

@[simp]
theorem subtypeRestr_source : (e.subtypeRestr hs).source = (↑) ⁻¹' e.source := by
  simp [subtypeRestr_def]

theorem map_subtype_source {x : s} (hxe : (x : X) ∈ e.source) :
    e x ∈ (e.subtypeRestr hs).target := by
  refine ⟨e.map_source hxe, ?_⟩
  rw [s.partialHomeomorphSubtypeCoe_target, mem_preimage, e.leftInvOn hxe]
  exact x.prop

lemma subtypeRestr_target_subset (hs : Nonempty s) : (e.subtypeRestr hs).target ⊆ e.target := by
  rw [← e.image_source_eq_target, ← PartialHomeomorph.image_source_eq_target,
    e.subtypeRestr_source]
  rintro z ⟨z₀, hz₀, rfl⟩
  use z₀.val
  simpa

theorem subtypeRestr_symm_apply {U : Set X} (hU : Nonempty U)
    {y : Y} (hy : y ∈ (e.subtypeRestr hU).target) :
    (Subtype.val ∘ (e.subtypeRestr hU).symm) y = e.symm y := by
  rw [e.eq_symm_apply _ hy.1]
  · change restrict _ e _ = _
    rw [← e.subtypeRestr_coe hU, (e.subtypeRestr hU).right_inv hy]
  · have := PartialHomeomorph.map_target _ hy
    rwa [e.subtypeRestr_source] at this

theorem subtypeRestr_symm_eqOn {U : Set X} (hU : Nonempty U) :
    EqOn e.symm (Subtype.val ∘ (e.subtypeRestr hU).symm) (e.subtypeRestr hU).target :=
  fun _y hy ↦ (e.subtypeRestr_symm_apply hU hy).symm

theorem subtypeRestr_symm_eqOn_of_le {U V : Set X} (hU : Nonempty U) (hV : Nonempty V)
    (hUV : U ≤ V) : EqOn (e.subtypeRestr hV).symm (Set.inclusion hUV ∘ (e.subtypeRestr hU).symm)
      (e.subtypeRestr hU).target := by
  set i := Set.inclusion hUV
  intro y hy
  dsimp [PartialHomeomorph.subtypeRestr_def] at hy ⊢
  have hyV : e.symm y ∈ (V.partialHomeomorphSubtypeCoe hV).target := by
    rw [partialHomeomorphSubtypeCoe_target] at hy ⊢
    exact hUV hy.2
  refine (V.partialHomeomorphSubtypeCoe hV).injOn ?_ trivial ?_
  · simp
  · rw [(V.partialHomeomorphSubtypeCoe hV).right_inv hyV]
    change _ = U.partialHomeomorphSubtypeCoe hU _
    rw [(U.partialHomeomorphSubtypeCoe hU).right_inv hy.2]

end subtypeRestr

/-!
## Extending along an embedding
-/
section lift_embedding

variable {X X' Z : Type*} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Z]
  [Nonempty Z] {f : X → X'}

/-- Extend a partial homeomorphism `e : X → Z` to `X' → Z`, using an embedding
`ι : X → X'`. On `ι(X)`, the extension is specified by `e`; its value elsewhere is arbitrary
(and uninteresting). -/
noncomputable def lift_embedding (e : PartialHomeomorph X Z) (hf : IsEmbedding f) :
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
  continuousOn_toFun := by
    by_cases Nonempty X; swap
    · intro x hx; simp_all
    set F := (extend f e (fun _ ↦ (Classical.arbitrary Z))) with F_eq
    have heq : EqOn F (e ∘ (hf.toPartialHomeomorph).symm) (f '' e.source) := by
      intro x ⟨x₀, hx₀, hxx₀⟩
      rw [← hxx₀, F_eq, hf.injective.extend_apply e, comp_apply,
        hf.toPartialHomeomorph_left_inv]
    have : ContinuousOn (e ∘ (hf.toPartialHomeomorph).symm) (f '' e.source) := by
      apply e.continuousOn_toFun.comp; swap
      · intro x' ⟨x, hx, hx'x⟩
        rw [← hx'x, hf.toPartialHomeomorph_left_inv]; exact hx
      have : ContinuousOn (hf.toPartialHomeomorph).symm (f '' univ) :=
        (hf.toPartialHomeomorph).continuousOn_invFun
      exact this.mono <| image_mono <| subset_univ _
    exact ContinuousOn.congr this heq
  continuousOn_invFun := hf.continuous.comp_continuousOn e.continuousOn_invFun

@[simp]
lemma lift_embedding_toFun (e : PartialHomeomorph X Z) (hf : IsEmbedding f) :
    (e.lift_embedding hf) = extend f e (fun _ ↦ (Classical.arbitrary Z)) := rfl

lemma lift_embedding_apply (e : PartialHomeomorph X Z) (hf : IsEmbedding f) {x : X} :
    (lift_embedding e hf) (f x) = e x := by
  simp_rw [e.lift_embedding_toFun]
  apply hf.injective.extend_apply

@[simp]
lemma lift_embedding_source (e : PartialHomeomorph X Z) (hf : IsEmbedding f) :
    (e.lift_embedding hf).source = f '' e.source := rfl

@[simp]
lemma lift_embedding_target (e : PartialHomeomorph X Z) (hf : IsEmbedding f) :
    (e.lift_embedding hf).target = e.target := rfl

@[simp]
lemma lift_embedding_symm (e : PartialHomeomorph X Z) (hf : IsEmbedding f) :
    (e.lift_embedding hf).symm = f ∘ e.symm := rfl

@[simp]
lemma lift_embedding_symm_source (e : PartialHomeomorph X Z) (hf : IsEmbedding f) :
    (e.lift_embedding hf).symm.source = e.target := rfl

@[simp]
lemma lift_embedding_symm_target (e : PartialHomeomorph X Z) (hf : IsEmbedding f) :
    (e.lift_embedding hf).symm.target = f '' e.source := by
  rw [PartialHomeomorph.symm_target, e.lift_embedding_source]

lemma lift_embedding_trans_apply
    (e e' : PartialHomeomorph X Z) (hf : IsEmbedding f) (z : Z) :
    (e.lift_embedding hf).symm.trans (e'.lift_embedding hf) z = (e.symm.trans e') z := by
  simp [hf.injective.extend_apply e']

@[simp]
lemma lift_embedding_trans (e e' : PartialHomeomorph X Z) (hf : IsEmbedding f) :
    (e.lift_embedding hf).symm.trans (e'.lift_embedding hf) = e.symm.trans e' := by
  ext z
  · exact e.lift_embedding_trans_apply e' hf z
  · simp [hf.injective.extend_apply e]
  · simp_rw [PartialHomeomorph.trans_source, e.lift_embedding_symm_source, e.symm_source,
      e.lift_embedding_symm, e'.lift_embedding_source]
    refine ⟨fun ⟨hx, ⟨y, hy, hxy⟩⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, hx'⟩ ↦ ⟨hx, mem_image_of_mem f hx'⟩⟩
    rw [mem_preimage]; rw [comp_apply] at hxy
    exact (hf.injective hxy) ▸ hy

end lift_embedding

end PartialHomeomorph
