/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yury Kudryashov
-/
import Mathlib.Tactic.TFAE
import Mathlib.Topology.ContinuousOn

/-!
# Inseparable points in a topological space

In this file we prove basic properties of the following notions defined elsewhere.

* `Specializes` (notation: `x ⤳ y`) : a relation saying that `𝓝 x ≤ 𝓝 y`;

* `Inseparable`: a relation saying that two points in a topological space have the same
  neighbourhoods; equivalently, they can't be separated by an open set;

* `InseparableSetoid X`: same relation, as a `Setoid`;

* `SeparationQuotient X`: the quotient of `X` by its `InseparableSetoid`.

We also prove various basic properties of the relation `Inseparable`.

## Notations

- `x ⤳ y`: notation for `Specializes x y`;
- `x ~ᵢ y` is used as a local notation for `Inseparable x y`;
- `𝓝 x` is the neighbourhoods filter `nhds x` of a point `x`, defined elsewhere.

## Tags

topological space, separation setoid
-/


open Set Filter Function Topology List

variable {X Y Z α ι : Type*} {π : ι → Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [∀ i, TopologicalSpace (π i)] {x y z : X} {s : Set X} {f g : X → Y}

/-!
### `Specializes` relation
-/

/-- A collection of equivalent definitions of `x ⤳ y`. The public API is given by `iff` lemmas
below. -/
theorem specializes_TFAE (x y : X) :
    TFAE [x ⤳ y,
      pure x ≤ 𝓝 y,
      ∀ s : Set X , IsOpen s → y ∈ s → x ∈ s,
      ∀ s : Set X , IsClosed s → x ∈ s → y ∈ s,
      y ∈ closure ({ x } : Set X),
      closure ({ y } : Set X) ⊆ closure { x },
      ClusterPt y (pure x)] := by
  tfae_have 1 → 2
  · exact (pure_le_nhds _).trans
  tfae_have 2 → 3
  · exact fun h s hso hy => h (hso.mem_nhds hy)
  tfae_have 3 → 4
  · exact fun h s hsc hx => of_not_not fun hy => h sᶜ hsc.isOpen_compl hy hx
  tfae_have 4 → 5
  · exact fun h => h _ isClosed_closure (subset_closure <| mem_singleton _)
  tfae_have 6 ↔ 5
  · exact isClosed_closure.closure_subset_iff.trans singleton_subset_iff
  tfae_have 5 ↔ 7
  · rw [mem_closure_iff_clusterPt, principal_singleton]
  tfae_have 5 → 1
  · refine fun h => (nhds_basis_opens _).ge_iff.2 ?_
    rintro s ⟨hy, ho⟩
    rcases mem_closure_iff.1 h s ho hy with ⟨z, hxs, rfl : z = x⟩
    exact ho.mem_nhds hxs
  tfae_finish

theorem specializes_iff_nhds : x ⤳ y ↔ 𝓝 x ≤ 𝓝 y :=
  Iff.rfl

theorem Specializes.not_disjoint (h : x ⤳ y) : ¬Disjoint (𝓝 x) (𝓝 y) := fun hd ↦
  absurd (hd.mono_right h) <| by simp [NeBot.ne']

theorem specializes_iff_pure : x ⤳ y ↔ pure x ≤ 𝓝 y :=
  (specializes_TFAE x y).out 0 1

alias ⟨Specializes.nhds_le_nhds, _⟩ := specializes_iff_nhds

alias ⟨Specializes.pure_le_nhds, _⟩ := specializes_iff_pure

theorem ker_nhds_eq_specializes : (𝓝 x).ker = {y | y ⤳ x} := by
  ext; simp [specializes_iff_pure, le_def]

theorem specializes_iff_forall_open : x ⤳ y ↔ ∀ s : Set X, IsOpen s → y ∈ s → x ∈ s :=
  (specializes_TFAE x y).out 0 2

theorem Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (hy : y ∈ s) : x ∈ s :=
  specializes_iff_forall_open.1 h s hs hy

theorem IsOpen.not_specializes (hs : IsOpen s) (hx : x ∉ s) (hy : y ∈ s) : ¬x ⤳ y := fun h =>
  hx <| h.mem_open hs hy

theorem specializes_iff_forall_closed : x ⤳ y ↔ ∀ s : Set X, IsClosed s → x ∈ s → y ∈ s :=
  (specializes_TFAE x y).out 0 3

theorem Specializes.mem_closed (h : x ⤳ y) (hs : IsClosed s) (hx : x ∈ s) : y ∈ s :=
  specializes_iff_forall_closed.1 h s hs hx

theorem IsClosed.not_specializes (hs : IsClosed s) (hx : x ∈ s) (hy : y ∉ s) : ¬x ⤳ y := fun h =>
  hy <| h.mem_closed hs hx

theorem specializes_iff_mem_closure : x ⤳ y ↔ y ∈ closure ({x} : Set X) :=
  (specializes_TFAE x y).out 0 4

alias ⟨Specializes.mem_closure, _⟩ := specializes_iff_mem_closure

theorem specializes_iff_closure_subset : x ⤳ y ↔ closure ({y} : Set X) ⊆ closure {x} :=
  (specializes_TFAE x y).out 0 5

alias ⟨Specializes.closure_subset, _⟩ := specializes_iff_closure_subset

theorem specializes_iff_clusterPt : x ⤳ y ↔ ClusterPt y (pure x) :=
  (specializes_TFAE x y).out 0 6

theorem Filter.HasBasis.specializes_iff {ι} {p : ι → Prop} {s : ι → Set X}
    (h : (𝓝 y).HasBasis p s) : x ⤳ y ↔ ∀ i, p i → x ∈ s i :=
  specializes_iff_pure.trans h.ge_iff

theorem specializes_rfl : x ⤳ x := le_rfl

@[refl]
theorem specializes_refl (x : X) : x ⤳ x :=
  specializes_rfl

@[trans]
theorem Specializes.trans : x ⤳ y → y ⤳ z → x ⤳ z :=
  le_trans

theorem specializes_of_eq (e : x = y) : x ⤳ y :=
  e ▸ specializes_refl x

theorem specializes_of_nhdsWithin (h₁ : 𝓝[s] x ≤ 𝓝[s] y) (h₂ : x ∈ s) : x ⤳ y :=
  specializes_iff_pure.2 <|
    calc
      pure x ≤ 𝓝[s] x := le_inf (pure_le_nhds _) (le_principal_iff.2 h₂)
      _ ≤ 𝓝[s] y := h₁
      _ ≤ 𝓝 y := inf_le_left

theorem Specializes.map_of_continuousAt (h : x ⤳ y) (hy : ContinuousAt f y) : f x ⤳ f y :=
  specializes_iff_pure.2 fun _s hs =>
    mem_pure.2 <| mem_preimage.1 <| mem_of_mem_nhds <| hy.mono_left h hs

theorem Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳ f y :=
  h.map_of_continuousAt hf.continuousAt

theorem Inducing.specializes_iff (hf : Inducing f) : f x ⤳ f y ↔ x ⤳ y := by
  simp only [specializes_iff_mem_closure, hf.closure_eq_preimage_closure_image, image_singleton,
    mem_preimage]

theorem subtype_specializes_iff {p : X → Prop} (x y : Subtype p) : x ⤳ y ↔ (x : X) ⤳ y :=
  inducing_subtype_val.specializes_iff.symm

@[simp]
theorem specializes_prod {x₁ x₂ : X} {y₁ y₂ : Y} : (x₁, y₁) ⤳ (x₂, y₂) ↔ x₁ ⤳ x₂ ∧ y₁ ⤳ y₂ := by
  simp only [Specializes, nhds_prod_eq, prod_le_prod]

theorem Specializes.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ⤳ x₂) (hy : y₁ ⤳ y₂) :
    (x₁, y₁) ⤳ (x₂, y₂) :=
  specializes_prod.2 ⟨hx, hy⟩

theorem Specializes.fst {a b : X × Y} (h : a ⤳ b) : a.1 ⤳ b.1 := (specializes_prod.1 h).1
theorem Specializes.snd {a b : X × Y} (h : a ⤳ b) : a.2 ⤳ b.2 := (specializes_prod.1 h).2

@[simp]
theorem specializes_pi {f g : ∀ i, π i} : f ⤳ g ↔ ∀ i, f i ⤳ g i := by
  simp only [Specializes, nhds_pi, pi_le_pi]

theorem not_specializes_iff_exists_open : ¬x ⤳ y ↔ ∃ S : Set X, IsOpen S ∧ y ∈ S ∧ x ∉ S := by
  rw [specializes_iff_forall_open]
  push_neg
  rfl

theorem not_specializes_iff_exists_closed : ¬x ⤳ y ↔ ∃ S : Set X, IsClosed S ∧ x ∈ S ∧ y ∉ S := by
  rw [specializes_iff_forall_closed]
  push_neg
  rfl

theorem IsOpen.continuous_piecewise_of_specializes [DecidablePred (· ∈ s)] (hs : IsOpen s)
    (hf : Continuous f) (hg : Continuous g) (hspec : ∀ x, f x ⤳ g x) :
    Continuous (s.piecewise f g) := by
  have : ∀ U, IsOpen U → g ⁻¹' U ⊆ f ⁻¹' U := fun U hU x hx ↦ (hspec x).mem_open hU hx
  rw [continuous_def]
  intro U hU
  rw [piecewise_preimage, ite_eq_of_subset_right _ (this U hU)]
  exact hU.preimage hf |>.inter hs |>.union (hU.preimage hg)

theorem IsClosed.continuous_piecewise_of_specializes [DecidablePred (· ∈ s)] (hs : IsClosed s)
    (hf : Continuous f) (hg : Continuous g) (hspec : ∀ x, g x ⤳ f x) :
    Continuous (s.piecewise f g) := by
  simpa only [piecewise_compl] using hs.isOpen_compl.continuous_piecewise_of_specializes hg hf hspec

attribute [local instance] specializationPreorder

/-- A continuous function is monotone with respect to the specialization preorders on the domain and
the codomain. -/
theorem Continuous.specialization_monotone (hf : Continuous f) : Monotone f :=
  fun _ _ h => h.map hf

lemma closure_singleton_eq_Iic (x : X) : closure {x} = Iic x :=
  Set.ext fun _ ↦ specializes_iff_mem_closure.symm

/-- A subset `S` of a topological space is stable under specialization
if `x ∈ S → y ∈ S` for all `x ⤳ y`. -/
def StableUnderSpecialization (s : Set X) : Prop :=
  ∀ ⦃x y⦄, x ⤳ y → x ∈ s → y ∈ s

/-- A subset `S` of a topological space is stable under specialization
if `x ∈ S → y ∈ S` for all `y ⤳ x`. -/
def StableUnderGeneralization (s : Set X) : Prop :=
  ∀ ⦃x y⦄, y ⤳ x → x ∈ s → y ∈ s

example {s : Set X} : StableUnderSpecialization s ↔ IsLowerSet s := Iff.rfl
example {s : Set X} : StableUnderGeneralization s ↔ IsUpperSet s := Iff.rfl

lemma IsClosed.stableUnderSpecialization {s : Set X} (hs : IsClosed s) :
    StableUnderSpecialization s :=
  fun _ _ e ↦ e.mem_closed hs

lemma IsOpen.stableUnderGeneralization {s : Set X} (hs : IsOpen s) :
    StableUnderGeneralization s :=
  fun _ _ e ↦ e.mem_open hs

@[simp]
lemma stableUnderSpecialization_compl_iff {s : Set X} :
    StableUnderSpecialization sᶜ ↔ StableUnderGeneralization s :=
  isLowerSet_compl

@[simp]
lemma stableUnderGeneralization_compl_iff {s : Set X} :
    StableUnderGeneralization sᶜ ↔ StableUnderSpecialization s :=
  isUpperSet_compl

alias ⟨_, StableUnderGeneralization.compl⟩ := stableUnderSpecialization_compl_iff
alias ⟨_, StableUnderSpecialization.compl⟩ := stableUnderGeneralization_compl_iff

lemma stableUnderSpecialization_univ : StableUnderSpecialization (univ : Set X) := isLowerSet_univ
lemma stableUnderSpecialization_empty : StableUnderSpecialization (∅ : Set X) := isLowerSet_empty
lemma stableUnderGeneralization_univ : StableUnderGeneralization (univ : Set X) := isUpperSet_univ
lemma stableUnderGeneralization_empty : StableUnderGeneralization (∅ : Set X) := isUpperSet_empty

lemma stableUnderSpecialization_sUnion (S : Set (Set X))
    (H : ∀ s ∈ S, StableUnderSpecialization s) : StableUnderSpecialization (⋃₀ S) :=
  isLowerSet_sUnion H

lemma stableUnderSpecialization_sInter (S : Set (Set X))
    (H : ∀ s ∈ S, StableUnderSpecialization s) : StableUnderSpecialization (⋂₀ S) :=
  isLowerSet_sInter H

lemma stableUnderGeneralization_sUnion (S : Set (Set X))
    (H : ∀ s ∈ S, StableUnderGeneralization s) : StableUnderGeneralization (⋃₀ S) :=
  isUpperSet_sUnion H

lemma stableUnderGeneralization_sInter (S : Set (Set X))
    (H : ∀ s ∈ S, StableUnderGeneralization s) : StableUnderGeneralization (⋂₀ S) :=
  isUpperSet_sInter H

lemma stableUnderSpecialization_iUnion {ι : Sort*} (S : ι → Set X)
    (H : ∀ i, StableUnderSpecialization (S i)) : StableUnderSpecialization (⋃ i, S i) :=
  isLowerSet_iUnion H

lemma stableUnderSpecialization_iInter {ι : Sort*} (S : ι → Set X)
    (H : ∀ i, StableUnderSpecialization (S i)) : StableUnderSpecialization (⋂ i, S i) :=
  isLowerSet_iInter H

lemma stableUnderGeneralization_iUnion {ι : Sort*} (S : ι → Set X)
    (H : ∀ i, StableUnderGeneralization (S i)) : StableUnderGeneralization (⋃ i, S i) :=
  isUpperSet_iUnion H

lemma stableUnderGeneralization_iInter {ι : Sort*} (S : ι → Set X)
    (H : ∀ i, StableUnderGeneralization (S i)) : StableUnderGeneralization (⋂ i, S i) :=
  isUpperSet_iInter H

lemma Union_closure_singleton_eq_iff {s : Set X} :
    (⋃ x ∈ s, closure {x}) = s ↔ StableUnderSpecialization s :=
  show _ ↔ IsLowerSet s by simp only [closure_singleton_eq_Iic, ← lowerClosure_eq, coe_lowerClosure]

lemma stableUnderSpecialization_iff_Union_eq {s : Set X} :
    StableUnderSpecialization s ↔ (⋃ x ∈ s, closure {x}) = s :=
  Union_closure_singleton_eq_iff.symm

alias ⟨StableUnderSpecialization.Union_eq, _⟩ := stableUnderSpecialization_iff_Union_eq

/-- A set is stable under specialization iff it is a union of closed sets. -/
lemma stableUnderSpecialization_iff_exists_sUnion_eq {s : Set X} :
    StableUnderSpecialization s ↔ ∃ (S : Set (Set X)), (∀ s ∈ S, IsClosed s) ∧ ⋃₀ S = s := by
  refine ⟨fun H ↦ ⟨(fun x : X ↦ closure {x}) '' s, ?_, ?_⟩, fun ⟨S, hS, e⟩ ↦ e ▸
    stableUnderSpecialization_sUnion S (fun x hx ↦ (hS x hx).stableUnderSpecialization)⟩
  · rintro _ ⟨_, _, rfl⟩; exact isClosed_closure
  · conv_rhs => rw [← H.Union_eq]
    simp

/-- A set is stable under generalization iff it is an intersection of open sets. -/
lemma stableUnderGeneralization_iff_exists_sInter_eq {s : Set X} :
    StableUnderGeneralization s ↔ ∃ (S : Set (Set X)), (∀ s ∈ S, IsOpen s) ∧ ⋂₀ S = s := by
  refine ⟨?_, fun ⟨S, hS, e⟩ ↦ e ▸
    stableUnderGeneralization_sInter S (fun x hx ↦ (hS x hx).stableUnderGeneralization)⟩
  rw [← stableUnderSpecialization_compl_iff, stableUnderSpecialization_iff_exists_sUnion_eq]
  exact fun ⟨S, h₁, h₂⟩ ↦ ⟨(·ᶜ) '' S, fun s ⟨t, ht, e⟩ ↦ e ▸ (h₁ t ht).isOpen_compl,
    compl_injective ((sUnion_eq_compl_sInter_compl S).symm.trans h₂)⟩

lemma StableUnderSpecialization.preimage {s : Set Y}
    (hs : StableUnderSpecialization s) (hf : Continuous f) :
    StableUnderSpecialization (f ⁻¹' s) :=
  IsLowerSet.preimage hs hf.specialization_monotone

lemma StableUnderGeneralization.preimage {s : Set Y}
    (hs : StableUnderGeneralization s) (hf : Continuous f) :
    StableUnderGeneralization (f ⁻¹' s) :=
  IsUpperSet.preimage hs hf.specialization_monotone

/-- A map `f` between topological spaces is specializing if specializations lifts along `f`,
i.e. for each `f x' ⤳ y` there is some `x` with `x' ⤳ x` whose image is `y`. -/
def SpecializingMap (f : X → Y) : Prop :=
  Relation.Fibration (flip (· ⤳ ·)) (flip (· ⤳ ·)) f

/-- A map `f` between topological spaces is generalizing if generalizations lifts along `f`,
i.e. for each `y ⤳ f x'` there is some `x ⤳ x'` whose image is `y`. -/
def GeneralizingMap (f : X → Y) : Prop :=
  Relation.Fibration (· ⤳ ·) (· ⤳ ·) f

lemma specializingMap_iff_closure_singleton_subset :
    SpecializingMap f ↔ ∀ x, closure {f x} ⊆ f '' closure {x} := by
  simp only [SpecializingMap, Relation.Fibration, flip, specializes_iff_mem_closure]; rfl

alias ⟨SpecializingMap.closure_singleton_subset, _⟩ := specializingMap_iff_closure_singleton_subset

lemma SpecializingMap.stableUnderSpecialization_image (hf : SpecializingMap f)
    {s : Set X} (hs : StableUnderSpecialization s) : StableUnderSpecialization (f '' s) :=
  IsLowerSet.image_fibration hf hs

alias StableUnderSpecialization.image := SpecializingMap.stableUnderSpecialization_image

lemma specializingMap_iff_stableUnderSpecialization_image_singleton :
    SpecializingMap f ↔ ∀ x, StableUnderSpecialization (f '' closure {x}) := by
  simpa only [closure_singleton_eq_Iic] using Relation.fibration_iff_isLowerSet_image_Iic

lemma specializingMap_iff_stableUnderSpecialization_image :
    SpecializingMap f ↔ ∀ s, StableUnderSpecialization s → StableUnderSpecialization (f '' s) :=
  Relation.fibration_iff_isLowerSet_image

lemma specializingMap_iff_closure_singleton (hf : Continuous f) :
    SpecializingMap f ↔ ∀ x, f '' closure {x} = closure {f x} := by
  simpa only [closure_singleton_eq_Iic] using
    Relation.fibration_iff_image_Iic hf.specialization_monotone

lemma specializingMap_iff_isClosed_image_closure_singleton (hf : Continuous f) :
    SpecializingMap f ↔ ∀ x, IsClosed (f '' closure {x}) := by
  refine ⟨fun h x ↦ ?_, fun h ↦ specializingMap_iff_stableUnderSpecialization_image_singleton.mpr
    (fun x ↦ (h x).stableUnderSpecialization)⟩
  rw [(specializingMap_iff_closure_singleton hf).mp h x]
  exact isClosed_closure

lemma IsClosedMap.specializingMap (hf : IsClosedMap f) : SpecializingMap f :=
  specializingMap_iff_stableUnderSpecialization_image_singleton.mpr $
    fun _ ↦ (hf _ isClosed_closure).stableUnderSpecialization

lemma Inducing.specializingMap (hf : Inducing f) (h : StableUnderSpecialization (range f)) :
    SpecializingMap f := by
  intros x y e
  obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩
  exact ⟨_, hf.specializes_iff.mp e, rfl⟩

lemma Inducing.generalizingMap (hf : Inducing f) (h : StableUnderGeneralization (range f)) :
    GeneralizingMap f := by
  intros x y e
  obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩
  exact ⟨_, hf.specializes_iff.mp e, rfl⟩

lemma OpenEmbedding.generalizingMap (hf : OpenEmbedding f) : GeneralizingMap f :=
  hf.toInducing.generalizingMap hf.isOpen_range.stableUnderGeneralization

lemma SpecializingMap.stableUnderSpecialization_range (h : SpecializingMap f) :
    StableUnderSpecialization (range f) :=
  @image_univ _ _ f ▸ stableUnderSpecialization_univ.image h

lemma GeneralizingMap.stableUnderGeneralization_image (hf : GeneralizingMap f) {s : Set X}
    (hs : StableUnderGeneralization s) : StableUnderGeneralization (f '' s) :=
  IsUpperSet.image_fibration hf hs

lemma GeneralizingMap_iff_stableUnderGeneralization_image :
    GeneralizingMap f ↔ ∀ s, StableUnderGeneralization s → StableUnderGeneralization (f '' s) :=
  Relation.fibration_iff_isUpperSet_image

alias StableUnderGeneralization.image := GeneralizingMap.stableUnderGeneralization_image

lemma GeneralizingMap.stableUnderGeneralization_range (h : GeneralizingMap f) :
    StableUnderGeneralization (range f) :=
  @image_univ _ _ f ▸ stableUnderGeneralization_univ.image h

/-!
### `Inseparable` relation
-/

@[inherit_doc] local infixl:0 " ~ᵢ " => Inseparable

theorem inseparable_def : (x ~ᵢ y) ↔ 𝓝 x = 𝓝 y :=
  Iff.rfl

theorem inseparable_iff_specializes_and : (x ~ᵢ y) ↔ x ⤳ y ∧ y ⤳ x :=
  le_antisymm_iff

theorem Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y := h.le

theorem Inseparable.specializes' (h : x ~ᵢ y) : y ⤳ x := h.ge

theorem Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x ~ᵢ y :=
  le_antisymm h₁ h₂

theorem inseparable_iff_forall_open : (x ~ᵢ y) ↔ ∀ s : Set X, IsOpen s → (x ∈ s ↔ y ∈ s) := by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_open, ← forall_and, ← iff_def,
    Iff.comm]

theorem not_inseparable_iff_exists_open :
    ¬(x ~ᵢ y) ↔ ∃ s : Set X, IsOpen s ∧ Xor' (x ∈ s) (y ∈ s) := by
  simp [inseparable_iff_forall_open, ← xor_iff_not_iff]

theorem inseparable_iff_forall_closed : (x ~ᵢ y) ↔ ∀ s : Set X, IsClosed s → (x ∈ s ↔ y ∈ s) := by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_closed, ← forall_and, ←
    iff_def]

theorem inseparable_iff_mem_closure :
    (x ~ᵢ y) ↔ x ∈ closure ({y} : Set X) ∧ y ∈ closure ({x} : Set X) :=
  inseparable_iff_specializes_and.trans <| by simp only [specializes_iff_mem_closure, and_comm]

theorem inseparable_iff_closure_eq : (x ~ᵢ y) ↔ closure ({x} : Set X) = closure {y} := by
  simp only [inseparable_iff_specializes_and, specializes_iff_closure_subset, ← subset_antisymm_iff,
    eq_comm]

theorem inseparable_of_nhdsWithin_eq (hx : x ∈ s) (hy : y ∈ s) (h : 𝓝[s] x = 𝓝[s] y) : x ~ᵢ y :=
  (specializes_of_nhdsWithin h.le hx).antisymm (specializes_of_nhdsWithin h.ge hy)

theorem Inducing.inseparable_iff (hf : Inducing f) : (f x ~ᵢ f y) ↔ (x ~ᵢ y) := by
  simp only [inseparable_iff_specializes_and, hf.specializes_iff]

theorem subtype_inseparable_iff {p : X → Prop} (x y : Subtype p) : (x ~ᵢ y) ↔ ((x : X) ~ᵢ y) :=
  inducing_subtype_val.inseparable_iff.symm

@[simp] theorem inseparable_prod {x₁ x₂ : X} {y₁ y₂ : Y} :
    ((x₁, y₁) ~ᵢ (x₂, y₂)) ↔ (x₁ ~ᵢ x₂) ∧ (y₁ ~ᵢ y₂) := by
  simp only [Inseparable, nhds_prod_eq, prod_inj]

theorem Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x₂) (hy : y₁ ~ᵢ y₂) :
    (x₁, y₁) ~ᵢ (x₂, y₂) :=
  inseparable_prod.2 ⟨hx, hy⟩

@[simp]
theorem inseparable_pi {f g : ∀ i, π i} : (f ~ᵢ g) ↔ ∀ i, f i ~ᵢ g i := by
  simp only [Inseparable, nhds_pi, funext_iff, pi_inj]

namespace Inseparable

@[refl]
theorem refl (x : X) : x ~ᵢ x :=
  Eq.refl (𝓝 x)

theorem rfl : x ~ᵢ x :=
  refl x

theorem of_eq (e : x = y) : Inseparable x y :=
  e ▸ refl x

@[symm]
nonrec theorem symm (h : x ~ᵢ y) : y ~ᵢ x := h.symm

@[trans]
nonrec theorem trans (h₁ : x ~ᵢ y) (h₂ : y ~ᵢ z) : x ~ᵢ z := h₁.trans h₂

theorem nhds_eq (h : x ~ᵢ y) : 𝓝 x = 𝓝 y := h

theorem mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x ∈ s ↔ y ∈ s :=
  inseparable_iff_forall_open.1 h s hs

theorem mem_closed_iff (h : x ~ᵢ y) (hs : IsClosed s) : x ∈ s ↔ y ∈ s :=
  inseparable_iff_forall_closed.1 h s hs

theorem map_of_continuousAt (h : x ~ᵢ y) (hx : ContinuousAt f x) (hy : ContinuousAt f y) :
    f x ~ᵢ f y :=
  (h.specializes.map_of_continuousAt hy).antisymm (h.specializes'.map_of_continuousAt hx)

theorem map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y :=
  h.map_of_continuousAt hf.continuousAt hf.continuousAt

end Inseparable

theorem IsClosed.not_inseparable (hs : IsClosed s) (hx : x ∈ s) (hy : y ∉ s) : ¬(x ~ᵢ y) := fun h =>
  hy <| (h.mem_closed_iff hs).1 hx

theorem IsOpen.not_inseparable (hs : IsOpen s) (hx : x ∈ s) (hy : y ∉ s) : ¬(x ~ᵢ y) := fun h =>
  hy <| (h.mem_open_iff hs).1 hx

/-!
### Separation quotient

In this section we define the quotient of a topological space by the `Inseparable` relation.
-/


variable (X)

instance : TopologicalSpace (SeparationQuotient X) := instTopologicalSpaceQuotient

variable {X}
variable {t : Set (SeparationQuotient X)}

namespace SeparationQuotient

/-- The natural map from a topological space to its separation quotient. -/
def mk : X → SeparationQuotient X := Quotient.mk''

theorem quotientMap_mk : QuotientMap (mk : X → SeparationQuotient X) :=
  quotientMap_quot_mk

@[fun_prop, continuity]
theorem continuous_mk : Continuous (mk : X → SeparationQuotient X) :=
  continuous_quot_mk

@[simp]
theorem mk_eq_mk : mk x = mk y ↔ (x ~ᵢ y) :=
  Quotient.eq''

theorem surjective_mk : Surjective (mk : X → SeparationQuotient X) :=
  surjective_quot_mk _

@[simp]
theorem range_mk : range (mk : X → SeparationQuotient X) = univ :=
  surjective_mk.range_eq

instance [Nonempty X] : Nonempty (SeparationQuotient X) :=
  Nonempty.map mk ‹_›

instance [Inhabited X] : Inhabited (SeparationQuotient X) :=
  ⟨mk default⟩

instance [Subsingleton X] : Subsingleton (SeparationQuotient X) :=
  surjective_mk.subsingleton

theorem preimage_image_mk_open (hs : IsOpen s) : mk ⁻¹' (mk '' s) = s := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_open_iff hs).1 hys

theorem isOpenMap_mk : IsOpenMap (mk : X → SeparationQuotient X) := fun s hs =>
  quotientMap_mk.isOpen_preimage.1 <| by rwa [preimage_image_mk_open hs]

theorem preimage_image_mk_closed (hs : IsClosed s) : mk ⁻¹' (mk '' s) = s := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_closed_iff hs).1 hys

theorem inducing_mk : Inducing (mk : X → SeparationQuotient X) :=
  ⟨le_antisymm (continuous_iff_le_induced.1 continuous_mk) fun s hs =>
      ⟨mk '' s, isOpenMap_mk s hs, preimage_image_mk_open hs⟩⟩

theorem isClosedMap_mk : IsClosedMap (mk : X → SeparationQuotient X) :=
  inducing_mk.isClosedMap <| by rw [range_mk]; exact isClosed_univ

@[simp]
theorem comap_mk_nhds_mk : comap mk (𝓝 (mk x)) = 𝓝 x :=
  (inducing_mk.nhds_eq_comap _).symm

@[simp]
theorem comap_mk_nhdsSet_image : comap mk (𝓝ˢ (mk '' s)) = 𝓝ˢ s :=
  (inducing_mk.nhdsSet_eq_comap _).symm

theorem map_mk_nhds : map mk (𝓝 x) = 𝓝 (mk x) := by
  rw [← comap_mk_nhds_mk, map_comap_of_surjective surjective_mk]

theorem map_mk_nhdsSet : map mk (𝓝ˢ s) = 𝓝ˢ (mk '' s) := by
  rw [← comap_mk_nhdsSet_image, map_comap_of_surjective surjective_mk]

theorem comap_mk_nhdsSet : comap mk (𝓝ˢ t) = 𝓝ˢ (mk ⁻¹' t) := by
  conv_lhs => rw [← image_preimage_eq t surjective_mk, comap_mk_nhdsSet_image]

theorem preimage_mk_closure : mk ⁻¹' closure t = closure (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_closure_eq_closure_preimage continuous_mk t

theorem preimage_mk_interior : mk ⁻¹' interior t = interior (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_interior_eq_interior_preimage continuous_mk t

theorem preimage_mk_frontier : mk ⁻¹' frontier t = frontier (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_frontier_eq_frontier_preimage continuous_mk t

theorem image_mk_closure : mk '' closure s = closure (mk '' s) :=
  (image_closure_subset_closure_image continuous_mk).antisymm <|
    isClosedMap_mk.closure_image_subset _

theorem map_prod_map_mk_nhds (x : X) (y : Y) :
    map (Prod.map mk mk) (𝓝 (x, y)) = 𝓝 (mk x, mk y) := by
  rw [nhds_prod_eq, ← prod_map_map_eq', map_mk_nhds, map_mk_nhds, nhds_prod_eq]

theorem map_mk_nhdsWithin_preimage (s : Set (SeparationQuotient X)) (x : X) :
    map mk (𝓝[mk ⁻¹' s] x) = 𝓝[s] mk x := by
  rw [nhdsWithin, ← comap_principal, Filter.push_pull, nhdsWithin, map_mk_nhds]

/-- The map `(x, y) ↦ (mk x, mk y)` is a quotient map. -/
theorem quotientMap_prodMap_mk : QuotientMap (Prod.map mk mk : X × Y → _) := by
  have hsurj : Surjective (Prod.map mk mk : X × Y → _) := surjective_mk.prodMap surjective_mk
  refine quotientMap_iff.2 ⟨hsurj, fun s ↦ ?_⟩
  refine ⟨fun hs ↦ hs.preimage (continuous_mk.prod_map continuous_mk), fun hs ↦ ?_⟩
  refine isOpen_iff_mem_nhds.2 <| hsurj.forall.2 fun (x, y) h ↦ ?_
  rw [Prod.map_mk, nhds_prod_eq, ← map_mk_nhds, ← map_mk_nhds, Filter.prod_map_map_eq',
    ← nhds_prod_eq, Filter.mem_map]
  exact hs.mem_nhds h

/-- Lift a map `f : X → α` such that `Inseparable x y → f x = f y` to a map
`SeparationQuotient X → α`. -/
def lift (f : X → α) (hf : ∀ x y, (x ~ᵢ y) → f x = f y) : SeparationQuotient X → α := fun x =>
  Quotient.liftOn' x f hf

@[simp]
theorem lift_mk {f : X → α} (hf : ∀ x y, (x ~ᵢ y) → f x = f y) (x : X) : lift f hf (mk x) = f x :=
  rfl

@[simp]
theorem lift_comp_mk {f : X → α} (hf : ∀ x y, (x ~ᵢ y) → f x = f y) : lift f hf ∘ mk = f :=
  rfl

@[simp]
theorem tendsto_lift_nhds_mk {f : X → α} {hf : ∀ x y, (x ~ᵢ y) → f x = f y} {l : Filter α} :
    Tendsto (lift f hf) (𝓝 <| mk x) l ↔ Tendsto f (𝓝 x) l := by
  simp only [← map_mk_nhds, tendsto_map'_iff, lift_comp_mk]

@[simp]
theorem tendsto_lift_nhdsWithin_mk {f : X → α} {hf : ∀ x y, (x ~ᵢ y) → f x = f y}
    {s : Set (SeparationQuotient X)} {l : Filter α} :
    Tendsto (lift f hf) (𝓝[s] mk x) l ↔ Tendsto f (𝓝[mk ⁻¹' s] x) l := by
  simp only [← map_mk_nhdsWithin_preimage, tendsto_map'_iff, lift_comp_mk]

@[simp]
theorem continuousAt_lift {hf : ∀ x y, (x ~ᵢ y) → f x = f y} :
    ContinuousAt (lift f hf) (mk x) ↔ ContinuousAt f x :=
  tendsto_lift_nhds_mk

@[simp]
theorem continuousWithinAt_lift {hf : ∀ x y, (x ~ᵢ y) → f x = f y}
    {s : Set (SeparationQuotient X)} :
    ContinuousWithinAt (lift f hf) s (mk x) ↔ ContinuousWithinAt f (mk ⁻¹' s) x :=
  tendsto_lift_nhdsWithin_mk

@[simp]
theorem continuousOn_lift {hf : ∀ x y, (x ~ᵢ y) → f x = f y} {s : Set (SeparationQuotient X)} :
    ContinuousOn (lift f hf) s ↔ ContinuousOn f (mk ⁻¹' s) := by
  simp only [ContinuousOn, surjective_mk.forall, continuousWithinAt_lift, mem_preimage]

@[simp]
theorem continuous_lift {hf : ∀ x y, (x ~ᵢ y) → f x = f y} :
    Continuous (lift f hf) ↔ Continuous f := by
  simp only [continuous_iff_continuousOn_univ, continuousOn_lift, preimage_univ]

/-- Lift a map `f : X → Y → α` such that `Inseparable a b → Inseparable c d → f a c = f b d` to a
map `SeparationQuotient X → SeparationQuotient Y → α`. -/
def lift₂ (f : X → Y → α) (hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d) :
    SeparationQuotient X → SeparationQuotient Y → α := fun x y => Quotient.liftOn₂' x y f hf

@[simp]
theorem lift₂_mk {f : X → Y → α} (hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d) (x : X)
    (y : Y) : lift₂ f hf (mk x) (mk y) = f x y :=
  rfl

@[simp]
theorem tendsto_lift₂_nhds {f : X → Y → α} {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d}
    {x : X} {y : Y} {l : Filter α} :
    Tendsto (uncurry <| lift₂ f hf) (𝓝 (mk x, mk y)) l ↔ Tendsto (uncurry f) (𝓝 (x, y)) l := by
  rw [← map_prod_map_mk_nhds, tendsto_map'_iff]
  rfl

@[simp] theorem tendsto_lift₂_nhdsWithin {f : X → Y → α}
    {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d} {x : X} {y : Y}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} {l : Filter α} :
    Tendsto (uncurry <| lift₂ f hf) (𝓝[s] (mk x, mk y)) l ↔
      Tendsto (uncurry f) (𝓝[Prod.map mk mk ⁻¹' s] (x, y)) l := by
  rw [nhdsWithin, ← map_prod_map_mk_nhds, ← Filter.push_pull, comap_principal]
  rfl

@[simp]
theorem continuousAt_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d}
    {x : X} {y : Y} :
    ContinuousAt (uncurry <| lift₂ f hf) (mk x, mk y) ↔ ContinuousAt (uncurry f) (x, y) :=
  tendsto_lift₂_nhds

@[simp] theorem continuousWithinAt_lift₂ {f : X → Y → Z}
    {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} {x : X} {y : Y} :
    ContinuousWithinAt (uncurry <| lift₂ f hf) s (mk x, mk y) ↔
      ContinuousWithinAt (uncurry f) (Prod.map mk mk ⁻¹' s) (x, y) :=
  tendsto_lift₂_nhdsWithin

@[simp]
theorem continuousOn_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} :
    ContinuousOn (uncurry <| lift₂ f hf) s ↔ ContinuousOn (uncurry f) (Prod.map mk mk ⁻¹' s) := by
  simp_rw [ContinuousOn, (surjective_mk.prodMap surjective_mk).forall, Prod.forall, Prod.map,
    continuousWithinAt_lift₂]
  rfl

@[simp]
theorem continuous_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d} :
    Continuous (uncurry <| lift₂ f hf) ↔ Continuous (uncurry f) := by
  simp only [continuous_iff_continuousOn_univ, continuousOn_lift₂, preimage_univ]

end SeparationQuotient

theorem continuous_congr_of_inseparable (h : ∀ x, f x ~ᵢ g x) :
    Continuous f ↔ Continuous g := by
  simp_rw [SeparationQuotient.inducing_mk.continuous_iff (Y := Y)]
  exact continuous_congr fun x ↦ SeparationQuotient.mk_eq_mk.mpr (h x)
