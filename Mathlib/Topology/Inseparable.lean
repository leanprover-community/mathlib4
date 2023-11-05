/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yury G. Kudryashov
-/
import Mathlib.Tactic.TFAE
import Mathlib.Topology.ContinuousOn

#align_import topology.inseparable from "leanprover-community/mathlib"@"bcfa726826abd57587355b4b5b7e78ad6527b7e4"

/-!
# Inseparable points in a topological space

In this file we define

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

/-- `x` specializes to `y` (notation: `x ⤳ y`) if either of the following equivalent properties
hold:

* `𝓝 x ≤ 𝓝 y`; this property is used as the definition;
* `pure x ≤ 𝓝 y`; in other words, any neighbourhood of `y` contains `x`;
* `y ∈ closure {x}`;
* `closure {y} ⊆ closure {x}`;
* for any closed set `s` we have `x ∈ s → y ∈ s`;
* for any open set `s` we have `y ∈ s → x ∈ s`;
* `y` is a cluster point of the filter `pure x = 𝓟 {x}`.

This relation defines a `Preorder` on `X`. If `X` is a T₀ space, then this preorder is a partial
order. If `X` is a T₁ space, then this partial order is trivial : `x ⤳ y ↔ x = y`. -/
def Specializes (x y : X) : Prop := 𝓝 x ≤ 𝓝 y

@[inherit_doc]
infixl:300 " ⤳ " => Specializes

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
  · refine' fun h => (nhds_basis_opens _).ge_iff.2 _
    rintro s ⟨hy, ho⟩
    rcases mem_closure_iff.1 h s ho hy with ⟨z, hxs, rfl : z = x⟩
    exact ho.mem_nhds hxs
  tfae_finish

theorem specializes_iff_nhds : x ⤳ y ↔ 𝓝 x ≤ 𝓝 y :=
  Iff.rfl

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

-- porting note: new lemma
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

variable (X)

/-- Specialization forms a preorder on the topological space. -/
def specializationPreorder : Preorder X :=
  { Preorder.lift (OrderDual.toDual ∘ 𝓝) with
    le := fun x y => y ⤳ x
    lt := fun x y => y ⤳ x ∧ ¬x ⤳ y }

variable {X}

/-- A continuous function is monotone with respect to the specialization preorders on the domain and
the codomain. -/
theorem Continuous.specialization_monotone (hf : Continuous f) :
    @Monotone _ _ (specializationPreorder X) (specializationPreorder Y) f := fun _ _ h => h.map hf

/-!
### `Inseparable` relation
-/

/-- Two points `x` and `y` in a topological space are `Inseparable` if any of the following
equivalent properties hold:

- `𝓝 x = 𝓝 y`; we use this property as the definition;
- for any open set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_open`;
- for any closed set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_closed`;
- `x ∈ closure {y}` and `y ∈ closure {x}`, see `inseparable_iff_mem_closure`;
- `closure {x} = closure {y}`, see `inseparable_iff_closure_eq`.
-/
def Inseparable (x y : X) : Prop :=
  𝓝 x = 𝓝 y

local infixl:0 " ~ᵢ " => Inseparable

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
    ¬(x ~ᵢ y) ↔ ∃ s : Set X, IsOpen s ∧ Xor' (x ∈ s) (y ∈ s) :=
  by simp [inseparable_iff_forall_open, ← xor_iff_not_iff]

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
    ((x₁, y₁) ~ᵢ (x₂, y₂)) ↔ (x₁ ~ᵢ x₂) ∧ (y₁ ~ᵢ y₂) :=
  by simp only [Inseparable, nhds_prod_eq, prod_inj]

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

/-- A `setoid` version of `Inseparable`, used to define the `SeparationQuotient`. -/
def inseparableSetoid : Setoid X := { Setoid.comap 𝓝 ⊥ with r := Inseparable }

/-- The quotient of a topological space by its `inseparableSetoid`. This quotient is guaranteed to
be a T₀ space. -/
def SeparationQuotient := Quotient (inseparableSetoid X)

instance : TopologicalSpace (SeparationQuotient X) := instTopologicalSpaceQuotient

variable {X}
variable {t : Set (SeparationQuotient X)}

namespace SeparationQuotient

/-- The natural map from a topological space to its separation quotient. -/
def mk : X → SeparationQuotient X := Quotient.mk''

theorem quotientMap_mk : QuotientMap (mk : X → SeparationQuotient X) :=
  quotientMap_quot_mk

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
  refine' Subset.antisymm _ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_open_iff hs).1 hys

theorem isOpenMap_mk : IsOpenMap (mk : X → SeparationQuotient X) := fun s hs =>
  quotientMap_mk.isOpen_preimage.1 <| by rwa [preimage_image_mk_open hs]

theorem preimage_image_mk_closed (hs : IsClosed s) : mk ⁻¹' (mk '' s) = s := by
  refine' Subset.antisymm _ (subset_preimage_image _ _)
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

theorem map_prod_map_mk_nhds (x : X) (y : Y) : map (Prod.map mk mk) (𝓝 (x, y)) = 𝓝 (mk x, mk y) :=
  by rw [nhds_prod_eq, ← prod_map_map_eq', map_mk_nhds, map_mk_nhds, nhds_prod_eq]

theorem map_mk_nhdsWithin_preimage (s : Set (SeparationQuotient X)) (x : X) :
    map mk (𝓝[mk ⁻¹' s] x) = 𝓝[s] mk x := by
  rw [nhdsWithin, ← comap_principal, Filter.push_pull, nhdsWithin, map_mk_nhds]

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
theorem tendsto_lift_nhds_mk {f : X → α} {hf : ∀ x y, (x ~ᵢ y) → f x = f y} {x : X} {l : Filter α} :
    Tendsto (lift f hf) (𝓝 <| mk x) l ↔ Tendsto f (𝓝 x) l := by
  simp only [← map_mk_nhds, tendsto_map'_iff, lift_comp_mk]

@[simp]
theorem tendsto_lift_nhdsWithin_mk {f : X → α} {hf : ∀ x y, (x ~ᵢ y) → f x = f y} {x : X}
    {s : Set (SeparationQuotient X)} {l : Filter α} :
    Tendsto (lift f hf) (𝓝[s] mk x) l ↔ Tendsto f (𝓝[mk ⁻¹' s] x) l := by
  simp only [← map_mk_nhdsWithin_preimage, tendsto_map'_iff, lift_comp_mk]

@[simp]
theorem continuousAt_lift {f : X → Y} {hf : ∀ x y, (x ~ᵢ y) → f x = f y} {x : X} :
    ContinuousAt (lift f hf) (mk x) ↔ ContinuousAt f x :=
  tendsto_lift_nhds_mk

@[simp]
theorem continuousWithinAt_lift {f : X → Y} {hf : ∀ x y, (x ~ᵢ y) → f x = f y}
    {s : Set (SeparationQuotient X)} {x : X} :
    ContinuousWithinAt (lift f hf) s (mk x) ↔ ContinuousWithinAt f (mk ⁻¹' s) x :=
  tendsto_lift_nhdsWithin_mk

@[simp]
theorem continuousOn_lift {f : X → Y} {hf : ∀ x y, (x ~ᵢ y) → f x = f y}
    {s : Set (SeparationQuotient X)} : ContinuousOn (lift f hf) s ↔ ContinuousOn f (mk ⁻¹' s) := by
  simp only [ContinuousOn, surjective_mk.forall, continuousWithinAt_lift, mem_preimage]

@[simp]
theorem continuous_lift {f : X → Y} {hf : ∀ x y, (x ~ᵢ y) → f x = f y} :
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
  simp_rw [ContinuousOn, (surjective_mk.Prod_map surjective_mk).forall, Prod.forall, Prod.map,
    continuousWithinAt_lift₂]
  rfl

@[simp]
theorem continuous_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d} :
    Continuous (uncurry <| lift₂ f hf) ↔ Continuous (uncurry f) := by
  simp only [continuous_iff_continuousOn_univ, continuousOn_lift₂, preimage_univ]

end SeparationQuotient

theorem continuous_congr_of_inseparable (h : ∀ x, f x ~ᵢ g x) :
    Continuous f ↔ Continuous g := by
  simp_rw [SeparationQuotient.inducing_mk.continuous_iff (β := Y)]
  exact continuous_congr fun x ↦ SeparationQuotient.mk_eq_mk.mpr (h x)
