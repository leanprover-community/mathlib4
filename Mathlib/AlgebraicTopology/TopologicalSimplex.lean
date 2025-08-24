/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Adam Topaz, Joël Riou
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Topology.Category.TopCat.ULift
import Mathlib.Topology.Connected.PathConnected

/-!
# Topological simplices

We define the natural functor from `SimplexCategory` to `TopCat` sending `⦋n⦌` to the
topological `n`-simplex.
This is used to define `TopCat.toSSet` in `AlgebraicTopology.SingularSet`.
-/

universe u

open CategoryTheory Simplicial

namespace Convex

section

variable {𝕜 E ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {s : Set E} (hs : Convex 𝕜 s)
  (t : Finset ι) (p : ι → s) (w : ι → 𝕜) (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : t.sum w = 1)

include hw₀ hw₁ hs

lemma finsetAffineCombination_mem :
    Finset.affineCombination 𝕜 t (fun i ↦ (p i).1) w ∈ s :=
  hs.convexHull_eq.subset
    (convexHull_mono (by grind) (affineCombination_mem_convexHull (by tauto) hw₁))

@[simps]
noncomputable def affineCombination : s :=
  ⟨_, hs.finsetAffineCombination_mem t p w hw₀ hw₁⟩

end

section

open unitInterval

@[simps]
def fromUnitInterval {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E} (hs : Convex ℝ s)
    (x₀ x₁ : s) (t : I) : s :=
  ⟨(1 - t.1) • x₀ + t.1 • x₁, by
    apply hs.starConvex x₀.2 x₁.2
    all_goals grind⟩

@[continuity]
lemma continuous_fromUnitInterval {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) (x₀ x₁ : s) :
    Continuous (fromUnitInterval hs x₀ x₁) :=
  Continuous.subtype_mk (by continuity) _

end

end Convex

namespace FunOnFinite

section

variable {M : Type*} [AddCommMonoid M] {X Y Z : Type*}

noncomputable def map [Finite X] [Finite Y] (f : X → Y) (s : X → M) : (Y → M) :=
  Finsupp.equivFunOnFinite (Finsupp.mapDomain f (Finsupp.equivFunOnFinite.symm s))

lemma map_apply_apply [Fintype X] [Finite Y] [DecidableEq Y] (f : X → Y) (s : X → M) (y : Y) :
    map f s y = (Finset.univ.filter (fun (x : X) ↦ f x = y)).sum s := by
  obtain ⟨s, rfl⟩ := Finsupp.equivFunOnFinite.surjective s
  dsimp [map]
  simp only [Equiv.symm_apply_apply, Finsupp.equivFunOnFinite_apply]
  nth_rw 1 [← Finsupp.univ_sum_single s]
  rw [Finsupp.mapDomain_finset_sum]
  simp [Finset.sum_filter]
  congr
  ext x
  by_cases hx : f x = y
  · simp [hx]
  · rw [if_neg hx, Finsupp.single_eq_of_ne hx]

@[simp]
lemma map_piSingle [Finite X] [Finite Y] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (x : X) (m : M) :
    map f (Pi.single x m) = Pi.single (f x) m := by
  simp [map]

variable (M) in
lemma map_id [Finite X] : map (id : X → X) (M := M) = id := by
  ext s
  simp [map]

lemma map_comp [Finite X] [Finite Y] [Finite Z] (g : Y → Z) (f : X → Y) :
    map (g.comp f) (M := M) = (map g).comp (map f) := by
  ext s
  simp [map, Finsupp.mapDomain_comp]

end

section

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] {X Y Z : Type*}

noncomputable def linearMap [Finite X] [Finite Y] (f : X → Y) :
    (X → M) →ₗ[R] (Y → M) :=
  (((Finsupp.linearEquivFunOnFinite R M Y)).comp (Finsupp.lmapDomain M R f)).comp
    (Finsupp.linearEquivFunOnFinite R M X).symm.toLinearMap

lemma linearMap_apply_apply
    [Fintype X] [Finite Y] [DecidableEq Y] (f : X → Y) (s : X → M) (y : Y) :
    linearMap R M f s y = (Finset.univ.filter (fun (x : X) ↦ f x = y)).sum s := by
  apply map_apply_apply

@[simp]
lemma linearMap_piSingle [Finite X] [Finite Y] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (x : X) (m : M) :
    linearMap R M f (Pi.single x m) = Pi.single (f x) m := by
  apply map_piSingle

variable (X) in
@[simp]
lemma linearMap_id [Finite X] : linearMap R M (id : X → X) = .id := by
  classical
  aesop

lemma linearMap_comp [Finite X] [Finite Y] [Finite Z] (f : X → Y) (g : Y → Z) :
    linearMap R M (g.comp f) = (linearMap R M g).comp (linearMap R M f) := by
  classical
  aesop

end

end FunOnFinite

variable (R : Type*) [Ring R] [PartialOrder R]
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  (X Y Z : Type*) [Fintype X] [Fintype Y] [Fintype Z]

/-- The simplex with a given type of vertices `X`. -/
def topologicalSimplex : Set (X → R) := setOf (fun f ↦ (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1)

variable {X} in
lemma mem_topologicalSimplex_iff (f : X → R) :
    f ∈ topologicalSimplex R X ↔ (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1 := Iff.rfl

/-- The simplex with a given type of vertices `X`, as a type. -/
abbrev TopologicalSimplex : Type _ := topologicalSimplex R X

namespace TopologicalSimplex

variable {R X Y Z}

instance : FunLike (TopologicalSimplex R X) X R where
  coe s := s.val
  coe_injective' := by aesop

@[continuity]
lemma continuous_apply (x : X) : Continuous (fun (s : TopologicalSimplex ℝ X) ↦ s x) :=
  (_root_.continuous_apply x).comp continuous_subtype_val

@[simp]
lemma mem (s : TopologicalSimplex R X) : ⇑s ∈ topologicalSimplex R X := s.2

@[ext high]
lemma ext {s t : TopologicalSimplex R X} (h : (s : X → R) = t) : s = t := by
  ext : 1
  assumption

@[simp]
lemma zero_le (s : TopologicalSimplex R X) (x : X) : 0 ≤ s x := s.2.1 x

@[simp]
lemma sum_eq_one (s : TopologicalSimplex R X) : ∑ i, s i = 1 := s.2.2

@[simp]
lemma le_one [IsOrderedRing R] (s : TopologicalSimplex R X) (x : X) : s x ≤ 1 := by
  classical
  rw [← s.sum_eq_one, ← Finset.sum_compl_add_sum {x}, Finset.sum_singleton,
    le_add_iff_nonneg_left]
  exact Finset.sum_nonneg (by simp)

section

variable [IsOrderedRing R]

variable (R X) in
lemma convex : Convex R (topologicalSimplex R X) := by
  rintro f ⟨hf, hf'⟩ g ⟨hg, hg'⟩ a b ha hb h
  refine ⟨fun i ↦ ?_, ?_⟩
  · replace hf := hf i
    replace hg := hg i
    dsimp
    positivity
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hf', hg', h]

noncomputable def affineCombination
    {ι : Type*} (t : Finset ι) (p : ι → TopologicalSimplex 𝕜 X)
    (w : ι → 𝕜) (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : t.sum w = 1) :
    TopologicalSimplex 𝕜 X :=
  (convex 𝕜 X).affineCombination t p w hw₀ hw₁

lemma affineCombination_coe
    {ι : Type*} (t : Finset ι) (p : ι → TopologicalSimplex 𝕜 X)
    (w : ι → 𝕜) (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : t.sum w = 1) :
    (affineCombination t p w hw₀ hw₁ : X → 𝕜) =
      Finset.affineCombination 𝕜 t (fun i ↦ (p i).1) w :=
  rfl

@[simp]
lemma affineCombination_apply
    {ι : Type*} (t : Finset ι) (p : ι → TopologicalSimplex 𝕜 X)
    (w : ι → 𝕜) (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : t.sum w = 1) (x : X) :
    affineCombination t p w hw₀ hw₁ x = t.sum (fun i ↦ w i * p i x) := by
  rw [affineCombination_coe]
  aesop

section

variable [DecidableEq X]

variable (R) in
@[simp]
lemma piSingle_mem (x : X) :
    Pi.single x 1 ∈ topologicalSimplex R X := by
  rw [mem_topologicalSimplex_iff]
  refine ⟨fun y ↦ ?_, ?_⟩
  · by_cases hy : y = x
    · subst hy
      simp
    · rw [Pi.single_eq_of_ne hy]
  · rw [Finset.sum_eq_single x, Pi.single_eq_same] <;> aesop

/-- The vertex of `TopologicalSimplex X` corresponding to `x : X`. -/
def vertex (x : X) : TopologicalSimplex R X :=
  ⟨_,piSingle_mem R x⟩

@[simp]
lemma vertex_eq_piSingle (x : X) :
    ⇑(vertex (R := R) x) = Pi.single x 1 :=
  rfl

@[simp]
lemma vertex_apply_self (x : X) :
    vertex (R := R) x x = 1 := by
  simp [vertex_eq_piSingle]

lemma vertex_apply_eq_zero {x y : X} (h : y ≠ x) :
    vertex (R := R) x y = 0 := by
  simp [vertex_eq_piSingle, Pi.single_eq_of_ne h]

lemma eq_affineCombination (s : TopologicalSimplex 𝕜 X) :
    s = affineCombination .univ vertex s (by simp) (by simp) := by
  ext x
  simp
  rw [Finset.sum_eq_single x _ (by simp), Pi.single_eq_same, mul_one]
  intro _ _ h
  simp [Pi.single_eq_of_ne' h]

lemma exists_eq_affineCombination (s : TopologicalSimplex 𝕜 X) :
    ∃ (w : X → 𝕜) (hw₀ : ∀ (i : X), 0 ≤ w i) (hw₁ : ∑ i, w i = 1),
      s = affineCombination .univ vertex w hw₀ hw₁ :=
  ⟨_, _, _, eq_affineCombination s⟩

lemma vertex_injective [Nontrivial R] :
    Function.Injective (vertex (R := R) (X := X)) := by
  intro x y h
  replace h := DFunLike.congr_fun h x
  by_contra!
  simp [Pi.single_eq_of_ne this] at h

variable (X) in
lemma eq_convexHull :
    topologicalSimplex 𝕜 X =
      convexHull 𝕜 (Set.range (fun x ↦ ⇑(vertex x))) := by
  refine subset_antisymm (fun f hf ↦ ?_)
    (convexHull_min (by rintro _ ⟨x, rfl⟩; simp) (convex 𝕜 X))
  obtain ⟨w, hw₀, hw₁, h⟩ := exists_eq_affineCombination ⟨f, hf⟩
  rw [Subtype.ext_iff] at h
  subst h
  apply affineCombination_mem_convexHull
  all_goals aesop

end

section

variable [IsStrictOrderedRing R]

instance [Nonempty X] : Nonempty (TopologicalSimplex R X) := by
  classical
  exact ⟨vertex (Classical.arbitrary _)⟩

instance [Nontrivial X] : Nontrivial (TopologicalSimplex R X) where
  exists_pair_ne := by
    classical
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    exact ⟨vertex x, vertex y, fun h ↦ hxy (vertex_injective h)⟩

instance [Subsingleton X] : Subsingleton (TopologicalSimplex R X) where
  allEq s t := by
    ext i
    have (u : TopologicalSimplex R X) : u i = 1 := by
      rw [← u.sum_eq_one, Finset.sum_eq_single i _ (by simp)]
      intro j _ hj
      exact (hj (Subsingleton.elim j i)).elim
    simp [this]

instance [Unique X] : Unique (TopologicalSimplex R X) where
  default := ⟨1, by simp, by simp⟩
  uniq := by subsingleton

end

instance [Nonempty X] : PathConnectedSpace (TopologicalSimplex ℝ X) :=
  isPathConnected_iff_pathConnectedSpace.1
    ((convex ℝ X).isPathConnected Set.Nonempty.of_subtype)

-- to be moved
@[continuity]
lemma continuous_linearMap (f : X → Y) : Continuous (FunOnFinite.linearMap ℝ ℝ f) := by
  classical
  refine continuous_pi (fun y ↦ ?_)
  simp only [FunOnFinite.linearMap_apply_apply]
  apply continuous_finset_sum
  continuity

lemma linearEquivFunOnFinite_single [DecidableEq X] (x : X) :
    (Finsupp.linearEquivFunOnFinite ℝ ℝ X) (Finsupp.single x 1) = Pi.single x 1 := by
  ext y
  rw [Finsupp.linearEquivFunOnFinite_apply]
  by_cases hy : y = x
  · subst hy
    simp
  · rw [Finsupp.single_eq_of_ne (Ne.symm hy), Pi.single_eq_of_ne hy]

lemma image_linearMap (f : X → Y) :
    Set.image (FunOnFinite.linearMap 𝕜 𝕜 f) (topologicalSimplex 𝕜 X) ⊆ topologicalSimplex 𝕜 Y := by
  classical
  simp only [eq_convexHull, (FunOnFinite.linearMap 𝕜 𝕜 f).isLinear.image_convexHull]
  apply convexHull_mono
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨f x, by simp⟩

noncomputable def map (f : X → Y) (s : TopologicalSimplex 𝕜 X) : TopologicalSimplex 𝕜 Y :=
  ⟨FunOnFinite.linearMap 𝕜 𝕜 f s, image_linearMap f (by aesop)⟩

@[simp]
lemma map_coe (f : X → Y) (s : TopologicalSimplex 𝕜 X) :
    ⇑(map f s) = FunOnFinite.linearMap 𝕜 𝕜 f s := rfl

@[simp]
lemma map_id_apply (x) : map (𝕜 := 𝕜) (id : X → X) x = x := by
  aesop

lemma map_comp_apply (f : X → Y) (g : Y → Z) (x) :
    map (𝕜 := 𝕜) g (map f x) = map (g.comp f) x := by
  ext
  simp [FunOnFinite.linearMap_comp]

@[continuity, fun_prop]
lemma continuous_map (f : X → Y) : Continuous (map (𝕜 := ℝ) f) :=
  Continuous.subtype_mk ((continuous_linearMap f).comp continuous_induced_dom) _

section

open unitInterval

variable [DecidableEq X] (x₀ x₁ : X)

noncomputable def fromUnitInterval (t : I) : TopologicalSimplex ℝ X :=
  (convex ℝ X).fromUnitInterval (vertex x₀) (vertex x₁) t

@[simp]
lemma fromUnitInterval_coe (t : I) :
    ⇑(fromUnitInterval x₀ x₁ t) =
      (1 - t.1) • (Pi.single x₀ 1 : _ → ℝ) + t.1 • (Pi.single x₁ 1 : _ → ℝ) :=
  rfl

@[simp]
lemma fromUnitInterval_zero :
    fromUnitInterval x₀ x₁ 0 = vertex x₀ := by
  aesop

@[simp]
lemma fromUnitInterval_one :
    fromUnitInterval x₀ x₁ 1 = vertex x₁ := by
  aesop

@[continuity]
lemma continuous_fromUnitInterval :
    Continuous (fromUnitInterval x₀ x₁) :=
  (convex ℝ X).continuous_fromUnitInterval _ _

@[simps]
noncomputable def homeoUnitInterval (h : x₀ ≠ x₁) (h' : {x₀, x₁} = Finset.univ) :
    TopologicalSimplex ℝ X ≃ₜ I where
  toFun s := ⟨s x₁, by simp, by simp⟩
  invFun := fromUnitInterval x₀ x₁
  left_inv s := by
    ext x
    have : s x₀ + s x₁ = 1 := by
      rw [← s.sum_eq_one, ← h', Finset.sum_insert (by simpa), Finset.sum_singleton]
    have hx := Finset.mem_univ x
    simp only [← h', Finset.mem_insert, Finset.mem_singleton] at hx
    obtain rfl | rfl := hx
    · simp [Pi.single_eq_of_ne h]
      grind
    · simp [Pi.single_eq_of_ne' h]
  right_inv t := by
    ext
    simp [Pi.single_eq_of_ne' h]

noncomputable def homeoUnitInterval' : TopologicalSimplex ℝ (Fin 2) ≃ₜ I :=
  homeoUnitInterval _ _ Fin.zero_ne_one (by aesop)

end
end
end TopologicalSimplex

namespace SimplexCategory

@[simp]
lemma concreteCategoryHom_id (n : SimplexCategory) : ConcreteCategory.hom (𝟙 n) = .id := rfl

attribute [local simp] TopologicalSimplex.map_comp_apply

/-- The functor `SimplexCategory ⥤ TopCat.{0}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps obj map]
noncomputable def toTop₀ : CosimplicialObject TopCat.{0} where
  obj n := TopCat.of (TopologicalSimplex ℝ (Fin (n.len + 1)))
  map f := TopCat.ofHom ⟨_, TopologicalSimplex.continuous_map f⟩

/-- The functor `SimplexCategory ⥤ TopCat.{u}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps! obj map, pp_with_univ]
noncomputable def toTop : CosimplicialObject TopCat.{u} :=
  toTop₀ ⋙ TopCat.uliftFunctor

end SimplexCategory


/-
namespace SimplexCategory

open Simplicial NNReal CategoryTheory

/-- The topological simplex associated to `x : SimplexCategory`.
  This is the object part of the functor `SimplexCategory.toTop`. -/
def toTopObj (x : SimplexCategory) := { f : ToType x → ℝ≥0 | ∑ i, f i = 1 }

instance (x : SimplexCategory) : CoeFun x.toTopObj fun _ => ToType x → ℝ≥0 :=
  ⟨fun f => (f : ToType x → ℝ≥0)⟩

@[ext]
theorem toTopObj.ext {x : SimplexCategory} (f g : x.toTopObj) : (f : ToType x → ℝ≥0) = g → f = g :=
  Subtype.ext

@[simp]
lemma toTopObj_zero_apply_zero (f : ⦋0⦌.toTopObj) : f 0 = 1 := by
  simpa [toType_apply] using show ∑ _, _ = _ from f.2

lemma toTopObj_one_add_eq_one (f : ⦋1⦌.toTopObj) : f 0 + f 1 = 1 := by
  simpa [toType_apply, Finset.sum] using show ∑ _, _ = _ from f.2

lemma toTopObj_one_coe_add_coe_eq_one (f : ⦋1⦌.toTopObj) : (f 0 : ℝ) + f 1 = 1 := by
  norm_cast
  rw [toTopObj_one_add_eq_one]

instance (x : SimplexCategory) : Nonempty x.toTopObj :=
  ⟨⟨Pi.single 0 1, (show ∑ _, _ = _ by simp)⟩⟩

instance : Unique ⦋0⦌.toTopObj :=
  ⟨⟨1, show ∑ _, _ = _ by simp [toType_apply]⟩, fun f ↦ by ext i; fin_cases i; simp⟩

open unitInterval in
/-- The one-dimensional topological simplex is homeomorphic to the unit interval. -/
def toTopObjOneHomeo : ⦋1⦌.toTopObj ≃ₜ I where
  toFun f := ⟨f 0, (f 0).2, toTopObj_one_coe_add_coe_eq_one f ▸ le_add_of_nonneg_right (f 1).2⟩
  invFun x := ⟨![toNNReal x, toNNReal (σ x)],
    show ∑ _, _ = _ by ext; simp [toType_apply, Finset.sum]⟩
  left_inv f := by ext i; fin_cases i <;> simp [← toTopObj_one_coe_add_coe_eq_one f]
  right_inv x := by simp
  continuous_toFun := .subtype_mk (continuous_subtype_val.comp
    ((continuous_apply _).comp continuous_subtype_val)) _
  continuous_invFun := .subtype_mk (continuous_pi fun i ↦ by fin_cases i <;> dsimp <;> fun_prop) _

open unitInterval in
instance (x : SimplexCategory) : PathConnectedSpace x.toTopObj := by
  refine ⟨inferInstance, ?_⟩
  intro f g
  dsimp [toTopObj, toType_apply] at f g ⊢
  refine ⟨⟨fun j ↦ ⟨toNNReal (symm j) • f.1 + toNNReal j • g.1, ?_⟩, ?_⟩, ?_, ?_⟩
  · ext; simp [Finset.sum_add_distrib, ← Finset.mul_sum, f.2, g.2]
  · fun_prop
  · ext; simp
  · ext; simp

open Classical in
/-- A morphism in `SimplexCategory` induces a map on the associated topological spaces. -/
def toTopMap {x y : SimplexCategory} (f : x ⟶ y) (g : x.toTopObj) : y.toTopObj :=
  ⟨fun i => ∑ j ∈ Finset.univ.filter (f · = i), g j, by
    simp only [toTopObj, Set.mem_setOf]
    rw [← Finset.sum_biUnion]
    · have hg : ∑ i : ToType x, g i = 1 := g.2
      convert hg
      simp [Finset.eq_univ_iff_forall]
    · convert Set.pairwiseDisjoint_filter _ _ _⟩

open Classical in
@[simp]
theorem coe_toTopMap {x y : SimplexCategory} (f : x ⟶ y) (g : x.toTopObj) (i : ToType y) :
    toTopMap f g i = ∑ j ∈ Finset.univ.filter (f · = i), g j :=
  rfl

@[continuity, fun_prop]
theorem continuous_toTopMap {x y : SimplexCategory} (f : x ⟶ y) : Continuous (toTopMap f) := by
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  dsimp only [coe_toTopMap]
  exact continuous_finset_sum _ (fun j _ => (continuous_apply _).comp continuous_subtype_val)

/-- The functor `SimplexCategory ⥤ TopCat.{0}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps obj map]
def toTop₀ : SimplexCategory ⥤ TopCat.{0} where
  obj x := TopCat.of x.toTopObj
  map f := TopCat.ofHom ⟨toTopMap f, by fun_prop⟩
  map_id := by
    classical
    intro Δ
    ext f
    simp [Finset.sum_filter]
  map_comp := fun f g => by
    classical
    ext h : 3
    dsimp
    rw [← Finset.sum_biUnion]
    · apply Finset.sum_congr
      · exact Finset.ext (fun j => ⟨fun hj => by simpa using hj, fun hj => by simpa using hj⟩)
      · tauto
    · apply Set.pairwiseDisjoint_filter

/-- The functor `SimplexCategory ⥤ TopCat.{u}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps! obj map, pp_with_univ]
def toTop : SimplexCategory ⥤ TopCat.{u} :=
  toTop₀ ⋙ TopCat.uliftFunctor

end SimplexCategory
-/
