/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Adam Topaz, Joël Riou
-/
import Mathlib.Analysis.Convex.Combination
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

section

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

end

section

variable (X Y Z : Type*) [Fintype X] [Fintype Y] [Fintype Z]

/-- The simplex with a given type of vertices `X`. -/
def topologicalSimplex : Set (X → ℝ) := setOf (fun f ↦ (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1)

variable {X} in
lemma mem_topologicalSimplex_iff (f : X → ℝ) :
    f ∈ topologicalSimplex X ↔ (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1 := Iff.rfl

/-- The simplex with a given type of vertices `X`, as a type. -/
abbrev TopologicalSimplex : Type _ := topologicalSimplex X

namespace TopologicalSimplex

variable {X Y Z}

instance : FunLike (TopologicalSimplex X) X ℝ where
  coe s := s.val
  coe_injective' := by aesop

@[continuity]
lemma continuous_apply (x : X) : Continuous (fun (s : TopologicalSimplex X) ↦ s x) :=
  (_root_.continuous_apply x).comp continuous_subtype_val

@[simp]
lemma mem (s : TopologicalSimplex X) : ⇑s ∈ topologicalSimplex X := s.2

@[ext high]
lemma ext {s t : TopologicalSimplex X} (h : (s : X → ℝ) = t) : s = t := by
  ext : 1
  assumption

@[simp]
lemma zero_le (s : TopologicalSimplex X) (x : X) : 0 ≤ s x := s.2.1 x

@[simp]
lemma sum_eq_one (s : TopologicalSimplex X) : ∑ i, s i = 1 := s.2.2

@[simp]
lemma le_one (s : TopologicalSimplex X) (x : X) : s x ≤ 1 := by
  classical
  rw [← s.sum_eq_one, ← Finset.sum_compl_add_sum {x}, Finset.sum_singleton,
    le_add_iff_nonneg_left]
  exact Finset.sum_nonneg (by simp)

/-- Constructor for elements in the topological simplex. -/
def mk (f : X → ℝ) (hf' : ∑ i, f i = 1) (hf : ∀ i, 0 ≤ f i := by intros; positivity) :
    TopologicalSimplex X where
  val := f
  property := ⟨hf, hf'⟩

@[simp]
lemma mk_apply (f : X → ℝ) (x : X) (hf' : ∑ i, f i = 1) (hf : ∀ i, 0 ≤ f i) :
    mk f hf' hf x = f x :=
  rfl

variable (X) in
lemma convex : Convex ℝ (topologicalSimplex X) := by
  rintro f ⟨hf, hf'⟩ g ⟨hg, hg'⟩ a b ha hb h
  refine ⟨fun i ↦ ?_, ?_⟩
  · replace hf := hf i
    replace hg := hg i
    dsimp
    positivity
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hf', hg', h]

noncomputable def affineCombination
    {ι : Type*} (t : Finset ι) (p : ι → TopologicalSimplex X)
    (w : ι → ℝ) (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : t.sum w = 1) :
    TopologicalSimplex X :=
  (convex X).affineCombination t p w hw₀ hw₁

lemma affineCombination_coe
    {ι : Type*} (t : Finset ι) (p : ι → TopologicalSimplex X)
    (w : ι → ℝ) (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : t.sum w = 1) :
    (affineCombination t p w hw₀ hw₁ : X → ℝ) =
      Finset.affineCombination ℝ t (fun i ↦ (p i).1) w :=
  rfl

@[simp]
lemma affineCombination_apply
    {ι : Type*} (t : Finset ι) (p : ι → TopologicalSimplex X)
    (w : ι → ℝ) (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : t.sum w = 1) (x : X) :
    affineCombination t p w hw₀ hw₁ x = t.sum (fun i ↦ w i * p i x) := by
  rw [affineCombination_coe]
  aesop

section

variable [DecidableEq X]

/-- The vertex of `TopologicalSimplex X` corresponding to `x : X`. -/
def vertex (x : X) : TopologicalSimplex X :=
  .mk (fun y ↦ if y = x then 1 else 0) (by
    rw [Finset.sum_eq_single x]
    all_goals grind)

@[simp]
lemma vertex_apply_self (x : X) :
    vertex x x = 1 := by
  simp [vertex]

lemma vertex_apply_eq_zero {x y : X} (h : y ≠ x) :
    vertex x y = 0 := by
  dsimp [vertex]
  aesop

lemma eq_affineCombination (s : TopologicalSimplex X) :
    s = affineCombination .univ vertex s (by simp) (by simp) := by
  ext x
  simp
  rw [Finset.sum_eq_single x _ (by aesop),
    vertex_apply_self, mul_one]
  intro _ _ hb
  simp [vertex_apply_eq_zero hb.symm]

lemma exists_eq_affineCombination (s : TopologicalSimplex X) :
    ∃ (w : X → ℝ) (hw₀ : ∀ (i : X), 0 ≤ w i) (hw₁ : ∑ i, w i = 1),
      s = affineCombination .univ vertex w hw₀ hw₁ :=
  ⟨_, _, _, eq_affineCombination s⟩

lemma vertex_injective : Function.Injective (vertex (X := X)) := by
  intro x y h
  replace h := DFunLike.congr_fun h x
  by_contra!
  simp [vertex_apply_self, vertex_apply_eq_zero this] at h

variable (X) in
lemma eq_convexHull :
    topologicalSimplex X =
      convexHull ℝ (Set.range (fun x ↦ ⇑(vertex x))) := by
  refine subset_antisymm (fun f hf ↦ ?_)
    (convexHull_min (by rintro _ ⟨i, rfl⟩; simp) (convex X))
  obtain ⟨w, hw₀, hw₁, h⟩ := exists_eq_affineCombination ⟨f, hf⟩
  rw [Subtype.ext_iff] at h
  subst h
  apply affineCombination_mem_convexHull
  all_goals aesop

end

instance [Nonempty X] : Nonempty (TopologicalSimplex X) := by
  classical
  exact ⟨vertex (Classical.arbitrary _)⟩

instance [Nontrivial X] : Nontrivial (TopologicalSimplex X) where
  exists_pair_ne := by
    classical
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    exact ⟨vertex x, vertex y, fun h ↦ hxy (vertex_injective h)⟩

instance [Subsingleton X] : Subsingleton (TopologicalSimplex X) where
  allEq s t := by
    ext i
    have (u : TopologicalSimplex X) : u i = 1 := by
      rw [← u.sum_eq_one, Finset.sum_eq_single i _ (by simp)]
      intro j _ hj
      exact (hj (Subsingleton.elim j i)).elim
    simp [this]

instance [Unique X] : Unique (TopologicalSimplex X) where
  default := .mk 1 (by
    rw [Finset.sum_eq_single default, Pi.one_apply]
    all_goals aesop) (by simp)
  uniq := by subsingleton

noncomputable def linearMap (f : X → Y) : (X → ℝ) →ₗ[ℝ] (Y → ℝ) :=
  (((Finsupp.linearEquivFunOnFinite ℝ ℝ Y)).comp (Finsupp.lmapDomain ℝ ℝ f)).comp
    (Finsupp.linearEquivFunOnFinite ℝ ℝ X).symm.toLinearMap

lemma linearMap_apply_apply [DecidableEq Y] (f : X → Y) (s : X → ℝ) (y : Y) :
    linearMap f s y = (Finset.univ.filter (fun (x : X) ↦ f x = y)).sum s := by
  obtain ⟨s, rfl⟩ := (Finsupp.linearEquivFunOnFinite ℝ ℝ X).surjective s
  dsimp [linearMap]
  simp only [LinearEquiv.symm_apply_apply, Finsupp.linearEquivFunOnFinite_apply]
  nth_rw 1 [← Finsupp.univ_sum_single s]
  rw [Finsupp.mapDomain_finset_sum]
  simp only [Finsupp.mapDomain_single, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finset.sum_filter]
  congr
  ext x
  by_cases hx : f x = y
  · simp [hx]
  · rw [if_neg hx, Finsupp.single_eq_of_ne hx]

@[continuity]
lemma continuous_linearMap (f : X → Y) : Continuous (linearMap f) := by
  classical
  refine continuous_pi (fun y ↦ ?_)
  simp only [linearMap_apply_apply]
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

@[simp]
lemma vertex_eq_piSingle [DecidableEq X] (x : X) :
    ⇑(vertex x) = Pi.single x 1 := by
  ext y
  by_cases hy : y = x
  · subst hy
    simp
  · rw [vertex_apply_eq_zero hy, Pi.single_eq_of_ne hy]

@[simp]
lemma linearMap_apply_piSingle [DecidableEq X] [DecidableEq Y] (f : X → Y) (x : X) (t : ℝ) :
    linearMap f (Pi.single x t) = Pi.single (f x) t := by
  simp [linearMap]

lemma linearMap_image (f : X → Y) :
    Set.image (linearMap f) (topologicalSimplex X) ⊆ topologicalSimplex Y := by
  classical
  simp only [eq_convexHull, (linearMap f).isLinear.image_convexHull]
  apply convexHull_mono
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨f x, by simp⟩

variable (X) in
@[simp]
lemma linearMap_id : linearMap (id : X → X) = .id := by
  classical
  aesop

lemma linearMap_comp (f : X → Y) (g : Y → Z) :
    linearMap (g.comp f) = (linearMap g).comp (linearMap f) := by
  classical
  aesop

noncomputable def map (f : X → Y) (s : TopologicalSimplex X) : TopologicalSimplex Y :=
  ⟨linearMap f s, linearMap_image f (by aesop)⟩

@[simp]
lemma map_coe (f : X → Y) (s : TopologicalSimplex X) :
    ⇑(map f s) = linearMap f s := rfl

@[continuity, fun_prop]
lemma continuous_map (f : X → Y) : Continuous (map f) :=
  Continuous.subtype_mk ((continuous_linearMap f).comp continuous_induced_dom) _

variable (X) in
@[simp]
lemma map_id_apply (x) : map (id : X → X) x = x := by
  aesop

lemma map_comp_apply (f : X → Y) (g : Y → Z) (x) :
    map g (map f x) = map (g.comp f) x := by
  ext
  simp [linearMap_comp]

section

open unitInterval

variable [DecidableEq X] (x₀ x₁ : X)

noncomputable def fromUnitInterval (t : I) : TopologicalSimplex X :=
  (convex X).fromUnitInterval (vertex x₀) (vertex x₁) t

@[simp]
lemma fromUnitInterval_coe (t : I) :
    ⇑(fromUnitInterval x₀ x₁ t) = (1 - t.1) • vertex x₀ + t.1 • vertex x₁:= rfl

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
  (convex X).continuous_fromUnitInterval _ _

@[simps]
noncomputable def homeoUnitInterval (h : x₀ ≠ x₁) (h' : {x₀, x₁} = Finset.univ) :
    TopologicalSimplex X ≃ₜ I where
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

noncomputable def homeoUnitInterval' : TopologicalSimplex (Fin 2) ≃ₜ I :=
  homeoUnitInterval _ _ Fin.zero_ne_one (by aesop)

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
  obj n := TopCat.of (TopologicalSimplex (Fin (n.len + 1)))
  map f := TopCat.ofHom ⟨_, TopologicalSimplex.continuous_map f⟩

/-- The functor `SimplexCategory ⥤ TopCat.{u}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps! obj map, pp_with_univ]
noncomputable def toTop : CosimplicialObject TopCat.{u} :=
  toTop₀ ⋙ TopCat.uliftFunctor

end SimplexCategory

end

#exit
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
