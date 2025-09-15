/-
Copyright (c) 2024 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
-- Homological algebra
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Exact

-- Module categories and linear algebra
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

-- Basic data structures and tactics
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals

-- Additional imports needed for our proofs
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Euler Polyhedron Formula via Homological Algebra

This file provides the core homological machinery for proving Euler's polyhedron formula
using chain complexes and homological algebra from Mathlib.

The key insight is that a geometric polyhedron gives rise to a chain complex
whose acyclicity implies the Euler characteristic formula.

## Main definitions

* `Polyhedron`: An abstract polyhedron with faces, dimensions, and incidence relations
* `GeometricPolyhedron`: A polyhedron equipped with a chain complex structure
* `toAugmentedComplex`: The augmented chain complex constructed from face spaces
* `isAcyclic`: Predicate for acyclic geometric polyhedra

## Main results

* `acyclic_augmented_euler_char`: For an acyclic geometric polyhedron,
  the Euler characteristic of the augmented complex equals (-1)^(dim + 1)
* `augmented_euler_characteristic_relation`: Relates the Euler characteristics
  of the augmented and original complexes

These results are used in `EulerPolyhedronFormula.lean` to prove:
- `euler_polyhedron_formula`: χ(P) = 1 + (-1)^dim
- `euler_formula_2d`: V - E + F = 2 for 2-dimensional polyhedra
-/

open CategoryTheory Limits HomologicalComplex

/-- A polyhedron parameterized by its face type α.
    This gives cleaner type signatures and more flexibility. -/
structure Polyhedron (α : Type) [Fintype α] where
  /-- The dimension function -/
  faceDim : α → ℕ
  /-- The maximum dimension of actual faces, not the ambient space -/
  dim : ℕ
  /-- All faces have dimension at most dim -/
  dim_le_max : ∀ f : α, faceDim f ≤ dim + 1
  /-- There exists at least one face of each dimension up to dim -/
  dim_surjective : ∀ k ≤ dim, ∃ f : α, faceDim f = k

  /-- Incidence relation between faces -/
  incident : α → α → Bool
  /-- Incidence is symmetric -/
  incident_symm : ∀ f g : α, incident f g = incident g f
  /-- Incidence only occurs between adjacent dimensions -/
  incident_dims : ∀ f g : α, incident f g → (faceDim g = faceDim f + 1 ∨ faceDim f = faceDim g + 1)

  /-- unique face of dimension dim + 1 -/
  unique_top_face : ∃! f : α, faceDim f = dim + 1

  /-- The unique top face is incident to all faces of dimension dim -/
  top_face_incident_all : ∀ f g : α,
    faceDim f = dim + 1 → faceDim g = dim → incident f g

  /-- No incidence above dim + 1 -/
  no_incidence_above_max_dim_plus_one : ∀ f g : α, faceDim f > dim + 1 → incident f g → False

  /-- Each edge (1-dimensional face) is incident to exactly 2 vertices (0-dimensional faces).
      This is essential for the augmentation map to work correctly. -/
  edge_vertex_count : ∀ e : α, faceDim e = 1 →
    (Finset.univ.filter (fun v => faceDim v = 0 ∧ incident e v)).card = 2

namespace Polyhedron

variable {α : Type} [Fintype α] (P : Polyhedron α)
end Polyhedron

section

variable {α : Type} [Fintype α] (P : Polyhedron α)


/-- Face count for dimension k -/
def faceCount (P : Polyhedron α) (k : ℕ) : ℕ :=
  Fintype.card { f : α // P.faceDim f = k }

open CategoryTheory

/-- Type representing k-dimensional chains (functions supported on k-faces) -/
def kChains (P : Polyhedron α) (k : ℕ) : Type :=
  { f : α // P.faceDim f = k } → ZMod 2

/-- AddCommGroup structure for k-dimensional chains -/
instance (P : Polyhedron α) (k : ℕ) : AddCommGroup (kChains P k) :=
  Pi.addCommGroup

/-- Module structure for k-dimensional chains -/
instance (P : Polyhedron α) (k : ℕ) : Module (ZMod 2) (kChains P k) :=
  Pi.module _ _ _

/-- k-dimensional chains form a finite-dimensional module -/
instance (P : Polyhedron α) (k : ℕ) : FiniteDimensional (ZMod 2) (kChains P k) := by
  -- kChains P k is functions from a finite type to ZMod 2
  unfold kChains
  -- Functions from a finite type to a finite field are finite-dimensional
  infer_instance

/-- k-dimensional chains form an additive commutative monoid -/
instance (P : Polyhedron α) (k : ℕ) : AddCommMonoid (kChains P k) := by
  -- kChains P k is functions from a finite type to ZMod 2
  unfold kChains
  infer_instance

/-- k-dimensional chains form a finite module -/
instance (P : Polyhedron α) (k : ℕ) : Module.Finite (ZMod 2) (kChains P k) := by
  -- kChains P k is functions from a finite type to ZMod 2
  unfold kChains
  -- Functions from a finite type to a finite ring form a finite module
  infer_instance

/-- The boundary operator: maps k-chains to (k-1)-chains -/
noncomputable def boundary (P : Polyhedron α) (k : ℕ) :
    kChains P (k + 1) →ₗ[ZMod 2] kChains P k where
  toFun := fun chain => fun ⟨g, hg⟩ =>
    -- Sum over all (k+1)-faces incident to g
    Finset.sum Finset.univ fun f : { f : α // P.faceDim f = k + 1 } =>
      if P.incident f.val g then chain f else 0
  map_add' := fun x y => by
    -- The boundary operator is linear
    funext ⟨g, hg⟩
    -- Simplify by unfolding the definition
    dsimp only
    -- Use the fact that the sum of if-then-else can be split
    have h : ∀ (f : { f : α // P.faceDim f = k + 1 }),
      (if P.incident f.val g then (x + y) f else 0) =
      (if P.incident f.val g then x f else 0) +
      (if P.incident f.val g then y f else 0) := by
      intro f
      by_cases hf : P.incident f.val g
      · simp only [if_pos hf]
        rfl
      · simp only [if_neg hf, add_zero]
    simp_rw [h]
    -- Now we have a sum of (x f + y f) which we need to split
    -- This is the same as boundary applied to x plus boundary applied to y
    -- Split the sum using Finset.sum_add_distrib
    rw [Finset.sum_add_distrib]
    rfl
  map_smul' := fun r x => by
    -- The boundary operator respects scalar multiplication
    funext ⟨g, hg⟩
    -- Simplify by unfolding the definition
    dsimp only
    simp only [RingHom.id_apply]
    -- Use the fact that scalar multiplication distributes through if-then-else
    have h : ∀ (f : { f : α // P.faceDim f = k + 1 }),
      (if P.incident f.val g then (r • x) f else 0) =
      r • (if P.incident f.val g then x f else 0) := by
      intro f
      by_cases hf : P.incident f.val g
      · simp only [if_pos hf]
        rfl
      · simp only [if_neg hf, smul_zero]
    simp_rw [h]
    -- Apply scalar multiplication distributes over sum
    rw [← Finset.smul_sum]
    rfl

/-- A polyhedron satisfies the chain complex property if ∂ₖ ∘ ∂ₖ₊₁ = 0 for all k.
    This is a fundamental property of geometric polyhedra: each k-face is reached
    from each (k+2)-face through an even number of paths. -/
def HasChainComplexProperty {α : Type} [Fintype α] (P : Polyhedron α) : Prop :=
  ∀ k, (boundary P k) ∘ₗ (boundary P (k + 1)) = 0

/-- A geometric polyhedron is a polyhedron that satisfies the chain complex property.
    This property ensures that the boundary of a boundary is zero (∂² = 0),
    which is a fundamental property of geometric polyhedra: each k-face is reached
    from each (k+2)-face through an even number of paths. -/
structure GeometricPolyhedron (α : Type) [Fintype α] extends Polyhedron α where
  /-- The boundary of boundary equals zero - this is the chain complex property -/
  boundary_of_boundary_eq_zero : ∀ k,
    (boundary toPolyhedron k) ∘ₗ (boundary toPolyhedron (k + 1)) = 0

/-- The chain complex of a geometric polyhedron over ZMod 2 -/
noncomputable def toChainComplex (GP : GeometricPolyhedron α) :
    ChainComplex (ModuleCat (ZMod 2)) ℕ where
  X k := ModuleCat.of (ZMod 2) (kChains GP.toPolyhedron k)
  d i j :=
    if h : (ComplexShape.down ℕ).Rel i j then
      -- j = i - 1, so we map from i-chains to (i-1)-chains
      -- But we need i ≥ 1 for this to make sense
      if hi : i > 0 then
        have : i = j + 1 := by
          simp [ComplexShape.down, ComplexShape.down'] at h
          omega
        ModuleCat.ofHom (this ▸ boundary GP.toPolyhedron j)
      else 0
    else 0
  shape := fun i j hij => by
    exact dif_neg hij
  d_comp_d' := fun i j k hij hjk => by
    -- We need to show: d i j ≫ d j k = 0
    -- hij : (ComplexShape.down ℕ).Rel i j means j + 1 = i
    -- hjk : (ComplexShape.down ℕ).Rel j k means k + 1 = j
    -- So we have k + 1 = j and j + 1 = i, thus k + 2 = i

    -- Unfold the definitions of d i j and d j k
    rw [dif_pos hij, dif_pos hjk]

    -- Get the index relationships
    have hi_eq : i = j + 1 := by
      simp [ComplexShape.down, ComplexShape.down'] at hij
      omega
    have hj_eq : j = k + 1 := by
      simp [ComplexShape.down, ComplexShape.down'] at hjk
      omega

    -- Handle the cases based on whether i > 0 and j > 0
    by_cases hi : i > 0
    · by_cases hj : j > 0
      · -- Both i > 0 and j > 0
        simp [hi, hj]
        -- We now have to show that the composition of the transported boundary maps is 0
        -- This follows from our axiom chain_complex_property

        -- We need to prove the composition of transported boundaries is zero
        -- Use the built-in boundary_of_boundary_eq_zero property
        have hprop := GP.boundary_of_boundary_eq_zero k
        -- This gives us: (boundary GP.toPolyhedron k) ∘ₗ (boundary GP.toPolyhedron (k + 1)) = 0

        -- Since j = k + 1, we can substitute
        have hj_k : j = k + 1 := hj_eq
        subst hj_k
        -- Now we know j = k + 1

        -- And since i = j + 1, we have i = k + 2
        have hi_k : i = k + 2 := by omega
        subst hi_k
        -- Now we know i = k + 2

        -- The goal simplifies significantly with these substitutions
        -- We're showing: ModuleCat.ofHom (boundary GP.toPolyhedron (k + 1)) ≫
        --                ModuleCat.ofHom (boundary GP.toPolyhedron k) = 0

        -- Convert to function composition
        ext x
        simp only []

        -- Apply the hypothesis
        rw [LinearMap.ext_iff] at hprop
        exact hprop _
      · -- i > 0 but j = 0, which is impossible since j + 1 = i
        simp [hi, hj]
    · -- i = 0, which is impossible since we need j + 1 = i and j ≥ 0
      simp [hi]

/-- Helper lemma: The number of vertices incident to an edge in the subtype representation
    equals the number in the original representation -/
lemma edge_vertex_count_subtype {α : Type} [Fintype α] (P : Polyhedron α)
    (e : { e : α // P.faceDim e = 1 }) :
    Finset.card (Finset.univ.filter (fun v : { v : α // P.faceDim v = 0 } =>
      P.incident e.val v.val)) =
    (Finset.univ.filter (fun v : α => P.faceDim v = 0 ∧ P.incident e.val v)).card := by
  -- Use a bijection between the two filtered sets
  refine Finset.card_bij
    (fun (v : { v : α // P.faceDim v = 0 })
         (hv : v ∈ Finset.univ.filter (fun w => P.incident e.val w.val)) =>
      v.val)
    ?_ ?_ ?_
  -- Show the mapping is into the target set
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨v.property, hv⟩
  -- Injectivity
  · intros v1 hv1 v2 hv2 heq
    exact Subtype.ext heq
  -- Surjectivity
  · intros v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    use ⟨v, hv.1⟩
    use (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hv.2 : _)

/-- The handshaking lemma: For any 1-chain, the sum of its boundary coefficients
    equals 0 in ZMod 2. This is the key property needed for the augmentation map.

    For example, a single edge e with vertices v1, v2 has boundary χ_v1 + χ_v2.
    The augmentation sums these coefficients: 1 + 1 = 2 = 0 in ZMod 2. -/
lemma handshaking_lemma {α : Type} [Fintype α] (P : Polyhedron α) :
  ∀ (chain : kChains P 1),
    Finset.sum Finset.univ (fun v : { v : α // P.faceDim v = 0 } =>
      (boundary P 0 chain) v) = 0 := by
  intro chain

  -- Step 1: Rewrite the sum to make the double summation explicit
  have step1 : Finset.sum Finset.univ (fun v : { v : α // P.faceDim v = 0 } =>
      (boundary P 0 chain) v) =
      Finset.sum Finset.univ (fun v : { v : α // P.faceDim v = 0 } =>
        Finset.sum Finset.univ (fun e : { e : α // P.faceDim e = 1 } =>
          if P.incident e.val v.val then chain e else 0)) := by
    simp only [boundary]
    congr 1

  -- Step 2: Exchange the order of summation
  have step2 : Finset.sum Finset.univ (fun v : { v : α // P.faceDim v = 0 } =>
        Finset.sum Finset.univ (fun e : { e : α // P.faceDim e = 1 } =>
          if P.incident e.val v.val then chain e else 0)) =
      Finset.sum Finset.univ (fun e : { e : α // P.faceDim e = 1 } =>
        Finset.sum Finset.univ (fun v : { v : α // P.faceDim v = 0 } =>
          if P.incident e.val v.val then chain e else 0)) := by
    -- Use Finset.sum_comm
    exact Finset.sum_comm

  -- Step 3: Factor out chain(e) from the inner sum
  have step3 : Finset.sum Finset.univ (fun e : { e : α // P.faceDim e = 1 } =>
        Finset.sum Finset.univ (fun v : { v : α // P.faceDim v = 0 } =>
          if P.incident e.val v.val then chain e else 0)) =
      Finset.sum Finset.univ (fun e : { e : α // P.faceDim e = 1 } =>
        chain e * Finset.card (Finset.univ.filter (fun v : { v : α // P.faceDim v = 0 } =>
          P.incident e.val v.val))) := by
    congr 1
    ext e
    -- For each edge e, the inner sum counts how many vertices are incident to e
    -- and multiplies by chain e
    simp_rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    -- The sum of chain e over the vertices incident to e
    rw [Finset.sum_const]
    -- This gives us chain e * card of incident vertices
    -- In ZMod 2, nsmul n x = n * x when n is cast to ZMod 2
    simp only [nsmul_eq_mul]
    ring

  -- Step 4: Use edge_vertex_count to show each edge has exactly 2 incident vertices
  have step4 : ∀ e : { e : α // P.faceDim e = 1 },
      Finset.card (Finset.univ.filter (fun v : { v : α // P.faceDim v = 0 } =>
        P.incident e.val v.val)) = 2 := by
    intro e
    rw [edge_vertex_count_subtype P e]
    exact P.edge_vertex_count e.val e.property

  -- Step 5: Simplify using step4
  have step5 : Finset.sum Finset.univ (fun e : { e : α // P.faceDim e = 1 } =>
        chain e * Finset.card (Finset.univ.filter (fun v : { v : α // P.faceDim v = 0 } =>
          P.incident e.val v.val))) =
      Finset.sum Finset.univ (fun e : { e : α // P.faceDim e = 1 } => chain e * 2) := by
    congr 1
    ext e
    rw [step4]
    norm_cast

  -- Step 6: Factor out the 2
  have step6 : Finset.sum Finset.univ (fun e : { e : α // P.faceDim e = 1 } => chain e * 2) =
      2 * Finset.sum Finset.univ (fun e : { e : α // P.faceDim e = 1 } => chain e) := by
    rw [← Finset.sum_mul]
    ring

  -- Step 7: In ZMod 2, we have 2 = 0
  have step7 : (2 : ZMod 2) = 0 := by
    rfl  -- 2 = 0 in ZMod 2 by definition

  -- Combine all steps
  rw [step1, step2, step3, step5, step6, step7]
  simp

-- Helper lemma: scalar multiplication distributes over sum for kChains
lemma kChains_smul_sum (P : Polyhedron α) (r : ZMod 2) (c : kChains P 0) :
    Finset.sum Finset.univ (fun f => (r • c) f) = r * Finset.sum Finset.univ (fun f => c f) := by
  -- Expand the definition of scalar multiplication on Pi types
  conv_lhs =>
    arg 2
    ext f
    rw [Pi.smul_apply, smul_eq_mul]
  -- Now we have: ∑ f, r * c f = r * ∑ f, c f
  rw [← Finset.mul_sum]

/-- The augmentation map for the chain complex -/
noncomputable def augmentationMap (P : Polyhedron α) :
    (kChains P 0) →ₗ[ZMod 2] (ZMod 2) where
  toFun := fun c => Finset.sum Finset.univ (fun f => c f)
  map_add' := fun _ _ => Finset.sum_add_distrib
  map_smul' := fun r c => kChains_smul_sum P r c

/-- The augmented chain complex adds ZMod 2 in degree -1 with augmentation ε : C₀ → ZMod 2 -/
noncomputable def toAugmentedComplex (GP : GeometricPolyhedron α) :
    ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  -- The augmentation map as a morphism in ModuleCat
  let ε : (toChainComplex GP).X 0 ⟶ ModuleCat.of (ZMod 2) (ZMod 2) :=
    ModuleCat.ofHom (augmentationMap GP.toPolyhedron)
  -- The key property: d₁ ≫ ε = 0
  have hε : (toChainComplex GP).d 1 0 ≫ ε = 0 := by
    -- This follows from the handshaking lemma
    ext x
    -- We need to show that ε(d₁(x)) = 0 for any 1-chain x
    -- That is: the sum of all coefficients in the boundary of x equals 0
    simp [ε, augmentationMap]
    -- Apply the handshaking lemma
    exact handshaking_lemma GP.toPolyhedron x
  ChainComplex.augment (toChainComplex GP) ε hε


/-- The augmented complex is acyclic if all its homology vanishes -/
def isAcyclic (GP : GeometricPolyhedron α) : Prop :=
  (toAugmentedComplex GP).Acyclic


/-- The Euler characteristic as alternating sum of face counts -/
def eulerCharacteristic (P : Polyhedron α) : ℤ :=
  Finset.sum (Finset.range (P.dim + 1))
    (fun k => (-1 : ℤ)^k * (faceCount P k : ℤ))


/-- The dimension of k-chains equals the number of k-faces.
    This is the fundamental connection: functions from k-faces to ZMod 2
    form a vector space of dimension equal to the cardinality of k-faces. -/
lemma kChains_finrank (P : Polyhedron α) (k : ℕ) :
    Module.finrank (ZMod 2) (kChains P k) = Fintype.card { f : α // P.faceDim f = k } := by
  -- kChains P k is definitionally { f : α // P.faceDim f = k } → ZMod 2
  unfold kChains
  -- Apply the standard result: faceDim(S → K) = |S| for finite S and field K
  exact Module.finrank_pi (ZMod 2)

/-- For the chain complex, the rank equals the face count -/
lemma chain_module_rank_eq_face_count (GP : GeometricPolyhedron α) (k : ℕ) :
    Module.finrank (ZMod 2) ((toChainComplex GP).X k) = faceCount GP.toPolyhedron k := by
  -- The k-th chain module is kChains GP.toPolyhedron k
  simp only [toChainComplex]
  -- Apply the fundamental dimension result
  rw [kChains_finrank]
  -- By definition of faceCount
  rfl

/-- Faces exist at all dimensions from 0 to dim + 1 -/
lemma exist_faces_at_all_dimensions (P : Polyhedron α) (k : ℕ) (hk : k ≤ P.dim + 1) :
    ∃ f : α, P.faceDim f = k := by
  by_cases h : k ≤ P.dim
  · -- For k ≤ dim, use dim_surjective
    exact P.dim_surjective k h
  · -- For k = dim + 1, use unique_top_face
    -- Since k ≤ dim + 1 and ¬(k ≤ dim), we have k = dim + 1
    have : k = P.dim + 1 := by omega
    obtain ⟨top_face, htop_dim, _⟩ := P.unique_top_face
    use top_face
    rw [this]
    exact htop_dim

-- The set of faces at dimension dim + 1 has a unique element
noncomputable instance unique_faces_at_top_dim (P : Polyhedron α) :
    Unique { f : α // P.faceDim f = P.dim + 1 } := by
  -- We know there exists a unique face at dimension dim + 1
  have hex := P.unique_top_face
  -- Choose any face at that dimension as the default
  choose top_face htop using hex.exists
  refine {
    default := ⟨top_face, htop⟩
    uniq := fun ⟨f, hf⟩ => by
      ext
      -- All faces at this dimension are equal by uniqueness
      exact hex.unique hf htop
  }


/-- Helper lemma for reindexing sums in the augmented characteristic relation -/
private lemma sum_reindex_helper (d : ℕ) (f : ℕ → ℤ) :
    Finset.sum (Finset.range (d + 2)) (fun k => (-1 : ℤ)^k * f k) =
    f 0 + Finset.sum (Finset.range (d + 1)) (fun k => (-1 : ℤ)^(k + 1) * f (k + 1)) := by
  -- Split off the first term: Σ_{k=0}^{d+1} = f(0) + Σ_{k=1}^{d+1}
  -- After splitting, the sum from 1 to d+1 can be reindexed to get the desired form
  rw [Finset.sum_range_succ_eq_head]
  -- Reindex the sum from k=1 to d+1 as k' = k-1, so k' runs from 0 to d
  have : Finset.sum (Finset.range (d + 1)) (fun k => (-1 : ℤ)^(k + 1) * f (k + 1)) =
         Finset.sum (Finset.range (d + 1)) (fun k' => (-1 : ℤ)^(k' + 1) * f (k' + 1)) := by
    rfl
  rw [this]
  -- After reindexing, we can use the original sum
  rw [Finset.sum_range_succ]
  -- Now we have: f(0) + Σ_{x ∈ range(d+1)} (-1)^{x+1} * f(x+1)
  -- Which is exactly what we want on the RHS
  norm_num

/-- For the augmented complex, we work with indices shifted by 1.
    The augmented chain at degree k+1 corresponds to the original chain at degree k. -/
lemma augmented_chain_shift (GP : GeometricPolyhedron α) (k : ℕ) :
    (toAugmentedComplex GP).X (k + 1) = (toChainComplex GP).X k := by
  -- By construction of the augmented complex
  rfl

/-- The augmented complex at position 0 has dimension 1 -/
lemma augmented_dim_zero (GP : GeometricPolyhedron α) :
    Module.finrank (ZMod 2) ((toAugmentedComplex GP).X 0) = 1 := by
  -- By definition of toAugmentedComplex and ChainComplex.augment,
  -- position 0 contains the augmentation module which is ZMod 2
  unfold toAugmentedComplex
  simp only [ChainComplex.augment_X_zero]
  -- The augmentation module is ZMod 2, which has dimension 1 over itself
  exact Module.finrank_self (ZMod 2)

/-- The Euler characteristic of the augmented complex A(P) relates to
    the original by χ(A(P)) = 1 - χ(P) -/
lemma augmented_euler_characteristic_relation (GP : GeometricPolyhedron α) [DecidableEq α] :
    ChainComplex.eulerChar (toAugmentedComplex GP) (GP.toPolyhedron.dim + 1) =
    1 - eulerCharacteristic GP.toPolyhedron := by
  unfold ChainComplex.eulerChar eulerCharacteristic
  -- Let's denote the augmented complex for clarity
  let A := toAugmentedComplex GP
  let d := GP.toPolyhedron.dim
  -- Step 1: χ_A = Σ_{k=0}^{d+1} (-1)^k * faceDim C^A_k (by definition)
  -- This is already expanded by unfold
  -- Step 2: Split off the first term using our helper lemma
  have step2 := sum_reindex_helper d (fun k => (Module.finrank (ZMod 2) (A.X k) : ℤ))
  -- Step 3: The augmented complex at position 0 has dimension 1
  have aug_zero : Module.finrank (ZMod 2) (A.X 0) = 1 := augmented_dim_zero GP
  -- Step 4: For k ≥ 1, A.X_k = (toChainComplex GP).X_{k-1}
  have shift_relation : ∀ k, 1 ≤ k → k ≤ d + 1 →
    Module.finrank (ZMod 2) (A.X k) =
    Module.finrank (ZMod 2) ((toChainComplex GP).X (k - 1)) := by
    intros k hk_pos hk_bound
    -- For k ≥ 1, we can write k = (k-1) + 1
    -- Then A.X k = A.X ((k-1) + 1) = (toChainComplex GP).X (k-1)
    -- by ChainComplex.augment_X_succ
    have hk_eq : k = (k - 1) + 1 := (Nat.sub_add_cancel hk_pos).symm
    calc Module.finrank (ZMod 2) (A.X k)
        = Module.finrank (ZMod 2) (A.X ((k - 1) + 1)) := by rw [← hk_eq]
        _ = Module.finrank (ZMod 2) ((toChainComplex GP).X (k - 1)) := by
          unfold A toAugmentedComplex
          simp only [ChainComplex.augment_X_succ]
  -- Step 5: Rewrite using the shift relation
  -- faceDim C^A_0 - Σ_{k=0}^d (-1)^k * faceDim C^A_{k+1}
  -- = faceDim C^A_0 - Σ_{k=0}^d (-1)^k * faceDim C_k
  have step5 : (Module.finrank (ZMod 2) (A.X 0) : ℤ) +
      Finset.sum (Finset.range (d + 1)) (fun k =>
        (-1 : ℤ)^(k + 1) * (Module.finrank (ZMod 2) (A.X (k + 1)) : ℤ)) =
    1 - Finset.sum (Finset.range (d + 1)) (fun k =>
        (-1 : ℤ)^k * (Module.finrank (ZMod 2) ((toChainComplex GP).X k) : ℤ)) := by
    rw [aug_zero]
    congr 1
    -- Transform the sum: Σ_{k=0}^d (-1)^{k+1} * faceDim A_{k+1} = -Σ_{k=0}^d (-1)^k * faceDim C_k
    have h1 : Finset.sum (Finset.range (d + 1)) (fun k =>
        (-1 : ℤ)^(k + 1) * (Module.finrank (ZMod 2) (A.X (k + 1)) : ℤ)) =
      Finset.sum (Finset.range (d + 1)) (fun k =>
        -(-1 : ℤ)^k * (Module.finrank (ZMod 2) ((toChainComplex GP).X k) : ℤ)) := by
      apply Finset.sum_congr rfl
      intros k hk
      simp only [Finset.mem_range] at hk
      have hk_bound : k + 1 ≤ d + 1 := Nat.succ_le_of_lt hk
      rw [shift_relation (k + 1) (Nat.succ_pos k) hk_bound]
      simp [pow_succ, neg_mul, mul_neg]
    rw [h1]
    simp [← Finset.sum_neg_distrib]
  -- Step 6: Apply face count relation
  -- We need to show the RHS equals 1 - eulerCharacteristic P
  have step6 : Finset.sum (Finset.range (d + 1)) (fun k =>
      (-1 : ℤ)^k * (Module.finrank (ZMod 2) ((toChainComplex GP).X k) : ℤ)) =
    Finset.sum (Finset.range (d + 1)) (fun k =>
      (-1 : ℤ)^k * (faceCount GP.toPolyhedron k : ℤ)) := by
    apply Finset.sum_congr rfl
    intros k hk
    simp only [Finset.mem_range] at hk
    congr 1
    have h' := chain_module_rank_eq_face_count GP k
    simp only [h']
  -- Combine all steps
  rw [step2, step5, step6]

-- FiniteDimensional instance for the chain complex
instance (GP : GeometricPolyhedron α) (i : ℕ) :
    FiniteDimensional (ZMod 2) ((toChainComplex GP).X i) := by
  -- toChainComplex GP).X i = ModuleCat.of (ZMod 2) (kChains GP.toPolyhedron i)
  -- We already have FiniteDimensional for kChains P i
  simp only [toChainComplex]
  exact inferInstance

-- FiniteDimensional instance for the augmented chain complex
instance (GP : GeometricPolyhedron α) (i : ℕ) :
    FiniteDimensional (ZMod 2) ((toAugmentedComplex GP).X i) := by
  unfold toAugmentedComplex
  -- This uses ChainComplex.augment which matches on i
  match i with
  | 0 =>
    -- At position 0, we have ZMod 2
    simp only [ChainComplex.augment_X_zero]
    exact FiniteDimensional.finiteDimensional_self (ZMod 2)
  | n + 1 =>
    -- At position n+1, we have (toChainComplex P h).X n
    simp only [ChainComplex.augment_X_succ]
    exact inferInstance

-- The boundary operator from the top dimension is non-zero
lemma boundary_from_top_dim_nonzero (P : Polyhedron α) [DecidableEq α] :
    boundary P P.dim ≠ 0 := by
  -- Proof by contradiction
  by_contra h
  -- Assume the boundary operator is zero
  have hzero : boundary P P.dim = 0 := h

  -- There exists a unique (dim + 1)-dimensional face
  obtain ⟨top_face, htop_dim, htop_unique⟩ := P.unique_top_face

  -- The unique non-zero element v in C_{dim + 1} is the characteristic function of top_face
  let v : kChains P (P.dim + 1) := fun ⟨f, hf⟩ => if f = top_face then 1 else 0

  -- v is non-zero
  have hv_nonzero : v ≠ 0 := by
    -- v(top_face) = 1 ≠ 0
    intro hcontra
    have : v ⟨top_face, htop_dim⟩ = 0 := by
      rw [hcontra]
      rfl
    simp only [v] at this
    -- We have if top_face = top_face then 1 else 0 = 0
    split_ifs at this with heq
    · -- Case: top_face = top_face, so we get 1 = 0
      norm_num at this
    · -- Case: top_face ≠ top_face, which is impossible
      contradiction

  -- top_face is incident to all dim-dimensional faces
  -- So the boundary of v sends every dim face to 1
  let v' := boundary P P.dim v

  -- By our assumption, boundary is zero, so v' = 0
  have hv'_zero : v' = 0 := by
    simp [v', hzero]

  -- But v' should send every dim face to 1 (by top_face_incident_all)
  -- Get any dim face
  obtain ⟨g, hg_dim⟩ := exist_faces_at_all_dimensions P P.dim (Nat.le_succ P.dim)

  -- top_face is incident to g
  have hincident := P.top_face_incident_all top_face g htop_dim hg_dim

  -- So v'(g) should be 1 (sum over incident faces of dimension dim + 1)
  -- Since top_face is the only face of dimension dim + 1, and it's incident to g,
  -- we have v'(g) = v(top_face) = 1
  have hv'_g : v' ⟨g, hg_dim⟩ = 1 := by
    -- v' = boundary P P.dim v
    -- By definition, (boundary P P.dim v) ⟨g, hg_dim⟩ is the sum over all
    -- (dim + 1)-faces f incident to g of v(f)
    simp only [v', boundary]
    -- The sum is over all f : { f : α // P.faceDim f = P.dim + 1 }
    -- But there's only one such face: top_face
    -- And top_face is incident to g (by top_face_incident_all)
    -- So the sum equals v(⟨top_face, htop_dim⟩) = 1
    have hunique : ∀ f : { f : α // P.faceDim f = P.dim + 1 }, f.val = top_face := by
      intro ⟨f, hf⟩
      simp
      exact htop_unique f hf
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    -- The sum is over a type with a unique element
    -- We can compute it directly
    have : Finset.univ =
        ({⟨top_face, htop_dim⟩} : Finset { f : α // P.faceDim f = P.dim + 1 }) := by
      ext ⟨f, hf⟩
      simp only [Finset.mem_singleton, Finset.mem_univ]
      constructor
      · intro _
        -- Need to show ⟨f, hf⟩ = ⟨top_face, htop_dim⟩
        apply Subtype.ext
        exact htop_unique f hf
      · intro _
        trivial
    rw [this, Finset.sum_singleton]
    -- Now we need: if P.incident top_face g then v ⟨top_face, htop_dim⟩ else 0 = 1
    rw [if_pos hincident]
    -- v ⟨top_face, htop_dim⟩ = if top_face = top_face then 1 else 0 = 1
    simp only [v]
    rfl

  -- But we also have v' = 0, so v'(g) = 0
  have hv'_g_zero : v' ⟨g, hg_dim⟩ = 0 := by
    rw [hv'_zero]
    rfl

  -- Contradiction: v'(g) = 1 and v'(g) = 0
  rw [hv'_g_zero] at hv'_g
  -- 1 = 0 in ZMod 2 is false
  norm_num at hv'_g

/-- The boundary map from the top dimension has trivial kernel -/
lemma boundary_from_top_dim_ker_zero (P : Polyhedron α) [DecidableEq α] :
    Module.finrank (ZMod 2) (LinearMap.ker (boundary P P.dim)) = 0 := by
  -- The domain (kChains at dim + 1) is 1-dimensional
  have hdim : Module.finrank (ZMod 2) (kChains P (P.dim + 1)) = 1 := by
    -- At dimension dim + 1, there's exactly one face (by unique_top_face)
    have hunique : Unique { f : α // P.faceDim f = P.dim + 1 } := unique_faces_at_top_dim P
    -- Functions from a Unique type to ZMod 2 have finrank 1
    unfold kChains
    rw [Module.finrank_fintype_fun_eq_card]
    rw [@Fintype.card_unique _ hunique _]

  -- The boundary operator is non-zero
  have hnonzero : boundary P P.dim ≠ 0 :=
    boundary_from_top_dim_nonzero P

  -- If ker has dimension 1, then the map is zero (since domain has dimension 1)
  by_contra h
  push_neg at h
  -- The kernel dimension is at most 1 (since domain has dimension 1)
  have hker_le : Module.finrank (ZMod 2) (LinearMap.ker (boundary P P.dim)) ≤ 1 := by
    calc Module.finrank (ZMod 2) (LinearMap.ker (boundary P P.dim))
        ≤ Module.finrank (ZMod 2) (kChains P (P.dim + 1)) := Submodule.finrank_le _
        _ = 1 := hdim
  -- So the kernel dimension is exactly 1
  have hker_eq : Module.finrank (ZMod 2) (LinearMap.ker (boundary P P.dim)) = 1 := by
    omega
  -- But then the map is zero (kernel = entire domain)
  have : LinearMap.ker (boundary P P.dim) = ⊤ := by
    -- The kernel has the same dimension as the whole space, so they're equal
    apply Submodule.eq_top_of_finrank_eq
    rw [hker_eq, hdim]
  have : boundary P P.dim = 0 := by
    ext x
    simp only [LinearMap.zero_apply]
    -- x is in the kernel since ker = ⊤
    have : x ∈ LinearMap.ker (boundary P P.dim) := by
      rw [this]; trivial
    exact this
  exact hnonzero this

/-- The boundary map from the top dimension has 1-dimensional image -/
lemma boundary_from_top_dim_image (P : Polyhedron α) [DecidableEq α] :
    Module.finrank (ZMod 2)
      (LinearMap.range (boundary P P.dim)) = 1 := by
  -- The domain (kChains at dim + 1) is 1-dimensional
  have hdim : Module.finrank (ZMod 2) (kChains P (P.dim + 1)) = 1 := by
    -- At dimension dim + 1, there's exactly one face (by unique_top_face)
    have hunique : Unique { f : α // P.faceDim f = P.dim + 1 } := unique_faces_at_top_dim P
    -- Functions from a Unique type to ZMod 2 have finrank 1
    unfold kChains
    rw [Module.finrank_fintype_fun_eq_card]
    rw [@Fintype.card_unique _ hunique _]

  -- The boundary operator is non-zero
  have hnonzero : boundary P P.dim ≠ 0 :=
    boundary_from_top_dim_nonzero P

  -- For a non-zero linear map from a 1-dimensional space, the image dimension is at most 1
  have hrange : Module.finrank (ZMod 2) (LinearMap.range (boundary P P.dim)) ≤ 1 := by
    -- The range is a submodule of the codomain, which is kChains P P.dim
    -- The range dimension is at most the domain dimension by rank-nullity
    -- Since domain has dimension 1, the range has dimension at most 1
    calc Module.finrank (ZMod 2) (LinearMap.range (boundary P P.dim))
        ≤ Module.finrank (ZMod 2) (kChains P (P.dim + 1)) := by
          -- Use rank-nullity: finrank(range) + finrank(ker) = finrank(domain)
          -- So finrank(range) ≤ finrank(domain)
          have := LinearMap.finrank_range_add_finrank_ker (boundary P P.dim)
          omega
        _ = 1 := hdim

  -- Since the map is non-zero from a 1-dimensional space, the kernel is 0-dimensional
  -- and hence the range is 1-dimensional by rank-nullity
  have hrank_nullity := LinearMap.finrank_range_add_finrank_ker (boundary P P.dim)
  rw [hdim] at hrank_nullity
  -- The kernel is trivial (0-dimensional) since the map is non-zero
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (boundary P P.dim)) = 0 :=
    boundary_from_top_dim_ker_zero P

  linarith

/-- For augmented complex, the differential shifts by one index -/
lemma augmented_d_shift (GP : GeometricPolyhedron α) (n : ℕ) :
    (toAugmentedComplex GP).d (n + 2) (n + 1) =
    (toChainComplex GP).d (n + 1) n := by
  simp only [toAugmentedComplex]
  -- The augmented differential at succ indices equals the original differential
  exact ChainComplex.augment_d_succ_succ _ _ _ _ _

/-- Augmented complex boundary from position dim + 2 has 1-dimensional image. -/
lemma augmented_boundary_from_top_image (GP : GeometricPolyhedron α) [DecidableEq α] :
    Module.finrank (ZMod 2)
      (LinearMap.range ((toAugmentedComplex GP).dFrom (GP.toPolyhedron.dim + 2)).hom) = 1 := by
  -- Establish the relation for dFrom_eq
  have aug_rel : (ComplexShape.down ℕ).Rel (GP.toPolyhedron.dim + 2) (GP.toPolyhedron.dim + 1) := by
    simp only [ComplexShape.down, ComplexShape.down']; omega

  -- dFrom is isomorphic to d via xNextIso
  have h_dFrom : (toAugmentedComplex GP).dFrom (GP.toPolyhedron.dim + 2) =
      (toAugmentedComplex GP).d (GP.toPolyhedron.dim + 2) (GP.toPolyhedron.dim + 1) ≫
      ((toAugmentedComplex GP).xNextIso aug_rel).inv :=
    (toAugmentedComplex GP).dFrom_eq aug_rel

  -- The range of dFrom has the same dimension as the range of d
  rw [h_dFrom]
  let ψ := ((toAugmentedComplex GP).xNextIso aug_rel).toLinearEquiv
  have : (((toAugmentedComplex GP).d (GP.toPolyhedron.dim + 2) (GP.toPolyhedron.dim + 1)) ≫
      ((toAugmentedComplex GP).xNextIso aug_rel).inv).hom =
      ψ.symm.toLinearMap ∘ₗ ((toAugmentedComplex GP).d (GP.toPolyhedron.dim + 2)
        (GP.toPolyhedron.dim + 1)).hom := rfl
  rw [this, LinearMap.range_comp]
  rw [LinearEquiv.finrank_map_eq ψ.symm]

  -- The augmented d at (dim+2, dim+1) equals the original d at (dim+1, dim)
  rw [augmented_d_shift GP GP.toPolyhedron.dim]

  -- The original d at (dim+1, dim) is the boundary operator
  have : (toChainComplex GP).d (GP.toPolyhedron.dim + 1) GP.toPolyhedron.dim =
      ModuleCat.ofHom (boundary GP.toPolyhedron GP.toPolyhedron.dim) := by
    simp only [toChainComplex]
    have pos : GP.toPolyhedron.dim + 1 > 0 := Nat.succ_pos _
    simp [pos]
  rw [this]

  -- Apply the main theorem about boundary from top dimension
  exact boundary_from_top_dim_image GP.toPolyhedron

/-- The image of dTo at position (GP.toPolyhedron.dim + 1) in the augmented complex has dimension 1.
    This follows from the relationship between dTo and dFrom, and the fact that
    dFrom at position (GP.toPolyhedron.dim + 2) maps from the top dimension. -/
lemma augmented_dTo_at_dim_plus_one_image_finrank (GP : GeometricPolyhedron α) [DecidableEq α] :
    Module.finrank (ZMod 2)
      (LinearMap.range ((toAugmentedComplex GP).dTo (GP.toPolyhedron.dim + 1)).hom) = 1 := by
  let C := toAugmentedComplex GP
  let n := GP.toPolyhedron.dim + 1
  -- dTo n is essentially C.d (n+1) n composed with an isomorphism
  -- Since isomorphisms preserve dimension, we can work with C.d (n+1) n
  have rel : (ComplexShape.down ℕ).Rel (n + 1) n := by
    simp [ComplexShape.down, ComplexShape.down']
  have dTo_eq : C.dTo n = (C.xPrevIso rel).hom ≫ C.d (n + 1) n := C.dTo_eq rel
  -- The range of dTo n has the same dimension as the range of C.d (n+1) n
  have range_eq : Module.finrank (ZMod 2) (LinearMap.range (C.dTo n).hom) =
                  Module.finrank (ZMod 2) (LinearMap.range (C.d (n + 1) n).hom) := by
    rw [dTo_eq]
    have : ((C.xPrevIso rel).hom ≫ C.d (n + 1) n).hom =
           (C.d (n + 1) n).hom ∘ₗ (C.xPrevIso rel).toLinearEquiv.toLinearMap := rfl
    rw [this, LinearMap.range_comp]
    have hsurj : Function.Surjective (C.xPrevIso rel).toLinearEquiv.toLinearMap :=
      (C.xPrevIso rel).toLinearEquiv.surjective
    rw [LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  -- Now we can use the fact that dFrom (n+1) also represents C.d (n+1) n
  have dFrom_eq : C.dFrom (n + 1) = C.d (n + 1) n ≫ (C.xNextIso rel).inv := C.dFrom_eq rel
  -- And dFrom (n+1) has range dimension 1
  have dFrom_range_one : Module.finrank (ZMod 2) (LinearMap.range (C.dFrom (n + 1)).hom) = 1 := by
    have : n + 1 = GP.toPolyhedron.dim + 2 := by simp [n]
    rw [this]
    exact augmented_boundary_from_top_image GP
  -- Since both dTo n and dFrom (n+1) represent C.d (n+1) n (up to isomorphism),
  -- we can transfer the dimension result
  rw [range_eq]
  -- Now we need to show Module.finrank (ZMod 2) (LinearMap.range (C.d (n + 1) n).hom) = 1
  -- Since dFrom (n+1) = C.d (n+1) n ≫ iso and isomorphisms preserve dimension
  convert dFrom_range_one using 2
  rw [dFrom_eq]
  -- The composition with an isomorphism preserves the dimension of the range
  have : ((C.d (n + 1) n) ≫ (C.xNextIso rel).inv).hom =
         (C.xNextIso rel).toLinearEquiv.symm.toLinearMap ∘ₗ (C.d (n + 1) n).hom := rfl
  rw [this, LinearMap.range_comp]
  -- The map by an isomorphism preserves dimension
  rw [← LinearEquiv.finrank_map_eq (C.xNextIso rel).toLinearEquiv.symm]

/-- The kernel of dFrom 0 in the augmented complex has dimension 1,
    since dFrom 0 is the zero map and X 0 has dimension 1. -/
lemma augmented_dFrom_zero_ker_finrank (GP : GeometricPolyhedron α) [DecidableEq α] :
    Module.finrank (ZMod 2) (LinearMap.ker ((toAugmentedComplex GP).dFrom 0).hom) = 1 := by
  -- Since dFrom 0 = 0, ker(dFrom 0) = the whole space C.X 0
  have h1 : ((toAugmentedComplex GP).dFrom 0).hom = 0 := by
    -- For complex, dFrom_zero applies
    have : (toAugmentedComplex GP).dFrom 0 = 0 := by
      apply HomologicalComplex.dFrom_eq_zero
      -- We need to show ¬(ComplexShape.down).Rel 0 (ComplexShape.down).next 0)
      -- which means there's no j such that j+1=0
      intro h
      simp [ComplexShape.down] at h
    rw [this]
    rfl
  rw [h1, LinearMap.ker_zero]
  -- ker(0) = ⊤ = the whole space, which is linearly equivalent to C.X 0
  have : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) ((toAugmentedComplex GP).X 0)) =
      Module.finrank (ZMod 2) ((toAugmentedComplex GP).X 0) := by
    -- Use that topEquiv is a linear equivalence from ⊤ to C.X 0
    exact LinearEquiv.finrank_eq (Submodule.topEquiv :
          (⊤ : Submodule (ZMod 2) ((toAugmentedComplex GP).X 0)) ≃ₗ[ZMod 2]
          ((toAugmentedComplex GP).X 0))
  rw [this]
  exact augmented_dim_zero GP

/-- The rank-nullity theorem for chain complexes -/
lemma chain_complex_rank_nullity (C : ChainComplex (ModuleCat (ZMod 2)) ℕ) (k : ℕ)
    [FiniteDimensional (ZMod 2) (C.X k)] :
    Module.finrank (ZMod 2) (C.X k) =
    Module.finrank (ZMod 2) (LinearMap.range (C.dFrom k).hom) +
    Module.finrank (ZMod 2) (LinearMap.ker (C.dFrom k).hom) := by
  rw [LinearMap.finrank_range_add_finrank_ker]

/-- Helper: Get the short complex at position k of a chain complex -/
noncomputable abbrev chainComplexSc (C : ChainComplex (ModuleCat (ZMod 2)) ℕ) (k : ℕ) :
    ShortComplex (ModuleCat (ZMod 2)) := C.sc k

/-- The short complex at position k has f = dTo k and g = dFrom k -/
lemma sc_morphisms (C : ChainComplex (ModuleCat (ZMod 2)) ℕ) (k : ℕ) :
    (C.sc k).f = C.dTo k ∧ (C.sc k).g = C.dFrom k := by
  constructor <;> rfl

-- Note: We can directly use the fact that C.Acyclic means ∀ k, C.ExactAt k
-- and C.ExactAt k is definitionally equal to (C.sc k).Exact
-- So we don't need intermediate lemmas


/-- For an acyclic polyhedron, the augmented complex is acyclic,
    so the Euler characteristic of the augmented complex has a specific value
    determined by the dimension. -/
lemma acyclic_augmented_euler_char (GP : GeometricPolyhedron α) [DecidableEq α]
    (hacyclic : isAcyclic GP) :
    ChainComplex.eulerChar (toAugmentedComplex GP) (GP.toPolyhedron.dim + 1) =
    (-1 : ℤ)^(GP.toPolyhedron.dim + 1) := by
  let C := toAugmentedComplex GP
  let n := GP.toPolyhedron.dim + 1
  -- Define the three sequences for the telescoping sum:
  -- a(k) = dimension of k-th chain group
  let a : ℕ → ℤ := fun k => (Module.finrank (ZMod 2) (C.X k) : ℤ)
  -- b(k) = rank of boundary operator from C_k to C_{k-1} (dimension of image)
  let b : ℕ → ℤ := fun k =>
    if k = 0 then 0  -- d_0 maps C_0 → 0 (augmentation to trivial)
    else (Module.finrank (ZMod 2) (LinearMap.range (C.dFrom k).hom) : ℤ)
  -- c(k) = dimension of kernel of boundary operator from C_k to C_{k-1}
  let c : ℕ → ℤ := fun k =>
    (Module.finrank (ZMod 2) (LinearMap.ker (C.dFrom k).hom) : ℤ)

  -- Step 1: Rank-nullity gives a(k) = b(k) + c(k)
  have rank_nullity : ∀ k ≤ n, a k = b k + c k := by
    intro k hk
    unfold a b c
    -- The rank-nullity theorem says: faceDim(V) = faceDim(image(f)) + faceDim(kernel(f))
    split_ifs with hzero
    · -- Case k = 0: The augmented complex has ℤ at position 0
      -- dFrom 0 is the zero map, so image = 0 and kernel = all of C.X 0 = ℤ
      -- We need to show: finrank(C.X 0) = 0 + finrank(ker(dFrom 0))
      -- Since C = toAugmentedComplex P, we can use our lemmas
      rw [hzero]
      have finrank_zero : Module.finrank (ZMod 2) (C.X 0) = 1 := augmented_dim_zero GP
      have ker_finrank : Module.finrank (ZMod 2) (LinearMap.ker (C.dFrom 0).hom) = 1 :=
        augmented_dFrom_zero_ker_finrank GP
      rw [finrank_zero, ker_finrank]
      simp only [Nat.cast_one, zero_add]
    · -- Case k > 0: apply the general rank-nullity theorem
      -- Now we have the FiniteDimensional instance, so we can use rank-nullity
      have rank_nullity_thm := chain_complex_rank_nullity C k
      rw [rank_nullity_thm]
      simp only [Nat.cast_add]

  -- We have that the augmented complex is acyclic by assumption
  have C_acyclic : C.Acyclic := by
    unfold isAcyclic at hacyclic
    exact hacyclic

  -- Step 2: Exactness gives b(k+1) = c(k) for telescoping
  have exactness_telescope : ∀ k ∈ Finset.range n, b (k + 1) = c k := by
    intro k hk
    unfold b c
    -- Since k+1 > 0 for any k : ℕ, we can simplify b(k+1)
    have hk_pos : k + 1 ≠ 0 := Nat.succ_ne_zero k
    rw [if_neg hk_pos]
    -- Now b(k+1) = finrank(range(dFrom(k+1))) and c(k) = finrank(ker(dFrom k))
    -- Since the complex is acyclic, the short complex at k is exact
    -- C.Acyclic means ∀ i, C.ExactAt i, and C.ExactAt k = (C.sc k).Exact by definition
    have hexact : (C.sc k).Exact := C_acyclic k
    -- Exactness means image(f) = kernel(g) for the short complex
    -- For the short complex: (C.sc k).f = C.dTo k and (C.sc k).g = C.dFrom k
    have ⟨hf, hg⟩ := sc_morphisms C k
    -- So exactness gives: range(dTo k) = ker(dFrom k)
    have img_eq_ker : LinearMap.range (C.dTo k).hom = LinearMap.ker (C.dFrom k).hom := by
      rw [← hf, ← hg]
      exact hexact.moduleCat_range_eq_ker
    -- We need to show finrank(range(dFrom(k+1))) = finrank(ker(dFrom k))
    -- We know from exactness that range(dTo k) = ker(dFrom k)
    rw [← img_eq_ker]
    -- So we need to show finrank(range(dFrom(k+1))) = finrank(range(dTo k))
    -- The key observation: both dTo k and dFrom (k+1) essentially represent the same
    -- differential C.d (k+1) k, just accessed through different APIs
    -- Since the chain complex shape is down ℕ, we have:
    -- - dTo k goes from C.X (c.prev k) = C.X (k+1) to C.X k
    -- - dFrom (k+1) goes from C.X (k+1) to C.X (c.next (k+1)) = C.X k
    -- - Both are essentially C.d (k+1) k up to isomorphisms

    -- We'll prove this by showing both have the same dimension as the range of C.d (k+1) k
    have rel : (ComplexShape.down ℕ).Rel (k + 1) k := by
      simp [ComplexShape.down, ComplexShape.down']

    -- First, let's relate dTo k to C.d (k+1) k
    have dTo_eq : C.dTo k = (C.xPrevIso rel).hom ≫ C.d (k + 1) k := C.dTo_eq rel
    -- dTo k is C.d (k+1) k pre-composed with an isomorphism
    -- Pre-composition with an isomorphism doesn't change range dimension
    have range_dTo : Module.finrank (ZMod 2) (LinearMap.range (C.dTo k).hom) =
                     Module.finrank (ZMod 2) (LinearMap.range (C.d (k + 1) k).hom) := by
      rw [dTo_eq]
      -- The morphism is a composition
      have : ((C.xPrevIso rel).hom ≫ C.d (k + 1) k).hom =
             (C.d (k + 1) k).hom ∘ₗ (C.xPrevIso rel).toLinearEquiv.toLinearMap := rfl
      rw [this, LinearMap.range_comp]
      -- Since xPrevIso is surjective, range(g ∘ f) = range(g) when f is surjective
      have hsurj : Function.Surjective (C.xPrevIso rel).toLinearEquiv.toLinearMap :=
        (C.xPrevIso rel).toLinearEquiv.surjective
      rw [LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]

    -- Now let's relate dFrom (k+1) to C.d (k+1) k
    have dFrom_eq : C.dFrom (k + 1) = C.d (k + 1) k ≫ (C.xNextIso rel).inv := C.dFrom_eq rel
    -- dFrom (k+1) is C.d (k+1) k post-composed with an isomorphism
    -- Post-composition with an isomorphism preserves range dimension
    have range_dFrom : Module.finrank (ZMod 2) (LinearMap.range (C.dFrom (k + 1)).hom) =
                       Module.finrank (ZMod 2) (LinearMap.range (C.d (k + 1) k).hom) := by
      rw [dFrom_eq]
      -- The morphism is a composition
      have : ((C.d (k + 1) k) ≫ (C.xNextIso rel).inv).hom =
             (C.xNextIso rel).toLinearEquiv.symm.toLinearMap ∘ₗ (C.d (k + 1) k).hom := rfl
      rw [this, LinearMap.range_comp]
      -- Post-composition with an isomorphism gives an isomorphic submodule
      -- Use the fact that isomorphic submodules have the same dimension
      have iso_preserve : Module.finrank (ZMod 2)
          (Submodule.map (C.xNextIso rel).toLinearEquiv.symm.toLinearMap
            (LinearMap.range (C.d (k + 1) k).hom)) =
          Module.finrank (ZMod 2) (LinearMap.range (C.d (k + 1) k).hom) := by
        rw [LinearEquiv.finrank_map_eq]
      exact iso_preserve

    -- Therefore dTo k and dFrom (k+1) have the same range dimension
    rw [range_dTo, ← range_dFrom]

  -- Step 3: Boundary condition at 0
  have b_zero : b 0 = 0 := by
    unfold b
    rfl

  -- Step 4: Boundary condition at dim + 1
  have c_max : c n = 1 := by
    unfold c n
    -- By exactness at position n = P.dim + 1:
    -- ker(dFrom n) = image(dTo n) = image(dFrom (n+1))
    -- So faceDim(ker(dFrom n)) = faceDim(image(dFrom (n+1)))
    -- Since the complex is acyclic, the short complex at n is exact
    have hexact : (C.sc n).Exact := C_acyclic n
    -- The kernel equals the image of the map from position n+1
    have ker_dim : Module.finrank (ZMod 2) (LinearMap.ker (C.dFrom n).hom) =
                   Module.finrank (ZMod 2) (LinearMap.range (C.dTo n).hom) := by
      -- Use exactness: range(dTo n) = ker(dFrom n)
      have ⟨hf, hg⟩ := sc_morphisms C n
      have h := hexact.moduleCat_range_eq_ker
      -- h : range((sc C n).f) = ker((sc C n).g)
      -- We know (sc C n).f = dTo C n and (sc C n).g = dFrom C n
      rw [hf, hg] at h
      -- Now h : range(dTo C n) = ker(dFrom C n)
      rw [← h]
    -- By the relationship between dTo and dFrom (they're the same up to isomorphism)
    have img_dim : Module.finrank (ZMod 2) (LinearMap.range (C.dTo n).hom) = 1 :=
      augmented_dTo_at_dim_plus_one_image_finrank GP
    rw [ker_dim, img_dim]
    simp only [Nat.cast_one]

  -- Apply the telescoping sum theorem from TelescopingSum.lean
  have telescoping := Finset.alternating_telescoping_sum n a b c rank_nullity exactness_telescope

  -- The Euler characteristic is the alternating sum of dimensions
  have euler_char_as_sum : ChainComplex.eulerChar C (GP.toPolyhedron.dim + 1) =
    Finset.sum (Finset.range (n + 1)) (fun k => (-1 : ℤ)^k * a k) :=
    rfl  -- This is true by definition of ChainComplex.eulerChar

  -- Combine everything
  rw [euler_char_as_sum, telescoping, b_zero, c_max]
  simp only [n]
  -- We have 0 + (-1)^(P.dim + 1) * 1 = (-1)^(P.dim + 1)
  ring

end
