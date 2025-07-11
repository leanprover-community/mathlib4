/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
# The low-degree homology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file contains specialised API for
the cycles and group homology  of a `k`-linear `G`-representation `A` in degrees 0, 1 and 2.
In `RepresentationTheory/Homological/GroupHomology/Basic.lean`, we define the `n`th group homology
of `A` to be the homology of a complex `inhomogeneousChains A`, whose objects are
`(Fin n →₀ G) → A`; this is unnecessarily unwieldy in low degree.

Given an additive abelian group `A` with an appropriate scalar action of `G`, we provide support
for turning a finsupp `f : G →₀ A` satisfying the 1-cycle identity into an element of the
`cycles₁` of the representation on `A` corresponding to the scalar action. We also do this for
0-boundaries, 1-boundaries, 2-cycles and 2-boundaries.

The file also contains an identification between the definitions in
`RepresentationTheory/Homological/GroupHomology/Basic.lean`, `groupHomology.cycles A n`, and the
`cyclesₙ` in this file for `n = 1, 2`, as well as an isomorphism `groupHomology.cycles A 0 ≅ A.V`.

## TODO
  * Provide API for the natural maps `cyclesₙ A → Hn A` for `n = 1, 2`.

-/

universe v u

noncomputable section

open CategoryTheory Limits Representation Rep Finsupp

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

namespace groupHomology

section Chains
variable [DecidableEq G]

/-- The 0th object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `A` as a `k`-module. -/
def chainsIso₀ : (inhomogeneousChains A).X 0 ≅ A.V :=
  (LinearEquiv.finsuppUnique _ _ _).toModuleIso

/-- The 1st object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `G →₀ A` as a `k`-module. -/
def chainsIso₁ : (inhomogeneousChains A).X 1 ≅ ModuleCat.of k (G →₀ A) :=
  (Finsupp.domLCongr (Equiv.funUnique (Fin 1) G)).toModuleIso

/-- The 2nd object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `G² →₀ A` as a `k`-module. -/
def chainsIso₂ : (inhomogeneousChains A).X 2 ≅ ModuleCat.of k (G × G →₀ A) :=
  (Finsupp.domLCongr (piFinTwoEquiv fun _ => G)).toModuleIso

/-- The 3rd object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `G³ → A` as a `k`-module. -/
def chainsIso₃ : (inhomogeneousChains A).X 3 ≅ ModuleCat.of k (G × G × G →₀ A) :=
  (Finsupp.domLCongr ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))).toModuleIso

end Chains

section Differentials

/-- The 0th differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G →₀ A) → A`. It is defined by `single g a ↦ ρ_A(g⁻¹)(a) - a.` -/
def d₁₀ : ModuleCat.of k (G →₀ A) ⟶ A.V :=
  ModuleCat.ofHom <| lsum k fun g => A.ρ g⁻¹ - LinearMap.id

@[simp]
theorem d₁₀_single (g : G) (a : A) : d₁₀ A (single g a) = A.ρ g⁻¹ a - a := by
  simp [d₁₀]

theorem d₁₀_single_one (a : A) : d₁₀ A (single 1 a) = 0 := by
  simp [d₁₀]

theorem d₁₀_single_inv (g : G) (a : A) :
    d₁₀ A (single g⁻¹ a) = - d₁₀ A (single g (A.ρ g a)) := by
  simp [d₁₀]

theorem range_d₁₀_eq_coinvariantsKer :
    LinearMap.range (d₁₀ A).hom = Coinvariants.ker A.ρ := by
  symm
  apply Submodule.span_eq_of_le
  · rintro _ ⟨x, rfl⟩
    use single x.1⁻¹ x.2
    simp [d₁₀]
  · rintro x ⟨y, hy⟩
    induction' y using Finsupp.induction with _ _ _ _ _ h generalizing x
    · simp [← hy]
    · simpa [← hy, add_sub_add_comm, sum_add_index, d₁₀_single (G := G)]
        using Submodule.add_mem _ (Coinvariants.mem_ker_of_eq _ _ _ rfl) (h rfl)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma d₁₀_comp_coinvariantsMk : d₁₀ A ≫ (coinvariantsMk k G).app A = 0 := by
  ext
  simp [d₁₀]

/-- The 0th differential in the complex of inhomogeneous chains of a `G`-representation `A` as a
linear map into the `k`-submodule of `A` spanned by elements of the form
`ρ(g)(x) - x, g ∈ G, x ∈ A`. -/
def chains₁ToCoinvariantsKer :
    ModuleCat.of k (G →₀ A) ⟶ ModuleCat.of k (Coinvariants.ker A.ρ) :=
  ModuleCat.ofHom <| (d₁₀ A).hom.codRestrict _ <|
    range_d₁₀_eq_coinvariantsKer A ▸ LinearMap.mem_range_self _

@[simp]
theorem d₁₀_eq_zero_of_isTrivial [A.IsTrivial] : d₁₀ A = 0 := by
  ext
  simp [d₁₀]

/-- The 1st differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G² →₀ A) → (G →₀ A)`. It is defined by
`a·(g₁, g₂) ↦ ρ_A(g₁⁻¹)(a)·g₂ - a·g₁g₂ + a·g₁`. -/
def d₂₁ : ModuleCat.of k (G × G →₀ A) ⟶ ModuleCat.of k (G →₀ A) :=
  ModuleCat.ofHom <| lsum k fun g => lsingle g.2 ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2) + lsingle g.1

variable {A}

@[simp]
lemma d₂₁_single (g : G × G) (a : A) :
    d₂₁ A (single g a) = single g.2 (A.ρ g.1⁻¹ a) - single (g.1 * g.2) a + single g.1 a := by
  simp [d₂₁]

lemma d₂₁_single_one_fst (g : G) (a : A) :
    d₂₁ A (single (1, g) a) = single 1 a := by
  simp [d₂₁]

lemma d₂₁_single_one_snd (g : G) (a : A) :
    d₂₁ A (single (g, 1) a) = single 1 (A.ρ g⁻¹ a) := by
  simp [d₂₁]

lemma d₂₁_single_inv_self_ρ_sub_self_inv (g : G) (a : A) :
    d₂₁ A (single (g⁻¹, g) (A.ρ g⁻¹ a) - single (g, g⁻¹) a) =
      single 1 a - single 1 (A.ρ g⁻¹ a) := by
  simp only [map_sub, d₂₁_single (G := G), inv_inv, self_inv_apply, inv_mul_cancel,
    mul_inv_cancel]
  abel

lemma d₂₁_single_self_inv_ρ_sub_inv_self (g : G) (a : A) :
    d₂₁ A (single (g, g⁻¹) (A.ρ g a) - single (g⁻¹, g) a) =
      single 1 a - single 1 (A.ρ g a) := by
  simp only [map_sub, d₂₁_single (G := G), inv_self_apply, mul_inv_cancel, inv_inv,
    inv_mul_cancel]
  abel

lemma d₂₁_single_ρ_add_single_inv_mul (g h : G) (a : A) :
    d₂₁ A (single (g, h) (A.ρ g a) + single (g⁻¹, g * h) a) =
      single g (A.ρ g a) + single g⁻¹ a := by
  simp only [map_add, d₂₁_single (G := G), inv_self_apply, inv_inv, inv_mul_cancel_left]
  abel

lemma d₂₁_single_inv_mul_ρ_add_single (g h : G) (a : A) :
    d₂₁ A (single (g⁻¹, g * h) (A.ρ g⁻¹ a) + single (g, h) a) =
      single g⁻¹ (A.ρ g⁻¹ a) + single g a := by
  simp only [map_add, d₂₁_single (G := G), inv_inv, self_inv_apply, inv_mul_cancel_left]
  abel

variable (A) in
/-- The 2nd differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G³ →₀ A) → (G² →₀ A)`. It is defined by
`a·(g₁, g₂, g₃) ↦ ρ_A(g₁⁻¹)(a)·(g₂, g₃) - a·(g₁g₂, g₃) + a·(g₁, g₂g₃) - a·(g₁, g₂)`. -/
def d₃₂ : ModuleCat.of k (G × G × G →₀ A) ⟶ ModuleCat.of k (G × G →₀ A) :=
  ModuleCat.ofHom <| lsum k fun g =>
    lsingle (g.2.1, g.2.2) ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2.1, g.2.2) +
    lsingle (g.1, g.2.1 * g.2.2) - lsingle (g.1, g.2.1)

@[simp]
lemma d₃₂_single (g : G × G × G) (a : A) :
    d₃₂ A (single g a) = single (g.2.1, g.2.2) (A.ρ g.1⁻¹ a) - single (g.1 * g.2.1, g.2.2) a +
      single (g.1, g.2.1 * g.2.2) a - single (g.1, g.2.1) a := by
  simp [d₃₂]

lemma d₃₂_single_one_fst (g h : G) (a : A) :
    d₃₂ A (single (1, g, h) a) = single (1, g * h) a - single (1, g) a := by
  simp [d₃₂]

lemma d₃₂_single_one_snd (g h : G) (a : A) :
    d₃₂ A (single (g, 1, h) a) = single (1, h) (A.ρ g⁻¹ a) - single (g, 1) a := by
  simp [d₃₂]

lemma d₃₂_single_one_thd (g h : G) (a : A) :
    d₃₂ A (single (g, h, 1) a) = single (h, 1) (A.ρ g⁻¹ a) - single (g * h, 1) a := by
  simp [d₃₂]

variable (A) [DecidableEq G]

/-- Let `C(G, A)` denote the complex of inhomogeneous chains of `A : Rep k G`. This lemma
says `d₁₀` gives a simpler expression for the 0th differential: that is, the following
square commutes:
```
  C₁(G, A) --d 1 0--> C₀(G, A)
    |                   |
    |                   |
    |                   |
    v                   v
  (G →₀ A) ----d₁₀----> A
```
where the vertical arrows are `chainsIso₁` and `chainsIso₀` respectively.
-/
theorem comp_d₁₀_eq :
    (chainsIso₁ A).hom ≫ d₁₀ A = (inhomogeneousChains A).d 1 0 ≫ (chainsIso₀ A).hom :=
  ModuleCat.hom_ext <| lhom_ext fun _ _ => by
    simp [inhomogeneousChains.d_def, chainsIso₀, chainsIso₁, d₁₀_single (G := G),
      Unique.eq_default (α := Fin 0 → G), sub_eq_add_neg, inhomogeneousChains.d_single (G := G)]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem eq_d₁₀_comp_inv :
    (chainsIso₁ A).inv ≫ (inhomogeneousChains A).d 1 0 = d₁₀ A ≫ (chainsIso₀ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₁₀_eq A⟩).w

/-- Let `C(G, A)` denote the complex of inhomogeneous chains of `A : Rep k G`. This lemma
says `d₂₁` gives a simpler expression for the 1st differential: that is, the following
square commutes:
```
  C₂(G, A) --d 2 1--> C₁(G, A)
    |                    |
    |                    |
    |                    |
    v                    v
  (G² →₀ A) --d₂₁--> (G →₀ A)
```
where the vertical arrows are `chainsIso₂` and `chainsIso₁` respectively.
-/

theorem comp_d₂₁_eq :
    (chainsIso₂ A).hom ≫ d₂₁ A = (inhomogeneousChains A).d 2 1 ≫ (chainsIso₁ A).hom :=
  ModuleCat.hom_ext <| lhom_ext fun _ _ => by
    simp [inhomogeneousChains.d_def, chainsIso₁, add_assoc, chainsIso₂, d₂₁_single (G := G),
      -Finsupp.domLCongr_apply, domLCongr_single, sub_eq_add_neg, Fin.contractNth,
      inhomogeneousChains.d_single (G := G)]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem eq_d₂₁_comp_inv :
    (chainsIso₂ A).inv ≫ (inhomogeneousChains A).d 2 1 = d₂₁ A ≫ (chainsIso₁ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₂₁_eq A⟩).w

/-- Let `C(G, A)` denote the complex of inhomogeneous chains of `A : Rep k G`. This lemma
says `d₃₂` gives a simpler expression for the 2nd differential: that is, the following
square commutes:
```
   C₃(G, A) --d 3 2--> C₂(G, A)
    |                    |
    |                    |
    |                    |
    v                    v
  (G³ →₀ A) --d₃₂--> (G² →₀ A)
```
where the vertical arrows are `chainsIso₃` and `chainsIso₂` respectively.
-/
theorem comp_d₃₂_eq :
    (chainsIso₃ A).hom ≫ d₃₂ A = (inhomogeneousChains A).d 3 2 ≫ (chainsIso₂ A).hom :=
  ModuleCat.hom_ext <| lhom_ext fun _ _ => by
    simp [inhomogeneousChains.d_def, chainsIso₂, pow_succ, chainsIso₃,
      -domLCongr_apply, domLCongr_single, d₃₂, Fin.sum_univ_three,
      Fin.contractNth, Fin.tail_def, sub_eq_add_neg, add_assoc,
      inhomogeneousChains.d_single (G := G), add_rotate' (-(single (_ * _, _) _)),
      add_left_comm (single (_, _ * _) _)]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem eq_d₃₂_comp_inv :
    (chainsIso₃ A).inv ≫ (inhomogeneousChains A).d 3 2 = d₃₂ A ≫ (chainsIso₂ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₃₂_eq A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem d₂₁_comp_d₁₀ : d₂₁ A ≫ d₁₀ A = 0 := by
  ext x g
  simp [d₁₀, d₂₁, sum_add_index, sum_sub_index, sub_sub_sub_comm, add_sub_add_comm]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem d₃₂_comp_d₂₁ : d₃₂ A ≫ d₂₁ A = 0 := by
  simp [← cancel_mono (chainsIso₁ A).inv, ← eq_d₂₁_comp_inv, ← eq_d₃₂_comp_inv_assoc]

open ShortComplex

/-- The (exact) short complex `(G →₀ A) ⟶ A ⟶ A.ρ.coinvariants`. -/
@[simps! -isSimp f g]
def shortComplexH0 : ShortComplex (ModuleCat k) :=
  mk _ _ (d₁₀_comp_coinvariantsMk A)

/-- The short complex `(G² →₀ A) --d₂₁--> (G →₀ A) --d₁₀--> A`. -/
@[simps! -isSimp f g]
def shortComplexH1 : ShortComplex (ModuleCat k) :=
  mk _ _ (d₂₁_comp_d₁₀ A)

/-- The short complex `(G³ →₀ A) --d₃₂--> (G² →₀ A) --d₂₁--> (G →₀ A)`. -/
@[simps! -isSimp f g]
def shortComplexH2 : ShortComplex (ModuleCat k) :=
  mk _ _ (d₃₂_comp_d₂₁ A)

end Differentials

section Cycles

/-- The 1-cycles `Z₁(G, A)` of `A : Rep k G`, defined as the kernel of the map
`(G →₀ A) → A` defined by `single g a ↦ ρ_A(g⁻¹)(a) - a`. -/
def cycles₁ : Submodule k (G →₀ A) := LinearMap.ker (d₁₀ A).hom

/-- The 2-cycles `Z₂(G, A)` of `A : Rep k G`, defined as the kernel of the map
`(G² →₀ A) → (G →₀ A)` defined by `a·(g₁, g₂) ↦ ρ_A(g₁⁻¹)(a)·g₂ - a·g₁g₂ + a·g₁`. -/
def cycles₂ : Submodule k (G × G →₀ A) := LinearMap.ker (d₂₁ A).hom

variable {A}

theorem mem_cycles₁_iff (x : G →₀ A) :
    x ∈ cycles₁ A ↔ x.sum (fun g a => A.ρ g⁻¹ a) = x.sum (fun _ a => a) := by
  change x.sum (fun g a => A.ρ g⁻¹ a - a) = 0 ↔ _
  rw [sum_sub, sub_eq_zero]

theorem single_mem_cycles₁_iff (g : G) (a : A) :
    single g a ∈ cycles₁ A ↔ A.ρ g a = a := by
  simp [mem_cycles₁_iff, ← (A.ρ.apply_bijective g).1.eq_iff (a := A.ρ g⁻¹ a), eq_comm]

theorem single_mem_cycles₁_of_mem_invariants (g : G) (a : A) (ha : a ∈ A.ρ.invariants) :
    single g a ∈ cycles₁ A :=
  (single_mem_cycles₁_iff g a).2 (ha g)

theorem d₂₁_apply_mem_cycles₁ [DecidableEq G] (x : G × G →₀ A) :
    d₂₁ A x ∈ cycles₁ A :=
  congr($(d₂₁_comp_d₁₀ A) x)

variable (A) in
theorem cycles₁_eq_top_of_isTrivial [A.IsTrivial] : cycles₁ A = ⊤ := by
  rw [cycles₁, d₁₀_eq_zero_of_isTrivial, ModuleCat.hom_zero, LinearMap.ker_zero]

variable (A) in
/-- The natural inclusion `Z₁(G, A) ⟶ C₁(G, A)` is an isomorphism when the representation
on `A` is trivial. -/
abbrev cycles₁IsoOfIsTrivial [A.IsTrivial] :
    ModuleCat.of k (cycles₁ A) ≅ ModuleCat.of k (G →₀ A) :=
  (LinearEquiv.ofTop _ (cycles₁_eq_top_of_isTrivial A)).toModuleIso

theorem mem_cycles₂_iff (x : G × G →₀ A) :
    x ∈ cycles₂ A ↔ x.sum (fun g a => single g.2 (A.ρ g.1⁻¹ a) + single g.1 a) =
      x.sum (fun g a => single (g.1 * g.2) a) := by
  change x.sum (fun g a => _) = 0 ↔ _
  simp [sub_add_eq_add_sub, sub_eq_zero]

theorem single_mem_cycles₂_iff_inv (g : G × G) (a : A) :
    single g a ∈ cycles₂ A ↔ single g.2 (A.ρ g.1⁻¹ a) + single g.1 a = single (g.1 * g.2) a := by
  simp [mem_cycles₂_iff]

theorem single_mem_cycles₂_iff (g : G × G) (a : A) :
    single g a ∈ cycles₂ A ↔
      single (g.1 * g.2) (A.ρ g.1 a) = single g.2 a + single g.1 (A.ρ g.1 a) := by
  rw [← (mapRange_injective (α := G) _ (map_zero _) (A.ρ.apply_bijective g.1⁻¹).1).eq_iff]
  simp [mem_cycles₂_iff, mapRange_add, eq_comm]

theorem d₃₂_apply_mem_cycles₂ [DecidableEq G] (x : G × G × G →₀ A) :
    d₃₂ A x ∈ cycles₂ A :=
  congr($(d₃₂_comp_d₂₁ A) x)

end Cycles

section Boundaries

/-- The 1-boundaries `B₁(G, A)` of `A : Rep k G`, defined as the image of the map
`(G² →₀ A) → (G →₀ A)` defined by `a·(g₁, g₂) ↦ ρ_A(g₁⁻¹)(a)·g₂ - a·g₁g₂ + a·g₁`. -/
def boundaries₁ : Submodule k (G →₀ A) :=
  LinearMap.range (d₂₁ A).hom

/-- The 2-boundaries `B₂(G, A)` of `A : Rep k G`, defined as the image of the map
`(G³ →₀ A) → (G² →₀ A)` defined by
`a·(g₁, g₂, g₃) ↦ ρ_A(g₁⁻¹)(a)·(g₂, g₃) - a·(g₁g₂, g₃) + a·(g₁, g₂g₃) - a·(g₁, g₂)`. -/
def boundaries₂ : Submodule k (G × G →₀ A) :=
  LinearMap.range (d₃₂ A).hom

variable {A}

section

variable [DecidableEq G]

lemma mem_cycles₁_of_mem_boundaries₁ (f : G →₀ A) (h : f ∈ boundaries₁ A) :
    f ∈ cycles₁ A := by
  rcases h with ⟨x, rfl⟩
  exact d₂₁_apply_mem_cycles₁ x

variable (A) in
lemma boundaries₁_le_cycles₁ : boundaries₁ A ≤ cycles₁ A :=
  mem_cycles₁_of_mem_boundaries₁

variable (A) in
/-- The natural inclusion `B₁(G, A) →ₗ[k] Z₁(G, A)`. -/
abbrev boundariesToCycles₁ : boundaries₁ A →ₗ[k] cycles₁ A :=
  Submodule.inclusion (boundaries₁_le_cycles₁ A)

@[simp]
lemma boundariesToCycles₁_apply (x : boundaries₁ A) :
    (boundariesToCycles₁ A x).1 = x.1 := rfl

end

theorem single_one_mem_boundaries₁ (a : A) :
    single 1 a ∈ boundaries₁ A := by
  use single (1, 1) a
  simp [d₂₁]

theorem single_ρ_self_add_single_inv_mem_boundaries₁ (g : G) (a : A) :
    single g (A.ρ g a) + single g⁻¹ a ∈ boundaries₁ A := by
  rw [← d₂₁_single_ρ_add_single_inv_mul g 1]
  exact Set.mem_range_self _

theorem single_inv_ρ_self_add_single_mem_boundaries₁ (g : G) (a : A) :
    single g⁻¹ (A.ρ g⁻¹ a) + single g a ∈ boundaries₁ A := by
  rw [← d₂₁_single_inv_mul_ρ_add_single g 1]
  exact Set.mem_range_self _

section

variable [DecidableEq G]

lemma mem_cycles₂_of_mem_boundaries₂ (x : G × G →₀ A) (h : x ∈ boundaries₂ A) :
    x ∈ cycles₂ A := by
  rcases h with ⟨x, rfl⟩
  exact d₃₂_apply_mem_cycles₂ x

variable (A) in
lemma boundaries₂_le_cycles₂ : boundaries₂ A ≤ cycles₂ A :=
  mem_cycles₂_of_mem_boundaries₂

variable (A) in
/-- The natural inclusion `B₂(G, A) →ₗ[k] Z₂(G, A)`. -/
abbrev boundariesToCycles₂ [DecidableEq G] : boundaries₂ A →ₗ[k] cycles₂ A :=
  Submodule.inclusion (boundaries₂_le_cycles₂ A)

@[simp]
lemma boundariesToCycles₂_apply (x : boundaries₂ A) :
    (boundariesToCycles₂ A x).1 = x.1 := rfl

end

lemma single_one_fst_sub_single_one_fst_mem_boundaries₂ (g h : G) (a : A) :
    single (1, g * h) a - single (1, g) a ∈ boundaries₂ A := by
  use single (1, g, h) a
  simp [d₃₂]

lemma single_one_fst_sub_single_one_snd_mem_boundaries₂ (g h : G) (a : A) :
    single (1, h) (A.ρ g⁻¹ a) - single (g, 1) a ∈ boundaries₂ A := by
  use single (g, 1, h) a
  simp [d₃₂]

lemma single_one_snd_sub_single_one_fst_mem_boundaries₂ (g h : G) (a : A) :
    single (g, 1) (A.ρ g a) - single (1, h) a ∈ boundaries₂ A := by
  use single (g, 1, h) (A.ρ g (-a))
  simp [d₃₂_single (G := G)]

lemma single_one_snd_sub_single_one_snd_mem_boundaries₂ (g h : G) (a : A) :
    single (h, 1) (A.ρ g⁻¹ a) - single (g * h, 1) a ∈ boundaries₂ A := by
  use single (g, h, 1) a
  simp [d₃₂]

end Boundaries

section IsCycle

section

variable {G A : Type*} [Mul G] [Inv G] [AddCommGroup A] [SMul G A]

/-- A finsupp `∑ aᵢ·gᵢ : G →₀ A` satisfies the 1-cycle condition if `∑ gᵢ⁻¹ • aᵢ = ∑ aᵢ`. -/
def IsCycle₁ (x : G →₀ A) : Prop := x.sum (fun g a => g⁻¹ • a) = x.sum (fun _ a => a)

/-- A finsupp `∑ aᵢ·(gᵢ, hᵢ) : G × G →₀ A` satisfies the 2-cycle condition if
`∑ (gᵢ⁻¹ • aᵢ)·hᵢ + aᵢ·gᵢ = ∑ aᵢ·gᵢhᵢ`. -/
def IsCycle₂ (x : G × G →₀ A) : Prop :=
  x.sum (fun g a => single g.2 (g.1⁻¹ • a) + single g.1 a) =
    x.sum (fun g a => single (g.1 * g.2) a)

end

section

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

@[simp]
theorem single_isCycle₁_iff (g : G) (a : A) :
    IsCycle₁ (single g a) ↔ g • a = a := by
  rw [← (MulAction.bijective g⁻¹).1.eq_iff]
  simp [IsCycle₁, eq_comm]

theorem single_isCycle₁_of_mem_fixedPoints
    (g : G) (a : A) (ha : a ∈ MulAction.fixedPoints G A) :
    IsCycle₁ (single g a) := by
  simp_all [IsCycle₁]

theorem single_isCycle₂_iff_inv (g : G × G) (a : A) :
    IsCycle₂ (single g a) ↔
      single g.2 (g.1⁻¹ • a) + single g.1 a = single (g.1 * g.2) a := by
  simp [IsCycle₂]

@[simp]
theorem single_isCycle₂_iff (g : G × G) (a : A) :
    IsCycle₂ (single g a) ↔
      single g.2 a + single g.1 (g.1 • a) = single (g.1 * g.2) (g.1 • a) := by
  rw [← (Finsupp.mapRange_injective (α := G) _ (smul_zero _) (MulAction.bijective g.1⁻¹).1).eq_iff]
  simp [mapRange_add, IsCycle₂]

end

end IsCycle

section IsBoundary

section

variable {G A : Type*} [Mul G] [Inv G] [AddCommGroup A] [SMul G A]

variable (G) in
/-- A term `x : A` satisfies the 0-boundary condition if there exists a finsupp
`∑ aᵢ·gᵢ : G →₀ A` such that `∑ gᵢ⁻¹ • aᵢ - aᵢ = x`. -/
def IsBoundary₀ (a : A) : Prop :=
  ∃ (x : G →₀ A), x.sum (fun g z => g⁻¹ • z - z) = a

/-- A finsupp `x : G →₀ A` satisfies the 1-boundary condition if there's a finsupp
`∑ aᵢ·(gᵢ, hᵢ) : G × G →₀ A` such that `∑ (gᵢ⁻¹ • aᵢ)·hᵢ - aᵢ·gᵢhᵢ + aᵢ·gᵢ = x`. -/
def IsBoundary₁ (x : G →₀ A) : Prop :=
  ∃ y : G × G →₀ A, y.sum
    (fun g a => single g.2 (g.1⁻¹ • a) - single (g.1 * g.2) a + single g.1 a) = x

/-- A finsupp `x : G × G →₀ A` satsfies the 2-boundary condition if there's a finsupp
`∑ aᵢ·(gᵢ, hᵢ, jᵢ) : G × G × G →₀ A` such that
`∑ (gᵢ⁻¹ • aᵢ)·(hᵢ, jᵢ) - aᵢ·(gᵢhᵢ, jᵢ) + aᵢ·(gᵢ, hᵢjᵢ) - aᵢ·(gᵢ, hᵢ) = x.` -/
def IsBoundary₂ (x : G × G →₀ A) : Prop :=
  ∃ y : G × G × G →₀ A, y.sum (fun g a => single (g.2.1, g.2.2) (g.1⁻¹ • a) -
    single (g.1 * g.2.1, g.2.2) a + single (g.1, g.2.1 * g.2.2) a - single (g.1, g.2.1) a) = x

end
section

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

variable (G) in
theorem isBoundary₀_iff (a : A) :
    IsBoundary₀ G a ↔ ∃ x : G →₀ A, x.sum (fun g z => g • z - z) = a := by
  constructor
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (- (g⁻¹ • a)))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (- (g • a)))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]

theorem isBoundary₁_iff (x : G →₀ A) :
    IsBoundary₁ x ↔ ∃ y : G × G →₀ A, y.sum
      (fun g a => single g.2 a - single (g.1 * g.2) (g.1 • a) + single g.1 (g.1 • a)) = x := by
  constructor
  · rintro ⟨y, hy⟩
    use y.sum (fun g a => single g (g.1⁻¹ • a))
    simp_all [sum_sum_index]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (g.1 • a))
    simp_all [sum_sum_index]

theorem isBoundary₂_iff (x : G × G →₀ A) :
    IsBoundary₂ x ↔ ∃ y : G × G × G →₀ A, y.sum
      (fun g a => single (g.2.1, g.2.2) a - single (g.1 * g.2.1, g.2.2) (g.1 • a) +
        single (g.1, g.2.1 * g.2.2) (g.1 • a) - single (g.1, g.2.1) (g.1 • a)) = x := by
  constructor
  · rintro ⟨y, hy⟩
    use y.sum (fun g a => single g (g.1⁻¹ • a))
    simp_all [sum_sum_index]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (g.1 • a))
    simp_all [sum_sum_index]

end
end IsBoundary

section ofDistribMulAction

variable {k G A : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a term
`x : A` satisfying the 0-boundary condition, this produces an element of the kernel of the quotient
map `A → A_G` for the representation on `A` induced by the `DistribMulAction`. -/
@[simps]
def coinvariantsKerOfIsBoundary₀ (x : A) (hx : IsBoundary₀ G x) :
    Coinvariants.ker (Representation.ofDistribMulAction k G A) :=
  ⟨x, by
    rcases (isBoundary₀_iff G x).1 hx with ⟨y, rfl⟩
    exact Submodule.finsuppSum_mem _ _ _ _ fun g _ => Coinvariants.mem_ker_of_eq g (y g) _ rfl⟩

theorem isBoundary₀_of_mem_coinvariantsKer [DecidableEq G]
    (x : A) (hx : x ∈ Coinvariants.ker (Representation.ofDistribMulAction k G A)) :
    IsBoundary₀ G x :=
  Submodule.span_induction (fun _ ⟨g, hg⟩ => ⟨single g.1⁻¹ g.2, by simp_all⟩) ⟨0, by simp⟩
    (fun _ _ _ _ ⟨X, hX⟩ ⟨Y, hY⟩ => ⟨X + Y, by simp_all [sum_add_index, add_sub_add_comm]⟩)
    (fun r _ _ ⟨X, hX⟩ => ⟨r • X, by simp [← hX, sum_smul_index', smul_comm, smul_sub, smul_sum]⟩)
    hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G →₀ A` satisfying the 1-cycle condition, produces a 1-cycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
def cyclesOfIsCycle₁ (x : G →₀ A) (hx : IsCycle₁ x) :
    cycles₁ (Rep.ofDistribMulAction k G A) :=
  ⟨x, (mem_cycles₁_iff (A := Rep.ofDistribMulAction k G A) x).2 hx⟩

theorem isCycle₁_of_mem_cycles₁
    (x : G →₀ A) (hx : x ∈ cycles₁ (Rep.ofDistribMulAction k G A)) :
    IsCycle₁ x := by
  simpa using (mem_cycles₁_iff (A := Rep.ofDistribMulAction k G A) x).1 hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G →₀ A` satisfying the 1-boundary condition, produces a 1-boundary for the representation
on `A` induced by the `DistribMulAction`. -/
@[simps]
def boundariesOfIsBoundary₁ (x : G →₀ A) (hx : IsBoundary₁ x) :
    boundaries₁ (Rep.ofDistribMulAction k G A) :=
  ⟨x, hx⟩

theorem isBoundary₁_of_mem_boundaries₁
    (x : G →₀ A) (hx : x ∈ boundaries₁ (Rep.ofDistribMulAction k G A)) :
    IsBoundary₁ x := hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G × G →₀ A` satisfying the 2-cycle condition, produces a 2-cycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
def cyclesOfIsCycle₂ (x : G × G →₀ A) (hx : IsCycle₂ x) :
    cycles₂ (Rep.ofDistribMulAction k G A) :=
  ⟨x, (mem_cycles₂_iff (A := Rep.ofDistribMulAction k G A) x).2 hx⟩

theorem isCycle₂_of_mem_cycles₂
    (x : G × G →₀ A) (hx : x ∈ cycles₂ (Rep.ofDistribMulAction k G A)) :
    IsCycle₂ x := (mem_cycles₂_iff (A := Rep.ofDistribMulAction k G A) x).1 hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G × G →₀ A` satisfying the 2-boundary condition, produces a 2-boundary for the
representation on `A` induced by the `DistribMulAction`. -/
@[simps]
def boundariesOfIsBoundary₂ (x : G × G →₀ A) (hx : IsBoundary₂ x) :
    boundaries₂ (Rep.ofDistribMulAction k G A) :=
  ⟨x, hx⟩

theorem isBoundary₂_of_mem_boundaries₂
    (x : G × G →₀ A) (hx : x ∈ boundaries₂ (Rep.ofDistribMulAction k G A)) :
    IsBoundary₂ x := hx

end ofDistribMulAction

open ShortComplex

section cyclesIso₀

instance : Epi (shortComplexH0 A).g := inferInstanceAs <| Epi ((coinvariantsMk k G).app A)

lemma shortComplexH0_exact : (shortComplexH0 A).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x (hx : Coinvariants.mk _ _ = 0)
  rw [Coinvariants.mk_eq_zero, ← range_d₁₀_eq_coinvariantsKer] at hx
  rcases hx with ⟨x, hx, rfl⟩
  use x
  rfl

variable [DecidableEq G]

/-- The 0-cycles of the complex of inhomogeneous chains of `A` are isomorphic to `A`. -/
def cyclesIso₀ : cycles A 0 ≅ A.V :=
  (inhomogeneousChains A).iCyclesIso _ 0 (by aesop) (by aesop) ≪≫ chainsIso₀ A

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cyclesIso₀_inv_comp_iCycles :
    (cyclesIso₀ A).inv ≫ iCycles A 0 = (chainsIso₀ A).inv := by
  simp [cyclesIso₀]

/-- The arrow `(G →₀ A) --d₁₀--> A` is isomorphic to the differential
`(inhomogeneousChains A).d 1 0` of the complex of inhomogeneous chains of `A`. -/
@[simps! hom_left hom_right inv_left inv_right]
def d₁₀ArrowIso :
    Arrow.mk ((inhomogeneousChains A).d 1 0) ≅ Arrow.mk (d₁₀ A) :=
  Arrow.isoMk (chainsIso₁ A) (chainsIso₀ A) (comp_d₁₀_eq A)

/-- The 0-cycles of the complex of inhomogeneous chains of `A` are isomorphic to
`A.ρ.coinvariants`, which is a simpler type. -/
def opcyclesIso₀ : (inhomogeneousChains A).opcycles 0 ≅ (coinvariantsFunctor k G).obj A :=
  CokernelCofork.mapIsoOfIsColimit
    ((inhomogeneousChains A).opcyclesIsCokernel 1 0 (by simp)) (shortComplexH0_exact A).gIsCokernel
      (d₁₀ArrowIso A)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma pOpcycles_comp_opcyclesIso_hom :
    (inhomogeneousChains A).pOpcycles 0 ≫ (opcyclesIso₀ A).hom =
      (chainsIso₀ A).hom ≫ (coinvariantsMk k G).app A :=
  CokernelCofork.π_mapOfIsColimit (φ := (d₁₀ArrowIso A).hom) _ _

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma coinvariantsMk_comp_opcyclesIso₀_inv :
    (coinvariantsMk k G).app A ≫ (opcyclesIso₀ A).inv =
      (chainsIso₀ A).inv ≫ (inhomogeneousChains A).pOpcycles 0 :=
  (CommSq.vert_inv ⟨pOpcycles_comp_opcyclesIso_hom A⟩).w

end cyclesIso₀

section isoCycles₁

variable [DecidableEq G]

/-- The short complex `(G² →₀ A) --d₂₁--> (G →₀ A) --d₁₀--> A` is isomorphic to the 1st
short complex associated to the complex of inhomogeneous chains of `A`. -/
@[simps! hom inv]
def isoShortComplexH1 : (inhomogeneousChains A).sc 1 ≅ shortComplexH1 A :=
  (inhomogeneousChains A).isoSc' 2 1 0 (by simp) (by simp) ≪≫
    isoMk (chainsIso₂ A) (chainsIso₁ A) (chainsIso₀ A) (comp_d₂₁_eq A) (comp_d₁₀_eq A)

/-- The 1-cycles of the complex of inhomogeneous chains of `A` are isomorphic to
`cycles₁ A`, which is a simpler type. -/
def isoCycles₁ : cycles A 1 ≅ ModuleCat.of k (cycles₁ A) :=
    cyclesMapIso' (isoShortComplexH1 A) ((inhomogeneousChains A).sc 1).leftHomologyData
      (shortComplexH1 A).moduleCatLeftHomologyData

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoCycles₁_hom_comp_i :
    (isoCycles₁ A).hom ≫ (shortComplexH1 A).moduleCatLeftHomologyData.i =
      iCycles A 1 ≫ (chainsIso₁ A).hom := by
  simp [isoCycles₁, iCycles, HomologicalComplex.iCycles, ShortComplex.iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoCycles₁_inv_comp_iCycles :
    (isoCycles₁ A).inv ≫ iCycles A 1 =
      (shortComplexH1 A).moduleCatLeftHomologyData.i ≫ (chainsIso₁ A).inv :=
  (CommSq.horiz_inv ⟨isoCycles₁_hom_comp_i A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toCycles_comp_isoCycles₁_hom :
    toCycles A 2 1 ≫ (isoCycles₁ A).hom =
      (chainsIso₂ A).hom ≫ (shortComplexH1 A).moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono (shortComplexH1 A).moduleCatLeftHomologyData.i, comp_d₂₁_eq,
    shortComplexH1_f]

end isoCycles₁

section isoCycles₂

variable [DecidableEq G]

/-- The short complex `(G³ →₀ A) --d₃₂--> (G² →₀ A) --d₂₁--> (G →₀ A)` is isomorphic to the 2nd
short complex associated to the complex of inhomogeneous chains of `A`. -/
@[simps! hom inv]
def isoShortComplexH2 : (inhomogeneousChains A).sc 2 ≅ shortComplexH2 A :=
  (inhomogeneousChains A).isoSc' 3 2 1 (by simp) (by simp) ≪≫
    isoMk (chainsIso₃ A) (chainsIso₂ A) (chainsIso₁ A) (comp_d₃₂_eq A) (comp_d₂₁_eq A)

/-- The 2-cycles of the complex of inhomogeneous chains of `A` are isomorphic to
`cycles₂ A`, which is a simpler type. -/
def isoCycles₂ : cycles A 2 ≅ ModuleCat.of k (cycles₂ A) :=
    cyclesMapIso' (isoShortComplexH2 A) ((inhomogeneousChains A).sc 2).leftHomologyData
      (shortComplexH2 A).moduleCatLeftHomologyData

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoCycles₂_hom_comp_i :
    (isoCycles₂ A).hom ≫ (shortComplexH2 A).moduleCatLeftHomologyData.i =
      iCycles A 2 ≫ (chainsIso₂ A).hom := by
  simp [isoCycles₂, iCycles, HomologicalComplex.iCycles, ShortComplex.iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoCycles₂_inv_comp_iCycles :
    (isoCycles₂ A).inv ≫ iCycles A 2 =
      (shortComplexH2 A).moduleCatLeftHomologyData.i ≫ (chainsIso₂ A).inv :=
  (CommSq.horiz_inv ⟨isoCycles₂_hom_comp_i A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toCycles_comp_isoCycles₂_hom :
    toCycles A 3 2 ≫ (isoCycles₂ A).hom =
      (chainsIso₃ A).hom ≫ (shortComplexH2 A).moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono (shortComplexH2 A).moduleCatLeftHomologyData.i, comp_d₃₂_eq,
    shortComplexH2_f]

end isoCycles₂
end groupHomology
