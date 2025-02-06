/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
# The low-degree homology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file will give simple expressions for
the group homology of a `k`-linear `G`-representation `A` in degrees 0, 1 and 2.
In `RepresentationTheory.Homological.GroupHomology.Basic`, we define the `n`th group homology of
`A` to be the homology of a complex `inhomogeneousChains A`, whose objects are `(Fin n →₀ G) → A`;
this is unnecessarily unwieldy in low degree. Moreover, homology of a complex is defined as an
abstract cokernel, whereas the definitions here will be explicit quotients of cycles by boundaries.

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
def zeroChainsLequiv : (inhomogeneousChains A).X 0 ≃ₗ[k] A :=
  LinearEquiv.finsuppUnique _ _ _

/-- The 1st object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `G →₀ A` as a `k`-module. -/
def oneChainsLequiv : (inhomogeneousChains A).X 1 ≃ₗ[k] G →₀ A :=
  Finsupp.domLCongr (Equiv.funUnique (Fin 1) G)

/-- The 2nd object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `G² →₀ A` as a `k`-module. -/
def twoChainsLequiv : (inhomogeneousChains A).X 2 ≃ₗ[k] G × G →₀ A :=
  Finsupp.domLCongr (piFinTwoEquiv fun _ => G)

/-- The 3rd object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `G³ → A` as a `k`-module. -/
def threeChainsLequiv : (inhomogeneousChains A).X 3 ≃ₗ[k] G × G × G →₀ A :=
  Finsupp.domLCongr ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))

end Chains

section Differentials

/-- The 0th differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G →₀ A) → A`. It sends `single g a ↦ ρ_A(g⁻¹)(a) - a.` -/
def dZero : (G →₀ A) →ₗ[k] A := lsum k fun g => A.ρ g⁻¹ - LinearMap.id

@[simp]
theorem dZero_single (g : G) (a : A) : dZero A (single g a) = A.ρ g⁻¹ a - a := by
  simp [dZero]

theorem dZero_single_one (a : A) : dZero A (single 1 a) = 0 := by
  simp

theorem dZero_single_inv (g : G) (a : A) :
    dZero A (single g⁻¹ a) = - dZero A (single g (A.ρ g a)) := by
  simp

theorem range_dZero_eq_augmentationSubmodule :
    LinearMap.range (dZero A) = augmentationSubmodule A.ρ := by
  symm
  apply Submodule.span_eq_of_le
  · rintro _ ⟨x, rfl⟩
    use single x.1⁻¹ x.2
    simp
  · rintro x ⟨y, hy⟩
    induction' y using Finsupp.induction with _ _ _ _ _ h generalizing x
    · simp [← hy]
    · simpa [← hy, add_sub_add_comm, sum_add_index]
        using Submodule.add_mem _ (mem_augmentationSubmodule_of_eq _ _ _ rfl) (h rfl)

lemma mkQ_comp_dZero : (augmentationSubmodule A.ρ).mkQ ∘ₗ dZero A = 0 := by
  rw [← range_dZero_eq_augmentationSubmodule]
  exact LinearMap.range_mkQ_comp _

/-- The 0th differential in the complex of inhomogeneous chains of a `G`-representation `A` as a
linear map into the `k`-submodule of `A` spanned by elements of the form
`ρ(g)(x) - x, g ∈ G, x ∈ A`.-/
def oneChainsToAugmentationSubmodule :
    (G →₀ A) →ₗ[k] augmentationSubmodule A.ρ :=
  (dZero A).codRestrict _ <| range_dZero_eq_augmentationSubmodule A ▸ LinearMap.mem_range_self _

@[simp]
theorem dZero_eq_zero_of_isTrivial [A.IsTrivial] : dZero A = 0 := by
  ext
  simp

/-- The 1st differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G² →₀ A) → (G →₀ A)`. It sends `a·(g₁, g₂) ↦ ρ_A(g₁⁻¹)(a)·g₂ - a·g₁g₂ + a·g₁`. -/
def dOne : (G × G →₀ A) →ₗ[k] G →₀ A :=
  lsum k fun g => lsingle g.2 ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2) + lsingle g.1

variable {A}

@[simp]
lemma dOne_single (g : G × G) (a : A) :
    dOne A (single g a) = single g.2 (A.ρ g.1⁻¹ a) - single (g.1 * g.2) a + single g.1 a := by
  simp [dOne]

lemma dOne_single_one_fst (g : G) (a : A) :
    dOne A (single (1, g) a) = single 1 a := by
  simp

lemma dOne_single_one_snd (g : G) (a : A) :
    dOne A (single (g, 1) a) = single 1 (A.ρ g⁻¹ a) := by
  simp

lemma dOne_single_inv_self_ρ_sub_self_inv (g : G) (a : A) :
    dOne A (single (g⁻¹, g) (A.ρ g⁻¹ a) - single (g, g⁻¹) a) =
      single 1 a - single 1 (A.ρ g⁻¹ a) := by
  simp only [map_sub, dOne_single, inv_inv, ρ_self_inv_apply, inv_mul_cancel, mul_inv_cancel]
  abel

lemma dOne_single_self_inv_ρ_sub_inv_self (g : G) (a : A) :
    dOne A (single (g, g⁻¹) (A.ρ g a) - single (g⁻¹, g) a) =
      single 1 a - single 1 (A.ρ g a) := by
  simp only [map_sub, dOne_single, ρ_inv_self_apply, mul_inv_cancel, inv_inv, inv_mul_cancel]
  abel

lemma dOne_single_ρ_add_single_inv_mul (g h : G) (a : A) :
    dOne A (single (g, h) (A.ρ g a) + single (g⁻¹, g * h) a) =
      single g (A.ρ g a) + single g⁻¹ a := by
  simp only [map_add, dOne_single, ρ_inv_self_apply, inv_inv, inv_mul_cancel_left]
  abel

lemma dOne_single_inv_mul_ρ_add_single (g h : G) (a : A) :
    dOne A (single (g⁻¹, g * h) (A.ρ g⁻¹ a) + single (g, h) a) =
      single g⁻¹ (A.ρ g⁻¹ a) + single g a := by
  simp only [map_add, dOne_single, inv_inv, ρ_self_inv_apply, inv_mul_cancel_left]
  abel

variable (A) in
/-- The 2nd differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G³ →₀ A) → (G² →₀ A)`. It sends
`a·(g₁, g₂, g₃) ↦ ρ_A(g₁⁻¹)(a)·(g₂, g₃) - a·(g₁g₂, g₃) + a·(g₁, g₂g₃) - a·(g₁, g₂)`. -/
def dTwo : (G × G × G →₀ A) →ₗ[k] G × G →₀ A :=
  lsum k fun g => lsingle (g.2.1, g.2.2) ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2.1, g.2.2) +
    lsingle (g.1, g.2.1 * g.2.2) - lsingle (g.1, g.2.1)

@[simp]
lemma dTwo_single (g : G × G × G) (a : A) :
    dTwo A (single g a) = single (g.2.1, g.2.2) (A.ρ g.1⁻¹ a) - single (g.1 * g.2.1, g.2.2) a +
      single (g.1, g.2.1 * g.2.2) a - single (g.1, g.2.1) a := by
  simp [dTwo]

lemma dTwo_single_one_fst (g h : G) (a : A) :
    dTwo A (single (1, g, h) a) = single (1, g * h) a - single (1, g) a := by
  simp

lemma dTwo_single_one_snd (g h : G) (a : A) :
    dTwo A (single (g, 1, h) a) = single (1, h) (A.ρ g⁻¹ a) - single (g, 1) a := by
  simp

lemma dTwo_single_one_thd (g h : G) (a : A) :
    dTwo A (single (g, h, 1) a) = single (h, 1) (A.ρ g⁻¹ a) - single (g * h, 1) a := by
  simp

section
variable (A) [DecidableEq G]

/-- Let `C(G, A)` denote the complex of inhomogeneous chains of `A : Rep k G`. This lemma
says `dZero` gives a simpler expression for the 0th differential: that is, the following
square commutes:
```
  C₁(G, A) ---d₀---> C₀(G, A)
    |                  |
    |                  |
    |                  |
    v                  v
  (G →₀ A) --dZero --> A
```
where the vertical arrows are `oneChainsLequiv` and `zeroChainsLequiv` respectively.
-/
theorem dZero_comp_eq :
    (oneChainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (dZero A) =
      (inhomogeneousChains A).d 1 0 ≫ (zeroChainsLequiv A).toModuleIso.hom :=
  ModuleCat.hom_ext <| lhom_ext fun _ _ => by
    simp [inhomogeneousChains.d_def, zeroChainsLequiv, oneChainsLequiv,
      Unique.eq_default (α := Fin 0 → G), sub_eq_add_neg]

/-- Let `C(G, A)` denote the complex of inhomogeneous chains of `A : Rep k G`. This lemma
says `dOne` gives a simpler expression for the 1st differential: that is, the following
square commutes:
```
  C₂(G, A) ---d₁-----> C₁(G, A)
    |                      |
    |                      |
    |                      |
    v                      v
  (G² →₀ A) --dOne--->  (G →₀ A)
```
where the vertical arrows are `twoChainsLequiv` and `oneChainsLequiv` respectively.
-/

theorem dOne_comp_eq :
    (twoChainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (dOne A) =
      (inhomogeneousChains A).d 2 1 ≫ (oneChainsLequiv A).toModuleIso.hom :=
  ModuleCat.hom_ext <| lhom_ext fun _ _ => by
    simp [inhomogeneousChains.d_def, oneChainsLequiv, add_assoc, twoChainsLequiv,
      -Finsupp.domLCongr_apply, domLCongr_single, sub_eq_add_neg, Fin.contractNth]

/-- Let `C(G, A)` denote the complex of inhomogeneous chains of `A : Rep k G`. This lemma
says `dTwo` gives a simpler expression for the 2nd differential: that is, the following
square commutes:
```
   C₃(G, A) -----d₂---> C₂(G, A)
    |                      |
    |                      |
    |                      |
    v                      v
  (G³ →₀ A) --dTwo--> (G² →₀ A)
```
where the vertical arrows are `threeChainsLequiv` and `twoChainsLequiv` respectively.
-/
theorem dTwo_comp_eq :
    (threeChainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (dTwo A) =
      (inhomogeneousChains A).d 3 2 ≫ (twoChainsLequiv A).toModuleIso.hom :=
  ModuleCat.hom_ext <| lhom_ext fun _ _ => by
    simp [inhomogeneousChains.d_def, twoChainsLequiv, pow_succ, threeChainsLequiv,
      -domLCongr_apply, domLCongr_single, dTwo, Fin.sum_univ_three,
      Fin.contractNth, Fin.tail_def, sub_eq_add_neg, add_assoc,
      add_rotate' (-(single (_ * _, _) _)), add_left_comm (single (_, _ * _) _)]

theorem dZero_comp_dOne : dZero A ∘ₗ dOne A = 0 := by
  ext x g
  simp [dZero, dOne, sum_add_index, sum_sub_index, sub_sub_sub_comm, add_sub_add_comm]

theorem dOne_comp_dTwo : dOne A ∘ₗ dTwo A = 0 := by
  apply_fun ModuleCat.ofHom using (fun _ _ h => ModuleCat.hom_ext_iff.1 h)
  simp [(Iso.eq_inv_comp _).2 (dOne_comp_eq A), (Iso.eq_inv_comp _).2 (dTwo_comp_eq A),
    ModuleCat.hom_ext_iff, -LinearEquiv.toModuleIso_hom, -LinearEquiv.toModuleIso_inv]

end
end Differentials

section Cycles

/-- The 1-cycles `Z₁(G, A)` of `A : Rep k G`, defined as the kernel of the map
`(G →₀ A) → A` sending `single g a ↦ ρ_A(g⁻¹)(a) - a`. -/
def oneCycles : Submodule k (G →₀ A) := LinearMap.ker (dZero A)

/-- The 2-cycles `Z₂(G, A)` of `A : Rep k G`, defined as the kernel of the map
`(G² →₀ A) → (G →₀ A)` sending `a·(g₁, g₂) ↦ ρ_A(g₁⁻¹)(a)·g₂ - a·g₁g₂ + a·g₁`. -/
def twoCycles : Submodule k (G × G →₀ A) := LinearMap.ker (dOne A)

variable {A}

theorem mem_oneCycles_iff (x : G →₀ A) :
    x ∈ oneCycles A ↔ x.sum (fun g a => A.ρ g⁻¹ a) = x.sum (fun _ a => a) := by
  show x.sum (fun g a => A.ρ g⁻¹ a - a) = 0 ↔ _
  rw [sum_sub, sub_eq_zero]

theorem single_mem_oneCycles_iff (g : G) (a : A) :
    single g a ∈ oneCycles A ↔ A.ρ g a = a := by
  simp [mem_oneCycles_iff, ← (A.ρ.ρ_apply_bijective g).1.eq_iff (a := A.ρ g⁻¹ a), eq_comm]

theorem single_mem_oneCycles_of_mem_invariants (g : G) (a : A) (ha : a ∈ A.ρ.invariants) :
    single g a ∈ oneCycles A :=
  (single_mem_oneCycles_iff g a).2 (ha g)

theorem dOne_apply_mem_oneCycles [DecidableEq G] (x : G × G →₀ A) :
    dOne A x ∈ oneCycles A :=
  congr($(dZero_comp_dOne A) x)

variable (A) in
theorem oneCycles_eq_top_of_isTrivial [A.IsTrivial] : oneCycles A = ⊤ := by
  rw [oneCycles, dZero_eq_zero_of_isTrivial, LinearMap.ker_zero]

variable (A) in
/-- The natural inclusion `Z₁(G, A) →ₗ[k] C₁(G, A)` is an isomorphism when the representation
on `A` is trivial. -/
abbrev oneCyclesLequivOfIsTrivial [A.IsTrivial] :
    oneCycles A ≃ₗ[k] (G →₀ A) :=
  LinearEquiv.ofTop _ (oneCycles_eq_top_of_isTrivial A)

theorem mem_twoCycles_iff (x : G × G →₀ A) :
    x ∈ twoCycles A ↔ x.sum (fun g a => single g.2 (A.ρ g.1⁻¹ a) + single g.1 a) =
      x.sum (fun g a => single (g.1 * g.2) a) := by
  show x.sum (fun g a => _) = 0 ↔ _
  simp [sub_add_eq_add_sub, sum_sub_index, sub_eq_zero]

theorem single_mem_twoCycles_iff_inv (g : G × G) (a : A) :
    single g a ∈ twoCycles A ↔ single g.2 (A.ρ g.1⁻¹ a) + single g.1 a = single (g.1 * g.2) a := by
  simp [mem_twoCycles_iff]

theorem single_mem_twoCycles_iff (g : G × G) (a : A) :
    single g a ∈ twoCycles A ↔
      single (g.1 * g.2) (A.ρ g.1 a) = single g.2 a + single g.1 (A.ρ g.1 a) := by
  rw [← (mapRange_injective (α := G) _ (map_zero _) (A.ρ.ρ_apply_bijective g.1⁻¹).1).eq_iff]
  simp [mem_twoCycles_iff, mapRange_add, eq_comm]

theorem dTwo_apply_mem_twoCycles [DecidableEq G] (x : G × G × G →₀ A) :
    dTwo A x ∈ twoCycles A :=
  congr($(dOne_comp_dTwo A) x)

end Cycles

section Boundaries

/-- The 1-boundaries `B₁(G, A)` of `A : Rep k G`, defined as the image of the map
`(G² →₀ A) → (G →₀ A)` sending `a·(g₁, g₂) ↦ ρ_A(g₁⁻¹)(a)·g₂ - a·g₁g₂ + a·g₁`. -/
def oneBoundaries : Submodule k (G →₀ A) :=
  LinearMap.range (dOne A)

/-- The 2-boundaries `B₂(G, A)` of `A : Rep k G`, defined as the image of the map
`(G³ →₀ A) → (G² →₀ A)` sending
`a·(g₁, g₂, g₃) ↦ ρ_A(g₁⁻¹)(a)·(g₂, g₃) - a·(g₁g₂, g₃) + a·(g₁, g₂g₃) - a·(g₁, g₂)`. -/
def twoBoundaries : Submodule k (G × G →₀ A) :=
  LinearMap.range (dTwo A)

variable {A}

section

variable [DecidableEq G]

lemma mem_oneCycles_of_mem_oneBoundaries (f : G →₀ A) (h : f ∈ oneBoundaries A) :
    f ∈ oneCycles A := by
  rcases h with ⟨x, rfl⟩
  exact dOne_apply_mem_oneCycles x

variable (A) in
lemma oneBoundaries_le_oneCycles : oneBoundaries A ≤ oneCycles A :=
  mem_oneCycles_of_mem_oneBoundaries

variable (A) in
/-- Natural inclusion `B₁(G, A) →ₗ[k] Z₁(G, A)`. -/
abbrev oneBoundariesToOneCycles : oneBoundaries A →ₗ[k] oneCycles A :=
  Submodule.inclusion (oneBoundaries_le_oneCycles A)

@[simp]
lemma oneBoundariesToOneCycles_apply (x : oneBoundaries A) :
    (oneBoundariesToOneCycles A x).1 = x.1 := rfl

end

theorem single_one_mem_oneBoundaries (a : A) :
    single 1 a ∈ oneBoundaries A := by
  use single (1, 1) a
  simp

theorem single_ρ_self_add_single_inv_mem_oneBoundaries (g : G) (a : A) :
    single g (A.ρ g a) + single g⁻¹ a ∈ oneBoundaries A := by
  rw [← dOne_single_ρ_add_single_inv_mul g 1]
  exact Set.mem_range_self _

theorem single_inv_ρ_self_add_single_mem_oneBoundaries (g : G) (a : A) :
    single g⁻¹ (A.ρ g⁻¹ a) + single g a ∈ oneBoundaries A := by
  rw [← dOne_single_inv_mul_ρ_add_single g 1]
  exact Set.mem_range_self _


section

variable [DecidableEq G]

lemma mem_twoCycles_of_mem_twoBoundaries (x : G × G →₀ A) (h : x ∈ twoBoundaries A) :
    x ∈ twoCycles A := by
  rcases h with ⟨x, rfl⟩
  exact dTwo_apply_mem_twoCycles x

variable (A) in
lemma twoBoundaries_le_twoCycles : twoBoundaries A ≤ twoCycles A :=
  mem_twoCycles_of_mem_twoBoundaries

variable (A) in
/-- Natural inclusion `B₂(G, A) →ₗ[k] Z₂(G, A)`. -/
abbrev twoBoundariesToTwoCycles [DecidableEq G] : twoBoundaries A →ₗ[k] twoCycles A :=
  Submodule.inclusion (twoBoundaries_le_twoCycles A)

@[simp]
lemma twoBoundariesToTwoCycles_apply (x : twoBoundaries A) :
    (twoBoundariesToTwoCycles A x).1 = x.1 := rfl

end

lemma single_one_fst_sub_single_one_fst_mem_twoBoundaries (g h : G) (a : A) :
    single (1, g * h) a - single (1, g) a ∈ twoBoundaries A := by
  use single (1, g, h) a
  simp

lemma single_one_fst_sub_single_one_snd_mem_twoBoundaries (g h : G) (a : A) :
    single (1, h) (A.ρ g⁻¹ a) - single (g, 1) a ∈ twoBoundaries A := by
  use single (g, 1, h) a
  simp

lemma single_one_snd_sub_single_one_fst_mem_twoBoundaries (g h : G) (a : A) :
    single (g, 1) (A.ρ g a) - single (1, h) a ∈ twoBoundaries A := by
  use single (g, 1, h) (A.ρ g (-a))
  simp

lemma single_one_snd_sub_single_one_snd_mem_twoBoundaries (g h : G) (a : A) :
    single (h, 1) (A.ρ g⁻¹ a) - single (g * h, 1) a ∈ twoBoundaries A := by
  use single (g, h, 1) a
  simp

end Boundaries
end groupHomology
