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

Let `k` be a commutative ring and `G` a group. This file will give simple expressions for
the group homology of a `k`-linear `G`-representation `A` in degrees 0, 1 and 2.
In `RepresentationTheory.Homological.GroupHomology.Basic`, we define the `n`th group homology of
`A` to be the homology of a complex `inhomogeneousChains A`, whose objects are `(Fin n →₀ G) → A`;
this is unnecessarily unwieldy in low degree. Moreover, homology of a complex is defined as an
abstract cokernel, whereas the definitions here will be explicit quotients of cycles by boundaries.

Given an additive abelian group `A` with an appropriate scalar action of `G`, we provide support
for turning a finsupp `f : G →₀ A` satisfying the 1-cycle identity into an element of the
`oneCycles` of the representation on `A` corresponding to the scalar action. We also do this for
0-boundaries, 1-boundaries, 2-cycles and 2-boundaries.

The file also contains an identification between the definitions in
`RepresentationTheory.Homological.GroupHomology.Basic`, `groupHomology.cycles A n` and
`groupHomology A n`, and the `nCycles` and `Hn A` in this file, for `n = 0, 1, 2`.

## Main definitions

* `groupHomology.H0 A`: the coinvariants `A_G` of the `G`-representation on `A`.
* `groupHomology.H1 A`: 1-cycles (i.e. `Z₁(G, A) := Ker(d₀ : (G →₀ A) → A`) modulo
  1-boundaries (i.e. `B₁(G, A) := Im(d₁ : (G² →₀ A) → (G →₀ A))`).
* `groupHomology.H2 A`: 2-cycles (i.e. `Z₁(G, A) := Ker(d₁ : (G² →₀ A) → (G →₀ A)`) modulo
  2-boundaries (i.e. `B₁(G, A) := Im(d₂ : (G³ →₀ A) → (G² →₀ A))`).
* `groupHomology.isoHn` for `n = 0, 1, 2`: an isomorphism `groupHomology A n ≅ groupHomology.Hn A`.

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
  simp only [map_sub, dOne_single, inv_inv, self_inv_apply, inv_mul_cancel, mul_inv_cancel]
  abel

lemma dOne_single_self_inv_ρ_sub_inv_self (g : G) (a : A) :
    dOne A (single (g, g⁻¹) (A.ρ g a) - single (g⁻¹, g) a) =
      single 1 a - single 1 (A.ρ g a) := by
  simp only [map_sub, dOne_single, inv_self_apply, mul_inv_cancel, inv_inv, inv_mul_cancel]
  abel

lemma dOne_single_ρ_add_single_inv_mul (g h : G) (a : A) :
    dOne A (single (g, h) (A.ρ g a) + single (g⁻¹, g * h) a) =
      single g (A.ρ g a) + single g⁻¹ a := by
  simp only [map_add, dOne_single, inv_self_apply, inv_inv, inv_mul_cancel_left]
  abel

lemma dOne_single_inv_mul_ρ_add_single (g h : G) (a : A) :
    dOne A (single (g⁻¹, g * h) (A.ρ g⁻¹ a) + single (g, h) a) =
      single g⁻¹ (A.ρ g⁻¹ a) + single g a := by
  simp only [map_add, dOne_single, inv_inv, self_inv_apply, inv_mul_cancel_left]
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
  simp [mem_oneCycles_iff, ← (A.ρ.apply_bijective g).1.eq_iff (a := A.ρ g⁻¹ a), eq_comm]

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
  rw [← (mapRange_injective (α := G) _ (map_zero _) (A.ρ.apply_bijective g.1⁻¹).1).eq_iff]
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

section IsCycle

section

variable {G A : Type*} [Mul G] [Inv G] [AddCommGroup A] [SMul G A]

/-- A finsupp `∑ aᵢ·gᵢ : G →₀ A` satisfies the 1-cycle condition if `∑ gᵢ⁻¹ • aᵢ = ∑ aᵢ`. -/
def IsOneCycle (x : G →₀ A) : Prop := x.sum (fun g a => g⁻¹ • a) = x.sum (fun _ a => a)

/-- A finsupp `∑ aᵢ·(gᵢ, hᵢ) : G × G →₀ A` satisfies the 2-cycle condition if
`∑ (gᵢ⁻¹ • aᵢ)·hᵢ + aᵢ·gᵢ = ∑ aᵢ·gᵢhᵢ`. -/
def IsTwoCycle (x : G × G →₀ A) : Prop :=
  x.sum (fun g a => single g.2 (g.1⁻¹ • a) + single g.1 a) =
    x.sum (fun g a => single (g.1 * g.2) a)

end

section

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

@[simp]
theorem single_isOneCycle_iff (g : G) (a : A) :
    IsOneCycle (single g a) ↔ g • a = a := by
  rw [← (MulAction.bijective g⁻¹).1.eq_iff]
  simp [IsOneCycle, eq_comm]

theorem single_isOneCycle_of_mem_fixedPoints
    (g : G) (a : A) (ha : a ∈ MulAction.fixedPoints G A) :
    IsOneCycle (single g a) := by
  simp_all [IsOneCycle]

theorem single_isTwoCycle_iff_inv (g : G × G) (a : A) :
    IsTwoCycle (single g a) ↔
      single g.2 (g.1⁻¹ • a) + single g.1 a = single (g.1 * g.2) a := by
  simp [IsTwoCycle]

@[simp]
theorem single_isTwoCycle_iff (g : G × G) (a : A) :
    IsTwoCycle (single g a) ↔
      single g.2 a + single g.1 (g.1 • a) = single (g.1 * g.2) (g.1 • a) := by
  rw [← (Finsupp.mapRange_injective (α := G) _ (smul_zero _) (MulAction.bijective g.1⁻¹).1).eq_iff]
  simp [mapRange_add, IsTwoCycle]

end

end IsCycle

section IsBoundary

section

variable {G A : Type*} [Mul G] [Inv G] [AddCommGroup A] [SMul G A]

variable (G) in
/-- A term `x : A` satisfies the 0-boundary condition if there exists a finsupp
`∑ aᵢ·gᵢ : G →₀ A` such that `∑ gᵢ⁻¹ • aᵢ - aᵢ = x`. -/
def IsZeroBoundary (a : A) : Prop :=
  ∃ (x : G →₀ A), x.sum (fun g a => g⁻¹ • a - a) = a

/-- A finsupp `x : G →₀ A` satisfies the 1-boundary condition if there's a finsupp
`∑ aᵢ·(gᵢ, hᵢ) : G × G →₀ A` such that `∑ (gᵢ⁻¹ • aᵢ)·hᵢ - aᵢ·gᵢhᵢ + aᵢ·gᵢ = x`. -/
def IsOneBoundary (x : G →₀ A) : Prop :=
  ∃ y : G × G →₀ A, y.sum
    (fun g a => single g.2 (g.1⁻¹ • a) - single (g.1 * g.2) a + single g.1 a) = x

/-- A finsupp `x : G × G →₀ A` satsfies the 2-boundary condition if there's a finsupp
`∑ aᵢ·(gᵢ, hᵢ, jᵢ) : G × G × G →₀ A` such that
`∑ (gᵢ⁻¹ • aᵢ)·(hᵢ, jᵢ) - aᵢ·(gᵢhᵢ, jᵢ) + aᵢ·(gᵢ, hᵢjᵢ) - aᵢ·(gᵢ, hᵢ) = x.` -/
def IsTwoBoundary (x : G × G →₀ A) : Prop :=
  ∃ y : G × G × G →₀ A, y.sum (fun g a => single (g.2.1, g.2.2) (g.1⁻¹ • a) -
    single (g.1 * g.2.1, g.2.2) a + single (g.1, g.2.1 * g.2.2) a - single (g.1, g.2.1) a) = x

end
section

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

variable (G) in
theorem isZeroBoundary_iff (a : A) :
    IsZeroBoundary G a ↔ ∃ x : G →₀ A, x.sum (fun g a => g • a - a) = a := by
  constructor
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (- (g⁻¹ • a)))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (- (g • a)))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]

theorem isOneBoundary_iff (x : G →₀ A) :
    IsOneBoundary x ↔ ∃ y : G × G →₀ A, y.sum
      (fun g a => single g.2 a - single (g.1 * g.2) (g.1 • a) + single g.1 (g.1 • a)) = x := by
  constructor
  · rintro ⟨y, hy⟩
    use y.sum (fun g a => single g (g.1⁻¹ • a))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (g.1 • a))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]

theorem isTwoBoundary_iff (x : G × G →₀ A) :
    IsTwoBoundary x ↔ ∃ y : G × G × G →₀ A, y.sum
      (fun g a => single (g.2.1, g.2.2) a - single (g.1 * g.2.1, g.2.2) (g.1 • a) +
        single (g.1, g.2.1 * g.2.2) (g.1 • a) - single (g.1, g.2.1) (g.1 • a)) = x := by
  constructor
  · rintro ⟨y, hy⟩
    use y.sum (fun g a => single g (g.1⁻¹ • a))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (g.1 • a))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]

end
end IsBoundary

section ofDistribMulAction

variable {k G A : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a term
`x : A` satisfying the 0-boundary condition, produces an element of the augmentation submodule for
the representation on `A` induced by the `DistribMulAction`. -/
@[simps]
def augmentationSubmoduleOfIsZeroBoundary (x : A) (hx : IsZeroBoundary G x) :
    augmentationSubmodule (Representation.ofDistribMulAction k G A) :=
  ⟨x, by
    rcases (isZeroBoundary_iff G x).1 hx with ⟨y, rfl⟩
    exact Submodule.finsupp_sum_mem _ _ _ _ fun g _ =>
      mem_augmentationSubmodule_of_eq g (y g) _ rfl⟩

theorem isZeroBoundary_of_mem_augmentationSubmodule [DecidableEq G]
    (x : A) (hx : x ∈ augmentationSubmodule (Representation.ofDistribMulAction k G A)) :
    IsZeroBoundary G x :=
  Submodule.span_induction (fun _ ⟨g, hg⟩ => ⟨single g.1⁻¹ g.2, by simp_all⟩) ⟨0, by simp⟩
    (fun _ _ _ _ ⟨X, hX⟩ ⟨Y, hY⟩ => ⟨X + Y, by simp_all [sum_add_index, add_sub_add_comm]⟩)
    (fun r _ _ ⟨X, hX⟩ => ⟨r • X, by simp [← hX, sum_smul_index', smul_comm, smul_sub, smul_sum]⟩)
    hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G →₀ A` satisfying the 1-cycle condition, produces a 1-cycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
def oneCyclesOfIsOneCycle (x : G →₀ A) (hx : IsOneCycle x) :
    oneCycles (Rep.ofDistribMulAction k G A) :=
  ⟨x, (mem_oneCycles_iff (A := Rep.ofDistribMulAction k G A) x).2 hx⟩

theorem isOneCycle_of_mem_oneCycles
    (x : G →₀ A) (hx : x ∈ oneCycles (Rep.ofDistribMulAction k G A)) :
    IsOneCycle x := by
  simpa using (mem_oneCycles_iff (A := Rep.ofDistribMulAction k G A) x).1 hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G →₀ A` satisfying the 1-boundary condition, produces a 1-boundary for the representation
on `A` induced by the `DistribMulAction`. -/
@[simps]
def oneBoundariesOfIsOneBoundary (x : G →₀ A) (hx : IsOneBoundary x) :
    oneBoundaries (Rep.ofDistribMulAction k G A) :=
  ⟨x, hx⟩

theorem isOneBoundary_of_mem_oneBoundaries
    (x : G →₀ A) (hx : x ∈ oneBoundaries (Rep.ofDistribMulAction k G A)) :
    IsOneBoundary x := hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G × G →₀ A` satisfying the 2-cycle condition, produces a 2-cycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
def twoCyclesOfIsTwoCycle (x : G × G →₀ A) (hx : IsTwoCycle x) :
    twoCycles (Rep.ofDistribMulAction k G A) :=
  ⟨x, (mem_twoCycles_iff (A := Rep.ofDistribMulAction k G A) x).2 hx⟩

theorem isTwoCycle_of_mem_twoCycles
    (x : G × G →₀ A) (hx : x ∈ twoCycles (Rep.ofDistribMulAction k G A)) :
    IsTwoCycle x := (mem_twoCycles_iff (A := Rep.ofDistribMulAction k G A) x).1 hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G × G →₀ A` satisfying the 2-boundary condition, produces a 2-boundary for the
representation on `A` induced by the `DistribMulAction`. -/
@[simps]
def twoBoundariesOfIsTwoBoundary (x : G × G →₀ A) (hx : IsTwoBoundary x) :
    twoBoundaries (Rep.ofDistribMulAction k G A) :=
  ⟨x, hx⟩

theorem isTwoBoundary_of_mem_twoBoundaries
    (x : G × G →₀ A) (hx : x ∈ twoBoundaries (Rep.ofDistribMulAction k G A)) :
    IsTwoBoundary x := hx

end ofDistribMulAction

section groupHomologyIso

open ShortComplex

section H0

section

variable [DecidableEq G]

/-- The 0-cycles of the complex of inhomogeneous chains of `A` are isomorphic to `A`. -/
def isoZeroCycles : cycles A 0 ≅ ModuleCat.of k A :=
  (inhomogeneousChains A).iCyclesIso _ 0 (by aesop) (by aesop) ≪≫ (zeroChainsLequiv A).toModuleIso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoZeroCycles_inv_comp_iCycles :
    (isoZeroCycles A).inv ≫ iCycles A 0 = (zeroChainsLequiv A).toModuleIso.inv := by
  simp [isoZeroCycles]

end

/-- The (exact) short complex `(G →₀ A) ⟶ A ⟶ A.ρ.coinvariants`. -/
def shortComplexH0 : ShortComplex (ModuleCat k) :=
  ShortComplex.moduleCatMk _ _ (mkQ_comp_dZero A)

/-- We define the 0th group homology of a `k`-linear `G`-representation `A`, `H₀(G, A)`, to be
the coinvariants of the representation, `A_G`. -/
abbrev H0 := (shortComplexH0 A).X₃

/-- The quotient map `Z₀(G, A) → H₀(G, A).` -/
abbrev H0π : ModuleCat.of k A ⟶ H0 A := (shortComplexH0 A).g

lemma H0π_eq_zero_iff (x : A) : H0π A x = 0 ↔ x ∈ augmentationSubmodule A.ρ :=
  Submodule.Quotient.mk_eq_zero _

lemma H0π_eq_iff (x y : A) : H0π A x = H0π A y ↔ x - y ∈ augmentationSubmodule A.ρ :=
  Submodule.Quotient.eq _

instance : Epi (H0π A) := by
  rw [ModuleCat.epi_iff_surjective]
  exact Submodule.mkQ_surjective _

lemma shortComplexH0_exact : (shortComplexH0 A).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro (x : A) (hx : Submodule.mkQ _ x = 0)
  rw [← range_dZero_eq_augmentationSubmodule, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hx
  rcases hx with ⟨x, hx, rfl⟩
  use x
  rfl

section
variable [DecidableEq G]

/-- The arrow `(G →₀ A) --dZero--> A` is isomorphic to the differential
`(inhomogeneousChains A).d 1 0` of the complex of inhomogeneous chains of `A`. -/
@[simps! hom_left hom_right inv_left inv_right]
def dZeroArrowIso :
    Arrow.mk ((inhomogeneousChains A).d 1 0) ≅ Arrow.mk (ModuleCat.ofHom (dZero A)) :=
  Arrow.isoMk (oneChainsLequiv A).toModuleIso (zeroChainsLequiv A).toModuleIso (dZero_comp_eq A)

/-- The 0-cycles of the complex of inhomogeneous chains of `A` are isomorphic to
`A.ρ.coinvariants`, which is a simpler type. -/
def isoZeroOpcycles : (inhomogeneousChains A).opcycles 0 ≅ ModuleCat.of k A.ρ.coinvariants :=
  CokernelCofork.mapIsoOfIsColimit
    ((inhomogeneousChains A).opcyclesIsCokernel 1 0 (by simp)) (shortComplexH0_exact A).gIsCokernel
      (dZeroArrowIso A)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma pOpcycles_comp_opcyclesIso_hom :
    (inhomogeneousChains A).pOpcycles 0 ≫ (isoZeroOpcycles A).hom =
      (zeroChainsLequiv A).toModuleIso.hom ≫ H0π A := by
  dsimp [isoZeroOpcycles]
  exact CokernelCofork.π_mapOfIsColimit (φ := (dZeroArrowIso A).hom) _ _

/-- The 0th group homology of `A`, defined as the 0th homology of the complex of inhomogeneous
chains, is isomorphic to the coinvariants of the representation on `A`. -/
def isoH0 : groupHomology A 0 ≅ H0 A :=
  ChainComplex.isoHomologyι₀ _ ≪≫ isoZeroOpcycles A

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma groupHomologyπ_comp_isoH0_hom :
    groupHomologyπ A 0 ≫ (isoH0 A).hom = (isoZeroCycles A).hom ≫ H0π A := by
  simp [isoZeroCycles, isoH0]

end
section Trivial

variable [A.IsTrivial]

/-- When the representation on `A` is trivial, then `H₀(G, A)` is all of `A.` -/
def H0LequivOfIsTrivial :
    H0 A ≃ₗ[k] A := Submodule.quotEquivOfEqBot _ A.ρ.augmentationSubmodule_eq_bot_of_isTrivial

@[simp]
theorem H0LequivOfIsTrivial_symm_eq_π :
    (H0LequivOfIsTrivial A).symm = (H0π A).hom := rfl

@[simp]
theorem H0LequivOfIsTrivial_mk (x : A) :
    H0LequivOfIsTrivial A (Submodule.Quotient.mk x) = x := rfl

@[simp]
theorem H0LequivOfIsTrivial_symm_apply (x : A) :
    (H0LequivOfIsTrivial A).symm x = Submodule.Quotient.mk x := rfl

end Trivial
end H0

section H1

variable [DecidableEq G]

/-- The short complex `(G² →₀ A) --dOne--> (G →₀ A) --dZero--> A`. -/
def shortComplexH1 : ShortComplex (ModuleCat k) :=
  moduleCatMk (dOne A) (dZero A) (dZero_comp_dOne A)

/-- We define the 1st group homology of a `k`-linear `G`-representation `A`, `H₁(G, A)`, to be
1-cycles (i.e. `Z₁(G, A) := Ker(d₀ : (G →₀ A) → A`) modulo 1-boundaries
(i.e. `B₁(G, A) := Im(d₁ : (G →₀ A) → A)`). -/
abbrev H1 := moduleCatHomology <| shortComplexH1 A

/-- The quotient map `Z₁(G, A) → H₁(G, A).` -/
abbrev H1π : ModuleCat.of k (oneCycles A) ⟶ H1 A :=
  moduleCatHomologyπ (shortComplexH1 A)

variable {A} in
lemma H1π_eq_zero_iff (x : oneCycles A) : H1π A x = 0 ↔ x.1 ∈ oneBoundaries A := by
  show (LinearMap.range ((dOne A).codRestrict (oneCycles A) _)).mkQ _ = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.range_codRestrict]
  rfl

variable {A} in
lemma H1π_eq_iff (x y : oneCycles A) :
    H1π A x = H1π A y ↔ x.1 - y.1 ∈ oneBoundaries A := by
  rw [← sub_eq_zero, ← map_sub]
  exact H1π_eq_zero_iff (x - y)

/-- The short complex `(G² →₀ A) --dOne--> (G →₀ A) --dZero--> A` is isomorphic to the 1st
short complex associated to the complex of inhomogeneous chains of `A`. -/
@[simps! hom inv]
def shortComplexH1Iso : (inhomogeneousChains A).sc' 2 1 0 ≅ shortComplexH1 A :=
    isoMk (twoChainsLequiv A).toModuleIso (oneChainsLequiv A).toModuleIso
      (zeroChainsLequiv A).toModuleIso (dOne_comp_eq A) (dZero_comp_eq A)

/-- The 1-cycles of the complex of inhomogeneous chains of `A` are isomorphic to
`oneCycles A`, which is a simpler type. -/
def isoOneCycles : cycles A 1 ≅ ModuleCat.of k (oneCycles A) :=
  (inhomogeneousChains A).cyclesIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    cyclesMapIso (shortComplexH1Iso A) ≪≫ (shortComplexH1 A).moduleCatCyclesIso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoOneCycles_hom_comp_subtype :
    (isoOneCycles A).hom ≫ ModuleCat.ofHom (oneCycles A).subtype =
      iCycles A 1 ≫ (oneChainsLequiv A).toModuleIso.hom := by
  have := (shortComplexH1 A).moduleCatCyclesIso_hom_subtype
  simp_all [shortComplexH1, isoOneCycles, oneCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoOneCycles_inv_comp_iCycles :
    (isoOneCycles A).inv ≫ iCycles A 1 =
      ModuleCat.ofHom (oneCycles A).subtype ≫ (oneChainsLequiv A).toModuleIso.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, isoOneCycles_hom_comp_subtype]

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toCycles_comp_isoOneCycles_hom :
    toCycles A 2 1 ≫ (isoOneCycles A).hom =
      (twoChainsLequiv A).toModuleIso.hom ≫
        ModuleCat.ofHom (shortComplexH1 A).moduleCatToCycles := by
  simp [isoOneCycles]

/-- The 1st group homology of `A`, defined as the 1st homology of the complex of inhomogeneous
chains, is isomorphic to `oneCycles A ⧸ oneBoundaries A`, which is a simpler type. -/
def isoH1 : groupHomology A 1 ≅ H1 A :=
  (inhomogeneousChains A).homologyIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    homologyMapIso (shortComplexH1Iso A) ≪≫ (shortComplexH1 A).moduleCatHomologyIso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma groupHomologyπ_comp_isoH1_hom  :
    groupHomologyπ A 1 ≫ (isoH1 A).hom = (isoOneCycles A).hom ≫ H1π A := by
  simp [H1π, isoH1, isoOneCycles]

end H1

section H2

variable [DecidableEq G]

/-- The short complex `(G³ →₀ A) --dTwo--> (G² →₀ A) --dOne--> (G →₀ A)`. -/
def shortComplexH2 : ShortComplex (ModuleCat k) :=
  moduleCatMk (dTwo A) (dOne A) (dOne_comp_dTwo A)

/-- We define the 2nd group homology of a `k`-linear `G`-representation `A`, `H₂(G, A)`, to be
2-cycles (i.e. `Z₂(G, A) := Ker(d₁ : (G² →₀ A) → (G →₀ A)`) modulo 2-boundaries
(i.e. `B₂(G, A) := Im(d₂ : (G³ →₀ A) → (G² →₀ A))`). -/
abbrev H2 := moduleCatHomology <| shortComplexH2 A

/-- The quotient map `Z₂(G, A) → H₂(G, A).` -/
abbrev H2π : ModuleCat.of k (twoCycles A) ⟶ H2 A :=
  moduleCatHomologyπ (shortComplexH2 A)

variable {A} in
lemma H2π_eq_zero_iff (x : twoCycles A) : H2π A x = 0 ↔ x.1 ∈ twoBoundaries A := by
  show (LinearMap.range ((dTwo A).codRestrict (twoCycles A) _)).mkQ _ = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.range_codRestrict]
  rfl

variable {A} in
lemma H2π_eq_iff (x y : twoCycles A) :
    H2π A x = H2π A y ↔ x.1 - y.1 ∈ twoBoundaries A := by
  rw [← sub_eq_zero, ← map_sub]
  exact H2π_eq_zero_iff (x - y)

/-- The short complex `(G³ →₀ A) --dTwo--> (G² →₀ A) --dOne--> (G →₀ A)` is
isomorphic to the 2nd short complex associated to the complex of inhomogeneous chains of `A`. -/
@[simps! hom inv]
def shortComplexH2Iso :
    (inhomogeneousChains A).sc' 3 2 1 ≅ shortComplexH2 A :=
  isoMk (threeChainsLequiv A).toModuleIso (twoChainsLequiv A).toModuleIso
    (oneChainsLequiv A).toModuleIso (dTwo_comp_eq A) (dOne_comp_eq A)

/-- The 2-cycles of the complex of inhomogeneous chains of `A` are isomorphic to
`twoCycles A`, which is a simpler type. -/
def isoTwoCycles : cycles A 2 ≅ ModuleCat.of k (twoCycles A) :=
  (inhomogeneousChains A).cyclesIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    cyclesMapIso (shortComplexH2Iso A) ≪≫ (shortComplexH2 A).moduleCatCyclesIso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoTwoCycles_hom_comp_subtype :
    (isoTwoCycles A).hom ≫ ModuleCat.ofHom (twoCycles A).subtype =
      iCycles A 2 ≫ (twoChainsLequiv A).toModuleIso.hom := by
  have := (shortComplexH2 A).moduleCatCyclesIso_hom_subtype
  simp_all [shortComplexH2, isoTwoCycles, twoCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoTwoCycles_inv_comp_iCycles :
    (isoTwoCycles A).inv ≫ iCycles A 2 =
      ModuleCat.ofHom (twoCycles A).subtype ≫ (twoChainsLequiv A).toModuleIso.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, isoTwoCycles_hom_comp_subtype]

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toCycles_comp_isoTwoCycles_hom :
    toCycles A 3 2 ≫ (isoTwoCycles A).hom =
      (threeChainsLequiv A).toModuleIso.hom ≫
        ModuleCat.ofHom (shortComplexH2 A).moduleCatToCycles := by
  simp [isoTwoCycles]

/-- The 2nd group homology of `A`, defined as the 2nd homology of the complex of inhomogeneous
chains, is isomorphic to `twoCycles A ⧸ twoBoundaries A`, which is a simpler type. -/
def isoH2 : groupHomology A 2 ≅ H2 A :=
  (inhomogeneousChains A).homologyIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    homologyMapIso (shortComplexH2Iso A) ≪≫ (shortComplexH2 A).moduleCatHomologyIso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma groupHomologyπ_comp_isoH2_hom  :
    groupHomologyπ A 2 ≫ (isoH2 A).hom = (isoTwoCycles A).hom ≫ H2π A := by
  simp [H2π, isoH2, isoTwoCycles]

end H2

end groupHomologyIso

end groupHomology
