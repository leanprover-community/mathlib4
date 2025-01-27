/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
# The low-degree homology of a `k`-linear `G`-representation
Let `k` be a commutative ring and `G` a group. This file gives simple expressions for
the group homology of a `k`-linear `G`-representation `A` in degrees 0, 1 and 2.
In `RepresentationTheory.GroupHomology.Basic`, we define the `n`th group homology of `A` to be
the cohomology of a complex `inhomogeneousChains A`, whose objects are `(Fin n →₀ G) → A`; this is
unnecessarily unwieldy in low degree. Moreover, homology of a complex is defined as an abstract
cokernel, whereas the definitions here are explicit quotients of cocycles by coboundaries.
We also show that when the representation on `A` is trivial, `H₁(G, A) ≃+ Gᵃᵇ ⊗[ℤ] A`.
Given an additive abelian group `A` with an appropriate scalar action of `G`, we provide support
for turning a finsupp `f : G →₀ A` satisfying the 1-cycle identity into an element of the
`oneCycles` of the representation on `A` corresponding to the scalar action. We also do this for
0-boundaries, 1-boundaries, 2-cycles and 2-boundaries.
The file also contains an identification between the definitions in
`RepresentationTheory.GroupHomology.Basic`, `groupHomology.cycles A n` and
`groupHomology A n`, and the `nCycles` and `Hn A` in this file, for `n = 0, 1, 2`.
## Main definitions
* `groupHomology.H0 A`: the coinvariants `A_G` of the `G`-representation on `A`.
* `groupHomology.H1 A`: 1-cycles (i.e. `Z₁(G, A) := Ker(d₀ : (G →₀ A) → A`) modulo
1-boundaries (i.e. `B₁(G, A) := Im(d₁ : (G² →₀ A) → (G →₀ A))`).
* `groupHomology.H2 A`: 2-cycles (i.e. `Z₁(G, A) := Ker(d₁ : (G² →₀ A) → (G →₀ A)`) modulo
2-boundaries (i.e. `B₁(G, A) := Im(d₂ : (G³ →₀ A) → (G² →₀ A))`).
* `groupHomology.isoHn` for `n = 0, 1, 2`: an isomorphism `groupHomology A n ≅ groupHomology.Hn A`.
* `groupHomology.H1LequivOfIsTrivial`: an isomorphism `H₁(G, A) ≃+ Gᵃᵇ ⊗[ℤ] A` when the
representation on `A` is trivial.
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
    dZero A (single g⁻¹ a) = -(dZero A (single g (A.ρ g a))) := by
  simp

theorem range_dZero_eq_augmentationSubmodule :
    LinearMap.range (dZero A) = augmentationSubmodule A.ρ := by
  symm
  apply Submodule.span_eq_of_le
  · rintro _ ⟨x, rfl⟩
    use single x.1⁻¹ x.2
    simp
  · rintro x ⟨y, hy⟩
    induction' y using Finsupp.induction with g a s _ _ h generalizing x
    · simp [← hy]
    · simpa [← hy, add_sub_add_comm, sum_add_index]
        using Submodule.add_mem _ (mem_augmentationSubmodule_of_eq _ _ _ rfl) (h rfl)

lemma mkQ_comp_dZero : (augmentationSubmodule A.ρ).mkQ ∘ₗ dZero A = 0 := by
  rw [← range_dZero_eq_augmentationSubmodule]
  exact LinearMap.range_mkQ_comp _

/-- The 0th differential in the complex of inhomogeneous chains of a `G`-representation `A` as a
linear map into the `k`-submodule of `A` spanned by elements of the form
`ρ(g)(x) - x, g ∈ G, x ∈ A`.-/
def oneChainsToAugmentationSubmodule [DecidableEq G] :
    (G →₀ A) →ₗ[k] augmentationSubmodule A.ρ :=
  (dZero A).codRestrict _ <| range_dZero_eq_augmentationSubmodule A ▸ LinearMap.mem_range_self _

@[simp]
theorem dZero_eq_zero_of_isTrivial [A.ρ.IsTrivial] : dZero A = 0 := by
  ext
  simp

/-- The 1st differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G² →₀ A) → (G →₀ A)`. It sends
`single (g₁, g₂) a ↦ single g₂ ρ_A(g₁⁻¹)(a) - single g₁g₂ a + single g₁ a`. -/
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
  simp
  abel

lemma dOne_single_self_inv_ρ_sub_inv_self (g : G) (a : A) :
    dOne A (single (g, g⁻¹) (A.ρ g a) - single (g⁻¹, g) a) =
      single 1 a - single 1 (A.ρ g a) := by
  simp
  abel

lemma dOne_single_ρ_add_single_inv_mul (g h : G) (a : A) :
    dOne A (single (g, h) (A.ρ g a) + single (g⁻¹, g * h) a) =
      single g (A.ρ g a) + single g⁻¹ a := by
  simp
  abel

lemma dOne_single_inv_mul_ρ_add_single (g h : G) (a : A) :
    dOne A (single (g⁻¹, g * h) (A.ρ g⁻¹ a) + single (g, h) a) =
      single g⁻¹ (A.ρ g⁻¹ a) + single g a := by
  simp
  abel

variable (A) in
/-- The 2nd differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G³ →₀ A) → (G² →₀ A)`. It sends
`single (g₁, g₂, g₃) a ↦ single (g₂, g₃) ρ_A(g₁⁻¹)(a) - single (g₁g₂, g₃) a +`
`single (g₁, g₂g₃) a - single (g₁, g₂) a`. -/
def dTwo : (G × G × G →₀ A) →ₗ[k] G × G →₀ A :=
  lsum k fun g => lsingle (g.2.1, g.2.2) ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2.1, g.2.2)
    + lsingle (g.1, g.2.1 * g.2.2) - lsingle (g.1, g.2.1)

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

@[simp]
theorem _root_.Fin.contractNth_zero {α : Type*} (op : α → α → α) (g : Fin 1 → α) (j : Fin 1) :
    Fin.contractNth j op g = g ∘ Fin.castSucc := by
  ext i
  exact Fin.elim0 i

@[simp]
theorem _root_.Fin.contractNth_one_zero {α : Type*} (op : α → α → α) (g : Fin 2 → α) :
    Fin.contractNth 0 op g = fun _ => op (g 0) (g 1) := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [Fin.contractNth]

@[simp]
theorem _root_.Fin.contractNth_last {n : ℕ} {α : Type*} {op : α → α → α} (g : Fin (n + 1) → α)
    {j : Fin (n + 1)} (hj : j = Fin.last n) :
    Fin.contractNth j op g = g ∘ Fin.castSucc := by
  ext i
  simp_all [Fin.contractNth]

variable (A)

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
theorem dZero_comp_eq [DecidableEq G] :
    (oneChainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (dZero A) =
      (inhomogeneousChains A).d 1 0 ≫ (zeroChainsLequiv A).toModuleIso.hom :=
  ModuleCat.hom_ext <| lhom_ext fun _ _ => by
    simp [inhomogeneousChains.d_def, zeroChainsLequiv, oneChainsLequiv,
      inhomogeneousChains.d_single, Unique.eq_default (α := Fin 0 → G), sub_eq_add_neg]

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

theorem domLCongr_single {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {α₁ α₂ : Type*} (e : α₁ ≃ α₂) (a : α₁) (m : M) :
    Finsupp.domLCongr (R := R) e (Finsupp.single a m) = Finsupp.single (e a) m := by
  simp

theorem dOne_comp_eq [DecidableEq G] :
    (twoChainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (dOne A) =
      (inhomogeneousChains A).d 2 1 ≫ (oneChainsLequiv A).toModuleIso.hom :=
  ModuleCat.hom_ext <| lhom_ext fun _ _ => by
    simp [inhomogeneousChains.d_def, inhomogeneousChains.d_single, oneChainsLequiv,
      twoChainsLequiv, Fin.contractNth_last _ (show 1 = Fin.last 1 by rfl),
      -Finsupp.domLCongr_apply, domLCongr_single, sub_eq_add_neg, add_assoc]

@[to_additive]
lemma _root_.mul_rotate_comm {α : Type*} [CommSemigroup α] (a b c : α) :
    a * b * c = c * b * a := by
  rw [mul_rotate, mul_comm b]

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
theorem dTwo_comp_eq [DecidableEq G] :
    (threeChainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (dTwo A) =
    (inhomogeneousChains A).d 3 2 ≫ (twoChainsLequiv A).toModuleIso.hom :=
  ModuleCat.hom_ext <| lhom_ext fun _ _ => by
    simpa [inhomogeneousChains.d_def, inhomogeneousChains.d_single, twoChainsLequiv,
      threeChainsLequiv, Fin.contractNth_last _ (show 2 = Fin.last 2 by ext; rfl),
      -domLCongr_apply, domLCongr_single, dTwo, Fin.sum_univ_three, Fin.contractNth, pow_succ,
      Fin.tail_def, sub_eq_add_neg, add_assoc] using add_rotate_comm _ _ _

theorem dZero_comp_dOne [DecidableEq G] : dZero A ∘ₗ dOne A = 0 := by
  ext x g
  simp [dZero, dOne, sum_add_index, sum_sub_index, sub_sub_sub_comm, add_sub_add_comm]

theorem dOne_comp_dTwo [DecidableEq G] : dOne A ∘ₗ dTwo A = 0 := by
  apply_fun ModuleCat.ofHom using (fun _ _ h => ModuleCat.hom_ext_iff.1 h)
  simp [(Iso.eq_inv_comp _).2 (dOne_comp_eq A), (Iso.eq_inv_comp _).2 (dTwo_comp_eq A),
    ModuleCat.ofHom_hom, ModuleCat.hom_ofHom, Category.assoc, Iso.hom_inv_id_assoc,
    HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero, ModuleCat.hom_zero,
    ModuleCat.hom_ext_iff]

end Differentials
