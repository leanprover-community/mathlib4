/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston

-/
import Mathlib.RepresentationTheory.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
# The low-degree cocycles and coboundaries of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file gives simple expressions for
the cocycles and coboundaries of a `k`-linear `G`-representatio

## Main definitions

## Implementation notes

## TODO

-/

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

namespace GroupCohomology

open CategoryTheory CategoryTheory.Limits Representation

-- to be moved
@[simp]
theorem inhomogeneousCochains.d_def (n : ℕ) :
    (inhomogeneousCochains A).d n (n + 1) = InhomogeneousCochains.d n A :=
  CochainComplex.of_d _ _ _ _

section Cochains

/-- The 0th object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `A` as a `k`-module. -/
def zeroCochainsIso : (inhomogeneousCochains A).X 0 ≅ ModuleCat.of k A :=
  (LinearEquiv.funUnique (Fin 0 → G) k A).toModuleIso

/-- The 1st object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G, A)` as a `k`-module. -/
def oneCochainsIso : (inhomogeneousCochains A).X 1 ≅ ModuleCat.of k (G → A) :=
  (LinearEquiv.funCongrLeft k A (Equiv.funUnique (Fin 1) G).symm).toModuleIso

/-- The 2nd object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G × G, A)`. -/
def twoCochainsIso : (inhomogeneousCochains A).X 2 ≅ ModuleCat.of k (G × G → A) :=
  (LinearEquiv.funCongrLeft k A <| (piFinTwoEquiv fun _ => G).symm).toModuleIso

/-- The 3rd object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G × G × G, A)`. -/
def threeCochainsIso : (inhomogeneousCochains A).X 3 ≅ ModuleCat.of k (G × G × G → A) :=
  (LinearEquiv.funCongrLeft k A <| ((Equiv.piFinSucc 2 G).trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G))).symm).toModuleIso

end Cochains
section Differentials

/-- The 0th differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `A → Fun(G, A)`. It sends `(a, g) ↦ ρ_A(g)(a) - a.` -/
@[simps]
def dZero : A →ₗ[k] G → A where
  toFun m g := A.ρ g m - m
  map_add' x y := funext fun g => by simp only [map_add, add_sub_add_comm]; rfl
  map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_sub]

theorem dZero_ker_eq_invariants : LinearMap.ker (dZero A) = invariants A.ρ := by
  ext x
  simp only [LinearMap.mem_ker, mem_invariants, ← @sub_eq_zero _ _ _ x, Function.funext_iff]
  rfl

/-- The 1st differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G, A) → Fun(G × G, A)`. It sends
`(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
@[simps]
def dOne : (G → A) →ₗ[k] G × G → A where
  toFun f g := A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1
  map_add' x y := funext fun g => by dsimp; rw [map_add, add_add_add_comm, add_sub_add_comm]
  map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_add, smul_sub]

/-- The 2nd differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G × G, A) → Fun(G × G × G, A)`. It sends
`(f, (g₁, g₂, g₃)) ↦ ρ_A(g₁)(f(g₂, g₃)) - f(g₁g₂, g₃) + f(g₁, g₂g₃) - f(g₁, g₂).` -/
@[simps]
def dTwo : (G × G → A) →ₗ[k] G × G × G → A where
  toFun f g :=
    A.ρ g.1 (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2) + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1)
  map_add' x y :=
    funext fun g => by
      dsimp
      rw [map_add, add_sub_add_comm (A.ρ _ _), add_sub_assoc, add_sub_add_comm, add_add_add_comm,
        add_sub_assoc, add_sub_assoc]
  map_smul' r x := funext fun g => by dsimp; simp only [map_smul, smul_add, smul_sub]

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `dZero` gives a simpler expression for the 0th differential: that is, the following
square commutes:
```
  C⁰(G, A) ---d⁰---> C¹(G, A)
  |                    |
  |                    |
  |                    |
  v                    v
  A ---- d_zero ---> Fun(G, A)
```
where the vertical arrows are `zeroCochainsIso` and `oneCochainsIso` respectively.
-/
@[reassoc]
theorem comp_dZero_eq :
    (zeroCochainsIso A).hom ≫ ModuleCat.ofHom (dZero A) =
      (inhomogeneousCochains A).d 0 1 ≫ (oneCochainsIso A).hom := by
  ext x
  funext y
  show A.ρ y (x default) - x default = _ + ({0} : Finset _).sum _
  simp_rw [Fin.coe_fin_one, zero_add, pow_one, neg_smul, one_smul,
    Finset.sum_singleton, sub_eq_add_neg]
  rcongr i <;> exact Fin.elim0 i

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `dOne` gives a simpler expression for the 1st differential: that is, the following
square commutes:
```
  C¹(G, A) ---d¹-----> C²(G, A)
    |                      |
    |                      |
    |                      |
    v                      v
  Fun(G, A) -d_one-> Fun(G × G, A)
```
where the vertical arrows are `oneCochainsIso` and `twoCochainsIso` respectively.
-/
@[reassoc]
theorem comp_dOne_eq :
    (oneCochainsIso A).hom ≫ ModuleCat.ofHom (dOne A) =
      (inhomogeneousCochains A).d 1 2 ≫ (twoCochainsIso A).hom := by
  ext x
  funext y
  show A.ρ y.1 (x _) - x _ + x _ =  _ + _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Fin.val_one,
    Nat.one_add, neg_one_sq, sub_eq_add_neg, add_assoc]
  rcongr i <;> rw [Subsingleton.elim i 0] <;> rfl

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `dTwo` gives a simpler expression for the 2nd differential: that is, the following
square commutes:
```
      C²(G, A) ------d²-----> C³(G, A)
        |                         |
        |                         |
        |                         |
        v                         v
  Fun(G × G, A) --d_two--> Fun(G × G × G, A)
```
where the vertical arrows are `twoCochainsIso` and `threeCochainsIso` respectively.
-/
@[reassoc]
theorem comp_dTwo_eq :
    (twoCochainsIso A).hom ≫ ModuleCat.ofHom (dTwo A) =
      (inhomogeneousCochains A).d 2 3 ≫ (threeCochainsIso A).hom := by
  ext x
  funext y
  show A.ρ y.1 (x _) - x _ + x _ - x _ = _ + _
  dsimp
  rw [Fin.sum_univ_three]
  simp only [sub_eq_add_neg, add_assoc, Fin.val_zero, zero_add, pow_one, neg_smul,
    one_smul, Fin.val_one, Fin.val_two, pow_succ (-1 : k) 2, neg_sq, Nat.one_add, one_pow, mul_one]
  rcongr i <;> fin_cases i <;> rfl

theorem dOne_comp_dZero : dOne A ∘ₗ dZero A = 0 := by
  ext x g
  simp only [LinearMap.coe_comp, Function.comp_apply, dOne_apply A, dZero_apply A, map_sub,
    map_mul, LinearMap.mul_apply, sub_sub_sub_cancel_left, sub_add_sub_cancel, sub_self]
  rfl

theorem dTwo_comp_dOne : dTwo A ∘ₗ dOne A = 0 := by
  show ModuleCat.ofHom (dOne A) ≫ ModuleCat.ofHom (dTwo A) = _
  simp only [(Iso.eq_inv_comp _).2 (comp_dTwo_eq A), (Iso.eq_inv_comp _).2 (comp_dOne_eq A),
    Category.assoc, Iso.hom_inv_id_assoc, HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]

end Differentials

section Cocycles

/-- The 1-cocycles `Z¹(G, A)` of `A : Rep k G`, defined as the kernel of the map
`Fun(G, A) → Fun(G × G, A)` sending `(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
def oneCocycles : Submodule k (G → A) := LinearMap.ker (dOne A)

/-- The 2-cocycles `Z²(G, A)` of `A : Rep k G`, defined as the kernel of the map
`Fun(G × G, A) → Fun(G × G × G, A)` sending
`(f, (g₁, g₂, g₃)) ↦ ρ_A(g₁)(f(g₂, g₃)) - f(g₁g₂, g₃) + f(g₁, g₂g₃) - f(g₁, g₂).` -/
def twoCocycles : Submodule k (G × G → A) := LinearMap.ker (dTwo A)

variable {A}

theorem mem_oneCocycles (f : G → A) :
    f ∈ oneCocycles A ↔ ∀ g : G × G, A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1 = 0 :=
  LinearMap.mem_ker.trans Function.funext_iff

theorem mem_oneCocycles_iff (f : G → A) :
    f ∈ oneCocycles A ↔ ∀ g : G × G, f (g.1 * g.2) = A.ρ g.1 (f g.2) + f g.1 := by
  simp_rw [mem_oneCocycles, sub_add_eq_add_sub, sub_eq_zero, eq_comm]

theorem oneCocycles_map_one (f : oneCocycles A) : f.1 1 = 0 := by
  have := (mem_oneCocycles f.1).1 f.2 (1, 1)
  simpa only [map_one, LinearMap.one_apply, mul_one, sub_self, zero_add] using this

theorem oneCocycles_map_inv (f : oneCocycles A) (g : G) :
    A.ρ g (f.1 g⁻¹) = - f.1 g := by
  rw [← add_eq_zero_iff_eq_neg, ← oneCocycles_map_one f, ← mul_inv_self g,
    (mem_oneCocycles_iff f.1).1 f.2 (g, g⁻¹)]

theorem mem_twoCocycles (f : G × G → A) :
    f ∈ twoCocycles A ↔ ∀ g : G × G × G,
      A.ρ g.1 (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2) +
        f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1) = 0 :=
  LinearMap.mem_ker.trans Function.funext_iff

theorem mem_twoCocycles_iff (f : G × G → A) :
    f ∈ twoCocycles A ↔ ∀ g : G × G × G,
      f (g.1 * g.2.1, g.2.2) + f (g.1, g.2.1) =
        A.ρ g.1 (f (g.2.1, g.2.2)) + f (g.1, g.2.1 * g.2.2) := by
  simp_rw [mem_twoCocycles, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add, eq_comm,
    add_comm (f (Prod.fst _, _))]

theorem twoCocycles_map_one_fst (g : G) (f : twoCocycles A) :
    f.1 (1, g) = f.1 (1, 1) := by
  have := ((mem_twoCocycles_iff f.1).1 f.2 (1, (1, g))).symm
  simpa only [map_one, LinearMap.one_apply, one_mul, add_right_inj, this]

theorem twoCocycles_map_one_snd (g : G) (f : twoCocycles A) :
    f.1 (g, 1) = A.ρ g (f.1 (1, 1)) := by
  have := (mem_twoCocycles_iff f.1).1 f.2 (g, (1, 1))
  simpa only [mul_one, add_left_inj, this]

end Cocycles
section Coboundaries

/-- The 1-coboundaries `B¹(G, A)` of `A : Rep k G`, defined as the image of the map
`A → Fun(G, A)` sending `(a, g) ↦ ρ_A(g)(a) - a.` -/
def oneCoboundaries : Submodule k (oneCocycles A) :=
  LinearMap.range ((dZero A).codRestrict (oneCocycles A) fun c =>
    LinearMap.ext_iff.1 (dOne_comp_dZero A) c)

/-- The 2-coboundaries `B²(G, A)` of `A : Rep k G`, defined as the image of the map
`Fun(G, A) → Fun(G × G, A)` sending `(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
def twoCoboundaries : Submodule k (twoCocycles A) :=
  LinearMap.range ((dOne A).codRestrict (twoCocycles A) fun c =>
    LinearMap.ext_iff.1 (dTwo_comp_dOne.{u} A) c)

variable {A}

theorem mem_oneCoboundaries_of_dZero_apply (x : A) :
  ⟨dZero A x, LinearMap.ext_iff.1 (dOne_comp_dZero A) x⟩ ∈ oneCoboundaries A :=
LinearMap.mem_range_self _ _

theorem mem_oneCoboundaries_of_mem_range (f : G → A) (h : f ∈ LinearMap.range (dZero A)) :
    ⟨f, LinearMap.range_le_ker_iff.2 (dOne_comp_dZero A) h⟩ ∈ oneCoboundaries A := by
  rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩

theorem mem_range_of_mem_oneCoboundaries (f : oneCocycles A) (h : f ∈ oneCoboundaries A) :
    f.1 ∈ LinearMap.range (dZero A) := by
  rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩

theorem mem_twoCoboundaries_of_dOne_apply (x : G → A) :
  ⟨dOne A x, LinearMap.ext_iff.1 (dTwo_comp_dOne A) x⟩ ∈ twoCoboundaries A :=
LinearMap.mem_range_self _ _

theorem mem_twoCoboundaries_of_mem_range (f : G × G → A) (h : f ∈ LinearMap.range (dOne A)) :
    ⟨f, LinearMap.range_le_ker_iff.2 (dTwo_comp_dOne A) h⟩ ∈ twoCoboundaries A := by
  rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩

theorem mem_range_of_mem_twoCoboundaries (f : twoCocycles A) (h : f ∈ twoCoboundaries A) :
    (twoCocycles A).subtype f ∈ LinearMap.range (dOne A) := by
  rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩

end Coboundaries
end GroupCohomology
