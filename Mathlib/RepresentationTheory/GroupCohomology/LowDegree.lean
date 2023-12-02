/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston

-/
import Mathlib.RepresentationTheory.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
# The low-degree cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file gives simple expressions for
the group cohomology of a `k`-linear `G`-representation `A` in degrees 0, 1 and 2.

In `RepresentationTheory.GroupCohomology.Basic`, we define the `n`th group cohomology of `A` to be
the cohomology of a complex `inhomogeneousCochains A`, whose objects are `(Fin n → G) → A`; this is
unnecessarily unwieldy in low degree. Moreover, cohomology of a complex is defined as an abstract
cokernel, whereas the definitions here are explicit quotients of cocycles by coboundaries.

We also show that when the representation on `A` is trivial, `H¹(G, A) ≃ Hom(G, A)`.

Given an additive or multiplicative abelian group `A` with an appropriate scalar action of `G`,
we provide support for turning a function `f : G → A` satisfying the 1-cocycle identity into an
element of the `oneCocycles` of the representation on `A` (or `Additive A`) corresponding to the
scalar action. We also do this for 1-coboundaries, 2-cocycles and 2-coboundaries.

Later this file will contain an identification between the definition in
`RepresentationTheory.GroupCohomology.Basic`, `groupCohomology A n`, and the `Hn A` in this file,
for `n = 0, 1, 2`.

## Main definitions

* `groupCohomology.H0 A`: the invariants `Aᴳ` of the `G`-representation on `A`.
* `groupCohomology.H1 A`: 1-cocycles (i.e. `Z¹(G, A) := Ker(d¹ : Fun(G, A) → Fun(G², A)`) modulo
1-coboundaries (i.e. `B¹(G, A) := Im(d⁰: A → Fun(G, A))`).
* `groupCohomology.H2 A`: 2-cocycles (i.e. `Z²(G, A) := Ker(d² : Fun(G², A) → Fun(G³, A)`) modulo
2-coboundaries (i.e. `B²(G, A) := Im(d¹: Fun(G, A) → Fun(G², A))`).
* `groupCohomology.H1LequivOfIsTrivial`: the isomorphism `H¹(G, A) ≃ Hom(G, A)` when  the
representation on `A` is trivial.

## TODO

* Identify `Hn A` as defined in this file with `groupCohomology A n` for `n = 0, 1, 2`.
* Hilbert's theorem 90
* The relationship between `H2` and group extensions
* The inflation-restriction exact sequence
* Nonabelian group cohomology

-/

universe v u

noncomputable section

open CategoryTheory Limits Representation

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

namespace groupCohomology

section Cochains

/-- The 0th object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `A` as a `k`-module. -/
def zeroCochainsLequiv : (inhomogeneousCochains A).X 0 ≃ₗ[k] A :=
  LinearEquiv.funUnique (Fin 0 → G) k A

/-- The 1st object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G, A)` as a `k`-module. -/
def oneCochainsLequiv : (inhomogeneousCochains A).X 1 ≃ₗ[k] G → A :=
  LinearEquiv.funCongrLeft k A (Equiv.funUnique (Fin 1) G).symm

/-- The 2nd object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G², A)` as a `k`-module. -/
def twoCochainsLequiv : (inhomogeneousCochains A).X 2 ≃ₗ[k] G × G → A :=
  LinearEquiv.funCongrLeft k A <| (piFinTwoEquiv fun _ => G).symm

/-- The 3rd object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G³, A)` as a `k`-module. -/
def threeCochainsLequiv : (inhomogeneousCochains A).X 3 ≃ₗ[k] G × G × G → A :=
  LinearEquiv.funCongrLeft k A <| ((Equiv.piFinSucc 2 G).trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G))).symm

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

@[simp] theorem dZero_eq_zero [A.IsTrivial] : dZero A = 0 := by
  ext
  simp only [dZero_apply, apply_eq_self, sub_self, LinearMap.zero_apply, Pi.zero_apply]

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
  A ---- dZero ---> Fun(G, A)
```
where the vertical arrows are `zeroCochainsLequiv` and `oneCochainsLequiv` respectively.
-/
theorem dZero_comp_eq : dZero A ∘ₗ (zeroCochainsLequiv A) =
    oneCochainsLequiv A ∘ₗ (inhomogeneousCochains A).d 0 1 := by
  ext x y
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
  Fun(G, A) -dOne-> Fun(G × G, A)
```
where the vertical arrows are `oneCochainsLequiv` and `twoCochainsLequiv` respectively.
-/
theorem dOne_comp_eq : dOne A ∘ₗ oneCochainsLequiv A =
    twoCochainsLequiv A ∘ₗ (inhomogeneousCochains A).d 1 2 := by
  ext x y
  show A.ρ y.1 (x _) - x _ + x _ =  _ + _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Fin.val_one,
    Nat.one_add, neg_one_sq, sub_eq_add_neg, add_assoc]
  rcongr i <;> rw [Subsingleton.elim i 0] <;> rfl

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `dTwo` gives a simpler expression for the 2nd differential: that is, the following
square commutes:
```
      C²(G, A) -------d²-----> C³(G, A)
        |                         |
        |                         |
        |                         |
        v                         v
  Fun(G × G, A) --dTwo--> Fun(G × G × G, A)
```
where the vertical arrows are `twoCochainsLequiv` and `threeCochainsLequiv` respectively.
-/
theorem dTwo_comp_eq :
    dTwo A ∘ₗ twoCochainsLequiv A = threeCochainsLequiv A ∘ₗ (inhomogeneousCochains A).d 2 3 := by
  ext x y
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
  have h1 : _ ≫ ModuleCat.ofHom (dOne A) = _ ≫ _ := congr_arg ModuleCat.ofHom (dOne_comp_eq A)
  have h2 : _ ≫ ModuleCat.ofHom (dTwo A) = _ ≫ _ := congr_arg ModuleCat.ofHom (dTwo_comp_eq A)
  simp only [← LinearEquiv.toModuleIso_hom] at h1 h2
  simp only [(Iso.eq_inv_comp _).2 h2, (Iso.eq_inv_comp _).2 h1,
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

theorem mem_oneCocycles_def (f : G → A) :
    f ∈ oneCocycles A ↔ ∀ g h : G, A.ρ g (f h) - f (g * h) + f g = 0 :=
  LinearMap.mem_ker.trans $ by
    rw [Function.funext_iff]
    simp only [dOne_apply, Pi.zero_apply, Prod.forall]

theorem mem_oneCocycles_iff (f : G → A) :
    f ∈ oneCocycles A ↔ ∀ g h : G, f (g * h) = A.ρ g (f h) + f g := by
  simp_rw [mem_oneCocycles_def, sub_add_eq_add_sub, sub_eq_zero, eq_comm]

@[simp] theorem oneCocycles_map_one (f : oneCocycles A) : f.1 1 = 0 := by
  have := (mem_oneCocycles_def f.1).1 f.2 1 1
  simpa only [map_one, LinearMap.one_apply, mul_one, sub_self, zero_add] using this

@[simp] theorem oneCocycles_map_inv (f : oneCocycles A) (g : G) :
    A.ρ g (f.1 g⁻¹) = - f.1 g := by
  rw [← add_eq_zero_iff_eq_neg, ← oneCocycles_map_one f, ← mul_inv_self g,
    (mem_oneCocycles_iff f.1).1 f.2 g g⁻¹]

section oneCocyclesOfFiniteCyclic
open BigOperators Rep

theorem mem_oneCocycles_of_map_generator (f : G → A) (g : G) (hgmem : ∀ x, x ∈ Submonoid.powers g)
    (hg : ∀ n : ℕ, f (g ^ n) = ∑ i in Finset.range n, A.ρ (g ^ i) (f g)) :
    f ∈ oneCocycles A := (mem_oneCocycles_iff f).2 fun x y => by
  rcases hgmem x with ⟨m, rfl⟩
  rcases hgmem y with ⟨n, rfl⟩
  simp only [← pow_add, hg, map_pow, map_sum, add_comm ((Finset.range n).sum _)]
  convert Finset.sum_range_add _ _ _ using 3
  simp only [pow_add, LinearMap.mul_apply]

variable (A)

/-- The `k`-linear map sending `x : A` to `∑ ρ_A(gⁱ)(x)` for `0 ≤ i < n.` Used for defining one
cocycles when `G` is finite and cyclic. -/
noncomputable def sumρPowers (g : G) (n : ℕ) : A →ₗ[k] A :=
∑ i in Finset.range n, A.ρ (g ^ i)

variable {A}

theorem sumρPowers_def (g : G) (n : ℕ) :
    sumρPowers A g n = ∑ i in Finset.range n, A.ρ (g ^ i) := rfl

@[simp] theorem sumρPowers_zero (g : G) : sumρPowers A g 0 = 0 := by
  simp only [sumρPowers_def, Finset.range_zero, map_pow, Finset.sum_empty]

@[simp] theorem sumρPowers_one (g : G) : sumρPowers A g 1 = 1 := by
  simp only [sumρPowers_def, Finset.range_one, map_pow, Finset.sum_singleton, pow_zero]

theorem sumρPowers_orderOf_eq_norm [Fintype G] (g : G) (hg : ∀ h, h ∈ Submonoid.powers g) :
    sumρPowers A g (orderOf g) = (norm A).hom := by
  ext
  simp only [sumρPowers, norm, map_pow, LinearMap.coeFn_sum, Finset.sum_apply, Rep.homMk_hom]
  exact Finset.sum_bij (fun n _ => g ^ n) (fun a ha => Finset.mem_univ _)
    (fun a _ => by simp only [map_pow])
    (fun a b ha hb (hab : g ^ a = g ^ b) => Nat.ModEq.eq_of_lt_of_lt (pow_eq_pow_iff_modEq.1 hab)
      (Finset.mem_range.1 ha) (Finset.mem_range.1 hb))
    (fun b _ => by
    { rcases hg b with ⟨i, hi⟩
      exact ⟨i % orderOf g, Finset.mem_range.2 (Nat.mod_lt i $ IsOfFinOrder.orderOf_pos
        (isOfFinOrder_of_finite g)), by simp only [Finset.mem_univ, pow_mod_orderOf, hi] at *⟩ })

theorem sumρPowers_add (g : G) (m n : ℕ) :
    sumρPowers A g (m + n) = sumρPowers A g m + (A.ρ g) ^ m * sumρPowers A g n := by
  simp only [sumρPowers_def, map_pow, Finset.sum_range_add, pow_add, add_right_inj,
    ← Finset.mul_sum]

theorem sumρPowers_orderOf_mul (g : G) (i : ℕ) :
    sumρPowers A g (orderOf g * i) = i * sumρPowers A g (orderOf g) := by
  induction i with
  | zero =>
    simp only [Nat.zero_eq, mul_zero, sumρPowers_def, Finset.range_zero, map_pow,
      Finset.sum_empty, Nat.cast_zero, zero_mul]
  | succ i hi =>
    simp only [sumρPowers_def] at *
    simp only [Nat.cast_succ, mul_add, add_mul, ← hi, one_mul, mul_one, Nat.succ_eq_add_one,
      Finset.sum_range_add, pow_add, pow_mul, pow_orderOf_eq_one g, one_pow]

/-- Given a generator `g` of a finite cyclic group `G`, a representation `A` of `G`, and an element
`x : A` of norm zero, the map `G → A` sending `gⁱ ↦ ∑ ρ_A(gʲ)(x)` for `0 ≤ j < i` is
a 1-cocycle. -/
noncomputable def oneCocyclesOfGenerator [Fintype G] (x : A) (g : G)
    (hg : ∀ h, h ∈ Submonoid.powers g) (hx : (norm A).hom x = 0) :
    oneCocycles A where
  val :=
    let φ := (finEquivPowers _ (isOfFinOrder_of_finite g)).symm
    fun h => sumρPowers A g (φ ⟨h, hg h⟩) x
  property := by
    by_cases h1 : g = 1
    · cases h1
      rw [mem_oneCocycles_iff]
      intro g h
      rcases hg g with ⟨n, rfl⟩
      rcases hg h with ⟨m, rfl⟩
      simp only [one_pow, mul_one, finEquivPowers_symm_one, sumρPowers_zero,
        LinearMap.zero_apply, map_one, map_zero, add_zero]
    refine' mem_oneCocycles_of_map_generator _ g hg fun j => _
    rcases Nat.dvd_sub_mod (n := orderOf g) j with ⟨b, hb⟩
    nth_rw 2 [(Nat.sub_eq_iff_eq_add (Nat.mod_le _ _)).1 hb]
    simp only [finEquivPowers_symm_apply, finEquivPowers_symm_self g h1, sumρPowers_one,
      LinearMap.one_apply, ← LinearMap.sum_apply, ← sumρPowers_def, sumρPowers_add,
      sumρPowers_orderOf_mul, ← map_pow, pow_mul, pow_orderOf_eq_one, one_pow, map_one, one_mul,
      LinearMap.add_apply, LinearMap.mul_apply, Module.End.natCast_apply, self_eq_add_left,
      Nat.isUnit_iff, sumρPowers_orderOf_eq_norm g hg]
    erw [hx] -- erw with `norm` again :(
    rw [smul_zero]

theorem oneCocyclesOfGenerator_self [Fintype G] (x : A) (g : G) {hg : ∀ h, h ∈ Submonoid.powers g}
    {hx : (norm A).hom x = (0 : A)} : (oneCocyclesOfGenerator A x g hg hx).1 g = x := by
  by_cases h1 : g = 1
  · cases h1
    simp only [oneCocyclesOfGenerator, oneCocycles_map_one]
    have hU : Unique G := ⟨⟨1⟩, fun a => by rcases hg a with ⟨n, rfl⟩; simp only [one_pow]⟩
    erw [norm_of_unique (hU := hU)] at hx -- :(
    exact hx.symm
  simp_rw [oneCocyclesOfGenerator, finEquivPowers_symm_self _ h1, sumρPowers_one]
  rfl

end oneCocyclesOfFiniteCyclic

theorem oneCocycles_map_mul_of_isTrivial [A.IsTrivial] (f : oneCocycles A) (g h : G) :
    f.1 (g * h) = f.1 g + f.1 h := by
  rw [(mem_oneCocycles_iff f.1).1 f.2, apply_eq_self A.ρ g (f.1 h), add_comm]

theorem mem_oneCocycles_of_addMonoidHom [A.IsTrivial] (f : Additive G →+ A) :
    f ∘ Additive.ofMul ∈ oneCocycles A :=
  (mem_oneCocycles_iff _).2 fun g h => by
    simp only [Function.comp_apply, ofMul_mul, map_add,
      oneCocycles_map_mul_of_isTrivial, apply_eq_self A.ρ g (f (Additive.ofMul h)),
      add_comm (f (Additive.ofMul g))]

variable (A)

/-- When `A : Rep k G` is a trivial representation of `G`, `Z¹(G, A)` is isomorphic to the
group homs `G → A`. -/
@[simps] def oneCocyclesLequivOfIsTrivial [hA : A.IsTrivial] :
    oneCocycles A ≃ₗ[k] Additive G →+ A where
  toFun f :=
    { toFun := f.1 ∘ Additive.toMul
      map_zero' := oneCocycles_map_one f
      map_add' := oneCocycles_map_mul_of_isTrivial f }
  map_add' x y := rfl
  map_smul' r x := rfl
  invFun f :=
    { val := f
      property := mem_oneCocycles_of_addMonoidHom f }
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl

variable {A}

theorem mem_twoCocycles_def (f : G × G → A) :
    f ∈ twoCocycles A ↔ ∀ g h j : G,
      A.ρ g (f (h, j)) - f (g * h, j) + f (g, h * j) - f (g, h) = 0 :=
  LinearMap.mem_ker.trans $ by
    rw [Function.funext_iff]
    simp only [dTwo_apply, Prod.mk.eta, Pi.zero_apply, Prod.forall]

theorem mem_twoCocycles_iff (f : G × G → A) :
    f ∈ twoCocycles A ↔ ∀ g h j : G,
      f (g * h, j) + f (g, h) =
        A.ρ g (f (h, j)) + f (g, h * j) := by
  simp_rw [mem_twoCocycles_def, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add, eq_comm,
    add_comm (f (_ * _, _))]

theorem twoCocycles_map_one_fst (f : twoCocycles A) (g : G) :
    f.1 (1, g) = f.1 (1, 1) := by
  have := ((mem_twoCocycles_iff f.1).1 f.2 1 1 g).symm
  simpa only [map_one, LinearMap.one_apply, one_mul, add_right_inj, this]

theorem twoCocycles_map_one_snd (f : twoCocycles A) (g : G) :
    f.1 (g, 1) = A.ρ g (f.1 (1, 1)) := by
  have := (mem_twoCocycles_iff f.1).1 f.2 g 1 1
  simpa only [mul_one, add_left_inj, this]

lemma twoCocycles_ρ_map_inv_sub_map_inv (f : twoCocycles A) (g : G) :
    A.ρ g (f.1 (g⁻¹, g)) - f.1 (g, g⁻¹)
      = f.1 (1, 1) - f.1 (g, 1) := by
  have := (mem_twoCocycles_iff f.1).1 f.2 g g⁻¹ g
  simp only [mul_right_inv, mul_left_inv, twoCocycles_map_one_fst _ g]
    at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

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

/-- Makes a 1-coboundary out of `f ∈ Im(d⁰)`. -/
def oneCoboundariesOfMemRange (f : G → A) (h : f ∈ LinearMap.range (dZero A)) :
    oneCoboundaries A :=
  ⟨⟨f, LinearMap.range_le_ker_iff.2 (dOne_comp_dZero A) h⟩,
    by rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩⟩

theorem oneCoboundaries_of_mem_range_apply (f : G → A) {h : f ∈ LinearMap.range (dZero A)} :
    (oneCoboundariesOfMemRange f h).1.1 = f := rfl

/-- Makes a 1-coboundary out of `f : G → A` and `x` such that
`ρ(g)(x) - x = f(g)` for all `g : G`. -/
def oneCoboundariesOfEq (f : G → A) (x : A) (hf : ∀ g, A.ρ g x - x = f g) :
    oneCoboundaries A :=
  oneCoboundariesOfMemRange f ⟨x, by ext g; exact hf g⟩

theorem oneCoboundariesOfEq_apply (f : G → A) (x : A) {hf : ∀ g, A.ρ g x - x = f g} :
    (oneCoboundariesOfEq f x hf).1.1 = f := rfl

theorem mem_range_of_mem_oneCoboundaries (f : oneCocycles A) (h : f ∈ oneCoboundaries A) :
    f.1 ∈ LinearMap.range (dZero A) := by
  rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩

theorem oneCoboundaries_eq_bot_of_isTrivial (A : Rep k G) [A.IsTrivial] :
    oneCoboundaries A = ⊥ := by
  simp_rw [oneCoboundaries, dZero_eq_zero]
  exact LinearMap.range_eq_bot.2 rfl

/-- Makes a 2-coboundary out of `f ∈ Im(d¹)`. -/
def twoCoboundariesOfMemRange (f : G × G → A) (h : f ∈ LinearMap.range (dOne A)) :
    twoCoboundaries A :=
  ⟨⟨f, LinearMap.range_le_ker_iff.2 (dTwo_comp_dOne A) h⟩,
    by rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩⟩

theorem twoCoboundariesOfMemRange_apply (f : G × G → A) {h : f ∈ LinearMap.range (dOne A)} :
    (twoCoboundariesOfMemRange f h).1.1 = f := rfl

/-- Makes a 2-coboundary out of `f : G × G → A` and `x : G → A` such that
`ρ(g)(x(h)) - x(gh) + x(g) = f(g, h)` for all `g, h : G`. -/
def twoCoboundariesOfEq (f : G × G → A) (x : G → A)
    (hf : ∀ g h, A.ρ g (x h) - x (g * h) + x g = f (g, h)) :
    twoCoboundaries A :=
  twoCoboundariesOfMemRange f ⟨x, by ext g; exact hf g.1 g.2⟩

theorem twoCoboundariesOfEq_apply (f : G × G  → A) (x : G → A)
    {hf : ∀ g h, A.ρ g (x h) - x (g * h) + x g = f (g, h)} :
    (twoCoboundariesOfEq f x hf).1.1 = f := rfl

theorem mem_range_of_mem_twoCoboundaries (f : twoCocycles A) (h : f ∈ twoCoboundaries A) :
    (twoCocycles A).subtype f ∈ LinearMap.range (dOne A) := by
  rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩

end Coboundaries
section ofDistribMulAction
section
variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A] (n : ℕ)

/-- A function `f : G → A` satisfies the 1-cocycle condition if
`f(gh) = g • f(h) + f(g)` for all `g, h : G`. -/
def IsOneCocycle (f : G → A) : Prop := ∀ g h : G, f (g * h) = g • f h + f g

/-- A function `f : G → A` satisfies the 1-coboundary condition if there's `x : A` such that
`g • x - x = f(g)` for all `g : G`. -/
def IsOneCoboundary (f : G → A) : Prop := ∃ x : A, ∀ g : G, g • x - x = f g

/-- A function `f : G × G → A` satisfies the 2-cocycle condition if
`f(gh, j) + f(g, h) = g • f(h, j) + f(g, hj)` for all `g, h : G`. -/
def IsTwoCocycle (f : G × G → A) : Prop :=
  ∀ g h j : G, f (g * h, j) + f (g, h) = g • (f (h, j)) + f (g, h * j)

/-- A function `f : G × G → A` satisfies the 2-coboundary condition if there's `x : G → A` such
that `g • x(h) - x(gh) + x(g) = f(g, h)` for all `g, h : G`. -/
def IsTwoCoboundary (f : G × G → A) : Prop :=
  ∃ x : G → A, ∀ g h : G, g • x h - x (g * h) + x g = f (g, h)

end
section

variable {k G A : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G → A` satisfying the 1-cocycle condition, produces a 1-cocycle for the representation on
`A` induced by the `DistribMulAction`. -/
def oneCocyclesOfIsOneCocycle (f : G → A) (hf : IsOneCocycle f) :
    oneCocycles (Rep.ofDistribMulAction k G A) :=
  ⟨f, (mem_oneCocycles_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

theorem isOneCocycle_of_oneCocycles (f : oneCocycles (Rep.ofDistribMulAction k G A)) :
    IsOneCocycle (A := A) f.1 := (mem_oneCocycles_iff f.1).1 f.2

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G → A` satisfying the 1-coboundary condition, produces a 1-coboundary for the representation
on `A` induced by the `DistribMulAction`. -/
def oneCoboundariesOfIsOneCoboundary (f : G → A) (hf : IsOneCoboundary f) :
    oneCoboundaries (Rep.ofDistribMulAction k G A) :=
  oneCoboundariesOfMemRange f (by rcases hf with ⟨x, hx⟩; exact ⟨x, by ext g; exact hx g⟩)

theorem isOneCoboundary_of_oneCoboundaries (f : oneCoboundaries (Rep.ofDistribMulAction k G A)) :
    IsOneCoboundary (A := A) f.1.1 := by
  rcases mem_range_of_mem_oneCoboundaries f.1 f.2 with ⟨x, hx⟩
  exact ⟨x, by rw [← hx]; intro g; rfl⟩

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G × G → A` satisfying the 2-cocycle condition, produces a 2-cocycle for the representation on
`A` induced by the `DistribMulAction`. -/
def twoCocyclesOfIsTwoCocycle (f : G × G → A) (hf : IsTwoCocycle f) :
    twoCocycles (Rep.ofDistribMulAction k G A) :=
  ⟨f, (mem_twoCocycles_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

theorem isTwoCocycle_of_twoCocycles (f : twoCocycles (Rep.ofDistribMulAction k G A)) :
    IsTwoCocycle (A := A) f.1 := (mem_twoCocycles_iff f.1).1 f.2

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G × G → A` satisfying the 2-coboundary condition, produces a 2-coboundary for the
representation on `A` induced by the `DistribMulAction`. -/
def twoCoboundariesOfIsTwoCoboundary (f : G × G → A) (hf : IsTwoCoboundary f) :
    twoCoboundaries (Rep.ofDistribMulAction k G A) :=
  twoCoboundariesOfMemRange f (by rcases hf with ⟨x, hx⟩; exact ⟨x, by ext g; exact hx g.1 g.2⟩)

theorem isTwoCoboundary_of_twoCoboundaries (f : twoCoboundaries (Rep.ofDistribMulAction k G A)) :
    IsTwoCoboundary (A := A) f.1.1 := by
  rcases mem_range_of_mem_twoCoboundaries f.1 f.2 with ⟨x, hx⟩
  exact ⟨x, fun g h => Function.funext_iff.1 hx (g, h)⟩

end
end ofDistribMulAction
section ofMulDistribMulAction
section
variable {G M : Type*} [Mul G] [Group M] [SMul G M] (n : ℕ)

/-- A function `f : G → A` satisfies the multiplicative 1-cocycle condition if
`f(gh) = g • f(h) * f(g)` for all `g, h : G`. -/
def IsMulOneCocycle (f : G → M) : Prop := ∀ g h : G, f (g * h) = g • f h * f g

/-- A function `f : G → A` satisfies the multiplicative 1-coboundary condition if there's `x : A`
such that `g • x / x = f(g)` for all `g : G`. -/
def IsMulOneCoboundary (f : G → M) : Prop := ∃ x : M, ∀ g : G, g • x / x = f g

/-- A function `f : G × G → A` satisfies the multiplicative 2-cocycle condition if
`f(gh, j) * f(g, h) = g • f(h, j) * f(g, hj)` for all `g, h : G`. -/
def IsMulTwoCocycle (f : G × G → M) : Prop :=
  ∀ g h j : G, f (g * h, j) * f (g, h) = g • (f (h, j)) * f (g, h * j)

/-- A function `f : G × G → A` satisfies the multiplicative 2-coboundary condition if there's
`x : G → A` such that `g • x(h) / x(gh) * x(g) = f(g, h)` for all `g, h : G`. -/
def IsMulTwoCoboundary (f : G × G → M) : Prop :=
  ∃ x : G → M, ∀ g h : G, g • x h / x (g * h) * x g = f (g, h)

end
section
variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G → M` satisfying the multiplicative 1-cocycle condition, produces a 1-cocycle for the
representation on `Additive M` induced by the `MulDistribMulAction`. -/
def oneCocyclesOfIsMulOneCocycle (f : G → M) (hf : IsMulOneCocycle f) :
    oneCocycles (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_oneCocycles_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

theorem isMulOneCocycle_of_oneCocycles (f : oneCocycles (Rep.ofMulDistribMulAction G M)) :
    IsMulOneCocycle (M := M) (Additive.toMul ∘ f.1) := (mem_oneCocycles_iff f.1).1 f.2

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G → M` satisfying the multiplicative 1-coboundary condition, produces a
1-coboundary for the representation on `Additive M` induced by the `MulDistribMulAction`. -/
def oneCoboundariesOfIsMulOneCoboundary (f : G → M) (hf : IsMulOneCoboundary f) :
    oneCoboundaries (Rep.ofMulDistribMulAction G M) :=
  oneCoboundariesOfMemRange (Additive.ofMul ∘ f)
    (by rcases hf with ⟨x, hx⟩; exact ⟨x, by ext g; exact hx g⟩)

theorem isMulOneCoboundary_of_oneCoboundaries
    (f : oneCoboundaries (Rep.ofMulDistribMulAction G M)) :
    IsMulOneCoboundary (M := M) (Additive.ofMul ∘ f.1.1) := by
  rcases mem_range_of_mem_oneCoboundaries f.1 f.2 with ⟨x, hx⟩
  exact ⟨x, by rw [← hx]; intro g; rfl⟩

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G × G → M` satisfying the multiplicative 2-cocycle condition, produces a 2-cocycle for the
representation on `Additive M` induced by the `MulDistribMulAction`. -/
def twoCocyclesOfIsMulTwoCocycle (f : G × G → M) (hf : IsMulTwoCocycle f) :
    twoCocycles (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_twoCocycles_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

theorem isMulTwoCocycle_of_twoCocycles (f : twoCocycles (Rep.ofMulDistribMulAction G M)) :
    IsMulTwoCocycle (M := M) (Additive.toMul ∘ f.1) := (mem_twoCocycles_iff f.1).1 f.2

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G × G → M` satisfying the multiplicative 2-coboundary condition, produces a
2-coboundary for the representation on `M` induced by the `MulDistribMulAction`. -/
def twoCoboundariesOfIsMulTwoCoboundary (f : G × G → M) (hf : IsMulTwoCoboundary f) :
    twoCoboundaries (Rep.ofMulDistribMulAction G M) :=
  twoCoboundariesOfMemRange f (by rcases hf with ⟨x, hx⟩; exact ⟨x, by ext g; exact hx g.1 g.2⟩)

theorem isMulTwoCoboundary_of_twoCoboundaries
    (f : twoCoboundaries (Rep.ofMulDistribMulAction G M)) :
    IsMulTwoCoboundary (M := M) (Additive.toMul ∘ f.1.1) := by
  rcases mem_range_of_mem_twoCoboundaries f.1 f.2 with ⟨x, hx⟩
  exact ⟨x, fun g h => Function.funext_iff.1 hx (g, h)⟩

end
end ofMulDistribMulAction
section Cohomology

/-- We define the 0th group cohomology of a `k`-linear `G`-representation `A`, `H⁰(G, A)`, to be
the invariants of the representation, `Aᴳ`. -/
abbrev H0 := A.ρ.invariants

/-- We define the 1st group cohomology of a `k`-linear `G`-representation `A`, `H¹(G, A)`, to be
1-cocycles (i.e. `Z¹(G, A) := Ker(d¹ : Fun(G, A) → Fun(G², A)`) modulo 1-coboundaries
(i.e. `B¹(G, A) := Im(d⁰: A → Fun(G, A))`). -/
abbrev H1 := oneCocycles A ⧸ oneCoboundaries A

/-- The quotient map `Z¹(G, A) → H¹(G, A).` -/
def H1_π : oneCocycles A →ₗ[k] H1 A := (oneCoboundaries A).mkQ

/-- We define the 2nd group cohomology of a `k`-linear `G`-representation `A`, `H²(G, A)`, to be
2-cocycles (i.e. `Z²(G, A) := Ker(d² : Fun(G², A) → Fun(G³, A)`) modulo 2-coboundaries
(i.e. `B²(G, A) := Im(d¹: Fun(G, A) → Fun(G², A))`). -/
abbrev H2 := twoCocycles A ⧸ twoCoboundaries A

/-- The quotient map `Z²(G, A) → H²(G, A).` -/
def H2_π : twoCocycles A →ₗ[k] H2 A := (twoCoboundaries A).mkQ

end Cohomology
section H0

/-- When the representation on `A` is trivial, then `H⁰(G, A)` is all of `A.` -/
def H0LequivOfIsTrivial [A.IsTrivial] :
    H0 A ≃ₗ[k] A := LinearEquiv.ofTop _ (invariants_eq_top A.ρ)

@[simp] theorem H0LequivOfIsTrivial_eq_subtype [A.IsTrivial] :
    H0LequivOfIsTrivial A = A.ρ.invariants.subtype := rfl

theorem H0LequivOfIsTrivial_apply [A.IsTrivial] (x : H0 A) :
    H0LequivOfIsTrivial A x = x := rfl

@[simp] theorem H0LequivOfIsTrivial_symm_apply [A.IsTrivial] (x : A) :
    (H0LequivOfIsTrivial A).symm x = x := rfl

end H0
section H1

/-- When `A : Rep k G` is a trivial representation of `G`, `H¹(G, A)` is isomorphic to the
group homs `G → A`. -/
def H1LequivOfIsTrivial [A.IsTrivial] :
    H1 A ≃ₗ[k] Additive G →+ A :=
  (Submodule.quotEquivOfEqBot _ (oneCoboundaries_eq_bot_of_isTrivial A)).trans
    (oneCocyclesLequivOfIsTrivial A)

theorem H1LequivOfIsTrivial_comp_H1_π [A.IsTrivial] :
    (H1LequivOfIsTrivial A).comp (H1_π A) = oneCocyclesLequivOfIsTrivial A := by
  ext; rfl

@[simp] theorem H1LequivOfIsTrivial_H1_π_apply_apply
    [A.IsTrivial] (f : oneCocycles A) (x : Additive G) :
    H1LequivOfIsTrivial A (H1_π A f) x = f.1 (Additive.toMul x) := rfl

@[simp] theorem H1LequivOfIsTrivial_symm_apply [A.IsTrivial] (f : Additive G →+ A) :
    (H1LequivOfIsTrivial A).symm f = H1_π A ((oneCocyclesLequivOfIsTrivial A).symm f) :=
  rfl

end H1
end groupCohomology
