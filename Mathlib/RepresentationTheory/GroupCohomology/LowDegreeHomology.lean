/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Joël Riou

-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RepresentationTheory.GroupCohomology.blehfgh
import Mathlib.RepresentationTheory.Invariants


universe v u

noncomputable section

open CategoryTheory Limits Representation Rep

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

namespace groupHomology

section Chains
variable [DecidableEq G]
/-- The 0th object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `A` as a `k`-module. -/
def zeroChainsLEquiv : (inhomogeneousChains A).X 0 ≃ₗ[k] A :=
  Finsupp.LinearEquiv.finsuppUnique _ _ _

/-- The 1st object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G, A)` as a `k`-module. -/
def oneChainsLEquiv : (inhomogeneousChains A).X 1 ≃ₗ[k] G →₀ A :=
  Finsupp.domLCongr (Equiv.funUnique (Fin 1) G)

/-- The 2nd object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G², A)` as a `k`-module. -/
def twoChainsLEquiv : (inhomogeneousChains A).X 2 ≃ₗ[k] G × G →₀ A :=
  Finsupp.domLCongr (piFinTwoEquiv fun _ => G)

/-- The 3rd object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G³, A)` as a `k`-module. -/
def threeChainsLEquiv : (inhomogeneousChains A).X 3 ≃ₗ[k] G × G × G →₀ A :=
  Finsupp.domLCongr ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))

end Chains

section Differentials

/-- The 0th differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `A → Fun(G, A)`. It sends `(a, g) ↦ ρ_A(g)(a) - a.` -/
abbrev dZero : (G →₀ A) →ₗ[k] A :=
  Finsupp.lsum k fun g => A.ρ g⁻¹ - LinearMap.id

theorem dZero_range_eq_coinvariantsKer [DecidableEq G] :
    LinearMap.range (dZero A) = coinvariantsKer A.ρ := by
  symm
  apply Submodule.span_eq_of_le
  · rintro _ ⟨x, rfl⟩
    use Finsupp.single x.1⁻¹ x.2
    simp
  · rintro x ⟨y, hy⟩
    induction' y using Finsupp.induction with g a s _ _ h generalizing x
    · simp [← hy]
    · dsimp at *
      rw [Finsupp.sum_add_index (by simp) (by intros; simp [add_sub_add_comm]),
        Finsupp.sum_single_index (by simp)] at hy
      rw [← hy]
      exact Submodule.add_mem _ (mem_coinvariantsKer _ _ _ _ rfl) (h rfl)

@[simp]
theorem dZero_eq_zero [A.IsTrivial] : dZero A = 0 := by
  ext
  simp

/-- The 1st differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G, A) → Fun(G × G, A)`. It sends
`(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
abbrev dOne : (G × G →₀ A) →ₗ[k] G →₀ A :=
  Finsupp.lsum k fun g => Finsupp.lsingle g.2 ∘ₗ A.ρ g.1⁻¹
    - Finsupp.lsingle (g.1 * g.2) + Finsupp.lsingle g.1

/-- The 2nd differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G × G, A) → Fun(G × G × G, A)`. It sends
`(f, (g₁, g₂, g₃)) ↦ ρ_A(g₁)(f(g₂, g₃)) - f(g₁g₂, g₃) + f(g₁, g₂g₃) - f(g₁, g₂).` -/
abbrev dTwo : (G × G × G →₀ A) →ₗ[k] G × G →₀ A :=
  Finsupp.lsum k fun g =>
    Finsupp.lsingle (g.2.1, g.2.2) ∘ₗ A.ρ g.1⁻¹ - Finsupp.lsingle (g.1 * g.2.1, g.2.2)
    + Finsupp.lsingle (g.1, g.2.1 * g.2.2) - Finsupp.lsingle (g.1, g.2.1)

@[simp]
theorem _root_.Fin.contractNth_zero {α : Type*} (op : α → α → α)
    (g : Fin 1 → α) (j : Fin 1) :
    Fin.contractNth j op g = g ∘ Fin.castSucc := by
  ext i
  exact Fin.elim0 i

@[simp]
theorem _root_.Fin.contractNth_one_zero {α : Type*} (op : α → α → α)
    (g : Fin 2 → α) :
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


/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `dZero` gives a simpler expression for the 0th differential: that is, the following
square commutes:
```
  C₁(G, A) ---d₀---> C₀(G, A)
  |                    |
  |                    |
  |                    |
  v                    v
  (G →₀ A) --dZero --> A
```
where the vertical arrows are `zeroChainsLEquiv` and `oneChainsLEquiv` respectively.
-/
theorem dZero_comp_eq [DecidableEq G] :
    zeroChainsLEquiv A ∘ₗ (inhomogeneousChains A).d 1 0
      = dZero A ∘ₗ oneChainsLEquiv A := by
  apply Finsupp.lhom_ext
  intro f a
  have := A.d_apply 0 (Finsupp.single f a)
  simp_all only [ChainComplex.of_x, ModuleCat.coe_of, inhomogeneousChains.d_def,
    LinearMap.coe_comp, Function.comp_apply, Finsupp.LinearEquiv.finsuppUnique_apply]
  rw [Finsupp.sum_single_index]
  · simp [zeroChainsLEquiv, Unique.eq_default (α := Fin 0 → G),
      oneChainsLEquiv, sub_eq_add_neg]
  · simp

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
where the vertical arrows are `oneChainsLEquiv` and `twoChainsLEquiv` respectively.
-/
theorem dOne_comp_eq [DecidableEq G] :
    oneChainsLEquiv A ∘ₗ (inhomogeneousChains A).d 2 1
      = dOne A ∘ₗ twoChainsLEquiv A := by
  apply Finsupp.lhom_ext
  intro f a
  have := A.d_apply 1 (Finsupp.single f a)
  simp_all only [ChainComplex.of_x, ModuleCat.coe_of, inhomogeneousChains.d_def,
    LinearMap.coe_comp, Function.comp_apply, Finsupp.LinearEquiv.finsuppUnique_apply]
  rw [Finsupp.sum_single_index]
  · simp [oneChainsLEquiv, map_add, map_neg, twoChainsLEquiv, sub_eq_add_neg, add_assoc,
      Fin.contractNth_last _ (show 1 = Fin.last 1 by ext; rfl)]
  · simp

lemma ffs {α : Type*} [AddCommSemigroup α] (a b c : α) : a + b + c = c + b + a := by
  rw [add_rotate, add_comm b]

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
where the vertical arrows are `twoChainsLEquiv` and `threeChainsLEquiv` respectively.
-/
theorem dTwo_comp_eq [DecidableEq G] :
    twoChainsLEquiv A ∘ₗ (inhomogeneousChains A).d 3 2
      = dTwo A ∘ₗ threeChainsLEquiv A := by
  apply Finsupp.lhom_ext
  intro f a
  have := A.d_apply 2 (Finsupp.single f a)
  simp_all only [ChainComplex.of_x, ModuleCat.coe_of, inhomogeneousChains.d_def,
    LinearMap.coe_comp, Function.comp_apply, Finsupp.LinearEquiv.finsuppUnique_apply]
  rw [Finsupp.sum_single_index, dTwo]
  · simpa [twoChainsLEquiv, map_add, map_neg, threeChainsLEquiv, Fin.sum_univ_three,
    Fin.contractNth_last _ (show 2 = Fin.last 2 by ext; rfl), sub_eq_add_neg,
    add_assoc, pow_succ, Fin.tail_def, Fin.contractNth] using ffs _ _ _
  · simp

theorem dZero_comp_dOne [DecidableEq G] : dZero A ∘ₗ dOne A = 0 := by
  ext x g
  dsimp
  simp only [map_zero, Finsupp.sum_single_index]
  show (Finsupp.single x.2 (A.ρ x.1⁻¹ g) - Finsupp.single (x.1 * x.2) g
    + Finsupp.single x.1 g).sum _ = 0
  rw [Finsupp.sum_add_index, Finsupp.sum_sub_index]
  <;> simp [sub_sub_sub_comm, add_sub_add_comm]

open Finsupp
theorem dOne_comp_dTwo [DecidableEq G] : dOne A ∘ₗ dTwo A = 0 := by
  show ModuleCat.ofHom (dTwo A) ≫ ModuleCat.ofHom (dOne A) = _
  have h1 : _ ≫ _ = _ ≫ ModuleCat.ofHom (dOne A) := congr(ModuleCat.ofHom $(dOne_comp_eq A))
  have h2 : _ ≫ _ = _ ≫ ModuleCat.ofHom (dTwo A) := congr(ModuleCat.ofHom $(dTwo_comp_eq A))
  simp only [← LinearEquiv.toModuleIso_hom] at h1 h2
  simp only [(Iso.eq_inv_comp _).2 h2.symm, (Iso.eq_inv_comp _).2 h1.symm,
    Category.assoc, Iso.hom_inv_id_assoc, HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]

end Differentials

section Cycles

/-- The 1-cocycles `Z¹(G, A)` of `A : Rep k G`, defined as the kernel of the map
`Fun(G, A) → Fun(G × G, A)` sending `(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
def oneCycles : Submodule k (G →₀ A) := LinearMap.ker (dZero A)

/-- The 2-cocycles `Z²(G, A)` of `A : Rep k G`, defined as the kernel of the map
`Fun(G × G, A) → Fun(G × G × G, A)` sending
`(f, (g₁, g₂, g₃)) ↦ ρ_A(g₁)(f(g₂, g₃)) - f(g₁g₂, g₃) + f(g₁, g₂g₃) - f(g₁, g₂).` -/
def twoCycles : Submodule k (G × G →₀ A) := LinearMap.ker (dOne A)

variable {A}

#exit

theorem mem_oneCycles_def (f : G →₀ A) :
    f ∈ oneCycles A ↔ ∀ g : G, f.sum (fun g a => A.ρ g⁻¹ a - a) = 0 :=
  LinearMap.mem_ker.trans <| by
    sorry

theorem mem_oneCycles_iff (f : G →₀ A) :
    f ∈ oneCycles A ↔ ∀ g : G, f.sum (fun g a => A.ρ g⁻¹ a) = f.sum (fun g a => a) := by
  sorry
/-
@[simp] theorem oneCycles_map_one (f : oneCycles A) : f.1 1 = 0 := by
  have := (mem_oneCycles_def f.1).1 f.2 1
  simpa only [map_one, LinearMap.one_apply, mul_one, sub_self, zero_add] using this

@[simp] theorem oneCycles_map_inv (f : oneCycles A) (g : G) :
    A.ρ g (f.1 g⁻¹) = - f.1 g := by
  rw [← add_eq_zero_iff_eq_neg, ← oneCycles_map_one f, ← mul_inv_cancel g,
    (mem_oneCycles_iff f.1).1 f.2 g g⁻¹]

theorem oneCycles_map_mul_of_isTrivial [A.IsTrivial] (f : oneCycles A) (g h : G) :
    f.1 (g * h) = f.1 g + f.1 h := by
  rw [(mem_oneCycles_iff f.1).1 f.2, apply_eq_self A.ρ g (f.1 h), add_comm]

theorem mem_oneCycles_of_addMonoidHom [A.IsTrivial] (f : Additive G →+ A) :
    f ∘ Additive.ofMul ∈ oneCycles A :=
  (mem_oneCycles_iff _).2 fun g h => by
    simp only [Function.comp_apply, ofMul_mul, map_add,
      oneCycles_map_mul_of_isTrivial, apply_eq_self A.ρ g (f (Additive.ofMul h)),
      add_comm (f (Additive.ofMul g))]

variable (A)

/-- When `A : Rep k G` is a trivial representation of `G`, `Z¹(G, A)` is isomorphic to the
group homs `G → A`. -/
@[simps] def oneCyclesLEquivOfIsTrivial [hA : A.IsTrivial] :
    oneCycles A ≃ₗ[k] Additive G →+ A where
  toFun f :=
    { toFun := f.1 ∘ Additive.toMul
      map_zero' := oneCycles_map_one f
      map_add' := oneCycles_map_mul_of_isTrivial f }
  map_add' x y := rfl
  map_smul' r x := rfl
  invFun f :=
    { val := f
      property := mem_oneCycles_of_addMonoidHom f }
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl

variable {A}

theorem mem_twoCycles_def (f : G × G → A) :
    f ∈ twoCycles A ↔ ∀ g h j : G,
      A.ρ g (f (h, j)) - f (g * h, j) + f (g, h * j) - f (g, h) = 0 :=
  LinearMap.mem_ker.trans <| by
    rw [Function.funext_iff]
    simp only [dTwo_apply, Prod.mk.eta, Pi.zero_apply, Prod.forall]

theorem mem_twoCycles_iff (f : G × G → A) :
    f ∈ twoCycles A ↔ ∀ g h j : G,
      f (g * h, j) + f (g, h) =
        A.ρ g (f (h, j)) + f (g, h * j) := by
  simp_rw [mem_twoCycles_def, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add, eq_comm,
    add_comm (f (_ * _, _))]

theorem twoCycles_map_one_fst (f : twoCycles A) (g : G) :
    f.1 (1, g) = f.1 (1, 1) := by
  have := ((mem_twoCycles_iff f.1).1 f.2 1 1 g).symm
  simpa only [map_one, LinearMap.one_apply, one_mul, add_right_inj, this]

theorem twoCycles_map_one_snd (f : twoCycles A) (g : G) :
    f.1 (g, 1) = A.ρ g (f.1 (1, 1)) := by
  have := (mem_twoCycles_iff f.1).1 f.2 g 1 1
  simpa only [mul_one, add_left_inj, this]

lemma twoCycles_ρ_map_inv_sub_map_inv (f : twoCycles A) (g : G) :
    A.ρ g (f.1 (g⁻¹, g)) - f.1 (g, g⁻¹)
      = f.1 (1, 1) - f.1 (g, 1) := by
  have := (mem_twoCycles_iff f.1).1 f.2 g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, twoCycles_map_one_fst _ g]
    at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm
-/
end Cycles

section Boundaries

/-- The 1-coboundaries `B¹(G, A)` of `A : Rep k G`, defined as the image of the map
`A → Fun(G, A)` sending `(a, g) ↦ ρ_A(g)(a) - a.` -/
def oneBoundaries [DecidableEq G] : Submodule k (oneCycles A) :=
  LinearMap.range ((dOne A).codRestrict (oneCycles A) fun c =>
    LinearMap.ext_iff.1 (dZero_comp_dOne A) c)

/-- The 2-coboundaries `B²(G, A)` of `A : Rep k G`, defined as the image of the map
`Fun(G, A) → Fun(G × G, A)` sending `(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
def twoBoundaries [DecidableEq G] : Submodule k (twoCycles A) :=
  LinearMap.range ((dTwo A).codRestrict (twoCycles A) fun c =>
    LinearMap.ext_iff.1 (dOne_comp_dTwo.{u} A) c)

variable {A}
/-
/-- Makes a 1-coboundary out of `f ∈ Im(d⁰)`. -/
def oneBoundariesOfMemRange {f : G → A} (h : f ∈ LinearMap.range (dZero A)) :
    oneBoundaries A :=
  ⟨⟨f, LinearMap.range_le_ker_iff.2 (dOne_comp_dZero A) h⟩,
    by rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩⟩

theorem oneBoundaries_of_mem_range_apply {f : G → A} (h : f ∈ LinearMap.range (dZero A)) :
    (oneBoundariesOfMemRange h).1.1 = f := rfl

/-- Makes a 1-coboundary out of `f : G → A` and `x` such that
`ρ(g)(x) - x = f(g)` for all `g : G`. -/
def oneBoundariesOfEq {f : G → A} {x : A} (hf : ∀ g, A.ρ g x - x = f g) :
    oneBoundaries A :=
  oneBoundariesOfMemRange ⟨x, funext hf⟩

theorem oneBoundariesOfEq_apply {f : G → A} {x : A} (hf : ∀ g, A.ρ g x - x = f g) :
    (oneBoundariesOfEq hf).1.1 = f := rfl

theorem mem_range_of_mem_oneBoundaries {f : oneCycles A} (h : f ∈ oneBoundaries A) :
    f.1 ∈ LinearMap.range (dZero A) := by
  rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩

theorem oneBoundaries_eq_bot_of_isTrivial (A : Rep k G) [A.IsTrivial] :
    oneBoundaries A = ⊥ := by
  simp_rw [oneBoundaries, dZero_eq_zero]
  exact LinearMap.range_eq_bot.2 rfl

/-- Makes a 2-coboundary out of `f ∈ Im(d¹)`. -/
def twoBoundariesOfMemRange {f : G × G → A} (h : f ∈ LinearMap.range (dOne A)) :
    twoBoundaries A :=
  ⟨⟨f, LinearMap.range_le_ker_iff.2 (dTwo_comp_dOne A) h⟩,
    by rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩⟩

theorem twoBoundariesOfMemRange_apply {f : G × G → A} (h : f ∈ LinearMap.range (dOne A)) :
    (twoBoundariesOfMemRange h).1.1 = f := rfl

/-- Makes a 2-coboundary out of `f : G × G → A` and `x : G → A` such that
`ρ(g)(x(h)) - x(gh) + x(g) = f(g, h)` for all `g, h : G`. -/
def twoBoundariesOfEq {f : G × G → A} {x : G → A}
    (hf : ∀ g h, A.ρ g (x h) - x (g * h) + x g = f (g, h)) :
    twoBoundaries A :=
  twoBoundariesOfMemRange ⟨x, funext fun g ↦ hf g.1 g.2⟩

theorem twoBoundariesOfEq_apply {f : G × G → A} {x : G → A}
    (hf : ∀ g h, A.ρ g (x h) - x (g * h) + x g = f (g, h)) :
    (twoBoundariesOfEq hf).1.1 = f := rfl

theorem mem_range_of_mem_twoBoundaries {f : twoCycles A} (h : f ∈ twoBoundaries A) :
    (twoCycles A).subtype f ∈ LinearMap.range (dOne A) := by
  rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩
-/
end Boundaries

section IsCycle

section

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/-- A function `f : G → A` satisfies the 1-cocycle condition if
`f(gh) = g • f(h) + f(g)` for all `g, h : G`. -/
def IsOneCycle (f : G → A) : Prop := ∀ g h : G, f (g * h) = g • f h + f g

/-- A function `f : G × G → A` satisfies the 2-cocycle condition if
`f(gh, j) + f(g, h) = g • f(h, j) + f(g, hj)` for all `g, h : G`. -/
def IsTwoCycle (f : G × G → A) : Prop :=
  ∀ g h j : G, f (g * h, j) + f (g, h) = g • (f (h, j)) + f (g, h * j)

end

section

variable {G A : Type*} [Monoid G] [AddCommGroup A] [MulAction G A]

theorem map_one_of_isOneCycle {f : G → A} (hf : IsOneCycle f) :
    f 1 = 0 := by
  simpa only [mul_one, one_smul, self_eq_add_right] using hf 1 1

theorem map_one_fst_of_isTwoCycle {f : G × G → A} (hf : IsTwoCycle f) (g : G) :
    f (1, g) = f (1, 1) := by
  simpa only [one_smul, one_mul, mul_one, add_right_inj] using (hf 1 1 g).symm

theorem map_one_snd_of_isTwoCycle {f : G × G → A} (hf : IsTwoCycle f) (g : G) :
    f (g, 1) = g • f (1, 1) := by
  simpa only [mul_one, add_left_inj] using hf g 1 1

end

section

variable {G A : Type*} [Group G] [AddCommGroup A] [MulAction G A]

@[scoped simp] theorem map_inv_of_isOneCycle {f : G → A} (hf : IsOneCycle f) (g : G) :
    g • f g⁻¹ = - f g := by
  rw [← add_eq_zero_iff_eq_neg, ← map_one_of_isOneCycle hf, ← mul_inv_cancel g, hf g g⁻¹]

theorem smul_map_inv_sub_map_inv_of_isTwoCycle {f : G × G → A} (hf : IsTwoCycle f) (g : G) :
    g • f (g⁻¹, g) - f (g, g⁻¹) = f (1, 1) - f (g, 1) := by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isTwoCycle hf g] at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

end

end IsCycle

section IsBoundary

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/-- A function `f : G → A` satisfies the 1-coboundary condition if there's `x : A` such that
`g • x - x = f(g)` for all `g : G`. -/
def IsOneBoundary (f : G → A) : Prop := ∃ x : A, ∀ g : G, g • x - x = f g

/-- A function `f : G × G → A` satisfies the 2-coboundary condition if there's `x : G → A` such
that `g • x(h) - x(gh) + x(g) = f(g, h)` for all `g, h : G`. -/
def IsTwoBoundary (f : G × G → A) : Prop :=
  ∃ x : G → A, ∀ g h : G, g • x h - x (g * h) + x g = f (g, h)

end IsBoundary

section ofDistribMulAction

variable {k G A : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]
/-
/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G → A` satisfying the 1-cocycle condition, produces a 1-cocycle for the representation on
`A` induced by the `DistribMulAction`. -/
def oneCyclesOfIsOneCycle {f : G → A} (hf : IsOneCycle f) :
    oneCycles (Rep.ofDistribMulAction k G A) :=
  ⟨f, (mem_oneCycles_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

theorem isOneCycle_of_oneCycles (f : oneCycles (Rep.ofDistribMulAction k G A)) :
    IsOneCycle (A := A) f.1 := (mem_oneCycles_iff f.1).1 f.2

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G → A` satisfying the 1-coboundary condition, produces a 1-coboundary for the representation
on `A` induced by the `DistribMulAction`. -/
def oneBoundariesOfIsOneBoundary {f : G → A} (hf : IsOneBoundary f) :
    oneBoundaries (Rep.ofDistribMulAction k G A) :=
  oneBoundariesOfMemRange ⟨hf.choose, funext hf.choose_spec⟩

theorem isOneBoundary_of_oneBoundaries (f : oneBoundaries (Rep.ofDistribMulAction k G A)) :
    IsOneBoundary (A := A) f.1.1 := by
  rcases mem_range_of_mem_oneBoundaries f.2 with ⟨x, hx⟩
  exact ⟨x, by rw [← hx]; intro g; rfl⟩

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G × G → A` satisfying the 2-cocycle condition, produces a 2-cocycle for the representation on
`A` induced by the `DistribMulAction`. -/
def twoCyclesOfIsTwoCycle {f : G × G → A} (hf : IsTwoCycle f) :
    twoCycles (Rep.ofDistribMulAction k G A) :=
  ⟨f, (mem_twoCycles_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

theorem isTwoCycle_of_twoCycles (f : twoCycles (Rep.ofDistribMulAction k G A)) :
    IsTwoCycle (A := A) f.1 := (mem_twoCycles_iff f.1).1 f.2

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G × G → A` satisfying the 2-coboundary condition, produces a 2-coboundary for the
representation on `A` induced by the `DistribMulAction`. -/
def twoBoundariesOfIsTwoBoundary {f : G × G → A} (hf : IsTwoBoundary f) :
    twoBoundaries (Rep.ofDistribMulAction k G A) :=
  twoBoundariesOfMemRange (⟨hf.choose,funext fun g ↦ hf.choose_spec g.1 g.2⟩)

theorem isTwoBoundary_of_twoBoundaries (f : twoBoundaries (Rep.ofDistribMulAction k G A)) :
    IsTwoBoundary (A := A) f.1.1 := by
  rcases mem_range_of_mem_twoBoundaries f.2 with ⟨x, hx⟩
  exact ⟨x, fun g h => Function.funext_iff.1 hx (g, h)⟩
-/
end ofDistribMulAction

/-! The next few sections, until the section `Homology`, are a multiplicative copy of the
previous few sections beginning with `IsCycle`. Unfortunately `@[to_additive]` doesn't work with
scalar actions. -/

section IsMulCycle

section

variable {G M : Type*} [Mul G] [CommGroup M] [SMul G M]

/-- A function `f : G → M` satisfies the multiplicative 1-cocycle condition if
`f(gh) = g • f(h) * f(g)` for all `g, h : G`. -/
def IsMulOneCycle (f : G → M) : Prop := ∀ g h : G, f (g * h) = g • f h * f g

/-- A function `f : G × G → M` satisfies the multiplicative 2-cocycle condition if
`f(gh, j) * f(g, h) = g • f(h, j) * f(g, hj)` for all `g, h : G`. -/
def IsMulTwoCycle (f : G × G → M) : Prop :=
  ∀ g h j : G, f (g * h, j) * f (g, h) = g • (f (h, j)) * f (g, h * j)

end

section

variable {G M : Type*} [Monoid G] [CommGroup M] [MulAction G M]

theorem map_one_of_isMulOneCycle {f : G → M} (hf : IsMulOneCycle f) :
    f 1 = 1 := by
  simpa only [mul_one, one_smul, self_eq_mul_right] using hf 1 1

theorem map_one_fst_of_isMulTwoCycle {f : G × G → M} (hf : IsMulTwoCycle f) (g : G) :
    f (1, g) = f (1, 1) := by
  simpa only [one_smul, one_mul, mul_one, mul_right_inj] using (hf 1 1 g).symm

theorem map_one_snd_of_isMulTwoCycle {f : G × G → M} (hf : IsMulTwoCycle f) (g : G) :
    f (g, 1) = g • f (1, 1) := by
  simpa only [mul_one, mul_left_inj] using hf g 1 1

end

section

variable {G M : Type*} [Group G] [CommGroup M] [MulAction G M]

@[scoped simp] theorem map_inv_of_isMulOneCycle {f : G → M} (hf : IsMulOneCycle f) (g : G) :
    g • f g⁻¹ = (f g)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv, ← map_one_of_isMulOneCycle hf, ← mul_inv_cancel g, hf g g⁻¹]

theorem smul_map_inv_div_map_inv_of_isMulTwoCycle
    {f : G × G → M} (hf : IsMulTwoCycle f) (g : G) :
    g • f (g⁻¹, g) / f (g, g⁻¹) = f (1, 1) / f (g, 1) := by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isMulTwoCycle hf g] at this
  exact div_eq_div_iff_mul_eq_mul.2 this.symm

end

end IsMulCycle

section IsMulBoundary

variable {G M : Type*} [Mul G] [CommGroup M] [SMul G M]

/-- A function `f : G → M` satisfies the multiplicative 1-coboundary condition if there's `x : M`
such that `g • x / x = f(g)` for all `g : G`. -/
def IsMulOneBoundary (f : G → M) : Prop := ∃ x : M, ∀ g : G, g • x / x = f g

/-- A function `f : G × G → M` satisfies the 2-coboundary condition if there's `x : G → M` such
that `g • x(h) / x(gh) * x(g) = f(g, h)` for all `g, h : G`. -/
def IsMulTwoBoundary (f : G × G → M) : Prop :=
  ∃ x : G → M, ∀ g h : G, g • x h / x (g * h) * x g = f (g, h)

end IsMulBoundary

section ofMulDistribMulAction

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
/-
/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G → M` satisfying the multiplicative 1-cocycle condition, produces a 1-cocycle for the
representation on `Additive M` induced by the `MulDistribMulAction`. -/
def oneCyclesOfIsMulOneCycle {f : G → M} (hf : IsMulOneCycle f) :
    oneCycles (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_oneCycles_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

theorem isMulOneCycle_of_oneCycles (f : oneCycles (Rep.ofMulDistribMulAction G M)) :
    IsMulOneCycle (M := M) (Additive.toMul ∘ f.1) := (mem_oneCycles_iff f.1).1 f.2

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G → M` satisfying the multiplicative 1-coboundary condition, produces a
1-coboundary for the representation on `Additive M` induced by the `MulDistribMulAction`. -/
def oneBoundariesOfIsMulOneBoundary {f : G → M} (hf : IsMulOneBoundary f) :
    oneBoundaries (Rep.ofMulDistribMulAction G M) :=
  oneBoundariesOfMemRange (f := Additive.ofMul ∘ f) ⟨hf.choose, funext hf.choose_spec⟩

theorem isMulOneBoundary_of_oneBoundaries
    (f : oneBoundaries (Rep.ofMulDistribMulAction G M)) :
    IsMulOneBoundary (M := M) (Additive.ofMul ∘ f.1.1) := by
  rcases mem_range_of_mem_oneBoundaries f.2 with ⟨x, hx⟩
  exact ⟨x, by rw [← hx]; intro g; rfl⟩

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G × G → M` satisfying the multiplicative 2-cocycle condition, produces a 2-cocycle for the
representation on `Additive M` induced by the `MulDistribMulAction`. -/
def twoCyclesOfIsMulTwoCycle {f : G × G → M} (hf : IsMulTwoCycle f) :
    twoCycles (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_twoCycles_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

theorem isMulTwoCycle_of_twoCycles (f : twoCycles (Rep.ofMulDistribMulAction G M)) :
    IsMulTwoCycle (M := M) (Additive.toMul ∘ f.1) := (mem_twoCycles_iff f.1).1 f.2

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G × G → M` satisfying the multiplicative 2-coboundary condition, produces a
2-coboundary for the representation on `M` induced by the `MulDistribMulAction`. -/
def twoBoundariesOfIsMulTwoBoundary {f : G × G → M} (hf : IsMulTwoBoundary f) :
    twoBoundaries (Rep.ofMulDistribMulAction G M) :=
  twoBoundariesOfMemRange ⟨hf.choose, funext fun g ↦ hf.choose_spec g.1 g.2⟩

theorem isMulTwoBoundary_of_twoBoundaries
    (f : twoBoundaries (Rep.ofMulDistribMulAction G M)) :
    IsMulTwoBoundary (M := M) (Additive.toMul ∘ f.1.1) := by
  rcases mem_range_of_mem_twoBoundaries f.2 with ⟨x, hx⟩
  exact ⟨x, fun g h => Function.funext_iff.1 hx (g, h)⟩
-/
end ofMulDistribMulAction

section Homology
variable [DecidableEq G]

/-- We define the 0th group cohomology of a `k`-linear `G`-representation `A`, `H⁰(G, A)`, to be
the invariants of the representation, `Aᴳ`. -/
abbrev H0 := coinvariants A.ρ

/-- We define the 1st group cohomology of a `k`-linear `G`-representation `A`, `H¹(G, A)`, to be
1-cocycles (i.e. `Z¹(G, A) := Ker(d¹ : Fun(G, A) → Fun(G², A)`) modulo 1-coboundaries
(i.e. `B¹(G, A) := Im(d⁰: A → Fun(G, A))`). -/
abbrev H1 := oneCycles A ⧸ oneBoundaries A

/-- The quotient map `Z¹(G, A) → H¹(G, A).` -/
def H1_π : oneCycles A →ₗ[k] H1 A := (oneBoundaries A).mkQ

/-- We define the 2nd group cohomology of a `k`-linear `G`-representation `A`, `H²(G, A)`, to be
2-cocycles (i.e. `Z²(G, A) := Ker(d² : Fun(G², A) → Fun(G³, A)`) modulo 2-coboundaries
(i.e. `B²(G, A) := Im(d¹: Fun(G, A) → Fun(G², A))`). -/
abbrev H2 := twoCycles A ⧸ twoBoundaries A

/-- The quotient map `Z²(G, A) → H²(G, A).` -/
def H2_π : twoCycles A →ₗ[k] H2 A := (twoBoundaries A).mkQ

end Homology

section H0
variable [DecidableEq G]
/-
/-- When the representation on `A` is trivial, then `H⁰(G, A)` is all of `A.` -/
def H0LEquivOfIsTrivial [A.IsTrivial] :
    H0 A ≃ₗ[k] A := LinearEquiv.ofTop _ (invariants_eq_top A.ρ)

@[simp] theorem H0LEquivOfIsTrivial_eq_subtype [A.IsTrivial] :
    H0LEquivOfIsTrivial A = A.ρ.invariants.subtype := rfl

theorem H0LEquivOfIsTrivial_apply [A.IsTrivial] (x : H0 A) :
    H0LEquivOfIsTrivial A x = x := rfl

@[simp] theorem H0LEquivOfIsTrivial_symm_apply [A.IsTrivial] (x : A) :
    (H0LEquivOfIsTrivial A).symm x = x := rfl
-/
end H0

section H1
/-
/-- When `A : Rep k G` is a trivial representation of `G`, `H¹(G, A)` is isomorphic to the
group homs `G → A`. -/
def H1LEquivOfIsTrivial [A.IsTrivial] :
    H1 A ≃ₗ[k] Additive G →+ A :=
  (Submodule.quotEquivOfEqBot _ (oneBoundaries_eq_bot_of_isTrivial A)).trans
    (oneCyclesLEquivOfIsTrivial A)

theorem H1LEquivOfIsTrivial_comp_H1_π [A.IsTrivial] :
    (H1LEquivOfIsTrivial A).comp (H1_π A) = oneCyclesLEquivOfIsTrivial A := by
  ext; rfl

@[simp] theorem H1LEquivOfIsTrivial_H1_π_apply_apply
    [A.IsTrivial] (f : oneCycles A) (x : Additive G) :
    H1LEquivOfIsTrivial A (H1_π A f) x = f.1 (Additive.toMul x) := rfl

@[simp] theorem H1LEquivOfIsTrivial_symm_apply [A.IsTrivial] (f : Additive G →+ A) :
    (H1LEquivOfIsTrivial A).symm f = H1_π A ((oneCyclesLEquivOfIsTrivial A).symm f) :=
  rfl
-/
end H1

section groupHomologyIso

open ShortComplex

section H0
variable [DecidableEq G]

lemma dZero_comp_H0_subtype : (coinvariantsKer A.ρ).mkQ ∘ₗ dZero A = 0 := by
  sorry

/-- The (exact) short complex `A.ρ.invariants ⟶ A ⟶ (G → A)`. -/
def shortComplexH0 : ShortComplex (ModuleCat k) :=
  ShortComplex.moduleCatMk _ _ (dZero_comp_H0_subtype A)

instance : Epi (shortComplexH0 A).g := by
  rw [ModuleCat.epi_iff_surjective]
  sorry
  --apply Submodule.injective_subtype

lemma shortComplexH0_exact : (shortComplexH0 A).Exact := by
  /-rw [ShortComplex.moduleCat_exact_iff]
  intro (x : A) (hx : dZero _ x = 0)
  refine ⟨⟨x, fun g => ?_⟩, rfl⟩
  rw [← sub_eq_zero]
  exact congr_fun hx g-/

/-- The arrow `A --dZero--> Fun(G, A)` is isomorphic to the differential
`(inhomogeneousChains A).d 0 1` of the complex of inhomogeneous cochains of `A`. -/
@[simps! hom_left hom_right inv_left inv_right]
def dZeroArrowIso : Arrow.mk ((inhomogeneousChains A).d 1 0) ≅
    Arrow.mk (ModuleCat.ofHom (dZero A)) :=
  Arrow.isoMk (oneChainsLEquiv A).toModuleIso (zeroChainsLEquiv A).toModuleIso
    (dZero_comp_eq A).symm

/-- The 0-cocycles of the complex of inhomogeneous cochains of `A` are isomorphic to
`A.ρ.invariants`, which is a simpler type. -/
def isoZeroCycles : cocycles A 0 ≅ ModuleCat.of k A.ρ.invariants :=
  KernelFork.mapIsoOfIsLimit
    ((inhomogeneousChains A).cyclesIsKernel 0 1 (by simp)) (shortComplexH0_exact A).fIsKernel
      (dZeroArrowIso A)

lemma isoZeroCycles_hom_comp_subtype :
    (isoZeroCycles A).hom ≫ A.ρ.invariants.subtype =
      iCycles A 0 ≫ (zeroChainsLEquiv A).toModuleIso.hom := by
  dsimp [isoZeroCycles]
  apply KernelFork.mapOfIsLimit_ι

/-- The 0th group cohomology of `A`, defined as the 0th cohomology of the complex of inhomogeneous
cochains, is isomorphic to the invariants of the representation on `A`. -/
def isoH0 : groupHomology A 0 ≅ ModuleCat.of k (H0 A) :=
  (ChainComplex.isoHomologyπ₀ _).symm ≪≫ isoZeroCycles A

lemma groupHomologyπ_comp_isoH0_hom  :
    groupHomologyπ A 0 ≫ (isoH0 A).hom = (isoZeroCycles A).hom := by
  simp [isoH0]

end H0

section H1

/-- The short complex `A --dZero--> Fun(G, A) --dOne--> Fun(G × G, A)`. -/
def shortComplexH1 : ShortComplex (ModuleCat k) :=
  moduleCatMk (dZero A) (dOne A) (dOne_comp_dZero A)

/-- The short complex `A --dZero--> Fun(G, A) --dOne--> Fun(G × G, A)` is isomorphic to the 1st
short complex associated to the complex of inhomogeneous cochains of `A`. -/
@[simps! hom inv]
def shortComplexH1Iso : (inhomogeneousChains A).sc' 0 1 2 ≅ shortComplexH1 A :=
    isoMk (zeroChainsLEquiv A).toModuleIso (oneChainsLEquiv A).toModuleIso
      (twoChainsLEquiv A).toModuleIso (dZero_comp_eq A) (dOne_comp_eq A)

/-- The 1-cocycles of the complex of inhomogeneous cochains of `A` are isomorphic to
`oneCycles A`, which is a simpler type. -/
def isoOneCycles : cocycles A 1 ≅ ModuleCat.of k (oneCycles A) :=
  (inhomogeneousChains A).cyclesIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    cyclesMapIso (shortComplexH1Iso A) ≪≫ (shortComplexH1 A).moduleCatCyclesIso

lemma isoOneCycles_hom_comp_subtype :
    (isoOneCycles A).hom ≫ ModuleCat.ofHom (oneCycles A).subtype =
      iCycles A 1 ≫ (oneChainsLEquiv A).toModuleIso.hom := by
  dsimp [isoOneCycles]
  rw [Category.assoc, Category.assoc]
  erw [(shortComplexH1 A).moduleCatCyclesIso_hom_subtype]
  rw [cyclesMap_i, HomologicalComplex.cyclesIsoSc'_hom_iCycles_assoc]

lemma toCycles_comp_isoOneCycles_hom :
    toCycles A 0 1 ≫ (isoOneCycles A).hom =
      (zeroChainsLEquiv A).toModuleIso.hom ≫
        ModuleCat.ofHom (shortComplexH1 A).moduleCatToCycles := by
  simp [isoOneCycles]
  rfl

/-- The 1st group cohomology of `A`, defined as the 1st cohomology of the complex of inhomogeneous
cochains, is isomorphic to `oneCycles A ⧸ oneBoundaries A`, which is a simpler type. -/
def isoH1 : groupHomology A 1 ≅ ModuleCat.of k (H1 A) :=
  (inhomogeneousChains A).homologyIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    homologyMapIso (shortComplexH1Iso A) ≪≫ (shortComplexH1 A).moduleCatHomologyIso

lemma groupHomologyπ_comp_isoH1_hom  :
    groupHomologyπ A 1 ≫ (isoH1 A).hom =
      (isoOneCycles A).hom ≫ (shortComplexH1 A).moduleCatHomologyπ := by
  simp [isoH1, isoOneCycles]

end H1

section H2

/-- The short complex `Fun(G, A) --dOne--> Fun(G × G, A) --dTwo--> Fun(G × G × G, A)`. -/
def shortComplexH2 : ShortComplex (ModuleCat k) :=
  moduleCatMk (dOne A) (dTwo A) (dTwo_comp_dOne A)

/-- The short complex `Fun(G, A) --dOne--> Fun(G × G, A) --dTwo--> Fun(G × G × G, A)` is
isomorphic to the 2nd short complex associated to the complex of inhomogeneous cochains of `A`. -/
@[simps! hom inv]
def shortComplexH2Iso :
    (inhomogeneousChains A).sc' 1 2 3 ≅ shortComplexH2 A :=
  isoMk (oneChainsLEquiv A).toModuleIso (twoChainsLEquiv A).toModuleIso
    (threeChainsLEquiv A).toModuleIso (dOne_comp_eq A) (dTwo_comp_eq A)

/-- The 2-cocycles of the complex of inhomogeneous cochains of `A` are isomorphic to
`twoCycles A`, which is a simpler type. -/
def isoTwoCycles : cocycles A 2 ≅ ModuleCat.of k (twoCycles A) :=
  (inhomogeneousChains A).cyclesIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    cyclesMapIso (shortComplexH2Iso A) ≪≫ (shortComplexH2 A).moduleCatCyclesIso

lemma isoTwoCycles_hom_comp_subtype :
    (isoTwoCycles A).hom ≫ ModuleCat.ofHom (twoCycles A).subtype =
      iCycles A 2 ≫ (twoChainsLEquiv A).toModuleIso.hom := by
  dsimp [isoTwoCycles]
  rw [Category.assoc, Category.assoc]
  erw [(shortComplexH2 A).moduleCatCyclesIso_hom_subtype]
  rw [cyclesMap_i, HomologicalComplex.cyclesIsoSc'_hom_iCycles_assoc]

lemma toCycles_comp_isoTwoCycles_hom :
    toCycles A 1 2 ≫ (isoTwoCycles A).hom =
      (oneChainsLEquiv A).toModuleIso.hom ≫
        ModuleCat.ofHom (shortComplexH2 A).moduleCatToCycles := by
  simp [isoTwoCycles]
  rfl

/-- The 2nd group cohomology of `A`, defined as the 2nd cohomology of the complex of inhomogeneous
cochains, is isomorphic to `twoCycles A ⧸ twoBoundaries A`, which is a simpler type. -/
def isoH2 : groupHomology A 2 ≅ ModuleCat.of k (H2 A) :=
  (inhomogeneousChains A).homologyIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    homologyMapIso (shortComplexH2Iso A) ≪≫ (shortComplexH2 A).moduleCatHomologyIso

lemma groupHomologyπ_comp_isoH2_hom  :
    groupHomologyπ A 2 ≫ (isoH2 A).hom =
      (isoTwoCycles A).hom ≫ (shortComplexH2 A).moduleCatHomologyπ := by
  simp [isoH2, isoTwoCycles]

end H2

end groupHomologyIso

end groupHomology
