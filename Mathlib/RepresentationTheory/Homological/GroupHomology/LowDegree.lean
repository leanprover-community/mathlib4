/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Joël Riou

-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
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

/-- The 1st object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `G →₀ A` as a `k`-module. -/
def oneChainsLEquiv : (inhomogeneousChains A).X 1 ≃ₗ[k] G →₀ A :=
  Finsupp.domLCongr (Equiv.funUnique (Fin 1) G)

/-- The 2nd object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `G² →₀ A` as a `k`-module. -/
def twoChainsLEquiv : (inhomogeneousChains A).X 2 ≃ₗ[k] G × G →₀ A :=
  Finsupp.domLCongr (piFinTwoEquiv fun _ => G)

/-- The 3rd object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `G³ → A` as a `k`-module. -/
def threeChainsLEquiv : (inhomogeneousChains A).X 3 ≃ₗ[k] G × G × G →₀ A :=
  Finsupp.domLCongr ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))

end Chains

section Differentials

/-- The 0th differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G →₀ A) → A`. It sends `single g a ↦ ρ_A(g⁻¹)(a) - a.` -/
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
    · simpa [← hy, add_sub_add_comm, Finsupp.sum_add_index]
        using Submodule.add_mem _ (mem_coinvariantsKer_of_eq _ _ _ rfl) (h rfl)

@[simp]
theorem dZero_eq_zero [A.IsTrivial] : dZero A = 0 := by
  ext
  simp

/-- The 1st differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G² →₀ A) → (G →₀ A)`. It sends
`single (g₁, g₂) a ↦ single g₂ ρ_A(g₁⁻¹)(a) - single g₁g₂ a + single g₁ a`. -/
abbrev dOne : (G × G →₀ A) →ₗ[k] G →₀ A :=
  Finsupp.lsum k fun g => Finsupp.lsingle g.2 ∘ₗ A.ρ g.1⁻¹
    - Finsupp.lsingle (g.1 * g.2) + Finsupp.lsingle g.1

/-- The 2nd differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G³ →₀ A) → (G² →₀ A)`. It sends
`single (g₁, g₂, g₃) a ↦ single (g₂, g₃) ρ_A(g₁⁻¹)(a) - single (g₁g₂, g₃) a
  + single (g₁, g₂g₃) a - single (g₁, g₂) a`. -/
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


/-- Let `C(G, A)` denote the complex of inhomogeneous chains of `A : Rep k G`. This lemma
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
where the vertical arrows are `oneChainsLEquiv` and `zeroChainsLEquiv` respectively.
-/
theorem dZero_comp_eq [DecidableEq G] :
    dZero A ∘ₗ oneChainsLEquiv A = zeroChainsLEquiv A ∘ₗ (inhomogeneousChains A).d 1 0 :=
  Finsupp.lhom_ext fun f a => by
  simp [ModuleCat.coe_of, zeroChainsLEquiv, oneChainsLEquiv, inhomogeneousChains.d_apply,
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
where the vertical arrows are `twoChainsLEquiv` and `oneChainsLEquiv` respectively.
-/

theorem domLCongr_single {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {α₁ α₂ : Type*} (e : α₁ ≃ α₂) (a : α₁) (m : M) :
    Finsupp.domLCongr (R := R) e (Finsupp.single a m) = Finsupp.single (e a) m := by
  simp

theorem dOne_comp_eq [DecidableEq G] :
    dOne A ∘ₗ twoChainsLEquiv A = oneChainsLEquiv A ∘ₗ (inhomogeneousChains A).d 2 1 :=
  Finsupp.lhom_ext fun f a => by
  simp [inhomogeneousChains.d_apply, ModuleCat.coe_of, oneChainsLEquiv, twoChainsLEquiv,
    Fin.contractNth_last _ (show 1 = Fin.last 1 by rfl), -Finsupp.domLCongr_apply,
    domLCongr_single, sub_eq_add_neg, add_assoc]

lemma ffs {α : Type*} [AddCommSemigroup α] (a b c : α) : a + b + c = c + b + a := by
  rw [add_rotate, add_comm b]

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
where the vertical arrows are `threeChainsLEquiv` and `twoChainsLEquiv` respectively.
-/
theorem dTwo_comp_eq [DecidableEq G] :
    dTwo A ∘ₗ threeChainsLEquiv A
      = twoChainsLEquiv A ∘ₗ (inhomogeneousChains A).d 3 2 :=
  Finsupp.lhom_ext fun f a => by
  simpa [inhomogeneousChains.d_apply, ModuleCat.coe_of, twoChainsLEquiv, threeChainsLEquiv,
    Fin.contractNth_last _ (show 2 = Fin.last 2 by ext; rfl), -Finsupp.domLCongr_apply,
    domLCongr_single, dTwo, Fin.sum_univ_three, Fin.contractNth, pow_succ, Fin.tail_def,
    sub_eq_add_neg, add_assoc] using ffs _ _ _

theorem dZero_comp_dOne [DecidableEq G] : dZero A ∘ₗ dOne A = 0 := by
  ext x g
  simp [Finsupp.sum_add_index, Finsupp.sum_sub_index, sub_sub_sub_comm, add_sub_add_comm]

open Finsupp
theorem dOne_comp_dTwo [DecidableEq G] : dOne A ∘ₗ dTwo A = 0 := by
  show ModuleCat.asHom (dTwo A) ≫ ModuleCat.asHom (dOne A) = _
  have h1 : _ ≫ ModuleCat.asHom (dOne A) = _ ≫ _ := congr(ModuleCat.asHom $(dOne_comp_eq A))
  have h2 : _ ≫ ModuleCat.asHom (dTwo A) = _ ≫ _ := congr(ModuleCat.asHom $(dTwo_comp_eq A))
  simp only [← LinearEquiv.toModuleIso_hom] at h1 h2
  simp only [(Iso.eq_inv_comp _).2 h2, (Iso.eq_inv_comp _).2 h1,
    Category.assoc, Iso.hom_inv_id_assoc, HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]

end Differentials

section Cycles

/-- The 1-cycles `Z₁(G, A)` of `A : Rep k G`, defined as the kernel of the map
`(G →₀ A) → A` sending `single g a ↦ ρ_A(g⁻¹)(a) - a`. -/
def oneCycles : Submodule k (G →₀ A) := LinearMap.ker (dZero A)

/-- The 2-cycles `Z₂(G, A)` of `A : Rep k G`, defined as the kernel of the map
`(G² →₀ A) → (G →₀ A)` sending
`single (g₁, g₂) a ↦ single g₂ ρ_A(g₁⁻¹)(a) - single g₁g₂ a + single g₁ a`.` -/
def twoCycles : Submodule k (G × G →₀ A) := LinearMap.ker (dOne A)

variable {A}

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

/-- The 1-boundaries `B₁(G, A)` of `A : Rep k G`, defined as the image of the map
`(G² →₀ A) → (G →₀ A)` sending
`single (g₁, g₂) a ↦ single g₂ ρ_A(g₁⁻¹)(a) - single g₁g₂ a + single g₁ a`. -/
def oneBoundaries [DecidableEq G] : Submodule k (oneCycles A) :=
  LinearMap.range ((dOne A).codRestrict (oneCycles A) fun c =>
    LinearMap.ext_iff.1 (dZero_comp_dOne A) c)

/-- The 2-boundaries `B₂(G, A)` of `A : Rep k G`, defined as the image of the map
`(G³ →₀ A) → (G² →₀ A)` sending
`single (g₁, g₂, g₃) a ↦ single (g₂, g₃) ρ_A(g₁⁻¹)(a) - single (g₁g₂, g₃) a
  + single (g₁, g₂g₃) a - single (g₁, g₂) a` -/
def twoBoundaries [DecidableEq G] : Submodule k (twoCycles A) :=
  LinearMap.range ((dTwo A).codRestrict (twoCycles A) fun c =>
    LinearMap.ext_iff.1 (dOne_comp_dTwo.{u} A) c)

end Boundaries

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
-/
section Homology
variable [DecidableEq G]
variable (A)

/-- We define the 0th group homology of a `k`-linear `G`-representation `A`, `H₀(G, A)`, to be
the coinvariants of the representation, `A_G`. -/
abbrev H0 := A.ρ.coinvariants

/-- We define the 1st group homology of a `k`-linear `G`-representation `A`, `H₁(G, A)`, to be
1-cycles (i.e. `Z₁(G, A) := Ker(d₀ : (G →₀ A) → A`) modulo 1-boundaries
(i.e. `B₁(G, A) := Im(d₁: (G →₀ A) → A)`). -/
abbrev H1 := oneCycles A ⧸ oneBoundaries A

/-- We define the 2nd group homology of a `k`-linear `G`-representation `A`, `H₂(G, A)`, to be
2-cycles (i.e. `Z₂(G, A) := Ker(d₁ : (G² →₀ A) → (G →₀ A)`) modulo 2-boundaries
(i.e. `B²(G, A) := Im(d₂ : (G³ →₀ A) → (G² →₀ A))`). -/
abbrev H2 := twoCycles A ⧸ twoBoundaries A

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

theorem H1LEquivOfIsTrivial_comp_H1π [A.IsTrivial] :
    (H1LEquivOfIsTrivial A).comp (H1π A) = oneCyclesLEquivOfIsTrivial A := by
  ext; rfl

@[simp] theorem H1LEquivOfIsTrivial_H1π_apply_apply
    [A.IsTrivial] (f : oneCycles A) (x : Additive G) :
    H1LEquivOfIsTrivial A (H1π A f) x = f.1 (Additive.toMul x) := rfl

@[simp] theorem H1LEquivOfIsTrivial_symm_apply [A.IsTrivial] (f : Additive G →+ A) :
    (H1LEquivOfIsTrivial A).symm f = H1π A ((oneCyclesLEquivOfIsTrivial A).symm f) :=
  rfl
-/
end H1

section groupHomologyIso

open ShortComplex

section H0
variable (A) [DecidableEq G]

abbrev isoZeroCycles : cycles A 0 ≅ ModuleCat.of k A :=
  (inhomogeneousChains A).iCyclesIso _ 0 (by aesop) (by aesop)
    ≪≫ (zeroChainsLEquiv A).toModuleIso

lemma isoZeroCycles_eq_moduleCatCyclesIso_trans :
    isoZeroCycles A = moduleCatCyclesIso _ ≪≫
      ((LinearEquiv.ofEq _ _ (LinearMap.ker_eq_top.2 (by aesop)))
      ≪≫ₗ Submodule.topEquiv ≪≫ₗ zeroChainsLEquiv _).toModuleIso := by
  ext : 1
  rw [← Iso.inv_eq_inv]
  apply (cancel_mono ((inhomogeneousChains A).iCycles _)).1
  simp only [Iso.trans_inv, HomologicalComplex.iCyclesIso, HomologicalComplex.iCycles,
    asIso_inv, Category.assoc, IsIso.inv_hom_id, moduleCatCyclesIso_inv_iCycles]
  rfl

@[reassoc, elementwise]
lemma isoZeroCycles_inv_comp_iCycles :
    (isoZeroCycles A).inv ≫ iCycles A 0 = (zeroChainsLEquiv A).toModuleIso.inv := by
  simp

lemma mkQ_comp_dZero : (coinvariantsKer A.ρ).mkQ ∘ₗ dZero A = 0 := by
  rw [← dZero_range_eq_coinvariantsKer]
  exact LinearMap.range_mkQ_comp _

/-- The (exact) short complex `(G →₀ A) ⟶ A ⟶ A.ρ.coinvariants`. -/
def shortComplexH0 : ShortComplex (ModuleCat k) :=
  ShortComplex.moduleCatMk _ _ (mkQ_comp_dZero A)

abbrev H0π : ModuleCat.of k A ⟶ ModuleCat.of k (H0 A) := (shortComplexH0 A).g

instance : Epi (H0π A) := by
  rw [ModuleCat.epi_iff_surjective]
  exact Submodule.mkQ_surjective _

lemma shortComplexH0_exact : (shortComplexH0 A).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro (x : A) (hx : Submodule.mkQ _ x = 0)
  rw [← dZero_range_eq_coinvariantsKer, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  rcases hx with ⟨x, hx, rfl⟩
  use x
  rfl

/-- The arrow `(G →₀ A) --dZero--> A` is isomorphic to the differential
`(inhomogeneousChains A).d 1 0` of the complex of inhomogeneous chains of `A`. -/
@[simps! hom_left hom_right inv_left inv_right]
def dZeroArrowIso : Arrow.mk ((inhomogeneousChains A).d 1 0) ≅
    Arrow.mk (ModuleCat.asHom (dZero A)) :=
  Arrow.isoMk (oneChainsLEquiv A).toModuleIso (zeroChainsLEquiv A).toModuleIso
    (dZero_comp_eq A)

/-- The 0-cycles of the complex of inhomogeneous chains of `A` are isomorphic to
`A.ρ.coinvariants`, which is a simpler type. -/
def isoZeroOpcycles : opcycles A 0 ≅ ModuleCat.of k A.ρ.coinvariants :=
  CokernelCofork.mapIsoOfIsColimit
    ((inhomogeneousChains A).opcyclesIsCokernel 1 0 (by simp)) (shortComplexH0_exact A).gIsCokernel
      (dZeroArrowIso A)

@[reassoc (attr := simp)]
lemma pOpcycles_comp_opcyclesIso_hom :
    pOpcycles A 0 ≫ (isoZeroOpcycles A).hom =
      (zeroChainsLEquiv A).toModuleIso.hom ≫ H0π A := by
  dsimp [isoZeroOpcycles]
  exact CokernelCofork.π_mapOfIsColimit (φ := (dZeroArrowIso A).hom) _ _

/-- The 0th group homology of `A`, defined as the 0th homology of the complex of inhomogeneous
chains, is isomorphic to the coinvariants of the representation on `A`. -/
def isoH0 : groupHomology A 0 ≅ ModuleCat.of k (H0 A) :=
  (ChainComplex.isoHomologyι₀ _) ≪≫ (isoZeroOpcycles A)

@[reassoc (attr := simp)]
lemma π_comp_isoH0_hom :
    groupHomologyπ A 0 ≫ (isoH0 A).hom = (isoZeroCycles A).hom ≫ H0π A := by
  simp [isoH0]

end H0

section H1

variable (A) [DecidableEq G]

/-- The short complex `(G² →₀ A) --dOne--> (G →₀ A) --dZero--> A`. -/
def shortComplexH1 : ShortComplex (ModuleCat k) :=
  moduleCatMk (dOne A) (dZero A) (dZero_comp_dOne A)

/-- The quotient map `Z₁(G, A) → H₁(G, A).` -/
abbrev H1π : ModuleCat.of k (oneCycles A) ⟶ ModuleCat.of k (H1 A) :=
  moduleCatHomologyπ (shortComplexH1 A)

/-- The short complex `(G² →₀ A) --dOne--> (G →₀ A) --dZero--> A` is isomorphic to the 1st
short complex associated to the complex of inhomogeneous chains of `A`. -/
@[simps! hom inv]
def shortComplexH1Iso : (inhomogeneousChains A).sc' 2 1 0 ≅ shortComplexH1 A :=
    isoMk (twoChainsLEquiv A).toModuleIso (oneChainsLEquiv A).toModuleIso
      (zeroChainsLEquiv A).toModuleIso (dOne_comp_eq A) (dZero_comp_eq A)

/-- The 1-cycles of the complex of inhomogeneous chains of `A` are isomorphic to
`oneCycles A`, which is a simpler type. -/
def isoOneCycles : cycles A 1 ≅ ModuleCat.of k (oneCycles A) :=
  (inhomogeneousChains A).cyclesIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    cyclesMapIso (shortComplexH1Iso A) ≪≫ (shortComplexH1 A).moduleCatCyclesIso

@[reassoc (attr := simp)]
lemma isoOneCycles_hom_comp_subtype :
    (isoOneCycles A).hom ≫ ModuleCat.asHom (oneCycles A).subtype =
      iCycles A 1 ≫ (oneChainsLEquiv A).toModuleIso.hom := by
  have := (shortComplexH1 A).moduleCatCyclesIso_hom_subtype
  simp_all [shortComplexH1, ModuleCat.asHom, isoOneCycles, oneCycles]

@[reassoc (attr := simp)]
lemma isoOneCycles_inv_comp_iCycles :
    (isoOneCycles A).inv ≫ iCycles A 1 =
      ModuleCat.asHom (oneCycles A).subtype ≫ (oneChainsLEquiv A).toModuleIso.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, isoOneCycles_hom_comp_subtype]

@[reassoc (attr := simp)]
lemma toCycles_comp_isoOneCycles_hom :
    toCycles A 2 1 ≫ (isoOneCycles A).hom =
      (twoChainsLEquiv A).toModuleIso.hom ≫
        ModuleCat.asHom (shortComplexH1 A).moduleCatToCycles := by
  simp [isoOneCycles]
  rfl

lemma cyclesSuccIso_0_eq :
    cyclesSuccIso A 0 = isoOneCycles A ≪≫ (LinearEquiv.kerLEquivOfCompEqComp _ _ <| by
      simpa using dZero_comp_eq A).toModuleIso := by
  ext : 1
  rw [← Iso.inv_eq_inv, Iso.trans_inv, Iso.eq_inv_comp]
  apply (cancel_mono (HomologicalComplex.iCycles _ _)).1
  simp only [Nat.reduceAdd, Iso.trans_inv, LinearEquiv.toModuleIso_inv, LinearEquiv.symm_symm,
    Category.assoc, cyclesSuccIso_inv_comp_iCycles, isoOneCycles_inv_comp_iCycles]
  rfl

/-- The 1st group homology of `A`, defined as the 1st homology of the complex of inhomogeneous
chains, is isomorphic to `oneCycles A ⧸ oneBoundaries A`, which is a simpler type. -/
def isoH1 : groupHomology A 1 ≅ ModuleCat.of k (H1 A) :=
  (inhomogeneousChains A).homologyIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    homologyMapIso (shortComplexH1Iso A) ≪≫ (shortComplexH1 A).moduleCatHomologyIso

@[reassoc (attr := simp)]
lemma groupHomologyπ_comp_isoH1_hom  :
    groupHomologyπ A 1 ≫ (isoH1 A).hom = (isoOneCycles A).hom ≫ H1π A := by
  simp [isoH1, isoOneCycles]

end H1

section H2

variable (A) [DecidableEq G]

/-- The short complex `(G³ →₀ A) --dTwo--> (G² →₀ A) --dOne--> (G →₀ A)`. -/
def shortComplexH2 : ShortComplex (ModuleCat k) :=
  moduleCatMk (dTwo A) (dOne A) (dOne_comp_dTwo A)

/-- The quotient map `Z₂(G, A) → H₂(G, A).` -/
abbrev H2π : ModuleCat.of k (twoCycles A) ⟶ ModuleCat.of k (H2 A) :=
  moduleCatHomologyπ (shortComplexH2 A)

/-- The short complex `(G³ →₀ A) --dTwo--> (G² →₀ A) --dOne--> (G →₀ A)` is
isomorphic to the 2nd short complex associated to the complex of inhomogeneous chains of `A`. -/
@[simps! hom inv]
def shortComplexH2Iso :
    (inhomogeneousChains A).sc' 3 2 1 ≅ shortComplexH2 A :=
  isoMk (threeChainsLEquiv A).toModuleIso (twoChainsLEquiv A).toModuleIso
    (oneChainsLEquiv A).toModuleIso (dTwo_comp_eq A) (dOne_comp_eq A)

/-- The 2-cycles of the complex of inhomogeneous chains of `A` are isomorphic to
`twoCycles A`, which is a simpler type. -/
def isoTwoCycles : cycles A 2 ≅ ModuleCat.of k (twoCycles A) :=
  (inhomogeneousChains A).cyclesIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    cyclesMapIso (shortComplexH2Iso A) ≪≫ (shortComplexH2 A).moduleCatCyclesIso

@[reassoc (attr := simp)]
lemma isoTwoCycles_hom_comp_subtype :
    (isoTwoCycles A).hom ≫ ModuleCat.asHom (twoCycles A).subtype =
      iCycles A 2 ≫ (twoChainsLEquiv A).toModuleIso.hom := by
  have := (shortComplexH2 A).moduleCatCyclesIso_hom_subtype
  simp_all [shortComplexH2, ModuleCat.asHom, isoTwoCycles, twoCycles]

@[reassoc (attr := simp)]
lemma isoTwoCycles_inv_comp_iCycles :
    (isoTwoCycles A).inv ≫ iCycles A 2 =
      ModuleCat.asHom (twoCycles A).subtype ≫ (twoChainsLEquiv A).toModuleIso.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, isoTwoCycles_hom_comp_subtype]

@[reassoc (attr := simp)]
lemma toCycles_comp_isoTwoCycles_hom :
    toCycles A 3 2 ≫ (isoTwoCycles A).hom =
      (threeChainsLEquiv A).toModuleIso.hom ≫
        ModuleCat.asHom (shortComplexH2 A).moduleCatToCycles := by
  simp [isoTwoCycles]
  rfl

lemma cyclesSuccIso_1_eq :
    cyclesSuccIso A 1 = isoTwoCycles A ≪≫ (LinearEquiv.kerLEquivOfCompEqComp _ _ <| by
      simpa using dOne_comp_eq A).toModuleIso := by
  ext : 1
  rw [← Iso.inv_eq_inv, Iso.trans_inv, Iso.eq_inv_comp]
  apply (cancel_mono (HomologicalComplex.iCycles _ _)).1
  simp only [Nat.reduceAdd, Iso.trans_inv, LinearEquiv.toModuleIso_inv, LinearEquiv.symm_symm,
    Category.assoc, cyclesSuccIso_inv_comp_iCycles, isoTwoCycles_inv_comp_iCycles]
  rfl

/-- The 2nd group homology of `A`, defined as the 2nd homology of the complex of inhomogeneous
chains, is isomorphic to `twoCycles A ⧸ twoBoundaries A`, which is a simpler type. -/
def isoH2 : groupHomology A 2 ≅ ModuleCat.of k (H2 A) :=
  (inhomogeneousChains A).homologyIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    homologyMapIso (shortComplexH2Iso A) ≪≫ (shortComplexH2 A).moduleCatHomologyIso

@[reassoc (attr := simp)]
lemma groupHomologyπ_comp_isoH2_hom  :
    groupHomologyπ A 2 ≫ (isoH2 A).hom = (isoTwoCycles A).hom ≫ H2π A := by
  simp [isoH2, isoTwoCycles]

end H2

end groupHomologyIso

end groupHomology
