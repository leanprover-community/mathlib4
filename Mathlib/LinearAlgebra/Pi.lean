/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser
-/
import Mathlib.LinearAlgebra.Basic
import Mathlib.Logic.Equiv.Fin

#align_import linear_algebra.pi from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Pi types of modules

This file defines constructors for linear maps whose domains or codomains are pi types.

It contains theorems relating these to each other, as well as to `LinearMap.ker`.

## Main definitions

- pi types in the codomain:
  - `LinearMap.pi`
  - `LinearMap.single`
- pi types in the domain:
  - `LinearMap.proj`
  - `LinearMap.diag`

-/


universe u v w x y z u' v' w' x' y'

variable {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}

variable {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x} {ι' : Type x'}

open Function Submodule

open BigOperators

namespace LinearMap

universe i

variable [Semiring R] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]
  {φ : ι → Type i} [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]

/-- `pi` construction for linear functions. From a family of linear functions it produces a linear
function into a family of modules. -/
def pi (f : (i : ι) → M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (i : ι) → φ i :=
  { Pi.addHom fun i => (f i).toAddHom with
    toFun := fun c i => f i c
    map_smul' := fun _ _ => funext fun i => (f i).map_smul _ _ }
#align linear_map.pi LinearMap.pi

@[simp]
theorem pi_apply (f : (i : ι) → M₂ →ₗ[R] φ i) (c : M₂) (i : ι) : pi f c i = f i c :=
  rfl
#align linear_map.pi_apply LinearMap.pi_apply

theorem ker_pi (f : (i : ι) → M₂ →ₗ[R] φ i) : ker (pi f) = ⨅ i : ι, ker (f i) := by
  ext c; simp [funext_iff]
  -- ⊢ c ∈ ker (pi f) ↔ c ∈ ⨅ (i : ι), ker (f i)
         -- 🎉 no goals
#align linear_map.ker_pi LinearMap.ker_pi

theorem pi_eq_zero (f : (i : ι) → M₂ →ₗ[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 := by
  simp only [LinearMap.ext_iff, pi_apply, funext_iff];
  -- ⊢ (∀ (x : M₂) (a : ι), ↑(f a) x = ↑0 x a) ↔ ∀ (i : ι) (x : M₂), ↑(f i) x = ↑0 x
    exact ⟨fun h a b => h b a, fun h a b => h b a⟩
    -- 🎉 no goals
#align linear_map.pi_eq_zero LinearMap.pi_eq_zero

theorem pi_zero : pi (fun i => 0 : (i : ι) → M₂ →ₗ[R] φ i) = 0 := by ext; rfl
                                                                     -- ⊢ ↑(pi fun i => 0) x✝¹ x✝ = ↑0 x✝¹ x✝
                                                                          -- 🎉 no goals
#align linear_map.pi_zero LinearMap.pi_zero

theorem pi_comp (f : (i : ι) → M₂ →ₗ[R] φ i) (g : M₃ →ₗ[R] M₂) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl
#align linear_map.pi_comp LinearMap.pi_comp

/-- The projections from a family of modules are linear maps.

Note:  known here as `LinearMap.proj`, this construction is in other categories called `eval`, for
example `Pi.evalMonoidHom`, `Pi.evalRingHom`. -/
def proj (i : ι) : ((i : ι) → φ i) →ₗ[R] φ i where
  toFun := Function.eval i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align linear_map.proj LinearMap.proj

@[simp]
theorem coe_proj (i : ι) : ⇑(proj i : ((i : ι) → φ i) →ₗ[R] φ i) = Function.eval i :=
  rfl
#align linear_map.coe_proj LinearMap.coe_proj

theorem proj_apply (i : ι) (b : (i : ι) → φ i) : (proj i : ((i : ι) → φ i) →ₗ[R] φ i) b = b i :=
  rfl
#align linear_map.proj_apply LinearMap.proj_apply

theorem proj_pi (f : (i : ι) → M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
  ext fun _ => rfl
#align linear_map.proj_pi LinearMap.proj_pi

theorem iInf_ker_proj : (⨅ i, ker (proj i : ((i : ι) → φ i) →ₗ[R] φ i) :
    Submodule R ((i : ι) → φ i)) = ⊥ :=
  bot_unique <|
    SetLike.le_def.2 fun a h => by
      simp only [mem_iInf, mem_ker, proj_apply] at h
      -- ⊢ a ∈ ⊥
      exact (mem_bot _).2 (funext fun i => h i)
      -- 🎉 no goals
#align linear_map.infi_ker_proj LinearMap.iInf_ker_proj

/-- Linear map between the function spaces `I → M₂` and `I → M₃`, induced by a linear map `f`
between `M₂` and `M₃`. -/
@[simps]
protected def compLeft (f : M₂ →ₗ[R] M₃) (I : Type*) : (I → M₂) →ₗ[R] I → M₃ :=
  { f.toAddMonoidHom.compLeft I with
    toFun := fun h => f ∘ h
    map_smul' := fun c h => by
      ext x
      -- ⊢ AddHom.toFun { toFun := fun h => ↑f ∘ h, map_add' := (_ : ∀ (x y : I → M₂),  …
      exact f.map_smul' c (h x) }
      -- 🎉 no goals
#align linear_map.comp_left LinearMap.compLeft

theorem apply_single [AddCommMonoid M] [Module R M] [DecidableEq ι] (f : (i : ι) → φ i →ₗ[R] M)
    (i j : ι) (x : φ i) : f j (Pi.single i x j) = (Pi.single i (f i x) : ι → M) j :=
  Pi.apply_single (fun i => f i) (fun i => (f i).map_zero) _ _ _
#align linear_map.apply_single LinearMap.apply_single

/-- The `LinearMap` version of `AddMonoidHom.single` and `Pi.single`. -/
def single [DecidableEq ι] (i : ι) : φ i →ₗ[R] (i : ι) → φ i :=
  { AddMonoidHom.single φ i with
    toFun := Pi.single i
    map_smul' := Pi.single_smul i }
#align linear_map.single LinearMap.single

@[simp]
theorem coe_single [DecidableEq ι] (i : ι) : ⇑(single i : φ i →ₗ[R] (i : ι) → φ i) = Pi.single i :=
  rfl
#align linear_map.coe_single LinearMap.coe_single

variable (R φ)

/-- The linear equivalence between linear functions on a finite product of modules and
families of functions on these modules. See note [bundled maps over different rings]. -/
@[simps symm_apply]
def lsum (S) [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι] [Semiring S] [Module S M]
    [SMulCommClass R S M] : ((i : ι) → φ i →ₗ[R] M) ≃ₗ[S] ((i : ι) → φ i) →ₗ[R] M where
  toFun f := ∑ i : ι, (f i).comp (proj i)
  invFun f i := f.comp (single i)
  map_add' f g := by simp only [Pi.add_apply, add_comp, Finset.sum_add_distrib]
                     -- 🎉 no goals
  map_smul' c f := by simp only [Pi.smul_apply, smul_comp, Finset.smul_sum, RingHom.id_apply]
                      -- 🎉 no goals
  left_inv f := by
    ext i x
    -- ⊢ ↑((fun f i => comp f (single i)) (AddHom.toFun { toAddHom := { toFun := fun  …
    simp [apply_single]
    -- 🎉 no goals
  right_inv f := by
    ext x
    -- ⊢ ↑(AddHom.toFun { toAddHom := { toFun := fun f => ∑ i : ι, comp (f i) (proj i …
    suffices f (∑ j, Pi.single j (x j)) = f x by simpa [apply_single]
    -- ⊢ ↑f (∑ j : ι, Pi.single j (x j)) = ↑f x
    rw [Finset.univ_sum_single]
    -- 🎉 no goals
#align linear_map.lsum LinearMap.lsum
#align linear_map.lsum_symm_apply LinearMap.lsum_symm_apply

@[simp]
theorem lsum_apply (S) [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι] [Semiring S]
    [Module S M] [SMulCommClass R S M] (f : (i : ι) → φ i →ₗ[R] M) :
    lsum R φ S f = ∑ i : ι, (f i).comp (proj i) := rfl
#align linear_map.apply LinearMap.lsum_apply

@[simp high]
theorem lsum_single {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] {M : ι → Type*}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module R (M i)] :
    LinearMap.lsum R M R LinearMap.single = LinearMap.id :=
  LinearMap.ext fun x => by simp [Finset.univ_sum_single]
                            -- 🎉 no goals
#align linear_map.lsum_single LinearMap.lsum_single

variable {R φ}

section Ext

variable [Finite ι] [DecidableEq ι] [AddCommMonoid M] [Module R M] {f g : ((i : ι) → φ i) →ₗ[R] M}

theorem pi_ext (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) : f = g :=
  toAddMonoidHom_injective <| AddMonoidHom.functions_ext _ _ _ h
#align linear_map.pi_ext LinearMap.pi_ext

theorem pi_ext_iff : f = g ↔ ∀ i x, f (Pi.single i x) = g (Pi.single i x) :=
  ⟨fun h _ _ => h ▸ rfl, pi_ext⟩
#align linear_map.pi_ext_iff LinearMap.pi_ext_iff

/-- This is used as the ext lemma instead of `LinearMap.pi_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[ext]
theorem pi_ext' (h : ∀ i, f.comp (single i) = g.comp (single i)) : f = g := by
  refine' pi_ext fun i x => _
  -- ⊢ ↑f (Pi.single i x) = ↑g (Pi.single i x)
  convert LinearMap.congr_fun (h i) x
  -- 🎉 no goals
#align linear_map.pi_ext' LinearMap.pi_ext'

theorem pi_ext'_iff : f = g ↔ ∀ i, f.comp (single i) = g.comp (single i) :=
  ⟨fun h _ => h ▸ rfl, pi_ext'⟩
#align linear_map.pi_ext'_iff LinearMap.pi_ext'_iff

end Ext

section

variable (R φ)

/-- If `I` and `J` are disjoint index sets, the product of the kernels of the `J`th projections of
`φ` is linearly equivalent to the product over `I`. -/
def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, ker (proj i : ((i : ι) → φ i) →ₗ[R] φ i) :
    Submodule R ((i : ι) → φ i)) ≃ₗ[R] (i : I) → φ i := by
  refine'
    LinearEquiv.ofLinear (pi fun i => (proj (i : ι)).comp (Submodule.subtype _))
      (codRestrict _ (pi fun i => if h : i ∈ I then proj (⟨i, h⟩ : I) else 0) _) _ _
  · intro b
    -- ⊢ ↑(pi fun i => if h : i ∈ I then proj { val := i, property := h } else 0) b ∈ …
    simp only [mem_iInf, mem_ker, funext_iff, proj_apply, pi_apply]
    -- ⊢ ∀ (i : ι), i ∈ J → ↑(if h : i ∈ I then proj { val := i, property := h } else …
    intro j hjJ
    -- ⊢ ↑(if h : j ∈ I then proj { val := j, property := h } else 0) b = 0
    have : j ∉ I := fun hjI => hd.le_bot ⟨hjI, hjJ⟩
    -- ⊢ ↑(if h : j ∈ I then proj { val := j, property := h } else 0) b = 0
    rw [dif_neg this, zero_apply]
    -- 🎉 no goals
  · simp only [pi_comp, comp_assoc, subtype_comp_codRestrict, proj_pi, Subtype.coe_prop]
    -- ⊢ (pi fun i => if h : True then proj { val := ↑i, property := (_ : ↑i ∈ I) } e …
    ext b ⟨j, hj⟩
    -- ⊢ ↑(pi fun i => if h : True then proj { val := ↑i, property := (_ : ↑i ∈ I) }  …
    simp only [dif_pos, Function.comp_apply, Function.eval_apply, LinearMap.codRestrict_apply,
      LinearMap.coe_comp, LinearMap.coe_proj, LinearMap.pi_apply, Submodule.subtype_apply,
      Subtype.coe_prop]
    rfl
    -- 🎉 no goals
  · ext1 ⟨b, hb⟩
    -- ⊢ ↑(comp (codRestrict (⨅ (i : ι) (_ : i ∈ J), ker (proj i)) (pi fun i => if h  …
    apply Subtype.ext
    -- ⊢ ↑(↑(comp (codRestrict (⨅ (i : ι) (_ : i ∈ J), ker (proj i)) (pi fun i => if  …
    ext j
    -- ⊢ ↑(↑(comp (codRestrict (⨅ (i : ι) (_ : i ∈ J), ker (proj i)) (pi fun i => if  …
    have hb : ∀ i ∈ J, b i = 0 := by
      simpa only [mem_iInf, mem_ker, proj_apply] using (mem_iInf _).1 hb
    simp only [comp_apply, pi_apply, id_apply, proj_apply, subtype_apply, codRestrict_apply]
    -- ⊢ ↑(if h : j ∈ I then proj { val := j, property := h } else 0) (↑(pi fun i =>  …
    split_ifs with h
    -- ⊢ ↑(proj { val := j, property := h }) (↑(pi fun i => comp (proj ↑i) (Submodule …
    · rfl
      -- 🎉 no goals
    · exact (hb _ <| (hu trivial).resolve_left h).symm
      -- 🎉 no goals
#align linear_map.infi_ker_proj_equiv LinearMap.iInfKerProjEquiv

end

section

variable [DecidableEq ι]

/-- `diag i j` is the identity map if `i = j`. Otherwise it is the constant 0 map. -/
def diag (i j : ι) : φ i →ₗ[R] φ j :=
  @Function.update ι (fun j => φ i →ₗ[R] φ j) _ 0 i id j
#align linear_map.diag LinearMap.diag

theorem update_apply (f : (i : ι) → M₂ →ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ →ₗ[R] φ i) :
    (update f i b j) c = update (fun i => f i c) i (b c) j := by
  by_cases h : j = i
  -- ⊢ ↑(update f i b j) c = update (fun i => ↑(f i) c) i (↑b c) j
  · rw [h, update_same, update_same]
    -- 🎉 no goals
  · rw [update_noteq h, update_noteq h]
    -- 🎉 no goals
#align linear_map.update_apply LinearMap.update_apply

end

end LinearMap

namespace Submodule

variable [Semiring R] {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]

open LinearMap

/-- A version of `Set.pi` for submodules. Given an index set `I` and a family of submodules
`p : (i : ι) → Submodule R (φ i)`, `pi I s` is the submodule of dependent functions
`f : (i : ι) → φ i` such that `f i` belongs to `p a` whenever `i ∈ I`. -/
def pi (I : Set ι) (p : (i : ι) → Submodule R (φ i)) : Submodule R ((i : ι) → φ i) where
  carrier := Set.pi I fun i => p i
  zero_mem' i _ := (p i).zero_mem
  add_mem' {_ _} hx hy i hi := (p i).add_mem (hx i hi) (hy i hi)
  smul_mem' c _ hx i hi := (p i).smul_mem c (hx i hi)
#align submodule.pi Submodule.pi

variable {I : Set ι} {p q : (i : ι) → Submodule R (φ i)} {x : (i : ι) → φ i}

@[simp]
theorem mem_pi : x ∈ pi I p ↔ ∀ i ∈ I, x i ∈ p i :=
  Iff.rfl
#align submodule.mem_pi Submodule.mem_pi

@[simp, norm_cast]
theorem coe_pi : (pi I p : Set ((i : ι) → φ i)) = Set.pi I fun i => p i :=
  rfl
#align submodule.coe_pi Submodule.coe_pi

@[simp]
theorem pi_empty (p : (i : ι) → Submodule R (φ i)) : pi ∅ p = ⊤ :=
  SetLike.coe_injective <| Set.empty_pi _
#align submodule.pi_empty Submodule.pi_empty

@[simp]
theorem pi_top (s : Set ι) : (pi s fun i : ι => (⊤ : Submodule R (φ i))) = ⊤ :=
  SetLike.coe_injective <| Set.pi_univ _
#align submodule.pi_top Submodule.pi_top

theorem pi_mono {s : Set ι} (h : ∀ i ∈ s, p i ≤ q i) : pi s p ≤ pi s q :=
  Set.pi_mono h
#align submodule.pi_mono Submodule.pi_mono

theorem biInf_comap_proj :
    ⨅ i ∈ I, comap (proj i : ((i : ι) → φ i) →ₗ[R] φ i) (p i) = pi I p := by
  ext x
  -- ⊢ x ∈ ⨅ (i : ι) (_ : i ∈ I), comap (proj i) (p i) ↔ x ∈ pi I p
  simp
  -- 🎉 no goals
#align submodule.binfi_comap_proj Submodule.biInf_comap_proj

theorem iInf_comap_proj :
    ⨅ i, comap (proj i : ((i : ι) → φ i) →ₗ[R] φ i) (p i) = pi Set.univ p := by
  ext x
  -- ⊢ x ∈ ⨅ (i : ι), comap (proj i) (p i) ↔ x ∈ pi Set.univ p
  simp
  -- 🎉 no goals
#align submodule.infi_comap_proj Submodule.iInf_comap_proj

theorem iSup_map_single [DecidableEq ι] [Finite ι] :
    ⨆ i, map (LinearMap.single i : φ i →ₗ[R] (i : ι) → φ i) (p i) = pi Set.univ p := by
  cases nonempty_fintype ι
  -- ⊢ ⨆ (i : ι), map (single i) (p i) = pi Set.univ p
  refine' (iSup_le fun i => _).antisymm _
  -- ⊢ map (single i) (p i) ≤ pi Set.univ p
  · rintro _ ⟨x, hx : x ∈ p i, rfl⟩ j -
    -- ⊢ ↑(single i) x j ∈ (fun i => ↑(p i)) j
    rcases em (j = i) with (rfl | hj) <;> simp [*]
    -- ⊢ ↑(single j) x j ∈ (fun i => ↑(p i)) j
                                          -- 🎉 no goals
                                          -- 🎉 no goals
  · intro x hx
    -- ⊢ x ∈ ⨆ (i : ι), map (single i) (p i)
    rw [← Finset.univ_sum_single x]
    -- ⊢ ∑ i : ι, Pi.single i (x i) ∈ ⨆ (i : ι), map (single i) (p i)
    exact sum_mem_iSup fun i => mem_map_of_mem (hx i trivial)
    -- 🎉 no goals
#align submodule.supr_map_single Submodule.iSup_map_single

theorem le_comap_single_pi [DecidableEq ι] (p : (i : ι) → Submodule R (φ i)) {i} :
    p i ≤ Submodule.comap (LinearMap.single i : φ i →ₗ[R] _) (Submodule.pi Set.univ p) := by
  intro x hx
  -- ⊢ x ∈ comap (single i) (pi Set.univ p)
  rw [Submodule.mem_comap, Submodule.mem_pi]
  -- ⊢ ∀ (i_1 : ι), i_1 ∈ Set.univ → ↑(single i) x i_1 ∈ p i_1
  rintro j -
  -- ⊢ ↑(single i) x j ∈ p j
  by_cases h : j = i
  -- ⊢ ↑(single i) x j ∈ p j
  · rwa [h, LinearMap.coe_single, Pi.single_eq_same]
    -- 🎉 no goals
  · rw [LinearMap.coe_single, Pi.single_eq_of_ne h]
    -- ⊢ 0 ∈ p j
    exact (p j).zero_mem
    -- 🎉 no goals
#align submodule.le_comap_single_pi Submodule.le_comap_single_pi

end Submodule

namespace LinearEquiv

variable [Semiring R] {φ ψ χ : ι → Type*}

variable [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]

variable [(i : ι) → AddCommMonoid (ψ i)] [(i : ι) → Module R (ψ i)]

variable [(i : ι) → AddCommMonoid (χ i)] [(i : ι) → Module R (χ i)]

/-- Combine a family of linear equivalences into a linear equivalence of `pi`-types.

This is `Equiv.piCongrRight` as a `LinearEquiv` -/
def piCongrRight (e : (i : ι) → φ i ≃ₗ[R] ψ i) : ((i : ι) → φ i) ≃ₗ[R] (i : ι) → ψ i :=
  { AddEquiv.piCongrRight fun j => (e j).toAddEquiv with
    toFun := fun f i => e i (f i)
    invFun := fun f i => (e i).symm (f i)
    map_smul' := fun c f => by ext; simp }
                               -- ⊢ AddHom.toFun { toFun := fun f i => ↑(e i) (f i), map_add' := (_ : ∀ (x y : ( …
                                    -- 🎉 no goals
#align linear_equiv.Pi_congr_right LinearEquiv.piCongrRight

@[simp]
theorem piCongrRight_apply (e : (i : ι) → φ i ≃ₗ[R] ψ i) (f i) :
    piCongrRight e f i = e i (f i) := rfl
#align linear_equiv.Pi_congr_right_apply LinearEquiv.piCongrRight

@[simp]
theorem piCongrRight_refl : (piCongrRight fun j => refl R (φ j)) = refl _ _ :=
  rfl
#align linear_equiv.Pi_congr_right_refl LinearEquiv.piCongrRight_refl

@[simp]
theorem piCongrRight_symm (e : (i : ι) → φ i ≃ₗ[R] ψ i) :
    (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl
#align linear_equiv.Pi_congr_right_symm LinearEquiv.piCongrRight_symm

@[simp]
theorem piCongrRight_trans (e : (i : ι) → φ i ≃ₗ[R] ψ i) (f : (i : ι) → ψ i ≃ₗ[R] χ i) :
    (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).trans (f i) :=
  rfl
#align linear_equiv.Pi_congr_right_trans LinearEquiv.piCongrRight_trans

variable (R φ)

/-- Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as a `LinearEquiv`. -/
@[simps (config := { simpRhs := true })]
def piCongrLeft' (e : ι ≃ ι') : ((i' : ι) → φ i') ≃ₗ[R] (i : ι') → φ <| e.symm i :=
  { Equiv.piCongrLeft' φ e with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align linear_equiv.Pi_congr_left' LinearEquiv.piCongrLeft'

/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".

This is `Equiv.piCongrLeft` as a `LinearEquiv` -/
def piCongrLeft (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃ₗ[R] (i : ι) → φ i :=
  (piCongrLeft' R φ e.symm).symm
#align linear_equiv.Pi_congr_left LinearEquiv.piCongrLeft

/-- This is `Equiv.piOptionEquivProd` as a `LinearEquiv` -/
def piOptionEquivProd {ι : Type*} {M : Option ι → Type*} [(i : Option ι) → AddCommGroup (M i)]
    [(i : Option ι) → Module R (M i)] :
    ((i : Option ι) → M i) ≃ₗ[R] M none × ((i : ι) → M (some i)) :=
  { Equiv.piOptionEquivProd with
    map_add' := by simp [Function.funext_iff]
                   -- 🎉 no goals
    map_smul' := by simp [Function.funext_iff] }
                    -- 🎉 no goals
#align linear_equiv.pi_option_equiv_prod LinearEquiv.piOptionEquivProd

variable (ι M) (S : Type*) [Fintype ι] [DecidableEq ι] [Semiring S] [AddCommMonoid M]
  [Module R M] [Module S M] [SMulCommClass R S M]

/-- Linear equivalence between linear functions `Rⁿ → M` and `Mⁿ`. The spaces `Rⁿ` and `Mⁿ`
are represented as `ι → R` and `ι → M`, respectively, where `ι` is a finite type.

This as an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings]. -/
def piRing : ((ι → R) →ₗ[R] M) ≃ₗ[S] ι → M :=
  (LinearMap.lsum R (fun _ : ι => R) S).symm.trans
    (piCongrRight fun _ => LinearMap.ringLmapEquivSelf R S M)
#align linear_equiv.pi_ring LinearEquiv.piRing

variable {ι R M}

@[simp]
theorem piRing_apply (f : (ι → R) →ₗ[R] M) (i : ι) : piRing R M ι S f i = f (Pi.single i 1) :=
  rfl
#align linear_equiv.pi_ring_apply LinearEquiv.piRing_apply

@[simp]
theorem piRing_symm_apply (f : ι → M) (g : ι → R) : (piRing R M ι S).symm f g = ∑ i, g i • f i := by
  simp [piRing, LinearMap.lsum_apply]
  -- 🎉 no goals
#align linear_equiv.pi_ring_symm_apply LinearEquiv.piRing_symm_apply

-- TODO additive version?
/-- `Equiv.sumArrowEquivProdArrow` as a linear equivalence.
-/
def sumArrowLequivProdArrow (α β R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :
    (Sum α β → M) ≃ₗ[R] (α → M) × (β → M) :=
  { Equiv.sumArrowEquivProdArrow α β
      M with
    map_add' := by
      intro f g
      -- ⊢ Equiv.toFun src✝ (f + g) = Equiv.toFun src✝ f + Equiv.toFun src✝ g
      ext <;> rfl
      -- ⊢ Prod.fst (Equiv.toFun src✝ (f + g)) x✝ = Prod.fst (Equiv.toFun src✝ f + Equi …
              -- 🎉 no goals
              -- 🎉 no goals
    map_smul' := by
      intro r f
      -- ⊢ AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (f g : α ⊕ β → M), Eq …
      ext <;> rfl }
      -- ⊢ Prod.fst (AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (f g : α ⊕  …
              -- 🎉 no goals
              -- 🎉 no goals
#align linear_equiv.sum_arrow_lequiv_prod_arrow LinearEquiv.sumArrowLequivProdArrow

@[simp]
theorem sumArrowLequivProdArrow_apply_fst {α β} (f : Sum α β → M) (a : α) :
    (sumArrowLequivProdArrow α β R M f).1 a = f (Sum.inl a) :=
  rfl
#align linear_equiv.sum_arrow_lequiv_prod_arrow_apply_fst LinearEquiv.sumArrowLequivProdArrow_apply_fst

@[simp]
theorem sumArrowLequivProdArrow_apply_snd {α β} (f : Sum α β → M) (b : β) :
    (sumArrowLequivProdArrow α β R M f).2 b = f (Sum.inr b) :=
  rfl
#align linear_equiv.sum_arrow_lequiv_prod_arrow_apply_snd LinearEquiv.sumArrowLequivProdArrow_apply_snd

@[simp]
theorem sumArrowLequivProdArrow_symm_apply_inl {α β} (f : α → M) (g : β → M) (a : α) :
    ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inl a) = f a :=
  rfl
#align linear_equiv.sum_arrow_lequiv_prod_arrow_symm_apply_inl LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl

@[simp]
theorem sumArrowLequivProdArrow_symm_apply_inr {α β} (f : α → M) (g : β → M) (b : β) :
    ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inr b) = g b :=
  rfl
#align linear_equiv.sum_arrow_lequiv_prod_arrow_symm_apply_inr LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr

/-- If `ι` has a unique element, then `ι → M` is linearly equivalent to `M`. -/
@[simps (config :=
      { simpRhs := true
        fullyApplied := false }) symm_apply]
def funUnique (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M] :
    (ι → M) ≃ₗ[R] M :=
  { Equiv.funUnique ι M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align linear_equiv.fun_unique LinearEquiv.funUnique
#align linear_equiv.fun_unique_symm_apply LinearEquiv.funUnique_symm_apply

@[simp]
theorem funUnique_apply (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M] :
    (funUnique ι R M : (ι → M) → M) = eval default := rfl
#align linear_equiv.fun_unique_apply LinearEquiv.funUnique_apply

variable (R M)

/-- Linear equivalence between dependent functions `(i : Fin 2) → M i` and `M 0 × M 1`. -/
@[simps (config :=
      { simpRhs := true
        fullyApplied := false }) symm_apply]
def piFinTwo (M : Fin 2 → Type v)
    [(i : Fin 2) → AddCommMonoid (M i)] [(i : Fin 2) → Module R (M i)] :
    ((i : Fin 2) → M i) ≃ₗ[R] M 0 × M 1 :=
  { piFinTwoEquiv M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align linear_equiv.pi_fin_two LinearEquiv.piFinTwo
#align linear_equiv.pi_fin_two_symm_apply LinearEquiv.piFinTwo_symm_apply

@[simp]
theorem piFinTwo_apply (M : Fin 2 → Type v)
    [(i : Fin 2) → AddCommMonoid (M i)] [(i : Fin 2) → Module R (M i)] :
    (piFinTwo R M : ((i : Fin 2) → M i) → M 0 × M 1) = fun f => (f 0, f 1) := rfl
#align linear_equiv.pi_fin_two_apply LinearEquiv.piFinTwo_apply

/-- Linear equivalence between vectors in `M² = Fin 2 → M` and `M × M`. -/
@[simps! (config := .asFn)]
def finTwoArrow : (Fin 2 → M) ≃ₗ[R] M × M :=
  { finTwoArrowEquiv M, piFinTwo R fun _ => M with }
#align linear_equiv.fin_two_arrow LinearEquiv.finTwoArrow

end LinearEquiv

section Extend

variable (R) {η : Type x} [Semiring R] (s : ι → η)

/-- `Function.extend s f 0` as a bundled linear map. -/
@[simps]
noncomputable def Function.ExtendByZero.linearMap : (ι → R) →ₗ[R] η → R :=
  { Function.ExtendByZero.hom R s with
    toFun := fun f => Function.extend s f 0
    map_smul' := fun r f => by simpa using Function.extend_smul r s f 0 }
                               -- 🎉 no goals
#align function.extend_by_zero.linear_map Function.ExtendByZero.linearMap

end Extend

/-! ### Bundled versions of `Matrix.vecCons` and `Matrix.vecEmpty`

The idea of these definitions is to be able to define a map as `x ↦ ![f₁ x, f₂ x, f₃ x]`, where
`f₁ f₂ f₃` are already linear maps, as `f₁.vecCons $ f₂.vecCons $ f₃.vecCons $ vecEmpty`.

While the same thing could be achieved using `LinearMap.pi ![f₁, f₂, f₃]`, this is not
definitionally equal to the result using `LinearMap.vecCons`, as `Fin.cases` and function
application do not commute definitionally.

Versions for when `f₁ f₂ f₃` are bilinear maps are also provided.

-/


section Fin

section Semiring

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

/-- The linear map defeq to `Matrix.vecEmpty` -/
def LinearMap.vecEmpty : M →ₗ[R] Fin 0 → M₃ where
  toFun _ := Matrix.vecEmpty
  map_add' _ _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _
#align linear_map.vec_empty LinearMap.vecEmpty

@[simp]
theorem LinearMap.vecEmpty_apply (m : M) : (LinearMap.vecEmpty : M →ₗ[R] Fin 0 → M₃) m = ![] :=
  rfl
#align linear_map.vec_empty_apply LinearMap.vecEmpty_apply

/-- A linear map into `Fin n.succ → M₃` can be built out of a map into `M₃` and a map into
`Fin n → M₃`. -/
def LinearMap.vecCons {n} (f : M →ₗ[R] M₂) (g : M →ₗ[R] Fin n → M₂) : M →ₗ[R] Fin n.succ → M₂ where
  toFun m := Matrix.vecCons (f m) (g m)
  map_add' x y := by
    simp only []
    -- ⊢ Matrix.vecCons (↑f (x + y)) (↑g (x + y)) = Matrix.vecCons (↑f x) (↑g x) + Ma …
    rw [f.map_add, g.map_add, Matrix.cons_add_cons (f x)]
    -- 🎉 no goals
  map_smul' c x := by
    simp only []
    -- ⊢ Matrix.vecCons (↑f (c • x)) (↑g (c • x)) = ↑(RingHom.id R) c • Matrix.vecCon …
    rw [f.map_smul, g.map_smul, RingHom.id_apply, Matrix.smul_cons c (f x)]
    -- 🎉 no goals
#align linear_map.vec_cons LinearMap.vecCons

@[simp]
theorem LinearMap.vecCons_apply {n} (f : M →ₗ[R] M₂) (g : M →ₗ[R] Fin n → M₂) (m : M) :
    f.vecCons g m = Matrix.vecCons (f m) (g m) :=
  rfl
#align linear_map.vec_cons_apply LinearMap.vecCons_apply

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

/-- The empty bilinear map defeq to `Matrix.vecEmpty` -/
@[simps]
def LinearMap.vecEmpty₂ : M →ₗ[R] M₂ →ₗ[R] Fin 0 → M₃ where
  toFun _ := LinearMap.vecEmpty
  map_add' _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _
  map_smul' _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _
#align linear_map.vec_empty₂ LinearMap.vecEmpty₂

/-- A bilinear map into `Fin n.succ → M₃` can be built out of a map into `M₃` and a map into
`Fin n → M₃` -/
@[simps]
def LinearMap.vecCons₂ {n} (f : M →ₗ[R] M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂ →ₗ[R] Fin n → M₃) :
    M →ₗ[R] M₂ →ₗ[R] Fin n.succ → M₃ where
  toFun m := LinearMap.vecCons (f m) (g m)
  map_add' x y :=
    LinearMap.ext fun z => by
      simp only [f.map_add, g.map_add, LinearMap.add_apply, LinearMap.vecCons_apply,
        Matrix.cons_add_cons (f x z)]
  map_smul' r x := LinearMap.ext fun z => by simp [Matrix.smul_cons r (f x z)]
                                             -- 🎉 no goals
#align linear_map.vec_cons₂ LinearMap.vecCons₂

end CommSemiring

end Fin
