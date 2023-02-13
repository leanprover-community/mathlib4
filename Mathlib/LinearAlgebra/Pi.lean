/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.pi
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Basic
import Mathbin.Logic.Equiv.Fin

/-!
# Pi types of modules

This file defines constructors for linear maps whose domains or codomains are pi types.

It contains theorems relating these to each other, as well as to `linear_map.ker`.

## Main definitions

- pi types in the codomain:
  - `linear_map.pi`
  - `linear_map.single`
- pi types in the domain:
  - `linear_map.proj`
- `linear_map.diag`

-/


universe u v w x y z u' v' w' x' y'

variable {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}

variable {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x} {ι' : Type x'}

open Function Submodule

open BigOperators

namespace LinearMap

universe i

variable [Semiring R] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]
  {φ : ι → Type i} [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

/-- `pi` construction for linear functions. From a family of linear functions it produces a linear
function into a family of modules. -/
def pi (f : ∀ i, M₂ →ₗ[R] φ i) : M₂ →ₗ[R] ∀ i, φ i :=
  {
    Pi.addHom fun i => (f i).toAddHom with
    toFun := fun c i => f i c
    map_smul' := fun c d => funext fun i => (f i).map_smul _ _ }
#align linear_map.pi LinearMap.pi

@[simp]
theorem pi_apply (f : ∀ i, M₂ →ₗ[R] φ i) (c : M₂) (i : ι) : pi f c i = f i c :=
  rfl
#align linear_map.pi_apply LinearMap.pi_apply

theorem ker_pi (f : ∀ i, M₂ →ₗ[R] φ i) : ker (pi f) = ⨅ i : ι, ker (f i) := by
  ext c <;> simp [funext_iff] <;> rfl
#align linear_map.ker_pi LinearMap.ker_pi

theorem pi_eq_zero (f : ∀ i, M₂ →ₗ[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 := by
  simp only [LinearMap.ext_iff, pi_apply, funext_iff] <;>
    exact ⟨fun h a b => h b a, fun h a b => h b a⟩
#align linear_map.pi_eq_zero LinearMap.pi_eq_zero

theorem pi_zero : pi (fun i => 0 : ∀ i, M₂ →ₗ[R] φ i) = 0 := by ext <;> rfl
#align linear_map.pi_zero LinearMap.pi_zero

theorem pi_comp (f : ∀ i, M₂ →ₗ[R] φ i) (g : M₃ →ₗ[R] M₂) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl
#align linear_map.pi_comp LinearMap.pi_comp

/-- The projections from a family of modules are linear maps.

Note:  known here as `linear_map.proj`, this construction is in other categories called `eval`, for
example `pi.eval_monoid_hom`, `pi.eval_ring_hom`. -/
def proj (i : ι) : (∀ i, φ i) →ₗ[R] φ i
    where
  toFun := Function.eval i
  map_add' f g := rfl
  map_smul' c f := rfl
#align linear_map.proj LinearMap.proj

@[simp]
theorem coe_proj (i : ι) : ⇑(proj i : (∀ i, φ i) →ₗ[R] φ i) = Function.eval i :=
  rfl
#align linear_map.coe_proj LinearMap.coe_proj

theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →ₗ[R] φ i) b = b i :=
  rfl
#align linear_map.proj_apply LinearMap.proj_apply

theorem proj_pi (f : ∀ i, M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
  ext fun c => rfl
#align linear_map.proj_pi LinearMap.proj_pi

theorem infᵢ_ker_proj : (⨅ i, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) : Submodule R (∀ i, φ i)) = ⊥ :=
  bot_unique <|
    SetLike.le_def.2 fun a h =>
      by
      simp only [mem_infi, mem_ker, proj_apply] at h
      exact (mem_bot _).2 (funext fun i => h i)
#align linear_map.infi_ker_proj LinearMap.infᵢ_ker_proj

/-- Linear map between the function spaces `I → M₂` and `I → M₃`, induced by a linear map `f`
between `M₂` and `M₃`. -/
@[simps]
protected def compLeft (f : M₂ →ₗ[R] M₃) (I : Type _) : (I → M₂) →ₗ[R] I → M₃ :=
  { f.toAddMonoidHom.compLeft I with
    toFun := fun h => f ∘ h
    map_smul' := fun c h => by
      ext x
      exact f.map_smul' c (h x) }
#align linear_map.comp_left LinearMap.compLeft

theorem apply_single [AddCommMonoid M] [Module R M] [DecidableEq ι] (f : ∀ i, φ i →ₗ[R] M) (i j : ι)
    (x : φ i) : f j (Pi.single i x j) = Pi.single i (f i x) j :=
  Pi.apply_single (fun i => f i) (fun i => (f i).map_zero) _ _ _
#align linear_map.apply_single LinearMap.apply_single

/-- The `linear_map` version of `add_monoid_hom.single` and `pi.single`. -/
def single [DecidableEq ι] (i : ι) : φ i →ₗ[R] ∀ i, φ i :=
  { AddMonoidHom.single φ i with
    toFun := Pi.single i
    map_smul' := Pi.single_smul i }
#align linear_map.single LinearMap.single

@[simp]
theorem coe_single [DecidableEq ι] (i : ι) : ⇑(single i : φ i →ₗ[R] ∀ i, φ i) = Pi.single i :=
  rfl
#align linear_map.coe_single LinearMap.coe_single

variable (R φ)

/-- The linear equivalence between linear functions on a finite product of modules and
families of functions on these modules. See note [bundled maps over different rings]. -/
@[simps]
def lsum (S) [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι] [Semiring S] [Module S M]
    [SMulCommClass R S M] : (∀ i, φ i →ₗ[R] M) ≃ₗ[S] (∀ i, φ i) →ₗ[R] M
    where
  toFun f := ∑ i : ι, (f i).comp (proj i)
  invFun f i := f.comp (single i)
  map_add' f g := by simp only [Pi.add_apply, add_comp, Finset.sum_add_distrib]
  map_smul' c f := by simp only [Pi.smul_apply, smul_comp, Finset.smul_sum, RingHom.id_apply]
  left_inv f := by
    ext (i x)
    simp [apply_single]
  right_inv f := by
    ext
    suffices f (∑ j, Pi.single j (x j)) = f x by simpa [apply_single]
    rw [Finset.univ_sum_single]
#align linear_map.lsum LinearMap.lsum

@[simp]
theorem lsum_single {ι R : Type _} [Fintype ι] [DecidableEq ι] [CommRing R] {M : ι → Type _}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    LinearMap.lsum R M R LinearMap.single = LinearMap.id :=
  LinearMap.ext fun x => by simp [Finset.univ_sum_single]
#align linear_map.lsum_single LinearMap.lsum_single

variable {R φ}

section Ext

variable [Finite ι] [DecidableEq ι] [AddCommMonoid M] [Module R M] {f g : (∀ i, φ i) →ₗ[R] M}

theorem pi_ext (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) : f = g :=
  toAddMonoidHom_injective <| AddMonoidHom.functions_ext _ _ _ h
#align linear_map.pi_ext LinearMap.pi_ext

theorem pi_ext_iff : f = g ↔ ∀ i x, f (Pi.single i x) = g (Pi.single i x) :=
  ⟨fun h i x => h ▸ rfl, pi_ext⟩
#align linear_map.pi_ext_iff LinearMap.pi_ext_iff

/-- This is used as the ext lemma instead of `linear_map.pi_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[ext]
theorem pi_ext' (h : ∀ i, f.comp (single i) = g.comp (single i)) : f = g :=
  by
  refine' pi_ext fun i x => _
  convert LinearMap.congr_fun (h i) x
#align linear_map.pi_ext' LinearMap.pi_ext'

theorem pi_ext'_iff : f = g ↔ ∀ i, f.comp (single i) = g.comp (single i) :=
  ⟨fun h i => h ▸ rfl, pi_ext'⟩
#align linear_map.pi_ext'_iff LinearMap.pi_ext'_iff

end Ext

section

variable (R φ)

/-- If `I` and `J` are disjoint index sets, the product of the kernels of the `J`th projections of
`φ` is linearly equivalent to the product over `I`. -/
def infiKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) : Submodule R (∀ i, φ i)) ≃ₗ[R] ∀ i : I, φ i :=
  by
  refine'
    LinearEquiv.ofLinear (pi fun i => (proj (i : ι)).comp (Submodule.subtype _))
      (cod_restrict _ (pi fun i => if h : i ∈ I then proj (⟨i, h⟩ : I) else 0) _) _ _
  · intro b
    simp only [mem_infi, mem_ker, funext_iff, proj_apply, pi_apply]
    intro j hjJ
    have : j ∉ I := fun hjI => hd.le_bot ⟨hjI, hjJ⟩
    rw [dif_neg this, zero_apply]
  · simp only [pi_comp, comp_assoc, subtype_comp_cod_restrict, proj_pi, Subtype.coe_prop]
    ext (b⟨j, hj⟩)
    simp only [dif_pos, Function.comp_apply, Function.eval_apply, LinearMap.codRestrict_apply,
      LinearMap.coe_comp, LinearMap.coe_proj, LinearMap.pi_apply, Submodule.subtype_apply,
      Subtype.coe_prop]
    rfl
  · ext1 ⟨b, hb⟩
    apply Subtype.ext
    ext j
    have hb : ∀ i ∈ J, b i = 0 := by
      simpa only [mem_infi, mem_ker, proj_apply] using (mem_infi _).1 hb
    simp only [comp_apply, pi_apply, id_apply, proj_apply, subtype_apply, cod_restrict_apply]
    split_ifs
    · rfl
    · exact (hb _ <| (hu trivial).resolve_left h).symm
#align linear_map.infi_ker_proj_equiv LinearMap.infiKerProjEquiv

end

section

variable [DecidableEq ι]

/-- `diag i j` is the identity map if `i = j`. Otherwise it is the constant 0 map. -/
def diag (i j : ι) : φ i →ₗ[R] φ j :=
  @Function.update ι (fun j => φ i →ₗ[R] φ j) _ 0 i id j
#align linear_map.diag LinearMap.diag

theorem update_apply (f : ∀ i, M₂ →ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ →ₗ[R] φ i) :
    (update f i b j) c = update (fun i => f i c) i (b c) j :=
  by
  by_cases j = i
  · rw [h, update_same, update_same]
  · rw [update_noteq h, update_noteq h]
#align linear_map.update_apply LinearMap.update_apply

end

end LinearMap

namespace Submodule

variable [Semiring R] {φ : ι → Type _} [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

open LinearMap

/-- A version of `set.pi` for submodules. Given an index set `I` and a family of submodules
`p : Π i, submodule R (φ i)`, `pi I s` is the submodule of dependent functions `f : Π i, φ i`
such that `f i` belongs to `p a` whenever `i ∈ I`. -/
def pi (I : Set ι) (p : ∀ i, Submodule R (φ i)) : Submodule R (∀ i, φ i)
    where
  carrier := Set.pi I fun i => p i
  zero_mem' i hi := (p i).zero_mem
  add_mem' x y hx hy i hi := (p i).add_mem (hx i hi) (hy i hi)
  smul_mem' c x hx i hi := (p i).smul_mem c (hx i hi)
#align submodule.pi Submodule.pi

variable {I : Set ι} {p q : ∀ i, Submodule R (φ i)} {x : ∀ i, φ i}

@[simp]
theorem mem_pi : x ∈ pi I p ↔ ∀ i ∈ I, x i ∈ p i :=
  Iff.rfl
#align submodule.mem_pi Submodule.mem_pi

@[simp, norm_cast]
theorem coe_pi : (pi I p : Set (∀ i, φ i)) = Set.pi I fun i => p i :=
  rfl
#align submodule.coe_pi Submodule.coe_pi

@[simp]
theorem pi_empty (p : ∀ i, Submodule R (φ i)) : pi ∅ p = ⊤ :=
  SetLike.coe_injective <| Set.empty_pi _
#align submodule.pi_empty Submodule.pi_empty

@[simp]
theorem pi_top (s : Set ι) : (pi s fun i : ι => (⊤ : Submodule R (φ i))) = ⊤ :=
  SetLike.coe_injective <| Set.pi_univ _
#align submodule.pi_top Submodule.pi_top

theorem pi_mono {s : Set ι} (h : ∀ i ∈ s, p i ≤ q i) : pi s p ≤ pi s q :=
  Set.pi_mono h
#align submodule.pi_mono Submodule.pi_mono

theorem binfi_comap_proj : (⨅ i ∈ I, comap (proj i : (∀ i, φ i) →ₗ[R] φ i) (p i)) = pi I p :=
  by
  ext x
  simp
#align submodule.binfi_comap_proj Submodule.binfi_comap_proj

theorem infᵢ_comap_proj : (⨅ i, comap (proj i : (∀ i, φ i) →ₗ[R] φ i) (p i)) = pi Set.univ p :=
  by
  ext x
  simp
#align submodule.infi_comap_proj Submodule.infᵢ_comap_proj

theorem supᵢ_map_single [DecidableEq ι] [Finite ι] :
    (⨆ i, map (LinearMap.single i : φ i →ₗ[R] ∀ i, φ i) (p i)) = pi Set.univ p :=
  by
  cases nonempty_fintype ι
  refine' (supᵢ_le fun i => _).antisymm _
  · rintro _ ⟨x, hx : x ∈ p i, rfl⟩ j -
    rcases em (j = i) with (rfl | hj) <;> simp [*]
  · intro x hx
    rw [← Finset.univ_sum_single x]
    exact sum_mem_supr fun i => mem_map_of_mem (hx i trivial)
#align submodule.supr_map_single Submodule.supᵢ_map_single

theorem le_comap_single_pi [DecidableEq ι] (p : ∀ i, Submodule R (φ i)) {i} :
    p i ≤ Submodule.comap (LinearMap.single i : φ i →ₗ[R] _) (Submodule.pi Set.univ p) :=
  by
  intro x hx
  rw [Submodule.mem_comap, Submodule.mem_pi]
  rintro j -
  by_cases h : j = i
  · rwa [h, LinearMap.coe_single, Pi.single_eq_same]
  · rw [LinearMap.coe_single, Pi.single_eq_of_ne h]
    exact (p j).zero_mem
#align submodule.le_comap_single_pi Submodule.le_comap_single_pi

end Submodule

namespace LinearEquiv

variable [Semiring R] {φ ψ χ : ι → Type _} [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

variable [∀ i, AddCommMonoid (ψ i)] [∀ i, Module R (ψ i)]

variable [∀ i, AddCommMonoid (χ i)] [∀ i, Module R (χ i)]

/-- Combine a family of linear equivalences into a linear equivalence of `pi`-types.

This is `equiv.Pi_congr_right` as a `linear_equiv` -/
@[simps apply]
def piCongrRight (e : ∀ i, φ i ≃ₗ[R] ψ i) : (∀ i, φ i) ≃ₗ[R] ∀ i, ψ i :=
  {
    AddEquiv.piCongrRight fun j =>
      (e j).toAddEquiv with
    toFun := fun f i => e i (f i)
    invFun := fun f i => (e i).symm (f i)
    map_smul' := fun c f => by
      ext
      simp }
#align linear_equiv.Pi_congr_right LinearEquiv.piCongrRight

@[simp]
theorem piCongrRight_refl : (piCongrRight fun j => refl R (φ j)) = refl _ _ :=
  rfl
#align linear_equiv.Pi_congr_right_refl LinearEquiv.piCongrRight_refl

@[simp]
theorem piCongrRight_symm (e : ∀ i, φ i ≃ₗ[R] ψ i) :
    (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl
#align linear_equiv.Pi_congr_right_symm LinearEquiv.piCongrRight_symm

@[simp]
theorem piCongrRight_trans (e : ∀ i, φ i ≃ₗ[R] ψ i) (f : ∀ i, ψ i ≃ₗ[R] χ i) :
    (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).trans (f i) :=
  rfl
#align linear_equiv.Pi_congr_right_trans LinearEquiv.piCongrRight_trans

variable (R φ)

/-- Transport dependent functions through an equivalence of the base space.

This is `equiv.Pi_congr_left'` as a `linear_equiv`. -/
@[simps (config := { simpRhs := true })]
def piCongrLeft' (e : ι ≃ ι') : (∀ i', φ i') ≃ₗ[R] ∀ i, φ <| e.symm i :=
  { Equiv.piCongrLeft' φ e with
    map_add' := fun x y => rfl
    map_smul' := fun x y => rfl }
#align linear_equiv.Pi_congr_left' LinearEquiv.piCongrLeft'

/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".

This is `equiv.Pi_congr_left` as a `linear_equiv` -/
def piCongrLeft (e : ι' ≃ ι) : (∀ i', φ (e i')) ≃ₗ[R] ∀ i, φ i :=
  (piCongrLeft' R φ e.symm).symm
#align linear_equiv.Pi_congr_left LinearEquiv.piCongrLeft

/-- This is `equiv.pi_option_equiv_prod` as a `linear_equiv` -/
def piOptionEquivProd {ι : Type _} {M : Option ι → Type _} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] : (∀ i : Option ι, M i) ≃ₗ[R] M none × ∀ i : ι, M (some i) :=
  { Equiv.piOptionEquivProd with
    map_add' := by simp [Function.funext_iff]
    map_smul' := by simp [Function.funext_iff] }
#align linear_equiv.pi_option_equiv_prod LinearEquiv.piOptionEquivProd

variable (ι R M) (S : Type _) [Fintype ι] [DecidableEq ι] [Semiring S] [AddCommMonoid M]
  [Module R M] [Module S M] [SMulCommClass R S M]

/-- Linear equivalence between linear functions `Rⁿ → M` and `Mⁿ`. The spaces `Rⁿ` and `Mⁿ`
are represented as `ι → R` and `ι → M`, respectively, where `ι` is a finite type.

This as an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings]. -/
def piRing : ((ι → R) →ₗ[R] M) ≃ₗ[S] ι → M :=
  (LinearMap.lsum R (fun i : ι => R) S).symm.trans
    (piCongrRight fun i => LinearMap.ringLmapEquivSelf R S M)
#align linear_equiv.pi_ring LinearEquiv.piRing

variable {ι R M}

@[simp]
theorem piRing_apply (f : (ι → R) →ₗ[R] M) (i : ι) : piRing R M ι S f i = f (Pi.single i 1) :=
  rfl
#align linear_equiv.pi_ring_apply LinearEquiv.piRing_apply

@[simp]
theorem piRing_symm_apply (f : ι → M) (g : ι → R) : (piRing R M ι S).symm f g = ∑ i, g i • f i := by
  simp [pi_ring, LinearMap.lsum]
#align linear_equiv.pi_ring_symm_apply LinearEquiv.piRing_symm_apply

-- TODO additive version?
/-- `equiv.sum_arrow_equiv_prod_arrow` as a linear equivalence.
-/
def sumArrowLequivProdArrow (α β R M : Type _) [Semiring R] [AddCommMonoid M] [Module R M] :
    (Sum α β → M) ≃ₗ[R] (α → M) × (β → M) :=
  {
    Equiv.sumArrowEquivProdArrow α β
      M with
    map_add' := by
      intro f g
      ext <;> rfl
    map_smul' := by
      intro r f
      ext <;> rfl }
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
        fullyApplied := false })]
def funUnique (ι R M : Type _) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M] :
    (ι → M) ≃ₗ[R] M :=
  { Equiv.funUnique ι M with
    map_add' := fun f g => rfl
    map_smul' := fun c f => rfl }
#align linear_equiv.fun_unique LinearEquiv.funUnique

variable (R M)

/-- Linear equivalence between dependent functions `Π i : fin 2, M i` and `M 0 × M 1`. -/
@[simps (config :=
      { simpRhs := true
        fullyApplied := false })]
def piFinTwo (M : Fin 2 → Type v) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    (∀ i, M i) ≃ₗ[R] M 0 × M 1 :=
  { piFinTwoEquiv M with
    map_add' := fun f g => rfl
    map_smul' := fun c f => rfl }
#align linear_equiv.pi_fin_two LinearEquiv.piFinTwo

/-- Linear equivalence between vectors in `M² = fin 2 → M` and `M × M`. -/
@[simps (config :=
      { simpRhs := true
        fullyApplied := false })]
def finTwoArrow : (Fin 2 → M) ≃ₗ[R] M × M :=
  { finTwoArrowEquiv M, piFinTwo R fun _ => M with }
#align linear_equiv.fin_two_arrow LinearEquiv.finTwoArrow

end LinearEquiv

section Extend

variable (R) {η : Type x} [Semiring R] (s : ι → η)

/-- `function.extend s f 0` as a bundled linear map. -/
@[simps]
noncomputable def Function.ExtendByZero.linearMap : (ι → R) →ₗ[R] η → R :=
  {
    Function.ExtendByZero.hom R
      s with
    toFun := fun f => Function.extend s f 0
    map_smul' := fun r f => by simpa using Function.extend_smul r s f 0 }
#align function.extend_by_zero.linear_map Function.ExtendByZero.linearMap

end Extend

/-! ### Bundled versions of `matrix.vec_cons` and `matrix.vec_empty`

The idea of these definitions is to be able to define a map as `x ↦ ![f₁ x, f₂ x, f₃ x]`, where
`f₁ f₂ f₃` are already linear maps, as `f₁.vec_cons $ f₂.vec_cons $ f₃.vec_cons $ vec_empty`.

While the same thing could be achieved using `linear_map.pi ![f₁, f₂, f₃]`, this is not
definitionally equal to the result using `linear_map.vec_cons`, as `fin.cases` and function
application do not commute definitionally.

Versions for when `f₁ f₂ f₃` are bilinear maps are also provided.

-/


section Fin

section Semiring

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

/-- The linear map defeq to `matrix.vec_empty` -/
def LinearMap.vecEmpty : M →ₗ[R] Fin 0 → M₃
    where
  toFun m := Matrix.vecEmpty
  map_add' x y := Subsingleton.elim _ _
  map_smul' r x := Subsingleton.elim _ _
#align linear_map.vec_empty LinearMap.vecEmpty

@[simp]
theorem LinearMap.vecEmpty_apply (m : M) : (LinearMap.vecEmpty : M →ₗ[R] Fin 0 → M₃) m = ![] :=
  rfl
#align linear_map.vec_empty_apply LinearMap.vecEmpty_apply

/-- A linear map into `fin n.succ → M₃` can be built out of a map into `M₃` and a map into
`fin n → M₃`. -/
def LinearMap.vecCons {n} (f : M →ₗ[R] M₂) (g : M →ₗ[R] Fin n → M₂) : M →ₗ[R] Fin n.succ → M₂
    where
  toFun m := Matrix.vecCons (f m) (g m)
  map_add' x y := by rw [f.map_add, g.map_add, Matrix.cons_add_cons (f x)]
  map_smul' c x := by rw [f.map_smul, g.map_smul, RingHom.id_apply, Matrix.smul_cons c (f x)]
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

/-- The empty bilinear map defeq to `matrix.vec_empty` -/
@[simps]
def LinearMap.vecEmpty₂ : M →ₗ[R] M₂ →ₗ[R] Fin 0 → M₃
    where
  toFun m := LinearMap.vecEmpty
  map_add' x y := LinearMap.ext fun z => Subsingleton.elim _ _
  map_smul' r x := LinearMap.ext fun z => Subsingleton.elim _ _
#align linear_map.vec_empty₂ LinearMap.vecEmpty₂

/-- A bilinear map into `fin n.succ → M₃` can be built out of a map into `M₃` and a map into
`fin n → M₃` -/
@[simps]
def LinearMap.vecCons₂ {n} (f : M →ₗ[R] M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂ →ₗ[R] Fin n → M₃) :
    M →ₗ[R] M₂ →ₗ[R] Fin n.succ → M₃
    where
  toFun m := LinearMap.vecCons (f m) (g m)
  map_add' x y :=
    LinearMap.ext fun z => by
      simp only [f.map_add, g.map_add, LinearMap.add_apply, LinearMap.vecCons_apply,
        Matrix.cons_add_cons (f x z)]
  map_smul' r x := LinearMap.ext fun z => by simp [Matrix.smul_cons r (f x z)]
#align linear_map.vec_cons₂ LinearMap.vecCons₂

end CommSemiring

end Fin

