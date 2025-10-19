/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser
-/
import Mathlib.Algebra.Group.Fin.Tuple
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Fintype.Option

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

@[simp]
theorem pi_apply (f : (i : ι) → M₂ →ₗ[R] φ i) (c : M₂) (i : ι) : pi f c i = f i c :=
  rfl

theorem ker_pi (f : (i : ι) → M₂ →ₗ[R] φ i) : ker (pi f) = ⨅ i : ι, ker (f i) := by
  ext c; simp [funext_iff]

theorem pi_eq_zero (f : (i : ι) → M₂ →ₗ[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 := by
  simp only [LinearMap.ext_iff, pi_apply, funext_iff]
  exact ⟨fun h a b => h b a, fun h a b => h b a⟩

theorem pi_zero : pi (fun _ => 0 : (i : ι) → M₂ →ₗ[R] φ i) = 0 := by ext; rfl

theorem pi_comp (f : (i : ι) → M₂ →ₗ[R] φ i) (g : M₃ →ₗ[R] M₂) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

/-- The constant linear map, taking `x` to `Function.const ι x`. -/
def const : M₂ →ₗ[R] (ι → M₂) := pi fun _ ↦ .id

@[simp] lemma const_apply (x : M₂) : LinearMap.const (R := R) x = Function.const ι x := rfl

/-- The projections from a family of modules are linear maps.

Note: this definition would be called `Pi.evalLinearMap` if we followed the pattern established by
`Pi.evalAddHom`, `Pi.evalMonoidHom`, `Pi.evalRingHom`, ... -/
def proj (i : ι) : ((i : ι) → φ i) →ₗ[R] φ i where
  toFun := Function.eval i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_proj (i : ι) : ⇑(proj i : ((i : ι) → φ i) →ₗ[R] φ i) = Function.eval i :=
  rfl

@[simp]
theorem toAddMonoidHom_proj (i : ι) : (proj i).toAddMonoidHom (R := R) = Pi.evalAddMonoidHom φ i :=
  rfl

theorem proj_apply (i : ι) (b : (i : ι) → φ i) : (proj i : ((i : ι) → φ i) →ₗ[R] φ i) b = b i :=
  rfl

@[simp]
theorem proj_pi (f : (i : ι) → M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i := rfl

@[simp]
theorem pi_proj : pi proj = LinearMap.id (R := R) (M := ∀ i, φ i) := rfl

@[simp]
theorem pi_proj_comp (f : M₂ →ₗ[R] ∀ i, φ i) : pi (proj · ∘ₗ f) = f := rfl

theorem proj_surjective (i : ι) : Surjective (proj i : ((i : ι) → φ i) →ₗ[R] φ i) :=
  surjective_eval i

theorem iInf_ker_proj : (⨅ i, ker (proj i : ((i : ι) → φ i) →ₗ[R] φ i) :
    Submodule R ((i : ι) → φ i)) = ⊥ :=
  bot_unique <|
    SetLike.le_def.2 fun a h => by
      simp only [mem_iInf, mem_ker, proj_apply] at h
      exact (mem_bot _).2 (funext fun i => h i)

instance CompatibleSMul.pi (R S M N ι : Type*) [Semiring S]
    [AddCommMonoid M] [AddCommMonoid N] [SMul R M] [SMul R N] [Module S M] [Module S N]
    [LinearMap.CompatibleSMul M N R S] : LinearMap.CompatibleSMul M (ι → N) R S where
  map_smul f r m := by ext i; apply ((LinearMap.proj i).comp f).map_smul_of_tower

/-- Linear map between the function spaces `I → M₂` and `I → M₃`, induced by a linear map `f`
between `M₂` and `M₃`. -/
@[simps]
protected def compLeft (f : M₂ →ₗ[R] M₃) (I : Type*) : (I → M₂) →ₗ[R] I → M₃ :=
  { f.toAddMonoidHom.compLeft I with
    toFun := fun h => f ∘ h
    map_smul' := fun c h => by
      ext x
      exact f.map_smul' c (h x) }

theorem apply_single [AddCommMonoid M] [Module R M] [DecidableEq ι] (f : (i : ι) → φ i →ₗ[R] M)
    (i j : ι) (x : φ i) : f j (Pi.single i x j) = (Pi.single i (f i x) : ι → M) j :=
  Pi.apply_single (fun i => f i) (fun i => (f i).map_zero) _ _ _

variable (R φ)

/-- The `LinearMap` version of `AddMonoidHom.single` and `Pi.single`. -/
def single [DecidableEq ι] (i : ι) : φ i →ₗ[R] (i : ι) → φ i :=
  { AddMonoidHom.single φ i with
    toFun := Pi.single i
    map_smul' := Pi.single_smul i }

lemma single_apply [DecidableEq ι] {i : ι} (v : φ i) :
    single R φ i v = Pi.single i v :=
  rfl

lemma sum_single_apply [Fintype ι] [DecidableEq ι] (v : Π i, φ i) :
    ∑ i, Pi.single i (v i) = v := by ext; simp

@[simp]
theorem coe_single [DecidableEq ι] (i : ι) :
    ⇑(single R φ i : φ i →ₗ[R] (i : ι) → φ i) = Pi.single i :=
  rfl

variable [DecidableEq ι]

theorem proj_comp_single_same (i : ι) : (proj i).comp (single R φ i) = id :=
  LinearMap.ext <| Pi.single_eq_same i

theorem proj_comp_single_ne (i j : ι) (h : i ≠ j) : (proj i).comp (single R φ j) = 0 :=
  LinearMap.ext <| Pi.single_eq_of_ne h

theorem iSup_range_single_le_iInf_ker_proj (I J : Set ι) (h : Disjoint I J) :
    ⨆ i ∈ I, range (single R φ i) ≤ ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) := by
  refine iSup_le fun i => iSup_le fun hi => range_le_iff_comap.2 ?_
  simp only [← ker_comp, eq_top_iff, SetLike.le_def, mem_ker, comap_iInf, mem_iInf]
  rintro b - j hj
  rw [proj_comp_single_ne R φ j i, zero_apply]
  rintro rfl
  exact h.le_bot ⟨hi, hj⟩

theorem iInf_ker_proj_le_iSup_range_single {I : Finset ι} {J : Set ι} (hu : Set.univ ⊆ ↑I ∪ J) :
    ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) ≤ ⨆ i ∈ I, range (single R φ i) :=
  SetLike.le_def.2
    (by
      intro b hb
      simp only [mem_iInf, mem_ker, proj_apply] at hb
      rw [←
        show (∑ i ∈ I, Pi.single i (b i)) = b by
          ext i
          rw [Finset.sum_apply, ← Pi.single_eq_same i (b i)]
          refine Finset.sum_eq_single i (fun j _ ne => Pi.single_eq_of_ne ne.symm _) ?_
          intro hiI
          rw [Pi.single_eq_same]
          exact hb _ ((hu trivial).resolve_left hiI)]
      exact sum_mem_biSup fun i _ => mem_range_self (single R φ i) (b i))

theorem iSup_range_single_eq_iInf_ker_proj {I J : Set ι} (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) (hI : Set.Finite I) :
    ⨆ i ∈ I, range (single R φ i) = ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) := by
  refine le_antisymm (iSup_range_single_le_iInf_ker_proj _ _ _ _ hd) ?_
  have : Set.univ ⊆ ↑hI.toFinset ∪ J := by rwa [hI.coe_toFinset]
  refine le_trans (iInf_ker_proj_le_iSup_range_single R φ this) (iSup_mono fun i => ?_)
  rw [Set.Finite.mem_toFinset]

theorem iSup_range_single [Finite ι] : ⨆ i, range (single R φ i) = ⊤ := by
  cases nonempty_fintype ι
  convert top_unique (iInf_emptyset.ge.trans <| iInf_ker_proj_le_iSup_range_single R φ _)
  · rename_i i
    exact ((@iSup_pos _ _ _ fun _ => range <| single R φ i) <| Finset.mem_univ i).symm
  · rw [Finset.coe_univ, Set.union_empty]

theorem disjoint_single_single (I J : Set ι) (h : Disjoint I J) :
    Disjoint (⨆ i ∈ I, range (single R φ i)) (⨆ i ∈ J, range (single R φ i)) := by
  refine
    Disjoint.mono (iSup_range_single_le_iInf_ker_proj _ _ _ _ <| disjoint_compl_right)
      (iSup_range_single_le_iInf_ker_proj _ _ _ _ <| disjoint_compl_right) ?_
  simp only [disjoint_iff_inf_le, SetLike.le_def, mem_iInf, mem_inf, mem_ker, mem_bot, proj_apply,
    funext_iff]
  rintro b ⟨hI, hJ⟩ i
  classical
    by_cases hiI : i ∈ I
    · by_cases hiJ : i ∈ J
      · exact (h.le_bot ⟨hiI, hiJ⟩).elim
      · exact hJ i hiJ
    · exact hI i hiI

/-- The linear equivalence between linear functions on a finite product of modules and
families of functions on these modules. See note [bundled maps over different rings]. -/
@[simps symm_apply]
def lsum (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S] [Module S M]
    [SMulCommClass R S M] : ((i : ι) → φ i →ₗ[R] M) ≃ₗ[S] ((i : ι) → φ i) →ₗ[R] M where
  toFun f := ∑ i : ι, (f i).comp (proj i)
  invFun f i := f.comp (single R φ i)
  map_add' f g := by simp only [Pi.add_apply, add_comp, Finset.sum_add_distrib]
  map_smul' c f := by simp only [Pi.smul_apply, smul_comp, Finset.smul_sum, RingHom.id_apply]
  left_inv f := by
    ext i x
    simp [apply_single]
  right_inv f := by
    ext x
    suffices f (∑ j, Pi.single j (x j)) = f x by simpa [apply_single]
    rw [Finset.univ_sum_single]

@[simp]
theorem lsum_apply (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S]
    [Module S M] [SMulCommClass R S M] (f : (i : ι) → φ i →ₗ[R] M) :
    lsum R φ S f = ∑ i : ι, (f i).comp (proj i) := rfl

theorem lsum_piSingle (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S]
    [Module S M] [SMulCommClass R S M] (f : (i : ι) → φ i →ₗ[R] M) (i : ι) (x : φ i) :
    lsum R φ S f (Pi.single i x) = f i x := by
  simp_rw [lsum_apply, sum_apply, comp_apply, proj_apply, apply_single, Fintype.sum_pi_single']

@[simp high]
theorem lsum_single (S) [Fintype ι] [Semiring S]
    [∀ i, Module S (φ i)] [∀ i, SMulCommClass R S (φ i)] :
    LinearMap.lsum R φ S (LinearMap.single R φ) = LinearMap.id :=
  LinearMap.ext fun x => by simp [Finset.univ_sum_single]

variable {R φ}

section Ext

variable [Finite ι] [AddCommMonoid M] [Module R M] {f g : ((i : ι) → φ i) →ₗ[R] M}

theorem pi_ext (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) : f = g :=
  toAddMonoidHom_injective <| AddMonoidHom.functions_ext _ _ _ h

theorem pi_ext_iff : f = g ↔ ∀ i x, f (Pi.single i x) = g (Pi.single i x) :=
  ⟨fun h _ _ => h ▸ rfl, pi_ext⟩

/-- This is used as the ext lemma instead of `LinearMap.pi_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[ext]
theorem pi_ext' (h : ∀ i, f.comp (single R φ i) = g.comp (single R φ i)) : f = g := by
  refine pi_ext fun i x => ?_
  convert LinearMap.congr_fun (h i) x

end Ext

section

variable (R φ)

/-- If `I` and `J` are disjoint index sets, the product of the kernels of the `J`th projections of
`φ` is linearly equivalent to the product over `I`. -/
def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, ker (proj i : ((i : ι) → φ i) →ₗ[R] φ i) :
    Submodule R ((i : ι) → φ i)) ≃ₗ[R] (i : I) → φ i := by
  refine
    LinearEquiv.ofLinear (pi fun i => (proj (i : ι)).comp (Submodule.subtype _))
      (codRestrict _ (pi fun i => if h : i ∈ I then proj (⟨i, h⟩ : I) else 0) ?_) ?_ ?_
  · intro b
    simp only [mem_iInf, mem_ker, proj_apply, pi_apply]
    intro j hjJ
    have : j ∉ I := fun hjI => hd.le_bot ⟨hjI, hjJ⟩
    rw [dif_neg this, zero_apply]
  · simp only [pi_comp, comp_assoc, subtype_comp_codRestrict, proj_pi, Subtype.coe_prop]
    ext b ⟨j, hj⟩
    simp only [dif_pos,
      LinearMap.coe_proj, LinearMap.pi_apply]
    rfl
  · ext1 ⟨b, hb⟩
    apply Subtype.ext
    ext j
    have hb : ∀ i ∈ J, b i = 0 := by
      simpa only [mem_iInf, mem_ker, proj_apply] using (mem_iInf _).1 hb
    simp only [comp_apply, pi_apply, id_apply, codRestrict_apply]
    split_ifs with h
    · rfl
    · exact (hb _ <| (hu trivial).resolve_left h).symm

end

section

/-- `diag i j` is the identity map if `i = j`. Otherwise it is the constant 0 map. -/
def diag (i j : ι) : φ i →ₗ[R] φ j :=
  @Function.update ι (fun j => φ i →ₗ[R] φ j) _ 0 i id j

theorem update_apply (f : (i : ι) → M₂ →ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ →ₗ[R] φ i) :
    (update f i b j) c = update (fun i => f i c) i (b c) j := by
  by_cases h : j = i
  · rw [h, update_self, update_self]
  · rw [update_of_ne h, update_of_ne h]

variable (R φ)

theorem single_eq_pi_diag (i : ι) : single R φ i = pi (diag i) := by
  ext x j
  convert (update_apply 0 x i j _).symm
  rfl

theorem ker_single (i : ι) : ker (single R φ i) = ⊥ :=
  ker_eq_bot_of_injective <| Pi.single_injective _

theorem proj_comp_single (i j : ι) : (proj i).comp (single R φ j) = diag j i := by
  rw [single_eq_pi_diag, proj_pi]

end

/-- A linear map `f` applied to `x : ι → R` can be computed using the image under `f` of elements
of the canonical basis. -/
theorem pi_apply_eq_sum_univ [Fintype ι] (f : (ι → R) →ₗ[R] M₂) (x : ι → R) :
    f x = ∑ i, x i • f fun j => if i = j then 1 else 0 := by
  conv_lhs => rw [pi_eq_sum_univ x, map_sum]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  rw [map_smul]

end LinearMap

namespace Submodule

variable [Semiring R] {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]

open LinearMap

/-- A version of `Set.pi` for submodules. Given an index set `I` and a family of submodules
`p : (i : ι) → Submodule R (φ i)`, `pi I s` is the submodule of dependent functions
`f : (i : ι) → φ i` such that `f i` belongs to `p a` whenever `i ∈ I`. -/
@[simps]
def pi (I : Set ι) (p : (i : ι) → Submodule R (φ i)) : Submodule R ((i : ι) → φ i) where
  carrier := Set.pi I fun i => p i
  zero_mem' i _ := (p i).zero_mem
  add_mem' {_ _} hx hy i hi := (p i).add_mem (hx i hi) (hy i hi)
  smul_mem' c _ hx i hi := (p i).smul_mem c (hx i hi)

attribute [norm_cast] coe_pi

variable {I : Set ι} {p q : (i : ι) → Submodule R (φ i)} {x : (i : ι) → φ i}

@[simp]
theorem mem_pi : x ∈ pi I p ↔ ∀ i ∈ I, x i ∈ p i :=
  Iff.rfl

@[simp]
theorem pi_empty (p : (i : ι) → Submodule R (φ i)) : pi ∅ p = ⊤ :=
  SetLike.coe_injective <| Set.empty_pi _

@[simp]
theorem pi_top (s : Set ι) : (pi s fun i : ι ↦ (⊤ : Submodule R (φ i))) = ⊤ :=
  SetLike.coe_injective <| Set.pi_univ _

@[simp]
theorem pi_univ_bot : (pi Set.univ fun i : ι ↦ (⊥ : Submodule R (φ i))) = ⊥ :=
  le_bot_iff.mp fun _ h ↦ funext fun i ↦ h i trivial

@[gcongr]
theorem pi_mono {s : Set ι} (h : ∀ i ∈ s, p i ≤ q i) : pi s p ≤ pi s q :=
  Set.pi_mono h

theorem biInf_comap_proj :
    ⨅ i ∈ I, comap (proj i : ((i : ι) → φ i) →ₗ[R] φ i) (p i) = pi I p := by
  ext x
  simp

theorem iInf_comap_proj :
    ⨅ i, comap (proj i : ((i : ι) → φ i) →ₗ[R] φ i) (p i) = pi Set.univ p := by
  ext x
  simp

theorem le_comap_single_pi [DecidableEq ι] (p : (i : ι) → Submodule R (φ i)) {I i} :
    p i ≤ Submodule.comap (LinearMap.single R φ i : φ i →ₗ[R] _) (Submodule.pi I p) := by
  intro x hx
  rw [Submodule.mem_comap, Submodule.mem_pi]
  rintro j -
  rcases eq_or_ne j i with rfl | hne <;> simp [*]

theorem iSup_map_single_le [DecidableEq ι] :
    ⨆ i, map (LinearMap.single R φ i) (p i) ≤ pi I p :=
  iSup_le fun _ => map_le_iff_le_comap.mpr <| le_comap_single_pi _

theorem iSup_map_single [DecidableEq ι] [Finite ι] :
    ⨆ i, map (LinearMap.single R φ i : φ i →ₗ[R] (i : ι) → φ i) (p i) = pi Set.univ p := by
  cases nonempty_fintype ι
  refine iSup_map_single_le.antisymm fun x hx => ?_
  rw [← Finset.univ_sum_single x]
  exact sum_mem_iSup fun i => mem_map_of_mem (hx i trivial)

end Submodule

namespace LinearMap

variable [Semiring R]

lemma ker_compLeft [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) (I : Type*) :
    LinearMap.ker (f.compLeft I) = Submodule.pi (Set.univ : Set I) (fun _ => LinearMap.ker f) :=
  Submodule.ext fun _ => ⟨fun (hx : _ = _) i _ => congr_fun hx i,
    fun hx => funext fun i => hx i trivial⟩

lemma range_compLeft [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) (I : Type*) :
    LinearMap.range (f.compLeft I) =
      Submodule.pi (Set.univ : Set I) (fun _ => LinearMap.range f) :=
  Submodule.ext fun _ => ⟨fun ⟨y, hy⟩ i _ => ⟨y i, congr_fun hy i⟩, fun hx => by
    choose y hy using hx
    exact ⟨fun i => y i trivial, funext fun i => hy i trivial⟩⟩

end LinearMap

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

@[simp]
theorem piCongrRight_apply (e : (i : ι) → φ i ≃ₗ[R] ψ i) (f i) :
    piCongrRight e f i = e i (f i) := rfl

@[simp]
theorem piCongrRight_refl : (piCongrRight fun j => refl R (φ j)) = refl _ _ :=
  rfl

@[simp]
theorem piCongrRight_symm (e : (i : ι) → φ i ≃ₗ[R] ψ i) :
    (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl

@[simp]
theorem piCongrRight_trans (e : (i : ι) → φ i ≃ₗ[R] ψ i) (f : (i : ι) → ψ i ≃ₗ[R] χ i) :
    (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).trans (f i) :=
  rfl

variable (R φ)

/-- Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as a `LinearEquiv`. -/
@[simps +simpRhs]
def piCongrLeft' (e : ι ≃ ι') : ((i' : ι) → φ i') ≃ₗ[R] (i : ι') → φ <| e.symm i :=
  { Equiv.piCongrLeft' φ e with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".

This is `Equiv.piCongrLeft` as a `LinearEquiv` -/
def piCongrLeft (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃ₗ[R] (i : ι) → φ i :=
  (piCongrLeft' R φ e.symm).symm

/-- `Equiv.piCurry` as a `LinearEquiv`. -/
def piCurry {ι : Type*} {κ : ι → Type*} (α : ∀ i, κ i → Type*)
    [∀ i k, AddCommMonoid (α i k)] [∀ i k, Module R (α i k)] :
    (Π i : Sigma κ, α i.1 i.2) ≃ₗ[R] Π i j, α i j where
  __ := Equiv.piCurry α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem piCurry_apply {ι : Type*} {κ : ι → Type*} (α : ∀ i, κ i → Type*)
    [∀ i k, AddCommMonoid (α i k)] [∀ i k, Module R (α i k)]
    (f : ∀ x : Σ i, κ i, α x.1 x.2) :
    piCurry R α f = Sigma.curry f :=
  rfl

@[simp] theorem piCurry_symm_apply {ι : Type*} {κ : ι → Type*} (α : ∀ i, κ i → Type*)
    [∀ i k, AddCommMonoid (α i k)] [∀ i k, Module R (α i k)]
    (f : ∀ a b, α a b) :
    (piCurry R α).symm f = Sigma.uncurry f :=
  rfl

/-- This is `Equiv.piOptionEquivProd` as a `LinearEquiv` -/
def piOptionEquivProd {ι : Type*} {M : Option ι → Type*} [(i : Option ι) → AddCommMonoid (M i)]
    [(i : Option ι) → Module R (M i)] :
    ((i : Option ι) → M i) ≃ₗ[R] M none × ((i : ι) → M (some i)) :=
  { Equiv.piOptionEquivProd with
    map_add' := by simp [funext_iff]
    map_smul' := by simp [funext_iff] }

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

variable {ι R M}

@[simp]
theorem piRing_apply (f : (ι → R) →ₗ[R] M) (i : ι) : piRing R M ι S f i = f (Pi.single i 1) :=
  rfl

@[simp]
theorem piRing_symm_apply (f : ι → M) (g : ι → R) : (piRing R M ι S).symm f g = ∑ i, g i • f i := by
  simp [piRing, LinearMap.lsum_apply]

-- TODO additive version?
/-- `Equiv.sumArrowEquivProdArrow` as a linear equivalence.
-/
def sumArrowLequivProdArrow (α β R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :
    (α ⊕ β → M) ≃ₗ[R] (α → M) × (β → M) :=
  { Equiv.sumArrowEquivProdArrow α β
      M with
    map_add' := by
      intro f g
      ext <;> rfl
    map_smul' := by
      intro r f
      ext <;> rfl }

@[simp]
theorem sumArrowLequivProdArrow_apply_fst {α β} (f : α ⊕ β → M) (a : α) :
    (sumArrowLequivProdArrow α β R M f).1 a = f (Sum.inl a) :=
  rfl

@[simp]
theorem sumArrowLequivProdArrow_apply_snd {α β} (f : α ⊕ β → M) (b : β) :
    (sumArrowLequivProdArrow α β R M f).2 b = f (Sum.inr b) :=
  rfl

@[simp]
theorem sumArrowLequivProdArrow_symm_apply_inl {α β} (f : α → M) (g : β → M) (a : α) :
    ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inl a) = f a :=
  rfl

@[simp]
theorem sumArrowLequivProdArrow_symm_apply_inr {α β} (f : α → M) (g : β → M) (b : β) :
    ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inr b) = g b :=
  rfl

/-- If `ι` has a unique element, then `ι → M` is linearly equivalent to `M`. -/
@[simps +simpRhs -fullyApplied symm_apply]
def funUnique (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M] :
    (ι → M) ≃ₗ[R] M :=
  { Equiv.funUnique ι M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
theorem funUnique_apply (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M] :
    (funUnique ι R M : (ι → M) → M) = eval default := rfl

variable (R M)

/-- Linear equivalence between dependent functions `(i : Fin 2) → M i` and `M 0 × M 1`. -/
@[simps +simpRhs -fullyApplied symm_apply]
def piFinTwo (M : Fin 2 → Type v)
    [(i : Fin 2) → AddCommMonoid (M i)] [(i : Fin 2) → Module R (M i)] :
    ((i : Fin 2) → M i) ≃ₗ[R] M 0 × M 1 :=
  { piFinTwoEquiv M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
theorem piFinTwo_apply (M : Fin 2 → Type v)
    [(i : Fin 2) → AddCommMonoid (M i)] [(i : Fin 2) → Module R (M i)] :
    (piFinTwo R M : ((i : Fin 2) → M i) → M 0 × M 1) = fun f => (f 0, f 1) := rfl

/-- Linear equivalence between vectors in `M² = Fin 2 → M` and `M × M`. -/
@[simps! -fullyApplied]
def finTwoArrow : (Fin 2 → M) ≃ₗ[R] M × M :=
  { finTwoArrowEquiv M, piFinTwo R fun _ => M with }

end LinearEquiv

lemma Pi.mem_span_range_single_inl_iff
    [DecidableEq ι] [DecidableEq ι'] [Fintype ι] [Semiring R] {x : ι ⊕ ι' → R} :
    x ∈ span R (Set.range fun i ↦ single (Sum.inl i) 1) ↔ ∀ k, x (Sum.inr k) = 0 := by
  refine ⟨fun hx k ↦ ?_, fun hx ↦ ?_⟩
  · induction hx using span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; simp
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul t u _ hu => simp [hu]
  · suffices x = ∑ i : ι, x (Sum.inl i) • Pi.single (M := fun _ ↦ R) (Sum.inl i) (1 : R) by
      rw [this]
      exact sum_mem <| fun i _ ↦ SMulMemClass.smul_mem _ <| subset_span <| Set.mem_range_self i
    ext (i | i)
    · simp [single_apply]
    · simp [hx i]

section Extend

variable (R) {η : Type x} [Semiring R] (s : ι → η)

/-- `Function.extend s f 0` as a bundled linear map. -/
@[simps]
noncomputable def Function.ExtendByZero.linearMap : (ι → R) →ₗ[R] η → R :=
  { Function.ExtendByZero.hom R s with
    toFun := fun f => Function.extend s f 0
    map_smul' := fun r f => by simpa using Function.extend_smul r s f 0 }

end Extend

variable (R) in
/-- `Fin.consEquiv` as a continuous linear equivalence. -/
@[simps]
def Fin.consLinearEquiv
    {n : ℕ} (M : Fin n.succ → Type*) [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    (M 0 × Π i, M (Fin.succ i)) ≃ₗ[R] (Π i, M i) where
  __ := Fin.consEquiv M
  map_add' x y := funext <| Fin.cases rfl (by simp)
  map_smul' c x := funext <| Fin.cases rfl (by simp)


/-! ### Bundled versions of `Matrix.vecCons` and `Matrix.vecEmpty`

The idea of these definitions is to be able to define a map as `x ↦ ![f₁ x, f₂ x, f₃ x]`, where
`f₁ f₂ f₃` are already linear maps, as `f₁.vecCons <| f₂.vecCons <| f₃.vecCons <| vecEmpty`.

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

@[simp]
theorem LinearMap.vecEmpty_apply (m : M) : (LinearMap.vecEmpty : M →ₗ[R] Fin 0 → M₃) m = ![] :=
  rfl

/-- A linear map into `Fin n.succ → M₃` can be built out of a map into `M₃` and a map into
`Fin n → M₃`. -/
def LinearMap.vecCons {n} (f : M →ₗ[R] M₂) (g : M →ₗ[R] Fin n → M₂) : M →ₗ[R] Fin n.succ → M₂ :=
  Fin.consLinearEquiv R (fun _ : Fin n.succ => M₂) ∘ₗ f.prod g

@[simp]
theorem LinearMap.vecCons_apply {n} (f : M →ₗ[R] M₂) (g : M →ₗ[R] Fin n → M₂) (m : M) :
    f.vecCons g m = Matrix.vecCons (f m) (g m) :=
  rfl

variable (R) in
/--
To show a property `motive` of modules holds for arbitrary finite products of modules, it suffices
to show
1. `motive` is stable under isomorphism.
2. `motive` holds for the zero module.
3. `motive` holds for `M × N` if it holds for both `M` and `N`.

Since we need to apply `motive` to modules in `Type u` and in `Type (max u v)`, there is a second
`motive'` argument which is required to be equivalent to `motive` up to universe lifting by `equiv`.

See `Module.pi_induction'` for a version where `motive` assumes `AddCommGroup` instead.
-/
@[elab_as_elim]
lemma Module.pi_induction {ι : Type v} [Finite ι]
    (motive : ∀ (N : Type u) [AddCommMonoid N] [Module R N], Prop)
    (motive' : ∀ (N : Type (max u v)) [AddCommMonoid N] [Module R N], Prop)
    (equiv : ∀ {N : Type u} {N' : Type (max u v)} [AddCommMonoid N] [AddCommMonoid N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') → motive N → motive' N')
    (equiv' : ∀ {N N' : Type (max u v)} [AddCommMonoid N] [AddCommMonoid N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') → motive' N → motive' N')
    (unit : motive PUnit) (prod : ∀ {N : Type u} {N' : Type (max u v)} [AddCommMonoid N]
      [AddCommMonoid N'] [Module R N] [Module R N'], motive N → motive' N' → motive' (N × N'))
    (M : ι → Type u) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (h : ∀ i, motive (M i)) : motive' (∀ i, M i) := by
  classical
  cases nonempty_fintype ι
  revert M
  refine Fintype.induction_empty_option
    (fun α β _ e h M _ _ hM ↦ equiv' (LinearEquiv.piCongrLeft R M e) <| h _ fun i ↦ hM _)
    (fun M _ _ _ ↦ equiv default unit) (fun α _ h M _ _ hn ↦ ?_) ι
  exact equiv' (LinearEquiv.piOptionEquivProd R).symm <| prod (hn _) (h _ fun i ↦ hn i)

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

end CommSemiring

/-- A variant of `Module.pi_induction` that assumes `AddCommGroup` instead of `AddCommMonoid`. -/
@[elab_as_elim]
lemma Module.pi_induction' {ι : Type v} [Finite ι] (R : Type*) [Ring R]
    (motive : ∀ (N : Type u) [AddCommGroup N] [Module R N], Prop)
    (motive' : ∀ (N : Type (max u v)) [AddCommGroup N] [Module R N], Prop)
    (equiv : ∀ {N : Type u} {N' : Type (max u v)} [AddCommGroup N] [AddCommGroup N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') → motive N → motive' N')
    (equiv' : ∀ {N N' : Type (max u v)} [AddCommGroup N] [AddCommGroup N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') → motive' N → motive' N')
    (unit : motive PUnit) (prod : ∀ {N : Type u} {N' : Type (max u v)} [AddCommGroup N]
      [AddCommGroup N'] [Module R N] [Module R N'], motive N → motive' N' → motive' (N × N'))
    (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (h : ∀ i, motive (M i)) : motive' (∀ i, M i) := by
  classical
  cases nonempty_fintype ι
  revert M
  refine Fintype.induction_empty_option
    (fun α β _ e h M _ _ hM ↦ equiv' (LinearEquiv.piCongrLeft R M e) <| h _ fun i ↦ hM _)
    (fun M _ _ _ ↦ equiv default unit) (fun α _ h M _ _ hn ↦ ?_) ι
  exact equiv' (LinearEquiv.piOptionEquivProd R).symm <| prod (hn _) (h _ fun i ↦ hn i)

end Fin
