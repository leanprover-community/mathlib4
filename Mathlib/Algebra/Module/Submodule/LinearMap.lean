/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!

# Linear maps involving submodules of a module

In this file we define a number of linear maps involving submodules of a module.

## Main declarations

* `Submodule.subtype`: Embedding of a submodule `p` to the ambient space `M` as a `Submodule`.
* `LinearMap.domRestrict`: The restriction of a semilinear map `f : M → M₂` to a submodule `p ⊆ M`
  as a semilinear map `p → M₂`.
* `LinearMap.restrict`: The restriction of a linear map `f : M → M₁` to a submodule `p ⊆ M` and
  `q ⊆ M₁` (if `q` contains the codomain).
* `Submodule.inclusion`: the inclusion `p ⊆ p'` of submodules `p` and `p'` as a linear map.

## Tags

submodule, subspace, linear map
-/

open Function Set

universe u'' u' u v w

section

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

namespace SMulMemClass

variable [Semiring R] [AddCommMonoid M] [Module R M] {A : Type*} [SetLike A M]
  [AddSubmonoidClass A M] [SMulMemClass A R M] (S' : A)

/-- The natural `R`-linear map from a submodule of an `R`-module `M` to `M`. -/
protected def subtype : S' →ₗ[R] M where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {S'} in
@[simp]
lemma subtype_apply (x : S') :
    SMulMemClass.subtype S' x = x := rfl

lemma subtype_injective :
    Function.Injective (SMulMemClass.subtype S') :=
  Subtype.coe_injective

@[simp]
protected theorem coe_subtype : (SMulMemClass.subtype S' : S' → M) = Subtype.val :=
  rfl

end SMulMemClass

namespace Submodule

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}
variable {p q : Submodule R M}
variable {r : R} {x y : M}
variable (p)

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →ₗ[R] M where
  toFun := Subtype.val
  map_add' := by simp
  map_smul' := by simp

variable {p} in
@[simp]
theorem subtype_apply (x : p) : p.subtype x = x :=
  rfl

lemma subtype_injective :
    Function.Injective p.subtype :=
  Subtype.coe_injective

@[simp]
theorem coe_subtype : (Submodule.subtype p : p → M) = Subtype.val :=
  rfl

theorem injective_subtype : Injective p.subtype :=
  Subtype.coe_injective

/-- Note the `AddSubmonoid` version of this lemma is called `AddSubmonoid.coe_finset_sum`. -/
theorem coe_sum (x : ι → p) (s : Finset ι) : ↑(∑ i ∈ s, x i) = ∑ i ∈ s, (x i : M) :=
  map_sum p.subtype _ _

section AddAction

variable {α β : Type*}

/-- The action by a submodule is the action by the underlying module. -/
instance [AddAction M α] : AddAction p α :=
  AddAction.compHom _ p.subtype.toAddMonoidHom

end AddAction

end AddCommMonoid

end Submodule

end

section

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {ι : Type*}

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₁] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)


/-- The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a linear map
`p → M₂`. -/
def domRestrict (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p →ₛₗ[σ₁₂] M₂ :=
  f.comp p.subtype

@[simp]
theorem domRestrict_apply (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) (x : p) :
    f.domRestrict p x = f x :=
  rfl

/-- A linear map `f : M₂ → M` whose values lie in a submodule `p ⊆ M` can be restricted to a
linear map M₂ → p.

See also `LinearMap.codLift`. -/
def codRestrict (p : Submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) (h : ∀ c, f c ∈ p) : M →ₛₗ[σ₁₂] p where
  toFun c := ⟨f c, h c⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp]
theorem codRestrict_apply (p : Submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) {h} (x : M) :
    (codRestrict p f h x : M₂) = f x :=
  rfl

@[simp]
theorem comp_codRestrict (p : Submodule R₃ M₃) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M →ₛₗ[σ₁₃] p) = codRestrict p (g.comp f) fun _ => h _ :=
  ext fun _ => rfl

@[simp]
theorem subtype_comp_codRestrict (p : Submodule R₂ M₂) (h : ∀ b, f b ∈ p) :
    p.subtype.comp (codRestrict p f h) = f :=
  ext fun _ => rfl

section

variable {M₂' : Type*} [AddCommMonoid M₂'] [Module R₂ M₂']
(p : M₂' →ₗ[R₂] M₂) (hp : Injective p) (h : ∀ c, f c ∈ range p)

/-- A linear map `f : M → M₂` whose values lie in the image of an injective linear map
`p : M₂' → M₂` admits a unique lift to a linear map `M → M₂'`. -/
noncomputable def codLift :
    M →ₛₗ[σ₁₂] M₂' where
  toFun c := (h c).choose
  map_add' b c := by apply hp; simp_rw [map_add, (h _).choose_spec, ← map_add, (h _).choose_spec]
  map_smul' r c := by apply hp; simp_rw [map_smul, (h _).choose_spec, LinearMap.map_smulₛₗ]

@[simp] theorem codLift_apply (x : M) :
    (f.codLift p hp h x) = (h x).choose :=
  rfl

@[simp]
theorem comp_codLift :
    p.comp (f.codLift p hp h) = f := by
  ext x
  rw [comp_apply, codLift_apply, (h x).choose_spec]

end

/-- Restrict domain and codomain of a linear map. -/
def restrict (f : M →ₗ[R] M₁) {p : Submodule R M} {q : Submodule R M₁} (hf : ∀ x ∈ p, f x ∈ q) :
    p →ₗ[R] q :=
  (f.domRestrict p).codRestrict q <| SetLike.forall.2 hf

@[simp]
theorem restrict_coe_apply (f : M →ₗ[R] M₁) {p : Submodule R M} {q : Submodule R M₁}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : ↑(f.restrict hf x) = f x :=
  rfl

theorem restrict_apply {f : M →ₗ[R] M₁} {p : Submodule R M} {q : Submodule R M₁}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : f.restrict hf x = ⟨f x, hf x.1 x.2⟩ :=
  rfl

lemma restrict_sub {R M M₁ : Type*}
    [Ring R] [AddCommGroup M] [AddCommGroup M₁] [Module R M] [Module R M₁]
    {p : Submodule R M} {q : Submodule R M₁} {f g : M →ₗ[R] M₁}
    (hf : MapsTo f p q) (hg : MapsTo g p q)
    (hfg : MapsTo (f - g) p q := fun _ hx ↦ q.sub_mem (hf hx) (hg hx)) :
    f.restrict hf - g.restrict hg = (f - g).restrict hfg := by
  ext; simp

lemma restrict_comp
    {M₂ M₃ : Type*} [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₂] [Module R M₃]
    {p : Submodule R M} {p₂ : Submodule R M₂} {p₃ : Submodule R M₃}
    {f : M →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}
    (hf : MapsTo f p p₂) (hg : MapsTo g p₂ p₃) (hfg : MapsTo (g ∘ₗ f) p p₃ := hg.comp hf) :
    (g ∘ₗ f).restrict hfg = (g.restrict hg) ∘ₗ (f.restrict hf) :=
  rfl

-- TODO Consider defining `Algebra R (p.compatibleMaps p)`, `AlgHom` version of `LinearMap.restrict`
lemma restrict_smul_one
    {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {p : Submodule R M}
    (μ : R) (h : ∀ x ∈ p, (μ • (1 : Module.End R M)) x ∈ p := fun _ ↦ p.smul_mem μ) :
    (μ • 1 : Module.End R M).restrict h = μ • (1 : Module.End R p) :=
  rfl

lemma restrict_commute {f g : M →ₗ[R] M} (h : Commute f g) {p : Submodule R M}
    (hf : MapsTo f p p) (hg : MapsTo g p p) :
    Commute (f.restrict hf) (g.restrict hg) := by
  change (f ∘ₗ g).restrict (hf.comp hg) = (g ∘ₗ f).restrict (hg.comp hf)
  congr 1

theorem subtype_comp_restrict {f : M →ₗ[R] M₁} {p : Submodule R M} {q : Submodule R M₁}
    (hf : ∀ x ∈ p, f x ∈ q) : q.subtype.comp (f.restrict hf) = f.domRestrict p :=
  rfl

theorem restrict_eq_codRestrict_domRestrict {f : M →ₗ[R] M₁} {p : Submodule R M}
    {q : Submodule R M₁} (hf : ∀ x ∈ p, f x ∈ q) :
    f.restrict hf = (f.domRestrict p).codRestrict q fun x => hf x.1 x.2 :=
  rfl

theorem restrict_eq_domRestrict_codRestrict {f : M →ₗ[R] M₁} {p : Submodule R M}
    {q : Submodule R M₁} (hf : ∀ x, f x ∈ q) :
    (f.restrict fun x _ => hf x) = (f.codRestrict q hf).domRestrict p :=
  rfl

theorem sum_apply (t : Finset ι) (f : ι → M →ₛₗ[σ₁₂] M₂) (b : M) :
    (∑ d ∈ t, f d) b = ∑ d ∈ t, f d b :=
  _root_.map_sum ((AddMonoidHom.eval b).comp toAddMonoidHom') f _

@[simp, norm_cast]
theorem coeFn_sum {ι : Type*} (t : Finset ι) (f : ι → M →ₛₗ[σ₁₂] M₂) :
    ⇑(∑ i ∈ t, f i) = ∑ i ∈ t, (f i : M → M₂) :=
  _root_.map_sum
    (show AddMonoidHom (M →ₛₗ[σ₁₂] M₂) (M → M₂)
      from { toFun := DFunLike.coe,
             map_zero' := rfl
             map_add' := fun _ _ => rfl }) _ _

theorem _root_.Module.End.submodule_pow_eq_zero_of_pow_eq_zero {N : Submodule R M}
    {g : Module.End R N} {G : Module.End R M} (h : G.comp N.subtype = N.subtype.comp g) {k : ℕ}
    (hG : G ^ k = 0) : g ^ k = 0 := by
  ext m
  have hg : N.subtype.comp (g ^ k) m = 0 := by
    rw [← Module.End.commute_pow_left_of_commute h, hG, zero_comp, zero_apply]
  simpa using hg

section

variable {f' : M →ₗ[R] M}

theorem _root_.Module.End.pow_apply_mem_of_forall_mem {p : Submodule R M} (n : ℕ)
    (h : ∀ x ∈ p, f' x ∈ p) (x : M) (hx : x ∈ p) : (f' ^ n) x ∈ p := by
  induction n generalizing x with
  | zero => simpa
  | succ n ih =>
    simpa only [iterate_succ, coe_comp, Function.comp_apply, restrict_apply] using ih _ (h _ hx)

theorem _root_.Module.End.pow_restrict {p : Submodule R M} (n : ℕ) (h : ∀ x ∈ p, f' x ∈ p)
    (h' := Module.End.pow_apply_mem_of_forall_mem n h) :
    (f'.restrict h) ^ n = (f' ^ n).restrict h' := by
  ext x
  have : Semiconj (↑) (f'.restrict h) f' := fun _ ↦ restrict_coe_apply _ _ _
  simp [Module.End.coe_pow, this.iterate_right _ _]

end

end AddCommMonoid

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]
variable (f g : M →ₗ[R] M₂)

/-- Alternative version of `domRestrict` as a linear map. -/
def domRestrict' (p : Submodule R M) : (M →ₗ[R] M₂) →ₗ[R] p →ₗ[R] M₂ where
  toFun φ := φ.domRestrict p
  map_add' := by simp [LinearMap.ext_iff]
  map_smul' := by simp [LinearMap.ext_iff]

@[simp]
theorem domRestrict'_apply (f : M →ₗ[R] M₂) (p : Submodule R M) (x : p) :
    domRestrict' p f x = f x :=
  rfl

end CommSemiring

end LinearMap

end

namespace Submodule

section AddCommMonoid

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {p p' : Submodule R M}

/-- If two submodules `p` and `p'` satisfy `p ⊆ p'`, then `inclusion p p'` is the linear map version
of this inclusion. -/
def inclusion (h : p ≤ p') : p →ₗ[R] p' :=
  p.subtype.codRestrict p' fun ⟨_, hx⟩ => h hx

@[simp]
theorem coe_inclusion (h : p ≤ p') (x : p) : (inclusion h x : M) = x :=
  rfl

theorem inclusion_apply (h : p ≤ p') (x : p) : inclusion h x = ⟨x, h x.2⟩ :=
  rfl

theorem inclusion_injective (h : p ≤ p') : Function.Injective (inclusion h) := fun _ _ h =>
  Subtype.val_injective (Subtype.mk.inj h)

variable (p p')

theorem subtype_comp_inclusion (p q : Submodule R M) (h : p ≤ q) :
    q.subtype.comp (inclusion h) = p.subtype := by
  ext ⟨b, hb⟩
  rfl

end AddCommMonoid

end Submodule
