/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Decompositions of additive monoids, groups, and modules into direct sums

## Main definitions

* `DirectSum.Decomposition ℳ`: A typeclass to provide a constructive decomposition from
  an additive monoid `M` into a family of additive submonoids `ℳ`
* `DirectSum.decompose ℳ`: The canonical equivalence provided by the above typeclass
* `DirectSum.Rel.IsPureHomogeneous`: a relation `r` is `PureHomogeneous` iff `r a b` implies that
  `a` and `b` are homogeneous of the same degree.
* `DirecSum.Rel.IsHomogeneous`: a relation is `Homogeneous` iff `r a b` implies that the components
  of `a` and `b` are related by `r`.

## Main statements

* `DirectSum.Decomposition.isInternal`: The link to `DirectSum.IsInternal`.

## Implementation details

As we want to talk about different types of decomposition (additive monoids, modules, rings, ...),
we choose to avoid heavily bundling `DirectSum.decompose`, instead making copies for the
`AddEquiv`, `LinearEquiv`, etc. This means we have to repeat statements that follow from these
bundled homs, but means we don't have to repeat statements for different types of decomposition.
-/

@[expose] public section


variable {ι R M σ : Type*}

open DirectSum

namespace DirectSum

section AddCommMonoid

variable [DecidableEq ι] [AddCommMonoid M]
variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

/-- A decomposition is an equivalence between an additive monoid `M` and a direct sum of additive
submonoids `ℳ i` of that `M`, such that the "recomposition" is canonical. This definition also
works for additive groups and modules.

This is a version of `DirectSum.IsInternal` which comes with a constructive inverse to the
canonical "recomposition" rather than just a proof that the "recomposition" is bijective.

Often it is easier to construct a term of this type via `Decomposition.ofAddHom` or
`Decomposition.ofLinearMap`. -/
class Decomposition where
  decompose' : M → ⨁ i, ℳ i
  left_inv : Function.LeftInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
  right_inv : Function.RightInverse (DirectSum.coeAddMonoidHom ℳ) decompose'

/-- `DirectSum.Decomposition` instances, while carrying data, are always equal. -/
instance : Subsingleton (Decomposition ℳ) :=
  ⟨fun x y ↦ by
    obtain ⟨_, _, xr⟩ := x
    obtain ⟨_, yl, _⟩ := y
    congr
    exact Function.LeftInverse.eq_rightInverse xr yl⟩

/-- A convenience method to construct a decomposition from an `AddMonoidHom`, such that the proofs
of left and right inverse can be constructed via `ext`. -/
abbrev Decomposition.ofAddHom (decompose : M →+ ⨁ i, ℳ i)
    (h_left_inv : (DirectSum.coeAddMonoidHom ℳ).comp decompose = .id _)
    (h_right_inv : decompose.comp (DirectSum.coeAddMonoidHom ℳ) = .id _) : Decomposition ℳ where
  decompose' := decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv

/-- Noncomputably conjure a decomposition instance from a `DirectSum.IsInternal` proof. -/
@[implicit_reducible]
noncomputable def IsInternal.chooseDecomposition (h : IsInternal ℳ) :
    DirectSum.Decomposition ℳ where
  decompose' := (Equiv.ofBijective _ h).symm
  left_inv := (Equiv.ofBijective _ h).right_inv
  right_inv := (Equiv.ofBijective _ h).left_inv

variable [Decomposition ℳ]

protected theorem Decomposition.isInternal : DirectSum.IsInternal ℳ :=
  ⟨Decomposition.right_inv.injective, Decomposition.left_inv.surjective⟩

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
to a direct sum of components. This is the canonical spelling of the `decompose'` field. -/
def decompose : M ≃ ⨁ i, ℳ i where
  toFun := Decomposition.decompose'
  invFun := DirectSum.coeAddMonoidHom ℳ
  left_inv := Decomposition.left_inv
  right_inv := Decomposition.right_inv

/-- A relation `r` is `PureHomogeneous` with respect to a family `ℳ : ι → σ` (where `SetLike σ M`)
iff `r a b` implies that `a` and `b` are homogeneous of the same degree. -/
def Rel.IsPureHomogeneous (r : M → M → Prop) : Prop :=
  ∀ {a b : M} (_ : r a b), ∃ i, a ∈ ℳ i ∧ b ∈ ℳ i

omit [DecidableEq ι] [AddCommMonoid M] [AddSubmonoidClass σ M] [Decomposition ℳ] in
theorem Rel.isPureHomogeneous_iff {r : M → M → Prop} :
    Rel.IsPureHomogeneous ℳ r ↔ ∀ {a b : M} (_ : r a b), ∃ i, a ∈ ℳ i ∧ b ∈ ℳ i := Iff.rfl

/-- A relation `r` is `Homogeneous` for a `DirectSum.Decomposition` iff
`r a b` implies that the components of `a` and `b` are related by `r`. -/
def Rel.IsHomogeneous (r : M → M → Prop) : Prop :=
  ∀ {a b : M} (_ : r a b), ∀ i, r (decompose ℳ a i) (decompose ℳ b i)

theorem Rel.isHomogeneous_iff {r : M → M → Prop} :
    Rel.IsHomogeneous ℳ r ↔ ∀ {a b : M} (_ : r a b), ∀ i, r (decompose ℳ a i) (decompose ℳ b i) :=
  Iff.rfl

omit [AddSubmonoidClass σ M] in
/-- A substructure `p ⊆ M` is homogeneous if for every `m ∈ p`, all homogeneous components
  of `m` are in `p`. -/
def SetLike.IsHomogeneous {P : Type*} [SetLike P M] (p : P) : Prop :=
  ∀ (i : ι) ⦃m : M⦄, m ∈ p → (DirectSum.decompose ℳ m i : M) ∈ p

@[elab_as_elim]
protected theorem Decomposition.inductionOn {motive : M → Prop} (zero : motive 0)
    (homogeneous : ∀ {i} (m : ℳ i), motive (m : M))
    (add : ∀ m m' : M, motive m → motive m' → motive (m + m')) : ∀ m, motive m := by
  let ℳ' : ι → AddSubmonoid M := fun i ↦
    (⟨⟨ℳ i, fun x y ↦ AddMemClass.add_mem x y⟩, (ZeroMemClass.zero_mem _)⟩ : AddSubmonoid M)
  haveI t : DirectSum.Decomposition ℳ' :=
    { decompose' := DirectSum.decompose ℳ
      left_inv := fun _ ↦ (decompose ℳ).left_inv _
      right_inv := fun _ ↦ (decompose ℳ).right_inv _ }
  have mem : ∀ m, m ∈ iSup ℳ' := fun _m ↦
    (DirectSum.IsInternal.addSubmonoid_iSup_eq_top ℳ' (Decomposition.isInternal ℳ')).symm ▸ trivial
  -- Porting note: needs to use @ even though no implicit argument is provided
  exact fun m ↦ @AddSubmonoid.iSup_induction _ _ _ ℳ' _ _ (mem m)
    (fun i m h ↦ homogeneous ⟨m, h⟩) zero add
--  exact fun m ↦
--    AddSubmonoid.iSup_induction ℳ' (mem m) (fun i m h ↦ h_homogeneous ⟨m, h⟩) h_zero h_add

@[simp]
theorem Decomposition.decompose'_eq : Decomposition.decompose' = decompose ℳ := rfl

@[simp]
theorem decompose_symm_of {i : ι} (x : ℳ i) : (decompose ℳ).symm (DirectSum.of _ i x) = x :=
  DirectSum.coeAddMonoidHom_of ℳ _ _

@[simp]
theorem decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (x : M) = DirectSum.of _ i x := by
  rw [← decompose_symm_of _, Equiv.apply_symm_apply]

theorem decompose_of_mem {x : M} {i : ι} (hx : x ∈ ℳ i) :
    decompose ℳ x = DirectSum.of (fun i ↦ ℳ i) i ⟨x, hx⟩ :=
  decompose_coe _ ⟨x, hx⟩

theorem decompose_of_mem_same {x : M} {i : ι} (hx : x ∈ ℳ i) :
    (decompose ℳ x i) = (⟨x, hx⟩ : ℳ i) := by
  rw [decompose_of_mem _ hx, DirectSum.of_eq_same]

theorem coe_decompose_of_mem_same {x : M} {i : ι} (hx : x ∈ ℳ i) : (decompose ℳ x i : M) = x := by
  simp [decompose_of_mem_same _ hx]

theorem decompose_of_mem_ne {x : M} {i j : ι} (hx : x ∈ ℳ i) (hij : i ≠ j) :
    (decompose ℳ x j) = 0 := by
  rw [decompose_of_mem _ hx, DirectSum.of_eq_of_ne _ _ _ hij.symm]

theorem coe_decompose_of_mem_ne {x : M} {i j : ι} (hx : x ∈ ℳ i) (hij : i ≠ j) :
    (decompose ℳ x j : M) = 0 := by
  simp [decompose_of_mem_ne _ hx hij]

theorem degree_eq_of_mem_mem {x : M} {i j : ι} (hxi : x ∈ ℳ i) (hxj : x ∈ ℳ j) (hx : x ≠ 0) :
    i = j := by
  contrapose! hx; rw [← coe_decompose_of_mem_same ℳ hxj, coe_decompose_of_mem_ne ℳ hxi hx]

theorem mem_iff_exists_decompose_eq_of_same {m : M} {i : ι} :
    m ∈ ℳ i ↔ ∃ x, decompose ℳ m = DirectSum.of (fun i ↦ ℳ i) i x := by
  constructor
  · intro hm
    use decompose ℳ m i
    rw [← Equiv.eq_symm_apply, decompose_symm_of, coe_decompose_of_mem_same ℳ hm]
  · rintro ⟨⟨x, xmem⟩, hx⟩
    simp only [← Equiv.eq_symm_apply, decompose_symm_of] at hx
    rwa [hx]

theorem mem_iff_forall_ne_decompose_eq_zero {m : M} {i : ι} :
    m ∈ ℳ i ↔ ∀ j ≠ i, decompose ℳ m j = 0 := by
  constructor
  · intro hm j hj
    simpa using DirectSum.decompose_of_mem_ne ℳ hm (Ne.symm hj)
  · intro hm
    rw [mem_iff_exists_decompose_eq_of_same]
    use decompose ℳ m i
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [SetLike.coe_eq_coe, hm j hj, eq_comm, of_eq_of_ne _ _ _ hj]

lemma Rel.IsPureHomogeneous.isHomogeneous (r : M → M → Prop)
    (hr0 : r 0 0) (hr : Rel.IsPureHomogeneous ℳ r) :
    Rel.IsHomogeneous ℳ r := by
  intro a b h i
  obtain ⟨j, ha, hb⟩ := hr h
  by_cases hij : j = i
  · simp [← hij, decompose_of_mem_same, ha, hb, h]
  · simp [decompose_of_mem_ne _ ha hij, decompose_of_mem_ne _ hb hij, hr0]

open Relation in
theorem Rel.IsHomogeneous.eqvGenIsHomogeneous (r : M → M → Prop) (hr : Rel.IsHomogeneous ℳ r) :
    Rel.IsHomogeneous ℳ (EqvGen r) := by
  intro a b h
  induction h with grind [EqvGen, IsHomogeneous]

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
an additive monoid to a direct sum of components. -/
@[simps!]
def decomposeAddEquiv : M ≃+ ⨁ i, ℳ i :=
  AddEquiv.symm { (decompose ℳ).symm with map_add' := map_add (DirectSum.coeAddMonoidHom ℳ) }

@[simp]
theorem decompose_zero : decompose ℳ (0 : M) = 0 :=
  map_zero (decomposeAddEquiv ℳ)

@[simp]
theorem decompose_symm_zero : (decompose ℳ).symm 0 = (0 : M) :=
  map_zero (decomposeAddEquiv ℳ).symm

@[simp]
theorem decompose_add (x y : M) : decompose ℳ (x + y) = decompose ℳ x + decompose ℳ y :=
  map_add (decomposeAddEquiv ℳ) x y

@[simp]
theorem decompose_symm_add (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x + y) = (decompose ℳ).symm x + (decompose ℳ).symm y :=
  map_add (decomposeAddEquiv ℳ).symm x y

@[simp]
theorem decompose_sum {ι'} (s : Finset ι') (f : ι' → M) :
    decompose ℳ (∑ i ∈ s, f i) = ∑ i ∈ s, decompose ℳ (f i) :=
  map_sum (decomposeAddEquiv ℳ) f s

@[simp]
theorem decompose_symm_sum {ι'} (s : Finset ι') (f : ι' → ⨁ i, ℳ i) :
    (decompose ℳ).symm (∑ i ∈ s, f i) = ∑ i ∈ s, (decompose ℳ).symm (f i) :=
  map_sum (decomposeAddEquiv ℳ).symm f s

theorem sum_support_decompose [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (r : M) :
    (∑ i ∈ (decompose ℳ r).support, (decompose ℳ r i : M)) = r := by
  conv_rhs =>
    rw [← (decompose ℳ).symm_apply_apply r, ← sum_support_of (decompose ℳ r)]
  rw [decompose_symm_sum]
  simp_rw [decompose_symm_of]

theorem AddSubmonoidClass.IsHomogeneous.mem_iff
    {P : Type*} [SetLike P M] [AddSubmonoidClass P M] (p : P)
    (hp : SetLike.IsHomogeneous ℳ p) {x} :
    x ∈ p ↔ ∀ i, (decompose ℳ x i : M) ∈ p := by
  classical
  refine ⟨fun hx i ↦ hp i hx, fun hx ↦ ?_⟩
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact sum_mem (fun i _ ↦ hx i)

theorem AddSubmonoidClass.IsHomogeneous.ext
    {ℳ : ι → σ} [Decomposition ℳ] {P : Type*} [SetLike P M] [AddSubmonoidClass P M]
    {p q : P} (hp : SetLike.IsHomogeneous ℳ p) (hq : SetLike.IsHomogeneous ℳ q)
    (hpq : ∀ i, ∀ m ∈ ℳ i, m ∈ p ↔ m ∈ q) :
    p = q := by
  refine SetLike.ext fun m ↦ ?_
  rw [AddSubmonoidClass.IsHomogeneous.mem_iff ℳ p hp,
    AddSubmonoidClass.IsHomogeneous.mem_iff ℳ q hq]
  exact forall_congr' fun i ↦ hpq i _ (decompose ℳ _ i).2

end AddCommMonoid

section AddCommGroup

variable [DecidableEq ι] [AddCommGroup M]
variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)
variable [Decomposition ℳ]

@[simp]
theorem decompose_neg (x : M) : decompose ℳ (-x) = -decompose ℳ x :=
  map_neg (decomposeAddEquiv ℳ) x

@[simp]
theorem decompose_symm_neg (x : ⨁ i, ℳ i) : (decompose ℳ).symm (-x) = -(decompose ℳ).symm x :=
  map_neg (decomposeAddEquiv ℳ).symm x

@[simp]
theorem decompose_sub (x y : M) : decompose ℳ (x - y) = decompose ℳ x - decompose ℳ y :=
  map_sub (decomposeAddEquiv ℳ) x y

@[simp]
theorem decompose_symm_sub (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x - y) = (decompose ℳ).symm x - (decompose ℳ).symm y :=
  map_sub (decomposeAddEquiv ℳ).symm x y

end AddCommGroup

section Module

variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]
variable (ℳ : ι → Submodule R M)

theorem coeLinearMap_apply [Decomposition ℳ] (x : ⨁ i, ℳ i) :
  coeLinearMap ℳ x = (decompose ℳ).symm x := rfl

/-- A convenience method to construct a decomposition from an `LinearMap`, such that the proofs
of left and right inverse can be constructed via `ext`. -/
abbrev Decomposition.ofLinearMap (decompose : M →ₗ[R] ⨁ i, ℳ i)
    (h_left_inv : DirectSum.coeLinearMap ℳ ∘ₗ decompose = .id)
    (h_right_inv : decompose ∘ₗ DirectSum.coeLinearMap ℳ = .id) : Decomposition ℳ where
  decompose' := decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv

variable [Decomposition ℳ]

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
a module to a direct sum of components. -/
def decomposeLinearEquiv : M ≃ₗ[R] ⨁ i, ℳ i :=
  LinearEquiv.symm
    { (decomposeAddEquiv ℳ).symm with map_smul' := map_smul (DirectSum.coeLinearMap ℳ) }

theorem decomposeLinearEquiv_apply (m : M) :
    decomposeLinearEquiv ℳ m = decompose ℳ m := rfl

theorem decomposeLinearEquiv_symm_apply (m : ⨁ i, ℳ i) :
    (decomposeLinearEquiv ℳ).symm m = (decompose ℳ).symm m := rfl

@[simp]
theorem decompose_smul (r : R) (x : M) : decompose ℳ (r • x) = r • decompose ℳ x :=
  map_smul (decomposeLinearEquiv ℳ) r x

@[simp] theorem decomposeLinearEquiv_symm_comp_lof (i : ι) :
    (decomposeLinearEquiv ℳ).symm ∘ₗ lof R ι (ℳ ·) i = (ℳ i).subtype :=
  LinearMap.ext <| decompose_symm_of _

@[simp] lemma decomposeLinearEquiv_symm_lof (i : ι) (x : ℳ i) :
    (decomposeLinearEquiv ℳ).symm (lof R _ _ i x) = x :=
  congr($(decomposeLinearEquiv_symm_comp_lof ℳ i) x)

@[simp] lemma decomposeLinearEquiv_apply_coe (i : ι) (x : ℳ i) :
    decomposeLinearEquiv ℳ x = lof R _ _ i x :=
  (LinearEquiv.eq_symm_apply _).mp (decomposeLinearEquiv_symm_lof ..).symm

/-- Two linear maps from a module with a decomposition agree if they agree on every piece.

Note this cannot be `@[ext]` as `ℳ` cannot be inferred. -/
theorem decompose_lhom_ext {N} [AddCommMonoid N] [Module R N] ⦃f g : M →ₗ[R] N⦄
    (h : ∀ i, f ∘ₗ (ℳ i).subtype = g ∘ₗ (ℳ i).subtype) : f = g :=
  LinearMap.ext <| (decomposeLinearEquiv ℳ).symm.surjective.forall.mpr <|
    suffices f ∘ₗ (decomposeLinearEquiv ℳ).symm
           = (g ∘ₗ (decomposeLinearEquiv ℳ).symm : (⨁ i, ℳ i) →ₗ[R] N) from
      DFunLike.congr_fun this
    linearMap_ext _ fun i => by
      simp_rw [LinearMap.comp_assoc, decomposeLinearEquiv_symm_comp_lof ℳ i, h]

end Module

end DirectSum
