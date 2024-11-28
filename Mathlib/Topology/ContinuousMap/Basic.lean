/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.Data.Set.UnionLift
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.Homeomorph

/-!
# Continuous bundled maps

In this file we define the type `ContinuousMap` of continuous bundled maps.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.
-/


open Function Topology

section ContinuousMapClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β]
variable [ContinuousMapClass F α β]

theorem map_continuousAt (f : F) (a : α) : ContinuousAt f a :=
  (map_continuous f).continuousAt

theorem map_continuousWithinAt (f : F) (s : Set α) (a : α) : ContinuousWithinAt f s a :=
  (map_continuous f).continuousWithinAt

end ContinuousMapClass

/-! ### Continuous maps -/


namespace ContinuousMap

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

variable {f g : C(α, β)}

/-- Deprecated. Use `map_continuousAt` instead. -/
protected theorem continuousAt (f : C(α, β)) (x : α) : ContinuousAt f x :=
  map_continuousAt f x

theorem map_specializes (f : C(α, β)) {x y : α} (h : x ⤳ y) : f x ⤳ f y :=
  h.map f.2

section

variable (α β)

/--
The continuous functions from `α` to `β` are the same as the plain functions when `α` is discrete.
-/
@[simps]
def equivFnOfDiscrete [DiscreteTopology α] : C(α, β) ≃ (α → β) :=
  ⟨fun f => f,
    fun f => ⟨f, continuous_of_discreteTopology⟩,
    fun _ => by ext; rfl,
    fun _ => by ext; rfl⟩

end

variable (α)

/-- The identity as a continuous map. -/
protected def id : C(α, α) where
  toFun := id

@[simp]
theorem coe_id : ⇑(ContinuousMap.id α) = id :=
  rfl

/-- The constant map as a continuous map. -/
def const (b : β) : C(α, β) where
  toFun := fun _ : α => b

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

/-- `Function.const α b` as a bundled continuous function of `b`. -/
@[simps (config := .asFn)]
def constPi : C(β, α → β) where
  toFun b := Function.const α b

instance [Inhabited β] : Inhabited C(α, β) :=
  ⟨const α default⟩

variable {α}

@[simp]
theorem id_apply (a : α) : ContinuousMap.id α a = a :=
  rfl

@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

/-- The composition of continuous maps, as a continuous map. -/
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) where
  toFun := f ∘ g

@[simp]
theorem coe_comp (f : C(β, γ)) (g : C(α, β)) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : C(γ, δ)) (g : C(β, γ)) (h : C(α, β)) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem id_comp (f : C(α, β)) : (ContinuousMap.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : C(α, β)) : f.comp (ContinuousMap.id _) = f :=
  ext fun _ => rfl

@[simp]
theorem const_comp (c : γ) (f : C(α, β)) : (const β c).comp f = const α c :=
  ext fun _ => rfl

@[simp]
theorem comp_const (f : C(β, γ)) (b : β) : f.comp (const α b) = const α (f b) :=
  ext fun _ => rfl

@[simp]
theorem cancel_right {f₁ f₂ : C(β, γ)} {g : C(α, β)} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h ↦ ext <| hg.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (ContinuousMap.comp · g)⟩

@[simp]
theorem cancel_left {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h ↦ ext fun a ↦ hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

instance [Nonempty α] [Nontrivial β] : Nontrivial C(α, β) :=
  ⟨let ⟨b₁, b₂, hb⟩ := exists_pair_ne β
  ⟨const _ b₁, const _ b₂, fun h ↦ hb <| DFunLike.congr_fun h <| Classical.arbitrary α⟩⟩

section Prod

variable {α₁ α₂ β₁ β₂ : Type*} [TopologicalSpace α₁] [TopologicalSpace α₂] [TopologicalSpace β₁]
  [TopologicalSpace β₂]

/-- `Prod.fst : (x, y) ↦ x` as a bundled continuous map. -/
@[simps (config := .asFn)]
def fst : C(α × β, α) where
  toFun := Prod.fst

/-- `Prod.snd : (x, y) ↦ y` as a bundled continuous map. -/
@[simps (config := .asFn)]
def snd : C(α × β, β) where
  toFun := Prod.snd

/-- Given two continuous maps `f` and `g`, this is the continuous map `x ↦ (f x, g x)`. -/
def prodMk (f : C(α, β₁)) (g : C(α, β₂)) : C(α, β₁ × β₂) where
  toFun x := (f x, g x)

/-- Given two continuous maps `f` and `g`, this is the continuous map `(x, y) ↦ (f x, g y)`. -/
@[simps]
def prodMap (f : C(α₁, α₂)) (g : C(β₁, β₂)) : C(α₁ × β₁, α₂ × β₂) where
  toFun := Prod.map f g

@[simp]
theorem prod_eval (f : C(α, β₁)) (g : C(α, β₂)) (a : α) : (prodMk f g) a = (f a, g a) :=
  rfl

/-- `Prod.swap` bundled as a `ContinuousMap`. -/
@[simps!]
def prodSwap : C(α × β, β × α) := .prodMk .snd .fst

end Prod

section Sigma

variable {I A : Type*} {X : I → Type*} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]

/-- `Sigma.mk i` as a bundled continuous map. -/
@[simps apply]
def sigmaMk (i : I) : C(X i, Σ i, X i) where
  toFun := Sigma.mk i

/--
To give a continuous map out of a disjoint union, it suffices to give a continuous map out of
each term. This is `Sigma.uncurry` for continuous maps.
-/
@[simps]
def sigma (f : ∀ i, C(X i, A)) : C((Σ i, X i), A) where
  toFun ig := f ig.fst ig.snd

variable (A X) in
/--
Giving a continuous map out of a disjoint union is the same as giving a continuous map out of
each term. This is a version of `Equiv.piCurry` for continuous maps.
-/
@[simps]
def sigmaEquiv : (∀ i, C(X i, A)) ≃ C((Σ i, X i), A) where
  toFun := sigma
  invFun f i := f.comp (sigmaMk i)
  left_inv := by intro; ext; simp
  right_inv := by intro; ext; simp

end Sigma

section Pi

variable {I A : Type*} {X Y : I → Type*} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (Y i)]

/-- Abbreviation for product of continuous maps, which is continuous -/
def pi (f : ∀ i, C(A, X i)) : C(A, ∀ i, X i) where
  toFun (a : A) (i : I) := f i a

@[simp]
theorem pi_eval (f : ∀ i, C(A, X i)) (a : A) : (pi f) a = fun i : I => (f i) a :=
  rfl

/-- Evaluation at point as a bundled continuous map. -/
@[simps (config := .asFn)]
def eval (i : I) : C(∀ j, X j, X i) where
  toFun := Function.eval i

variable (A X) in
/--
Giving a continuous map out of a disjoint union is the same as giving a continuous map out of
each term
-/
@[simps]
def piEquiv : (∀ i, C(A, X i)) ≃ C(A, ∀ i, X i) where
  toFun := pi
  invFun f i := (eval i).comp f
  left_inv := by intro; ext; simp [pi]
  right_inv := by intro; ext; simp [pi]

/-- Combine a collection of bundled continuous maps `C(X i, Y i)` into a bundled continuous map
`C(∀ i, X i, ∀ i, Y i)`. -/
@[simps!]
def piMap (f : ∀ i, C(X i, Y i)) : C((i : I) → X i, (i : I) → Y i) :=
  .pi fun i ↦ (f i).comp (eval i)

/-- "Precomposition" as a continuous map between dependent types. -/
def precomp {ι : Type*} (φ : ι → I) : C((i : I) → X i, (i : ι) → X (φ i)) :=
  ⟨_, Pi.continuous_precomp' φ⟩

end Pi

section Restrict

variable (s : Set α)

/-- The restriction of a continuous function `α → β` to a subset `s` of `α`. -/
def restrict (f : C(α, β)) : C(s, β) where
  toFun := f ∘ ((↑) : s → α)

@[simp]
theorem coe_restrict (f : C(α, β)) : ⇑(f.restrict s) = f ∘ ((↑) : s → α) :=
  rfl

@[simp]
theorem restrict_apply (f : C(α, β)) (s : Set α) (x : s) : f.restrict s x = f x :=
  rfl

@[simp]
theorem restrict_apply_mk (f : C(α, β)) (s : Set α) (x : α) (hx : x ∈ s) :
    f.restrict s ⟨x, hx⟩ = f x :=
  rfl

theorem injective_restrict [T2Space β] {s : Set α} (hs : Dense s) :
    Injective (restrict s : C(α, β) → C(s, β)) := fun f g h ↦
  DFunLike.ext' <| (map_continuous f).ext_on hs (map_continuous g) <|
    Set.restrict_eq_restrict_iff.1 <| congr_arg DFunLike.coe h

/-- The restriction of a continuous map to the preimage of a set. -/
@[simps]
def restrictPreimage (f : C(α, β)) (s : Set β) : C(f ⁻¹' s, s) :=
  ⟨s.restrictPreimage f, continuous_iff_continuousAt.mpr fun _ ↦
    (map_continuousAt f _).restrictPreimage⟩

end Restrict

section Gluing

variable {ι : Type*} (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
  (hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS : ∀ x : α, ∃ i, S i ∈ 𝓝 x)

/-- A family `φ i` of continuous maps `C(S i, β)`, where the domains `S i` contain a neighbourhood
of each point in `α` and the functions `φ i` agree pairwise on intersections, can be glued to
construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover : C(α, β) :=
  haveI H : ⋃ i, S i = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun x ↦ (hS x).imp fun _ ↦ mem_of_mem_nhds
  mk (Set.liftCover S (fun i ↦ φ i) hφ H) <| continuous_of_cover_nhds hS fun i ↦ by
    rw [continuousOn_iff_continuous_restrict]
    simpa (config := { unfoldPartialApp := true }) only [Set.restrict, Set.liftCover_coe]
      using map_continuous (φ i)

variable {S φ hφ hS}

@[simp]
theorem liftCover_coe {i : ι} (x : S i) : liftCover S φ hφ hS x = φ i x := by
  rw [liftCover, coe_mk, Set.liftCover_coe _]

@[simp]
theorem liftCover_restrict {i : ι} : (liftCover S φ hφ hS).restrict (S i) = φ i := by
  ext
  simp only [coe_restrict, Function.comp_apply, liftCover_coe]

variable (A : Set (Set α)) (F : ∀ s ∈ A, C(s, β))
  (hF : ∀ (s) (hs : s ∈ A) (t) (ht : t ∈ A) (x : α) (hxi : x ∈ s) (hxj : x ∈ t),
    F s hs ⟨x, hxi⟩ = F t ht ⟨x, hxj⟩)
  (hA : ∀ x : α, ∃ i ∈ A, i ∈ 𝓝 x)

/-- A family `F s` of continuous maps `C(s, β)`, where (1) the domains `s` are taken from a set `A`
of sets in `α` which contain a neighbourhood of each point in `α` and (2) the functions `F s` agree
pairwise on intersections, can be glued to construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover' : C(α, β) := by
  let S : A → Set α := (↑)
  let F : ∀ i : A, C(i, β) := fun i => F i i.prop
  refine liftCover S F (fun i j => hF i i.prop j j.prop) ?_
  intro x
  obtain ⟨s, hs, hsx⟩ := hA x
  exact ⟨⟨s, hs⟩, hsx⟩

variable {A F hF hA}

-- Porting note: did not need `by delta liftCover'; exact` in mathlib3; goal was
-- closed by `liftCover_coe x'`
-- Might be something to do with the `let`s in the definition of `liftCover'`?
@[simp]
theorem liftCover_coe' {s : Set α} {hs : s ∈ A} (x : s) : liftCover' A F hF hA x = F s hs x :=
  let x' : ((↑) : A → Set α) ⟨s, hs⟩ := x
  by delta liftCover'; exact liftCover_coe x'

-- Porting note: porting program suggested `ext <| liftCover_coe'`
@[simp]
theorem liftCover_restrict' {s : Set α} {hs : s ∈ A} :
    (liftCover' A F hF hA).restrict s = F s hs := ext <| liftCover_coe' (hF := hF) (hA := hA)

end Gluing

/-- `Set.inclusion` as a bundled continuous map. -/
def inclusion {s t : Set α} (h : s ⊆ t) : C(s, t) where
  toFun := Set.inclusion h
  continuous_toFun := continuous_inclusion h

end ContinuousMap

section Lift

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : C(X, Y)}

/-- `Setoid.quotientKerEquivOfRightInverse` as a homeomorphism. -/
@[simps!]
def Function.RightInverse.homeomorph {f' : C(Y, X)} (hf : Function.RightInverse f' f) :
    Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfRightInverse _ _ hf
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr (map_continuous f)
  continuous_invFun := continuous_quotient_mk'.comp (map_continuous f')

namespace Topology.IsQuotientMap

/--
The homeomorphism from the quotient of a quotient map to its codomain. This is
`Setoid.quotientKerEquivOfSurjective` as a homeomorphism.
-/
@[simps!]
noncomputable def homeomorph (hf : IsQuotientMap f) : Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfSurjective _ hf.surjective
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr hf.continuous
  continuous_invFun := by
    rw [hf.continuous_iff]
    convert continuous_quotient_mk'
    ext
    simp only [Equiv.invFun_as_coe, Function.comp_apply,
      (Setoid.quotientKerEquivOfSurjective f hf.surjective).symm_apply_eq]
    rfl

variable (hf : IsQuotientMap f) (g : C(X, Z)) (h : Function.FactorsThrough g f)

/-- Descend a continuous map, which is constant on the fibres, along a quotient map. -/
@[simps]
noncomputable def lift : C(Y, Z) where
  toFun := ((fun i ↦ Quotient.liftOn' i g (fun _ _ (hab : f _ = f _) ↦ h hab)) :
    Quotient (Setoid.ker f) → Z) ∘ hf.homeomorph.symm
  continuous_toFun := Continuous.comp (continuous_quot_lift _ g.2) (Homeomorph.continuous _)

/--
The obvious triangle induced by `IsQuotientMap.lift` commutes:
```
     g
  X --→ Z
  |   ↗
f |  / hf.lift g h
  v /
  Y
```
-/
@[simp]
theorem lift_comp : (hf.lift g h).comp f = g := by
  ext
  simpa using h (Function.rightInverse_surjInv _ _)

/-- `IsQuotientMap.lift` as an equivalence. -/
@[simps]
noncomputable def liftEquiv : { g : C(X, Z) // Function.FactorsThrough g f} ≃ C(Y, Z) where
  toFun g := hf.lift g g.prop
  invFun g := ⟨g.comp f, fun _ _ h ↦ by simp only [ContinuousMap.comp_apply]; rw [h]⟩
  left_inv := by intro; simp
  right_inv := by
    intro g
    ext a
    simpa using congrArg g (Function.rightInverse_surjInv hf.surjective a)

end Topology.IsQuotientMap
end Lift

namespace Homeomorph

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
variable (f : α ≃ₜ β) (g : β ≃ₜ γ)

instance instContinuousMapClass : ContinuousMapClass (α ≃ₜ β) α β where
  map_continuous f := f.continuous_toFun

/-- The forward direction of a homeomorphism, as a bundled continuous map. -/
@[simps, deprecated _root_.toContinuousMap (since := "2024-10-12")]
protected def toContinuousMap (e : α ≃ₜ β) : C(α, β) :=
  ⟨e, e.continuous_toFun⟩

attribute [deprecated ContinuousMap.coe_apply (since := "2024-10-12")] toContinuousMap_apply

@[simp]
theorem coe_refl : (Homeomorph.refl α : C(α, α)) = ContinuousMap.id α :=
  rfl

@[simp]
theorem coe_trans : (f.trans g : C(α, γ)) = (g : C(β, γ)).comp f :=
  rfl

/-- Left inverse to a continuous map from a homeomorphism, mirroring `Equiv.symm_comp_self`. -/
@[simp]
theorem symm_comp_toContinuousMap :
    (f.symm : C(β, α)).comp (f : C(α, β)) = ContinuousMap.id α := by
  rw [← coe_trans, self_trans_symm, coe_refl]

/-- Right inverse to a continuous map from a homeomorphism, mirroring `Equiv.self_comp_symm`. -/
@[simp]
theorem toContinuousMap_comp_symm :
    (f : C(α, β)).comp (f.symm : C(β, α)) = ContinuousMap.id β := by
  rw [← coe_trans, symm_trans_self, coe_refl]

end Homeomorph
