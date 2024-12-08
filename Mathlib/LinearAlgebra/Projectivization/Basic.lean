/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!

# Projective Spaces

This file contains the definition of the projectivization of a vector space over a field,
as well as the bijection between said projectivization and the collection of all one
dimensional subspaces of the vector space.

## Notation
`ℙ K V` is localized notation for `Projectivization K V`, the projectivization of a `K`-vector
space `V`.

## Constructing terms of `ℙ K V`.
We have three ways to construct terms of `ℙ K V`:
- `Projectivization.mk K v hv` where `v : V` and `hv : v ≠ 0`.
- `Projectivization.mk' K v` where `v : { w : V // w ≠ 0 }`.
- `Projectivization.mk'' H h` where `H : Submodule K V` and `h : finrank H = 1`.

## Other definitions
- For `v : ℙ K V`, `v.submodule` gives the corresponding submodule of `V`.
- `Projectivization.equivSubmodule` is the equivalence between `ℙ K V`
  and `{ H : Submodule K V // finrank H = 1 }`.
- For `v : ℙ K V`, `v.rep : V` is a representative of `v`.

-/

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The setoid whose quotient is the projectivization of `V`. -/
def projectivizationSetoid : Setoid { v : V // v ≠ 0 } :=
  (MulAction.orbitRel Kˣ V).comap (↑)

/-- The projectivization of the `K`-vector space `V`.
The notation `ℙ K V` is preferred. -/
def Projectivization := Quotient (projectivizationSetoid K V)

/-- We define notations `ℙ K V` for the projectivization of the `K`-vector space `V`. -/
scoped[LinearAlgebra.Projectivization] notation "ℙ" => Projectivization

namespace Projectivization

open scoped LinearAlgebra.Projectivization

variable {V}

/-- Construct an element of the projectivization from a nonzero vector. -/
def mk (v : V) (hv : v ≠ 0) : ℙ K V :=
  Quotient.mk'' ⟨v, hv⟩

/-- A variant of `Projectivization.mk` in terms of a subtype. `mk` is preferred. -/
def mk' (v : { v : V // v ≠ 0 }) : ℙ K V :=
  Quotient.mk'' v

@[simp]
theorem mk'_eq_mk (v : { v : V // v ≠ 0 }) : mk' K v = mk K ↑v v.2 := rfl

instance [Nontrivial V] : Nonempty (ℙ K V) :=
  let ⟨v, hv⟩ := exists_ne (0 : V)
  ⟨mk K v hv⟩

variable {K}

/-- A function on non-zero vectors which is independent of scale, descends to a function on the
projectivization. -/
protected def lift {α : Type*} (f : { v : V // v ≠ 0 } → α)
    (hf : ∀ (a b : { v : V // v ≠ 0 }) (t : K), a = t • (b : V) → f a = f b)
    (x : ℙ K V) : α :=
  Quotient.lift f (by rintro ⟨-, hv⟩ ⟨w, hw⟩ ⟨⟨t, -⟩, rfl⟩; exact hf ⟨_, hv⟩ ⟨w, hw⟩ t rfl) x

@[simp]
protected lemma lift_mk {α : Type*} (f : { v : V // v ≠ 0 } → α)
    (hf : ∀ (a b : { v : V // v ≠ 0 }) (t : K), a = t • (b : V) → f a = f b)
    (v : V) (hv : v ≠ 0) :
    Projectivization.lift f hf (mk K v hv) = f ⟨v, hv⟩ :=
  rfl

/-- Choose a representative of `v : Projectivization K V` in `V`. -/
protected noncomputable def rep (v : ℙ K V) : V :=
  v.out

theorem rep_nonzero (v : ℙ K V) : v.rep ≠ 0 :=
  v.out.2

@[simp]
theorem mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero = v := Quotient.out_eq' _

open Module

/-- Consider an element of the projectivization as a submodule of `V`. -/
protected def submodule (v : ℙ K V) : Submodule K V :=
  (Quotient.liftOn' v fun v => K ∙ (v : V)) <| by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨x, rfl : x • b = a⟩
    exact Submodule.span_singleton_group_smul_eq _ x _

variable (K)

theorem mk_eq_mk_iff (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk K v hv = mk K w hw ↔ ∃ a : Kˣ, a • w = v :=
  Quotient.eq''

/-- Two nonzero vectors go to the same point in projective space if and only if one is
a scalar multiple of the other. -/
theorem mk_eq_mk_iff' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk K v hv = mk K w hw ↔ ∃ a : K, a • w = v := by
  rw [mk_eq_mk_iff K v w hv hw]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨Units.mk0 a fun c => hv.symm ?_, ha⟩
    rwa [c, zero_smul] at ha

theorem exists_smul_eq_mk_rep (v : V) (hv : v ≠ 0) : ∃ a : Kˣ, a • v = (mk K v hv).rep :=
  (mk_eq_mk_iff K _ _ (rep_nonzero _) hv).1 (mk_rep _)

variable {K}

/-- An induction principle for `Projectivization`. Use as `induction v`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
theorem ind {P : ℙ K V → Prop} (h : ∀ (v : V) (h : v ≠ 0), P (mk K v h)) : ∀ p, P p :=
  Quotient.ind' <| Subtype.rec <| h

@[simp]
theorem submodule_mk (v : V) (hv : v ≠ 0) : (mk K v hv).submodule = K ∙ v :=
  rfl

theorem submodule_eq (v : ℙ K V) : v.submodule = K ∙ v.rep := by
  conv_lhs => rw [← v.mk_rep]
  rfl

theorem finrank_submodule (v : ℙ K V) : finrank K v.submodule = 1 := by
  rw [submodule_eq]
  exact finrank_span_singleton v.rep_nonzero

instance (v : ℙ K V) : FiniteDimensional K v.submodule := by
  rw [← v.mk_rep]
  change FiniteDimensional K (K ∙ v.rep)
  infer_instance

theorem submodule_injective :
    Function.Injective (Projectivization.submodule : ℙ K V → Submodule K V) := fun u v h ↦ by
  induction' u using ind with u hu
  induction' v using ind with v hv
  rw [submodule_mk, submodule_mk, Submodule.span_singleton_eq_span_singleton] at h
  exact ((mk_eq_mk_iff K v u hv hu).2 h).symm

variable (K V)

/-- The equivalence between the projectivization and the
collection of subspaces of dimension 1. -/
noncomputable def equivSubmodule : ℙ K V ≃ { H : Submodule K V // finrank K H = 1 } :=
  (Equiv.ofInjective _ submodule_injective).trans <| .subtypeEquiv (.refl _) fun H ↦ by
    refine ⟨fun ⟨v, hv⟩ ↦ hv ▸ v.finrank_submodule, fun h ↦ ?_⟩
    rcases finrank_eq_one_iff'.1 h with ⟨v : H, hv₀, hv : ∀ w : H, _⟩
    use mk K (v : V) (Subtype.coe_injective.ne hv₀)
    rw [submodule_mk, SetLike.ext'_iff, Submodule.span_singleton_eq_range]
    refine (Set.range_subset_iff.2 fun _ ↦ H.smul_mem _ v.2).antisymm fun x hx ↦ ?_
    rcases hv ⟨x, hx⟩ with ⟨c, hc⟩
    exact ⟨c, congr_arg Subtype.val hc⟩

variable {K V}

/-- Construct an element of the projectivization from a subspace of dimension 1. -/
noncomputable def mk'' (H : Submodule K V) (h : finrank K H = 1) : ℙ K V :=
  (equivSubmodule K V).symm ⟨H, h⟩

@[simp]
theorem submodule_mk'' (H : Submodule K V) (h : finrank K H = 1) : (mk'' H h).submodule = H :=
  congr_arg Subtype.val <| (equivSubmodule K V).apply_symm_apply ⟨H, h⟩

@[simp]
theorem mk''_submodule (v : ℙ K V) : mk'' v.submodule v.finrank_submodule = v :=
  (equivSubmodule K V).symm_apply_apply v

section Map

variable {L W : Type*} [DivisionRing L] [AddCommGroup W] [Module L W]

/-- An injective semilinear map of vector spaces induces a map on projective spaces. -/
def map {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : Function.Injective f) : ℙ K V → ℙ L W :=
  Quotient.map' (fun v => ⟨f v, fun c => v.2 (hf (by simp [c]))⟩)
    (by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨a, ha⟩
      use Units.map σ.toMonoidHom a
      dsimp at ha ⊢
      erw [← f.map_smulₛₗ, ha])

theorem map_mk {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : Function.Injective f) (v : V) (hv : v ≠ 0) :
    map f hf (mk K v hv) = mk L (f v) (map_zero f ▸ hf.ne hv) :=
  rfl

/-- Mapping with respect to a semilinear map over an isomorphism of fields yields
an injective map on projective spaces. -/
theorem map_injective {σ : K →+* L} {τ : L →+* K} [RingHomInvPair σ τ] (f : V →ₛₗ[σ] W)
    (hf : Function.Injective f) : Function.Injective (map f hf) := fun u v h ↦ by
  induction' u using ind with u hu; induction' v using ind with v hv
  simp only [map_mk, mk_eq_mk_iff'] at h ⊢
  rcases h with ⟨a, ha⟩
  refine ⟨τ a, hf ?_⟩
  rwa [f.map_smulₛₗ, RingHomInvPair.comp_apply_eq₂]

@[simp]
theorem map_id : map (LinearMap.id : V →ₗ[K] V) (LinearEquiv.refl K V).injective = id := by
  ext ⟨v⟩
  rfl

-- Porting note: removed `@[simp]` because of unusable `hg.comp hf` in the LHS
theorem map_comp {F U : Type*} [Field F] [AddCommGroup U] [Module F U] {σ : K →+* L} {τ : L →+* F}
    {γ : K →+* F} [RingHomCompTriple σ τ γ] (f : V →ₛₗ[σ] W) (hf : Function.Injective f)
    (g : W →ₛₗ[τ] U) (hg : Function.Injective g) :
    map (g.comp f) (hg.comp hf) = map g hg ∘ map f hf := by
  ext ⟨v⟩
  rfl

end Map

section Cardinality

section

variable {α : Type*} (β : Type*) [Group α] [MulAction α β] (b : β)

variable (α)

/-- If `α` acts on `β` with trivial stabilizers, `β` is equivalent
to the product of the quotient of `β` by `α` and `α`.
See `MulAction.selfEquivOrbitsQuotientProd` with `φ = Quotient.out`. -/
noncomputable def MulAction.selfEquivOrbitsQuotientProd'
    {φ : Quotient (MulAction.orbitRel α β) → β} (hφ : Function.LeftInverse Quotient.mk'' φ)
    (h : ∀ b : β, MulAction.stabilizer α b = ⊥) :
    β ≃ Quotient (MulAction.orbitRel α β) × α :=
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer' α β hφ).trans <|
    (Equiv.sigmaCongrRight <| fun _ ↦
      (Subgroup.quotientEquivOfEq (h _)).trans (QuotientGroup.quotientBot).toEquiv).trans <|
    Equiv.sigmaEquivProd _ _

/-- If `α` acts on `β` with trivial stabilizers, `β` is equivalent
to the product of the quotient of `β` by `α` and `α`. -/
noncomputable def MulAction.selfEquivOrbitsQuotientProd
    (h : ∀ b : β, MulAction.stabilizer α b = ⊥) :
    β ≃ Quotient (MulAction.orbitRel α β) × α :=
  MulAction.selfEquivOrbitsQuotientProd' α β Quotient.out_eq' h

end

section

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/-- The units of `R` act on the non-zero elements of `M`. -/
instance : SMul Rˣ { x : M // x ≠ 0 } where
  smul a v := ⟨a • v, by simpa [Units.smul_def] using v.property⟩

@[simp]
lemma smul_coe (a : Rˣ) (x : { x : M // x ≠ 0 }) :
    (a • x).val = a • x.val :=
  rfl

instance : MulAction Rˣ { v : M // v ≠ 0 } where
  one_smul v := by ext; simp
  mul_smul a b x := by ext; simp [mul_smul]

lemma orbitRel_iff (x y : { v : M // v ≠ 0 }) :
    MulAction.orbitRel Rˣ { v // v ≠ 0 } x y ↔ MulAction.orbitRel Rˣ M x.val y.val :=
  ⟨by rintro ⟨a, rfl⟩; exact ⟨a, by simp⟩, by intro ⟨a, ha⟩; exact ⟨a, by ext; simpa⟩⟩

lemma comap_orbitRel_eq_orbitRel :
    (MulAction.orbitRel Rˣ M).comap (↑) = MulAction.orbitRel Rˣ { v : M // v ≠ 0 } := by
  ext x y
  rw [Setoid.comap_rel, orbitRel_iff]

end

section

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]

lemma stabilizer_eq_bot (x : { v : M // v ≠ 0 }) : MulAction.stabilizer Rˣ x = ⊥ := by
  rw [eq_bot_iff]
  intro g (hg : g • x = x)
  ext
  simp only [Subtype.ext_iff, ne_eq, smul_coe, Units.smul_def] at hg
  rw [← sub_eq_zero, ← smul_eq_zero_iff_left x.property]
  simp [sub_smul, hg]

end

section

variable (k V : Type*) [DivisionRing k] [AddCommGroup V] [Module k V]

/-- `ℙ k V` is equivalent to the quotient of the non-zero elements of `V` by `kˣ`. -/
def equivQuotientOrbitRel : ℙ k V ≃ Quotient (MulAction.orbitRel kˣ { v : V // v ≠ 0 }) :=
  Quotient.congr (Equiv.refl _) (fun x y ↦ (orbitRel_iff k V x y).symm)

/-- The non-zero elements of `V` are equivalent to the product of `ℙ k V` with the units of `k`. -/
noncomputable def nonZeroEquivProjectivizationProdUnits : { v : V // v ≠ 0 } ≃ ℙ k V × kˣ :=
  let e := MulAction.selfEquivOrbitsQuotientProd _ _ (stabilizer_eq_bot k V)
  e.trans (Equiv.prodCongrLeft (fun _ ↦ (equivQuotientOrbitRel k V).symm))

/-- If `V` is a finite `k`-module and `k` is finite, `ℙ k V` is finite. -/
instance finite_of_finite [Finite k] [Finite V] : Finite (ℙ k V) :=
  have : Finite (ℙ k V × kˣ) := Finite.of_equiv _ (nonZeroEquivProjectivizationProdUnits k V)
  Finite.prod_left kˣ

/-- Fraction free cardinality formula for the points of `ℙ k V` if `k` and `V` are finite.
See `Projectivization.card'` and `Projectivization.card''` for other spellings of the formula. -/
lemma card [Finite k] [Finite V] :
    Nat.card V - 1 = Nat.card (ℙ k V) * (Nat.card k - 1) := by
  classical
  haveI : Finite V := Module.finite_of_finite k
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (ℙ k V) := Fintype.ofFinite (ℙ k V)
  haveI : Fintype k := Fintype.ofFinite k
  have hV : Fintype.card { v : V // v ≠ 0 } = Fintype.card V - 1 := by simp
  simp_rw [← Fintype.card_eq_nat_card, ← Fintype.card_units (α := k), ← hV]
  rw [Fintype.card_congr (nonZeroEquivProjectivizationProdUnits k V), Fintype.card_prod]

/-- Cardinality formula for the points of `ℙ k V` if `k` and `V` are finite with less
natural subtraction. -/
lemma card' [Finite k] [Finite V] :
    Nat.card V = Nat.card (ℙ k V) * (Nat.card k - 1) + 1 := by
  rw [← card k V]
  have : Nat.card V > 0 := Nat.card_pos
  omega

end

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]

/-- Cardinality formula for the points of `ℙ k V` if `k` and `V` are finite expressed
as a fraction. -/
lemma card'' [Finite k] [Finite V] :
    Nat.card (ℙ k V) = (Nat.card V - 1) / (Nat.card k - 1) := by
  haveI : Fintype k := Fintype.ofFinite k
  rw [card k]
  have : 2 ≤ Nat.card k := FiniteField.two_le_card k
  have h : 0 ≠ (Nat.card k - 1) := by omega
  exact Nat.eq_div_of_mul_eq_left (Ne.symm h) rfl

lemma card_of_finrank_two [Finite k] (h : Module.finrank k V = 2) :
    Nat.card (ℙ k V) = Nat.card k + 1 := by
  have : 2 ≤ Nat.card k := FiniteField.two_le_card k
  have h' : Nat.card k - 1 ≠ 0 := by omega
  have : Module.Finite k V := Module.finite_of_finrank_eq_succ h
  have : Finite V := Module.finite_of_finite k
  let e : V ≃ₗ[k] (Fin 2 → k) := LinearEquiv.ofFinrankEq _ _ (by simpa)
  have : Nat.card V = Nat.card k ^ 2 := by
    simp only [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [card'', this, Nat.sq_sub_sq _ 1]
  exact (Nat.eq_div_of_mul_eq_left h' rfl).symm

end Cardinality

end Projectivization
