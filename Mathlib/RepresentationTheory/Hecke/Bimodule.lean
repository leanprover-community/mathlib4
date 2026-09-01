/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Hecke.Basic
public import Mathlib.RepresentationTheory.Hecke.LeftFiniteDoubleCoset
public import Mathlib.RepresentationTheory.Hecke.Multiplicity

/-!
# Hecke bimodules and action on Hecke modules

-/

@[expose] public section

variable {k : Type*} [CommRing k] {G : Type*} [Group G] {H H₁ H₂ H₃ : Subgroup G}
variable {V : Type*} [AddCommGroup V] [Module k V] {W : Type*} [AddCommGroup W] [Module k W]

open DoubleCoset MonoidAlgebra

namespace Representation

section Bimodule

variable (k H₁ H₂) in
abbrev HeckeBimodule := HeckeModule H₁ (ofMulAction k G (G ⧸ H₂))

variable (k) in
/-- tbd -/
noncomputable def doubleCosetVector : DoubleCoset₀ H₁ H₂ → k[G ⧸ H₂] :=
  fun x => ∑ᶠ (i : x.LeftDecomposition), cosetVector k i

lemma doubleCosetVector_def (x : DoubleCoset₀ H₁ H₂) :
    doubleCosetVector k x = ∑ᶠ (i : x.LeftDecomposition), cosetVector k i := rfl

lemma doubleCosetVector_eq_sum_rep (x : DoubleCoset₀ H₁ H₂) :
    doubleCosetVector k x =
      ∑ (i : LeftDecompQuotient H₁ H₂ x.rep), cosetVector k (i.out * x.rep : G) := by classical
  nth_rw 1 [← DoubleCoset₀.mk_rep x]
  rw [doubleCosetVector_def, ← finsum_comp_equiv LeftDecompQuotient.toLeftDecompositionEquiv]
  simp [finsum_eq_sum_of_fintype, LeftDecompQuotient.toLeftCoset_apply]

lemma doubleCosetVector_isInvariant (x : DoubleCoset₀ H₁ H₂) (h₁ : H₁) :
    ofMulAction k G (G ⧸ H₂) h₁ (doubleCosetVector k x) = doubleCosetVector k x := by
  simpa [doubleCosetVector_def, map_finsum _ (Set.toFinite _)] using
    finsum_comp_equiv (MulAction.toPerm h₁) (f := fun i : x.LeftDecomposition => cosetVector k i.1)

/-- tbd -/
noncomputable def HeckeBimodule.mk (x : DoubleCoset₀ H₁ H₂) : HeckeBimodule k H₁ H₂ :=
  HeckeModule.invariantsEquiv H₁ _ ⟨doubleCosetVector k x, doubleCosetVector_isInvariant x⟩

@[simp]
lemma HeckeBimodule.mk_apply (x : DoubleCoset₀ H₁ H₂) :
    mk x (cosetVector k (1 : G)) = doubleCosetVector k x := by
  simp [mk]

namespace HeckeBimodule

/-- tbd -/
private noncomputable abbrev eval₁ (f : HeckeBimodule k H₁ H₂) :
    k[G ⧸ H₂] := f (cosetVector k (1 : G))

private lemma eval₁_coeff_isInvariant (h₁ : H₁) (x : G ⧸ H₂) (f : HeckeBimodule k H₁ H₂) :
    f.eval₁.coeff ((h₁ : G) • x) = f.eval₁.coeff x := by
  have : ofMulAction k G (G ⧸ H₂) h₁ f.eval₁ = f.eval₁ := by
    simp [← IntertwiningMap.isIntertwining]
  simpa using congrArg (fun w => w.coeff ((h₁ : G) • x)) this.symm

private lemma isLeftFinite_of_eval₁_coeff_ne_zero (f : HeckeBimodule k H₁ H₂) (y : G)
    (hy : f.eval₁.coeff (y : G ⧸ H₂) ≠ 0) :
    IsLeftFinite H₁ H₂ y := by
  rw [isLeftFinite_iff, DoubleCoset.mk_degree]
  refine Nat.card_ne_zero.mpr ⟨⟨QuotientGroup.mk (1 : H₁)⟩, ?_⟩
  exact Finite.of_injective (β := f.eval₁.coeff.support)
    (fun z => ⟨LeftDecompQuotient.toLeftCoset z, by simpa [LeftDecompQuotient.toLeftCoset_apply]
      using (eval₁_coeff_isInvariant _ _ f).trans_ne hy⟩)
    fun _ _ h => LeftDecompQuotient.toLeftCoset_injective (congrArg Subtype.val h)

variable (k H₁ H₂)

/-- tbd -/
noncomputable def toHeckeCosetModuleMap :
    HeckeBimodule k H₁ H₂ →ₗ[k] k[DoubleCoset₀ H₁ H₂] where
  toFun f := comapDomain (fun x => (x.rep : G ⧸ H₂)) (fun x y hxy => by
    have := QuotientGroup.eq.mp hxy
    rw [← DoubleCoset₀.mk_rep x, ← DoubleCoset₀.mk_rep y, DoubleCoset₀.mk_eq_iff]
    exact ⟨1, H₁.one_mem, x.rep⁻¹ * y.rep, this, by simp⟩) (f (cosetVector k (1 : G)))
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

private lemma toHeckeCosetModuleMap_apply_coeff (x : DoubleCoset₀ H₁ H₂)
    (f : HeckeBimodule k H₁ H₂) :
    (toHeckeCosetModuleMap k H₁ H₂ f).coeff x = f.eval₁.coeff x.rep := rfl

private lemma toHeckeCosetModuleMap_apply_mk (x : DoubleCoset₀ H₁ H₂) :
    (toHeckeCosetModuleMap k H₁ H₂) (mk x) = single x 1
  := by classical
  ext y
  simp only [mk, doubleCosetVector_eq_sum_rep, toHeckeCosetModuleMap_apply_coeff,
    HeckeModule.invariantsEquiv_apply, map_one, map_sum, Module.End.one_apply, coeff_sum,
    coeff_single, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Finset.sum_boole]
  convert congrArg (fun (r : ℕ) => (r : k)) (LeftDecompQuotient.nat_card_fiber H₁ H₂ x.rep y.rep)
  · simp
  · rw [← DoubleCoset₀.coe_mk, ← DoubleCoset₀.coe_mk, DoubleCoset₀.mk_rep, DoubleCoset₀.mk_rep]
    simp

private lemma toHeckeCosetModuleMap.injective :
    Function.Injective (toHeckeCosetModuleMap k H₁ H₂) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  ext y
  simp only [IntertwiningMap.coe_zero, Pi.ofNat_apply, coeff_zero, Finsupp.coe_zero]
  by_contra! hy
  apply hy
  have : IsLeftFinite H₁ H₂ y.out := isLeftFinite_of_eval₁_coeff_ne_zero f y.out (by simp [hy])
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ :=
    DoubleCoset₀.mk_eq_iff.mp (DoubleCoset₀.mk_rep (DoubleCoset₀.mk H₁ H₂ y.out))
  rw [← QuotientGroup.out_eq' y, heq, QuotientGroup.mk_mul_of_mem _ hh₂]
  simp only [← smul_eq_mul, ← MulAction.Quotient.smul_mk, eval₁_coeff_isInvariant ⟨h₁, hh₁⟩]
  simpa [toHeckeCosetModuleMap_apply_coeff] using
    congrArg (fun f => f.coeff (DoubleCoset₀.mk H₁ H₂ y.out)) hf

/-- tbd -/
noncomputable def toHeckeCosetModuleInv :
    k[DoubleCoset₀ H₁ H₂] →ₗ[k] HeckeBimodule k H₁ H₂ :=
  Finsupp.lift _ k _ (fun x => mk x) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private lemma toHeckeCosetModuleInv_apply_single (x : DoubleCoset₀ H₁ H₂) :
    ((toHeckeCosetModuleInv k H₁ H₂) (single x 1)) = mk x := by
  simp [toHeckeCosetModuleInv]

private lemma toHeckeCosetModuleInv_isRightInv (x : k[DoubleCoset₀ H₁ H₂]) :
    toHeckeCosetModuleMap k H₁ H₂ (toHeckeCosetModuleInv k H₁ H₂ x) = x :=
  induction_linear x (by simp) (fun _ _ h h' => by nth_rw 2 [← h, ← h']; simp) <| by
    intro _ r
    rw [← mul_one r, ← MonoidAlgebra.smul_single', map_smul]
    simp [toHeckeCosetModuleMap_apply_mk, toHeckeCosetModuleInv_apply_single]

/-- tbd -/
noncomputable def toHeckeCosetModuleEquiv :
    HeckeBimodule k H₁ H₂ ≃ₗ[k] k[DoubleCoset₀ H₁ H₂] where
  toLinearMap := toHeckeCosetModuleMap k H₁ H₂
  invFun := toHeckeCosetModuleInv k H₁ H₂
  left_inv f := by
    apply toHeckeCosetModuleMap.injective
    exact toHeckeCosetModuleInv_isRightInv k H₁ H₂ ((toHeckeCosetModuleMap k H₁ H₂) f)
  right_inv := by
    exact toHeckeCosetModuleInv_isRightInv k H₁ H₂

@[simp]
lemma toHeckeCosetModuleEquiv_apply (x : DoubleCoset₀ H₁ H₂) :
    (toHeckeCosetModuleEquiv k H₁ H₂) (mk x) = single x 1 :=
  toHeckeCosetModuleMap_apply_mk k H₁ H₂ x

@[simp]
lemma toHeckeCosetModuleEquiv_symm_apply (x : DoubleCoset₀ H₁ H₂) :
    ((toHeckeCosetModuleEquiv k H₁ H₂).symm (single x 1)) = mk x :=
  toHeckeCosetModuleInv_apply_single k H₁ H₂ x

variable {k H₁ H₂}

/-- tbd -/
noncomputable def coeff :
    HeckeBimodule k H₁ H₂ →ₗ[k] (DoubleCoset₀ H₁ H₂ →₀ k) :=
  MonoidAlgebra.coeffLinearEquiv (S := k) (R := k) (M := DoubleCoset₀ H₁ H₂) ∘ₗ
    (toHeckeCosetModuleEquiv k H₁ H₂).toLinearMap

@[simp]
lemma coeff_apply (x y : DoubleCoset₀ H₁ H₂) [Decidable (x = y)] :
    (mk x).coeff y = if x = y then (1 : k) else 0 := by
  simp [coeff, Finsupp.single_apply]

lemma coeff_eq_coeff_apply_one (x : DoubleCoset₀ H₁ H₂) (f : HeckeBimodule k H₁ H₂) :
    f.coeff x = (f (cosetVector k (1 : G))).coeff x.rep := rfl

@[simp]
lemma coeff_finsuppSum_of_Nat (f : DoubleCoset₀ H₁ H₂ →₀ ℕ) (x : DoubleCoset₀ H₁ H₂) :
    coeff (f.sum fun y c => c • mk y) x (k := k) = f x := by classical
  simpa [map_finsuppSum] using fun h => by simp [h]

lemma ext_coeff (x y : HeckeBimodule k H₁ H₂) (hxy : ∀ z, x.coeff z = y.coeff z) :
    x = y := by classical
  apply (toHeckeCosetModuleEquiv k H₁ H₂).injective
  ext z
  exact hxy z

lemma induction_on (f : HeckeBimodule k H₁ H₂) {p : HeckeBimodule k H₁ H₂ → Prop}
    (zero : p 0)
    (mk' : ∀ (g : DoubleCoset₀ H₁ H₂), p (mk g))
    (smul : ∀ (r : k) (x : HeckeBimodule k H₁ H₂), p x → p (r • x))
    (add : ∀ x y, p x → p y → p (x + y)) : p f := by
  let E := toHeckeCosetModuleEquiv k H₁ H₂
  rw [← E.symm_apply_apply f]
  refine MonoidAlgebra.induction_linear (E f) ?_ ?_ ?_
  · simp [zero]
  · intro x y hx hy
    simpa using add (E.symm x) (E.symm y) hx hy
  · intro g r
    rw [← mul_one r, ← MonoidAlgebra.smul_single', map_smul]
    simpa [E] using smul r (mk g) (mk' g)

section Action

variable {ρ : Representation k G V}

/-- tbd -/
noncomputable def Action : HeckeBimodule k H₁ H₂ →ₗ[k] HeckeModule H₂ ρ →ₗ[k] HeckeModule H₁ ρ :=
  (IntertwiningMap.llcomp (ofMulAction k G (G ⧸ H₁)) (ofMulAction k G (G ⧸ H₂)) ρ).flip

lemma Action_eq_comp (x : HeckeBimodule k H₁ H₂) (v : HeckeModule H₂ ρ) :
    Action x v = v.comp x := by
  rw [Action, LinearMap.flip_apply, IntertwiningMap.comp_def]

lemma Action_assoc (x : HeckeBimodule k H₁ H₂) (y : HeckeBimodule k H₂ H₃)
    (v : HeckeModule H₃ ρ) :
    Action (Action x y) v = Action x (Action y v) := by
  ext
  simp [Action_eq_comp]

lemma Action_diag_mul_eq (x y : HeckeBimodule k H H) :
    Action (y * x) (k := k) (ρ := ρ) = (Action x) * (Action y) := by
  rw [Action]
  rfl

lemma Action_mk_apply (x : DoubleCoset₀ H₁ H₂) (v : HeckeModule H₂ ρ) :
    Action (mk x) v (cosetVector k (1 : G)) =
      ∑ (i : LeftDecompQuotient H₁ H₂ x.rep), ρ (i.out * x.rep) (v (cosetVector k (1 : H₂))) := by
  simp [Action_eq_comp, HeckeBimodule.mk_apply, doubleCosetVector_eq_sum_rep,
    ← IntertwiningMap.isIntertwining]

theorem Action_mk_mk (x : DoubleCoset₀ H₁ H₂) (y : DoubleCoset₀ H₂ H₃) :
    Action (mk x) (mk y) = (x.multiplicity y).sum fun w n => n • mk w
    (k := k) := by classical
  apply ext_coeff
  intro z
  rw [coeff_eq_coeff_apply_one]
  simp only [coeff_finsuppSum_of_Nat, DoubleCoset₀.multiplicity_apply, mul_assoc,
    Nat.card_eq_fintype_card, Fintype.card_ofFinset, Set.mem_ofPred_eq]
  simp only [Action_mk_apply, map_mul, OneMemClass.coe_one, mk_apply, doubleCosetVector_eq_sum_rep,
        map_sum, Module.End.mul_apply, ofMulAction_single, MulAction.Quotient.smul_mk, smul_eq_mul,
        ← Fintype.sum_prod_type', coeff_sum, coeff_single, Finsupp.coe_finsetSum, Finset.sum_apply]
  simp [Finsupp.single_apply]

end Action

end HeckeBimodule

end Bimodule

section Algebra

variable (k H) in
abbrev HeckeAlgebra := MulOpposite (HeckeBimodule k H H)

variable (f : HeckeAlgebra k H) (ρ : Representation k G V) (σ : Representation k G W)

instance instPrecompSMul (σ : Representation k G W) :
    SMul (MulOpposite (IntertwiningMap σ σ)) (IntertwiningMap σ ρ) where
  smul f g := g.comp f.unop

lemma IntertWiningMap.smul_eq_precomp (f : MulOpposite (IntertwiningMap σ σ))
    (g : IntertwiningMap σ ρ) :
    f • g = g.comp f.unop := rfl

instance instPrecompModule (σ : Representation k G W) :
    Module (MulOpposite (IntertwiningMap σ σ)) (IntertwiningMap σ ρ) :=
  fast_instance%
  { one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_zero _ := by ext; simp [IntertWiningMap.smul_eq_precomp]
    smul_add f x y := IntertwiningMap.comp_add _ _ _ x y f.unop
    add_smul x y f := IntertwiningMap.add_comp _ _ _ f x.unop y.unop
    zero_smul _ := by ext; simp [IntertWiningMap.smul_eq_precomp]}

namespace HeckeAlgebra

/-- tbd -/
noncomputable def mk (x : DoubleCoset₀ H H) :
    HeckeAlgebra k H := MulOpposite.opLinearEquiv k (HeckeBimodule.mk x)

lemma mk_def (x : DoubleCoset₀ H H) :
    mk x (k := k) = MulOpposite.op (HeckeBimodule.mk x) := rfl

lemma mk_one :
    mk (DoubleCoset₀.mk H H 1) (k := k) = 1 := by
  simp only [mk, MulOpposite.coe_opLinearEquiv, MulOpposite.op_eq_one_iff]
  ext
  have : Fintype.card (LeftDecompQuotient H H (DoubleCoset₀.mk H H 1).rep) = 1 := by
    rw [Fintype.card_eq_nat_card, ← DoubleCoset₀.mk_degree, DoubleCoset₀.mk_rep]
    simp
  simp [doubleCosetVector_eq_sum_rep, this]

lemma smul_eq_comp (v : HeckeModule H ρ) :
    f • v = v.comp f.unop := rfl

lemma smul_eq_mul (g : HeckeAlgebra k H) :
    f • g = f * g := rfl

lemma mul_eq_Action (g : HeckeAlgebra k H) :
    f * g = MulOpposite.op (HeckeBimodule.Action f.unop g.unop) := rfl

lemma mk_mul_mk (x y : DoubleCoset₀ H H) :
    mk x * mk y (k := k) = (x.multiplicity y).sum fun w n => n • mk w := by
  simp only [mul_eq_Action, mk, ← Nat.cast_smul_eq_nsmul k,
    ← (MulOpposite.opLinearEquiv k).map_smul, ← map_finsuppSum]
  simp [HeckeBimodule.Action_mk_mk, Nat.cast_smul_eq_nsmul k]

variable (k H) in
/-- tbd -/
@[simps! symm_apply]
noncomputable def toHeckeCosetModuleEquiv :
    HeckeAlgebra k H ≃ₗ[k] k[DoubleCoset₀ H H] :=
  (MulOpposite.opLinearEquiv k).symm.trans (HeckeBimodule.toHeckeCosetModuleEquiv k H H)

@[simp]
lemma toHeckeCosetModuleEquiv_apply (x : DoubleCoset₀ H H) :
    toHeckeCosetModuleEquiv k H (mk x) = single x (1 : k) := by
  apply (toHeckeCosetModuleEquiv k H).symm.injective
  simp [mk_def]

/-- tbd -/
noncomputable def coeff :
    HeckeAlgebra k H →ₗ[k] (DoubleCoset₀ H H →₀ k) :=
  MonoidAlgebra.coeffLinearEquiv k (S := k) (M := DoubleCoset₀ H H) ∘ₗ
    (toHeckeCosetModuleEquiv k H).toLinearMap

@[simp]
lemma coeff_apply (x y : DoubleCoset₀ H H) [Decidable (x = y)] :
    (mk x).coeff y = if x = y then (1 : k) else 0 := by
  simp [coeff, toHeckeCosetModuleEquiv_apply, Finsupp.single_apply]

@[ext]
lemma ext (f g : HeckeAlgebra k H) (h : ∀ x, f.coeff x = g.coeff x) :
    f = g := by
  apply (toHeckeCosetModuleEquiv k H).injective
  ext x
  exact h x

lemma induction_on {p : HeckeAlgebra k H → Prop}
    (mk' : ∀ x : DoubleCoset₀ H H, p (mk x))
    (smul : ∀ (r : k) x , p x → p (r • x))
    (add : ∀ x y, p x → p y → p (x + y)) :
    p f := by
  rw [← MulOpposite.op_unop f]
  refine HeckeBimodule.induction_on f.unop (p := fun x => p (MulOpposite.op x)) ?_ ?_ ?_ ?_
  · simpa using smul 0 (mk (DoubleCoset₀.mk H H 1)) (mk' (DoubleCoset₀.mk H H 1))
  · exact fun x => by simpa [mk_def] using mk' x
  · exact fun r x hx => by simpa using smul r (MulOpposite.op x) hx
  · exact fun x y hx hy => by simpa using add (MulOpposite.op x) (MulOpposite.op y) hx hy

end HeckeAlgebra

end Algebra

end Representation
