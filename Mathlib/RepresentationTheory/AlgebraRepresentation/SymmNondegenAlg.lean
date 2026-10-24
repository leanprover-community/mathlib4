/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Symmetric Nondegenerate Algebras and Trace Representatives

This file introduces symmetric nondegenerate algebras and construct central idempotents from those
representations with representable trace.

Given a `k`-algebra `A` and a linear functional `Φ : A →ₗ[k] k`, we say that `(A, Φ)` is symmetric
(resp. nondegenerate) if the bilinear `⟨x, y⟩ := Φ (x * y)` is symmetric (resp. nondegenerate). For
example, `A = k[G]` with `Φ` being taking coefficient at `1` is a symmetric nondegenerate algebra.
When `k` is a field and `A` is finite dimensional over `k`, this notion is the same as (symmetric)
Frobenius algebras. A more intricate exmaple is the Hecke algebra `A = End_G(ℂ[G ⧸ H])ᵒᵖ` with `Φ`
being taking coefficient at `1`. The `ℂ`-Hecke algebra is always nondegenerate. It is symmetric if
and only if `H` is unimodular, i.e. `[HgH : H] = [Hg⁻¹H : H]` for all `g : G`.

The symmetric nondegenerate structure gives an injective map from the center `Z(A)` to the space of
functionals `A ⧸ [A, A] →ₗ[k] k` vanishing on commutators. In practice, it could be very difficult
to describe `Z(A)` explicitly, e.g. when `A` is the Hecke algebra of a `p`-adic reductive group with
integer coefficients. On the other hands, the space `A ⧸ [A, A] →ₗ[k] k` is always abundant (and
stricly larger when `Z(A)` is infinite dimensional), since the trace of any `k`-finite-projective
`A`-module will provide such a functional. In this file we study those elements of `A` coming from
the trace functionals.

We say that `f : A` is the trace representative of a `k`-linear `A`-module `V` if `∀ x : A` we have
`⟨f, x⟩ = Trace_V(x)`.
1) We prove that such an `f` is always central.
2) Assume further that `V` is simple, we prove that `f W = 0` for any `k`-linear simple `A`-module
`W` distinct from `V`, using Jacobson's density theorem and Wedderburn-Artin theorem.
3) If we assume furthermore `f ^ 2 ≠ 0` and `k` is algebraically closed, we prove that there exists
some scalar `r : k` such that `r • f` is idempotent satisfying `(r • f : Endₖ(V))= 1` using
nondegeneracy and Schur's lemma. In other words, `r • f` is a central idempotent element isolating
the `V`-isotypic component.

A toy model is `A = ℂ[G]` for a finite group `G` where all central idempotents can be obtained
this way and the condition `f ^ 2 ≠ 0` is unnecessary. We warn the reader that the condition
`f ^ 2 ≠ 0` is genuinely unavoidable for general symmetric nondegenerate algebras. For example, if
we take `A = 𝔽₂[ℤ/2ℤ] ≃ 𝔽₂[x]/(x²)`, then the trace of the trivial representation will produce
a nilpotent central element `x`.

Finally we remark that we do not have a general criterion for which representation the trace is
representatble. It could happen that none of the nontrivial trace functionals is representable,
e.g. `A = ℂ[ℤ] ≃ ℂ[T, T⁻¹]`. This is exactly the case for the Hecke algebra of a `p`-adic reductive
group with non-compact center, while in that case there is bridge call "unramified twist" connecting
its representation theory to a subgroup with compact center where the trace of any compact
representation is representable. Thus materials from this file are still fundamental for the
smooth representation theory of `p`-adic reductive groups with non-compact center.

TODO: investigate those interesting functionals not coming from the trace.

## Main definitions

* `IsSymmNondegenAlg`: `(A, Φ)` is symmetric nondegenerate if the bilinear form
  `⟨x, y⟩ := Φ (x * y)` is symmetric nondegenerate.
* `IsSymmNondegenAlg.IsTraceRepresentative`: `f : A` is the trace representative of a `k`-linear
  `A`-module `V` if `⟨f, x⟩ = Trace ((x : Endₖ(V)))`.

## Main results

* `IsSymmNondegenAlg.mul_comm_of_isTraceRepresentative`: Any trace representative is central.
* `IsTraceRepresentative.lsmul_eq_zero_of_isEmpty`: If `V` is simple and its trace is represented by
  `f : A`, then `(f : Endₖ(W)) = 0` for any simple `A`-module `W` distinct from `V`.
* `IsSymmNondegenAlg.IsTraceRepresentative.ne_zero_of_isSimpleModule`: The trace representative of
  a simple `A`-module `V` is non-zero.
* `IsSymmNondegenAlg.IsTraceRepresentative.normalization_isIdempotentElem` : The normalization of
  the trace representative of a simple `A`-module `V` is an idempotnet element.
* `IsSymmNondegenAlg.IsTraceRepresentative.lsmul_normalization_eq_one`: The idempotent element
  `normalization Φ f a` isolate the simple module `V`.

-/

public section

/-- `(A, Φ)` is symmetric nondegenerate if the bilinear form `⟨x, y⟩ := Φ (x * y)` is symmetric
nondegenerate. -/
class IsSymmNondegenAlg {k : Type*} (A : Type*) [CommSemiring k] [NonUnitalNonAssocSemiring A]
    [Module k A] [SMulCommClass k A A] [IsScalarTower k A A] (Φ : A →ₗ[k] k) where
  isSymm : ∀ a b : A, Φ (a * b) = Φ (b * a)
  separatingLeft : ∀ a : A, (∀ b : A, Φ (a * b) = 0) → a = 0
  separatingRight : ∀ a : A, (∀ b : A, Φ (b * a) = 0) → a = 0 :=
    fun a ha => separatingLeft a (fun b => by rw [isSymm a b, ha])

section CommRing

variable {k A V W : Type*} [CommRing k] [Ring A] [Algebra k A] {Φ : A →ₗ[k] k}
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

variable (Φ V) in
/-- `f : A` is the trace representative of a `k`-linear `A`-module `V` if
  `∀ a, ⟨f, a⟩ = Trace_V(a)`. -/
def IsTraceRepresentative (f : A) : Prop :=
  ∀ a, Φ (f * a) = LinearMap.trace k V (Algebra.lsmul k k V a)

lemma isTraceRepresentative_iff {f : A} :
    IsTraceRepresentative V Φ f ↔ ∀ a, Φ (f * a) = LinearMap.trace k V (Algebra.lsmul k k V a) := by
  rfl

lemma IsTraceRepresentative.ne_zero_of_charZero [CharZero k] [Nontrivial V] [Module.Finite k V]
    [Module.Free k V] {f : A} (hf : IsTraceRepresentative V Φ f) :
    Φ f ≠ 0 := by
  by_contra
  rw [← mul_one f, hf 1] at this
  simp_all [Module.finrank_eq_zero_iff_of_free, ← not_nontrivial_iff_subsingleton]

variable [IsSymmNondegenAlg A Φ]

variable (Φ) in
lemma IsSymmNondegenAlg.eq_iff {a b : A} :
    a = b ↔ (∀ c, Φ (a * c) = Φ (b * c)) := by
  apply Iff.intro
  · exact fun h _ => by rw [h]
  rw [← sub_eq_zero]
  exact fun h => separatingLeft (a - b) (Φ := Φ) fun c => by simp [sub_mul, h]

lemma IsTraceRepresentative.unique {f g : A} (hf : IsTraceRepresentative V Φ f)
    (hg : IsTraceRepresentative V Φ g) :
    f = g :=
  (IsSymmNondegenAlg.eq_iff Φ).mpr <| fun c => by rw [hf c, hg c]

lemma IsTraceRepresentative.mul_comm' {f : A} (hf : IsTraceRepresentative V Φ f) :
    ∀ a, f * a = a * f :=
  fun a => (IsSymmNondegenAlg.eq_iff Φ).mpr <| fun c => by
    simp_rw [mul_assoc a f c, IsSymmNondegenAlg.isSymm a, mul_assoc f, hf _, map_mul,
      LinearMap.trace_mul_comm]

theorem IsTraceRepresentative.smul_eq_zero_of_isEmpty [IsSimpleModule A V] [IsSimpleModule A W]
    [IsEmpty (V ≃ₗ[A] W)] [Module.Finite (Module.End A V) V] {f : A}
    (hf : IsTraceRepresentative V Φ f) (w : W) :
    f • w = 0 := by
  let EndAV := Module.End A V
  let toEndAV := (Module.toModuleEnd EndAV (S := A) V)
  let I := RingHom.ker toEndAV
  have hmul_ker {a : A} (ha : a ∈ I) : f * a = 0 := by
    refine (IsSymmNondegenAlg.eq_iff Φ).mpr fun c => ?_
    simp only [RingHom.mem_ker, Module.toModuleEnd_apply, I, toEndAV] at ha
    have : DistribSMul.toLinearMap EndAV V a = Algebra.lsmul k k V a := rfl
    rw [mul_assoc, hf (a * c), map_mul, ← this, ha]
    simp
  by_cases hW : I • ⊤ = (0 : Submodule A W)
  · -- The idea is that `A ⧸ I` is isomorphic to `End_{End_A(V)}(V)` by Jacoboson's density theorem
    -- and that `End_{End_A(V)}(V)` is a simple Artinian ring forcing `W` to be isomorphic to `V`.
    let EAux : A ⧸ I →+* Module.End EndAV V := RingHom.kerLift toEndAV
    have : Nontrivial V := IsSimpleModule.nontrivial A V
    have : Function.Bijective EAux := by
      refine ⟨RingHom.kerLift_injective _, ?_⟩
      refine Function.Surjective.of_comp (g := Ideal.Quotient.mk I) ?_
      have : EAux ∘ (Ideal.Quotient.mk I) = Module.toModuleEnd EndAV V := rfl
      simp [this, EndAV, Module.Finite.toModuleEnd_moduleEnd_surjective]
    let E := (RingEquiv.ofBijective EAux this).symm.toRingHom
    have E_apply_lsmul (a : A) : E (toEndAV a) = a := by
      apply (RingEquiv.ofBijective EAux this).injective
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply, E]
      rfl
    have : RingHomSurjective E := ⟨(RingEquiv.ofBijective EAux this).symm.surjective⟩
    let F : A ⧸ I →+* Module.End k W := by
      refine Ideal.Quotient.lift I (Algebra.lsmul k k W).toRingHom (fun a ha => ?_)
      ext x
      have : a • x ∈ I • (⊤ : Submodule A W) := Submodule.smul_mem_smul ha Submodule.mem_top
      simpa [hW] using this
    -- We show that `W` is a simple `End_{End_A(V)}(V)`-module by pulling back `A ⧸ I`-simpleness
    -- along the surjective ring homomorphism `E : End_{End_A(V)}(V) →+* A ⧸ I`.
    let : Module (A ⧸ I) W := Module.compHom W F
    let : Module (Module.End EndAV V) W := Module.compHom W E
    let sl1 : W →ₛₗ[Ideal.Quotient.mk I] W :=
      { toFun w := w, map_add' _ _ := rfl, map_smul' a x := rfl }
    let sl2 : W →ₛₗ[E] W :=
      { toFun w := w, map_add' _ _ := rfl, map_smul' a x := rfl }
    have : IsSimpleModule (Module.End EndAV V) W :=
      (LinearMap.isSimpleModule_iff_of_bijective sl2 Function.bijective_id).mpr <|
        (LinearMap.isSimpleModule_iff_of_bijective sl1 Function.bijective_id).mp (by assumption)
    -- We show that `End_{End_A(V)}(V)` is isomorphic to `Matrix_{n,n}(D)` where `D = End_A(V)` is a
    -- division algebra and use that the matrix algebra over a division ring is simple Artinian.
    obtain ⟨n, _, m, _, ⟨e⟩⟩ := IsIsotypic.linearEquiv_fun (IsSimpleRing.isIsotypic EndAV V)
    let eMat := e.conjRingEquiv.trans (endVecRingEquivMatrixEnd (Fin n) EndAV m)
    have : IsSimpleRing (Module.End EndAV V) := IsSimpleRing.of_ringEquiv eMat.symm (inferInstance)
    have : IsArtinianRing (Module.End EndAV V) := eMat.symm.isArtinianRing
    -- Any two simple modules over a simple Artinian ring are isomorphic.
    obtain ⟨f⟩ := IsSimpleRing.nonempty_linearEquiv_of_isSimpleModule (Module.End EndAV V) V W
    let iso : V ≃ₗ[A] W :=
      { toFun := f, invFun := f.symm, left_inv _ := by simp, right_inv _ := by simp,
        map_add' := by simp,
        map_smul' a v := by
          have hsmul (a : A) (w : W) : toEndAV a • w = a • w := by
            rw [show toEndAV a • w = F (E (toEndAV a)) • w by rfl, E_apply_lsmul]
            rfl
          rw [show f (a • v) = f (toEndAV a • v) by rfl, map_smul, hsmul, RingHom.id_apply] }
    exact False.elim (IsEmpty.false iso)
  have : w ∈ I • (⊤ : Submodule A W) := by simp [(IsSimpleOrder.eq_bot_or_eq_top _).resolve_left hW]
  refine Submodule.smul_induction_on this (fun a ha x _ => ?_) fun _ _ h1 h2 => ?_
  · simp_rw [← smul_assoc, smul_eq_mul, hmul_ker ha, zero_smul]
  simp_rw [smul_add, h1, h2, zero_add]

end CommRing

section Field

variable {k A V W : Type*} [Field k] [Ring A] [Algebra k A] {Φ : A →ₗ[k] k}
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

namespace IsTraceRepresentative

set_option linter.unusedVariables false
/-- A scalar multiple of `f` which becomes idempotent if `f` is the trace representative of some
simple `A`-module over an algebraically closed field `k`. -/
def normalization {f : A} (hf : IsTraceRepresentative V Φ f) (a : A) :
    A := (Φ (f * (f * a)))⁻¹ • Φ (f * a) • f

lemma normalization_def {a f : A} (hf : IsTraceRepresentative V Φ f) :
    hf.normalization a = (Φ (f * (f * a)))⁻¹ • Φ (f * a) • f := by
  rw [normalization]

variable [Module.Finite k V]

lemma ne_zero_of_isAlgClosed [IsSimpleModule A V] [IsAlgClosed k] {f : A}
    (hf : IsTraceRepresentative V Φ f) :
    f ≠ 0 := by
  let : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one k hv
  obtain ⟨a, ha⟩ := IsSimpleModule.lsmul_surjective_of_isAlgClosed A k (g.smulRight v)
  by_contra
  simpa [this, ha, hg] using hf a

omit [Module.Finite k V] in
private lemma normalization_eq_smul_and_ne_zero {f a : A} (hf : IsTraceRepresentative V Φ f)
    {r : k} (ha : Φ (f * (f * a)) ≠ 0) (hr : ∀ v : V, f • v = r • v) :
    hf.normalization a = r⁻¹ • f ∧ r ≠ 0 := by
  let r' : k := (Φ (f * (f * a)))⁻¹ • Φ (f * a)
  have hr : Algebra.lsmul k k V f = r • 1 := by ext x; simp [hr]
  have hr_ne_zero : r ≠ 0 := by
    by_contra
    apply ha
    simp [isTraceRepresentative_iff.mp hf, hr, this]
  have hr' : r' = r⁻¹ := by
    simp_rw [r', smul_eq_mul, inv_mul_eq_iff_eq_mul₀ ha, mul_comm _ r⁻¹]
    simp [isTraceRepresentative_iff.mp hf, hr, hr_ne_zero]
  exact ⟨by simp [r', normalization_def, mul_smul, ← hr'], hr_ne_zero⟩

variable [IsSymmNondegenAlg A Φ] [IsSimpleModule A V] [IsAlgClosed k]

lemma normalization_isIdempotentElem {f : A} (hf : IsTraceRepresentative V Φ f) (a : A) :
    hf.normalization a ^ 2 = hf.normalization a := by
  by_cases ha : Φ (f * (f * a)) = 0
  · simp [normalization, ha]
  obtain ⟨r, hr⟩ :=
    IsSimpleModule.smul_eq_smul_of_mul_comm V k hf.mul_comm'
  refine (IsSymmNondegenAlg.eq_iff Φ).mpr fun c => ?_
  obtain ⟨heq, hr_ne_zero⟩ := normalization_eq_smul_and_ne_zero hf ha hr
  have hr : Algebra.lsmul k k V f = r • 1 := by ext x; simp [hr]
  simp [heq, pow_two, mul_assoc, isTraceRepresentative_iff.mp hf, hr, hr_ne_zero]

lemma normalization_smul {f a : A} (hf : IsTraceRepresentative V Φ f)
    (ha : Φ (f * (f * a)) ≠ 0) (v : V) :
    (hf.normalization a) • v = v := by
  obtain ⟨r, hr⟩ := IsSimpleModule.smul_eq_smul_of_mul_comm V k hf.mul_comm'
  obtain ⟨heq, hr_ne_zero⟩ := normalization_eq_smul_and_ne_zero hf ha hr
  rw [heq, smul_assoc, hr v, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hr_ne_zero, one_smul]

lemma normalization_eq_normalization_of_ne_zero {a b f : A} (hf : IsTraceRepresentative V Φ f)
    (ha : (Φ (f * (f * a))) ≠ 0) (hb : (Φ (f * (f * b))) ≠ 0) :
    hf.normalization a = hf.normalization b := by
  obtain ⟨r, hr⟩ := IsSimpleModule.smul_eq_smul_of_mul_comm V k hf.mul_comm'
  exact (normalization_eq_smul_and_ne_zero hf ha hr).left.trans
    (normalization_eq_smul_and_ne_zero hf hb hr).left.symm

lemma normalization_smul_of_charZero [CharZero k] {f : A} (hf : IsTraceRepresentative V Φ f)
    (hff : f * f ≠ 0) (v : V) :
    hf.normalization 1 • v = v := by
  refine normalization_smul hf ?_ v
  obtain ⟨c, hc⟩ := IsSimpleModule.smul_eq_smul_of_mul_comm V k hf.mul_comm'
  have hc : Algebra.lsmul k k V f = c • 1 := by ext x; simp [hc]
  have : c ≠ 0 := by
    by_contra
    refine hff <| (IsSymmNondegenAlg.eq_iff Φ).mpr fun x => ?_
    simp [mul_assoc, isTraceRepresentative_iff.mp hf, hc, this]
  simp [isTraceRepresentative_iff.mp hf, hc, this, Module.finrank_eq_zero_iff_of_free,
    ← not_nontrivial_iff_subsingleton, IsSimpleModule.nontrivial A V]

omit [IsAlgClosed k] [Module.Finite k V] in
theorem normalization_smul_eq_zero_of_isEmpty [IsSimpleModule A W] [IsEmpty (V ≃ₗ[A] W)]
    [Module.Finite (Module.End A V) V] {f : A} (hf : IsTraceRepresentative V Φ f) (a : A) (w : W) :
    hf.normalization a • w = 0 := by
  simp [normalization_def, smul_eq_zero_of_isEmpty hf]

omit [Module k W] [IsScalarTower k A W]

theorem normalization_smul_of_nonempty [Nonempty (V ≃ₗ[A] W)] {f a : A}
    (hf : IsTraceRepresentative V Φ f) (ha : Φ (f * (f * a)) ≠ 0) (w : W) :
    hf.normalization a • w = w := by
  obtain ⟨e⟩ := ‹Nonempty (V ≃ₗ[A] W)›
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [← e.map_smul, normalization_smul hf ha v]

lemma normalization_smul_of_nonempty_charZero [CharZero k] [Nonempty (V ≃ₗ[A] W)] {f : A}
    (hf : IsTraceRepresentative V Φ f) (hff : f * f ≠ 0) (w : W) :
    hf.normalization 1 • w = w := by
  obtain ⟨e⟩ := ‹Nonempty (V ≃ₗ[A] W)›
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [← e.map_smul, normalization_smul_of_charZero hf hff v]

end IsTraceRepresentative

end Field
