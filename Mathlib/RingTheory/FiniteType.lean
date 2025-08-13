/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.Adjoin.Polynomial
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `Algebra.FiniteType`, `RingHom.FiniteType`, `AlgHom.FiniteType`
  all of these express that some object is finitely generated *as algebra* over some base ring.

-/

open Function (Surjective)

open Polynomial

section ModuleAndAlgebra

universe uR uS uA uB uM uN
variable (R : Type uR) (S : Type uS) (A : Type uA) (B : Type uB) (M : Type uM) (N : Type uN)

/-- An algebra over a commutative semiring is of `FiniteType` if it is finitely generated
over the base ring as algebra. -/
class Algebra.FiniteType [CommSemiring R] [Semiring A] [Algebra R A] : Prop where
  out : (⊤ : Subalgebra R A).FG

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Finite

open Submodule Set

variable {R S M N}

section Algebra

-- see Note [lower instance priority]
instance (priority := 100) finiteType {R : Type*} (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [hRA : Module.Finite R A] : Algebra.FiniteType R A :=
  ⟨Subalgebra.fg_of_submodule_fg hRA.1⟩

end Algebra

end Finite

end Module

namespace Algebra

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

namespace FiniteType

@[deprecated inferInstance (since := "2025-07-12")]
theorem self : FiniteType R R := inferInstance

theorem of_restrictScalars_finiteType [Algebra S A] [IsScalarTower R S A] [hA : FiniteType R A] :
    FiniteType S A := by
  obtain ⟨s, hS⟩ := hA.out
  refine ⟨⟨s, eq_top_iff.2 fun b => ?_⟩⟩
  have le : adjoin R (s : Set A) ≤ Subalgebra.restrictScalars R (adjoin S s) := by
    apply (Algebra.adjoin_le _ : adjoin R (s : Set A) ≤ Subalgebra.restrictScalars R (adjoin S ↑s))
    simp only [Subalgebra.coe_restrictScalars]
    exact Algebra.subset_adjoin
  exact le (eq_top_iff.1 hS b)

variable {R S A B}

theorem of_surjective [FiniteType R A] (f : A →ₐ[R] B) (hf : Surjective f) : FiniteType R B :=
  ⟨by
    convert ‹FiniteType R A›.1.map f
    simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, AlgHom.mem_range] using hf⟩

theorem equiv (hRA : FiniteType R A) (e : A ≃ₐ[R] B) : FiniteType R B :=
  hRA.of_surjective e e.surjective

theorem trans [Algebra S A] [IsScalarTower R S A] (hRS : FiniteType R S) (hSA : FiniteType S A) :
    FiniteType R A :=
  ⟨fg_trans' hRS.1 hSA.1⟩

instance quotient (R : Type*) {S : Type*} [CommSemiring R] [CommRing S] [Algebra R S] (I : Ideal S)
    [h : Algebra.FiniteType R S] : Algebra.FiniteType R (S ⧸ I) :=
  Algebra.FiniteType.trans h inferInstance

instance [FiniteType R S] : FiniteType R S[X] := by
  refine .trans ‹_› ⟨{Polynomial.X}, ?_⟩
  rw [Finset.coe_singleton]
  exact Polynomial.adjoin_X

@[deprecated inferInstance (since := "2025-07-12")]
protected theorem polynomial : FiniteType R R[X] := inferInstance

instance {ι : Type*} [Finite ι] [FiniteType R S] : FiniteType R (MvPolynomial ι S) := by
  classical
  cases nonempty_fintype ι
  refine .trans ‹_› ⟨Finset.univ.image MvPolynomial.X, ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact MvPolynomial.adjoin_range_X

@[deprecated inferInstance (since := "2025-07-12")]
protected theorem mvPolynomial (ι : Type*) [Finite ι] : FiniteType R (MvPolynomial ι R) :=
  inferInstance

instance {ι : Type*} [Finite ι] [FiniteType R S] : FiniteType R (FreeAlgebra S ι) := by
  classical
  cases nonempty_fintype ι
  refine .trans ‹_› ⟨Finset.univ.image (FreeAlgebra.ι _), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact FreeAlgebra.adjoin_range_ι ..

@[deprecated inferInstance (since := "2025-07-12")]
protected theorem freeAlgebra (ι : Type*) [Finite ι] : FiniteType R (FreeAlgebra R ι) :=
  inferInstance

/-- An algebra is finitely generated if and only if it is a quotient
of a free algebra whose variables are indexed by a finset. -/
theorem iff_quotient_freeAlgebra :
    FiniteType R A ↔
      ∃ (s : Finset A) (f : FreeAlgebra R s →ₐ[R] A), Surjective f := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, FreeAlgebra.lift _ (↑), ?_⟩
    rw [← Set.range_eq_univ, ← AlgHom.coe_range, ← adjoin_range_eq_range_freeAlgebra_lift,
      Subtype.range_coe_subtype, Finset.setOf_mem, hs, coe_top]
  · rintro ⟨s, f, hsur⟩
    exact .of_surjective f hsur

/-- A commutative algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a finset. -/
theorem iff_quotient_mvPolynomial :
    FiniteType R S ↔
      ∃ (s : Finset S) (f : MvPolynomial { x // x ∈ s } R →ₐ[R] S), Surjective f := by
  constructor
  · rintro ⟨s, hs⟩
    use s, MvPolynomial.aeval (↑)
    intro x
    have hrw : (↑s : Set S) = fun x : S => x ∈ s.val := rfl
    rw [← Set.mem_range, ← AlgHom.coe_range, ← adjoin_eq_range]
    simp_rw [← hrw, hs]
    exact Set.mem_univ x
  · rintro ⟨s, f, hsur⟩
    exact .of_surjective f hsur

/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype. -/
theorem iff_quotient_freeAlgebra' : FiniteType R A ↔
    ∃ (ι : Type uA) (_ : Fintype ι) (f : FreeAlgebra R ι →ₐ[R] A), Surjective f := by
  constructor
  · rw [iff_quotient_freeAlgebra]
    rintro ⟨s, f, hsur⟩
    use { x : A // x ∈ s }, inferInstance, f
  · rintro ⟨ι, hfintype, f, hsur⟩
    letI : Fintype ι := hfintype
    exact .of_surjective f hsur

/-- A commutative algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype. -/
theorem iff_quotient_mvPolynomial' : FiniteType R S ↔
    ∃ (ι : Type uS) (_ : Fintype ι) (f : MvPolynomial ι R →ₐ[R] S), Surjective f := by
  constructor
  · rw [iff_quotient_mvPolynomial]
    rintro ⟨s, f, hsur⟩
    use { x : S // x ∈ s }, inferInstance, f
  · rintro ⟨ι, hfintype, f, hsur⟩
    letI : Fintype ι := hfintype
    exact .of_surjective f hsur

/-- A commutative algebra is finitely generated if and only if it is a quotient of a polynomial ring
in `n` variables. -/
theorem iff_quotient_mvPolynomial'' :
    FiniteType R S ↔ ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] S), Surjective f := by
  constructor
  · rw [iff_quotient_mvPolynomial']
    rintro ⟨ι, hfintype, f, hsur⟩
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    exact ⟨Fintype.card ι, AlgHom.comp f equiv.symm.toAlgHom, by simpa using hsur⟩
  · rintro ⟨n, f, hsur⟩
    exact .of_surjective f hsur

instance prod [hA : FiniteType R A] [hB : FiniteType R B] : FiniteType R (A × B) :=
  ⟨by rw [← Subalgebra.prod_top]; exact hA.1.prod hB.1⟩

theorem isNoetherianRing (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [h : Algebra.FiniteType R S] [IsNoetherianRing R] : IsNoetherianRing S := by
  obtain ⟨s, hs⟩ := h.1
  apply
    isNoetherianRing_of_surjective (MvPolynomial s R) S
      (MvPolynomial.aeval (↑) : MvPolynomial s R →ₐ[R] S).toRingHom
  rw [← Set.range_eq_univ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← AlgHom.coe_range,
    ← Algebra.adjoin_range_eq_range_aeval, Subtype.range_coe_subtype, Finset.setOf_mem, hs]
  rfl

theorem _root_.Subalgebra.fg_iff_finiteType (S : Subalgebra R A) : S.FG ↔ Algebra.FiniteType R S :=
  S.fg_top.symm.trans ⟨fun h => ⟨h⟩, fun h => h.out⟩

end FiniteType

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is of `FiniteType` if `B` is finitely generated as `A`-algebra. -/
@[algebraize]
def FiniteType (f : A →+* B) : Prop :=
  @Algebra.FiniteType A B _ _ f.toAlgebra

lemma finiteType_algebraMap [Algebra A B] :
    (algebraMap A B).FiniteType ↔ Algebra.FiniteType A B := by
  delta FiniteType
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

namespace Finite

theorem finiteType {f : A →+* B} (hf : f.Finite) : FiniteType f :=
  @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf

end Finite

namespace FiniteType

variable (A) in
theorem id : FiniteType (RingHom.id A) := by simp [FiniteType]; infer_instance

theorem comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.FiniteType) (hg : Surjective g) :
    (g.comp f).FiniteType := by
  algebraize_only [f, g.comp f]
  exact ‹Algebra.FiniteType _ _›.of_surjective
    { g with
      toFun := g
      commutes' := fun a => rfl }
    hg

theorem of_surjective (f : A →+* B) (hf : Surjective f) : f.FiniteType := by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.FiniteType) (hf : f.FiniteType) :
    (g.comp f).FiniteType := by
  algebraize_only [f, g, g.comp f]
  exact Algebra.FiniteType.trans hf hg

theorem of_finite {f : A →+* B} (hf : f.Finite) : f.FiniteType :=
  @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf

alias _root_.RingHom.Finite.to_finiteType := of_finite

theorem of_comp_finiteType {f : A →+* B} {g : B →+* C} (h : (g.comp f).FiniteType) :
    g.FiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.FiniteType.of_restrictScalars_finiteType A B C

end FiniteType

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommRing R]
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is of `FiniteType` if it is of finite type as ring morphism.
In other words, if `B` is finitely generated as `A`-algebra. -/
def FiniteType (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.FiniteType

namespace Finite

theorem finiteType {f : A →ₐ[R] B} (hf : f.Finite) : FiniteType f :=
  RingHom.Finite.finiteType hf

end Finite

namespace FiniteType

variable (R A)

theorem id : FiniteType (AlgHom.id R A) :=
  RingHom.FiniteType.id A

variable {R A}

theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.FiniteType) (hf : f.FiniteType) :
    (g.comp f).FiniteType :=
  RingHom.FiniteType.comp hg hf

theorem comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.FiniteType) (hg : Surjective g) :
    (g.comp f).FiniteType :=
  RingHom.FiniteType.comp_surjective hf hg

theorem of_surjective (f : A →ₐ[R] B) (hf : Surjective f) : f.FiniteType :=
  RingHom.FiniteType.of_surjective f.toRingHom hf

theorem of_comp_finiteType {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).FiniteType) :
    g.FiniteType :=
  RingHom.FiniteType.of_comp_finiteType h

end FiniteType

end AlgHom

@[deprecated (since := "2025-08-12")] alias algebraMap_finiteType_iff_algebra_finiteType :=
  RingHom.finiteType_algebraMap

section MonoidAlgebra

variable {R : Type*} {M : Type*}

namespace AddMonoidAlgebra

open Algebra AddSubmonoid Submodule

section Span

section Semiring

variable [CommSemiring R] [AddMonoid M]

/-- An element of `R[M]` is in the subalgebra generated by its support. -/
theorem mem_adjoin_support (f : R[M]) : f ∈ adjoin R (of' R M '' f.support) := by
  suffices span R (of' R M '' f.support) ≤
      Subalgebra.toSubmodule (adjoin R (of' R M '' f.support)) by
    exact this (mem_span_support f)
  rw [Submodule.span_le]
  exact subset_adjoin

/-- If a set `S` generates, as algebra, `R[M]`, then the set of supports of
elements of `S` generates `R[M]`. -/
theorem support_gen_of_gen {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (⋃ f ∈ S, of' R M '' (f.support : Set M)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hS, adjoin_le_iff]
  intro f hf
  have hincl :
    of' R M '' f.support ⊆ ⋃ (g : R[M]) (_ : g ∈ S), of' R M '' g.support := by
    intro s hs
    exact Set.mem_iUnion₂.2 ⟨f, ⟨hf, hs⟩⟩
  exact adjoin_mono hincl (mem_adjoin_support f)

/-- If a set `S` generates, as algebra, `R[M]`, then the image of the union of
the supports of elements of `S` generates `R[M]`. -/
theorem support_gen_of_gen' {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (of' R M '' ⋃ f ∈ S, (f.support : Set M)) = ⊤ := by
  suffices (of' R M '' ⋃ f ∈ S, (f.support : Set M)) = ⋃ f ∈ S, of' R M '' (f.support : Set M) by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_iUnion]

end Semiring

section Ring

variable [CommRing R] [AddMonoid M]

/-- If `R[M]` is of finite type, then there is a `G : Finset M` such that its
image generates, as algebra, `R[M]`. -/
theorem exists_finset_adjoin_eq_top [h : FiniteType R R[M]] :
    ∃ G : Finset M, Algebra.adjoin R (of' R M '' G) = ⊤ := by
  obtain ⟨S, hS⟩ := h
  letI : DecidableEq M := Classical.decEq M
  use Finset.biUnion S fun f => f.support
  have : (Finset.biUnion S fun f => f.support : Set M) = ⋃ f ∈ S, (f.support : Set M) := by
    simp only [Finset.set_biUnion_coe, Finset.coe_biUnion]
  rw [this]
  exact support_gen_of_gen' hS

/-- The image of an element `m : M` in `R[M]` belongs the submodule generated by
`S : Set M` if and only if `m ∈ S`. -/
theorem of'_mem_span [Nontrivial R] {m : M} {S : Set M} :
    of' R M m ∈ span R (of' R M '' S) ↔ m ∈ S := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span <| Set.mem_image_of_mem (of R M) h⟩
  unfold of' at h
  rw [← Finsupp.supported_eq_span_single, Finsupp.mem_supported,
    Finsupp.support_single_ne_zero _ (one_ne_zero' R)] at h
  simpa using h

/--
If the image of an element `m : M` in `R[M]` belongs the submodule generated by
the closure of some `S : Set M` then `m ∈ closure S`. -/
theorem mem_closure_of_mem_span_closure [Nontrivial R] {m : M} {S : Set M}
    (h : of' R M m ∈ span R (Submonoid.closure (of' R M '' S) : Set R[M])) :
    m ∈ closure S := by
  suffices Multiplicative.ofAdd m ∈ Submonoid.closure (Multiplicative.toAdd ⁻¹' S) by
    simpa [← toSubmonoid_closure]
  let S' := @Submonoid.closure (Multiplicative M) Multiplicative.mulOneClass S
  have h' : Submonoid.map (of R M) S' = Submonoid.closure ((fun x : M => (of R M) x) '' S) :=
    MonoidHom.map_mclosure _ _
  rw [Set.image_congr' (show ∀ x, of' R M x = of R M x from fun x => of'_eq_of x), ← h'] at h
  simpa using of'_mem_span.1 h

end Ring

end Span

/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`R[M]`. -/
theorem mvPolynomial_aeval_of_surjective_of_closure [AddCommMonoid M] [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (MvPolynomial.aeval fun s : S => of' R M ↑s : MvPolynomial S R → R[M]) := by
  intro f
  induction f using induction_on with
  | hM m =>
    have : m ∈ closure S := hS.symm ▸ mem_top _
    refine AddSubmonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨MvPolynomial.X ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single,
            one_mul]; rfl⟩
  | hadd f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | hsmul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

variable [AddMonoid M]

/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`R[M]`. -/
theorem freeAlgebra_lift_of_surjective_of_closure [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (FreeAlgebra.lift R fun s : S => of' R M ↑s : FreeAlgebra R S → R[M]) := by
  intro f
  induction f using induction_on with
  | hM m =>
    have : m ∈ closure S := hS.symm ▸ mem_top _
    refine AddSubmonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨FreeAlgebra.ι R ⟨m, hm⟩, FreeAlgebra.lift_ι_apply _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single,
            one_mul]; rfl⟩
  | hadd f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | hsmul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

variable (R M)

/-- If an additive monoid `M` is finitely generated then `R[M]` is of finite
type. -/
instance finiteType_of_fg [CommRing R] [h : AddMonoid.FG M] :
    FiniteType R R[M] := by
  obtain ⟨S, hS⟩ := h.fg_top
  exact .of_surjective
      (FreeAlgebra.lift R fun s : (S : Set M) => of' R M ↑s)
      (freeAlgebra_lift_of_surjective_of_closure hS)

variable {R M}

/-- An additive monoid `M` is finitely generated if and only if `R[M]` is of
finite type. -/
theorem finiteType_iff_fg [CommRing R] [Nontrivial R] :
    FiniteType R R[M] ↔ AddMonoid.FG M := by
  refine ⟨fun h => ?_, fun h => @AddMonoidAlgebra.finiteType_of_fg _ _ _ _ h⟩
  obtain ⟨S, hS⟩ := @exists_finset_adjoin_eq_top R M _ _ h
  refine AddMonoid.fg_def.2 ⟨S, (eq_top_iff' _).2 fun m => ?_⟩
  have hm : of' R M m ∈ Subalgebra.toSubmodule (adjoin R (of' R M '' ↑S)) := by
    simp only [hS, top_toSubmodule, Submodule.mem_top]
  rw [adjoin_eq_span] at hm
  exact mem_closure_of_mem_span_closure hm

/-- If `R[M]` is of finite type then `M` is finitely generated. -/
theorem fg_of_finiteType [CommRing R] [Nontrivial R] [h : FiniteType R R[M]] :
    AddMonoid.FG M :=
  finiteType_iff_fg.1 h

/-- An additive group `G` is finitely generated if and only if `R[G]` is of
finite type. -/
theorem finiteType_iff_group_fg {G : Type*} [AddGroup G] [CommRing R] [Nontrivial R] :
    FiniteType R R[G] ↔ AddGroup.FG G := by
  simpa [AddGroup.fg_iff_addMonoid_fg] using finiteType_iff_fg

end AddMonoidAlgebra

namespace MonoidAlgebra

open Algebra Submonoid Submodule

section Span

section Semiring

variable [CommSemiring R] [Monoid M]

/-- An element of `MonoidAlgebra R M` is in the subalgebra generated by its support. -/
theorem mem_adjoin_support (f : MonoidAlgebra R M) : f ∈ adjoin R (of R M '' f.support) := by
  suffices span R (of R M '' f.support) ≤ Subalgebra.toSubmodule (adjoin R (of R M '' f.support)) by
    exact this (mem_span_support f)
  rw [Submodule.span_le]
  exact subset_adjoin

/-- If a set `S` generates, as algebra, `MonoidAlgebra R M`, then the set of supports of elements
of `S` generates `MonoidAlgebra R M`. -/
theorem support_gen_of_gen {S : Set (MonoidAlgebra R M)} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (⋃ f ∈ S, of R M '' (f.support : Set M)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hS, adjoin_le_iff]
  intro f hf
  -- Porting note: ⋃ notation did not work here. Was
  -- ⋃ (g : MonoidAlgebra R M) (H : g ∈ S), (of R M '' g.support)
  have hincl : (of R M '' f.support) ⊆
      Set.iUnion fun (g : MonoidAlgebra R M)
        => Set.iUnion fun (_ : g ∈ S) => (of R M '' g.support) := by
    intro s hs
    exact Set.mem_iUnion₂.2 ⟨f, ⟨hf, hs⟩⟩
  exact adjoin_mono hincl (mem_adjoin_support f)

/-- If a set `S` generates, as algebra, `MonoidAlgebra R M`, then the image of the union of the
supports of elements of `S` generates `MonoidAlgebra R M`. -/
theorem support_gen_of_gen' {S : Set (MonoidAlgebra R M)} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (of R M '' ⋃ f ∈ S, (f.support : Set M)) = ⊤ := by
  suffices (of R M '' ⋃ f ∈ S, (f.support : Set M)) = ⋃ f ∈ S, of R M '' (f.support : Set M) by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_iUnion]

end Semiring

section Ring

variable [CommRing R] [Monoid M]

/-- If `MonoidAlgebra R M` is of finite type, then there is a `G : Finset M` such that its image
generates, as algebra, `MonoidAlgebra R M`. -/
theorem exists_finset_adjoin_eq_top [h : FiniteType R (MonoidAlgebra R M)] :
    ∃ G : Finset M, Algebra.adjoin R (of R M '' G) = ⊤ := by
  obtain ⟨S, hS⟩ := h
  letI : DecidableEq M := Classical.decEq M
  use Finset.biUnion S fun f => f.support
  have : (Finset.biUnion S fun f => f.support : Set M) = ⋃ f ∈ S, (f.support : Set M) := by
    simp only [Finset.set_biUnion_coe, Finset.coe_biUnion]
  rw [this]
  exact support_gen_of_gen' hS

/-- The image of an element `m : M` in `MonoidAlgebra R M` belongs the submodule generated by
`S : Set M` if and only if `m ∈ S`. -/
theorem of_mem_span_of_iff [Nontrivial R] {m : M} {S : Set M} :
    of R M m ∈ span R (of R M '' S) ↔ m ∈ S := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span <| Set.mem_image_of_mem (of R M) h⟩
  dsimp [of] at h
  rw [← Finsupp.supported_eq_span_single, Finsupp.mem_supported,
    Finsupp.support_single_ne_zero _ (one_ne_zero' R)] at h
  simpa using h

/--
If the image of an element `m : M` in `MonoidAlgebra R M` belongs the submodule generated by the
closure of some `S : Set M` then `m ∈ closure S`. -/
theorem mem_closure_of_mem_span_closure [Nontrivial R] {m : M} {S : Set M}
    (h : of R M m ∈ span R (Submonoid.closure (of R M '' S) : Set (MonoidAlgebra R M))) :
    m ∈ closure S := by
  rw [← MonoidHom.map_mclosure] at h
  simpa using of_mem_span_of_iff.1 h

end Ring

end Span

/-- If a set `S` generates a monoid `M`, then the image of `M` generates, as algebra,
`MonoidAlgebra R M`. -/
theorem mvPolynomial_aeval_of_surjective_of_closure [CommMonoid M] [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (MvPolynomial.aeval fun s : S => of R M ↑s : MvPolynomial S R → MonoidAlgebra R M) := by
  intro f
  induction f using induction_on with
  | hM m =>
    have : m ∈ closure S := hS.symm ▸ mem_top _
    refine Submonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨MvPolynomial.X ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single, one_mul]⟩
  | hadd f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩; rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | hsmul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩


variable [Monoid M]

/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`R[M]`. -/
theorem freeAlgebra_lift_of_surjective_of_closure [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (FreeAlgebra.lift R fun s : S => of R M ↑s : FreeAlgebra R S → MonoidAlgebra R M) := by
  intro f
  induction f using induction_on with
  | hM m =>
    have : m ∈ closure S := hS.symm ▸ mem_top _
    refine Submonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨FreeAlgebra.ι R ⟨m, hm⟩, FreeAlgebra.lift_ι_apply _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single, one_mul]⟩
  | hadd f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | hsmul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

/-- If a monoid `M` is finitely generated then `MonoidAlgebra R M` is of finite type. -/
instance finiteType_of_fg [CommRing R] [Monoid.FG M] : FiniteType R (MonoidAlgebra R M) :=
  (AddMonoidAlgebra.finiteType_of_fg R (Additive M)).equiv (toAdditiveAlgEquiv R M).symm

/-- A monoid `M` is finitely generated if and only if `MonoidAlgebra R M` is of finite type. -/
theorem finiteType_iff_fg [CommRing R] [Nontrivial R] :
    FiniteType R (MonoidAlgebra R M) ↔ Monoid.FG M :=
  ⟨fun h =>
    Monoid.fg_iff_add_fg.2 <|
      AddMonoidAlgebra.finiteType_iff_fg.1 <| h.equiv <| toAdditiveAlgEquiv R M,
    fun h => @MonoidAlgebra.finiteType_of_fg _ _ _ _ h⟩

/-- If `MonoidAlgebra R M` is of finite type then `M` is finitely generated. -/
theorem fg_of_finiteType [CommRing R] [Nontrivial R] [h : FiniteType R (MonoidAlgebra R M)] :
    Monoid.FG M :=
  finiteType_iff_fg.1 h

/-- A group `G` is finitely generated if and only if `R[G]` is of finite type. -/
theorem finiteType_iff_group_fg {G : Type*} [Group G] [CommRing R] [Nontrivial R] :
    FiniteType R (MonoidAlgebra R G) ↔ Group.FG G := by
  simpa [Group.fg_iff_monoid_fg] using finiteType_iff_fg

end MonoidAlgebra

end MonoidAlgebra

section Orzech

open Submodule Module Module.Finite in
/-- Any commutative ring `R` satisfies the `OrzechProperty`, that is, for any finitely generated
`R`-module `M`, any surjective homomorphism `f : N →ₗ[R] M` from a submodule `N` of `M` to `M`
is injective.

This is a consequence of Noetherian case
(`IsNoetherian.injective_of_surjective_of_injective`), which requires that `M` is a
Noetherian module, but allows `R` to be non-commutative. The reduction of this result to
Noetherian case is adapted from <https://math.stackexchange.com/a/1066110>:
suppose `{ m_j }` is a finite set of generator of `M`, for any `n : N` one can write
`i n = ∑ j, b_j * m_j` for `{ b_j }` in `R`, here `i : N →ₗ[R] M` is the standard inclusion.
We can choose `{ n_j }` which are preimages of `{ m_j }` under `f`, and can choose
`{ c_jl }` in `R` such that `i n_j = ∑ l, c_jl * m_l` for each `j`.
Now let `A` be the subring of `R` generated by `{ b_j }` and `{ c_jl }`, then it is
Noetherian. Let `N'` be the `A`-submodule of `N` generated by `n` and `{ n_j }`,
`M'` be the `A`-submodule of `M` generated by `{ m_j }`,
then it's easy to see that `i` and `f` restrict to `N' →ₗ[A] M'`,
and the restricted version of `f` is surjective, hence by Noetherian case,
it is also injective, in particular, if `f n = 0`, then `n = 0`.

See also Orzech's original paper: *Onto endomorphisms are isomorphisms* [orzech1971]. -/
instance (priority := 100) CommRing.orzechProperty
    (R : Type*) [CommRing R] : OrzechProperty R := by
  refine ⟨fun {M} _ _ _ {N} f hf ↦ ?_⟩
  letI := addCommMonoidToAddCommGroup R (M := M)
  letI := addCommMonoidToAddCommGroup R (M := N)
  let i := N.subtype
  let hi : Function.Injective i := N.injective_subtype
  refine LinearMap.ker_eq_bot.1 <| LinearMap.ker_eq_bot'.2 fun n hn ↦ ?_
  obtain ⟨k, mj, hmj⟩ := exists_fin (R := R) (M := M)
  rw [← surjective_piEquiv_apply_iff] at hmj
  obtain ⟨b, hb⟩ := hmj (i n)
  choose nj hnj using fun j ↦ hf (mj j)
  choose c hc using fun j ↦ hmj (i (nj j))
  let A := Subring.closure (Set.range b ∪ Set.range c.uncurry)
  let N' := span A ({n} ∪ Set.range nj)
  let M' := span A (Set.range mj)
  haveI : IsNoetherianRing A := is_noetherian_subring_closure _
    (.union (Set.finite_range _) (Set.finite_range _))
  haveI : Module.Finite A M' := span_of_finite A (Set.finite_range _)
  refine congr($((LinearMap.ker_eq_bot'.1 <| LinearMap.ker_eq_bot.2 <|
    IsNoetherian.injective_of_surjective_of_injective
      ((i.restrictScalars A).restrict fun x hx ↦ ?_ : N' →ₗ[A] M')
      ((f.restrictScalars A).restrict fun x hx ↦ ?_ : N' →ₗ[A] M')
      (fun _ _ h ↦ injective_subtype _ (hi congr(($h).1)))
      fun ⟨x, hx⟩ ↦ ?_) ⟨n, (subset_span (by simp))⟩ (Subtype.val_injective hn)).1)
  · induction hx using span_induction with
    | mem x hx =>
      change i x ∈ M'
      simp only [Set.singleton_union, Set.mem_insert_iff, Set.mem_range] at hx
      rcases hx with hx | ⟨j, rfl⟩
      · rw [hx, ← hb, piEquiv_apply_apply]
        refine Submodule.sum_mem _ fun j _ ↦ ?_
        let b' : A := ⟨b j, Subring.subset_closure (by simp)⟩
        rw [show b j • mj j = b' • mj j from rfl]
        exact smul_mem _ _ (subset_span (by simp))
      · rw [← hc, piEquiv_apply_apply]
        refine Submodule.sum_mem _ fun j' _ ↦ ?_
        let c' : A := ⟨c j j', Subring.subset_closure
          (by simp [show ∃ a b, c a b = c j j' from ⟨j, j', rfl⟩])⟩
        rw [show c j j' • mj j' = c' • mj j' from rfl]
        exact smul_mem _ _ (subset_span (by simp))
    | zero => simp
    | add x _ y _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact smul_mem _ _ hx
  · induction hx using span_induction with
    | mem x hx =>
      change f x ∈ M'
      simp only [Set.singleton_union, Set.mem_insert_iff, Set.mem_range] at hx
      rcases hx with hx | ⟨j, rfl⟩
      · rw [hx, hn]; exact zero_mem _
      · exact subset_span (by simp [hnj])
    | zero => simp
    | add x _ y _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact smul_mem _ _ hx
  suffices x ∈ LinearMap.range ((f.restrictScalars A).domRestrict N') by
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Subtype.val_injective ha⟩
  induction hx using span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨⟨nj j, subset_span (by simp)⟩, hnj j⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact smul_mem _ a hx

end Orzech
