/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Finiteness
import Mathlib.RingTheory.Noetherian
import Mathlib.Data.Polynomial.Module.Basic

#align_import ring_theory.finite_type from "leanprover-community/mathlib"@"bb168510ef455e9280a152e7f31673cabd3d7496"

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `Algebra.FiniteType`, `RingHom.FiniteType`, `AlgHom.FiniteType`
  all of these express that some object is finitely generated *as algebra* over some base ring.

-/

set_option autoImplicit true


open Function (Surjective)

open BigOperators Polynomial

section ModuleAndAlgebra

universe uR uS uA uB uM uN
variable (R : Type uR) (S : Type uS) (A : Type uA) (B : Type uB) (M : Type uM) (N : Type uN)

/-- An algebra over a commutative semiring is of `FiniteType` if it is finitely generated
over the base ring as algebra. -/
class Algebra.FiniteType [CommSemiring R] [Semiring A] [Algebra R A] : Prop where
  out : (⊤ : Subalgebra R A).FG
#align algebra.finite_type Algebra.FiniteType

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Finite

open Submodule Set

variable {R S M N}

section Algebra

-- see Note [lower instance priority]
instance (priority := 100) finiteType {R : Type*} (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [hRA : Finite R A] : Algebra.FiniteType R A :=
  ⟨Subalgebra.fg_of_submodule_fg hRA.1⟩
#align module.finite.finite_type Module.Finite.finiteType

end Algebra

end Finite

end Module

namespace Algebra

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

namespace FiniteType

theorem self : FiniteType R R :=
  ⟨⟨{1}, Subsingleton.elim _ _⟩⟩
#align algebra.finite_type.self Algebra.FiniteType.self

protected theorem polynomial : FiniteType R R[X] :=
  ⟨⟨{Polynomial.X}, by
      rw [Finset.coe_singleton]
      exact Polynomial.adjoin_X⟩⟩
#align algebra.finite_type.polynomial Algebra.FiniteType.polynomial

open scoped Classical

protected theorem freeAlgebra (ι : Type*) [Finite ι] : FiniteType R (FreeAlgebra R ι) := by
  cases nonempty_fintype ι
  exact
    ⟨⟨Finset.univ.image (FreeAlgebra.ι R), by
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
        exact FreeAlgebra.adjoin_range_ι R ι⟩⟩

protected theorem mvPolynomial (ι : Type*) [Finite ι] : FiniteType R (MvPolynomial ι R) := by
  cases nonempty_fintype ι
  exact
    ⟨⟨Finset.univ.image MvPolynomial.X, by
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
        exact MvPolynomial.adjoin_range_X⟩⟩
#align algebra.finite_type.mv_polynomial Algebra.FiniteType.mvPolynomial

theorem of_restrictScalars_finiteType [Algebra S A] [IsScalarTower R S A] [hA : FiniteType R A] :
    FiniteType S A := by
  obtain ⟨s, hS⟩ := hA.out
  refine' ⟨⟨s, eq_top_iff.2 fun b => _⟩⟩
  have le : adjoin R (s : Set A) ≤ Subalgebra.restrictScalars R (adjoin S s) := by
    apply (Algebra.adjoin_le _ : adjoin R (s : Set A) ≤ Subalgebra.restrictScalars R (adjoin S ↑s))
    simp only [Subalgebra.coe_restrictScalars]
    exact Algebra.subset_adjoin
  exact le (eq_top_iff.1 hS b)
#align algebra.finite_type.of_restrict_scalars_finite_type Algebra.FiniteType.of_restrictScalars_finiteType

variable {R S A B}

theorem of_surjective (hRA : FiniteType R A) (f : A →ₐ[R] B) (hf : Surjective f) : FiniteType R B :=
  ⟨by
    convert hRA.1.map f
    simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, AlgHom.mem_range] using hf⟩
#align algebra.finite_type.of_surjective Algebra.FiniteType.of_surjective

theorem equiv (hRA : FiniteType R A) (e : A ≃ₐ[R] B) : FiniteType R B :=
  hRA.of_surjective e e.surjective
#align algebra.finite_type.equiv Algebra.FiniteType.equiv

theorem trans [Algebra S A] [IsScalarTower R S A] (hRS : FiniteType R S) (hSA : FiniteType S A) :
    FiniteType R A :=
  ⟨fg_trans' hRS.1 hSA.1⟩
#align algebra.finite_type.trans Algebra.FiniteType.trans

/-- An algebra is finitely generated if and only if it is a quotient
of a free algebra whose variables are indexed by a finset. -/
theorem iff_quotient_freeAlgebra :
    FiniteType R A ↔
      ∃ (s : Finset A) (f : FreeAlgebra R s →ₐ[R] A), Surjective f := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, FreeAlgebra.lift _ (↑), ?_⟩
    intro x
    have hrw : (↑s : Set A) = fun x : A => x ∈ s.val := rfl
    rw [← Set.mem_range, ← AlgHom.coe_range]
    erw [← adjoin_eq_range_freeAlgebra_lift, ← hrw, hs]
    exact Set.mem_univ x
  · rintro ⟨s, ⟨f, hsur⟩⟩
    exact FiniteType.of_surjective (FiniteType.freeAlgebra R s) f hsur

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
    rw [← Set.mem_range, ← AlgHom.coe_range, ← adjoin_eq_range, ← hrw, hs]
    exact Set.mem_univ x
  · rintro ⟨s, ⟨f, hsur⟩⟩
    exact FiniteType.of_surjective (FiniteType.mvPolynomial R { x // x ∈ s }) f hsur
#align algebra.finite_type.iff_quotient_mv_polynomial Algebra.FiniteType.iff_quotient_mvPolynomial

/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype. -/
theorem iff_quotient_freeAlgebra' : FiniteType R A ↔
    ∃ (ι : Type uA) (_ : Fintype ι) (f : FreeAlgebra R ι →ₐ[R] A), Surjective f := by
  constructor
  · rw [iff_quotient_freeAlgebra]
    rintro ⟨s, ⟨f, hsur⟩⟩
    use { x : A // x ∈ s }, inferInstance, f
  · rintro ⟨ι, ⟨hfintype, ⟨f, hsur⟩⟩⟩
    letI : Fintype ι := hfintype
    exact FiniteType.of_surjective (FiniteType.freeAlgebra R ι) f hsur

/-- A commutative algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype. -/
theorem iff_quotient_mvPolynomial' : FiniteType R S ↔
    ∃ (ι : Type uS) (_ : Fintype ι) (f : MvPolynomial ι R →ₐ[R] S), Surjective f := by
  constructor
  · rw [iff_quotient_mvPolynomial]
    rintro ⟨s, ⟨f, hsur⟩⟩
    use { x : S // x ∈ s }, inferInstance, f
  · rintro ⟨ι, ⟨hfintype, ⟨f, hsur⟩⟩⟩
    letI : Fintype ι := hfintype
    exact FiniteType.of_surjective (FiniteType.mvPolynomial R ι) f hsur
#align algebra.finite_type.iff_quotient_mv_polynomial' Algebra.FiniteType.iff_quotient_mvPolynomial'

/-- A commutative algebra is finitely generated if and only if it is a quotient of a polynomial ring
in `n` variables. -/
theorem iff_quotient_mvPolynomial'' :
    FiniteType R S ↔ ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] S), Surjective f := by
  constructor
  · rw [iff_quotient_mvPolynomial']
    rintro ⟨ι, hfintype, ⟨f, hsur⟩⟩
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    exact ⟨Fintype.card ι, AlgHom.comp f equiv.symm.toAlgHom, by simpa using hsur⟩
  · rintro ⟨n, ⟨f, hsur⟩⟩
    exact FiniteType.of_surjective (FiniteType.mvPolynomial R (Fin n)) f hsur
#align algebra.finite_type.iff_quotient_mv_polynomial'' Algebra.FiniteType.iff_quotient_mvPolynomial''

instance prod [hA : FiniteType R A] [hB : FiniteType R B] : FiniteType R (A × B) :=
  ⟨by rw [← Subalgebra.prod_top]; exact hA.1.prod hB.1⟩
#align algebra.finite_type.prod Algebra.FiniteType.prod

theorem isNoetherianRing (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [h : Algebra.FiniteType R S] [IsNoetherianRing R] : IsNoetherianRing S := by
  obtain ⟨s, hs⟩ := h.1
  apply
    isNoetherianRing_of_surjective (MvPolynomial s R) S
      (MvPolynomial.aeval (↑) : MvPolynomial s R →ₐ[R] S).toRingHom
  erw [← Set.range_iff_surjective, ← AlgHom.coe_range, ←
    Algebra.adjoin_range_eq_range_aeval, Subtype.range_coe_subtype, Finset.setOf_mem, hs]
  rfl
#align algebra.finite_type.is_noetherian_ring Algebra.FiniteType.isNoetherianRing

theorem _root_.Subalgebra.fg_iff_finiteType (S : Subalgebra R A) : S.FG ↔ Algebra.FiniteType R S :=
  S.fg_top.symm.trans ⟨fun h => ⟨h⟩, fun h => h.out⟩
#align subalgebra.fg_iff_finite_type Subalgebra.fg_iff_finiteType

end FiniteType

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is of `FiniteType` if `B` is finitely generated as `A`-algebra. -/
def FiniteType (f : A →+* B) : Prop :=
  @Algebra.FiniteType A B _ _ f.toAlgebra
#align ring_hom.finite_type RingHom.FiniteType

namespace Finite

theorem finiteType {f : A →+* B} (hf : f.Finite) : FiniteType f :=
  @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf
#align ring_hom.finite.finite_type RingHom.Finite.finiteType

end Finite

namespace FiniteType

variable (A)

theorem id : FiniteType (RingHom.id A) :=
  Algebra.FiniteType.self A
#align ring_hom.finite_type.id RingHom.FiniteType.id

variable {A}

theorem comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.FiniteType) (hg : Surjective g) :
    (g.comp f).FiniteType := by
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra A C := (g.comp f).toAlgebra
  exact Algebra.FiniteType.of_surjective hf
    { g with
      toFun := g
      commutes' := fun a => rfl }
    hg
#align ring_hom.finite_type.comp_surjective RingHom.FiniteType.comp_surjective

theorem of_surjective (f : A →+* B) (hf : Surjective f) : f.FiniteType := by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf
#align ring_hom.finite_type.of_surjective RingHom.FiniteType.of_surjective

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.FiniteType) (hf : f.FiniteType) :
    (g.comp f).FiniteType := by
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra A C := (g.comp f).toAlgebra
  let _ : Algebra B C := g.toAlgebra
  exact @Algebra.FiniteType.trans A B C _ _ _ f.toAlgebra (g.comp f).toAlgebra g.toAlgebra
    ⟨by
      intro a b c
      simp [Algebra.smul_def, RingHom.map_mul, mul_assoc]
      rfl⟩
    hf hg
#align ring_hom.finite_type.comp RingHom.FiniteType.comp

theorem of_finite {f : A →+* B} (hf : f.Finite) : f.FiniteType :=
  @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf
#align ring_hom.finite_type.of_finite RingHom.FiniteType.of_finite

alias _root_.RingHom.Finite.to_finiteType := of_finite
#align ring_hom.finite.to_finite_type RingHom.Finite.to_finiteType

theorem of_comp_finiteType {f : A →+* B} {g : B →+* C} (h : (g.comp f).FiniteType) :
    g.FiniteType := by
  let _ := f.toAlgebra
  let _ := g.toAlgebra
  let _ := (g.comp f).toAlgebra
  let _ : IsScalarTower A B C := RestrictScalars.isScalarTower A B C
  let _ : Algebra.FiniteType A C := h
  exact Algebra.FiniteType.of_restrictScalars_finiteType A B C
#align ring_hom.finite_type.of_comp_finite_type RingHom.FiniteType.of_comp_finiteType

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
#align alg_hom.finite_type AlgHom.FiniteType

namespace Finite

theorem finiteType {f : A →ₐ[R] B} (hf : f.Finite) : FiniteType f :=
  RingHom.Finite.finiteType hf
#align alg_hom.finite.finite_type AlgHom.Finite.finiteType

end Finite

namespace FiniteType

variable (R A)

theorem id : FiniteType (AlgHom.id R A) :=
  RingHom.FiniteType.id A
#align alg_hom.finite_type.id AlgHom.FiniteType.id

variable {R A}

theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.FiniteType) (hf : f.FiniteType) :
    (g.comp f).FiniteType :=
  RingHom.FiniteType.comp hg hf
#align alg_hom.finite_type.comp AlgHom.FiniteType.comp

theorem comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.FiniteType) (hg : Surjective g) :
    (g.comp f).FiniteType :=
  RingHom.FiniteType.comp_surjective hf hg
#align alg_hom.finite_type.comp_surjective AlgHom.FiniteType.comp_surjective

theorem of_surjective (f : A →ₐ[R] B) (hf : Surjective f) : f.FiniteType :=
  RingHom.FiniteType.of_surjective f.toRingHom hf
#align alg_hom.finite_type.of_surjective AlgHom.FiniteType.of_surjective

theorem of_comp_finiteType {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).FiniteType) :
    g.FiniteType :=
  RingHom.FiniteType.of_comp_finiteType h
#align alg_hom.finite_type.of_comp_finite_type AlgHom.FiniteType.of_comp_finiteType

end FiniteType

end AlgHom

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
#align add_monoid_algebra.mem_adjoin_support AddMonoidAlgebra.mem_adjoin_support

/-- If a set `S` generates, as algebra, `R[M]`, then the set of supports of
elements of `S` generates `R[M]`. -/
theorem support_gen_of_gen {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (⋃ f ∈ S, of' R M '' (f.support : Set M)) = ⊤ := by
  refine' le_antisymm le_top _
  rw [← hS, adjoin_le_iff]
  intro f hf
  have hincl :
    of' R M '' f.support ⊆ ⋃ (g : R[M]) (_ : g ∈ S), of' R M '' g.support := by
    intro s hs
    exact Set.mem_iUnion₂.2 ⟨f, ⟨hf, hs⟩⟩
  exact adjoin_mono hincl (mem_adjoin_support f)
#align add_monoid_algebra.support_gen_of_gen AddMonoidAlgebra.support_gen_of_gen

/-- If a set `S` generates, as algebra, `R[M]`, then the image of the union of
the supports of elements of `S` generates `R[M]`. -/
theorem support_gen_of_gen' {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (of' R M '' ⋃ f ∈ S, (f.support : Set M)) = ⊤ := by
  suffices (of' R M '' ⋃ f ∈ S, (f.support : Set M)) = ⋃ f ∈ S, of' R M '' (f.support : Set M) by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_iUnion]
#align add_monoid_algebra.support_gen_of_gen' AddMonoidAlgebra.support_gen_of_gen'

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
#align add_monoid_algebra.exists_finset_adjoin_eq_top AddMonoidAlgebra.exists_finset_adjoin_eq_top

/-- The image of an element `m : M` in `R[M]` belongs the submodule generated by
`S : Set M` if and only if `m ∈ S`. -/
theorem of'_mem_span [Nontrivial R] {m : M} {S : Set M} :
    of' R M m ∈ span R (of' R M '' S) ↔ m ∈ S := by
  refine' ⟨fun h => _, fun h => Submodule.subset_span <| Set.mem_image_of_mem (of R M) h⟩
  erw [of', ← Finsupp.supported_eq_span_single, Finsupp.mem_supported,
    Finsupp.support_single_ne_zero _ (one_ne_zero' R)] at h
  simpa using h
#align add_monoid_algebra.of'_mem_span AddMonoidAlgebra.of'_mem_span

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
#align add_monoid_algebra.mem_closure_of_mem_span_closure AddMonoidAlgebra.mem_closure_of_mem_span_closure

end Ring

end Span

/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`R[M]`. -/
theorem mvPolynomial_aeval_of_surjective_of_closure [AddCommMonoid M] [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (MvPolynomial.aeval fun s : S => of' R M ↑s : MvPolynomial S R → R[M]) := by
  intro f
  induction' f using induction_on with m f g ihf ihg r f ih
  · have : m ∈ closure S := hS.symm ▸ mem_top _
    refine' AddSubmonoid.closure_induction this (fun m hm => _) _ _
    · exact ⟨MvPolynomial.X ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    · exact ⟨1, AlgHom.map_one _⟩
    · rintro m₁ m₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [AlgHom.map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single,
            one_mul]; rfl⟩
  · rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, AlgHom.map_add _ _ _⟩
  · rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, AlgHom.map_smul _ _ _⟩
#align add_monoid_algebra.mv_polynomial_aeval_of_surjective_of_closure AddMonoidAlgebra.mvPolynomial_aeval_of_surjective_of_closure

variable [AddMonoid M]

/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`R[M]`. -/
theorem freeAlgebra_lift_of_surjective_of_closure [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (FreeAlgebra.lift R fun s : S => of' R M ↑s : FreeAlgebra R S → R[M]) := by
  intro f
  induction' f using induction_on with m f g ihf ihg r f ih
  · have : m ∈ closure S := hS.symm ▸ mem_top _
    refine' AddSubmonoid.closure_induction this (fun m hm => _) _ _
    · exact ⟨FreeAlgebra.ι R ⟨m, hm⟩, FreeAlgebra.lift_ι_apply _ _⟩
    · exact ⟨1, AlgHom.map_one _⟩
    · rintro m₁ m₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [AlgHom.map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single,
            one_mul]; rfl⟩
  · rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, AlgHom.map_add _ _ _⟩
  · rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, AlgHom.map_smul _ _ _⟩

variable (R M)

/-- If an additive monoid `M` is finitely generated then `R[M]` is of finite
type. -/
instance finiteType_of_fg [CommRing R] [h : AddMonoid.FG M] :
    FiniteType R R[M] := by
  obtain ⟨S, hS⟩ := h.out
  exact (FiniteType.freeAlgebra R (S : Set M)).of_surjective
      (FreeAlgebra.lift R fun s : (S : Set M) => of' R M ↑s)
      (freeAlgebra_lift_of_surjective_of_closure hS)
#align add_monoid_algebra.finite_type_of_fg AddMonoidAlgebra.finiteType_of_fg

variable {R M}

/-- An additive monoid `M` is finitely generated if and only if `R[M]` is of
finite type. -/
theorem finiteType_iff_fg [CommRing R] [Nontrivial R] :
    FiniteType R R[M] ↔ AddMonoid.FG M := by
  refine' ⟨fun h => _, fun h => @AddMonoidAlgebra.finiteType_of_fg _ _ _ _ h⟩
  obtain ⟨S, hS⟩ := @exists_finset_adjoin_eq_top R M _ _ h
  refine' AddMonoid.fg_def.2 ⟨S, (eq_top_iff' _).2 fun m => _⟩
  have hm : of' R M m ∈ Subalgebra.toSubmodule (adjoin R (of' R M '' ↑S)) := by
    simp only [hS, top_toSubmodule, Submodule.mem_top]
  rw [adjoin_eq_span] at hm
  exact mem_closure_of_mem_span_closure hm
#align add_monoid_algebra.finite_type_iff_fg AddMonoidAlgebra.finiteType_iff_fg

/-- If `R[M]` is of finite type then `M` is finitely generated. -/
theorem fg_of_finiteType [CommRing R] [Nontrivial R] [h : FiniteType R R[M]] :
    AddMonoid.FG M :=
  finiteType_iff_fg.1 h
#align add_monoid_algebra.fg_of_finite_type AddMonoidAlgebra.fg_of_finiteType

/-- An additive group `G` is finitely generated if and only if `R[G]` is of
finite type. -/
theorem finiteType_iff_group_fg {G : Type*} [AddCommGroup G] [CommRing R] [Nontrivial R] :
    FiniteType R R[G] ↔ AddGroup.FG G := by
  simpa [AddGroup.fg_iff_addMonoid_fg] using finiteType_iff_fg
#align add_monoid_algebra.finite_type_iff_group_fg AddMonoidAlgebra.finiteType_iff_group_fg

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
#align monoid_algebra.mem_adjoin_support MonoidAlgebra.mem_adjoin_support

/-- If a set `S` generates, as algebra, `MonoidAlgebra R M`, then the set of supports of elements
of `S` generates `MonoidAlgebra R M`. -/
theorem support_gen_of_gen {S : Set (MonoidAlgebra R M)} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (⋃ f ∈ S, of R M '' (f.support : Set M)) = ⊤ := by
  refine' le_antisymm le_top _
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
#align monoid_algebra.support_gen_of_gen MonoidAlgebra.support_gen_of_gen

/-- If a set `S` generates, as algebra, `MonoidAlgebra R M`, then the image of the union of the
supports of elements of `S` generates `MonoidAlgebra R M`. -/
theorem support_gen_of_gen' {S : Set (MonoidAlgebra R M)} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (of R M '' ⋃ f ∈ S, (f.support : Set M)) = ⊤ := by
  suffices (of R M '' ⋃ f ∈ S, (f.support : Set M)) = ⋃ f ∈ S, of R M '' (f.support : Set M) by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_iUnion]
#align monoid_algebra.support_gen_of_gen' MonoidAlgebra.support_gen_of_gen'

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
#align monoid_algebra.exists_finset_adjoin_eq_top MonoidAlgebra.exists_finset_adjoin_eq_top

/-- The image of an element `m : M` in `MonoidAlgebra R M` belongs the submodule generated by
`S : Set M` if and only if `m ∈ S`. -/
theorem of_mem_span_of_iff [Nontrivial R] {m : M} {S : Set M} :
    of R M m ∈ span R (of R M '' S) ↔ m ∈ S := by
  refine' ⟨fun h => _, fun h => Submodule.subset_span <| Set.mem_image_of_mem (of R M) h⟩
  erw [of, MonoidHom.coe_mk, ← Finsupp.supported_eq_span_single, Finsupp.mem_supported,
    Finsupp.support_single_ne_zero _ (one_ne_zero' R)] at h
  simpa using h
#align monoid_algebra.of_mem_span_of_iff MonoidAlgebra.of_mem_span_of_iff

/--
If the image of an element `m : M` in `MonoidAlgebra R M` belongs the submodule generated by the
closure of some `S : Set M` then `m ∈ closure S`. -/
theorem mem_closure_of_mem_span_closure [Nontrivial R] {m : M} {S : Set M}
    (h : of R M m ∈ span R (Submonoid.closure (of R M '' S) : Set (MonoidAlgebra R M))) :
    m ∈ closure S := by
  rw [← MonoidHom.map_mclosure] at h
  simpa using of_mem_span_of_iff.1 h
#align monoid_algebra.mem_closure_of_mem_span_closure MonoidAlgebra.mem_closure_of_mem_span_closure

end Ring

end Span

/-- If a set `S` generates a monoid `M`, then the image of `M` generates, as algebra,
`MonoidAlgebra R M`. -/
theorem mvPolynomial_aeval_of_surjective_of_closure [CommMonoid M] [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (MvPolynomial.aeval fun s : S => of R M ↑s : MvPolynomial S R → MonoidAlgebra R M) := by
  intro f
  induction' f using induction_on with m f g ihf ihg r f ih
  · have : m ∈ closure S := hS.symm ▸ mem_top _
    refine' Submonoid.closure_induction this (fun m hm => _) _ _
    · exact ⟨MvPolynomial.X ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    · exact ⟨1, AlgHom.map_one _⟩
    · rintro m₁ m₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [AlgHom.map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single, one_mul]⟩
  · rcases ihf with ⟨P, rfl⟩; rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, AlgHom.map_add _ _ _⟩
  · rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, AlgHom.map_smul _ _ _⟩
#align monoid_algebra.mv_polynomial_aeval_of_surjective_of_closure MonoidAlgebra.mvPolynomial_aeval_of_surjective_of_closure


variable [Monoid M]

/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`R[M]`. -/
theorem freeAlgebra_lift_of_surjective_of_closure [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (FreeAlgebra.lift R fun s : S => of R M ↑s : FreeAlgebra R S → MonoidAlgebra R M) := by
  intro f
  induction' f using induction_on with m f g ihf ihg r f ih
  · have : m ∈ closure S := hS.symm ▸ mem_top _
    refine' Submonoid.closure_induction this (fun m hm => _) _ _
    · exact ⟨FreeAlgebra.ι R ⟨m, hm⟩, FreeAlgebra.lift_ι_apply _ _⟩
    · exact ⟨1, AlgHom.map_one _⟩
    · rintro m₁ m₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [AlgHom.map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single, one_mul]⟩
  · rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, AlgHom.map_add _ _ _⟩
  · rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, AlgHom.map_smul _ _ _⟩

/-- If a monoid `M` is finitely generated then `MonoidAlgebra R M` is of finite type. -/
instance finiteType_of_fg [CommRing R] [Monoid.FG M] : FiniteType R (MonoidAlgebra R M) :=
  (AddMonoidAlgebra.finiteType_of_fg R (Additive M)).equiv (toAdditiveAlgEquiv R M).symm
#align monoid_algebra.finite_type_of_fg MonoidAlgebra.finiteType_of_fg

/-- A monoid `M` is finitely generated if and only if `MonoidAlgebra R M` is of finite type. -/
theorem finiteType_iff_fg [CommRing R] [Nontrivial R] :
    FiniteType R (MonoidAlgebra R M) ↔ Monoid.FG M :=
  ⟨fun h =>
    Monoid.fg_iff_add_fg.2 <|
      AddMonoidAlgebra.finiteType_iff_fg.1 <| h.equiv <| toAdditiveAlgEquiv R M,
    fun h => @MonoidAlgebra.finiteType_of_fg _ _ _ _ h⟩
#align monoid_algebra.finite_type_iff_fg MonoidAlgebra.finiteType_iff_fg

/-- If `MonoidAlgebra R M` is of finite type then `M` is finitely generated. -/
theorem fg_of_finiteType [CommRing R] [Nontrivial R] [h : FiniteType R (MonoidAlgebra R M)] :
    Monoid.FG M :=
  finiteType_iff_fg.1 h
#align monoid_algebra.fg_of_finite_type MonoidAlgebra.fg_of_finiteType

/-- A group `G` is finitely generated if and only if `R[G]` is of finite type. -/
theorem finiteType_iff_group_fg {G : Type*} [Group G] [CommRing R] [Nontrivial R] :
    FiniteType R (MonoidAlgebra R G) ↔ Group.FG G := by
  simpa [Group.fg_iff_monoid_fg] using finiteType_iff_fg
#align monoid_algebra.finite_type_iff_group_fg MonoidAlgebra.finiteType_iff_group_fg

end MonoidAlgebra

end MonoidAlgebra

section Vasconcelos

/-- A theorem/proof by Vasconcelos, given a finite module `M` over a commutative ring, any
surjective endomorphism of `M` is also injective. Based on,
https://math.stackexchange.com/a/239419/31917,
https://www.ams.org/journals/tran/1969-138-00/S0002-9947-1969-0238839-5/.
This is similar to `IsNoetherian.injective_of_surjective_endomorphism` but only applies in the
commutative case, but does not use a Noetherian hypothesis. -/
theorem Module.Finite.injective_of_surjective_endomorphism {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Finite R M] (f : M →ₗ[R] M)
    (f_surj : Function.Surjective f) : Function.Injective f := by
  have : (⊤ : Submodule R[X] (AEval' f)) ≤ Ideal.span {(X : R[X])} • ⊤ := by
    intro a _
    obtain ⟨y, rfl⟩ := f_surj.comp (AEval'.of f).symm.surjective a
    rw [Function.comp_apply, ← AEval'.of_symm_X_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton.mpr (dvd_refl _)) trivial
  obtain ⟨F, hFa, hFb⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul _ (⊤ : Submodule R[X] (AEval' f))
      (finite_def.mp inferInstance) this
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  rw [← map_eq_zero_iff (AEval'.of f) (AEval'.of f).injective]
  set m' := Module.AEval'.of f m
  rw [Ideal.mem_span_singleton'] at hFa
  obtain ⟨G, hG⟩ := hFa
  suffices (F - 1) • m' = 0 by
    have Fmzero := hFb m' (by simp)
    rwa [← sub_add_cancel F 1, add_smul, one_smul, this, zero_add] at Fmzero
  rw [← hG, mul_smul, AEval'.X_smul_of, hm, map_zero, smul_zero]
#align module.finite.injective_of_surjective_endomorphism Module.Finite.injective_of_surjective_endomorphism

end Vasconcelos
