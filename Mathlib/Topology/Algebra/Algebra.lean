/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Topological (sub)algebras

A topological algebra over a topological semiring `R` is a topological semiring with a compatible
continuous scalar multiplication by elements of `R`. We reuse typeclass `ContinuousSMul` for
topological algebras.

## Results

The topological closure of a subalgebra is still a subalgebra, which as an algebra is a
topological algebra.

In this file we define continuous algebra homomorphisms, as algebra homomorphisms between
topological (semi-)rings which are continuous. The set of continuous algebra homomorphisms between
the topological `R`-algebras `A` and `B` is denoted by `A →A[R] B`.

TODO: add continuous algebra isomorphisms.

-/

open Algebra Set TopologicalSpace Topology

universe u v w

section TopologicalAlgebra

variable (R : Type*) (A : Type u)
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [TopologicalSpace R] [TopologicalSpace A]

@[continuity, fun_prop]
theorem continuous_algebraMap [ContinuousSMul R A] : Continuous (algebraMap R A) := by
  rw [algebraMap_eq_smul_one']
  exact continuous_id.smul continuous_const

theorem continuous_algebraMap_iff_smul [TopologicalSemiring A] :
    Continuous (algebraMap R A) ↔ Continuous fun p : R × A => p.1 • p.2 := by
  refine ⟨fun h => ?_, fun h => have : ContinuousSMul R A := ⟨h⟩; continuous_algebraMap _ _⟩
  simp only [Algebra.smul_def]
  exact (h.comp continuous_fst).mul continuous_snd

theorem continuousSMul_of_algebraMap [TopologicalSemiring A] (h : Continuous (algebraMap R A)) :
    ContinuousSMul R A :=
  ⟨(continuous_algebraMap_iff_smul R A).1 h⟩

instance Subalgebra.continuousSMul (S : Subalgebra R A) (X) [TopologicalSpace X] [MulAction A X]
    [ContinuousSMul A X] : ContinuousSMul S X :=
  Subsemiring.continuousSMul S.toSubsemiring X

section
variable [ContinuousSMul R A]

/-- The inclusion of the base ring in a topological algebra as a continuous linear map. -/
@[simps]
def algebraMapCLM : R →L[R] A :=
  { Algebra.linearMap R A with
    toFun := algebraMap R A
    cont := continuous_algebraMap R A }

theorem algebraMapCLM_coe : ⇑(algebraMapCLM R A) = algebraMap R A :=
  rfl

theorem algebraMapCLM_toLinearMap : (algebraMapCLM R A).toLinearMap = Algebra.linearMap R A :=
  rfl

end

/-- If `R` is a discrete topological ring, then any topological ring `S` which is an `R`-algebra
is also a topological `R`-algebra.

NB: This could be an instance but the signature makes it very expensive in search.
See https://github.com/leanprover-community/mathlib4/pull/15339
for the regressions caused by making this an instance. -/
theorem DiscreteTopology.instContinuousSMul [TopologicalSemiring A] [DiscreteTopology R] :
    ContinuousSMul R A := continuousSMul_of_algebraMap _ _ continuous_of_discreteTopology

end TopologicalAlgebra

section TopologicalAlgebra

section

variable (R : Type*) [CommSemiring R]
  (A : Type*) [Semiring A]

/-- Continuous algebra homomorphisms between algebras. We only put the type classes that are
necessary for the definition, although in applications `M` and `B` will be topological algebras
over the topological ring `R`. -/
structure ContinuousAlgHom (R : Type*) [CommSemiring R] (A : Type*) [Semiring A]
    [TopologicalSpace A] (B : Type*) [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
    extends A →ₐ[R] B where
-- TODO: replace with `fun_prop` when that is stable
  cont : Continuous toFun := by continuity

@[inherit_doc]
notation:25 A " →A[" R "] " B => ContinuousAlgHom R A B

namespace ContinuousAlgHom

section Semiring

variable {R} {A}
variable [TopologicalSpace A]

variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]

instance : FunLike (A →A[R] B) A B where
  coe f := f.toAlgHom
  coe_injective'  f g h  := by
    cases f; cases g
    simp only [mk.injEq]
    exact AlgHom.ext (congrFun h)

instance : AlgHomClass (A →A[R] B) R A B where
  map_mul f x y    := map_mul f.toAlgHom x y
  map_one f        := map_one f.toAlgHom
  map_add f        := map_add f.toAlgHom
  map_zero f       := map_zero f.toAlgHom
  commutes f r     := f.toAlgHom.commutes r

@[simp]
theorem toAlgHom_eq_coe (f : A →A[R] B) : f.toAlgHom = f := rfl

@[simp, norm_cast]
theorem coe_inj {f g : A →A[R] B} : (f : A →ₐ[R] B) = g ↔ f = g :=   by
  cases f; cases g; simp only [mk.injEq]; exact Eq.congr_right rfl

@[simp]
theorem coe_mk (f : A →ₐ[R] B) (h) : (mk f h : A →ₐ[R] B) = f := rfl

@[simp]
theorem coe_mk' (f : A →ₐ[R] B) (h) : (mk f h : A → B) = f := rfl

@[simp, norm_cast]
theorem coe_coe (f : A →A[R] B) : ⇑(f : A →ₐ[R] B) = f := rfl

instance : ContinuousMapClass (A →A[R] B) A B where
  map_continuous f := f.2

@[fun_prop]
protected theorem continuous (f : A →A[R] B) : Continuous f := f.2

protected theorem uniformContinuous {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [Ring E₁] [Ring E₂] [Algebra R E₁] [Algebra R E₂] [UniformAddGroup E₁]
    [UniformAddGroup E₂] (f : E₁ →A[R] E₂) : UniformContinuous f :=
  uniformContinuous_addMonoidHom_of_continuous f.continuous

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (h : A →A[R] B) : A → B := h

/-- See Note [custom simps projection]. -/
def Simps.coe (h : A →A[R] B) : A →ₐ[R] B := h

initialize_simps_projections ContinuousAlgHom (toFun → apply, toAlgHom → coe)

@[ext]
theorem ext {f g : A →A[R] B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/-- Copy of a `ContinuousAlgHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
def copy (f : A →A[R] B) (f' : A → B) (h : f' = ⇑f) : A →A[R] B where
  toAlgHom := {
    toRingHom := (f : A →A[R] B).toRingHom.copy f' h
    commutes' := fun r => by
      simp only [AlgHom.toRingHom_eq_coe, h, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_copy, AlgHomClass.commutes f r] }
  cont := show Continuous f' from h.symm ▸ f.continuous

@[simp]
theorem coe_copy (f : A →A[R] B) (f' : A → B) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' := rfl

theorem copy_eq (f : A →A[R] B) (f' : A → B) (h : f' = ⇑f) : f.copy f' h = f := DFunLike.ext' h

protected theorem map_zero (f : A →A[R] B) : f (0 : A) = 0 := map_zero f

protected theorem map_add (f : A →A[R] B) (x y : A) : f (x + y) = f x + f y := map_add f x y

protected theorem map_smul (f : A →A[R] B) (c : R) (x : A) :
    f (c • x) = c • f x :=
  map_smul ..

theorem map_smul_of_tower {R S : Type*} [CommSemiring S] [SMul R A] [Algebra S A] [SMul R B]
    [Algebra S B] [MulActionHomClass (A →A[S] B) R A B] (f : A →A[S] B) (c : R) (x : A) :
    f (c • x) = c • f x :=
  map_smul f c x

protected theorem map_sum {ι : Type*} (f : A →A[R] B) (s : Finset ι) (g : ι → A) :
    f (∑ i in s, g i) = ∑ i in s, f (g i) :=
  map_sum ..

/-- Any two continuous `R`-algebra morphisms from `R` are equal -/
@[ext (iff := false)]
theorem ext_ring [TopologicalSpace R] {f g : R →A[R] A} : f = g :=
  coe_inj.mp (ext_id _ _ _)

theorem ext_ring_iff [TopologicalSpace R] {f g : R →A[R] A} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, fun _ => ext_ring ⟩

/-- If two continuous algebra maps are equal on a set `s`, then they are equal on the closure
of the `Algebra.adjoin` of this set. -/
theorem eqOn_closure_adjoin [T2Space B] {s : Set A} {f g : A →A[R] B} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure (Algebra.adjoin R s : Set A)) :=
  Set.EqOn.closure (AlgHom.eqOn_adjoin_iff.mpr h) f.continuous g.continuous

/-- If the subalgebra generated by a set `s` is dense in the ambient module, then two continuous
algebra maps equal on `s` are equal. -/
theorem ext_on [T2Space B] {s : Set A} (hs : Dense (Algebra.adjoin R s : Set A))
    {f g : A →A[R] B} (h : Set.EqOn f g s) : f = g :=
  ext fun x => eqOn_closure_adjoin h (hs x)

variable [TopologicalSemiring A]

/-- The topological closure of a subalgebra -/
def _root_.Subalgebra.topologicalClosure (s : Subalgebra R A) : Subalgebra R A where
  toSubsemiring := s.toSubsemiring.topologicalClosure
  algebraMap_mem' r := by
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subsemiring.topologicalClosure_coe,
      Subalgebra.coe_toSubsemiring]
    apply subset_closure
    exact algebraMap_mem s r

/-- Under a continuous algebra map, the image of the `TopologicalClosure` of a subalgebra is
contained in the `TopologicalClosure` of its image. -/
theorem _root_.Subalgebra.topologicalClosure_map
    [TopologicalSemiring B] (f : A →A[R] B) (s : Subalgebra R A) :
    s.topologicalClosure.map f ≤ (s.map f.toAlgHom).topologicalClosure :=
  image_closure_subset_closure_image f.continuous

@[simp]
theorem _root_.Subalgebra.topologicalClosure_coe
    (s : Subalgebra R A) :
  (s.topologicalClosure : Set A) = closure ↑s := rfl

/-- Under a dense continuous algebra map, a subalgebra
whose `TopologicalClosure` is `⊤` is sent to another such submodule.
That is, the image of a dense subalgebra under a map with dense range is dense.
-/
theorem _root_.DenseRange.topologicalClosure_map_subalgebra
    [TopologicalSemiring B] {f : A →A[R] B} (hf' : DenseRange f) {s : Subalgebra R A}
    (hs : s.topologicalClosure = ⊤) : (s.map (f : A →ₐ[R] B)).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Subalgebra.topologicalClosure_coe, coe_top, ← dense_iff_closure_eq, Subalgebra.coe_map,
    AlgHom.coe_coe] at hs ⊢
  exact hf'.dense_image f.continuous hs

end Semiring

section id

variable [TopologicalSpace A]
variable [Algebra R A]

/-- The identity map as a continuous algebra homomorphism. -/
protected def id : A →A[R] A := ⟨AlgHom.id R A, continuous_id⟩

instance : One (A →A[R] A) := ⟨ContinuousAlgHom.id R A⟩

theorem one_def : (1 : A →A[R] A) = ContinuousAlgHom.id R A := rfl

theorem id_apply (x : A) : ContinuousAlgHom.id R A x = x := rfl

@[simp, norm_cast]
theorem coe_id : ((ContinuousAlgHom.id R A) : A →ₐ[R] A) = AlgHom.id R A:= rfl

@[simp, norm_cast]
theorem coe_id' : ⇑(ContinuousAlgHom.id R A ) = _root_.id := rfl

@[simp, norm_cast]
theorem coe_eq_id {f : A →A[R] A} :
    (f : A →ₐ[R] A) = AlgHom.id R A ↔ f = ContinuousAlgHom.id R A:= by
  rw [← coe_id, coe_inj]

@[simp]
theorem one_apply (x : A) : (1 : A →A[R] A) x = x := rfl

end id

section comp

variable {R} {A}
variable [TopologicalSpace A]
variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
  {C : Type*} [Semiring C] [Algebra R C] [TopologicalSpace C]

/-- Composition of continuous algebra homomorphisms. -/
def comp (g : B →A[R] C) (f : A →A[R] B) : A →A[R] C :=
  ⟨(g : B →ₐ[R] C).comp (f : A →ₐ[R] B), g.2.comp f.2⟩

@[simp, norm_cast]
theorem coe_comp (h : B →A[R] C) (f : A →A[R] B) :
    (h.comp f : A →ₐ[R] C) = (h : B →ₐ[R] C).comp (f : A →ₐ[R] B) := rfl

@[simp, norm_cast]
theorem coe_comp' (h : B →A[R] C) (f : A →A[R] B) : ⇑(h.comp f) = h ∘ f := rfl

theorem comp_apply (g : B →A[R] C) (f : A →A[R] B) (x : A) : (g.comp f) x = g (f x) := rfl

@[simp]
theorem comp_id (f : A →A[R] B) : f.comp (ContinuousAlgHom.id R A) = f :=
  ext fun _x => rfl

@[simp]
theorem id_comp (f : A →A[R] B) : (ContinuousAlgHom.id R B).comp f = f :=
  ext fun _x => rfl

theorem comp_assoc {D : Type*} [Semiring D] [Algebra R D] [TopologicalSpace D] (h : C →A[R] D)
    (g : B →A[R] C) (f : A →A[R] B) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

instance : Mul (A →A[R] A) := ⟨comp⟩

theorem mul_def (f g : A →A[R] A) : f * g = f.comp g := rfl

@[simp]
theorem coe_mul (f g : A →A[R] A) : ⇑(f * g) = f ∘ g := rfl

theorem mul_apply (f g : A →A[R] A) (x : A) : (f * g) x = f (g x) := rfl

instance : Monoid (A →A[R] A) where
  mul_one _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_assoc _ _ _ := ext fun _ => rfl

theorem coe_pow (f : A →A[R] A) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

/-- coercion from `ContinuousAlgHom` to `AlgHom` as a `RingHom`. -/
@[simps]
def toAlgHomMonoidHom : (A →A[R] A) →* A →ₐ[R] A where
  toFun        := (↑)
  map_one'     := rfl
  map_mul' _ _ := rfl

end comp

section prod

variable {R} {A}
variable [TopologicalSpace A]
variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
  {C : Type*} [Semiring C] [Algebra R C] [TopologicalSpace C]

/-- The cartesian product of two continuous algebra morphisms as a continuous algebra morphism. -/
protected def prod (f₁ : A →A[R] B) (f₂ : A →A[R] C) :
    A →A[R] B × C :=
  ⟨(f₁ : A →ₐ[R] B).prod f₂, f₁.2.prod_mk f₂.2⟩

@[simp, norm_cast]
theorem coe_prod (f₁ : A →A[R] B) (f₂ : A →A[R] C) :
    (f₁.prod f₂ : A →ₐ[R] B × C) = AlgHom.prod f₁ f₂ :=
  rfl

@[simp, norm_cast]
theorem prod_apply (f₁ : A →A[R] B) (f₂ : A →A[R] C) (x : A) :
    f₁.prod f₂ x = (f₁ x, f₂ x) :=
  rfl

variable {F : Type*}

instance {D : Type*} [UniformSpace D] [CompleteSpace D]
    [Semiring D] [Algebra R D] [T2Space B]
    [FunLike F D B] [AlgHomClass F R D B] [ContinuousMapClass F D B]
    (f g : F) : CompleteSpace (AlgHom.equalizer f g) :=
  isClosed_eq (map_continuous f) (map_continuous g) |>.completeSpace_coe

variable (R A B)

/-- `Prod.fst` as a `ContinuousAlgHom`. -/
def fst : A × B →A[R] A where
  cont     := continuous_fst
  toAlgHom := AlgHom.fst R A B

/-- `Prod.snd` as a `ContinuousAlgHom`. -/
def snd : A × B →A[R] B where
  cont := continuous_snd
  toAlgHom := AlgHom.snd R A B

variable {R A B}

@[simp, norm_cast]
theorem coe_fst : ↑(fst R A B) = AlgHom.fst R A B :=
  rfl

@[simp, norm_cast]
theorem coe_fst' : ⇑(fst R A B) = Prod.fst :=
  rfl

@[simp, norm_cast]
theorem coe_snd : ↑(snd R A B) = AlgHom.snd R A B :=
  rfl

@[simp, norm_cast]
theorem coe_snd' : ⇑(snd R A B) = Prod.snd :=
  rfl

@[simp]
theorem fst_prod_snd  : (fst R A B).prod (snd R A B) = ContinuousAlgHom.id R (A × B) :=
  ext fun ⟨_x, _y⟩ => rfl

@[simp]
theorem fst_comp_prod (f : A →A[R] B) (g : A →A[R] C) :
    (fst R B C).comp (f.prod g) = f :=
  ext fun _x => rfl

@[simp]
theorem snd_comp_prod (f : A →A[R] B) (g : A →A[R] C) :
    (snd R B C).comp (f.prod g) = g :=
  ext fun _x => rfl

/-- `Prod.map` of two continuous algebra homomorphisms. -/
def prodMap {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A →A[R] B)
    (f₂ : C →A[R] D) : A × C →A[R] B × D :=
  (f₁.comp (fst R A C)).prod (f₂.comp (snd R A C))


@[simp, norm_cast]
theorem coe_prodMap {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A →A[R] B)
    (f₂ : C →A[R] D) :
    (f₁.prodMap f₂ : A × C →ₐ[R] B × D) = (f₁ : A →ₐ[R] B).prodMap (f₂ : C →ₐ[R] D) :=
  rfl

@[simp, norm_cast]
theorem coe_prodMap' {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A →A[R] B)
    (f₂ : C →A[R] D) : ⇑(f₁.prodMap f₂) = Prod.map f₁ f₂ :=
  rfl

/-- `ContinuousAlgHom.prod` as an `Equiv`. -/
@[simps apply]
def prodEquiv : (A →A[R] B) × (A →A[R] C) ≃ (A →A[R] B × C) where
  toFun f     := f.1.prod f.2
  invFun f    := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩
  left_inv f  := by ext <;> rfl
  right_inv f := by ext <;> rfl

end prod

section subalgebra

variable {R A}
variable [TopologicalSpace A]
variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]

/-- Restrict codomain of a continuous algebra morphism. -/
def codRestrict (f : A →A[R] B) (p : Subalgebra R B) (h : ∀ x, f x ∈ p) : A →A[R] p where
  cont     := f.continuous.subtype_mk _
  toAlgHom := (f : A →ₐ[R] B).codRestrict p h

@[norm_cast]
theorem coe_codRestrict (f : A →A[R] B) (p : Subalgebra R B) (h : ∀ x, f x ∈ p) :
    (f.codRestrict p h : A →ₐ[R] p) = (f : A →ₐ[R] B).codRestrict p h :=
  rfl

@[simp]
theorem coe_codRestrict_apply (f : A →A[R] B) (p : Subalgebra R B) (h : ∀ x, f x ∈ p) (x) :
    (f.codRestrict p h x : B) = f x :=
  rfl

/-- Restrict the codomain of a continuous algebra homomorphism `f` to `f.range`. -/
@[reducible]
def rangeRestrict (f : A →A[R] B) :=
  f.codRestrict (@AlgHom.range R A B  _ _ _ _ _ f) (@AlgHom.mem_range_self R A B  _ _ _ _ _ f)

@[simp]
theorem coe_rangeRestrict (f : A →A[R] B) :
    (f.rangeRestrict : A →ₐ[R] (@AlgHom.range R A B  _ _ _ _ _ f)) =
      (f : A →ₐ[R] B).rangeRestrict :=
  rfl

/-- `Subalgebra.val` as a `ContinuousAlgHom`. -/
def _root_.Subalgebra.valA (p : Subalgebra R A) : p →A[R] A where
  cont := continuous_subtype_val
  toAlgHom := p.val

@[simp, norm_cast]
theorem _root_.Subalgebra.coe_valA (p : Subalgebra R A) :
    (p.valA : p →ₐ[R] A) = p.subtype :=
  rfl

@[simp]
theorem _root_.Subalgebra.coe_valA' (p : Subalgebra R A) : ⇑p.valA = p.subtype :=
  rfl

@[simp]
theorem _root_.Subalgebra.valA_apply (p : Subalgebra R A) (x : p) : p.valA x = x :=
  rfl

@[simp]
theorem _root_.Submodule.range_valA (p : Subalgebra R A) :
    @AlgHom.range R p A _ _ _ _ _ p.valA = p :=
  Subalgebra.range_val p

end subalgebra

section Ring


variable {S : Type*} [Ring S] [TopologicalSpace S] [Algebra R S] {B : Type*} [Ring B]
  [TopologicalSpace B] [Algebra R B]

protected theorem map_neg (f : S →A[R] B) (x : S) : f (-x) = -f x := map_neg f x

protected theorem map_sub (f : S →A[R] B) (x y : S) : f (x - y) = f x - f y := map_sub f x y

end Ring


section RestrictScalars

variable {S : Type*} [CommSemiring S] [Algebra R S] {B : Type*} [Ring B] [TopologicalSpace B]
  [Algebra R B] [Algebra S B] [IsScalarTower R S B] {C : Type*} [Ring C] [TopologicalSpace C]
  [Algebra R C] [Algebra S C] [IsScalarTower R S C]

/-- If `A` is an `R`-algebra, then a continuous `A`-algebra morphism can be interpreted as a
continuous `R`-algebra morphism. -/
def restrictScalars (f : B →A[S] C) : B →A[R] C :=
  ⟨(f : B →ₐ[S] C).restrictScalars R, f.continuous⟩

variable {R}

@[simp]
theorem coe_restrictScalars (f : B →A[S] C) :
    (f.restrictScalars R : B →ₐ[R] C) = (f : B →ₐ[S] C).restrictScalars R :=
  rfl

@[simp]
theorem coe_restrictScalars' (f : B →A[S] C) : ⇑(f.restrictScalars R) = f :=
  rfl

end RestrictScalars

end ContinuousAlgHom

end

variable {R : Type*} [CommSemiring R]
variable {A : Type u} [TopologicalSpace A]
variable [Semiring A] [Algebra R A]
variable [TopologicalSemiring A]

instance (s : Subalgebra R A) : TopologicalSemiring s :=
  s.toSubsemiring.topologicalSemiring

theorem Subalgebra.le_topologicalClosure (s : Subalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure

theorem Subalgebra.isClosed_topologicalClosure (s : Subalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) := by convert @isClosed_closure A s _

theorem Subalgebra.topologicalClosure_minimal (s : Subalgebra R A) {t : Subalgebra R A} (h : s ≤ t)
    (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a subalgebra of a topological algebra is commutative, then so is its topological closure.

See note [reducible non-instances]. -/
abbrev Subalgebra.commSemiringTopologicalClosure [T2Space A] (s : Subalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

/-- This is really a statement about topological algebra isomorphisms,
but we don't have those, so we use the clunky approach of talking about
an algebra homomorphism, and a separate homeomorphism,
along with a witness that as functions they are the same.
-/
theorem Subalgebra.topologicalClosure_comap_homeomorph (s : Subalgebra R A) {B : Type*}
    [TopologicalSpace B] [Ring B] [TopologicalRing B] [Algebra R B] (f : B →ₐ[R] A) (f' : B ≃ₜ A)
    (w : (f : B → A) = f') : s.topologicalClosure.comap f = (s.comap f).topologicalClosure := by
  apply SetLike.ext'
  simp only [Subalgebra.topologicalClosure_coe]
  simp only [Subalgebra.coe_comap, Subsemiring.coe_comap, AlgHom.coe_toRingHom]
  rw [w]
  exact f'.preimage_closure _

variable (R)

open Subalgebra

/-- The topological closure of the subalgebra generated by a single element. -/
def Algebra.elemental (x : A) : Subalgebra R A :=
  (Algebra.adjoin R ({x} : Set A)).topologicalClosure

@[deprecated (since := "2024-11-05")] alias Algebra.elementalAlgebra := Algebra.elemental

namespace Algebra.elemental

@[aesop safe apply (rule_sets := [SetLike])]
theorem self_mem (x : A) : x ∈ elemental R x :=
  le_topologicalClosure _ <| self_mem_adjoin_singleton R x

@[deprecated (since := "2024-11-05")] alias _root_.Algebra.self_mem_elementalAlgebra := self_mem

variable {R} in
theorem le_of_mem {x : A} {s : Subalgebra R A} (hs : IsClosed (s : Set A)) (hx : x ∈ s) :
    elemental R x ≤ s :=
  topologicalClosure_minimal _ (adjoin_le <| by simpa using hx) hs

variable {R} in
theorem le_iff_mem {x : A} {s : Subalgebra R A} (hs : IsClosed (s : Set A)) :
    elemental R x ≤ s ↔ x ∈ s :=
  ⟨fun h ↦ h (self_mem R x), fun h ↦ le_of_mem hs h⟩

instance isClosed (x : A) : IsClosed (elemental R x : Set A) :=
  isClosed_topologicalClosure _

instance [T2Space A] {x : A} : CommSemiring (elemental R x) :=
  commSemiringTopologicalClosure _
    letI : CommSemiring (adjoin R {x}) :=
      adjoinCommSemiringOfComm R fun y hy z hz => by
        rw [mem_singleton_iff] at hy hz
        rw [hy, hz]
    fun _ _ => mul_comm _ _

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [Semiring A]
    [TopologicalSemiring A] [Algebra R A] (x : A) :
    CompleteSpace (elemental R x) :=
  isClosed_closure.completeSpace_coe

/-- The coercion from an elemental algebra to the full algebra is a `IsClosedEmbedding`. -/
theorem isClosedEmbedding_coe (x : A) : IsClosedEmbedding ((↑) : elemental R x → A) where
  eq_induced := rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x

end Algebra.elemental

end TopologicalAlgebra

section Ring

variable {R : Type*} [CommRing R]
variable {A : Type u} [TopologicalSpace A]
variable [Ring A]
variable [Algebra R A] [TopologicalRing A]

/-- If a subalgebra of a topological algebra is commutative, then so is its topological closure.
See note [reducible non-instances]. -/
abbrev Subalgebra.commRingTopologicalClosure [T2Space A] (s : Subalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }

instance [T2Space A] {x : A} : CommRing (elemental R x) where
  mul_comm := mul_comm

end Ring
