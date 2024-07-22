/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.Topology.Algebra.Algebra
import Mathlib.Algebra.Algebra.Pi

/-!  # Topological algebras

A topological algebra `S` over a commutative topological ring `R` is an `R`-algebra `S`
which is a topological ring and such that the algebra map from `R` to `S` is continuous.

-/

section
--TODO: move to correct file

/-- `Prod.map` of two algebra homomorphisms. -/
def AlgHom.prodMap {R A B C D : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Semiring D] [Algebra R A] [Algebra R B] [Algebra R C]  [Algebra R D] (f : A →ₐ[R] B)
    (g : C →ₐ[R] D) :
    A × C →ₐ[R] B × D :=
  { toRingHom := f.toRingHom.prodMap g.toRingHom
    commutes' := fun r => by
      simp only [toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, Prod.algebraMap_apply,
        OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_prodMap,
        RingHom.coe_coe, Prod.map_apply, commutes] }

-- NOTE: RingHom.pi and AlgHom.pi are not available.
end


open Set Filter TopologicalSpace Function Topology Filter BigOperators

/- MI: I am commenting out this section because in the Mathlib file, there is a comment that
`ContinuousSMul` is reused for `TopologicalAlgebra`.
In terms of `DContinuousSMul`, the only one of these lemmas that seems to be missing in Mathlib
 is `DiscreteTopology.continuousSMul`.
-/
/- section TopologicalAlgebra

/-- A topological algebra `S` over a commutative topological semiring `R` is an `R`-algebra `S`
  which is a topological semiring and such that the algebra map from `R` to `S` is continuous. -/
class TopologicalAlgebra (R : Type*) [CommSemiring R] [TopologicalSpace R]
    [TopologicalSemiring R] (A : Type*) [Semiring A] [TopologicalSpace A] [TopologicalSemiring A] extends
    Algebra R A where
  continuous_algebraMap : Continuous (algebraMap R A)

variable (R : Type*) [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]
  (A : Type*) [Semiring A] [TopologicalSpace A] [TopologicalSemiring A]

/-- If `R` is a discrete topological ring,
  then any topological ring `S` which is an `R`-algebra
  is also a topological `R`-algebra. -/
instance DiscreteTopology.topologicalAlgebra [DiscreteTopology R] [Algebra R A] :
    TopologicalAlgebra R A :=
  { (inferInstance : Algebra R A) with
    continuous_algebraMap := continuous_of_discreteTopology }

namespace Subalgebra

variable [TopologicalAlgebra R A]
/-- An `R`-subalgebra `S` of `A` is a topological algebra (with the subspace topology). -/
instance topologicalAlgebra (S : Subalgebra R A) :
    TopologicalAlgebra R S where
  continuous_algebraMap := by
    rw [inducing_subtype_val.continuous_iff]
    suffices Subtype.val ∘ (algebraMap R S) = algebraMap R A by
      erw [this]
      exact TopologicalAlgebra.continuous_algebraMap
    rfl

end Subalgebra

section Prod

/-- The product topology on the cartesian product of two topological algebras
  makes the product into a topological algebra. -/
instance [TopologicalAlgebra R A] {B : Type*} [Semiring B] [TopologicalSpace B]
    [TopologicalSemiring B] [TopologicalAlgebra R B] : TopologicalAlgebra R (A × B) :=
{ (inferInstance : Algebra R (A × B)) with
  continuous_algebraMap := continuous_prod_mk.mpr
    ⟨TopologicalAlgebra.continuous_algebraMap, TopologicalAlgebra.continuous_algebraMap⟩ }

end Prod

section Pi

/-- The product topology on the cartesian product of two topological algebras
  makes the product into a topological algebra. -/
instance Pi.topologicalAlgebra {β : Type*} {C : β → Type*} [∀ b, Semiring (C b)]
    [∀ b, TopologicalSpace (C b)] [∀ b, TopologicalSemiring (C b)]
    [∀ b, TopologicalAlgebra R (C b)] :
  TopologicalAlgebra R (Π b , C b) :=
{ toAlgebra := Pi.algebra _ _
  continuous_algebraMap :=
    continuous_pi_iff.mpr fun _ =>  TopologicalAlgebra.continuous_algebraMap }

end Pi -/

section TopologicalAlgebra

variable (R : Type*) [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]
  (A : Type*) [Semiring A] [TopologicalSpace A] [TopologicalSemiring A]

/-- If `R` is a discrete topological ring,
  then any topological ring `S` which is an `R`-algebra
  is also a topological `R`-algebra. -/
instance DiscreteTopology.continuousSMul [DiscreteTopology R] [Algebra R A] :
    ContinuousSMul R A := continuousSMul_of_algebraMap _ _ continuous_of_discreteTopology
section

/-- Continuous algebra homomorphisms between algebras. We only put the type classes that are necessary for the
definition, although in applications `M` and `B` will be topological algebras over the topological
ring `R`. -/
structure ContinuousAlgHom (R : Type*) [CommSemiring R] (A : Type*) [Semiring A]
    [TopologicalSpace A] (B : Type*) [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
    extends A →ₐ[R] B where
  cont : Continuous toFun := by continuity

/-- `ContinuousAlgHomClass F R A B` asserts `F` is a type of bundled continuous `R`-agebra
  homomorphisms `A → B`. -/
class ContinuousAlgHomClass (F : Type*) (R : outParam (Type*)) [CommSemiring R]
    (A : outParam (Type*)) [Semiring A] [TopologicalSpace A]
    (B : outParam (Type*)) [Semiring B] [TopologicalSpace B][Algebra R A]
    [Algebra R B] [FunLike F A B]
    extends AlgHomClass F R A B, ContinuousMapClass F A B : Prop
attribute [inherit_doc ContinuousAlgHom] ContinuousAlgHom.cont

@[inherit_doc]
notation:25 A " →A[" R "] " B => ContinuousAlgHom R A B

namespace ContinuousAlgHom

section Semiring

variable {R} {A}
variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]

attribute [coe] ContinuousAlgHom.toAlgHom
/-- Coerce continuous algebra morphisms to algebra morphisms. -/
instance AlgHom.coe : Coe (A →A[R] B) (A →ₐ[R] B) := ⟨toAlgHom⟩

theorem coe_injective : Function.Injective ((↑) : (A →A[R] B) → A →ₐ[R] B) := by
  intro f g H
  cases f
  cases g
  congr

instance funLike : FunLike (A →A[R] B) A B where
  coe f := f.toAlgHom
  coe_injective'  _ _ h  := coe_injective (DFunLike.coe_injective h)

instance continuousAlgHomClass :
    ContinuousAlgHomClass (A →A[R] B) R A B where
      map_mul f x y    := map_mul f.toAlgHom x y
      map_one f        := map_one f.toAlgHom
      map_add f        := map_add f.toAlgHom
      map_zero f       := map_zero f.toAlgHom
      commutes f r     := f.toAlgHom.commutes r
      map_continuous f := f.2

theorem coe_mk (f : A →ₐ[R] B) (h) : (mk f h : A →ₐ[R] B) = f := rfl

@[simp]
theorem coe_mk' (f : A →ₐ[R] B) (h) : (mk f h : A → B) = f := rfl

@[continuity]
protected theorem continuous (f : A →A[R] B) : Continuous f := f.2

protected theorem uniformContinuous {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [Ring E₁] [Ring E₂] [Algebra R E₁] [Algebra R E₂] [UniformAddGroup E₁]
    [UniformAddGroup E₂] (f : E₁ →A[R] E₂) : UniformContinuous f :=
  uniformContinuous_addMonoidHom_of_continuous f.continuous

@[simp, norm_cast]
theorem coe_inj {f g : A →A[R] B} : (f : A →ₐ[R] B) = g ↔ f = g := coe_injective.eq_iff

theorem coeFn_injective : @Function.Injective (A →A[R] B) (A → B) (↑) := DFunLike.coe_injective

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : A →A[R] B) : A → B := h

/-- See Note [custom simps projection]. -/
def Simps.coe (h : A →A[R] B) : A →ₐ[R] B := h

initialize_simps_projections ContinuousAlgHom (toAlgHom_toFun → apply, toAlgHom → coe)

@[ext]
theorem ext {f g : A →A[R] B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

theorem ext_iff {f g : A →A[R] B} : f = g ↔ ∀ x, f x = g x := DFunLike.ext_iff

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
    f (c • x) = c • f x := map_smul f c x

theorem map_smul_of_tower {R S : Type*} [CommSemiring S] [SMul R A] [Algebra S A] [SMul R B]
    [Algebra S B] [MulActionHomClass (A →A[S] B) R A B] (f : A →A[S] B) (c : R) (x : A) :
    f (c • x) = c • f x :=
  map_smul f c x

@[deprecated _root_.map_sum]
protected theorem map_sum {ι : Type*} (f : A →A[R] B) (s : Finset ι) (g : ι → A) :
    f (∑ i in s, g i) = ∑ i in s, f (g i) :=
  map_sum ..

@[simp, norm_cast]
theorem coe_coe (f : A →A[R] B) : ⇑(f : A →ₐ[R] B) = f := rfl

@[ext]
theorem ext_ring [TopologicalSpace R] {f g : R →A[R] A} : f = g := by
  apply coe_inj.1
  apply Algebra.ext_id

theorem ext_ring_iff [TopologicalSpace R] {f g : R →A[R] A} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, fun _ => ext_ring ⟩

/-- If two continuous algebra maps are equal on a set `s`, then they are equal on the closure
of the `Submodule.span` of this set. -/
theorem eqOn_closure_span [T2Space B] {s : Set A} {f g : A →A[R] B} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure (Submodule.span R s : Set A)) :=
  (LinearMap.eqOn_span' h).closure f.continuous g.continuous

/-- If the submodule generated by a set `s` is dense in the ambient module, then two continuous
algebra maps equal on `s` are equal. -/
theorem ext_on [T2Space B] {s : Set A} (hs : Dense (Submodule.span R s : Set A))
    {f g : A →A[R] B} (h : Set.EqOn f g s) : f = g :=
  ext fun x => eqOn_closure_span h (hs x)

/-- Under a continuous algebra map, the image of the `TopologicalClosure` of a submodule is
contained in the `TopologicalClosure` of its image. -/
theorem _root_.Submodule.topologicalClosure_map' [TopologicalSpace R] [ContinuousAdd A]
    [ContinuousSMul R B] [ContinuousAdd B] (f : A →A[R] B) (s : Submodule R A) :
    s.topologicalClosure.map (f : A →ₐ[R] B) ≤ (s.map (f : A →ₐ[R] B)).topologicalClosure :=
  image_closure_subset_closure_image f.continuous

/-- Under a dense continuous algebra map, a submodule whose `TopologicalClosure` is `⊤` is sent to
another such submodule.  That is, the image of a dense set under a map with dense range is dense.
-/
theorem _root_.DenseRange.topologicalClosure_map_submodule' [TopologicalSpace R] [ContinuousAdd A]
    [ContinuousSMul R B] [ContinuousAdd B] {f : A →A[R] B}  (hf' : DenseRange f) {s : Submodule R A}
    (hs : s.topologicalClosure = ⊤) : (s.map (f : A →ₐ[R] B)).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Submodule.topologicalClosure_coe, Submodule.top_coe, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image f.continuous hs

end Semiring

section id

variable [Algebra R A]

/-- The identity map as a continuous algebra homomorphism. -/
def id : A →A[R] A := ⟨AlgHom.id R A, continuous_id⟩

instance one : One (A →A[R] A) := ⟨id R A⟩

theorem one_def : (1 : A →A[R] A) = id R A := rfl

theorem id_apply (x : A) : id R A x = x := rfl

@[simp, norm_cast]
theorem coe_id : ((id R A) : A →ₐ[R] A) = AlgHom.id R A:= rfl

@[simp, norm_cast]
theorem coe_id' : ⇑(id R A ) = _root_.id := rfl

@[simp, norm_cast]
theorem coe_eq_id {f : A →A[R] A} : (f : A →ₐ[R] A) = AlgHom.id R A ↔ f = id R A:= by
  rw [← coe_id, coe_inj]

@[simp]
theorem one_apply (x : A) : (1 : A →A[R] A) x = x := rfl

end id

section comp

variable {R} {A}
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
theorem comp_id (f : A →A[R] B) : f.comp (id R A) = f := ext fun _x => rfl

@[simp]
theorem id_comp (f : A →A[R] B) : (id R B).comp f = f := ext fun _x => rfl

theorem comp_assoc {D : Type*} [Semiring D] [Algebra R D] [TopologicalSpace D] (h : C →A[R] D)
    (g : B →A[R] C) (f : A →A[R] B) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

instance instMul : Mul (A →A[R] A) := ⟨comp⟩

theorem mul_def (f g : A →A[R] A) : f * g = f.comp g := rfl

@[simp]
theorem coe_mul (f g : A →A[R] A) : ⇑(f * g) = f ∘ g := rfl

theorem mul_apply (f g : A →A[R] A) (x : A) : (f * g) x = f (g x) := rfl

instance monoidWithZero : Monoid (A →A[R] A) where
  mul_one _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_assoc _ _ _ := ext fun _ => rfl

theorem coe_pow (f : A →A[R] A) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

/-- `ContinuousAlgHom.toAlgHom` as a `RingHom`. -/
@[simps]
def toAlgHomMonoidHom : (A →A[R] A) →* A →ₐ[R] A where
  toFun        := toAlgHom
  map_one'     := rfl
  map_mul' _ _ := rfl

end comp

section prod

variable {R} {A}
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

instance completeSpace_eqLocus {D : Type*} [UniformSpace D] [CompleteSpace D]
    [Semiring D] [Algebra R D] [T2Space B]
    [FunLike F D B] [ContinuousAlgHomClass F R D B]
    (f g : F) : CompleteSpace (LinearMap.eqLocus f g) :=
  IsClosed.completeSpace_coe <| isClosed_eq (map_continuous f) (map_continuous g)

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
theorem fst_prod_snd  : (fst R A B).prod (snd R A B) = id R (A × B) :=
  ext fun ⟨_x, _y⟩ => rfl

@[simp]
theorem fst_comp_prod (f : A →A[R] B) (g : A →A[R] C) :
    (fst R B C).comp (f.prod g) = f :=
  ext fun _x => rfl

@[simp]
theorem snd_comp_prod  (f : A →A[R] B) (g : A →A[R] C) :
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

@[simp] -- @[norm_cast] -- Porting note: A theorem with this can't have a rhs starting with `↑`.
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

end TopologicalAlgebra
