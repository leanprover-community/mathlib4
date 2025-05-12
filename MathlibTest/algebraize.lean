import Mathlib.Tactic.Algebraize

set_option linter.unusedVariables false

section example_definitions

/-- Test property for when `RingHom` and `Algebra` properties are definitionally the same,
see e.g. `RingHom.FiniteType` for a concrete example of this. -/
class Algebra.testProperty1 (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Prop where
  out : ∀ x : A, algebraMap A B x = 0

/-- Test property for when `RingHom` and `Algebra` properties are definitionally the same,
see e.g. `RingHom.FiniteType` for a concrete example of this. -/
@[algebraize]
def RingHom.testProperty1 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  @Algebra.testProperty1 A B _ _ f.toAlgebra

/-- Test property for when the `RingHom` property corresponds to a `Module` property (that is
definitionally the same). See e.g. `Module.Finite` for a concrete example of this. -/
class Module.testProperty2 (A M : Type*) [Semiring A] [AddCommMonoid M] [Module A M] : Prop where
  out : ∀ x : A, ∀ M : M, x • M = 0

/-- Test property for when the `RingHom` property corresponds to a `Module` property (that is
definitionally the same). See e.g. `Module.Finite` for a concrete example of this. -/
@[algebraize Module.testProperty2]
def RingHom.testProperty2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  letI : Algebra A B := f.toAlgebra
  Module.testProperty2 A B

/-- Test property for when the `RingHom` property corresponds to a `Algebra` property that is not
definitionally the same, and needs to be created through a lemma. See e.g. `Algebra.IsIntegral` for
an example. -/
class Algebra.testProperty3 (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Prop where
  out : Algebra.testProperty1 A B

/- Test property for when the `RingHom` property corresponds to a `Algebra` property that is not
definitionally the same, and needs to be created through a lemma. See e.g. `Algebra.IsIntegral` for
an example. -/
@[algebraize Algebra.testProperty3.mk]
def RingHom.testProperty3 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  f.testProperty1

/- Test property for when the `RingHom` (and `Algebra`) property have an extra explicit argument,
and hence needs to be created through a lemma. See e.g.
`Algebra.IsStandardSmoothOfRelativeDimension` for an example. -/
class Algebra.testProperty4 (n : ℕ) (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Prop where
  out : ∀ m, n = m

/- Test property for when the `RingHom` (and `Algebra`) property have an extra explicit argument,
and hence needs to be created through a lemma. See e.g.
`Algebra.IsStandardSmoothOfRelativeDimension` for an example. -/
@[algebraize testProperty4.toAlgebra]
def RingHom.testProperty4 (n : ℕ) {A B : Type*} [CommRing A] [CommRing B] (_ : A →+* B) : Prop :=
  ∀ m, n = m

lemma testProperty4.toAlgebra (n : ℕ) {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.testProperty4 n) :
    letI : Algebra A B := f.toAlgebra
    Algebra.testProperty4 n A B :=
      letI : Algebra A B := f.toAlgebra
      { out := hf }

end example_definitions

set_option tactic.hygienic false

/-- Synthesize algebra instance from ring hom. -/
example (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) : True := by
  fail_if_success -- Check that this instance is not available by default
    have h : Algebra A B := inferInstance
  algebraize [f]
  guard_hyp algInst := f.toAlgebra
  trivial

/-- Synthesize algebra instance from ring hom defined using a `let` statement. -/
example (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) : True := by
  let f' : A →+* B := f
  fail_if_success -- Check that this instance is not available by default
    have h : Algebra A B := inferInstance
  algebraize [f']
  guard_hyp algInst :=ₛ f'.toAlgebra
  trivial

/-- Synthesize algebra instance from a composition -/
example (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    True := by
  fail_if_success -- Check that this instance is not available by default
    have h : Algebra A C := inferInstance
  algebraize [g.comp f]
  guard_hyp algInst := (g.comp f).toAlgebra
  trivial

/-- Synthesize algebra instance and scalar tower instance from a composition -/
example (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    True := by
  fail_if_success -- Check that this instance is not available by default
    have h : IsScalarTower A B C := inferInstance
  algebraize [f, g, g.comp f]
  guard_hyp scalarTowerInst := IsScalarTower.of_algebraMap_eq' rfl
  trivial

example (A B : Type*) [CommRing A] [CommRing B] (f g : A →+* B) (hf : f.testProperty1)
    (hg : g.testProperty1) : True := by
  algebraize [f]
  guard_hyp algebraizeInst : @Algebra.testProperty1 A B _ _ f.toAlgebra
  fail_if_success
    guard_hyp algebraizeInst_1
  trivial

example (A B : Type*) [CommRing A] [CommRing B] (f g : A →+* B) (hf : f.testProperty2)
  (hg : g.testProperty2) : True := by
  algebraize [f]
  guard_hyp algebraizeInst : @Module.testProperty2 A B _ _ f.toAlgebra.toModule
  fail_if_success
    guard_hyp algebraizeInst_1
  trivial

-- #print RingHom.testProperty3

example (A B : Type*) [CommRing A] [CommRing B] (f g : A →+* B) (hf : f.testProperty3)
    (hg : g.testProperty3) : True := by
  algebraize [f]
  guard_hyp algebraizeInst : @Algebra.testProperty3 A B _ _ f.toAlgebra
  fail_if_success
    guard_hyp algebraizeInst_1
  trivial

example (n m: ℕ) (A B : Type*) [CommRing A] [CommRing B] (f g : A →+* B) (hf : f.testProperty4 n)
    (hg : g.testProperty4 m): True := by
  algebraize [f]
  guard_hyp algebraizeInst : Algebra.testProperty4 n A B
  fail_if_success
    guard_hyp algebraizeInst_1
  trivial

/-- Synthesize from morphism property of a composition (and check that tower is also synthesized). -/
example (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (hfg : (g.comp f).testProperty1) : True := by
  fail_if_success -- Check that this instance is not available by default
    have h : Algebra.Flat A C := inferInstance
  fail_if_success
    have h : IsScalarTower A B C := inferInstance
  algebraize [f, g, g.comp f]
  guard_hyp algebraizeInst : Algebra.testProperty1 A C
  guard_hyp scalarTowerInst := IsScalarTower.of_algebraMap_eq' rfl
  trivial

section
/- Test that the algebraize tactic also works on non-RingHom types -/

structure Bar (A B : Type*) [CommRing A] [CommRing B] where
  f : A →+* B

@[algebraize testProperty1_ofBar]
def Bar.testProperty1 {A B : Type*} [CommRing A] [CommRing B] (b : Bar A B) : Prop :=
  ∀ z, b.f z = 0

lemma testProperty1_ofBar {A B : Type*} [CommRing A] [CommRing B] (b : Bar A B) (h : b.testProperty1) :
  @Algebra.testProperty1 A B _ _ b.f.toAlgebra := @Algebra.testProperty1.mk A B _ _ b.f.toAlgebra h

@[algebraize testProperty2_ofBar]
def Bar.testProperty2 {A B : Type*} [CommRing A] [CommRing B] (b : Bar A B) : Prop :=
  letI : Algebra A B := b.f.toAlgebra;
  ∀ (r : A) (M : B), r • M = 0

lemma testProperty2_ofBar {A B : Type*} [CommRing A] [CommRing B] (b : Bar A B) (h : b.testProperty2) :
  @Module.testProperty2 A B _ _ b.f.toAlgebra.toModule :=
    @Module.testProperty2.mk A B _ _ b.f.toAlgebra.toModule h

example {A B : Type*} [CommRing A] [CommRing B] (b c: Bar A B) (hb : b.testProperty1)
    (hc : c.testProperty1) : True := by
  algebraize [b.f]
  guard_hyp algebraizeInst : @Algebra.testProperty1 A B _ _ b.f.toAlgebra
  fail_if_success -- make sure that only arguments are used
    guard_hyp algebraizeInst_1 : @Algebra.testProperty1 A B _ _ c.f.toAlgebra
  trivial

example {A B : Type*} [CommRing A] [CommRing B] (b c : Bar A B) (hb : b.testProperty2)
    (hc : c.testProperty2) : True := by
  algebraize [b.f]
  guard_hyp algebraizeInst : @Module.testProperty2 A B _ _ b.f.toAlgebra.toModule
  fail_if_success
    guard_hyp algebraizeInst_1 --: @Module.testProperty2 A B _ _ c.f.toAlgebra.toModule
  trivial

structure Buz (A B : Type*) [CommRing A] [CommRing B] where
  x : (A →+* B) ⊕ (A →+* B)

@[algebraize testProperty1_ofBuz_inl]
def Buz.testProperty1 {A B : Type*} [CommRing A] [CommRing B] (b : Buz A B) :=
  b.x.elim (@Algebra.testProperty1 A B _ _ ·.toAlgebra) (fun _ => False)

lemma testProperty1_ofBuz_inl {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
  Buz.testProperty1 ⟨.inl f⟩ → @Algebra.testProperty1 A B _ _ f.toAlgebra := id

-- check that this also works when the argument *contains* a ringhom
example {A B : Type*} [CommRing A] [CommRing B] (f g: A →+* B)
    (hf : Buz.testProperty1 ⟨.inl f⟩) (hg : Buz.testProperty1 ⟨.inl g⟩): True := by
  algebraize [f]
  guard_hyp algebraizeInst : @Algebra.testProperty1 A B _ _ f.toAlgebra
  fail_if_success
    guard_hyp algebraizeInst_1 --: @Algebra.testProperty1 A B _ _ g.toAlgebra
  trivial

-- check that there is no issue with trying the lemma on a mismatching argument.
example {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
  (hf : Buz.testProperty1 ⟨.inr f⟩) : True := by
  algebraize [f] -- this could error if it tried applying `testProperty1_ofBuz_inl` to `hf`
  fail_if_success
    guard_hyp algebraizeInst
  trivial

end
