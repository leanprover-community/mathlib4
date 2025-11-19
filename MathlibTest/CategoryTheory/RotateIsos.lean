import Mathlib.Tactic.CategoryTheory.RotateIsos.Core

set_option linter.unusedTactic false
set_option linter.unusedVariables false

open CategoryTheory
variable {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]

-- tesing the tactic on compositions of isomorphisms

example {a₁ a₂ a₃ a₄ a₅ : A} {f f' : a₁ ≅ a₂} {g g': a₂ ≅ a₃} {h h': a₃ ≅ a₄} {i i': a₄ ≅ a₅}
    (hyp : f ≪≫ g ≪≫ h ≪≫ i = f' ≪≫ (g' ≪≫ h') ≪≫ i') :
    h ≪≫ i = g.symm ≪≫ f.symm ≪≫ f' ≪≫ g' ≪≫ h' ≪≫ i' := rotate_isos% 2 0 hyp

-- tesing the tactic on compositions of isomorphisms

example {a₁ a₂ a₃ a₄ a₅ : A} {f f' : a₁ ≅ a₂} {g g': a₂ ≅ a₃} {h h': a₃ ≅ a₄} {i i': a₄ ≅ a₅}
    (hyp : f ≪≫ g ≪≫ h ≪≫ i = f' ≪≫ (g' ≪≫ h') ≪≫ i') :
    f'.symm ≪≫ f ≪≫ g = g' ≪≫ (h' ≪≫ i') ≪≫ i.symm ≪≫ h.symm := by
  rotate_isos 0 2
  exact rotate_isos% ← 0 1 hyp

-- testing at syntax for the tactic

example {a₁ a₂ a₃ a₄ a₅ : A} {f : a₁ ≅ a₂} {g g': a₂ ≅ a₃} {h h': a₃ ≅ a₄} {i i': a₄ ≅ a₅}
    (hyp : ∀ {f' : a₁ ≅ a₂}, f ≪≫ g ≪≫ h ≪≫ i = f' ≪≫ g' ≪≫ h' ≪≫ i') :
    ∀ {f' : a₁ ≅ a₂}, f'.symm ≪≫ f ≪≫ g = g' ≪≫ h' ≪≫ i' ≪≫ i.symm ≪≫ h.symm := by
  rotate_isos ← 2 1 at hyp
  exact hyp

-- tesing the tactic for terms under a forall, and checks that binder infos are preserved.

/--
info: ∀ {f' : a₁ ≅ a₂} (f : a₁ ≅ a₂) ⦃g' : a₂ ≅ a₃⦄, g ≪≫ h ≪≫ i ≪≫ i'.symm ≪≫ h'.symm = f.symm ≪≫ f' ≪≫ g'
-/
#guard_msgs in
example {a₁ a₂ a₃ a₄ a₅ : A} {g : a₂ ≅ a₃} {h h': a₃ ≅ a₄} {i i': a₄ ≅ a₅}
    (hyp : ∀ {f' : a₁ ≅ a₂} (f : a₁ ≅ a₂) ⦃g' : a₂ ≅ a₃⦄,
      f ≪≫ g ≪≫ h ≪≫ i = f' ≪≫ (g' ≪≫ h') ≪≫ i') :
    ∀ {f' : a₁ ≅ a₂} (f : a₁ ≅ a₂) ⦃g' : a₂ ≅ a₃⦄,
      f'.symm ≪≫ f ≪≫ g = g' ≪≫ (h' ≪≫ i') ≪≫ i.symm ≪≫ h.symm := by
  type_check rotate_isos% 1 2 @hyp
  rotate_isos 1 2 using @hyp

example (a b c d e : A) (g : b ≅ c) (h : d ≅ c) (i : d ⟶ e) (k : a ⟶ e)
    (hyp : ∀ (f : a ≅ b), f.hom ≫ g.hom ≫ h.inv ≫ i = k) :
    ∀ (f : a ≅ b), i = h.hom ≫ g.inv ≫ f.inv ≫ k := by
  rotate_isos ← 0 3 using hyp

-- testing the tactic with the "using rfl" syntax, as well as for terms under multiple applications
-- of a functor

example {x y : A} (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (I : D ⥤ E) (f : x ≅ y) :
    I.map (H.map (G.map (F.map (f.hom)))) ≫ I.map (H.map (G.map (F.map (f.inv)))) = 𝟙 _ := by
  rotate_isos 1 0 using rfl

-- Test the tactic for mixed type of morphisms

/--
info: 𝟙 (I.obj (H.obj (G.obj t))) =
  I.map (H.map (G.map (inv g))) ≫
    I.map (H.map (G.map (α.inv.app z))) ≫
      I.map (H.map (G.map (F.map (inv f')))) ≫ I.map (H.map (G.map (F.map f.inv))) ≫ h
-/
#guard_msgs in
example {x y z : A} {t : B} (F F': A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (I : D ⥤ E)
    (f : x ≅ y) (f' : y ⟶ z) [IsIso f'] (α : F ≅ F') (g : F'.obj z ⟶ t)  [IsIso g]
    (h : I.obj (H.obj (G.obj (F.obj x))) ⟶ I.obj (H.obj (G.obj t)))
    (hyp : I.map (H.map (G.map (F.map (f.hom)))) ≫ I.map (H.map (G.map (F.map (f')))) ≫
      I.map (H.map (G.map (α.hom.app z))) ≫ I.map (H.map (G.map g)) = h) : x = x := by
  type_check rotate_isos% 4 0 hyp
  rfl

/--
error: Not enough cancelable morphisms in one of the sides of the provided equality.
-/
#guard_msgs in
example {a₁ a₂ a₃ a₄ a₅ : A} {f : a₁ ⟶ a₂} {g g' : a₂ ⟶ a₃} {h h': a₃ ⟶ a₄} {i i': a₄ ⟶ a₅}
    [IsIso f] [IsIso g] [IsIso h'] [IsIso i']
    (hyp : ∀ {f' : a₁ ⟶ a₂} [IsIso f'],
      f ≫ g ≫ h ≫ i = f' ≫ (g' ≫ h') ≫ i') :
    a₁ = a₁ := by
  haveI := rotate_isos% 2 0 @hyp -- works
  rotate_isos ← 2 0 at hyp -- fails as `g'` is not invertible

/--
error: rotate_isos can only be used on equalities of (iso)morphisms in categories.
-/
#guard_msgs in
example : 0 + 1 = 1 := by
  rotate_isos 1 0

-- tesing the elaborator in rewrites
example {a₁ a₂ a₃ a₄: A} {f f' : a₁ ⟶ a₂} {g g' : a₂ ⟶ a₃} {h h': a₃ ⟶ a₄}
    [IsIso f] [IsIso g] [IsIso h]
    (hyp : f ≫ g ≫ h = f ≫ g' ≫ h') :
    f ≫ g ≫ h' = f ≫ g' ≫ h' ≫ inv h ≫ h' := by
  rw [reassoc_of% rotate_isos% ← 1 0 hyp]

