import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Fork

universe u v

open CategoryTheory

variable {C : Type u} [Category.{v, u} C] [Limits.HasTerminal C]

structure StrongSubobjectClassifier (P : MorphismProperty C)
  (h : P ≤ MorphismProperty.monomorphisms C) where
  Ω : C
  map : ⊤_ C ⟶ Ω
  c : ∀ ⦃U X : C⦄ (f : U ⟶ X) [Mono f], X ⟶ Ω
  isPullback : ∀ ⦃U X : C⦄ (f : U ⟶ X) [Mono f],
    CategoryTheory.IsPullback (Limits.terminal.from U) f map (c f)
  isUnique :  ∀ ⦃U X : C⦄ (f : U ⟶ X) [Mono f] (g : X ⟶ Ω),
    CategoryTheory.IsPullback (Limits.terminal.from U) f map g →
    g = (c f)

abbrev SubobjectClassifier (C : Type u) [Category.{v, u} C] [Limits.HasTerminal C] :=
  StrongSubobjectClassifier (MorphismProperty.monomorphisms C) <|
    le_refl (MorphismProperty.monomorphisms C)

class HasStrongSubobjectClassifier (P : MorphismProperty C)
  (h : P ≤ MorphismProperty.monomorphisms C) where
  mk' : Nonempty (StrongSubobjectClassifier P h)

abbrev HasSubobjectClassifier (C : Type u) [Category.{v, u} C] [Limits.HasTerminal C] :=
  HasStrongSubobjectClassifier (MorphismProperty.monomorphisms C) <|
    le_refl (MorphismProperty.monomorphisms C)

noncomputable section

def strongSubobjectClassifier (P : MorphismProperty C)
  (h : P ≤ MorphismProperty.monomorphisms C) [H : HasStrongSubobjectClassifier P h] :=
     Classical.choice <| H.mk'

abbrev subobjectClassifier (C : Type u) [Category.{v, u} C] [Limits.HasTerminal C]
  [HasSubobjectClassifier C] := strongSubobjectClassifier (MorphismProperty.monomorphisms C) <|
    le_refl (MorphismProperty.monomorphisms C)

instance StrongSubobjectClassifier.map_mono {P : MorphismProperty C}
  {h : P ≤ MorphismProperty.monomorphisms C} (S : StrongSubobjectClassifier P h) : Mono S.map :=
    Limits.IsTerminal.mono_from Limits.terminalIsTerminal S.map

namespace SubobjectClassifier

section lemmas

variable {C : Type u} [Category.{v, u} C] [Limits.HasTerminal C] {U X : C} (f : U ⟶ X) [Mono f]
  (s : SubobjectClassifier C)

@[simp]
lemma comp_factor_eq_map :
  f ≫ Limits.terminal.from X ≫ s.map = f ≫ s.c f := by
    letI := eq_whisker (Limits.terminal.comp_from f) s.map
    simp only [Category.assoc] at this
    rw [this]
    exact (s.isPullback f).w

lemma terminal_map_eq_forkι_classifiying
  (c : Limits.Cone (Limits.parallelPair (Limits.terminal.from X ≫ s.map) (s.c f))) :
  (Limits.terminal.from c.pt) ≫ s.map = (Limits.Fork.ι c) ≫ (s.c f) := by
    sorry


def fork := Limits.Fork.ofι f (comp_factor_eq_map f s)

def lift (c : Limits.Cone (Limits.parallelPair (Limits.terminal.from X ≫ s.map) (s.c f))) :
  c.pt ⟶ (fork f s).pt :=
    (IsPullback.isLimit <| s.isPullback f).lift <|
    Limits.PullbackCone.mk (Limits.terminal.from c.pt) (Limits.Fork.ι c) <|
    terminal_map_eq_forkι_classifiying f s c

def aux (c : Limits.Cone (Limits.parallelPair (Limits.terminal.from X ≫ s.map) (s.c f))) :=
  (IsPullback.isLimit <| s.isPullback f).fac <|
    Limits.PullbackCone.mk (Limits.terminal.from c.pt) (Limits.Fork.ι c) <|
    terminal_map_eq_forkι_classifiying f s c

def fac (c : Limits.Cone (Limits.parallelPair (Limits.terminal.from X ≫ s.map) (s.c f)))
  (j : Limits.WalkingParallelPair) : (lift f s c) ≫ (fork f s).π.app j = c.π.app j := by
    letI := (IsPullback.isLimit <| s.isPullback f).fac <|
      Limits.PullbackCone.mk (Limits.terminal.from c.pt) (Limits.Fork.ι c) <|
      terminal_map_eq_forkι_classifiying f s c

    cases j with
    | zero =>
      let h := this Limits.WalkingCospan.left
      simp at h

      sorry
    | one => sorry


def fine :
  Limits.IsLimit (fork f s) where
    lift c := lift f s c
    fac c j := by

      sorry
    uniq := sorry

end lemmas

variable {C : Type u} [Category.{v, u} C] [Limits.HasTerminal C] [HasSubobjectClassifier C]

instance instRegularMono {U X : C} (f : U ⟶ X) [Mono f] : RegularMono f where
  Z := (subobjectClassifier C).Ω
  left := Limits.terminal.from X ≫ (subobjectClassifier C).map
  right := (subobjectClassifier C).c f
  isLimit := fine f <| subobjectClassifier C


instance instRegularMonoCat : RegularMonoCategory C where
  regularMonoOfMono f _ := instRegularMono f


end SubobjectClassifier
