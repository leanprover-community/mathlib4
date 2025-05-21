import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# Cartesian Functors

For fibered categories `p : 𝒳 ⥤ 𝒮` and `q : 𝒴 ⥤ 𝒮`, a functor `F : 𝒳 ⥤ 𝒴` is cartesian (also
called fibered) if it satisfies `F ⋙ q = p` and it preserves cartesian morphisms.
We show that these form a category in the obvious manner.

## References
* [T. Streicher, *Fibered Categories à la Jean Bénabou*](https://arxiv.org/abs/math/0206203)

-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory Functor Category IsHomLift

namespace FiberedCategoryTheory
namespace Functor

section
variable
  {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]

class IsCartesianFunctor
  (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) [IsFibered p] [IsFibered q] (F : 𝒳 ⥤ 𝒴) : Prop where
  triangle (p) (q) (F) : F ⋙ q = p := by aesop_cat
  preservesCartesian (p) (q) (F) {a b : 𝒳} (f : a ⟶ b) [IsCartesian p (p.map f) f] :
    IsCartesian q (p.map f) (F.map f) := by aesop_cat

attribute [simp] Functor.IsCartesianFunctor.triangle

end

section
variable
  {𝒮 : Type u₁} {𝒳 : Type u₂}
  [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]
  (p : 𝒳 ⥤ 𝒮) [IsFibered p]

instance id_IsCartesainFunctor : Functor.IsCartesianFunctor p p (𝟭 𝒳) where
end

section
variable
  {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃} {𝒵 : Type u₄}
  [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴] [Category.{v₄} 𝒵]
  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {r : 𝒵 ⥤ 𝒮} [IsFibered p] [IsFibered q] [IsFibered r]
  (F : 𝒳 ⥤ 𝒴) [Fcart : Functor.IsCartesianFunctor p q F]
  (G : 𝒴 ⥤ 𝒵) [Gcart : Functor.IsCartesianFunctor q r G]

def comp_IsCartesainFunctor : Functor.IsCartesianFunctor p r (F ⋙ G) where
  triangle := by
    rw [Functor.assoc,
      Functor.IsCartesianFunctor.triangle q r G,
      Functor.IsCartesianFunctor.triangle p q F]
  preservesCartesian f _ := by
    have := Functor.IsCartesianFunctor.preservesCartesian p q F f
    have : q.IsCartesian (q.map (F.map f)) (F.map f) := by
      rw [← Functor.comp_map]
      rw [← Functor.IsCartesianFunctor.triangle p q F] at this
      exact this
    have := Functor.IsCartesianFunctor.preservesCartesian q r G (F.map f)
    rw [← Functor.comp_map] at this
    rw [← Functor.IsCartesianFunctor.triangle p q F]
    exact this
end

section
variable
  {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]
  (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) [IsFibered p] [IsFibered q]

structure OverFunctor where
  functor : 𝒳 ⥤ 𝒴
  triangle : functor ⋙ q = p := by aesop_cat

attribute [simp] OverFunctor.functor OverFunctor.triangle

-- Christian says this should be OverFunctor.IsCartesian but I can't make this work,
-- as I don't know how to qualify the other IsCartesian
class IsCartesianOverFunctor (F : OverFunctor p q) : Prop where
  preservesCartesian {a b : 𝒳} (f : a ⟶ b) [IsCartesian p (p.map f) f] :
    IsCartesian q (p.map f) (F.functor.map f) := by aesop_cat

structure CartesianFunctor extends OverFunctor p q where
  IsCartesianFunctor : IsCartesianOverFunctor p q toOverFunctor := by infer_instance

instance (F : OverFunctor p q) [IsCartesianFunctor p q F.functor] :
    IsCartesianOverFunctor p q F where
  preservesCartesian f _ := IsCartesianFunctor.preservesCartesian p q F.functor f

instance (F : OverFunctor p q) [IsCartesianOverFunctor p q F] :
    IsCartesianFunctor p q F.functor where
  preservesCartesian f _ := IsCartesianOverFunctor.preservesCartesian (F := F) f

instance (F : CartesianFunctor p q) :
    IsCartesianFunctor p q F.functor where
  preservesCartesian f _ := F.IsCartesianFunctor.preservesCartesian f
end

section
variable
  {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]
  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮}
  (F : OverFunctor p q) (G : OverFunctor p q)

@[ext]
lemma extOverFunctor (p : F.functor = G.functor) : F = G := by cases F; simp_all
end

section
variable
  {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]
  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮}
  (F : CartesianFunctor p q) (G : CartesianFunctor p q)

@[ext]
lemma extCartFunctor (p : F.functor = G.functor) : F = G := by
  cases F; cases G; simp_all; ext; exact p

end

section
variable
  {𝒮 : Type u₁} {𝒳 : Type u₂}
  [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]
  (p : 𝒳 ⥤ 𝒮) [IsFibered p]

def id_OverFunctor : OverFunctor p p where
  functor := 𝟭 𝒳

instance : IsCartesianOverFunctor p p (id_OverFunctor p) where
  preservesCartesian f := by simp [id_OverFunctor]

def id_CartesianFunctor : CartesianFunctor p p where
  __ := id_OverFunctor p
end

section
variable
  {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃} {𝒵 : Type u₄}
  [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴] [Category.{v₄} 𝒵]
  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {r : 𝒵 ⥤ 𝒮} [IsFibered p] [IsFibered q] [IsFibered r]
  (F : CartesianFunctor p q) (G : CartesianFunctor q r)

def comp_OverFunctor : OverFunctor p r where
  functor := F.functor ⋙ G.functor
  triangle := by rw [Functor.assoc, G.triangle, F.triangle]

instance : IsCartesianOverFunctor p r (comp_OverFunctor F G) where
  preservesCartesian f _ := by
    simp [comp_OverFunctor]
    have foo : IsCartesianFunctor q r G.functor := by infer_instance
    have fee :=
      (comp_IsCartesainFunctor (p := p) (Gcart := foo) F.functor G.functor).preservesCartesian f
    exact fee

def comp_CartesianFunctor : CartesianFunctor p r where
  __ := comp_OverFunctor F G

-- we won't need this it seems?
-- lemma foo'' : comp' (id' p) F = F := by
--   ext
--   simp [comp', comp, id', id]; rfl

-- lemma foo' : comp' F (id' q) = F := by
--   ext
--   simp [comp', comp, id', id]; rfl

end

end Functor
end FiberedCategoryTheory
