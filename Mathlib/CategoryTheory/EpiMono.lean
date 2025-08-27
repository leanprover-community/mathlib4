/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison
-/
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Groupoid

/-!
# Facts about epimorphisms and monomorphisms.

The definitions of `Epi` and `Mono` are in `CategoryTheory.Category`,
since they are used by some lemmas for `Iso`, which is used everywhere.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

instance unop_mono_of_epi {A B : Cᵒᵖ} (f : A ⟶ B) [Epi f] : Mono f.unop :=
  ⟨fun _ _ eq => Quiver.Hom.op_inj ((cancel_epi f).1 (Quiver.Hom.unop_inj eq))⟩

instance unop_epi_of_mono {A B : Cᵒᵖ} (f : A ⟶ B) [Mono f] : Epi f.unop :=
  ⟨fun _ _ eq => Quiver.Hom.op_inj ((cancel_mono f).1 (Quiver.Hom.unop_inj eq))⟩

instance op_mono_of_epi {A B : C} (f : A ⟶ B) [Epi f] : Mono f.op :=
  ⟨fun _ _ eq => Quiver.Hom.unop_inj ((cancel_epi f).1 (Quiver.Hom.op_inj eq))⟩

instance op_epi_of_mono {A B : C} (f : A ⟶ B) [Mono f] : Epi f.op :=
  ⟨fun _ _ eq => Quiver.Hom.unop_inj ((cancel_mono f).1 (Quiver.Hom.op_inj eq))⟩

/-- A split monomorphism is a morphism `f : X ⟶ Y` with a given retraction `retraction f : Y ⟶ X`
such that `f ≫ retraction f = 𝟙 X`.

Every split monomorphism is a monomorphism.
-/
@[ext, aesop apply safe (rule_sets := [CategoryTheory])]
structure SplitMono {X Y : C} (f : X ⟶ Y) where
  /-- The map splitting `f` -/
  retraction : Y ⟶ X
  /-- `f` composed with `retraction` is the identity -/
  id : f ≫ retraction = 𝟙 X := by cat_disch

attribute [reassoc (attr := simp)] SplitMono.id

/-- `IsSplitMono f` is the assertion that `f` admits a retraction -/
class IsSplitMono {X Y : C} (f : X ⟶ Y) : Prop where
  /-- There is a splitting -/
  exists_splitMono : Nonempty (SplitMono f)

/-- A composition of `SplitMono` is a `SplitMono`. -/
@[simps]
def SplitMono.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (smf : SplitMono f) (smg : SplitMono g) :
    SplitMono (f ≫ g) where
  retraction := smg.retraction ≫ smf.retraction

/-- A constructor for `IsSplitMono f` taking a `SplitMono f` as an argument -/
theorem IsSplitMono.mk' {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) : IsSplitMono f :=
  ⟨Nonempty.intro sm⟩

/-- A split epimorphism is a morphism `f : X ⟶ Y` with a given section `section_ f : Y ⟶ X`
such that `section_ f ≫ f = 𝟙 Y`.
(Note that `section` is a reserved keyword, so we append an underscore.)

Every split epimorphism is an epimorphism.
-/
@[ext, aesop apply safe (rule_sets := [CategoryTheory])]
structure SplitEpi {X Y : C} (f : X ⟶ Y) where
  /-- The map splitting `f` -/
  section_ : Y ⟶ X
  /-- `section_` composed with `f` is the identity -/
  id : section_ ≫ f = 𝟙 Y := by cat_disch

attribute [reassoc (attr := simp)] SplitEpi.id

/-- `IsSplitEpi f` is the assertion that `f` admits a section -/
class IsSplitEpi {X Y : C} (f : X ⟶ Y) : Prop where
  /-- There is a splitting -/
  exists_splitEpi : Nonempty (SplitEpi f)

/-- A composition of `SplitEpi` is a split `SplitEpi`. -/
@[simps]
def SplitEpi.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (sef : SplitEpi f) (seg : SplitEpi g) :
    SplitEpi (f ≫ g) where
  section_ := seg.section_ ≫ sef.section_

/-- A constructor for `IsSplitEpi f` taking a `SplitEpi f` as an argument -/
theorem IsSplitEpi.mk' {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : IsSplitEpi f :=
  ⟨Nonempty.intro se⟩

/-- The chosen retraction of a split monomorphism. -/
noncomputable def retraction {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] : Y ⟶ X :=
  hf.exists_splitMono.some.retraction

@[reassoc (attr := simp)]
theorem IsSplitMono.id {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] : f ≫ retraction f = 𝟙 X :=
  hf.exists_splitMono.some.id

/-- The retraction of a split monomorphism has an obvious section. -/
def SplitMono.splitEpi {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) : SplitEpi sm.retraction where
  section_ := f

/-- The retraction of a split monomorphism is itself a split epimorphism. -/
instance retraction_isSplitEpi {X Y : C} (f : X ⟶ Y) [IsSplitMono f] :
    IsSplitEpi (retraction f) :=
  IsSplitEpi.mk' (SplitMono.splitEpi _)

/-- A split mono which is epi is an iso. -/
theorem isIso_of_epi_of_isSplitMono {X Y : C} (f : X ⟶ Y) [IsSplitMono f] [Epi f] : IsIso f :=
  ⟨⟨retraction f, ⟨by simp, by simp [← cancel_epi f]⟩⟩⟩

/-- The chosen section of a split epimorphism.
(Note that `section` is a reserved keyword, so we append an underscore.)
-/
noncomputable def section_ {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : Y ⟶ X :=
  hf.exists_splitEpi.some.section_

@[reassoc (attr := simp)]
theorem IsSplitEpi.id {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : section_ f ≫ f = 𝟙 Y :=
  hf.exists_splitEpi.some.id

/-- The section of a split epimorphism has an obvious retraction. -/
def SplitEpi.splitMono {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : SplitMono se.section_ where
  retraction := f

/-- The section of a split epimorphism is itself a split monomorphism. -/
instance section_isSplitMono {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : IsSplitMono (section_ f) :=
  IsSplitMono.mk' (SplitEpi.splitMono _)

/-- A split epi which is mono is an iso. -/
theorem isIso_of_mono_of_isSplitEpi {X Y : C} (f : X ⟶ Y) [Mono f] [IsSplitEpi f] : IsIso f :=
  ⟨⟨section_ f, ⟨by simp [← cancel_mono f], by simp⟩⟩⟩

/-- Every iso is a split mono. -/
instance (priority := 100) IsSplitMono.of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsSplitMono f :=
  IsSplitMono.mk' { retraction := inv f }

/-- Every iso is a split epi. -/
instance (priority := 100) IsSplitEpi.of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsSplitEpi f :=
  IsSplitEpi.mk' { section_ := inv f }

theorem SplitMono.mono {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) : Mono f :=
  { right_cancellation := fun g h w => by replace w := w =≫ sm.retraction; simpa using w }

/-- Every split mono is a mono. -/
instance (priority := 100) IsSplitMono.mono {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] : Mono f :=
  hf.exists_splitMono.some.mono

theorem SplitEpi.epi {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : Epi f :=
  { left_cancellation := fun g h w => by replace w := se.section_ ≫= w; simpa using w }

/-- Every split epi is an epi. -/
instance (priority := 100) IsSplitEpi.epi {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : Epi f :=
  hf.exists_splitEpi.some.epi

instance {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [hf : IsSplitMono f] [hg : IsSplitMono g] :
    IsSplitMono (f ≫ g) := IsSplitMono.mk' <| hf.exists_splitMono.some.comp hg.exists_splitMono.some

instance {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [hf : IsSplitEpi f] [hg : IsSplitEpi g] :
    IsSplitEpi (f ≫ g) := IsSplitEpi.mk' <| hf.exists_splitEpi.some.comp hg.exists_splitEpi.some

/-- Every split mono whose retraction is mono is an iso. -/
theorem IsIso.of_mono_retraction' {X Y : C} {f : X ⟶ Y} (hf : SplitMono f) [Mono <| hf.retraction] :
    IsIso f :=
  ⟨⟨hf.retraction, ⟨by simp, (cancel_mono_id <| hf.retraction).mp (by simp)⟩⟩⟩

/-- Every split mono whose retraction is mono is an iso. -/
theorem IsIso.of_mono_retraction {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f]
    [hf' : Mono <| retraction f] : IsIso f :=
  @IsIso.of_mono_retraction' _ _ _ _ _ hf.exists_splitMono.some hf'

/-- Every split epi whose section is epi is an iso. -/
theorem IsIso.of_epi_section' {X Y : C} {f : X ⟶ Y} (hf : SplitEpi f) [Epi <| hf.section_] :
    IsIso f :=
  ⟨⟨hf.section_, ⟨(cancel_epi_id <| hf.section_).mp (by simp), by simp⟩⟩⟩

/-- Every split epi whose section is epi is an iso. -/
theorem IsIso.of_epi_section {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] [hf' : Epi <| section_ f] :
    IsIso f :=
  @IsIso.of_epi_section' _ _ _ _ _ hf.exists_splitEpi.some hf'

-- FIXME this has unnecessarily become noncomputable!
/-- A category where every morphism has a `Trunc` retraction is computably a groupoid. -/
noncomputable def Groupoid.ofTruncSplitMono
    (all_split_mono : ∀ {X Y : C} (f : X ⟶ Y), Trunc (IsSplitMono f)) : Groupoid.{v₁} C := by
  apply Groupoid.ofIsIso
  intro X Y f
  have ⟨a,_⟩ := Trunc.exists_rep <| all_split_mono f
  have ⟨b,_⟩ := Trunc.exists_rep <| all_split_mono <| retraction f
  apply IsIso.of_mono_retraction

section

variable (C)

/-- A split mono category is a category in which every monomorphism is split. -/
class SplitMonoCategory : Prop where
  /-- All monos are split -/
  isSplitMono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], IsSplitMono f

/-- A split epi category is a category in which every epimorphism is split. -/
class SplitEpiCategory : Prop where
  /-- All epis are split -/
  isSplitEpi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], IsSplitEpi f

end

/-- In a category in which every monomorphism is split, every monomorphism splits. This is not an
    instance because it would create an instance loop. -/
theorem isSplitMono_of_mono [SplitMonoCategory C] {X Y : C} (f : X ⟶ Y) [Mono f] : IsSplitMono f :=
  SplitMonoCategory.isSplitMono_of_mono _

/-- In a category in which every epimorphism is split, every epimorphism splits. This is not an
    instance because it would create an instance loop. -/
theorem isSplitEpi_of_epi [SplitEpiCategory C] {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f :=
  SplitEpiCategory.isSplitEpi_of_epi _

section

variable {D : Type u₂} [Category.{v₂} D]

/-- Split monomorphisms are also absolute monomorphisms. -/
@[simps]
def SplitMono.map {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) (F : C ⥤ D) : SplitMono (F.map f) where
  retraction := F.map sm.retraction
  id := by rw [← Functor.map_comp, SplitMono.id, Functor.map_id]

/-- Split epimorphisms are also absolute epimorphisms. -/
@[simps]
def SplitEpi.map {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) (F : C ⥤ D) : SplitEpi (F.map f) where
  section_ := F.map se.section_
  id := by rw [← Functor.map_comp, SplitEpi.id, Functor.map_id]

instance {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] (F : C ⥤ D) : IsSplitMono (F.map f) :=
  IsSplitMono.mk' (hf.exists_splitMono.some.map F)

instance {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] (F : C ⥤ D) : IsSplitEpi (F.map f) :=
  IsSplitEpi.mk' (hf.exists_splitEpi.some.map F)

end

section

/-- When `f` is an epimorphism, `f ≫ g` is epic iff `g` is. -/
@[simp]
lemma epi_comp_iff_of_epi {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) :
    Epi (f ≫ g) ↔ Epi g :=
  ⟨fun _ ↦ epi_of_epi f _, fun _ ↦ inferInstance⟩

/-- When `g` is an isomorphism, `f ≫ g` is epic iff `f` is. -/
@[simp]
lemma epi_comp_iff_of_isIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    Epi (f ≫ g) ↔ Epi f := by
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  simpa using (inferInstance : Epi ((f ≫ g) ≫ inv g ))

/-- When `f` is an isomorphism, `f ≫ g` is monic iff `g` is. -/
@[simp]
lemma mono_comp_iff_of_isIso {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) :
    Mono (f ≫ g) ↔ Mono g := by
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  simpa using (inferInstance : Mono (inv f ≫ f ≫ g))

/-- When `g` is a monomorphism, `f ≫ g` is monic iff `f` is. -/
@[simp]
lemma mono_comp_iff_of_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    Mono (f ≫ g) ↔ Mono f :=
  ⟨fun _ ↦ mono_of_mono _ g, fun _ ↦ inferInstance⟩

end

end CategoryTheory
