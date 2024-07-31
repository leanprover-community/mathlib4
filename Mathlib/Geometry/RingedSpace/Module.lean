import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Colimits

universe u v w

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat.Presheaf

variable {X : TopCat.{u}} (R : TopCat.Presheaf.{u, u} RingCat X) (M : PresheafOfModules R)

namespace PresheafOfModules

variable {R} in
noncomputable abbrev stalkAddCommGrp (pt : X) : AddCommGrp := TopCat.Presheaf.stalk M.presheaf pt

variable {R M} in
abbrev sectionHSMulSection
    {U V W : (Opens X)ᵒᵖ} (iU : U ⟶ W) (iV : V ⟶ W) (r : R.obj U) (m : M.presheaf.obj V) :
    M.presheaf.obj W := (R.map iU r) • (M.presheaf.map iV m)

namespace sectionHSMulSection

variable {U U' U'' V V' V'' W : (Opens X)ᵒᵖ}
variable (iU : U ⟶ W) (iU' : U' ⟶ W) (iU'' : U'' ⟶ W)
variable (iV : V ⟶ W) (iV' : V' ⟶ W) (iV'' : V'' ⟶ W)
variable (i₁ : U ⟶ U'') (i₂ : U' ⟶ U'') (j₁ : V ⟶ V'') (j₂ : V' ⟶ V'')
variable (r r' : R.obj U) (m m' : M.presheaf.obj V)

lemma one_smul : sectionHSMulSection iU iV 1 m = M.presheaf.map iV m :=
  show (R.map iU 1) • _ = _ by rw [map_one, MulAction.one_smul]

lemma mul_smul :
    sectionHSMulSection iU iV (r * r') m =
    sectionHSMulSection iU (𝟙 W) r (sectionHSMulSection iU iV r' m) := by
  delta sectionHSMulSection
  rw [map_mul, MulAction.mul_smul, M.presheaf.map_id]
  rfl

lemma mul_smul' (j : W ⟶ W) (r : R.obj U) (r' : R.obj U') :
    sectionHSMulSection iU'' iV (R.map i₁ r * R.map i₂ r') m =
    sectionHSMulSection iU j r (sectionHSMulSection iU' iV r' m) := by
  delta sectionHSMulSection
  rw [map_mul, MulAction.mul_smul]
  erw [M.presheaf.map_id, id_apply]
  rw [← comp_apply, ← comp_apply, ← R.map_comp, ← R.map_comp]
  rfl

lemma smul_zero : sectionHSMulSection iU iV r (0 : M.presheaf.obj V) = 0 :=
  show (R.map iU r) • _ = _ by rw [map_zero, DistribMulAction.smul_zero]

lemma smul_add :
    sectionHSMulSection iU iV r (m + m') =
    sectionHSMulSection iU iV r m + sectionHSMulSection iU iV r m' := by
  delta sectionHSMulSection
  rw [map_add, DistribMulAction.smul_add]

lemma smul_add' (m : M.presheaf.obj V) (m' : M.presheaf.obj V') :
    sectionHSMulSection iU iV'' r (M.presheaf.map j₁ m + M.presheaf.map j₂ m') =
    sectionHSMulSection iU iV r m + sectionHSMulSection iU iV' r m' := by
  delta sectionHSMulSection
  rw [map_add]
  erw [← comp_apply, ← comp_apply]
  rw [← Functor.map_comp, ← Functor.map_comp, ← DistribMulAction.smul_add]
  rfl

lemma add_smul :
    sectionHSMulSection iU iV (r + r') m =
    sectionHSMulSection iU iV r m + sectionHSMulSection iU iV r' m := by
  delta sectionHSMulSection
  rw [map_add, Module.add_smul]

lemma add_smul' (r : R.obj U) (r' : R.obj U') :
    sectionHSMulSection iU'' iV (R.map i₁ r + R.map i₂ r') m =
    sectionHSMulSection iU iV r m + sectionHSMulSection iU' iV r' m := by
  delta sectionHSMulSection
  rw [map_add, Module.add_smul]
  rw [← comp_apply, ← comp_apply, ← R.map_comp, ← R.map_comp]
  rfl

lemma zero_smul : sectionHSMulSection iU iV 0 m = 0 :=
  show (R.map iU 0) • _ = _ by rw [map_zero, Module.zero_smul]

lemma respect_germ {U U' V V' W W' : (Opens X)ᵒᵖ} (pt : X)
    (iU : U ⟶ W) (iU' : U' ⟶ W') (iV : V ⟶ W) (iV' : V' ⟶ W')
    (mem : pt ∈ W.unop) (mem' : pt ∈ W'.unop)
    (r : R.obj U) (r' : R.obj U')
    (hrr' : TopCat.Presheaf.germ R ⟨pt, leOfHom iU.unop mem⟩ r =
      R.germ ⟨pt, leOfHom iU'.unop mem'⟩ r')
    (m : M.presheaf.obj V) (m' : M.presheaf.obj V')
    (hmm' : TopCat.Presheaf.germ M.presheaf ⟨pt, leOfHom iV.unop mem⟩ m =
      TopCat.Presheaf.germ M.presheaf ⟨pt, leOfHom iV'.unop mem'⟩ m') :
    TopCat.Presheaf.germ M.presheaf ⟨pt, mem⟩ (sectionHSMulSection iU iV r m) =
    TopCat.Presheaf.germ M.presheaf ⟨pt, mem'⟩ (sectionHSMulSection iU' iV' r' m') := by
  delta sectionHSMulSection
  obtain ⟨O, mem_O, iO₁, iO₂, eq⟩ := TopCat.Presheaf.germ_eq (h := hrr')
  obtain ⟨O', mem_O', iO₁', iO₂', eq'⟩ := TopCat.Presheaf.germ_eq (h := hmm')
  fapply TopCat.Presheaf.germ_ext (W := O ⊓ O' ⊓ W.unop ⊓ W'.unop)
    (hxW := ⟨⟨⟨mem_O, mem_O'⟩, mem⟩, mem'⟩)
  · refine homOfLE fun _ h => h.1.2
  · refine homOfLE $ by aesop
  erw [M.map_smul, M.map_smul]
  rw [← comp_apply, ← comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  erw [← comp_apply, ← comp_apply]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  · convert congr(R.map _ $eq) using 1
    pick_goal 3
    · exact op $ homOfLE fun _ h => h.1.1.1
    · rw [← comp_apply, ← Functor.map_comp]; rfl
    · rw [← comp_apply, ← Functor.map_comp]; rfl
  · convert congr(M.presheaf.map _ $eq') using 1
    pick_goal 3
    · exact op $ homOfLE fun _ h => h.1.1.2
    · erw [← comp_apply, ← Functor.map_comp]; rfl
    · erw [← comp_apply, ← Functor.map_comp]; rfl

lemma respect_germ' {U U' V V' W W' : (Opens X)} (pt : X)
    (iU : W ⟶ U) (iU' : W' ⟶ U') (iV : W ⟶ V) (iV' : W' ⟶ V')
    (mem : pt ∈ W) (mem' : pt ∈ W')
    (r : R.obj $ op U) (r' : R.obj $ op U')
    (hrr' : TopCat.Presheaf.germ R ⟨pt, leOfHom iU mem⟩ r = R.germ ⟨pt, leOfHom iU' mem'⟩ r')
    (m : M.presheaf.obj $ op V) (m' : M.presheaf.obj $ op V')
    (hmm' : TopCat.Presheaf.germ M.presheaf ⟨pt, leOfHom iV mem⟩ m =
      TopCat.Presheaf.germ M.presheaf ⟨pt, leOfHom iV' mem'⟩ m') :
    TopCat.Presheaf.germ M.presheaf ⟨pt, mem⟩ (sectionHSMulSection (op iU) (op iV) r m) =
    TopCat.Presheaf.germ M.presheaf ⟨pt, mem'⟩ (sectionHSMulSection (op iU') (op iV') r' m') :=
  respect_germ R M pt (op iU) (op iU') (op iV) (op iV') mem mem' r r' hrr' m m' hmm'

end sectionHSMulSection

variable {R M} in
noncomputable def sectionSMulStalk {pt : X} {U : (OpenNhds pt)}
    (r : R.obj $ op $ U.1) (m : M.stalkAddCommGrp pt) :
    M.stalkAddCommGrp pt :=
  TopCat.Presheaf.germ M.presheaf
    (U := U.1 ⊓ TopCat.Presheaf.openOfStalk (F := M.presheaf) m)
    ⟨pt, ⟨U.2, TopCat.Presheaf.mem_openOfStalk _⟩⟩
    (sectionHSMulSection (op $ homOfLE fun _ h => by exact h.1)
      (op $ homOfLE fun _ h => by exact h.2)
      r (TopCat.Presheaf.sectionOfStalk (F := M.presheaf) m))

namespace sectionSMulStalk

variable {pt : X} {U : (OpenNhds pt)} (r r' : R.obj $ op $ U.1) (m m' : M.stalkAddCommGrp pt)

lemma smul_germ {V : Opens X} (mem_V : pt ∈ V) (s : M.presheaf.obj $ op $ V) :
    sectionSMulStalk r (TopCat.Presheaf.germ M.presheaf ⟨pt, mem_V⟩ s) =
    TopCat.Presheaf.germ M.presheaf (U := U.1 ⊓ V) ⟨pt, ⟨U.2, mem_V⟩⟩
      (sectionHSMulSection (op $ homOfLE $ by aesop) (op $ homOfLE $ by aesop) r s) := by
  delta sectionSMulStalk
  apply sectionHSMulSection.respect_germ'
  · rfl
  · erw [TopCat.Presheaf.germ_sectionOfStalk]

lemma one_smul : sectionSMulStalk (U := U) 1 m = m := by
  rw [← TopCat.Presheaf.germ_sectionOfStalk (F := M.presheaf) m]
  erw [smul_germ]
  rw [sectionHSMulSection.one_smul]
  erw [TopCat.Presheaf.germ_res_apply]

lemma mul_smul :
    sectionSMulStalk (U := U) (r * r') m =
    sectionSMulStalk (U := U) r (sectionSMulStalk (U := U) r' m) := by
  rw [← TopCat.Presheaf.germ_sectionOfStalk (F := M.presheaf) m]
  erw [smul_germ, smul_germ]
  rw [sectionHSMulSection.mul_smul]
  apply sectionHSMulSection.respect_germ'
  · rfl
  · erw [TopCat.Presheaf.germ_sectionOfStalk]

lemma smul_zero : sectionSMulStalk (M := M) (U := U) r 0 = 0 := by
  rw [show (0 : M.stalkAddCommGrp pt) = TopCat.Presheaf.germ (F := M.presheaf) ⟨pt, U.2⟩ 0 by
    rw [map_zero]]
  erw [smul_germ]
  rw [sectionHSMulSection.smul_zero, map_zero, map_zero]

lemma smul_add :
    sectionSMulStalk r (m + m') =
    sectionSMulStalk r m + sectionSMulStalk r m' := by
  have eq1 : m + m' =
    germ (F := M.presheaf) (U := openOfStalk (F := M.presheaf) m ⊓ openOfStalk (F := M.presheaf) m')
      ⟨pt, ⟨mem_openOfStalk _, mem_openOfStalk _⟩⟩
      (M.presheaf.map (op $ homOfLE $ by aesop) (sectionOfStalk (F := M.presheaf) m) +
        M.presheaf.map (op $ homOfLE $ by aesop) (sectionOfStalk (F := M.presheaf) m')) := by
    rw [map_add]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    rw [TopCat.Presheaf.germ_sectionOfStalk, TopCat.Presheaf.germ_sectionOfStalk]

  have eq2 : m = germ (F := M.presheaf) (U := openOfStalk (F := M.presheaf) m ⊓ openOfStalk (F := M.presheaf) m')
      ⟨pt, ⟨mem_openOfStalk _, mem_openOfStalk _⟩⟩
      (M.presheaf.map (op $ homOfLE $ by aesop) (sectionOfStalk (F := M.presheaf) m)) := by
    erw [TopCat.Presheaf.germ_res_apply]
    rw [TopCat.Presheaf.germ_sectionOfStalk]

  have eq3 : m' = germ (F := M.presheaf) (U := openOfStalk (F := M.presheaf) m ⊓ openOfStalk (F := M.presheaf) m')
      ⟨pt, ⟨mem_openOfStalk _, mem_openOfStalk _⟩⟩
      (M.presheaf.map (op $ homOfLE $ by aesop) (sectionOfStalk (F := M.presheaf) m')) := by
    erw [TopCat.Presheaf.germ_res_apply]
    rw [TopCat.Presheaf.germ_sectionOfStalk]

  rw [eq1, smul_germ]
  conv_rhs => rw [eq2, smul_germ]
  conv_rhs => rhs; rw [eq3, smul_germ]
  conv_rhs => erw [← map_add]; rw [← sectionHSMulSection.smul_add]

lemma add_smul :
    sectionSMulStalk (r + r') m =
    sectionSMulStalk r m + sectionSMulStalk r' m := by
  rw [← TopCat.Presheaf.germ_sectionOfStalk (F := M.presheaf) m]
  erw [smul_germ, smul_germ, smul_germ]
  rw [sectionHSMulSection.add_smul, map_add]

lemma zero_smul : sectionSMulStalk (U := U) 0 m = 0 := by
  rw [← TopCat.Presheaf.germ_sectionOfStalk (F := M.presheaf) m]
  erw [smul_germ]
  rw [sectionHSMulSection.zero_smul, map_zero]


end sectionSMulStalk

noncomputable instance {pt : X} (U : (OpenNhds pt)) :
    Module (R.obj $ op $ OpenNhds.inclusion _ |>.obj U) (M.stalkAddCommGrp pt) where
  smul := sectionSMulStalk
  one_smul := sectionSMulStalk.one_smul _ _
  mul_smul := sectionSMulStalk.mul_smul _ _
  smul_zero := sectionSMulStalk.smul_zero _ _
  smul_add := sectionSMulStalk.smul_add _ _
  add_smul := sectionSMulStalk.add_smul _ _
  zero_smul := sectionSMulStalk.zero_smul _ _

variable {R M} in
noncomputable def stalkSMulStalk  {pt : X}
    (r : R.stalk pt) (m : M.stalkAddCommGrp pt) :
    M.stalkAddCommGrp pt :=
  sectionSMulStalk (U := ⟨R.openOfStalk r, mem_openOfStalk _⟩) (R.sectionOfStalk r) m

namespace stalkSMulStalk

variable {pt : X} (r r' : R.stalk pt) (m m' : M.stalkAddCommGrp pt)

lemma germ_smul {V : Opens X} (mem_V : pt ∈ V) (s : R.obj $ op V) :
    stalkSMulStalk (R.germ ⟨pt, mem_V⟩ s) m =
    sectionSMulStalk (U := ⟨V, mem_V⟩) s m := by
  delta stalkSMulStalk
  rw [← TopCat.Presheaf.germ_sectionOfStalk (F := M.presheaf) m]

  erw [sectionSMulStalk.smul_germ, sectionSMulStalk.smul_germ]
  apply sectionHSMulSection.respect_germ'
  · erw [TopCat.Presheaf.germ_sectionOfStalk]
  · rfl

-- lemma germ_smul_germ {V V' : Opens X} (mem_V : pt ∈ V) (mem_V' : pt ∈ V')
--     (s : R.obj $ op V) (t : M.presheaf.obj $ op V') :
--     stalkSMulStalk (R.germ ⟨pt, mem_V⟩ s) (TopCat.Presheaf.germ M.presheaf ⟨pt, mem_V'⟩ t) =
--     TopCat.Presheaf.germ M.presheaf (U := V ⊓ V') ⟨pt, ⟨mem_V, mem_V'⟩⟩
--       (sectionHSMulSection (op $ homOfLE $ by aesop) (op $ homOfLE $ by aesop)
--         s t) := by
--   delta stalkSMulStalk
--   rw [sectionSMulStalk.smul_germ]
--   apply sectionHSMulSection.respect_germ'
--   · erw [TopCat.Presheaf.germ_sectionOfStalk]
--   · rfl

lemma one_smul : stalkSMulStalk 1 m = m := by
  rw [show (1 : R.stalk pt) = R.germ (U := ⊤) ⟨pt, ⟨⟩⟩ 1 by rw [map_one]]
  rw [germ_smul, sectionSMulStalk.one_smul]

lemma mul_smul : stalkSMulStalk (r * r') m = stalkSMulStalk r (stalkSMulStalk r' m) := by
  have eq1 : r * r' =
    R.germ (U := openOfStalk r ⊓ openOfStalk r')
      ⟨pt, ⟨mem_openOfStalk _, mem_openOfStalk _⟩⟩
      (R.map (op $ homOfLE $ by aesop) (sectionOfStalk r) *
        R.map (op $ homOfLE $ by aesop) (sectionOfStalk r')) := by
    rw [map_mul]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    rw [TopCat.Presheaf.germ_sectionOfStalk, TopCat.Presheaf.germ_sectionOfStalk]

  have eq2 : r = R.germ (U := openOfStalk r ⊓ openOfStalk r')
      ⟨pt, ⟨mem_openOfStalk _, mem_openOfStalk _⟩⟩
      (R.map (op $ homOfLE $ by aesop) (sectionOfStalk r)) := by
    erw [TopCat.Presheaf.germ_res_apply]
    rw [TopCat.Presheaf.germ_sectionOfStalk]

  have eq3 : r' = R.germ (U := openOfStalk r ⊓ openOfStalk r')
      ⟨pt, ⟨mem_openOfStalk _, mem_openOfStalk _⟩⟩
      (R.map (op $ homOfLE $ by aesop) (sectionOfStalk r')) := by
    erw [TopCat.Presheaf.germ_res_apply]
    rw [TopCat.Presheaf.germ_sectionOfStalk]

  rw [eq1, germ_smul, sectionSMulStalk.mul_smul]
  conv_rhs => rw [eq2, germ_smul]
  conv_rhs => rhs; rw [eq3, germ_smul]

lemma smul_zero : stalkSMulStalk (M := M) r 0 = 0 := by
  rw [← TopCat.Presheaf.germ_sectionOfStalk r, germ_smul, sectionSMulStalk.smul_zero]

lemma smul_add : stalkSMulStalk r (m + m') = stalkSMulStalk r m + stalkSMulStalk r m' := by
  rw [← TopCat.Presheaf.germ_sectionOfStalk r, germ_smul, germ_smul, germ_smul,
    sectionSMulStalk.smul_add]

lemma add_smul : stalkSMulStalk (r + r') m = stalkSMulStalk r m + stalkSMulStalk r' m := by
  have eq1 : r + r' =
    R.germ (U := openOfStalk r ⊓ openOfStalk r')
      ⟨pt, ⟨mem_openOfStalk _, mem_openOfStalk _⟩⟩
      (R.map (op $ homOfLE $ by aesop) (sectionOfStalk r) +
        R.map (op $ homOfLE $ by aesop) (sectionOfStalk r')) := by
    rw [map_add]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    rw [TopCat.Presheaf.germ_sectionOfStalk, TopCat.Presheaf.germ_sectionOfStalk]

  have eq2 : r = R.germ (U := openOfStalk r ⊓ openOfStalk r')
      ⟨pt, ⟨mem_openOfStalk _, mem_openOfStalk _⟩⟩
      (R.map (op $ homOfLE $ by aesop) (sectionOfStalk r)) := by
    erw [TopCat.Presheaf.germ_res_apply]
    rw [TopCat.Presheaf.germ_sectionOfStalk]

  have eq3 : r' = R.germ (U := openOfStalk r ⊓ openOfStalk r')
      ⟨pt, ⟨mem_openOfStalk _, mem_openOfStalk _⟩⟩
      (R.map (op $ homOfLE $ by aesop) (sectionOfStalk r')) := by
    erw [TopCat.Presheaf.germ_res_apply]
    rw [TopCat.Presheaf.germ_sectionOfStalk]

  rw [eq1, germ_smul, sectionSMulStalk.add_smul]
  conv_rhs => rw [eq2, germ_smul]
  conv_rhs => rhs; rw [eq3, germ_smul]

lemma zero_smul : stalkSMulStalk 0 m = 0 := by
  rw [show (0 : R.stalk pt) = R.germ (U := ⊤) ⟨pt, ⟨⟩⟩ 0 by rw [map_zero], germ_smul,
    sectionSMulStalk.zero_smul]

end stalkSMulStalk

noncomputable instance {pt : X} : Module (R.stalk pt) (M.stalkAddCommGrp pt) where
  smul := stalkSMulStalk
  one_smul := stalkSMulStalk.one_smul _ _
  mul_smul := stalkSMulStalk.mul_smul _ _
  smul_zero := stalkSMulStalk.smul_zero _ _
  smul_add := stalkSMulStalk.smul_add _ _
  add_smul := stalkSMulStalk.add_smul _ _
  zero_smul := stalkSMulStalk.zero_smul _ _

end PresheafOfModules
