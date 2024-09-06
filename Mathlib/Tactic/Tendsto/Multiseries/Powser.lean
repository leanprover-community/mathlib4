import Mathlib.Tactic.Tendsto.Multiseries.BasicNew
import Mathlib.Tactic.Tendsto.Multiseries.OperationsNew
import Mathlib.Tactic.Tendsto.Multiseries.TrimmingNew

namespace TendstoTactic

namespace PreMS

abbrev Series := CoList ℝ

namespace Series

-- We use this simplified condition. It implies that the function has radius of converges ≥ 1
def analytic (s : Series) : Prop := s.all fun c => |c| ≤ 1

-- We define it on entire ℝ but it's really a desired sum of series only inside (-1, 1)
noncomputable def toFun {s : Series} (h : analytic s) (x : ℝ) : ℝ :=
  if h : |x| < 1 then
    let approximations : CoList ℝ :=
      s.enum.fold' (0 : ℝ) fun acc (c, n) =>
        acc + x^n * c
    let seq : ℕ → ℝ := fun n ↦ (approximations.get n).get!
    have has_limit : ∃ a, Filter.Tendsto seq Filter.atTop (nhds a) := by
      sorry -- 3rd task
    has_limit.choose
  else
    0

def mulConst {basis : Basis} (ms : PreMS basis) (c : ℝ) : PreMS basis :=
  match basis with
  | [] => ms * c
  | _ :: _ =>
    CoList.map (fun (deg, coef) => (deg, mulConst coef c)) ms

noncomputable def apply (s : Series) {basis : Basis}
    (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => default
  | basis_hd :: basis_tl =>
    let T := PreMS (basis_hd :: basis_tl) × Series
    let g : T → CoList.OutType (PreMS (basis_hd :: basis_tl)) T := fun (cur_power, cur_s) =>
      cur_s.casesOn'
      (nil := .nil)
      (cons := fun c cs =>
        .cons (mulConst cur_power c) (cur_power.mul ms, cs)
      )
    let series := CoList.corec g (PreMS.one _, s) -- [c0, c1 * ms, c2, * ms^2, ...]
    merge1 series

theorem apply_spec {s : Series} (h_analytic : s.analytic) {basis : Basis} {ms : PreMS basis}
    (h_neg : ms.hasNegativeLeading) (h_trimmed : ms.isTrimmed) {F : ℝ → ℝ}
    (h_approx : ms.isApproximation F basis) : (apply s ms).isApproximation ((s.toFun h_analytic) ∘ F) basis := by
  sorry -- 4th task

end Series



-- 1/(1-t), i.e. ones
def Series.inv' : Series :=
  let g : Unit → CoList.OutType ℝ Unit := fun () => .cons 1 ()
  CoList.corec g ()

-- 1/(1+t), i.e. [1, -1, 1, -1, ...]
def Series.inv : Series :=
  let g : Bool → CoList.OutType ℝ Bool := fun b => .cons (b.casesOn 1 (-1)) !b
  CoList.corec g false

theorem inv_analytic : Series.inv.analytic := by
  simp [Series.analytic]
  sorry -- second task

example (x : ℝ) (hx : |x| < 1) : Series.inv.toFun inv_analytic x = 1/(1 + x) := by
  sorry -- first task

#eval Series.inv.take 10

noncomputable def inv {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => ms⁻¹
  | basis_hd :: basis_tl =>
    ms.casesOn'
    (nil := PreMS.zero _)
    (cons := fun (deg, coef) tl =>
      let leadingInv : PreMS (basis_hd :: basis_tl) := .cons (-deg, coef.inv) .nil
      leadingInv.mul <| Series.inv.apply (leadingInv.mul tl)
    )

end PreMS

end TendstoTactic
