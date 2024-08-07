import Mathlib.Tactic.Tendsto.Multiseries.Trimming

namespace TendstoTactic

abbrev Series := LazyList ℝ

def Series.apply (s : Series) (ms : PreMS) : PreMS :=
  match s with
  | .nil => .nil
  | .cons hd tl => PreMS.cons 1 (PreMS.const hd) (.mk fun () => ms.mul <| tl.get.apply ms)

end TendstoTactic
