import ComputableReal.IsComputable
import ComputableReal.SpecialFunctions.Basic

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ComputableℝSeq

open scoped QInterval

namespace Log

def lb_log (x : ComputableℝSeq) (hpos : 0 < x.val) : CauSeq ℚ abs :=
  --Will implement this by either ... squaring to get successive approximation, then
  --dividing by powers of 2;
  -- or, dividing by powers of 2 to get it in the range [0,2], using Taylor series,
  -- and then adding back in an appropriate constant (this would give log base 2 though).
  ⟨fun n ↦ sorry, sorry⟩

def ub_log (x : ComputableℝSeq) (hpos : 0 < x.val) : CauSeq ℚ abs :=
  ⟨fun n ↦ sorry, sorry⟩

theorem lb_log_correct {x : ComputableℝSeq} (hpos : 0 < x.val) : ∀n,
    lb_log (x.dropTilSigned hpos.ne') ((val_dropTilSigned _).symm ▸ hpos) n ≤ Real.log x.val :=
  sorry

theorem ub_log_correct {x : ComputableℝSeq} (hpos : 0 < x.val) : ∀n,
    Real.log x.val ≤ ub_log (x.dropTilSigned hpos.ne') ((val_dropTilSigned _).symm ▸ hpos) n :=
  sorry

theorem lb_log_converges {x : ComputableℝSeq} (hpos : 0 < x.val) :
    Real.mk (lb_log x hpos) = Real.log x.val := by
  sorry

theorem ub_log_converges {x : ComputableℝSeq} (hpos : 0 < x.val) :
    Real.mk (ub_log x hpos) = Real.log x.val := by
  sorry

theorem lb_log_signed_converges {x : ComputableℝSeq} (hpos : 0 < x.val) :
    Real.mk (lb_log (x.dropTilSigned hpos.ne') ((val_dropTilSigned _).symm ▸ hpos)) = Real.log x.val := by
  simp [lb_log_converges ((val_dropTilSigned _).symm ▸ hpos)]

theorem ub_log_signed_converges {x : ComputableℝSeq} (hpos : 0 < x.val) :
    Real.mk (ub_log (x.dropTilSigned hpos.ne') ((val_dropTilSigned _).symm ▸ hpos)) = Real.log x.val := by
  simp [ub_log_converges ((val_dropTilSigned _).symm ▸ hpos)]

/-- Natural log of a sequence that's guaranteed to be eventually positive. Compare
  with `ComputableℝSeq.safe_inv` for implementation. -/
def safe_log (x : ComputableℝSeq) (hpos : 0 < x.val) : ComputableℝSeq :=
  let signed := x.dropTilSigned hpos.ne'
  let hpos' := ((val_dropTilSigned _).symm ▸ hpos)
  mk
  (x := Real.log x.val)
  (lub := fun n ↦ ⟨⟨(lb_log signed hpos') n, (ub_log signed hpos') n⟩,
    Rat.cast_le.mp ((lb_log_correct hpos n).trans (ub_log_correct hpos n))⟩)
  (hcl := (lb_log signed hpos').prop)
  (hcu := (ub_log signed hpos').prop)
  (hlb := lb_log_correct hpos)
  (hub := ub_log_correct hpos)
  (heq := Real.mk_eq.mp ((lb_log_signed_converges hpos).trans (ub_log_signed_converges hpos).symm))

/-- Natural log of a computable real. Will terminate if the argument is nonzero, or if it is zero and the
  upper and lower bounds become exactly zero at some point. Similar structure and
  caveats to `ComputableℝSeq.inv` -/
def log : ComputableℝSeq → ComputableℝSeq :=
  fun x ↦ match h : x.sign with
  | SignType.pos =>
    safe_log x (x.sign_pos_iff.1 h)
  | SignType.neg =>
    safe_log (-x) (by simpa only [val_neg, Left.neg_pos_iff] using x.sign_neg_iff.1 h)
  | SignType.zero => 0

@[simp]
theorem log_val (x : ComputableℝSeq) : (log x).val = Real.log x.val := by
  rw [log]
  split
  · rw [safe_log, mk_val_eq_val]
  · rw [safe_log, mk_val_eq_val, val_neg, Real.log_neg_eq_log]
  · rename_i h
    rw [x.sign_zero_iff] at h
    simp [h]

end Log

end ComputableℝSeq

namespace IsComputable

instance instComputableLog (x : ℝ) [hx : IsComputable x] : IsComputable (Real.log x) :=
  lift Real.log ComputableℝSeq.Log.log (fun _ ↦ ComputableℝSeq.Log.log_val _) hx

end IsComputable
