import ComputableReal.IsComputable
import ComputableReal.SpecialFunctions.Basic
import ComputableReal.SpecialFunctions.Exp

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ComputableℝSeq

open scoped QInterval

namespace Log



def lb_log (x : ComputableℝSeq) (hpos : 0 < x.val) : CauSeq ℚ abs :=
  --Will implement this by squaring to get successive approximation, then
  --dividing by powers of 2. This is not very efficient, really, and should be
  --redone. Ideally by normalizing until it's in the range [1/2, 2), and then
  --using Taylor series for ln(x). The normalizing could be done by taking square
  -- roots (but then you have intermediate irrational numbers), or by dividing by
  -- powers of e (which, again, means intermediate irrationals), or by dividing by
  -- powers of 2 (which means you need to add a multiple of `ln 2` afterwards, which
  -- is an irrational post-processing step which is annoying to work with).
  ⟨fun n ↦

--This implementation using dropTilSigned is fundamentally kind of broken.
--We need to cache/remember the first value, like we do in `let ub0 := x.ub 0`
-- for safe_inv. This implementation gives incorrect results.
    let xn := x.lb n
    let y := xn ^ (2 ^ n)
    (⌊y.num⌋₊.log2 - Nat.clog 2 ⌈y.den⌉₊ : ℤ) / (2 ^ n)
    ,
    sorry⟩

def ub_log (x : ComputableℝSeq) (hpos : 0 < x.val) : CauSeq ℚ abs :=
  ⟨fun n ↦
    let xn := x.ub n
    let y := xn ^ (2 ^ n)
    (Nat.clog 2 ⌈y.num⌉₊ - ⌊y.den⌋₊.log2 : ℤ) / (2 ^ n),
    sorry⟩

theorem lb_log_correct {x : ComputableℝSeq} (hpos : 0 < x.val) : ∀n,
    lb_log (x.dropTilSigned hpos.ne') ((val_dropTilSigned _).symm ▸ hpos) n ≤ Real.logb 2 x.val := by
  intro n
  dsimp [lb_log]
  set lbn := (x.dropTilSigned _).lb n
  have h₁ : 0 < lbn := by
    sorry--defn of dropTilSigned
  have h₂ : 0 < lbn.num := Rat.num_pos.mpr h₁
  suffices (⌊lbn.num ^ 2 ^ n⌋₊.log2 - Nat.clog 2 ⌈lbn.den ^ 2 ^ n⌉₊ : ℤ) ≤ 2 ^ n * Real.logb 2 x.val by
    sorry
  have h₃ : (lbn.num ^ 2 ^ n).toNat.log2 ≤ 2 ^ n * Real.logb 2 lbn.num := by
    sorry
  have h₄ : 2 ^ n * Real.logb 2 lbn.den ≤ Nat.clog 2 (lbn.den ^ 2 ^ n) := by
    conv_lhs => equals Real.logb 2 (lbn.den ^ 2 ^ n) =>
      rw [Real.logb_pow]
      simp
    sorry
  have h₅ : Real.logb 2 (lbn.num / lbn.den) ≤ Real.logb 2 x.val := by
    norm_cast
    simp only [Rat.divInt_ofNat, Rat.mkRat_num_den', Nat.one_lt_ofNat, Nat.ofNat_pos]
    apply Real.logb_le_logb_of_le one_lt_two (Rat.cast_pos.mpr h₁)
    dsimp [lbn]
    nth_rewrite 2 [← val_dropTilSigned hpos.ne']
    exact hlb _ n
  have h₆ : Real.logb 2 (lbn.num / lbn.den) = Real.logb 2 lbn.num - Real.logb 2 lbn.den := by
    apply Real.logb_div
    · simpa using h₁.ne'
    · simp
  trans 2 ^ n * Real.logb 2 lbn.num - 2 ^ n * Real.logb 2 lbn.den
  · simp only [Nat.floor_int, Nat.ceil_nat, id_eq, Int.cast_sub, Int.cast_natCast]
    linarith
  · simpa [← mul_sub, ← h₆]

theorem ub_log_correct {x : ComputableℝSeq} (hpos : 0 < x.val) : ∀n,
    Real.logb 2 x.val ≤ ub_log (x.dropTilSigned hpos.ne') ((val_dropTilSigned _).symm ▸ hpos) n :=
  sorry

theorem lb_log_converges {x : ComputableℝSeq} (hpos : 0 < x.val) :
    Real.mk (lb_log x hpos) = Real.logb 2 x.val := by
  sorry

theorem ub_log_converges {x : ComputableℝSeq} (hpos : 0 < x.val) :
    Real.mk (ub_log x hpos) = Real.logb 2 x.val := by
  sorry

theorem lb_log_signed_converges {x : ComputableℝSeq} (hpos : 0 < x.val) :
    Real.mk (lb_log (x.dropTilSigned hpos.ne') ((val_dropTilSigned _).symm ▸ hpos)) = Real.logb 2 x.val := by
  simp [lb_log_converges ((val_dropTilSigned _).symm ▸ hpos)]

theorem ub_log_signed_converges {x : ComputableℝSeq} (hpos : 0 < x.val) :
    Real.mk (ub_log (x.dropTilSigned hpos.ne') ((val_dropTilSigned _).symm ▸ hpos)) = Real.logb 2 x.val := by
  simp [ub_log_converges ((val_dropTilSigned _).symm ▸ hpos)]

/-- Natural log of a sequence that's guaranteed to be eventually positive. Compare
  with `ComputableℝSeq.safe_inv` for implementation. -/
def safe_log (x : ComputableℝSeq) (hpos : 0 < x.val) : ComputableℝSeq :=
  let signed := x.dropTilSigned hpos.ne'
  let hpos' := ((val_dropTilSigned _).symm ▸ hpos)
  mk
  (x := Real.logb 2 x.val)
  (lub := fun n ↦ ⟨⟨(lb_log signed hpos') n, (ub_log signed hpos') n⟩,
    Rat.cast_le.mp ((lb_log_correct hpos n).trans (ub_log_correct hpos n))⟩)
  (hcl := (lb_log signed hpos').prop)
  (hcu := (ub_log signed hpos').prop)
  (hlb := lb_log_correct hpos)
  (hub := ub_log_correct hpos)
  (heq := Real.mk_eq.mp ((lb_log_signed_converges hpos).trans (ub_log_signed_converges hpos).symm))

/-- Log base 2 of a computable real. Will terminate if the argument is nonzero, or if it is zero and the
  upper and lower bounds become exactly zero at some point. Similar structure and
  caveats to `ComputableℝSeq.inv` -/
def log2 : ComputableℝSeq → ComputableℝSeq :=
  fun x ↦ match h : x.sign with
  | SignType.pos =>
    safe_log x (x.sign_pos_iff.1 h)
  | SignType.neg =>
    safe_log (-x) (by simpa only [val_neg, Left.neg_pos_iff] using x.sign_neg_iff.1 h)
  | SignType.zero => 0

@[simp]
theorem log_val (x : ComputableℝSeq) : (log2 x).val = Real.logb 2 x.val := by
  rw [log2]
  split
  · rw [safe_log, mk_val_eq_val]
  · rw [safe_log, mk_val_eq_val, val_neg, Real.logb_neg_eq_logb]
  · rename_i h
    rw [x.sign_zero_iff] at h
    simp [h]

#eval! ((log2 (17/2)).lb 10).toDecimal
#eval! ((log2 (17/2)).ub 10).toDecimal

end Log

end ComputableℝSeq

namespace IsComputable

instance instComputableLog2 (x : ℝ) [hx : IsComputable x] : IsComputable (Real.logb 2 x) :=
  lift (Real.logb 2 ·) ComputableℝSeq.Log.log2 ComputableℝSeq.Log.log_val hx

instance instComputableLog (x : ℝ) [hx : IsComputable x] : IsComputable (Real.log x) :=
  lift_eq (show .logb 2 x / .logb 2 (.exp 1) = _ by field_simp [Real.logb]) inferInstance

end IsComputable
