import ComputableReal.IsComputable
import ComputableReal.SpecialFunctions.Cos
import ComputableReal.SpecialFunctions.Exp
import ComputableReal.SpecialFunctions.Log
import ComputableReal.SpecialFunctions.Pi
import ComputableReal.SpecialFunctions.Sqrt

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Data.Real.GoldenRatio

/-!
Special functions that can be derived from the other ones, e.g. how `Real.arsinh` is
given in terms of `Real.sqrt` and `Real.log`, or how `Real.pow` is given in terms of
`Real.cos`, `Real.log`, and `Real.exp`.
-/

namespace IsComputable

/-- The golden ratio is defined as `((1 + √5) / 2)`, which can be computed given
a `sqrt` implementation. -/
instance instComputableGoldenRatio : IsComputable goldenRatio :=
  inferInstanceAs (IsComputable ((1 + √5) / 2))

/-- The conjugate of the golden ratio is defined as `((1 - √5) / 2)`, which can
be computed given a `sqrt` implementation. -/
instance instComputableGoldenConj : IsComputable goldenConj :=
  inferInstanceAs (IsComputable ((1 - √5) / 2))

/-- `Real.sinh` can be calculated in terms of `Real.exp`. -/
instance instComputableSinh (x : ℝ) [hx : IsComputable x] : IsComputable (Real.sinh x) :=
  lift_eq (Real.sinh_eq x).symm inferInstance

/-- `Real.cosh` can be calculated in terms of `Real.exp`. -/
instance instComputableCosh (x : ℝ) [hx : IsComputable x] : IsComputable (Real.cosh x) :=
  lift_eq (Real.cosh_eq x).symm inferInstance

/-- `Real.tanh` can be calculated in terms of `Real.exp`. -/
instance instComputableTanh (x : ℝ) [hx : IsComputable x] : IsComputable (Real.tanh x) :=
  lift_eq (Real.tanh_eq_sinh_div_cosh x).symm inferInstance

/-- `Real.sin x` can be calculated as `Real.cos x - π/2`. -/
instance instComputableSin (x : ℝ) [hx : IsComputable x] : IsComputable (Real.sin x) :=
  lift_eq (Real.cos_pi_div_two_sub x) inferInstance

/-- `Real.tan x` can be calculated as `Real.sin x / Real.cos x`. -/
instance instComputableTan (x : ℝ) [hx : IsComputable x] : IsComputable (Real.tan x) :=
  lift_eq (Real.tan_eq_sin_div_cos x).symm inferInstance

/-- `Real.cot x` can be calculated as `Real.cos x / Real.sin x`. -/
instance instComputableCot (x : ℝ) [hx : IsComputable x] : IsComputable (Real.cot x) :=
  lift_eq (Real.cot_eq_cos_div_sin x).symm inferInstance

/-- `Real.logb b x` can be calculated as `Real.log x / Real.log b`. -/
instance instComputableLogb (x b : ℝ) [hx : IsComputable x] [hb : IsComputable b] :
    IsComputable (Real.logb b x) :=
  lift_eq (Real.logb.eq_1 b x).symm inferInstance

/-- `Real.arsinh x` can be calculated as `Real.log (x + √(1 + x ^ 2))`. -/
instance instComputableArsinh (x : ℝ) [hx : IsComputable x] :
    IsComputable (Real.arsinh x) :=
  lift_eq (Real.arsinh.eq_1 x).symm inferInstance

/-- The real power function, `Real.rpow` or `x ^ y`, can be calculated using
`if` statements, `Real.exp`, `Real.log`, and `Real.cos`. -/
instance instComputableRpow (x y : ℝ) [hx : IsComputable x] [hy : IsComputable y] :
    IsComputable (x ^ y) :=
  lift_eq (x :=
    --This is the actual definition of real powers. Unfortunately.
    if x = 0 then
      if y = 0 then 1 else 0
    else if x < 0 then
      Real.exp (Real.log x * y) * Real.cos (y * Real.pi)
    else
      Real.exp (Real.log x * y)
  )
  (by
    split_ifs with hx₁ hy₁ hx₂
    · simp [hx₁, hy₁]
    · simp [hx₁, hy₁]
    · rw [Real.rpow_def_of_neg hx₂]
    · have : 0 < x := by linarith +splitNe
      rw [Real.rpow_def_of_pos this]
  )
  --note: using instComputableIte gives a noncomputable def because there isn't enough
  --inlining going on. Switching to Dite makes it one layer shallower, and the current
  --code generator works.
  (instComputableDite _ _ _)

--TODO: negMulLog, posLog, binEntropy, qaryEntropy

--TODO: mulExpNegMulSq

end IsComputable

--Tests + examples
example : Real.sin 3 < 1/7 := by
  native_decide

example : 2/3 ≤ (1 : ℝ).sin.sin.sin := by --0.678
  native_decide

example :
    let diff := √(1 - (Real.cos 7)^2) - Real.sin 7; --exactly 0 by sin²+cos²=1
    -0.00001 < diff ∧ diff < 0.00001 := by
  native_decide

example :
    --cosine has a unique fixed point so this will be close regardless of starting values
    let diff := (1 : ℝ).cos.cos.cos.cos.cos - (2 : ℝ).cos.cos.cos.cos.cos;
    -0.02 < diff ∧ diff < 0.02 := by
  native_decide

--TODO: once when log is implemented, check this runs.
-- example :
--     0.1 < (-2 : ℝ) ^ (-1/3 : ℝ) := by
--   native_decide
