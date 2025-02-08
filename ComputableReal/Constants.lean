import ComputableReal.IsComputable

example : ((3 : ℝ) + 5) / 100 ≤ (3 : ℚ) * (5+5 - 1) := by
  let _ : IsComputable (((3 : ℝ) + 5) / 100) := inferInstance
  let _ : IsComputable ((3 : ℚ) * (5+5 - 1)) := inferInstance
  native_decide
  sorry

-- namespace pi

-- def pi_lb

-- end pi

-- def pi : Computableℝ :=
--   mk (ComputableℝSeq.mk
--   (lb := x.lb.drop start)
--   (ub := x.ub.drop start)
--   (hlb := fun n ↦ x.hlb (start+n))
--   (hub := fun n ↦ x.hub (start+n))
--   (heq := Setoid.trans (
--       Setoid.trans (x.lb.drop_equiv_self start) x.heq)
--       (Setoid.symm (x.ub.drop_equiv_self start))))
-- end Computableℝ
