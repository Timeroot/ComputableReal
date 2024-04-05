import ComputableReal.ComputableReal

namespace Computableℝ

namespace pi

def pi_lb

end pi

def pi : Computableℝ :=
  mk (ComputableℝSeq.mk
  (lb := x.lb.drop start)
  (ub := x.ub.drop start)
  (hlb := fun n ↦ x.hlb (start+n))
  (hub := fun n ↦ x.hub (start+n))
  (heq := Setoid.trans (
      Setoid.trans (x.lb.drop_equiv_self start) x.heq)
      (Setoid.symm (x.ub.drop_equiv_self start))))
end Computableℝ
