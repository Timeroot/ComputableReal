import Mathlib
import computableR.ComputableRSeq

/- Computableℝ carries around a real value, val:ℝ, and a
  computable sequence `seq`. seq is (essentially) a ComputableℝSeq val. But we
  would like Computableℝ's x and y to be equal iff x.val and y.val are, so we
  use Trunc: all seq's of the right type are equal (and so the corresponding
  structures are). -/
-- structure Computableℝ where
--   val : ℝ
--   seq : Trunc (IsComputable val)

/-- Computable reals, defined as the quotient of ComputableℝSeq sequences -- sequences with
  Cauchy sequences of lower and upper bounds that converge to the same value -- by the equivalence
  relation of havint the same converged value. This is similar to how reals are quotients of Cauchy
  sequence (without any guarantees on lower/upper bounds). -/
def Computableℝ :=
  @Quotient ComputableℝSeq ComputableℝSeq.equiv

namespace Computableℝ

def mk : ComputableℝSeq → Computableℝ :=
  Quotient.mk''

def val : Computableℝ → ℝ := Quot.lift ComputableℝSeq.val (fun _ _ h ↦ h)

@[simp]
theorem val_mk_eq_val : (mk x).val = x.val :=
  rfl

@[simp]
theorem eq_iff_seq_val (x y : ComputableℝSeq) : (mk x).val = (mk y).val ↔ mk x = mk y:=
  ⟨fun h ↦ Quotient.eq.2 h, Quotient.eq.1⟩

@[simp]
theorem eq_iff_eq_val (x y : Computableℝ) : x.val = y.val ↔ x = y :=
  ⟨by
    let ⟨x',hx'⟩ := Quotient.exists_rep x
    let ⟨y',hy'⟩ := Quotient.exists_rep y
    subst hx'
    subst hy'
    exact (eq_iff_seq_val x' y').1,
  congrArg val⟩

def mapℝ (f : ComputableℝSeq → ComputableℝSeq) {f₂ : ℝ → ℝ} (h : ∀x, (f x).val = f₂ x.val) :
    Computableℝ → Computableℝ :=
  Quotient.map f (fun a b h₂ ↦ (h₂ ▸ h a).trans (h b).symm)

def map₂ℝ (f : ComputableℝSeq → ComputableℝSeq → ComputableℝSeq) {f₂ : ℝ → ℝ → ℝ}
    (h : ∀x y, (f x y).val = f₂ x.val y.val) :
    Computableℝ → Computableℝ → Computableℝ :=
  Quotient.map₂ f (fun a b h₂ y z h₃ ↦ (h₂ ▸ h₃ ▸ h a y).trans (h b z).symm)

@[simp]
theorem val_mapℝ_eq_Val : (@mapℝ f f₂ h x).val = f₂ x.val := by
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  subst hx'
  rw [mapℝ, Quotient.map_mk]
  apply h


@[simp]
theorem val_map₂ℝ_eq_Val : (@map₂ℝ f f₂ h x y).val = f₂ x.val y.val := by
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  let ⟨y',hy'⟩ := Quotient.exists_rep y
  subst hx'
  subst hy'
  rw [map₂ℝ, Quotient.map₂_mk]
  apply h

instance instComputableAdd : Add Computableℝ :=
  ⟨map₂ℝ (· + ·) ComputableℝSeq.add_eq_add⟩

instance instComputableMul : Mul Computableℝ :=
  ⟨map₂ℝ (· * ·) ComputableℝSeq.mul_eq_mul⟩

instance instComputableNeg : Neg Computableℝ :=
  ⟨mapℝ (- ·) ComputableℝSeq.neg_eq_neg⟩

instance instComputableSub : Sub Computableℝ :=
  ⟨map₂ℝ (· - ·) ComputableℝSeq.sub_eq_sub⟩

instance instComputableZero : Zero Computableℝ :=
  ⟨mk 0⟩

instance instComputableOne : One Computableℝ :=
  ⟨mk 1⟩

variable (x y : Computableℝ)

@[simp]
theorem add_val : (x + y).val = x.val + y.val :=
  val_map₂ℝ_eq_Val

@[simp]
theorem mul_val : (x * y).val = x.val * y.val :=
  val_map₂ℝ_eq_Val

@[simp]
theorem neg_val : (-x).val = -(x.val) :=
  val_mapℝ_eq_Val

@[simp]
theorem sub_val : (x - y).val = x.val - y.val :=
  val_map₂ℝ_eq_Val

@[simp]
theorem zero_val : (0 : Computableℝ).val = 0 := by
  rw [Zero.toOfNat0, instComputableZero]
  simp only [val_mk_eq_val, ComputableℝSeq.zero_val]

 @[simp]
theorem one_val : (1 : Computableℝ).val = 1 := by
  rw [One.toOfNat1, instComputableOne]
  simp only [val_mk_eq_val, ComputableℝSeq.one_val]

-- /-- Take the inverse of an element, given that it is nonzero. -/
-- partial def inv (hx : x.val ≠ 0) : Computableℝ :=
--   { val := x.val⁻¹, seq := Trunc.map (fun xv ↦ ComputableℝSeq.computableInv xv hx) x.seq }

-- /-- Take the inverse of an element (with an implict hypothesis that it is nonzero.) -/
-- def inv' (x : Computableℝ) [hx : NeZero x] : Computableℝ :=
--   x.inv hx.1

-- theorem inv_mul_self (x : Computableℝ) (hx : x ≠ 0) : x * (x.inv hx)

instance instComputableRing : CommRing Computableℝ := by
  refine' { natCast := fun n => mk n
            intCast := fun z => mk z
            zero := 0
            one := 1
            mul := (· * ·)
            add := (· + ·)
            neg := (- ·)
            sub := (· - ·)
            npow := @npowRec _ ⟨mk (1:ℕ)⟩ ⟨(· * ·)⟩
            nsmul := @nsmulRec _ ⟨mk (0:ℕ)⟩ ⟨(· + ·)⟩
            zsmul := @zsmulRec _ ⟨mk (0:ℕ)⟩ ⟨(· + ·)⟩ ⟨@Neg.neg _ _⟩,
            .. }
  all_goals
    intros
    first
    | rfl
    | rw [← eq_iff_eq_val]
      simp
      try ring_nf!

-- theorem isField : IsField Computableℝ where
--   exists_pair_ne := ⟨0, 1, by
--     rw [ne_eq, eq_iff_Computableℝ, zero_val, one_val]
--     exact zero_ne_one⟩
--   mul_comm := mul_comm
--   mul_inv_cancel {a} ha := ⟨inv a ha, sorry⟩

-- theorem lb_equiv_self (hx : ComputableℝSeq x) : CauSeq.Completion.mk hx.lb = x.cauchy := by
  -- rw [← Quotient.out_equiv_out]
  -- intro ε hε
  -- obtain ⟨i₁, hi₁⟩ := hx.heq (ε/2) (half_pos hε)
  -- obtain ⟨i₂, hi₂⟩ := (Quotient.out x.cauchy).2 (ε/2) (half_pos hε)
  -- let i := max i₁ i₂
  -- use i
  -- intro j hj
  -- replace hi₁ := hi₁ j (le_of_max_le_left hj)
  -- replace hi₂ := hi₂ j (le_of_max_le_right hj)
  -- push_cast
  -- have hs₁ : (↑(Quotient.out (CauSeq.Completion.mk (lb x))) : ℕ → ℚ) j = lb x j := by
  --   suffices ↑(Quotient.out (CauSeq.Completion.mk (lb x))) = ↑(lb x) by
  --     rw
  --   simp
  --   sorry
  -- have hs₂ := hx.hlb j
  -- have hs₃ := hx.hub j
  -- rw [abs_ite_le] at hi₁ hi₂ ⊢
  -- split_ifs at hi₁ hi₂ ⊢
  -- <;> try linarith
  -- simp
  -- sorry

-- theorem lb_eq_self (hx : ComputableℝSeq x) : Real.mk hx.lb = x := by
--   rw [Real.mk, lb_equiv_self]

-- theorem ub_eq_self (hx : ComputableℝSeq x) : Real.mk hx.lb = x :=
  -- sorry

end Computableℝ
