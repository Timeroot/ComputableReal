import ComputableReal.ComputableReal

/- Type class stating that `x:ℝ` has a ComputableℝSeq, i.e. that x is a computable number. Like
`Decidable`, it carries data with it - even though (classically) we could prove that ever proposition
is decidable, and every real is computable. -/
class IsComputable (x : ℝ) : Type where
    seq : ComputableℝSeq
    prop : seq.val = x

namespace IsComputable

def lift (fr : ℝ → ℝ) (fs : ComputableℝSeq → ComputableℝSeq)
    (h : ∀ a, (fs a).val = fr a.val) :
    IsComputable x → IsComputable (fr x) :=
  fun ⟨sx, hsx⟩ ↦ ⟨fs sx, hsx ▸ h sx⟩

def lift₂ (fr : ℝ → ℝ → ℝ) (fs : ComputableℝSeq → ComputableℝSeq → ComputableℝSeq)
    (h : ∀a b, (fs a b).val = fr a.val b.val) :
    IsComputable x → IsComputable y → IsComputable (fr x y) :=
  fun ⟨sx, hsx⟩ ⟨sy, hsy⟩ ↦ ⟨fs sx sy, hsx ▸ hsy ▸ h sx sy⟩

instance instComputableNat (n : ℕ) : IsComputable n :=
  ⟨ComputableℝSeq.ofRat n, ComputableℝSeq.val_natCast⟩

instance instComputableInt (z : ℤ) : IsComputable z :=
  ⟨ComputableℝSeq.ofRat z, ComputableℝSeq.val_intCast⟩

instance instComputableRat (q : ℚ) : IsComputable q :=
  ⟨ComputableℝSeq.ofRat q, ComputableℝSeq.val_ratCast⟩

instance instComputableOfNat1 : IsComputable
    (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real inferInstance)) :=
  ⟨1, ComputableℝSeq.val_one⟩

instance instComputableOfNat0 : IsComputable
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real inferInstance)) :=
  ⟨0, ComputableℝSeq.val_zero⟩

instance instComputableOfNatAtLeastTwo : (n : ℕ) → [n.AtLeastTwo] → IsComputable ofNat(n) :=
  fun _ _ ↦ ⟨
    ⟨fun _ ↦ ⟨⟨_, _⟩, rfl.le⟩,
      IsCauSeq.const _, IsCauSeq.const _,
      fun _ ↦ by simpa using ⟨rfl.le, rfl.le⟩,
      by rfl⟩,
    ComputableℝSeq.val_eq_mk_lb _⟩

instance instComputableNeg (x : ℝ) [hx : IsComputable x] : IsComputable (-x) :=
  lift _ (- ·) ComputableℝSeq.val_neg hx

instance instComputableInv (x : ℝ) [hx : IsComputable x] : IsComputable (x⁻¹) :=
  lift _ (·⁻¹) ComputableℝSeq.val_inv hx

instance instComputableAdd [hx : IsComputable x] [hy : IsComputable y] : IsComputable (x + y) :=
  lift₂ _ (· + ·) ComputableℝSeq.val_add hx hy

instance instComputableSub [hx : IsComputable x] [hy : IsComputable y] : IsComputable (x - y) :=
  lift₂ _ (· - ·) ComputableℝSeq.val_sub hx hy

instance instComputableMul [hx : IsComputable x] [hy : IsComputable y] : IsComputable (x * y) :=
  lift₂ _ (· * ·) ComputableℝSeq.val_mul hx hy

instance instComputableDiv [hx : IsComputable x] [hy : IsComputable y] : IsComputable (x / y) :=
  lift₂ _ (· / ·) ComputableℝSeq.val_div hx hy

instance instComputableNatPow [hx : IsComputable x] (n : ℕ) : IsComputable (x ^ n) := by
  /-TODO(mul_assoc)
  Redo this to use native powering on the ComputableℝSeq. This avoids more costly
  (and inaccurate) interval multiplications. That will also turn it into exponentiation
  by squaring.
  -/
  induction n
  · rw [pow_zero]
    infer_instance
  · rw [pow_succ]
    infer_instance

instance instComputableZPow [hx : IsComputable x] (z : ℤ) : IsComputable (x ^ z) := by
  cases z
  · rw [Int.ofNat_eq_coe, zpow_natCast]
    infer_instance
  · simp only [zpow_negSucc]
    infer_instance

instance instComputableNSMul [hx : IsComputable x] (n : ℕ) : IsComputable (n • x) :=
  lift _ (n • ·) (by
    --TODO move to a ComputableℝSeq lemma
    intro a
    induction n
    · simp
    · rename_i ih
      simp [ih, succ_nsmul, add_mul]
    ) hx

instance instComputableZSMul [hx : IsComputable x] (z : ℤ) : IsComputable (z • x) := by
  rw [zsmul_eq_mul]
  infer_instance

instance instComputableQSMul [hx : IsComputable x] (q : ℚ) : IsComputable (q • x) := by
  change IsComputable (_ * _)
  infer_instance

/-- When expressions involve that happen to be `IsComputable`, we can get a decidability
instance by lifting them to a comparison on the `ComputableℝSeq`s, where comparison is
computable. -/
instance instDecidableLE [hx : IsComputable x] [hy : IsComputable y] : Decidable (x ≤ y) :=
  decidable_of_decidable_of_iff (p := Computableℝ.mk hx.seq ≤ Computableℝ.mk hy.seq) (by
    simp only [← Computableℝ.le_iff_le, Computableℝ.val_mk_eq_val, hx.prop, hy.prop]
  )

instance instDecidableEq [hx : IsComputable x] [hy : IsComputable y] : Decidable (x = y) :=
  decidable_of_decidable_of_iff (p := (Computableℝ.mk hx.seq = Computableℝ.mk hy.seq)) (by
    simp only [← Computableℝ.eq_iff_eq_val, Computableℝ.val_mk_eq_val, hx.prop, hy.prop]
  )

instance instDecidableLT [hx : IsComputable x] [hy : IsComputable y] : Decidable (x < y) :=
  decidable_of_decidable_of_iff (p := Computableℝ.mk hx.seq < Computableℝ.mk hy.seq) (by
    simp only [← Computableℝ.lt_iff_lt, Computableℝ.val_mk_eq_val, hx.prop, hy.prop]
  )

example : ((3 : ℝ) + (5 : ℕ)) / 100 < (3 : ℚ) * (5 + (1 / 5)^2 - 1) ∧
    (5:ℕ) = ((1:ℝ) + (2:ℚ)^2) := by
  native_decide

end IsComputable
