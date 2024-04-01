import Mathlib

--silly lemma
theorem abs_ite_le [inst : LinearOrderedAddCommGroup α] (x : α) :
    abs x = if 0 ≤ x then x else -x := by
  split_ifs <;> simp_all
  next h =>
    exact LT.lt.le h

class Computableℝ (x : ℝ) :=
  lb : ℕ → ℚ
  ub : ℕ → ℚ
  hlb : ∀n, lb n ≤ x
  hub : ∀n, ub n ≥ x
  hgap : IsCauSeq (abs : ℚ → ℚ) (ub - lb)

namespace Computableℝ

theorem lb_le_ub (hx : Computableℝ x) : ∀n, hx.lb n ≤ hx.ub n :=
  fun n ↦ Rat.cast_le.mp (le_trans (hx.hlb n) (hx.hub n))

variable (x y : ℝ) (q : ℚ)

instance instComputableRat : Computableℝ q :=
  ⟨fun _ ↦ q, fun _ ↦ q, fun _ ↦ rfl.le, fun _ ↦ rfl.le, IsCauSeq.const (Rat.sub _ _)⟩

instance instComputableInt (n : ℤ): Computableℝ n :=
  instComputableRat n

instance instComputableNat (n : ℕ): Computableℝ n :=
  instComputableRat n

instance instComputableAdd [hx : Computableℝ x] [hy : Computableℝ y] : Computableℝ (x + y) where
  lb n :=  hx.lb n + hy.lb n
  ub n := hx.ub n + hy.ub n
  hlb n := by push_cast; exact add_le_add (hx.hlb n) (hy.hlb n)
  hub n := by push_cast; exact add_le_add (hx.hub n) (hy.hub n)
  hgap := by
    convert (IsCauSeq.add hx.hgap hy.hgap) using 1
    funext; dsimp; linarith

def lb_mul_q [hx : Computableℝ x] :=
  fun n ↦ min (hx.lb n * q) (hx.ub n * q)

def ub_mul_q [hx : Computableℝ x] :=
  fun n ↦ max (hx.lb n * q) (hx.ub n * q)

instance instComputableMulQ [hx : Computableℝ x] : Computableℝ (x * q) where
  lb := lb_mul_q x q
  ub := ub_mul_q x q
  hlb n := by
    simp_rw [lb_mul_q, min_def]
    by_cases hq : (q:ℝ) > 0
    <;> split_ifs with h
    <;> rify at *
    <;> nlinarith (config := {splitNe := true}) [hx.hlb n, hx.hub n]
  hub n := by
    simp_rw [ub_mul_q, max_def]
    by_cases hq : (q:ℝ) > 0
    <;> split_ifs with h
    <;> rify at *
    <;> nlinarith (config := {splitNe := true}) [hx.hlb n, hx.hub n]
  hgap := by
    have : (ub_mul_q x q - lb_mul_q x q)
      = fun n => (abs (ub x n - lb x n)) * (abs q) := by
      funext n
      dsimp
      simp_rw [ub_mul_q, lb_mul_q]
      simp_rw [min_def, max_def, abs_ite_le]
      split_ifs <;> nlinarith
    rw [this]
    apply IsCauSeq.mul
    · intro ε hε
      obtain ⟨i, hi⟩ := hx.hgap ε hε
      use i
      intro j hj
      replace hi := hi j hj
      simp_rw [abs_ite_le] at hi ⊢
      split_ifs at hi ⊢
      <;> dsimp at * <;> linarith
    · exact IsCauSeq.const _

instance instComputableQMul [Computableℝ x] : Computableℝ (q * x) :=
  mul_comm x q ▸ instComputableMulQ x q

-- instance instComputableMul [hx : Computableℝ x] [hy : Computableℝ y]: Computableℝ (x * y) where
--   lb n := (instComputableMulQ x q).lb
--   ub n := hx.ub n + hy.ub n
--   hlb n := by push_cast; exact add_le_add (hx.hlb n) (hy.hlb n)
--   hub n := by push_cast; exact add_le_add (hx.hub n) (hy.hub n)
--   hgap := by
--     convert (IsCauSeq.add hx.hgap hy.hgap) using 1
--     funext; dsimp; linarith

variable {x : ℝ}

/- Given a proof that a real number x isn't *exactly* zero, it's possible to decide if
0 ≤ x or not. Without that proof, we get a partial function. -/
partial def is_nonneg' (hx : Computableℝ x) : Bool :=
  is_nonneg_aux 0 where
  is_nonneg_aux (n : ℕ) :=
    if hx.ub n < 0 then
      false
    else if hx.lb n > 0 then
      true
    else
      is_nonneg_aux (n+1)

/-- For all positive reals, there's a rational between it and zero. -/
lemma exists_rat_between (x : ℝ) (hx : 0 < x) : ∃(q:ℚ), q ≤ x ∧ 0 < q := by
  use 1/(Int.ceil (1/x))
  have s1 : 0 < 1/x := one_div_pos.mpr hx
  have s2 : 1/x ≤ Int.ceil (1/x) := Int.le_ceil (1/x)
  have s3 : 0 < Int.ceil (1/x) := by exact Int.ceil_pos.mpr s1
  have s4 : 0 < (Int.ceil (1/x) : ℝ) := Int.cast_pos.mpr s3
  have s5 : 1/(Int.ceil (1/x)) ≥ 1/(1/x) := by
    push_cast
    have : 0 < (1:ℝ) := by norm_num
    -- apply?
    sorry
  -- have : 0 < Int.ceil x := Int.ceil_pos.mpr hx
  constructor
  · field_simp
    sorry
  · positivity

/-- With the proof, we get a total function. -/
def is_nonneg (hx : Computableℝ x) (hnz : x ≠ 0) : Bool :=
  is_nonneg_aux 0 hnz where
  is_nonneg_aux (n : ℕ) (hnz : x ≠ 0) :=
    if hx.ub n < 0 then
      false
    else if hx.lb n > 0 then
      true
    else
      is_nonneg_aux (n+1) hnz
    termination_by (by
      by_cases hsx : x > 0
      · have hx' : ∃(x':ℚ), x' ≤ x ∧ 0 < x' :=
          exists_rat_between x hsx
        -- obtain ⟨x', hx'⟩ := Classical.indefiniteDescription _ hx'
        -- obtain ⟨i, hi⟩ := Classical.indefiniteDescription _ (hx.hgap x' hx'.2)
        set x' := Classical.choose hx' with x'_def
        replace hx' := Classical.choose_spec hx'
        rw [← x'_def] at hx'
        exact Classical.choose (hx.hgap x' hx'.2)
      · replace hsx : -x > 0 := by linarith (config := {splitNe := true})
        have hq' : ∃(q:ℚ), q ≤ -x ∧ 0 < q :=
          exists_rat_between (-x) (hsx)
        obtain ⟨q, hq⟩ := Classical.indefiniteDescription _ hq'
        obtain ⟨i, hi⟩ := Classical.indefiniteDescription _ (hx.hgap q hq.2)
        exact i
       : ℕ) - n
    decreasing_by
    · decreasing_with
      apply Nat.sub_add_lt_sub _ Nat.le.refl
      split_ifs
      · dsimp
        sorry
      · simp
        dsimp
        sorry

theorem is_nonneg_iff {x : ℝ} (hx : Computableℝ x) (hnz : x ≠ 0) : is_nonneg hx hnz ↔ 0 < x := by
  constructor
  · sorry
  · intro hxpos
    obtain ⟨q, ⟨hq₁, hq₂⟩⟩ := exists_rat_between x hxpos
    obtain ⟨n, hn⟩ := hx.hgap q hq₂
    replace hn := hn n rfl.le
    have : is_nonneg.is_nonneg_aux hx n hnz := by
      rw [is_nonneg.is_nonneg_aux]
      sorry
    sorry

end Computableℝ
