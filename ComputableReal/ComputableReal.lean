import Mathlib
import ComputableReal.ComputableRSeq

/-- Computable reals, defined as the quotient of ComputableℝSeq sequences -- sequences with
  Cauchy sequences of lower and upper bounds that converge to the same value -- by the equivalence
  relation of havint the same converged value. This is similar to how reals are quotients of Cauchy
  sequence (without any guarantees on lower/upper bounds). -/
def Computableℝ :=
  @Quotient ComputableℝSeq ComputableℝSeq.equiv

namespace Computableℝ

def mk : ComputableℝSeq → Computableℝ :=
  Quotient.mk ComputableℝSeq.equiv

def val : Computableℝ → ℝ := Quotient.lift ComputableℝSeq.val (fun _ _ h ↦ h)

@[simp]
theorem val_mk_eq_val : (mk x).val = x.val :=
  rfl

@[simp]
theorem val_quot_eq_val (x : ComputableℝSeq) : val (⟦x⟧ : Computableℝ) = x.val :=
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

/-- Alternate version of mapℝ that doesn't directly refer to f₂, so it stays
  computable even if f₂ isn't. -/
def mapℝ' (f : ComputableℝSeq → ComputableℝSeq) (h : ∃ f₂ : ℝ → ℝ, ∀x, (f x).val = f₂ x.val) :
    Computableℝ → Computableℝ :=
  Quotient.map f (fun a b h₂ ↦ h.elim fun _ h ↦ (h₂ ▸ h a).trans (h b).symm)

/-- Given a unary function that clearly mimics a standard real function, lift that. -/
def mapℝ (f : ComputableℝSeq → ComputableℝSeq) {f₂ : ℝ → ℝ} (h : ∀x, (f x).val = f₂ x.val) :
    Computableℝ → Computableℝ :=
  mapℝ' f ⟨f₂, h⟩

theorem mapℝ'_eq_mapℝ : mapℝ' f h = mapℝ f h₂ := by
  ext
  rw [mapℝ]

/-- Alternate version of map₂ℝ that doesn't directly refer to f₂, so it stays
  computable even if f₂ isn't. -/
def map₂ℝ' (f : ComputableℝSeq → ComputableℝSeq → ComputableℝSeq) (h : ∃ f₂ : ℝ → ℝ → ℝ, ∀x y,
    (f x y).val = f₂ x.val y.val) : Computableℝ → Computableℝ → Computableℝ :=
  Quotient.map₂ f (fun a b h₂ y z h₃ ↦ h.elim fun _ h ↦ (h₂ ▸ h₃ ▸ h a y).trans (h b z).symm)

/-- Given a binary function that clearly mimics a standard real function, lift that. -/
def map₂ℝ (f : ComputableℝSeq → ComputableℝSeq → ComputableℝSeq) {f₂ : ℝ → ℝ → ℝ}
    (h : ∀x y, (f x y).val = f₂ x.val y.val) :
    Computableℝ → Computableℝ → Computableℝ :=
  map₂ℝ' f ⟨f₂, h⟩

theorem map₂ℝ'_eq_map₂ℝ : map₂ℝ' f h = map₂ℝ f h₂ := by
  ext
  rw [map₂ℝ]

@[simp]
theorem val_mapℝ_eq_val : (@mapℝ f f₂ h x).val = f₂ x.val := by
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  subst hx'
  rw [mapℝ, mapℝ', Quotient.map_mk]
  apply h

@[simp]
theorem val_map₂ℝ_eq_val : (@map₂ℝ f f₂ h x y).val = f₂ x.val y.val := by
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  let ⟨y',hy'⟩ := Quotient.exists_rep y
  subst hx'
  subst hy'
  rw [map₂ℝ, map₂ℝ', Quotient.map₂_mk]
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
  val_map₂ℝ_eq_val

@[simp]
theorem mul_val : (x * y).val = x.val * y.val :=
  val_map₂ℝ_eq_val

@[simp]
theorem neg_val : (-x).val = -(x.val) :=
  val_mapℝ_eq_val

@[simp]
theorem sub_val : (x - y).val = x.val - y.val :=
  val_map₂ℝ_eq_val

@[simp]
theorem sub_mk (x' y' : ComputableℝSeq) : mk x' - mk y' = mk (x' - y') :=
  rfl

@[simp]
theorem zero_val : (0 : Computableℝ).val = 0 := by
  rw [Zero.toOfNat0, instComputableZero]
  simp only [val_mk_eq_val, ComputableℝSeq.zero_val]

 @[simp]
theorem one_val : (1 : Computableℝ).val = 1 := by
  rw [One.toOfNat1, instComputableOne]
  simp only [val_mk_eq_val, ComputableℝSeq.one_val]

instance instCommRing : CommRing Computableℝ := by
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

section safe_inv

private def nz_quot_equiv := Equiv.subtypeQuotientEquivQuotientSubtype
    (fun x : ComputableℝSeq ↦ x.val ≠ 0)
    (fun x : Computableℝ ↦ x ≠ 0)
    (fun _ ↦ ⟨
      fun h h₂ ↦ by
        rw [← eq_iff_eq_val, zero_val] at h₂
        exact h h₂,
      fun (h : ¬_ = 0) h₂ ↦ by
        rw [← eq_iff_eq_val, zero_val] at h
        exact h h₂⟩)
    (fun _ _ ↦ Iff.rfl)

/-- Auxiliary inverse definition that operates on the nonzero Computableℝ values. -/
def safe_inv' : { x : Computableℝ // x ≠ 0 } → { x : Computableℝ // x ≠ 0 } :=
  fun v ↦ nz_quot_equiv.invFun <| Quotient.map _ fun x y h₁ ↦ by
    change (ComputableℝSeq.inv_nz x).val.val = (ComputableℝSeq.inv_nz y).val.val
    rw [ComputableℝSeq.val_inv_nz x, ComputableℝSeq.val_inv_nz y, h₁]
  (nz_quot_equiv.toFun v)

/-- Inverse of a nonzero Computableℝ, safe (terminating) as long as x is nonzero. -/
irreducible_def safe_inv (hnz : x ≠ 0) : Computableℝ := safe_inv' ⟨x, hnz⟩

@[simp]
theorem safe_inv_val (hnz : x ≠ 0) : (x.safe_inv hnz).val = x.val⁻¹ := by
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  subst hx'
  have : (nz_quot_equiv { val := ⟦x'⟧, property := hnz : { x : Computableℝ // x ≠ 0 } }) =
      ⟦{ val := x', property := _ }⟧ := by
    apply Equiv.subtypeQuotientEquivQuotientSubtype_mk
  rw [safe_inv, safe_inv', val, Equiv.toFun_as_coe, Equiv.invFun_as_coe, Quotient.lift_mk, this,
    Quotient.map_mk, nz_quot_equiv, Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk,
    Quotient.lift_mk, ComputableℝSeq.val_inv_nz]

end safe_inv

section field

instance instComputableInv : Inv Computableℝ :=
  ⟨mapℝ' (·⁻¹) ⟨(·⁻¹), ComputableℝSeq.val_inv⟩⟩

@[simp]
theorem inv_val : (x⁻¹).val = (x.val)⁻¹ := by
  change (mapℝ' _ _ _).val = (x.val)⁻¹
  rw [mapℝ'_eq_mapℝ]
  exact val_mapℝ_eq_val (h := ComputableℝSeq.val_inv)

example : True := ⟨⟩

instance instField : Field Computableℝ := { instCommRing with
  qsmul := qsmulRec _
  exists_pair_ne := ⟨0, 1, by
    rw [ne_eq, ← eq_iff_eq_val, zero_val, one_val]
    exact zero_ne_one⟩
  mul_inv_cancel := by
    intro a ha
    rw [← eq_iff_eq_val, mul_val, inv_val, one_val]
    have : val a ≠ 0 := by rwa [← zero_val, ne_eq, eq_iff_eq_val]
    field_simp
  inv_zero := by rw [← eq_iff_eq_val]; simp
    }

@[simp]
theorem div_val : (x / y).val = x.val / y.val := by
  change (x * y⁻¹).val = _
  rw [mul_val, inv_val]
  field_simp

end field

section ordered

variable (x y : Computableℝ)

def lt : Prop := by
  apply Quotient.lift (fun z ↦ z.sign = SignType.pos) ?_ (y - x)
  intro a b h
  dsimp
  rw [ComputableℝSeq.sign_sound, ComputableℝSeq.sign_sound, h]

instance instLT : LT Computableℝ :=
  ⟨lt⟩

def le : Prop := by
  apply Quotient.lift (fun z ↦ SignType.zero ≤ z.sign) ?_ (y - x)
  intro a b h
  dsimp
  rw [ComputableℝSeq.sign_sound, ComputableℝSeq.sign_sound, h]

instance instLE : LE Computableℝ :=
  ⟨le⟩

@[simp]
theorem lt_iff_lt : x.val < y.val ↔ x < y := by
  change x.val < y.val ↔ lt x y
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  let ⟨y',hy'⟩ := Quotient.exists_rep y
  subst hx'
  subst hy'
  rw [lt, ← mk, val_mk_eq_val, val_mk_eq_val, sub_mk, mk, Quotient.lift_mk]
  rw [ComputableℝSeq.sign_pos_iff, ComputableℝSeq.sub_eq_sub, sub_pos]

@[simp]
theorem le_iff_le : x.val ≤ y.val ↔ x ≤ y := by
  change x.val ≤ y.val ↔ le x y
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  let ⟨y',hy'⟩ := Quotient.exists_rep y
  subst hx'
  subst hy'
  rw [le, ← mk, val_mk_eq_val, val_mk_eq_val, sub_mk, mk, Quotient.lift_mk]
  rw [ComputableℝSeq.sign_sound, SignType.zero_eq_zero, sign_nonneg_iff]
  rw [ComputableℝSeq.sub_eq_sub, sub_nonneg]

instance instDecidableLE : DecidableRel (fun (x y : Computableℝ) ↦ x ≤ y) :=
  fun a b ↦ by
    change Decidable (le a b)
    rw [le]
    infer_instance

--TODO: add a faster `min` and `max` that don't require sign computation.
instance instLinearOrderedField : LinearOrderedField Computableℝ := by
  refine' { instField, instLT, instLE with
      decidableLE := inferInstance
      le_refl := _
      le_trans := _
      le_antisymm := _
      add_le_add_left := _
      zero_le_one := _
      mul_pos := _
      le_total := _
      lt_iff_le_not_le := _
    }
  all_goals
    intros
    simp only [← le_iff_le, ← lt_iff_lt, ← eq_iff_eq_val, add_val, mul_val, zero_val, one_val] at *
    first
    | linarith (config := {splitNe := true})
    | apply mul_pos ‹_› ‹_›
    | apply le_total
    | apply lt_iff_le_not_le

end ordered

end Computableℝ
