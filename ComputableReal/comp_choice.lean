import Mathlib
--https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Choice.20is.20computable!

-- Multi-sorted version of `Option`
inductive POption (α : Sort u) where
  /-- No value. -/
  | none : POption α
  /-- Some value of type `α`. -/
  | some (val : α) : POption α

instance : Inhabited (POption α) := ⟨POption.none⟩

noncomputable instance aux_1_sound {α : Sort u} (p : { p' : α → Prop // ∃ x, p' x}) :
    Inhabited {x // p.val x} :=
  let h : Nonempty (Subtype _) := Exists.elim p.property (fun w h => ⟨w, h⟩);
  Classical.inhabited_of_nonempty h

partial def aux_1 {α : Sort u} (p : { p' : α → Prop // ∃ x, p' x}) (f₁ : Prop → POption {x // p.val x}
    := (inferInstance : Inhabited _).default) : {x // p.val x} :=
  conf (type_of% @proof_irrel_heq) where --proof irrelevance
  conf (q : Prop) : {x // p.val x} :=
  match f₁ q with
  | POption.some x => x
  | _ => conf (¬q ∨ q) --law of excluded middle

--and now the main event:

/-computable-/
def computable_indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=
  aux_1 ⟨p,h⟩

/-computable-/
def computable_choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (computable_indefiniteDescription p h).val

theorem computable_choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (computable_choose h) :=
  (computable_indefiniteDescription p h).property

--double check that the new `computable_choose` is identical in type to `Classical.choose`:
#check (@Classical.choose : type_of% @computable_choose)
#check (@computable_choose : type_of% @Classical.choose)
