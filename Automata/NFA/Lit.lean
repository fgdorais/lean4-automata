import Automata.NFA.Basic

namespace NFA
variable (set : α -> Bool)

protected def lit : NFA α where
  State := Bool
  start s := !s
  trans
  | x, false, true => set x
  | _, _, _ => false
  final s := s

@[simp] theorem lit_start : (NFA.lit set).start s = !s := rfl

@[simp] theorem lit_final : (NFA.lit set).final s = s := rfl

@[simp] theorem lit_trans : (NFA.lit set).trans x t s = (!t && s && set x) := by
  simp only [NFA.lit]
  split
  next => simp
  next h =>
    match s, t with
    | true, true => rfl
    | true, false => contradiction
    | false, true => rfl
    | false, false => rfl

@[simp] theorem lit_run : (NFA.lit set).run xs t s = match xs with | [] => s = t | [x] => !t && s && set x | _ => false := by
  split
  next =>
    unfold NFA.run
    simp
    constructor <;> intro | hysmm => symm; assumption
  next x =>
    rw [Bool.eq_iff_iff]
    simp
  next xs' h₀ h₁ =>
    match xs with
    | [] =>
      exfalso
      exact h₀ rfl
    | [x] =>
      exfalso
      exact h₁ x rfl
    | _::_::_ =>
      rw [Bool.eq_iff_iff]
      simp

@[simp] theorem lit_correct: (NFA.lit set).accept xs = match xs with | [x] => set x | _ => false := by
  unfold accept
  rw [Bool.eq_iff_iff]
  simp
  match xs with
  | [] =>
    simp
  | [x] =>
    simp
  | _::_::_ =>
    simp

@[simp] theorem lit_sound : set x = true -> (NFA.lit set).accept [x] = true := by
  intro h
  rw [lit_correct]
  split
  next hx =>
    cases hx
    exact h
  next =>
    assumption

@[simp] theorem lit_exact : (NFA.lit set).accept xs = true -> ∃ x, set x = true ∧ xs = [x] := by
  intro h
  rw [lit_correct] at h
  split at h
  next x =>
    exists x
  next =>
    contradiction

end NFA
