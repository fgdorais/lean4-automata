import Automata.NFA.Basic

namespace NFA
variable (set : α → Bool)

protected def lit : NFA α where
  State := Bool
  start s := !s
  trans x s t := !s && t && set x
  final s := s

@[simp] theorem lit_start : (NFA.lit set).start s = !s := rfl

@[simp] theorem lit_final : (NFA.lit set).final s = s := rfl

@[simp] theorem lit_trans : (NFA.lit set).trans x t s = (!t && s && set x) := rfl

@[simp] theorem lit_run : (NFA.lit set).run xs t s = match xs with | [] => s = t | [x] => !t && s && set x | _ => false := by
  split
  next =>
    simp [NFA.run]
    constructor <;> intro | hsymm => symm; assumption
  next x =>
    rw [Bool.eq_iff_iff]
    simp
  next _ h₀ h₁ =>
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
  rw [Bool.eq_iff_iff]
  simp
  match xs with
  | [] =>
    simp
  | [x] =>
    simp
  | _::_::_ =>
    simp

theorem lit_sound : set x = true → (NFA.lit set).accept [x] = true := by
  intro h
  simp
  exact h

theorem lit_exact : (NFA.lit set).accept xs = true → ∃ x, set x = true ∧ xs = [x] := by
  simp only [lit_correct]
  intro h
  split at h
  next x =>
    exists x
  next =>
    contradiction

end NFA
