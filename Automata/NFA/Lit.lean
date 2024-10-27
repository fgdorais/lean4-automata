import Automata.NFA.Basic

namespace NFA
variable (set : α → Bool)

protected def lit : NFA α where
  State := Bool
  start s := !s
  trans x s t := !s && t && set x
  final s := s

@[simp] theorem lit_start (s) : (NFA.lit set).start s = !s := rfl

@[simp] theorem lit_final (s) : (NFA.lit set).final s = s := rfl

@[simp] theorem lit_trans (x t s) : (NFA.lit set).trans x t s = (!t && s && set x) := rfl

@[simp] theorem lit_run (xs t s) : (NFA.lit set).run xs t s = match xs with | [] => t = s | [x] => !t && s && set x | _ => false := by
  rw [Bool.eq_iff_iff]
  split
  · simp
  · simp
  · next _ h₀ h₁ =>
    rw [Bool.false_eq_true, iff_false]
    match xs with
    | [] => simp at h₀
    | [_] => simp at h₁
    | _::_::_ => simp

@[simp] theorem lit_correct (xs) : (NFA.lit set).accept xs = match xs with | [x] => set x | _ => false := by
  rw [Bool.eq_iff_iff, accept_eq_true_iff]
  simp only [lit_run]
  split <;> simp

theorem lit_sound (h : set x = true) : (NFA.lit set).accept [x] = true := by
  simp [*]

theorem lit_exact (h : (NFA.lit set).accept xs = true) : ∃ x, set x = true ∧ xs = [x] := by
  rw [lit_correct] at h
  split at h
  · simp [h]
  · contradiction

end NFA
