import Automata.NFA.Basic

namespace NFA

protected def eps : NFA α where
  State := Unit
  start _ := true
  final _ := true
  trans _ _ _ := false

@[simp] theorem eps_start : (NFA.eps (α := α)).start s = true := rfl

@[simp] theorem eps_final : (NFA.eps (α := α)).final s = true := rfl

@[simp] theorem eps_trans : NFA.eps.trans x s t = false := rfl

/-- Proof of correctness for `eps` machine -/
@[simp] theorem eps_correct (xs : List α) : NFA.eps.accept xs = match xs with | [] => true | _ => false := by
  split
  next =>
    simp
    exists ()
  next h =>
    simp
    intro () ()
    cases xs with
    | nil =>
      contradiction
    | cons x xs =>
      rw [Bool.eq_false_iff, ne_eq]
      rw [NFA.run_cons]
      simp

@[simp] theorem eps_sound : xs = [] → NFA.eps.accept xs := by
  intro h
  rw [eps_correct, h]

@[simp] theorem eps_exact : NFA.eps.accept xs → xs = [] := by
  intro h
  rw [eps_correct] at h
  split at h
  next => rfl
  next => contradiction

end NFA
