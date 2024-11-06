import Automata.NFA.Basic

namespace NFA

protected def eps : NFA α where
  State := Unit
  start _ := true
  final _ := true
  trans _ _ _ := false

@[simp] theorem eps_start (s) : (NFA.eps (α := α)).start s = true := rfl

@[simp] theorem eps_final (s) : (NFA.eps (α := α)).final s = true := rfl

@[simp] theorem eps_trans (x s t) : (NFA.eps (α := α)).trans x s t = false := rfl

/-- Proof of correctness for `eps` machine -/
@[simp] theorem eps_correct (xs : List α) : NFA.eps.accept xs = match xs with | [] => true | _ => false := by
  split
  next =>
    simp only [accept_eq_true_iff, run_nil, eps_start, eps_final, and_self, and_true, exists_eq']
    exists ()
  next h =>
    simp only [accept_eq_false_iff, Bool.not_eq_true, eps_start, not_true_eq_false, eps_final,
      or_self, or_false]
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
