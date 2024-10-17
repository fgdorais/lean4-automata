import Automata.NFA.Basic

namespace NFA
variable (m : NFA α)

@[simp] theorem run_unappend : m.run (ys ++ xs) s t → ∃ u, m.run ys s u ∧ m.run xs u t := by
  intro happend
  induction ys generalizing s t with
  | nil =>
    rw [List.nil_append] at happend
    exists s
    constructor
    · simp only [NFA.run]; rfl
    · exact happend
  | cons y ys ih =>
    rw [List.cons_append] at happend
    simp at happend
    match happend with
    | ⟨v, htrans, hrun⟩ =>
      match ih hrun with
      | ⟨w, hrunxs, hrunys⟩ =>
        exists w
        constructor
        · simp
          exists v
        · exact hrunys

@[simp] theorem run_append_eq : m.run (ys ++ xs) s t = Find.any (λ u => m.run ys s u ∧ m.run xs u t) := by
  rw [Bool.eq_iff_iff]
  simp
  constructor
  · exact m.run_unappend
  · intro
    | ⟨w, hs, ht⟩ =>
      rw [run_append]
      exists w

def reachExact [Find α] : (d : Nat) → m.State → m.State → Bool
| 0, s, t => Find.any fun x => m.trans x s t
| d+1, s, t => Find.any fun u => reachExact d s u && reachExact d u t

theorem run_of_reachExact [Find α] : m.reachExact d s t → ∃ xs, xs.length = 2 ^ d ∧ m.run xs s t := by
  intro hr
  induction d using Nat.recAux generalizing s t with
  | zero =>
    unfold reachExact at hr
    simp at hr
    match hr with
    | ⟨x, htrans⟩ =>
      exists [x]
      constructor
      · rfl
      · simp
        exact htrans
  | succ d ih =>
    unfold reachExact at hr
    simp at hr
    match hr with
    | ⟨u, hreachsu, hreachut⟩ =>
      match ih hreachsu, ih hreachut with
      | ⟨xs, hlengthxs, hrunxs⟩, ⟨ys, hlengthys, hrunys⟩ =>
        exists xs ++ ys
        constructor
        · rw [List.length_append]
          rw [hlengthxs]
          rw [hlengthys]
          rw [Nat.pow_succ, Nat.mul_succ, Nat.mul_one]
        · rw [run_append]
          exists u

@[simp] theorem reachExact_of_run [Find α] : m.run xs s t → xs.length = 2 ^ d → m.reachExact d s t := by
  intro hrun hxs
  induction d using Nat.recAux generalizing s t xs with
  | zero =>
    match xs with
    | [] => contradiction
    | [x] =>
      unfold reachExact
      simp at hrun ⊢
      exists x
    | _::_::_ => injection hxs; contradiction
  | succ d ih =>
    unfold reachExact
    simp
    rw [←List.take_append_drop (2 ^ d) xs] at hrun
    match m.run_unappend hrun with
    | ⟨u,hrunsu,hrunut⟩ =>
      exists u
      constructor
      · apply ih hrunsu
        rw [List.length_take, Nat.min_def, hxs]
        rw [if_pos (Nat.pow_le_pow_of_le_right (Nat.zero_lt _) (Nat.le_add_right _ 1))]
      · apply ih hrunut
        rw [List.length_drop, hxs, Nat.pow_succ, Nat.mul_succ, Nat.mul_one, Nat.add_sub_cancel]

def reach [Find α] : (d : Nat) → m.State → m.State → Bool
| 0, s, t => t = s
| d+1, s, t => reach d s t || Find.any (λ u => m.reachExact d s u && reach d u t)

theorem run_of_reach [Find α] {d : Nat} {s t : m.State} : m.reach d s t → ∃ xs, xs.length < 2 ^ d ∧ m.run xs s t := by
  intro hr
  induction d using Nat.recAux generalizing s with
  | zero =>
    unfold reach at hr
    simp at hr
    exists []
    constructor
    · exact Nat.zero_lt ..
    · unfold run
      simp
      rw [hr]
  | succ d ih =>
    unfold reach at hr
    simp at hr
    cases hr with
    | inl il =>
      match ih il with
      | ⟨ys, hlist, hrun⟩ =>
        exists ys
        constructor
        · trans (2 ^ d)
          · exact hlist
          · rw [Nat.pow_succ, Nat.mul_succ, Nat.mul_one]
            apply Nat.lt_add_of_pos_right
            exact Nat.zero_lt ..
        · exact hrun
    | inr ir =>
      match ir with
      | ⟨s₁, rexact, r⟩ =>
        match ih r with
        | ⟨ys, hlist, hrun⟩ =>
          match run_of_reachExact m rexact with
          |⟨zs, hrlist, hrrun⟩ =>
            exists zs++ys
            constructor
            · rw [List.length_append]
              rw [hrlist]
              rw [Nat.pow_succ]
              rw [Nat.mul_succ]
              rw [Nat.mul_one]
              apply Nat.add_lt_add_left
              exact hlist
            · rw [run_append m]
              exists s₁

@[simp] theorem reach_of_run [Find α] {d : Nat} {s t : m.State} {xs : List α} : m.run xs s t → xs.length < 2 ^ d → m.reach d s t := by
  intro hrun hxs₁
  induction d using Nat.recAux generalizing s t xs with
  | zero =>
    cases xs with
    | nil =>
      unfold run at hrun
      unfold reach
      simp at hrun ⊢
      rw [hrun]
    | cons _ _ => contradiction
  | succ d ih =>
    unfold reach
    simp
    if hxs₂: xs.length < 2 ^ d then
      left
      exact ih hrun hxs₂
    else
      have lxs := Nat.le_of_not_gt hxs₂
      right
      rw [←List.take_append_drop (2 ^ d) xs] at hrun
      match m.run_unappend hrun with
      | ⟨u,hrunsu,hrunut⟩ =>
        exists u
        constructor
        · apply m.reachExact_of_run hrunsu
          rw [List.length_take]
          rw [Nat.min_def]
          rw [if_pos lxs]
        · apply ih hrunut
          rw [List.length_drop]
          apply Nat.sub_lt_left_of_lt_add
          · exact lxs
          · rw [Nat.pow_succ, Nat.mul_two] at hxs₁
            exact hxs₁

theorem reachableAux {s t : m.State} {ws : List α} {n : Nat} : ws.length < n → m.run ws s t → ∃ (ws : List α), ws.length < m.size ∧ m.run ws s t := by
  intro hws hrun
  induction n generalizing ws with
  | zero => contradiction
  | succ n ih =>
    by_cases ws.length < m.size with
    | isTrue hlt => exists ws
    | isFalse hge =>
      have hge : ws.length ≥ m.size := Nat.le_of_not_lt hge
      match m.splitting hge hrun with
      | ⟨u,xs,ys,zs,heq,hys,hxrun,_,hzrun⟩ =>
        have hrun : m.run (xs ++ zs) s t := by
          rw [run_append]
          exists u
        have hlt : (xs ++ zs).length < n := calc
          _ = xs.length + zs.length := by rw [List.length_append]
          _ < (xs.length + ys.length) + zs.length := by apply Nat.add_lt_add_right; apply Nat.lt_add_of_pos_right; exact hys
          _ = (xs ++ ys).length + zs.length := by rw [List.length_append]
          _ = ((xs ++ ys) ++ zs).length := by rw [List.length_append (xs ++ ys)]
          _ = ws.length := by rw [heq]
          _ ≤ n := by apply Nat.le_of_lt_succ hws
        apply ih hlt hrun

theorem reachable {s t : m.State} {ws : List α} : m.run ws s t → ∃ (ws : List α), ws.length < m.size ∧ m.run ws s t :=
  m.reachableAux (Nat.lt_succ_self ws.length)

@[simp] theorem reach_lg2_iff_reachable [Find α] (s t : m.State) : m.reach m.size.lg2 s t ↔ ∃ xs, m.run xs s t := by
constructor
· intro h
  match m.run_of_reach h with
  | ⟨xs,_,hrun⟩ =>
    exists xs
· intro h
  match h with
  | ⟨_,hrun⟩ =>
    match m.reachable hrun with
    | ⟨ys,hlength,hrun⟩ =>
      apply reach_of_run
      · exact hrun
      · calc ys.length
          < m.size := hlength
        _ < 2 ^ m.size.lg2 := Nat.lt_pow_lg2_self ..

instance (s t : m.State) [Find α] : Decidable (∃ xs, m.run xs s t) :=
  if h : m.reach m.size.lg2 s t then
    isTrue ((m.reach_lg2_iff_reachable s t).mp h)
  else
    isFalse fun f => h ((m.reach_lg2_iff_reachable s t).mpr f)

end NFA
