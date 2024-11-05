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
        rw [if_pos]
        omega
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
    · simp
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
            omega
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

-- Taken from `Automata/NFA/Pumping.lean`
theorem splitting [Fin.Enum  α] {s t : m.State} {ws : List α} : ws.length ≥ m.size → m.run ws s t → ∃ (u : m.State) (xs ys zs : List α), ws = xs ++ ys ++ zs ∧ ys.length > 0 ∧ m.run xs s u ∧ m.run ys u u ∧ m.run zs u t := by
  intro hw hrun
  match m.trace_of_run hrun with
  | ⟨p, hp⟩ =>
    match Finite.php p.val with
    | ⟨i,j,hij,hjs,hval⟩ =>
      let zs := ws.drop j
      let ys := (ws.take j).drop i
      let xs := (ws.take j).take i
      let pz := p.drop j
      let py := (p.take j).drop i
      let px := (p.take j).take i
      have hz : Trace m zs pz := m.trace_drop j hp
      have hy : Trace m ys py := m.trace_drop i (m.trace_take j hp)
      have hx : Trace m xs px := m.trace_take i (m.trace_take j hp)
      have hjp : j ≤ p.length := by
        rw [←Trace.length_eq_length m hp]
        transitivity m.size
        · exact hjs
        · exact hw
      have hpij : p.val i = (p.take j).val i := by rw [Path.val_take hjp (Nat.le_of_lt hij)]
      exists p.val i, xs, ys, zs
      constructor
      · calc
        _ = ws.take j ++ zs := by rw [List.take_append_drop j]
        _ = (xs ++ ys) ++ zs := by rw [List.take_append_drop i]
      · constructor
        · have : j ≤ ws.length := Nat.le_trans hjs hw
          rw [List.length_drop i (ws.take j)]
          rw [List.length_take j ws]
          rw [Nat.min_eq_left this]
          apply Nat.sub_pos_of_lt hij
        · constructor
          · rw [hpij]
            apply m.run_of_trace hx
            done
          · constructor
            · transitivity (m.run ys (p.val i) (p.val j))
              · rw [hval]
              · rw [hpij]
                apply m.run_of_trace hy
            · rw [hval]
              apply m.run_of_trace hz
              done

-- Taken from `Automata/NFA/Pumping.lean`
@[simp] theorem reachableAux [Fin.Enum α] {s t : m.State} {ws : List α} {n : Nat} : ws.length < n → m.run ws s t → ∃ (ws : List α), ws.length < m.size ∧ m.run ws s t := by
  intro hws hrun
  induction n generalizing ws with
  | zero => contradiction
  | succ n ih =>
    if hwslt: ws.length < m.size then
      exists ws
    else
      have hge : ws.length ≥ m.size := Nat.le_of_not_lt hwslt
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

-- Taken from `Automata/NFA/Pumping.lean`
@[simp] theorem reachable [Fin.Enum α] {s t : m.State} {ws : List α} : m.run ws s t → ∃ (ws : List α), ws.length < m.size ∧ m.run ws s t :=
  m.reachableAux (Nat.lt_succ_self ws.length)

@[simp] theorem reach_lg2_iff_reachable [Fin.Enum α] (s t : m.State) : m.reach m.size.lg2 s t ↔ ∃ xs, m.run xs s t := by
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
        _ < 2 ^ m.size.lg2 := sorry


instance (s t : m.State) [Fin.Enum α] : Decidable (∃ xs, m.run xs s t) :=
  if h : m.reach m.size.lg2 s t then
    isTrue ((m.reach_lg2_iff_reachable s t).mp h)
  else
    isFalse fun f => h ((m.reach_lg2_iff_reachable s t).mpr f)

end NFA
