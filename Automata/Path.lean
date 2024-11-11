import Batteries
local infix:50 " ≅ " => HEq

inductive Path {σ : Type _} : σ → σ → Type _
| nil (s) : Path s s
| cons (s) {t u} : Path t u → Path s u

namespace Path

scoped syntax (name := path) "⟦" term,+ "⟧"  : term
scoped macro_rules (kind := path)
  | `(⟦ $a ⟧)        => `(Path.nil $a)
  | `(⟦ $a, $as,* ⟧) => `(Path.cons $a ⟦$as,*⟧)

protected def append : Path s t → Path t u → Path s u
| nil _, q => q
| cons s p, q => cons s (Path.append p q)
scoped instance (s t u : σ) : HAppend (Path s t) (Path t u) (Path s u) := ⟨Path.append⟩

@[simp] theorem append_cons_left (p : Path s t) (q : Path t u) : cons r p ++ q = cons r (p ++ q) := rfl

@[simp] theorem append_left_id (p : Path s t) : ⟦s⟧ ++ p = p := rfl

@[simp] theorem append_right_id : (p : Path s t) → p ++ ⟦t⟧ = p
| nil _ => rfl
| cons s p => congrArg (cons s) (append_right_id p)

@[simp] theorem append_assoc : (p : Path s t) → (q : Path t u) → (r : Path u v) → (p ++ q) ++ r = p ++ (q ++ r)
| nil _, q, r => rfl
| cons s p, q, r => congrArg (cons s) (append_assoc p q r)

@[simp] theorem append_cancel_left : (p : Path s t) → {q r : Path t u} → p ++ q = p ++ r → q = r
| nil _, _, r, h => h
| cons s p, q, r, h =>
  have h : p ++ q = p ++ r := by injection h
  append_cancel_left p h

protected def reverse : Path s t → Path t s
| nil _ => nil _
| cons s p => Path.append (Path.reverse p) (cons _ (nil s))

@[simp] theorem reverse_nil : ⟦s⟧.reverse = ⟦s⟧ := rfl

@[simp] theorem reverse_append : (p : Path s t) → (q : Path t u) → (p ++ q).reverse = q.reverse ++ p.reverse
| nil _, q => by rw [append_left_id, reverse_nil, append_right_id]
| @cons _ r s _ p, q => calc
  _ = (p ++ q).reverse ++ ⟦s, r⟧ := rfl
  _ = (q.reverse ++ p.reverse) ++ ⟦s, r⟧ := by rw [reverse_append p q]
  _ = q.reverse ++ (p.reverse ++ ⟦s, r⟧) := by rw [append_assoc]

@[simp] theorem reverse_reverse : (p : Path s t) → p.reverse.reverse = p
| nil _ => rfl
| @cons _ s t u p => calc
  _ = (p.reverse ++ ⟦t,s⟧).reverse := rfl
  _ = ⟦t,s⟧.reverse ++ p.reverse.reverse := by rw [reverse_append]
  _ = ⟦t,s⟧.reverse ++ p := by rw [reverse_reverse p]

@[simp] theorem append_cancel_right (p : Path t u) {q r : Path s t} : q ++ p = r ++ p → q = r := by
  intro h
  have h : q.reverse = r.reverse := by
    apply append_cancel_left p.reverse
    rw [←reverse_append, ←reverse_append, h]
  rw [←reverse_reverse q, ←reverse_reverse r, h]

protected def length : Path s t → Nat
| nil _ => 0
| cons _ p => Path.length p + 1

@[simp] theorem length_nil : (nil s).length = 0 := rfl

@[simp] theorem length_cons (p : Path t u) : (cons s p).length = p.length + 1 := rfl

@[simp] theorem length_append : (p : Path s t) →  (q : Path t u) → (p ++ q).length = p.length + q.length
| nil _, q => by rw [append_left_id, length_nil, Nat.zero_add]
| cons _ p, q => by rw [append_cons_left, length_cons, length_cons, Nat.add_right_comm, length_append p q]

def val : Nat → {s t : σ} → Path s t → σ
| 0, s, _, _ => s
| _+1, _, t, nil _ => t
| n+1, _, _, cons _ p => val n p

def take : (n : Nat) → {s t : σ} → (p : Path s t) → Path s (val n p)
| 0, _, _, _ => nil _
| _+1, _, _, nil _ => nil _
| n+1, _, _, cons s p => cons s (take n p)

@[simp] theorem take_nil : (nil s).take n ≅ nil s := match n with | 0 => HEq.rfl | _+1 => HEq.rfl

@[simp] theorem take_nil_zero : (nil s).take 0 = nil s := rfl

@[simp] theorem take_nil_succ (n : Nat) {s : σ} : (nil s).take (n+1) = nil s := rfl

@[simp] theorem take_cons_zero : (cons s p).take 0 = nil s :=  rfl

@[simp] theorem take_cons_succ {s t u : σ} {p : Path t u} : (cons s p).take (n+1) = cons s (p.take n) :=  rfl

def drop : (n : Nat) → {s t : σ} → (p : Path s t) → Path (val n p) t
| 0, _, _, p => p
| _+1, _, _, nil _ => nil _
| n+1, _, _, cons _ p => drop n p

@[simp] theorem drop_nil : (nil s).drop n ≅ nil s := match n with | 0 => HEq.rfl | _+1 => HEq.rfl

@[simp] theorem drop_nil_zero : (nil s).drop 0 = nil s := rfl

@[simp] theorem drop_nil_succ {s : σ} : (nil s).drop (n+1) = nil s := rfl

@[simp] theorem drop_cons_zero : (cons s p).drop 0 = cons s p :=  rfl

@[simp] theorem drop_cons_succ {s t u : σ} {p : Path t u} : (cons s p).drop (n+1) = p.drop n :=  rfl

@[simp] theorem drop_zero {p : Path s t} : p.drop 0 = p := rfl

@[simp] theorem append_take_drop : (n : Nat) → {s t : σ} → (p : Path s t) → take n p ++ drop n p = p
| 0, _, _, _ => rfl
| _+1, _, _, nil _ => rfl
| n+1, _, _, cons _ p => congrArg (cons _) (append_take_drop n p)

@[simp] theorem val_nil : (nil s).val i = s := match i with | 0 => rfl | _+1 => rfl

@[simp] theorem val_cons_zero {p : Path t u} : (cons s p).val 0 = s := rfl

@[simp] theorem val_cons_succ : (cons s p).val (i+1) = p.val i := rfl

@[simp] theorem val_cons : (cons s p).val i = match i with | 0 => s | i+1 => p.val i := by
  split
  next => rw [val_cons_zero]
  next => rw [val_cons_succ]

@[simp] theorem val_take {p : Path s t} : n ≤ p.length → i ≤ n → (p.take n).val i = p.val i := by
  intro hp hi
  induction n, i using Nat.recDiag generalizing s t p with
  | zero_zero => rfl
  | zero_succ => contradiction
  | succ_zero => rfl
  | succ_succ n i ih =>
    match p with
    | nil _ => rfl
    | cons _ _ =>
      simp only [take_cons_succ, val_cons_succ]
      apply ih
      · exact Nat.le_of_succ_le_succ hp
      · exact Nat.le_of_succ_le_succ hi

@[simp] theorem val_drop {p : Path s t} : n ≤ p.length → i ≥ n → (p.drop n).val i = p.val (i+n) := by
  intro hp hi
  induction n generalizing s t p with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ i]
    match p with
    | nil _ => contradiction
    | cons _ _ =>
      simp only [drop_cons_succ, val_cons_succ]
      apply ih
      · exact Nat.le_of_succ_le_succ hp
      · omega

end Path
