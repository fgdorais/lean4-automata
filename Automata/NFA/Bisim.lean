import Automata.NFA.Basic

namespace NFA

structure Bisim (m₁ m₂ : NFA α) where
  rel : m₁.State → m₂.State → Bool
  start {s₁ s₂} : rel s₁ s₂ → m₁.start s₁ = m₂.start s₂
  transLR {s₁ s₂ t₁ x} : rel s₁ s₂ → m₁.trans x s₁ t₁ → Find.any (λ t₂ => rel t₁ t₂ && m₂.trans x s₂ t₂)
  transRL {s₁ s₂ t₂ x} : rel s₁ s₂ → m₂.trans x s₂ t₂ → Find.any (λ t₁ => rel t₁ t₂ && m₁.trans x s₁ t₁)
  final {s₁ s₂} : rel s₁ s₂ → m₁.final s₁ = m₂.final s₂

namespace Bisim
variable (m : NFA α) {m₁ m₂ m₃ : NFA α}

protected def id : Bisim m m where
  rel s₁ s₂ := decide (s₁ = s₂)
  start h := by
    simp at h
    rw [h]
  transLR h ht := by
    simp at h ⊢
    rw [← h, ht]
  transRL h ht := by
    simp at h ⊢
    rw [h, ht]
  final h := by
    simp at h
    rw [h]

protected def inv (a : Bisim m₁ m₂) : Bisim m₂ m₁ where
  rel s₁ s₂ := a.rel s₂ s₁
  start h := by
    apply Eq.symm
    exact a.start h
  transLR := a.transRL
  transRL := a.transLR
  final h := by
    apply Eq.symm
    exact a.final h

protected def comp (a : Bisim m₂ m₃) (b : Bisim m₁ m₂) : Bisim m₁ m₃ where
  rel s₁ s₃ := Find.any (λ s₂ => b.rel s₁ s₂ && a.rel s₂ s₃)
  start h := by
    simp at h
    match h with
    | ⟨s₂, hb, ha⟩ =>
      trans (m₂.start s₂)
      exact b.start hb
      exact a.start ha
  transLR H h₁ := by
    simp at H h₁ ⊢
    match H with
    | ⟨s₂, hb, ha⟩ =>
      have H := b.transLR hb h₁
      simp at H
      match H with
      | ⟨t₂, htb, h₂⟩ =>
        have H := a.transLR ha h₂
        simp at H
        match H with
        | ⟨t₃, hta, h₃⟩ =>
          exists t₃
          constructor
          exists t₂
          exact h₃
  transRL H h₃ := by
    simp at H h₃ ⊢
    match H with
    | ⟨s₂, hb, ha⟩ =>
      have H := a.transRL ha h₃
      simp at H
      match H with
      | ⟨t₂, hta, h₂⟩ =>
        have H := b.transRL hb h₂
        simp at H
        match H with
        | ⟨t₁, htb, h₁⟩ =>
          exists t₁
          constructor
          exists t₂
          exact h₁
  final h := by
    simp at h
    match h with
    | ⟨s₂, hb, ha⟩ =>
      trans (m₂.final s₂)
      exact b.final hb
      exact a.final ha

end Bisim

end NFA
