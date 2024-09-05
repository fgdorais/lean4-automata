import Batteries

open Batteries

macro "constr" : tactic => `(tactic| constructor)

structure StateType.{u} where State : Type u

abbrev Matrix (α) (rows cols : Nat) := Vector (Vector α cols) rows

#exit

namespace Vector
variable {size : Nat} {α : Type _}

theorem getElem_fin_eq_toArray_getElem (vec : Vector size α) (i : Fin size) : vec[i] = vec.toArray[i.val]'(by rw [vec.size_eq]; exact i.isLt) := rfl

instance : GetElem (Vector size α) Nat α (fun _ i => i < size) where
  getElem vec i hi := vec.toArray[i]'(by rw [vec.size_eq]; exact hi)

theorem getElem_nat_eq_toArray_getElem (vec : Vector size α) (i : Nat) (hi : i < size) : vec[i] = vec.toArray[i]'(by rw [vec.size_eq]; exact hi) := rfl

protected theorem ext' {α : Type _} {size : Nat} {v w : Vector size α} : (∀ i, (hi : i < size) → v[i] = w[i]) → v = w := by
  intro h
  cases v with
  | mk v hv =>
  cases w with
  | mk w hw =>
    congr 1
    apply Array.ext
    · rw [hv, hw]
    · intro i hi _
      rw [hv] at hi
      have := h i hi
      exact this

@[ext] protected theorem ext {α : Type _} {size : Nat} {v w : Vector size α} : (∀ (i : Fin size), v[i] = w[i]) → v = w := by
  intro h
  apply Vector.ext'
  intro i hi
  exact h ⟨i, hi⟩

protected def replicate {size : Nat} (val : α) : Vector size α where
  data := List.replicate size val
  size_eq := by rw [Array.size_mk, List.length_replicate]

instance [Inhabited α] : Inhabited (Vector size α) where
  default := Vector.replicate default

theorem getElem_replicate (val : α) (i : Fin size) : (Vector.replicate (size:=size) val)[i] = val := by
  unfold Vector.replicate
  rw [getElem_fin_eq_toArray_getElem]
  rw [Array.getElem_eq_data_getElem]
  rw [List.getElem_replicate]

protected abbrev map (f : α → β) (vec : Vector size α) : Vector size β where
  toArray := vec.toArray.map f
  size_eq := by simp_arith [vec.size_eq]

theorem getElem_map {f : α → β} (vec : Vector size α) (i : Fin size) :
  (vec.map f)[i] = f vec[i] := by
    rw [Vector.map]
    rw [getElem_fin_eq_toArray_getElem]
    rw [Array.getElem_map]
    rw [getElem_fin_eq_toArray_getElem]

def mapIdx (f : Fin size → α → β) (vec : Vector size α) : Vector size β where
  toArray := vec.toArray.mapIdx fun i x => f (vec.size_eq ▸ i) x
  size_eq := by rw [Array.size_mapIdx, vec.size_eq]

theorem getElem_mapIdx {f : Fin size → α → β} (vec : Vector size α) (i : Fin size) :
  (vec.mapIdx f)[i] = f i vec[i] := by
    rw [Vector.mapIdx]
    rw [getElem_fin_eq_toArray_getElem]
    rw [Array.getElem_mapIdx]
    rw [getElem_fin_eq_toArray_getElem]
    congr
    ext
    rw [congr_ndrec @Fin.val]

def set (vec : Vector size α) (i : Fin size) (val : α) : Vector size α where
  toArray := vec.toArray.set ⟨i.val, by simp [i.isLt, vec.size_eq]⟩ val
  size_eq := by simp [vec.size_eq]

def set? (vec : Vector size α) (i : Nat) (val : α) : Option (Vector size α) :=
  if hi : i < size then
    some <| vec.set ⟨i, hi⟩ val
  else
    none

def set! (vec : Vector size α) (i : Nat) (val : α) : Vector size α :=
  let _ : Inhabited α := ⟨val⟩
  if hi : i < size then
    vec.set ⟨i, hi⟩ val
  else
    panic! "index out of bounds"

@[inline]
def ofFn {size : Nat} (f : Fin size → α) : Vector size α where
  toArray := Array.ofFn f
  size_eq := by rw [Array.size_ofFn]

theorem get_ofFn {size : Nat} (f : Fin size → α) (i : Fin size) : (Vector.ofFn f)[i] = f i := by
  unfold Vector.ofFn
  rw [Vector.getElem_fin_eq_toArray_getElem, Array.getElem_ofFn]

protected def append (vec₁ : Vector size₁ α) (vec₂ : Vector size₂ α) : Vector (size₁ + size₂) α :=
  Vector.ofFn fun k => match (Fin.equivSum size₁ size₂).fwd k with
  | .inl i => vec₁[i]
  | .inr j => vec₂[j]

instance : HAppend (Vector m α) (Vector n α) (Vector (m + n) α) := ⟨Vector.append⟩

protected def left (vec : Vector (size₁ + size₂) α) : Vector size₁ α :=
  let e := Fin.equivSum size₁ size₂
  Vector.ofFn fun i => vec[e.rev (.inl i)]

protected def right (vec : Vector (size₁ + size₂) α) : Vector size₂ α :=
  let e := Fin.equivSum size₁ size₂
  Vector.ofFn fun j => vec[e.rev (.inr j)]

theorem get_append (vec₁ : Vector size₁ α) (vec₂ : Vector size₂ α) (k : Fin (size₁ + size₂)) :
  (vec₁ ++ vec₂)[k] = match (Fin.equivSum size₁ size₂).fwd k with
  | .inl i => vec₁[i]
  | .inr j => vec₂[j] :=
  Vector.get_ofFn ..

theorem get_append_left (vec₁ : Vector size₁ α) (vec₂ : Vector size₂ α) (i : Fin size₁) :
  (vec₁ ++ vec₂)[(Fin.equivSum size₁ size₂).rev (.inl i)] = vec₁[i] := by
  rw [get_append]
  rw [Equiv.fwd_rev]

theorem get_append_right (vec₁ : Vector size₁ α) (vec₂ : Vector size₂ α) (j : Fin size₂) :
  (vec₁ ++ vec₂)[(Fin.equivSum size₁ size₂).rev (.inr j)] = vec₂[j] := by
  rw [get_append]
  rw [Equiv.fwd_rev]

theorem append_left (vec₁ : Vector size₁ α) (vec₂ : Vector size₂ α) : (vec₁ ++ vec₂).left = vec₁ := by
  apply Vector.ext
  intro i
  simp only [HAppend.hAppend]
  unfold Vector.left Vector.append
  rw [Vector.get_ofFn]
  rw [Vector.get_ofFn]
  rw [Equiv.fwd_rev]

theorem append_right (vec₁ : Vector size₁ α) (vec₂ : Vector size₂ α) : (vec₁ ++ vec₂).right = vec₂ := by
  apply Vector.ext
  intro i
  simp only [HAppend.hAppend]
  unfold Vector.right Vector.append
  rw [Vector.get_ofFn]
  rw [Vector.get_ofFn]
  rw [Equiv.fwd_rev]

theorem append_left_right (vec : Vector (size₁ + size₂) α) : vec.left ++ vec.right = vec := by
  apply Vector.ext
  intro ⟨i, hi⟩
  simp only [HAppend.hAppend]
  unfold Vector.left Vector.right Vector.append
  rw [Vector.get_ofFn]
  split
  next heq =>
    rw [Vector.get_ofFn]
    rw [←heq]
    rw [Equiv.rev_fwd]
  next heq =>
    rw [Vector.get_ofFn]
    rw [←heq]
    rw [Equiv.rev_fwd]

@[inline]
def orVecBool {size : Nat} (vec₁ vec₂ : Vector size Bool) : Vector size Bool :=
  Vector.ofFn fun i => vec₁[i] || vec₂[i]

@[inline]
def andVecBool {size : Nat} (vec₁ vec₂ : Vector size Bool) : Vector size Bool :=
  Vector.ofFn fun i => vec₁[i] && vec₂[i]

abbrev dotBool {size : Nat} (vec₁ vec₂ : Vector size Bool) : Bool :=
  Fin.any (n:=size) fun i => vec₁[i] && vec₂[i]

end Vector

namespace Matrix

@[inline]
def ofFn {α} {row col : Nat} (f : Fin row → Fin col → α) : Matrix α row col :=
  Vector.ofFn fun i => Vector.ofFn (f i)

theorem get_ofFn {row col : Nat} (f : Fin row → Fin col → α) (i : Fin row) (j : Fin col) : (Matrix.ofFn f)[i][j] = f i j := by
  unfold Matrix.ofFn
  rw [Vector.getElem_ofFn]
  rw [Vector.get_ofFn]

@[inline]
def mulVecBool {row col : Nat} (mat : Matrix row col Bool) (vec : Vector col Bool) : Vector row Bool :=
  Vector.ofFn fun i => Fin.any (n:=col) fun j => mat[i][j] && vec[j]

@[inline]
def mulMatBool {row mid col : Nat} (mat₁ : Matrix row mid Bool) (mat₂ : Matrix mid col Bool) : Matrix row col Bool :=
  Matrix.ofFn fun i j => Fin.any (n:=mid) fun k => mat₁[i][k] && mat₂[k][j]

@[inline]
def orMatBool {row col : Nat} (mat₁ mat₂ : Matrix row col Bool) : Matrix row col Bool :=
  Matrix.ofFn fun i j => mat₁[i][j] || mat₂[i][j]

@[inline]
def andMatBool {row col : Nat} (mat₁ mat₂ : Matrix row col Bool) : Matrix row col Bool :=
  Matrix.ofFn fun i j => mat₁[i][j] && mat₂[i][j]

@[inline]
def eyeMatBool (size : Nat) : Matrix size size Bool :=
  Matrix.ofFn fun i j => i = j

end Matrix

instance : OfNat Bool (nat_lit 0) := ⟨false⟩
instance : OfNat Bool (nat_lit 1) := ⟨true⟩

structure Bits {α} (xs : List α) extends Fin (2 ^ xs.length)

namespace Bits
variable {α} {xs : List α}

protected def eq : {a b : Bits xs} → a.val = b.val → a = b
| ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

protected def equiv (xs :  List α) : Equiv (Bits xs) (Fin (2 ^ xs.length)) where
  fwd := Bits.toFin
  rev := Bits.mk
  fwd_eq_iff_rev_eq {x y} := match x, y with
  | ⟨⟨_,_⟩⟩, ⟨_,_⟩ => ⟨fun | rfl => rfl, fun | rfl => rfl⟩

instance (xs : List α) : DecidableEq (Bits xs)
| ⟨a⟩ ,⟨b⟩ => match a, b, inferInstanceAs (Decidable (a = b)) with
  | _, _, isTrue rfl => isTrue rfl
  | _, _, isFalse h => isFalse fun | rfl => h rfl

instance (xs : List α) : Finite (Bits xs) := Finite.ofEquiv (Bits.equiv xs)

protected def get (b : Bits xs) : Fin xs.length → Bool
| ⟨i, _⟩ => (b.val >>> i).isOdd

instance : GetElem (Bits xs) Nat Bool fun _ i => i < xs.length where
  getElem b i h := b.get ⟨i, h⟩

instance : GetElem (Bits xs) (Fin xs.length) Bool fun _ _ => True where
  getElem b i _ := b.get i

instance : GetElem (Bits xs) (List.Index xs) Bool fun _ _ => True where
  getElem b i _ := b.get i.toFin

def mkOfNat {α} {xs : List α} : Nat → List (Bits xs) → List (Bool × Bits xs)
| _, [] => []
| n, b :: bs => (n.isOdd, b) :: mkOfNat (n / 2) bs

theorem mkOfNat_nil {α} {xs : List α} (n : Nat) : mkOfNat (xs:=xs) n [] = [] := rfl

theorem mkOfNat_cons {α} {xs : List α} (n : Nat) (b : Bits xs) (bs : List (Bits xs)) : mkOfNat n (b::bs) = (n.isOdd, b) :: mkOfNat (n / 2) bs := rfl

def mkOfInt {α} {xs : List α} : Int → List (Bits xs) → List (Bool × Bits xs)
| _, [] => []
| n, b :: bs => (n.isOdd, b) :: mkOfInt (n / 2) bs

theorem mkOfInt_nil {α} {xs : List α} (n : Int) : mkOfInt (xs:=xs) n [] = [] := rfl

theorem mkOfInt_cons {α} {xs : List α} (n : Int) (b : Bits xs) (bs : List (Bits xs)) : mkOfInt n (b::bs) = (n.isOdd, b) :: mkOfInt (n / 2) bs := rfl

end Bits
