import LRX.ZeroGapEventGeometry

/-! Weighted paths retain the signed integer motion of tokens through the
endpoint events; their weights do not identify coordinates modulo n. -/
namespace LRX.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def EventMove (events : List (Event n)) (i j : Fin n) (z : ℤ) : Prop :=
  ∃ e ∈ events, (i=e.1 ∧ j=e.2 ∧ z=(distance e.1 e.2 : ℤ)) ∨
    (i=e.2 ∧ j=e.1 ∧ z= -(distance e.1 e.2 : ℤ))

inductive Travel (events : List (Event n)) : Fin n → Fin n → ℤ → Prop
  | refl (i : Fin n) : Travel events i i 0
  | head {i j k : Fin n} {a b : ℤ} (he : EventMove events i j a)
      (hp : Travel events j k b) : Travel events i k (a+b)

theorem Travel.trans {events : List (Event n)} {i j k : Fin n} {a b : ℤ}
    (h : Travel events i j a) (h' : Travel events j k b) : Travel events i k (a+b) := by
  induction h with
  | refl => simpa using h'
  | head he hp ih => simpa only [add_assoc] using Travel.head he (ih h')

theorem Travel.mono {events more : List (Event n)} (hsub : ∀ e ∈ events, e ∈ more)
    {i j : Fin n} {z : ℤ} (h : Travel events i j z) : Travel more i j z := by
  induction h with
  | refl => exact Travel.refl _
  | head he hp ih =>
    obtain ⟨e,he,hmove⟩ := he
    exact Travel.head ⟨e,hsub e he,hmove⟩ ih

theorem event_move_rotate (u : Fin n) {events : List (Event n)} {i j : Fin n} {z : ℤ}
    (h : EventMove events i j z) : EventMove (events.map (rotateEvent u)) (i+u) (j+u) z := by
  obtain ⟨e,he,h⟩ := h
  refine ⟨rotateEvent u e,List.mem_map.mpr ⟨e,he,rfl⟩,?_⟩
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl,by simp [rotateEvent,distance_translate]⟩
  · exact Or.inr ⟨rfl,rfl,by simp [rotateEvent,distance_translate]⟩

theorem Travel.rotate (u : Fin n) {events : List (Event n)} {i j : Fin n} {z : ℤ}
    (h : Travel events i j z) : Travel (events.map (rotateEvent u)) (i+u) (j+u) z := by
  induction h with
  | refl => exact Travel.refl _
  | head he hp ih => exact Travel.head (event_move_rotate u he) ih

def headShift (v i : Fin n) : ℤ := if i=0 then (v : ℤ) else if i=v then -(v : ℤ) else 0

theorem head_travel (v i : Fin n) (events : List (Event n)) :
    Travel ((0,v)::events) i (Equiv.swap 0 v i) (headShift v i) := by
  by_cases hi : i=0
  · subst i
    have he : EventMove ((0,v)::events) 0 v (v : ℤ) :=
      ⟨(0,v),by simp,Or.inl ⟨rfl,rfl,by simp [distance]⟩⟩
    simpa [headShift] using Travel.head he (Travel.refl v)
  · by_cases hiv : i=v
    · subst i
      have he : EventMove ((0,v)::events) v 0 (-(v : ℤ)) :=
        ⟨(0,v),by simp,Or.inr ⟨rfl,rfl,by simp [distance]⟩⟩
      simpa [headShift,hi] using Travel.head he (Travel.refl 0)
    · simpa [headShift,hi,hiv,Equiv.swap_apply_of_ne_of_ne hi hiv] using (Travel.refl (events := (0,v)::events) i)

theorem exchange_motion (d : Fin n → ℤ) (v i : Fin n) (hv : v ≠ 0) :
    headShift v i+exchange d v (Equiv.swap 0 v i)=d i := by
  by_cases hi : i=0
  · subst i
    simp [headShift,exchange,hv]
  · by_cases hiv : i=v
    · subst i
      simp [headShift,exchange,hv]
    · simp [headShift,exchange,hi,hiv,Equiv.swap_apply_of_ne_of_ne hi hiv]

#print axioms Travel.rotate
#print axioms exchange_motion
end LRX.ZeroGap
