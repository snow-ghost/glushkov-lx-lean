import LRX.ZeroGapFactorization

/-! Directed open arcs and the geometric condition satisfied by the ordered
list of zero-gap exchanges. Later endpoints avoid each earlier open arc. -/
namespace LRX.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

abbrev Event (n : ℕ) := Fin n × Fin n

def eventSwap (e : Event n) : State n := Equiv.swap e.1 e.2

def rotateEvent (u : Fin n) (e : Event n) : Event n := (e.1+u,e.2+u)

def Inside (e : Event n) (i : Fin n) : Prop := 0 < distance e.1 i ∧ distance e.1 i < distance e.1 e.2

def LaterOutside (e f : Event n) : Prop := ¬Inside e f.1 ∧ ¬Inside e f.2

theorem distance_translate (u a b : Fin n) : distance (a+u) (b+u)=distance a b := by
  unfold distance
  congr 1
  ring

theorem inside_translate (u : Fin n) (e : Event n) (i : Fin n) :
    Inside (rotateEvent u e) (i+u) ↔ Inside e i := by
  simp only [Inside,rotateEvent,distance_translate]

theorem later_outside_translate (u : Fin n) {e f : Event n} (h : LaterOutside e f) :
    LaterOutside (rotateEvent u e) (rotateEvent u f) := by
  simpa only [LaterOutside,rotateEvent,Inside,distance_translate] using h

theorem event_swap_translate (u : Fin n) (e : Event n) :
    eventSwap (rotateEvent u e)=MulAut.conj (RotationWords.rotation u) (eventSwap e) := by
  have h := Equiv.swap_apply_apply (RotationWords.rotation u) e.1 e.2
  simpa only [eventSwap,rotateEvent,RotationWords.rotation,AffineLift.rotation_power_apply,
    Fin.cast_val_eq_self,MulAut.conj_apply] using h

theorem exchange_active_subset (d : Fin n → ℤ) (v i : Fin n)
    (hpos : 0 < d 0) (hneg : d v < 0) (hi : exchange d v i ≠ 0) : d i ≠ 0 := by
  by_cases hi0 : i=0
  · subst i
    omega
  · by_cases hiv : i=v
    · subst i
      omega
    · simpa only [exchange,ite_eq_right hi0,ite_eq_right hiv] using hi

theorem zero_gap_excludes_active_event (d : Fin n → ℤ) (v : Fin n)
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < v.val → d i=0)
    (e : Event n) (he : d e.1 ≠ 0 ∧ d e.2 ≠ 0) : LaterOutside (0,v) e := by
  have hdist (i : Fin n) : distance 0 i=i.val := by simp [distance]
  constructor
  · intro h
    obtain ⟨hlo,hhi⟩ := h
    simp only [hdist] at hlo hhi
    exact he.1 (hgap e.1 hlo hhi)
  · intro h
    obtain ⟨hlo,hhi⟩ := h
    simp only [hdist] at hlo hhi
    exact he.2 (hgap e.2 hlo hhi)

#print axioms event_swap_translate
#print axioms zero_gap_excludes_active_event
end LRX.ZeroGap
