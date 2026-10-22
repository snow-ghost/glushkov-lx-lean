import LRX.ShallowCutShift

namespace LRX.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def shiftCarrier (S : Finset (Fin n)) (c : Fin n) : Finset (Fin n) := S.image (fun i => i-c)

def ExtremePair (S : Finset (Fin n)) (x y : Fin n) : Prop :=
  x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ ∀ z ∈ S, min x.val y.val ≤ z.val ∧ z.val ≤ max x.val y.val

theorem shift_injective (c : Fin n) : Function.Injective (fun i : Fin n => i-c) := by
  intro i j h
  have hh := congrArg (fun k : Fin n => k+c) h
  simpa only [sub_add_cancel] using hh

@[simp] theorem mem_shift_carrier (S : Finset (Fin n)) (c i : Fin n) :
    i-c ∈ shiftCarrier S c ↔ i ∈ S := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
    exact (shift_injective c he) ▸ hj
  · intro h
    exact Finset.mem_image.mpr ⟨i,h,rfl⟩

theorem shift_value (i c : Fin n) :
    (i-c).val=if c.val ≤ i.val then i.val-c.val else n+i.val-c.val := by
  by_cases h : c.val ≤ i.val
  · rw [if_pos h,Fin.sub_val_of_le h]
  · rw [if_neg h,Fin.coe_sub_iff_lt.mpr (show i < c from lt_of_not_ge h)]

theorem shift_between_increasing (c x y z : Fin n) (hxy : x.val < y.val)
    (hz : x.val < z.val ∧ z.val < y.val) (hs : (x-c).val < (y-c).val) :
    (x-c).val < (z-c).val ∧ (z-c).val < (y-c).val := by
  simp only [shift_value] at hs ⊢
  split_ifs at * <;> omega

theorem shift_outside_decreasing (c x y z : Fin n) (hxy : x.val < y.val)
    (hz : z.val < x.val ∨ y.val < z.val) (hs : (y-c).val < (x-c).val) :
    (y-c).val < (z-c).val ∧ (z-c).val < (x-c).val := by
  simp only [shift_value] at hs ⊢
  split_ifs at * <;> omega

theorem ordered_shift_neighbor_cases (S : Finset (Fin n)) (c x y : Fin n)
    (hxy : x.val < y.val) (h : RankAdjacent (shiftCarrier S c) (x-c) (y-c)) :
    RankAdjacent S x y ∨ ExtremePair S x y := by
  have hx := (mem_shift_carrier S c x).mp h.1
  have hy := (mem_shift_carrier S c y).mp h.2.1
  have hne : x ≠ y := by intro he; subst y; omega
  by_cases hs : (x-c).val < (y-c).val
  · left
    refine ⟨hx,hy,hne,?_⟩
    intro z hz hbetween
    have hb : x.val < z.val ∧ z.val < y.val := by
      simpa only [min_eq_left (le_of_lt hxy),max_eq_right (le_of_lt hxy)] using hbetween
    have ht := shift_between_increasing c x y z hxy hb hs
    apply h.2.2.2 (z-c) ((mem_shift_carrier S c z).mpr hz)
    simpa only [min_eq_left (le_of_lt hs),max_eq_right (le_of_lt hs)] using ht
  · right
    have hnv : (x-c).val ≠ (y-c).val := fun he => h.2.2.1 (Fin.ext he)
    have hs' : (y-c).val < (x-c).val := by omega
    refine ⟨hx,hy,hne,?_⟩
    intro z hz
    by_contra hbound
    have hout : z.val < x.val ∨ y.val < z.val := by
      simp only [min_eq_left (le_of_lt hxy),max_eq_right (le_of_lt hxy)] at hbound
      omega
    have ht := shift_outside_decreasing c x y z hxy hout hs'
    apply h.2.2.2 (z-c) ((mem_shift_carrier S c z).mpr hz)
    simpa only [min_eq_right (le_of_lt hs'),max_eq_left (le_of_lt hs')] using ht

theorem extreme_pair_symm {S : Finset (Fin n)} {x y : Fin n}
    (h : ExtremePair S x y) : ExtremePair S y x := by
  refine ⟨h.2.1,h.1,Ne.symm h.2.2.1,?_⟩
  intro z hz
  simpa only [min_comm,max_comm] using h.2.2.2 z hz

theorem shift_neighbor_cases (S : Finset (Fin n)) (c x y : Fin n)
    (h : RankAdjacent (shiftCarrier S c) (x-c) (y-c)) :
    RankAdjacent S x y ∨ ExtremePair S x y := by
  by_cases hxy : x.val < y.val
  · exact ordered_shift_neighbor_cases S c x y hxy h
  · have hne : x.val ≠ y.val := by
      intro he
      exact h.2.2.1 (congrArg (fun i : Fin n => i-c) (Fin.ext he))
    rcases ordered_shift_neighbor_cases S c y x (by omega) (rank_adjacent_symm h) with h | h
    · exact Or.inl (rank_adjacent_symm h)
    · exact Or.inr (extreme_pair_symm h)

/-- Two distinct extreme vertices can be linearly adjacent only in a
carrier of at most two vertices. -/
theorem adjacent_extremes_card_le_two (S : Finset (Fin n)) (x y : Fin n)
    (ha : RankAdjacent S x y) (he : ExtremePair S x y) : S.card ≤ 2 := by
  classical
  have hsub : S ⊆ {x,y} := by
    intro z hz
    have hb := he.2.2.2 z hz
    have hn := ha.2.2.2 z hz
    have hval : z.val=x.val ∨ z.val=y.val := by omega
    rcases hval with h | h
    · simp [Fin.ext h]
    · simp [Fin.ext h]
  exact (Finset.card_le_card hsub).trans (by simp [Finset.card_pair ha.2.2.1])

#print axioms shift_neighbor_cases
end LRX.ZeroGap
