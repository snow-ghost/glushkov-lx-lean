import LRX.MatchingCircularReflection

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The reverse arrow of an adjacent pair consumes n-1 units in the clockwise lift. -/
theorem shifted_adjacent_reverse_coordinate {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ))
    (hinv : Function.Involutive (shiftedLiftPermutation p c h))
    (a : Fin n) (ha : a.val+1=(shiftedLiftPermutation p c h a).val) :
    d (shiftedLiftPermutation p c h a)=(n : ℤ)-1-h := by
  let q := shiftedLiftPermutation p c h
  let b := q a
  have hba : q b=a := hinv a
  have hab : a.val < b.val := by change a.val+1=b.val at ha; omega
  have heq : (fun i : Fin n => (i : ℤ)+d i+h)=clockwiseRepresentative q :=
    clockwise_representative_unique q _ (fun i => by have := hband i; omega)
      (shifted_lift_permutation_modEq hd h)
  have hb := congrFun heq b
  simp only [clockwiseRepresentative,hba,if_pos hab] at hb
  change a.val+1=b.val at ha
  change d b=(n : ℤ)-1-h
  omega

/-- The even strict band is too narrow for the reverse arrow of an adjacent pair. -/
theorem shifted_no_adjacent_of_narrow_strip {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ))
    (hupper : ∀ i, d i ≤ h) (hn : 2*h+1 < (n : ℤ))
    (hinv : Function.Involutive (shiftedLiftPermutation p c h)) :
    ∀ a : Fin n, a.val+1 ≠ (shiftedLiftPermutation p c h a).val := by
  intro a ha
  have hr := shifted_adjacent_reverse_coordinate hd h hband hinv a ha
  have hu := hupper (shiftedLiftPermutation p c h a)
  omega

/-- In the odd band, distinct adjacent pairs would yield two inherited positive extremes. -/
theorem shifted_unique_adjacent_of_inherited_extremes {p : State n} {c : ℤ}
    {original d : Fin n → ℤ} (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p c d) (h : ℤ) (hn : (n : ℤ)=2*h+1)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ))
    (hinherit : ∀ i, d i=h → original i=h)
    (hinv : Function.Involutive (shiftedLiftPermutation p c h)) :
    ∀ a b : Fin n, a.val+1=(shiftedLiftPermutation p c h a).val →
      b.val+1=(shiftedLiftPermutation p c h b).val → a=b := by
  classical
  have hc := AffineLift.majorized_level_count hmaj h (by omega)
  have hc1 : (Finset.univ.filter (fun i => original i=h)).card ≤ 1 := by omega
  intro a b ha hb
  have ha' := shifted_adjacent_reverse_coordinate hd h hband hinv a ha
  have hb' := shifted_adjacent_reverse_coordinate hd h hband hinv b hb
  have hma : shiftedLiftPermutation p c h a ∈ Finset.univ.filter (fun i => original i=h) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hinherit _ (by omega)⟩
  have hmb : shiftedLiftPermutation p c h b ∈ Finset.univ.filter (fun i => original i=h) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hinherit _ (by omega)⟩
  exact (shiftedLiftPermutation p c h).injective (Finset.card_le_one.mp hc1 _ hma _ hmb)

/-- Strict shortness supplies the symmetric integer bound, including the tighter even case. -/
theorem strict_short_upper (d : Fin n → ℤ) (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    ∀ i, d i ≤ (((n-1)/2 : ℕ) : ℤ) := by
  intro i
  have hh := hshort i
  have hu := le_abs_self (d i)
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  omega

#print axioms shifted_adjacent_reverse_coordinate
#print axioms shifted_no_adjacent_of_narrow_strip
#print axioms shifted_unique_adjacent_of_inherited_extremes
end LRX.FiniteCuts
