import LX.HigherPhasePayment

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

noncomputable def higherForwardMinima (p : State n) (m : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => GlobalMinimum p i ∧ height p i=m ∧ i.val < (p i).val

/-- In an unpaid odd input, the forward global maxima can occupy only a
short interval of displacement values, four terminal values, and the head.
The count is reduced by the actual dimension-wide exchange reserve. -/
theorem odd_unpaid_higher_forward_count {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (hn4 : 4 ≤ n) (m R : ℕ) (hn : n=2*m+1)
    (hR : inversions (displacement p a)+R=m*m)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    (higherForwardMinima p m).card ≤ (m-R-31)+5 := by
  classical
  let P := higherForwardMinima p m
  let span := fun i : Fin n => (p i).val-i.val
  have hmem (i : Fin n) (hi : i ∈ P) :
      GlobalMinimum p i ∧ height p i=m ∧ i.val < (p i).val :=
    (Finset.mem_filter.mp hi).2
  have hinj : Set.InjOn span P := by
    intro i hi j hj he
    have hi' := hmem i hi
    have hj' := hmem j hj
    have hf := odd_higher_fixed_unique p j (global_minimum_majorized hj'.1) (by omega)
    apply one_fixed_last_offset p j hf i
    have hc := congrArg (fun z : ℕ => (z : Fin n)) he
    simpa only [span,Nat.cast_sub (Nat.le_of_lt hi'.2.2),
      Nat.cast_sub (Nat.le_of_lt hj'.2.2),Fin.cast_val_eq_self] using hc
  have hreserve (i : Fin n) (hi : i ∈ P) : anchorReserve p i=R := by
    have hm := hmem i hi
    have hI : inversions (displacement p i)=inversions (displacement p a) :=
      Nat.le_antisymm (global_minimum_exchanges hm.1 a) (global_minimum_exchanges ha i)
    unfold anchorReserve
    rw [hm.2.1,hI]
    have hn' : (n : ℤ)=2*(m : ℤ)+1 := by exact_mod_cast hn
    have hR' : (inversions (displacement p a) : ℤ)+(R : ℤ)=(m : ℤ)*(m : ℤ) := by exact_mod_cast hR
    nlinarith
  let U : Finset ℕ := (Finset.Icc 1 (m-R-31) ∪ Finset.Icc (n-4) (n-1)) ∪ {span 0}
  have hsub : P.image span ⊆ U := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hm := hmem i hi
    by_cases hi0 : i=0
    · subst i
      simp [U]
    · have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
      by_cases hlow : span i ≤ m-R-31
      · have hspos : 0 < span i := by dsimp [span]; omega
        simp only [U,Finset.mem_union,Finset.mem_Icc,Finset.mem_singleton]
        exact Or.inl (Or.inl ⟨hspos,hlow⟩)
      · have hshort : i.val+(-p i).val < 5 := by
          by_contra hnot
          have hb := odd_unpaid_higher_forward_span hm.1 hn4 (by omega) hip hm.2.2 (by omega) hunpaid
          rw [hm.2.1,hreserve i hi] at hb
          dsimp [span] at hlow
          omega
        have hne : p i ≠ 0 := by intro he; rw [he,Fin.val_zero] at hm; omega
        have hneg : (-p i).val=n-(p i).val := by simp [Fin.val_neg,hne]
        rw [hneg] at hshort
        have hpi := (p i).isLt
        have hbounds : n-4 ≤ span i ∧ span i ≤ n-1 := by dsimp [span]; omega
        simp only [U,Finset.mem_union,Finset.mem_Icc,Finset.mem_singleton]
        exact Or.inl (Or.inr hbounds)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj] at hc
  have hu := Finset.card_union_le (Finset.Icc 1 (m-R-31) ∪ Finset.Icc (n-4) (n-1)) {span 0}
  have hu' := Finset.card_union_le (Finset.Icc 1 (m-R-31)) (Finset.Icc (n-4) (n-1))
  change U.card ≤ _ at hu
  simp only [Nat.card_Icc,Finset.card_singleton] at hu hu'
  change P.card ≤ _
  omega

/-- A countable property of the original global phases now supplies a
literal word with the target quadratic and linear terms. -/
theorem odd_many_higher_forward_minima_upper_word {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (hn4 : 4 ≤ n) (m R : ℕ) (hn : n=2*m+1)
    (hR : inversions (displacement p a)+R=m*m)
    (hcount : (m-R-31)+5 < (higherForwardMinima p m).card) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_contra hunpaid
  have hc := odd_unpaid_higher_forward_count ha hn4 m R hn hR hunpaid
  omega

#print axioms odd_unpaid_higher_forward_count
#print axioms odd_many_higher_forward_minima_upper_word
end LX.AnchoredPhases
