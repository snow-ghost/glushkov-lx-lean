import LRX.RankHoleCoordinates

namespace LRX.ContractionBlocks
open scoped BigOperators
variable {m : ℕ}

theorem physical_sum_forward (holes : Fin m → ℤ) (hh : ∀ j, 0 ≤ holes j)
    (S : Finset (Fin (m+1))) (u v : Fin (m+1) → Fin (m+1))
    (huv : ∀ x ∈ S, u x ≤ v x) :
    (∑ x ∈ S, |position holes (v x)-position holes (u x)|) =
      (∑ x ∈ S, ((v x : ℤ)-(u x : ℤ))) +
      ∑ j, ((S.filter (fun x => (u x).val ≤ j.val ∧ j.val < (v x).val)).card : ℤ)*holes j := by
  have he : ∀ x ∈ S, |position holes (v x)-position holes (u x)| =
      (v x : ℤ)-(u x : ℤ)+∑ j, if (u x).val ≤ j.val ∧ j.val < (v x).val then holes j else 0 := by
    intro x hx
    rw [abs_of_nonneg (sub_nonneg.mpr (position_mono holes hh (huv x hx)))]
    exact position_difference holes (u x) (v x) (huv x hx)
  rw [Finset.sum_congr rfl he,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [Finset.sum_ite]

namespace System
variable {k : ℕ} {P : State (m+1)} {q : State k}

def physicalLength (S : Finset (Fin (m+1))) (P : State (m+1)) (f : Fin (m+1) → ℤ) : ℤ :=
  ∑ x ∈ S, |f (P x)-f x|

theorem positive_physical_decomposition (B : System P q)
    (holes : Fin m → ℤ) (hh : ∀ j, 0 ≤ holes j) :
    physicalLength B.positive P (position holes)=rankLength B.positive P+
      ∑ j, ((B.upward j.val).card : ℤ)*holes j := by
  have he := physical_sum_forward holes hh B.positive id P (by
    intro x hx
    have hp := (Finset.mem_filter.mp hx).2
    exact le_of_lt hp)
  have hc : ∀ j : Fin m, B.positive.filter (fun x => x.val ≤ j.val ∧ j.val < (P x).val)=B.upward j.val := by
    intro j
    ext x
    simp only [positive,upward,Finset.mem_filter]
    constructor
    · rintro ⟨⟨hs,_⟩,hcut⟩; exact ⟨hs,hcut⟩
    · rintro ⟨hs,hcut⟩; exact ⟨⟨hs,by omega⟩,hcut⟩
  have hr : (∑ x ∈ B.positive, ((P x : ℤ)-(x : ℤ)))=rankLength B.positive P := by
    apply Finset.sum_congr rfl
    intro x hx
    have hp := (Finset.mem_filter.mp hx).2
    exact (abs_of_nonneg (by omega)).symm
  simpa only [id_eq,hc,hr,physicalLength] using he

theorem negative_physical_decomposition (B : System P q)
    (holes : Fin m → ℤ) (hh : ∀ j, 0 ≤ holes j) :
    physicalLength B.negative P (position holes)=rankLength B.negative P+
      ∑ j, ((B.downward j.val).card : ℤ)*holes j := by
  have he := physical_sum_forward holes hh B.negative P id (by
    intro x hx
    have hp := (Finset.mem_filter.mp hx).2
    exact le_of_lt hp)
  have hc : ∀ j : Fin m, B.negative.filter (fun x => (P x).val ≤ j.val ∧ j.val < x.val)=B.downward j.val := by
    intro j
    ext x
    simp only [negative,downward,Finset.mem_filter]
    constructor
    · rintro ⟨⟨hs,_⟩,hcut⟩; exact ⟨hs,hcut⟩
    · rintro ⟨hs,hcut⟩; exact ⟨⟨hs,by omega⟩,hcut⟩
  have hr : (∑ x ∈ B.negative, ((x : ℤ)-(P x : ℤ)))=rankLength B.negative P := by
    apply Finset.sum_congr rfl
    intro x hx
    have hp := (Finset.mem_filter.mp hx).2
    rw [abs_of_nonpos (by omega)]
    ring
  simp only [id_eq,hc,hr] at he
  unfold physicalLength
  rw [show (∑ x ∈ B.negative, |position holes (P x)-position holes x|)=
      ∑ x ∈ B.negative, |position holes x-position holes (P x)| by
    apply Finset.sum_congr rfl
    intro x _
    exact abs_sub_comm _ _]
  exact he

#print axioms positive_physical_decomposition
#print axioms negative_physical_decomposition
end System
end LRX.ContractionBlocks
