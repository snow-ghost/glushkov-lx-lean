import LRX.FinitePermutationProfile

/-! Integer load profiles and their exact area as a sum of superlevel widths. -/
namespace LRX.DiscreteLoad
open scoped BigOperators

structure Profile (b : ℕ) where
  height : ℕ → ℕ
  at_zero : height 0=0
  at_end : height b=0
  step_up : ∀ j, j < b → height (j+1) ≤ height j+1
  step_down : ∀ j, j < b → height j ≤ height (j+1)+1

variable {b : ℕ}

def area (P : Profile b) : ℕ := ∑ j ∈ Finset.range (b+1), P.height j

def peak (P : Profile b) : ℕ := (Finset.range (b+1)).sup P.height

def leftPeak (P : Profile b) (y : ℕ) : ℕ := (Finset.range (y+1)).sup P.height

def rightPeak (P : Profile b) (x : ℕ) : ℕ := (Finset.Icc x b).sup P.height

def level (P : Profile b) (h : ℕ) : Finset ℕ := (Finset.range (b+1)).filter (fun j => h < P.height j)

theorem height_step (P : Profile b) (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ b) :
    P.height y ≤ P.height x+(y-x) ∧ P.height x ≤ P.height y+(y-x) := by
  have hiter : ∀ k : ℕ, x+k ≤ b →
      P.height (x+k) ≤ P.height x+k ∧ P.height x ≤ P.height (x+k)+k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hu,hd⟩ := ih (by omega)
      have h1 := P.step_up (x+k) (by omega)
      have h2 := P.step_down (x+k) (by omega)
      have he : x+(k+1)=x+k+1 := by omega
      rw [he]
      constructor <;> omega
  simpa only [Nat.add_sub_of_le hxy] using hiter (y-x) (by omega)

theorem height_capacity (P : Profile b) (j : ℕ) (hj : j ≤ b) :
    P.height j ≤ j ∧ P.height j ≤ b-j := by
  have h1 := (height_step P 0 j (by omega) hj).1
  have h2 := (height_step P j b hj le_rfl).2
  rw [P.at_zero] at h1
  rw [P.at_end] at h2
  omega

theorem height_le_peak (P : Profile b) (j : ℕ) (hj : j ≤ b) : P.height j ≤ peak P :=
  Finset.le_sup (Finset.mem_range.mpr (by omega))

theorem peak_attained (P : Profile b) : ∃ j ≤ b, P.height j=peak P := by
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup (Finset.range (b+1)) ⟨0,by simp⟩ P.height
  exact ⟨j,by simpa using hj,he.symm⟩

theorem twice_peak_le (P : Profile b) : 2*peak P ≤ b := by
  obtain ⟨j,hj,he⟩ := peak_attained P
  obtain ⟨hlo,hhi⟩ := height_capacity P j hj
  omega

theorem left_peak_le (P : Profile b) (y : ℕ) (hy : y ≤ b) : leftPeak P y ≤ peak P := by
  apply Finset.sup_le
  intro j hj
  exact height_le_peak P j (by have := Finset.mem_range.mp hj; omega)

theorem area_by_levels (P : Profile b) : area P=∑ h ∈ Finset.range (peak P), (level P h).card := by
  unfold area level
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hheight := height_le_peak P j (by have := Finset.mem_range.mp hj; omega)
  have he : (Finset.range (peak P)).filter (fun h => h < P.height j)=Finset.range (P.height j) := by
    ext h
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  have hc := congrArg Finset.card he
  simpa only [Finset.card_filter,Finset.card_range] using hc.symm

end LRX.DiscreteLoad
namespace LRX.FiniteCuts
variable {b : ℕ}

def discreteProfile (p : State b) : DiscreteLoad.Profile b where
  height := halfLoad p
  at_zero := half_load_zero p
  at_end := half_load_end p
  step_up := half_load_succ_upper p
  step_down := half_load_succ_lower p

end LRX.FiniteCuts
#print axioms LRX.DiscreteLoad.area_by_levels
