import LX.AntipodeHeightReduction

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def center (m : ℕ) (z : ℤ) : ℤ := (z+m) % (n : ℤ)-m

theorem center_bounds (m : ℕ) (z : ℤ) :
    -(m : ℤ) ≤ center (n := n) m z ∧ center (n := n) m z < (n : ℤ)-m := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hlo := Int.emod_nonneg (z+m) (ne_of_gt hn)
  have hhi := Int.emod_lt_of_pos (z+m) hn
  unfold center
  omega

theorem center_cast (m : ℕ) (z : ℤ) : ((center (n := n) m z : ℤ) : Fin n)=(z : Fin n) := by
  apply (LRX.LiftedModel.cast_eq_iff_modEq _ _).mpr
  apply Int.modEq_iff_dvd.mpr
  refine ⟨(z+m)/(n : ℤ),?_⟩
  have he := Int.ediv_mul_add_emod (z+m) (n : ℤ)
  unfold center
  nlinarith

theorem center_add (m : ℕ) (z t : ℤ) :
    center (n := n) m (z+t)=center (n := n) m (center (n := n) m z+t) := by
  unfold center
  have h1 : z+t+m=(z+m)+t := by ring
  have h2 : (z+m)%(n : ℤ)-m+t+m=(z+m)%(n : ℤ)+t := by ring
  rw [h1,h2]
  simp only [Int.add_emod,Int.emod_emod]

theorem le_center_of_below_top (m : ℕ) (z : ℤ) (hz : z < (n : ℤ)-m) :
    z ≤ center (n := n) m z := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hq := (Int.ediv_lt_iff_lt_mul hn).mpr (show z+m < (1 : ℤ)*n by omega)
  have hm := mul_nonpos_of_nonpos_of_nonneg (show (z+m)/(n : ℤ) ≤ 0 by omega) (le_of_lt hn)
  have he := Int.ediv_mul_add_emod (z+m) (n : ℤ)
  unfold center
  omega

theorem sub_period_le_center_of_at_top (m : ℕ) (z : ℤ) (hz : z ≤ (n : ℤ)-m) :
    z-n ≤ center (n := n) m z := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hq := (Int.ediv_lt_iff_lt_mul hn).mpr (show z+m < (2 : ℤ)*n by omega)
  have hm := mul_le_mul_of_nonneg_right (show (z+m)/(n : ℤ) ≤ 1 by omega) (le_of_lt hn)
  have he := Int.ediv_mul_add_emod (z+m) (n : ℤ)
  unfold center
  nlinarith

/-- Increasing an input by at most one can wrap down only at the top
representative. Larger downward changes can only increase the remainder. -/
theorem center_perturb_lower (m : ℕ) (z t : ℤ) (ht : t ≤ 1) :
    center (n := n) m z+t-(if center (n := n) m z=(n : ℤ)-m-1 then n else 0) ≤
      center (n := n) m (z+t) := by
  rw [center_add]
  have hb := center_bounds (n := n) m z
  by_cases he : center (n := n) m z=(n : ℤ)-m-1
  · rw [ite_eq_left he]
    exact sub_period_le_center_of_at_top m _ (by omega)
  · rw [ite_eq_right he,Nat.cast_zero,sub_zero]
    exact le_center_of_below_top m _ (by omega)

def raiseAt (e : Fin n → ℤ) (a : Fin n) (i : Fin n) : ℤ := e i+if i=a then n else 0

/-- A balanced lift above the lower edge differs from a strip
representative of mass at least -n in at most one raised coordinate. -/
theorem balanced_single_raise (m : ℕ) (d e : Fin n → ℤ)
    (hd : ∑ i,d i=0) (hlo : ∀ i,-(m : ℤ) ≤ d i)
    (he : ∀ i,-(m : ℤ) ≤ e i ∧ e i < (n : ℤ)-m)
    (hres : ∀ i,(d i : Fin n)=(e i : Fin n))
    (hs : -(n : ℤ) ≤ ∑ i,e i) : d=e ∨ ∃ a,d=raiseAt e a := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  let δ : Fin n → ℤ := fun i => d i-e i
  have hgap (i : Fin n) : δ i=0 ∨ (n : ℤ) ≤ δ i := by
    have hmod := (LRX.LiftedModel.cast_eq_iff_modEq _ _).mp (hres i).symm
    obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp hmod
    change δ i=(n : ℤ)*k at hk
    have hδ : -(n : ℤ) < δ i := by have := hlo i; have := he i; dsimp [δ]; omega
    have hk0 : 0 ≤ k := by
      by_contra hnot
      have hm := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) (le_of_lt hn)
      nlinarith
    by_cases hkz : k=0
    · left; simp [hk,hkz]
    · right
      have hm := mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) (le_of_lt hn)
      nlinarith
  have hnonneg (i : Fin n) : 0 ≤ δ i := by have := hgap i; omega
  have htotal : (∑ i,δ i) ≤ (n : ℤ) := by
    simp only [δ,Finset.sum_sub_distrib,hd]
    omega
  by_cases hz : ∀ i,δ i=0
  · left; funext i; have := hz i; dsimp [δ] at this; omega
  · obtain ⟨a,ha⟩ := not_forall.mp hz
    have hamin := (hgap a).resolve_left ha
    have hale := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hnonneg i)
      (Finset.mem_univ a)
    have hea : δ a=n := by omega
    have herase := Finset.sum_erase_add (s := Finset.univ) (f := δ) (Finset.mem_univ a)
    have hrest : (∑ i ∈ Finset.univ.erase a,δ i) ≤ 0 := by omega
    right
    refine ⟨a,?_⟩
    funext i
    by_cases hi : i=a
    · subst i; simp only [raiseAt,ite_true]; dsimp [δ] at hea; omega
    · have hile := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ.erase a) => hnonneg j)
        (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩)
      simp only [raiseAt,ite_eq_right hi,Nat.cast_zero,add_zero]
      have hzi : δ i=0 := by have := hnonneg i; omega
      dsimp only [δ] at hzi
      omega

#print axioms balanced_single_raise
end LX.CenteredLift
