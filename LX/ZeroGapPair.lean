import Mathlib

/-! Every nonzero balanced displacement vector has an oppositely signed pair
with no nonzero displacement in the open forward arc between its endpoints. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def distance (u v : Fin n) : ℕ := (v-u).val

theorem balanced_signs (d : Fin n → ℤ) (hd : ∑ i, d i=0) (hne : ∃ i, d i ≠ 0) :
    (∃ u, 0 < d u) ∧ (∃ v, d v < 0) := by
  constructor
  · by_contra h
    push Not at h
    have hz : ∑ i : Fin n, -d i=0 := by rw [Finset.sum_neg_distrib,hd,neg_zero]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => neg_nonneg.mpr (h i))).mp hz
    obtain ⟨i,hi⟩ := hne
    have he := hall i (Finset.mem_univ i)
    exact hi (by omega)
  · by_contra h
    push Not at h
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h i)).mp hd
    obtain ⟨i,hi⟩ := hne
    exact hi (hall i (Finset.mem_univ i))

theorem distance_split (u v j : Fin n) (hj : distance u j ≤ distance u v) :
    distance j v=distance u v-distance u j := by
  have he : v-j=(v-u)-(j-u) := by ring
  unfold distance at *
  rw [he,Fin.sub_val_of_le (show j-u ≤ v-u from hj)]

theorem exists_zero_gap (d : Fin n → ℤ) (hd : ∑ i, d i=0) (hne : ∃ i, d i ≠ 0) :
    ∃ u v : Fin n, 0 < d u ∧ d v < 0 ∧ 0 < distance u v ∧
      ∀ j, 0 < distance u j → distance u j < distance u v → d j=0 := by
  classical
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := balanced_signs d hd hne
  let pairs := Finset.univ.filter (fun uv : Fin n × Fin n => 0 < d uv.1 ∧ d uv.2 < 0)
  have hnon : pairs.Nonempty := ⟨(u,v),by simp [pairs,hu,hv]⟩
  obtain ⟨uv,huv,hmin⟩ := pairs.exists_min_image (fun uv => distance uv.1 uv.2) hnon
  obtain ⟨hpos,hneg⟩ := (Finset.mem_filter.mp huv).2
  have hneuv : uv.1 ≠ uv.2 := by intro h; rw [h] at hpos; omega
  have hdist : 0 < distance uv.1 uv.2 := by
    by_contra h
    have he : uv.2-uv.1=0 := Fin.ext (by change distance uv.1 uv.2=0; omega)
    exact hneuv (sub_eq_zero.mp he).symm
  refine ⟨uv.1,uv.2,hpos,hneg,hdist,?_⟩
  intro j hj hj'
  by_contra hn
  by_cases hp : 0 < d j
  · have hm := hmin (j,uv.2) (by simp [pairs,hp,hneg])
    have hs := distance_split uv.1 uv.2 j (by omega)
    change distance uv.1 uv.2 ≤ distance j uv.2 at hm
    omega
  · have hjn : d j < 0 := by omega
    have hm := hmin (uv.1,j) (by simp [pairs,hpos,hjn])
    change distance uv.1 uv.2 ≤ distance uv.1 j at hm
    omega

#print axioms exists_zero_gap
end LX.Core.ZeroGap
