import LX.CompleteMappingConjecture
import LX.Small4
import LX.Small6

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- The actual constant-height geometry pays every even reflection at the
conjectured constant three, without a large-size assumption. -/
theorem even_reflection_conjecture_word (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m) (hm : 2 ≤ m) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
  by_cases hsmall : n ≤ 6
  · have hc : n=4 ∨ n=6 := by omega
    rcases hc with rfl | rfl
    · obtain ⟨w,hw,hprice⟩ := LX.Small4.sharp_words p⁻¹
      exact ⟨w,by rw [hw,mul_inv_cancel],by norm_num; omega⟩
    · obtain ⟨w,hw,hprice⟩ := LX.Small6.sharp_words p⁻¹
      exact ⟨w,by rw [hw,mul_inv_cancel],by norm_num; omega⟩
  have hall (a : Fin n) : height p a=m-1 := reflection_height_even p r hp m hn hm a
  have hF (a : Fin n) : (fixedPositions (permutation p a)).card ≤ 2 := by
    have hc := top_depth_count (is_lift p a)
      (global_minimum_majorized (reflection_global_minimum p r hp a))
      (height p a) (by have := hall a; omega)
      (fun i => by exact_mod_cast (candidate_price_components p a).2 i)
    rw [top_depth_count_eq_fixed] at hc
    have := hall a
    omega
  have hgood : ∃ a : Fin n,m < a.val ∧ a.val+(-p a).val ≤ n+2 := by
    by_cases hr : m < r.val
    · refine ⟨r,hr,?_⟩
      simp only [hp,sub_self,neg_zero,Fin.val_zero,add_zero]
      have := r.isLt
      omega
    · let a : Fin n := ⟨m+1,by omega⟩
      refine ⟨a,by dsimp [a]; omega,?_⟩
      have he : -p a=a-r := by rw [hp]; abel
      rw [he,Fin.coe_sub_iff_le.mpr (show r ≤ a by change r.val ≤ a.val; dsimp [a]; omega)]
      dsimp [a]
      omega
  obtain ⟨a,ha,hfinish⟩ := hgood
  obtain ⟨hdepthhead,hlastdepth⟩ := reflection_depth_positions_even p r hp m hn hm a ha
  have hfixed (i : Fin n) (hi : p i-i=p a-a) : permutation p a i=i := by
    change p i+(a-p a)=i
    linear_combination hi
  have hhead : p 0 ≠ p a-a := by
    intro he
    have hd := (depth_eq_height_iff_fixed p a 0).mpr (hfixed 0 (by simpa using he))
    omega
  have hlast (i : Fin n) (hi : p i-i=p a-a) : i.val ≤ a.val :=
    hlastdepth i ((depth_eq_height_iff_fixed p a i).mpr (hfixed i hi))
  have hc := constant_height_next_depth p (m-1) 2 hall hF (by omega) a
  have hh := hall a
  have hcount : depthCount (displacement p a) (height p a-1) ≤ a.val+(-p a).val := by
    rw [hh]
    omega
  obtain ⟨w,hw,hprice⟩ := even_anchor_reserve_price p a (by omega) (by omega) hhead hlast hcount
  have hr := anchor_reserve_nonneg p a
  exact ⟨w,hw,by omega⟩

theorem even_zero_reserve_conjecture_word (p : State n) (a : Fin n)
    (ha : GlobalMinimum p a) (hn4 : 4 ≤ n) (hn : n=2*height p a+2)
    (hz : anchorReserve p a=0) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
  have hn2 : n/2=height p a+1 := by omega
  have heq : (inversions (displacement p a) : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ) := by
    unfold anchorReserve at hz
    rw [hn2]
    push_cast
    have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
    nlinarith only [hz,hn']
  obtain ⟨r,hr⟩ := zero_exchange_reserve_reflection ha heq
  exact even_reflection_conjecture_word p r hr (n/2) (by omega) (by omega)

#print axioms even_reflection_conjecture_word
#print axioms even_zero_reserve_conjecture_word
end LX.AnchoredPhases
