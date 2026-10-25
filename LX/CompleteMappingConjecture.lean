import LX.CompleteMappingSharpScan
import LX.ConstantHeightEvenGeometry
import LX.EvenOneFixedObstruction
import LX.HigherPhasePayment
import LX.ReflectionPhases
import LX.Small5
import LX.ZeroExchangeReserve
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem complete_anchor_reserve_word (p : State n) (hp : CompleteMapping p)
    (hn : 5 ≤ n) (a : Fin n) (k : ℕ) (ha : 0 < a.val)
    (hforward : a.val+height p a ≤ (p a).val+k)
    (hcorner : 3 ≤ a.val+(n-(p a).val)) (hk : k < height p a) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+4*(k+1-anchorReserve p a)+1 := by
  let h := height p a
  have hparity : n=2*h+1 := complete_height p hp a
  have hall (a : Fin n) : height p a=h := by
    have := complete_height p hp a
    omega
  have hfixed (a : Fin n) : (fixedPositions (permutation p a)).card=1 :=
    odd_higher_fixed_unique p a (complete_majorized p hp a) (complete_height p hp a)
  have hhead : p 0 ≠ p a-a := by
    intro he
    have hz := one_fixed_last_offset p a (hfixed a) 0 (by simpa using he)
    have hv := congrArg Fin.val hz
    simp only [Fin.val_zero] at hv
    omega
  have hlast (i : Fin n) (hi : p i-i=p a-a) : i.val ≤ a.val := by
    rw [one_fixed_last_offset p a (hfixed a) i hi]
  have hne : p a ≠ 0 := by
    intro he
    rw [he,Fin.val_zero] at hforward
    omega
  have hneg : (-p a).val=n-(p a).val := by simp [Fin.val_neg,hne]
  have hc := constant_height_next_depth p h 1 hall (fun b => (hfixed b).le) (by omega) a
  have hcount : depthCount (displacement p a) (height p a-1) ≤ a.val+(-p a).val := by
    rw [hall a,hneg]
    omega
  obtain ⟨w,hw,hprice⟩ := odd_higher_anchor_reserve_price p a (by omega)
    (complete_height p hp a) hhead hlast hcount
  rw [hneg,hall a] at hprice
  exact ⟨w,hw,by omega⟩

omit [NeZero n] in
/-- Explicit good phases for odd reflections, including size five. -/
theorem odd_reflection_sharp_anchor (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m+1) (hm : 2 ≤ m) :
    ∃ a : Fin n,0 < a.val ∧ a.val+m ≤ (p a).val+1 ∧
      3 ≤ a.val+(n-(p a).val) := by
  by_cases hr : m+1 ≤ r.val
  · let a : Fin n := ⟨1,by omega⟩
    have ha : a.val=1 := rfl
    have hle : a ≤ r := by change a.val ≤ r.val; omega
    refine ⟨a,by omega,?_,?_⟩ <;> rw [hp,Fin.coe_sub_iff_le.mpr hle]
    all_goals have := r.isLt; omega
  · by_cases he : r.val=m
    · let a : Fin n := ⟨m+1,by omega⟩
      have ha : a.val=m+1 := rfl
      have hlt : r < a := by change r.val < a.val; omega
      refine ⟨a,by omega,?_,?_⟩ <;> rw [hp,Fin.coe_sub_iff_lt.mpr hlt]
      all_goals omega
    · by_cases hz : r.val=0
      · let a : Fin n := ⟨2,by omega⟩
        have ha : a.val=2 := rfl
        have hlt : r < a := by change r.val < a.val; omega
        refine ⟨a,by omega,?_,?_⟩ <;> rw [hp,Fin.coe_sub_iff_lt.mpr hlt]
        all_goals omega
      · let a : Fin n := ⟨r.val+1,by omega⟩
        have ha : a.val=r.val+1 := rfl
        have hlt : r < a := by change r.val < a.val; omega
        refine ⟨a,by omega,?_,?_⟩ <;> rw [hp,Fin.coe_sub_iff_lt.mpr hlt]
        all_goals omega

theorem odd_reflection_conjecture_word (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m+1) (hm : 2 ≤ m) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
  have hc := reflection_complete_odd p r hp m hn
  obtain ⟨a,ha,hforward,hcorner⟩ := odd_reflection_sharp_anchor p r hp m hn hm
  have hh : height p a=m := by have := complete_height p hc a; omega
  obtain ⟨w,hw,hprice⟩ := complete_anchor_reserve_word p hc (by omega) a 1 ha
    (by omega) hcorner (by omega)
  have hr := anchor_reserve_nonneg p a
  exact ⟨w,hw,by omega⟩

theorem complete_mapping_conjecture_word_large (p : State n) (hp : CompleteMapping p)
    (hn : 7 ≤ n) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
  let h := height p 0
  have hparity : n=2*h+1 := complete_height p hp 0
  obtain ⟨a,ha,hforward,hcorner⟩ := complete_good_anchor_two p hp h hparity (by omega)
  have hh : height p a=h := by have := complete_height p hp a; omega
  by_cases hr : 1 ≤ anchorReserve p a
  · obtain ⟨w,hw,hprice⟩ := complete_anchor_reserve_word p hp (by omega) a 2 ha
      (by omega) hcorner (by omega)
    exact ⟨w,hw,by omega⟩
  · have hz : anchorReserve p a=0 := by have := anchor_reserve_nonneg p a; omega
    have hn2 : n/2=h := by omega
    have heq : (inversions (displacement p a) : ℤ)=
        ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ) := by
      unfold anchorReserve at hz
      rw [hn2,hh] at *
      have hn' : (n : ℤ)=2*(h : ℤ)+1 := by exact_mod_cast hparity
      nlinarith only [hz,hn']
    obtain ⟨r,href⟩ := majorized_capacity_reflection (is_lift p a) (complete_majorized p hp a) heq
    exact odd_reflection_conjecture_word p r href h hparity (by omega)

theorem complete_mapping_conjecture_word (p : State n) (hp : CompleteMapping p)
    (hn : 4 ≤ n) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
  by_cases hlarge : 7 ≤ n
  · exact complete_mapping_conjecture_word_large p hp hlarge
  · have hn5 : n=5 := by have := complete_height p hp 0; omega
    subst n
    obtain ⟨w,hw,hprice⟩ := LX.Small5.sharp_words p⁻¹
    exact ⟨w,by rw [hw,mul_inv_cancel],by norm_num; omega⟩

#print axioms complete_mapping_conjecture_word
#print axioms complete_anchor_reserve_word
#print axioms odd_reflection_conjecture_word
#print axioms complete_mapping_conjecture_word_large
end LX.AnchoredPhases
