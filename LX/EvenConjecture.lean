import LX.EvenUnpaidHeadPattern
import LX.ReverseDual
import LX.EvenAntipodeLower

namespace LX
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Every even input is sorted at the conjectured constant three. Applying
the necessary head pattern to the mirrored inverse excludes every unpaid
input; no phase-selection premise remains. -/
theorem even_sorting_word_conjecture (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
  by_contra hunpaid
  have hp := AnchoredPhases.even_global_unpaid_head_pattern hn4 p m hn hunpaid
  have hdual : ¬ ∃ w : List Letter,reverseDual p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w.reverse,reverse_dual_sorting_word p w hw,by simpa using hprice⟩
  have hq := AnchoredPhases.even_global_unpaid_head_pattern hn4 (reverseDual p) m hn hdual
  have hq0 : (1 : Fin n)-p.symm 1=0 := by
    simpa only [reverseDual,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,
      LRX.WordReflection.reflection_apply,sub_zero] using hq.1
  have hi : p.symm 1=1 := by linear_combination -hq0
  have hp1 : p 1=1 := by
    have he := p.apply_symm_apply 1
    rw [hi] at he
    exact he
  have hone : (1 : Fin n)= -1 := hp1.symm.trans hp.2
  have htwo : (2 : Fin n)=0 := by linear_combination hone
  have hv2 : (2 : Fin n).val=2 := by simp [Nat.mod_eq_of_lt (show 2<n by omega)]
  have hv := congrArg Fin.val htwo
  rw [hv2,Fin.val_zero] at hv
  omega

theorem even_exists_word_conjecture (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m) :
    ∃ w : List Letter,eval w=p ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
  obtain ⟨w,hw,hprice⟩ := even_sorting_word_conjecture hn4 p⁻¹ m hn
  exact ⟨w,(inv_mul_eq_one.mp hw).symm,hprice⟩

theorem even_diameter_conjecture_upper (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) :
    (diameter n : ℚ) ≤ (3*(n : ℚ)^2-8*n+12)/4 := by
  obtain ⟨p,_,hp⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (State n)) ⟨1,Finset.mem_univ _⟩ length
  obtain ⟨w,hw,hprice⟩ := even_exists_word_conjecture hn4 p m hn
  have hd : diameter n=length p := hp
  have hlen : length p ≤ w.length := hw ▸ length_le_word w
  have hprice' : 4*(w.length : ℚ) ≤ 3*(n : ℚ)^2-8*n+12 := by exact_mod_cast hprice
  have hlen' : (length p : ℚ) ≤ w.length := by exact_mod_cast hlen
  rw [hd]
  linarith

/-- The exact conjectured directed LX diameter for every even n > 4. -/
theorem even_diameter_conjecture (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    (diameter n : ℚ)=(3*(n : ℚ)^2-8*n+12)/4 := by
  apply le_antisymm
  · exact even_diameter_conjecture_upper (by omega) m hn
  · exact Antipode.even_diameter_conjecture_lower m hm hn

#print axioms even_sorting_word_conjecture
#print axioms even_exists_word_conjecture
#print axioms even_diameter_conjecture_upper
#print axioms even_diameter_conjecture
end LX
