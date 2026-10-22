import LX.FiniteDropBudget
import LX.EvenSecondOrientation

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.FiniteDropBudget
variable {n : ℕ} [NeZero n]

/-- Minimum height permits at most one linear backward unit arrow. -/
theorem minimum_height_backward_units (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) :
    (backwardUnits (permutation p a)).card ≤ 1 := by
  classical
  have hr := minimum_height_ranks p a hmin (n-1) (by omega)
  let S := Finset.univ.filter fun i => (cyclicOffset p a i).val < n-1
  have hd : Disjoint S (backwardUnits (permutation p a)) := by
    apply Finset.disjoint_left.mpr
    intro i hs hu
    have hu : (permutation p a i).val+1=i.val := (Finset.mem_filter.mp hu).2
    have hv : (cyclicOffset p a i).val=n-1 := by
      rw [cyclic_offset_normalized,Fin.coe_sub_iff_lt.mpr
        (show permutation p a i < i by change (permutation p a i).val < i.val; omega)]
      omega
    have hs : (cyclicOffset p a i).val < n-1 := (Finset.mem_filter.mp hs).2
    omega
  have hc := Finset.card_le_card (Finset.subset_univ (S ∪ backwardUnits (permutation p a)))
  rw [Finset.card_union_of_disjoint hd,Finset.card_univ,Fintype.card_fin] at hc
  change n-1 ≤ S.card at hr
  have := NeZero.pos n
  omega

/-- The initial fixed interval is paid by the actual strip reserve. -/
theorem minimum_height_fixed_prefix_bound (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (r : ℕ) (hr : r < n)
    (hfix : ∀ i : Fin n,i.val < r → permutation p a i=i) :
    (r : ℤ) ≤ (n : ℤ)-2*height p a+anchorReserve p a := by
  have h := fixed_prefix_drop_bound (permutation p a) r hr hfix
  have hu := minimum_height_backward_units p a hmin
  have he := anchor_reserve_decomposition p a
  unfold LRX.FiniteCuts.cycleDefect at he
  change 3*(height p a : ℤ) ≤ _ at h
  rw [Nat.cast_sub (by omega : r ≤ n)] at h
  omega

/-- The lower even height is paid for every reserve and every fixed-prefix
length when the anchor has minimum height. -/
theorem even_second_minimum_height_upper_word (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (hn : n=2*height p a+4) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_contra hunpaid
  obtain ⟨hgap,hfix⟩ := even_second_unpaid_phase_prefix p a hn hunpaid
  let r := (a-p a).val+1
  have hrle : r ≤ n := by dsimp [r]; have := (a-p a).isLt; omega
  have hr : r < n := by
    by_contra hnot
    have hall (i : Fin n) : permutation p a i=i := hfix i (by have := i.isLt; dsimp [r] at *; omega)
    have hh : height p a=0 := by
      unfold height LRX.FiniteCuts.descendingPositions
      simp [hall]
    have hz := anchor_reserve_nonneg p a
    have hv := (a-p a).isLt
    omega
  have hb := minimum_height_fixed_prefix_bound p a hmin r hr
    (fun i hi => hfix i (by dsimp [r] at hi; omega))
  have hn' : (n : ℤ)=2*(height p a : ℤ)+4 := by exact_mod_cast hn
  dsimp [r] at hb
  omega

/-- Any anchor of the second even height yields a paid word: choosing a
minimum-height anchor either preserves this height or enters a lower case. -/
theorem even_second_height_upper_word (p : State n) (a : Fin n)
    (hn : n=2*height p a+4) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  obtain ⟨b,_,hb⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) (height p)
    ⟨0,Finset.mem_univ _⟩
  have hmin (c : Fin n) := hb c (Finset.mem_univ _)
  by_cases he : height p b=height p a
  · exact even_second_minimum_height_upper_word p b hmin (by omega)
  · have hlt := hmin a
    obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p b (by omega)
    exact ⟨w,hw,by linarith⟩

/-- Every anchor of an unpaid even input is above the eliminated second
height. This is stronger than a statement about globally minimal energy. -/
theorem even_unpaid_all_anchor_height_lower (p : State n) (m : ℕ)
    (hn : n=2*m) (hn4 : 4 ≤ n)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) (a : Fin n) :
    m ≤ height p a+1 := by
  by_contra hnot
  by_cases he : height p a+2=m
  · exact hunpaid (even_second_height_upper_word p a (by omega))
  · obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p a (by omega)
    exact hunpaid ⟨w,hw,by linarith⟩

/-- For unpaid even inputs, an energy-minimal anchor is now also a
minimum-height anchor. The eliminated branch supplies this implication. -/
theorem even_unpaid_global_minimum_height (p : State n) (m : ℕ)
    (hn : n=2*m) (hn4 : 4 ≤ n)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32)
    (a : Fin n) (ha : GlobalMinimum p a) :
    ∀ b,height p a ≤ height p b := by
  have hh := even_unpaid_global_height hn4 m hn ha hunpaid
  intro b
  have hb := even_unpaid_all_anchor_height_lower p m hn hn4 hunpaid b
  omega

#print axioms minimum_height_backward_units
#print axioms minimum_height_fixed_prefix_bound
#print axioms even_second_height_upper_word
#print axioms even_unpaid_all_anchor_height_lower
#print axioms even_unpaid_global_minimum_height
end LX.AnchoredPhases
