import LX.AllGlobalOddPayment

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The three remaining source configurations, always at a genuine global
minimum of the original input. This definition is not a word bound. -/
def CriticalPhase (p : State n) (a : Fin n) : Prop :=
  GlobalMinimum p a ∧
    ((n=2*height p a+2 ∧ (fixedPositions (permutation p a)).card=1) ∨
     (n=2*height p a+3 ∧
       ((fixedPositions (permutation p a)).card=1 ∨ (fixedPositions (permutation p a)).card=2)))

/-- Complete coverage of the still-unpaid input family. -/
theorem unpaid_critical_phase (hn4 : 4 ≤ n) (p : State n)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a : Fin n,CriticalPhase p a := by
  by_cases he : n=2*(n/2)
  · obtain ⟨a,ha,hh,hf⟩ := even_unpaid_one_fixed_minimum hn4 p (n/2) he hunpaid
    exact ⟨a,ha,Or.inl ⟨by omega,hf⟩⟩
  · have ho : n=2*(n/2)+1 := by omega
    obtain ⟨a,ha,hh,hf⟩ := odd_unpaid_lower_small_fixed hn4 p (n/2) ho hunpaid
    have hp : 0 < (fixedPositions (permutation p a)).card := Finset.card_pos.mpr
      ⟨a,(mem_fixedPositions _ _).mpr (permutation_anchor p a)⟩
    exact ⟨a,ha,Or.inr ⟨by omega,by omega⟩⟩

/-- Critical global sources of an unpaid input also minimize height. -/
theorem unpaid_critical_minimum_height (hn4 : 4 ≤ n) (p : State n) (a : Fin n)
    (ha : CriticalPhase p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∀ b : Fin n,height p a ≤ height p b := by
  rcases ha.2 with ⟨hn,_⟩ | ⟨hn,_⟩
  · exact even_unpaid_global_minimum_height p (height p a+1) (by omega) hn4 hunpaid a ha.1
  · intro b
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p b (by omega)
    exact hunpaid ⟨w,hw,by linarith⟩

/-- The first nonminimal phase is an actual anchor. It costs only one or
two extra exchanges, and raises height by at most one. Global minimality
of that successor is explicitly false. -/
theorem unpaid_critical_successor (hn4 : 4 ≤ n) (p : State n) (a : Fin n)
    (ha : CriticalPhase p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ b : Fin n,∃ t j : ℕ,(t=1 ∨ t=2) ∧ (j=1 ∨ j=2) ∧
      p b-b=p a-a+(t : Fin n) ∧
      height p b+t=height p a+(fixedPositions (permutation p a)).card ∧
      (height p b=height p a ∨ height p b=height p a+1) ∧
      inversions (displacement p b)=inversions (displacement p a)+j ∧
      NearMajorized (displacement p b) j ∧ ¬GlobalMinimum p b := by
  have hmin := unpaid_critical_minimum_height hn4 p a ha hunpaid
  have hpos : 0 < height p a := by rcases ha.2 with h | h <;> omega
  obtain ⟨b,t,ht,htf,_,hoff,hheight,hI⟩ := minimum_height_next_occupied_phase p a hpos hmin
  have hf : (fixedPositions (permutation p a)).card ≤ 2 := by rcases ha.2 with h | h <;> omega
  have ht12 : t=1 ∨ t=2 := by omega
  have hh : height p b=height p a ∨ height p b=height p a+1 := by omega
  have hcost : ∃ j : ℕ,(j=1 ∨ j=2) ∧
      inversions (displacement p b)=inversions (displacement p a)+j := by
    rcases ha.2 with ⟨hn,hf⟩ | ⟨hn,hf | hf⟩
    · rw [hf] at hI
      norm_num only [Nat.cast_one] at hI
      exact ⟨1,Or.inl rfl,by omega⟩
    · rw [hf] at hI
      norm_num only [Nat.cast_one] at hI
      exact ⟨2,Or.inr rfl,by omega⟩
    · rw [hf] at hI
      norm_num only [Nat.cast_ofNat] at hI
      exact ⟨2,Or.inr rfl,by omega⟩
  obtain ⟨j,hj,hjI⟩ := hcost
  refine ⟨b,t,j,ht12,hj,hoff,hheight,hh,hjI,
    near_majorized_of_exchange_allowance ha.1 b j hjI.le,?_⟩
  intro hb
  have hle := global_minimum_exchanges hb a
  omega

#print axioms unpaid_critical_phase
#print axioms unpaid_critical_minimum_height
#print axioms unpaid_critical_successor
end LX.AnchoredPhases

namespace LX
open AnchoredPhases

/-- The single remaining routing obligation. The theorem below verifies
that proving this statement with one fixed C ≥ 32 finishes the original
diameter objective. No instance of this proposition is assumed or supplied. -/
def CriticalPhaseWordBound (C : ℕ) : Prop :=
  ∀ (n : ℕ) [NeZero n],4 ≤ n → ∀ (p : State n) (a : Fin n),CriticalPhase p a →
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*C

theorem all_words_of_critical_phase_bound {C : ℕ} (hC : 32 ≤ C)
    (hcritical : CriticalPhaseWordBound C) (n : ℕ) [NeZero n] (hn4 : 4 ≤ n) (p : State n) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*C := by
  by_contra hunpaid
  have hunpaid32 : ¬∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
    rintro ⟨w,hw,hprice⟩
    apply hunpaid
    refine ⟨w,hw,?_⟩
    have hC' : (32 : ℤ) ≤ C := by exact_mod_cast hC
    linarith
  obtain ⟨a,ha⟩ := unpaid_critical_phase hn4 p hunpaid32
  exact hunpaid (hcritical n hn4 p a ha)

theorem quadratic_upper_of_critical_phase_bound {C : ℕ} (hC : 32 ≤ C)
    (hcritical : CriticalPhaseWordBound C) : QuadraticUpperBound := by
  apply quadratic_specification.mpr
  refine ⟨C,?_⟩
  intro n _ hn4 p
  obtain ⟨w,hw,hprice⟩ := all_words_of_critical_phase_bound hC hcritical n hn4 p⁻¹
  refine ⟨w,?_,hprice⟩
  have he := congrArg (fun q : State n => p*q) hw
  simpa only [← mul_assoc,mul_inv_cancel,one_mul,mul_one] using he

/-- Exact equivalence with the original quantified objective. This is a
verified reduction, not a proof that either side is inhabited. -/
theorem quadratic_critical_phase_specification : QuadraticUpperBound ↔
    ∃ C : ℕ,32 ≤ C ∧ CriticalPhaseWordBound C := by
  constructor
  · intro h
    obtain ⟨C,hC⟩ := quadratic_specification.mp h
    refine ⟨max C 32,le_max_right _ _,?_⟩
    intro n _ hn4 p a _
    obtain ⟨w,hw,hprice⟩ := hC n hn4 p⁻¹
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hle : (C : ℤ) ≤ (max C 32 : ℕ) := by exact_mod_cast le_max_left C 32
    linarith
  · rintro ⟨C,hC,hcritical⟩
    exact quadratic_upper_of_critical_phase_bound hC hcritical

#print axioms all_words_of_critical_phase_bound
#print axioms quadratic_upper_of_critical_phase_bound
#print axioms quadratic_critical_phase_specification
end LX
