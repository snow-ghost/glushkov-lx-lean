import LX.NearMinimumPhases
import LX.HeadReserve

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Equal displacement values may be split between the two sides of a phase
cut. Such a split can give width exactly n and need not be an anchored lift. -/
def IsTopSet (d : Fin n → ℤ) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S,∀ j ∉ S,d j ≤ d i

theorem exists_top_set (d : Fin n → ℤ) (k : ℕ) (hk : k ≤ n) :
    ∃ S : Finset (Fin n),S.card=k ∧ IsTopSet d S := by
  classical
  let F := (Finset.univ : Finset (Fin n)).powersetCard k
  have hF : F.Nonempty := Finset.powersetCard_nonempty.mpr (by simpa using hk)
  obtain ⟨S,hS,hmax⟩ := Finset.exists_max_image F (fun T => ∑ i ∈ T,d i) hF
  have hc : S.card=k := (Finset.mem_powersetCard.mp hS).2
  refine ⟨S,hc,?_⟩
  intro i hi j hj
  have hji : j ∉ S.erase i := fun hh => hj (Finset.mem_of_mem_erase hh)
  have hT : insert j (S.erase i) ∈ F := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _,?_⟩
    rw [Finset.card_insert_of_notMem hji,Finset.card_erase_of_mem hi]
    have hp : 0 < S.card := Finset.card_pos.mpr ⟨i,hi⟩
    omega
  have hm := hmax _ hT
  rw [Finset.sum_insert hji] at hm
  have hs := Finset.sum_erase_add S d hi
  omega

theorem top_phase_width (d : Fin n → ℤ) (S : Finset (Fin n))
    (hwidth : ∀ i j,d i-d j < (n : ℤ)) (htop : IsTopSet d S) :
    ∀ i j,phaseShift d S i-phaseShift d S j ≤ (n : ℤ) := by
  intro i j
  have hw := hwidth i j
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp only [phaseShift,ite_eq_left hi,ite_eq_left hj]; omega
  · simp only [phaseShift,ite_eq_left hi,ite_eq_right hj]; omega
  · have hh := htop j hj i hi
    simp only [phaseShift,ite_eq_right hi,ite_eq_left hj]; omega
  · simp only [phaseShift,ite_eq_right hi,ite_eq_right hj]; omega

/-- The additive penalty is exact even for a split of a tied displacement. -/
def phasePenalty (d : Fin n → ℤ) (S : Finset (Fin n)) : ℤ :=
  (S.card : ℤ)*((n : ℤ)-S.card)-2*∑ i ∈ S,d i

theorem phase_penalty_nonneg {d : Fin n → ℤ} (hm : Majorized d)
    (S : Finset (Fin n)) : 0 ≤ phasePenalty d S := by
  have hh := hm S
  unfold phasePenalty
  omega

theorem top_phase_exchange_price {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (hm : Majorized d) (S : Finset (Fin n))
    (htop : IsTopSet d S) :
    inversions (phaseShift d S)=inversions d+(phasePenalty d S).toNat := by
  have hw (i j : Fin n) : d i-d j < (n : ℤ) := by
    have := range_bound hd.1 hm i j
    omega
  have he := top_phase_inversions hd S hw htop
  have hp := phase_penalty_nonneg hm S
  change (inversions (phaseShift d S) : ℤ)-inversions d=phasePenalty d S at he
  omega

/-- Every actual lift has a literal word at its first-lap deadline. This also
covers width-n lifts which cannot be recovered by the strict-strip anchor API. -/
theorem lift_deadline_word (hn : 2 ≤ n) (p : State n) (c : ℤ)
    (d : Fin n → ℤ) (hd : IsLift p.symm c d) :
    ∃ w : List Letter,p*eval w=1 ∧
      w.length=inversions d+scanDeadline d+
        ((c : Fin n)-(scanDeadline d : Fin n)).val := by
  have hl (i : Fin n) : labels d i=p i+(c : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  obtain ⟨w,ht,_⟩ := exists_realized_scan hn p c d hd
  exact ht.word_at_cursor hn p (c : Fin n) hd.1 hi hl _
    (ht.rotations_le_deadline hn hd.1 hi)

#print axioms exists_top_set
#print axioms top_phase_exchange_price
#print axioms lift_deadline_word
end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- All cursor phases are represented, including the phases between actual
anchors. No bound on the penalty is assumed in this coverage theorem. -/
theorem every_phase_top_set_word {p : State n} {a : Fin n}
    (hn : 2 ≤ n) (ha : GlobalMinimum p a) (c : Fin n) :
    ∃ S : Finset (Fin n),S.card=(c-(phase p a : Fin n)).val ∧
      IsTopSet (displacement p a) S ∧
      ∃ w : List Letter,p*eval w=1 ∧
        w.length=inversions (displacement p a)+(phasePenalty (displacement p a) S).toNat+
          scanDeadline (phaseShift (displacement p a) S)+
          (c-(scanDeadline (phaseShift (displacement p a) S) : Fin n)).val := by
  obtain ⟨S,hcard,htop⟩ := exists_top_set (displacement p a)
    (c-(phase p a : Fin n)).val (Nat.le_of_lt (c-(phase p a : Fin n)).isLt)
  have hd := shift_lift (is_lift p a) S
  have hc : ((phase p a+(S.card : ℤ) : ℤ) : Fin n)=c := by
    rw [Int.cast_add,Int.cast_natCast,hcard,Fin.cast_val_eq_self]
    abel
  obtain ⟨w,hw,hlen⟩ := lift_deadline_word hn p _ _ hd
  rw [hc,top_phase_exchange_price (is_lift p a) (global_minimum_majorized ha) S htop] at hlen
  exact ⟨S,hcard,htop,w,hw,hlen⟩

/-- A bounded penalty supplies the near-majorization premise for the full
phase family; recovery as an anchor is not required. -/
theorem top_phase_near_majorized {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (S : Finset (Fin n)) (K : ℕ)
    (hpenalty : phasePenalty (displacement p a) S ≤ K) :
    NearMajorized (phaseShift (displacement p a) S) K := by
  apply near_majorized_of_energy_allowance (is_lift p a) ha
    (shift_lift (is_lift p a) S) K
  have he := shift_energy (displacement p a) S (is_lift p a).1
  change (energy (phaseShift (displacement p a) S) : ℤ)-energy (displacement p a)=
    (n : ℤ)*phasePenalty (displacement p a) S at he
  have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg _
  nlinarith

/-- All geometric premises refer to the shifted integer coordinates. This
version permits width n and therefore the intermediate tied phases. -/
theorem top_phase_crowded_word {p : State n} {a : Fin n}
    (hn : 2 ≤ n) (ha : GlobalMinimum p a) (S : Finset (Fin n))
    (htop : IsTopSet (displacement p a) S) (K h M : ℕ)
    (hpenalty : phasePenalty (displacement p a) S ≤ K)
    (hpos : 2 ≤ h) (hh : 2*h ≤ n)
    (hlower : ∀ i,-(h : ℤ) ≤ phaseShift (displacement p a) S i)
    (hhead : -(h : ℤ) < phaseShift (displacement p a) S 0)
    (hpositions : ∀ i,phaseShift (displacement p a) S i= -(h : ℤ) → i.val ≤ M) :
    let T := (h-1)*(n-1)+max M (3*(n-2*h)+2+3*K)-1
    ∃ w : List Letter,p*eval w=1 ∧
      w.length ≤ inversions (displacement p a)+K+T+
        ((phase p a+(S.card : ℤ) : Fin n)-(T : Fin n)).val := by
  intro T
  let d := phaseShift (displacement p a) S
  have hd := shift_lift (is_lift p a) S
  have hmax (i : Fin n) : backwardDepth d i ≤ h := by
    exact_mod_cast backward_depth_le_strip hd (h : ℤ) hlower i
  have htopcoord (i : Fin n) (hi : backwardDepth d i=h) : d i= -(h : ℤ) := by
    have he := maximum_depth_displacement hd i (by intro j; rw [hi]; exact hmax j)
    rwa [hi] at he
  have hhead' : backwardDepth d 0 < h := by
    have hb := hmax 0
    by_contra hnot
    have he := htopcoord 0 (by omega)
    change -(h : ℤ) < d 0 at hhead
    omega
  have hwidth := top_phase_width (displacement p a) S
    (fun i j => by have := range_bound (is_lift p a).1 (global_minimum_majorized ha) i j; omega) htop
  have hl (i : Fin n) : labels d i=p i+((phase p a+(S.card : ℤ) : ℤ) : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  have htime := near_majorized_scan_deadline hn hd
    (top_phase_near_majorized ha S K hpenalty) hwidth hi h M hpos hh hmax hhead'
    (fun i hi => hpositions i (htopcoord i hi))
  obtain ⟨w,ht,_⟩ := exists_realized_scan hn p _ d hd
  obtain ⟨v,hv,hlen⟩ := ht.word_at_cursor hn p _ hd.1 hi hl T
    ((ht.rotations_le_deadline hn hd.1 hi).trans htime)
  have hx : inversions d=inversions (displacement p a)+(phasePenalty (displacement p a) S).toNat :=
    top_phase_exchange_price (is_lift p a) (global_minimum_majorized ha) S htop
  refine ⟨v,hv,?_⟩
  rw [hlen,hx]
  simp only [Int.cast_add,Int.cast_natCast]
  omega

#print axioms every_phase_top_set_word
#print axioms top_phase_near_majorized
#print axioms top_phase_crowded_word
end LX.AnchoredPhases
