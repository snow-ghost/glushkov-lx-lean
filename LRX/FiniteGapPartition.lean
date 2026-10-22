import LRX.FiniteWindow

/-! The open intervals following a finite set of marked vertices partition
its complement. The interval after the last mark ends at n. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.NatCast
variable {n : ℕ} [NeZero n]

def successors (S : Finset (Fin n)) (a : Fin n) : Finset ℕ :=
  insert n ((S.filter (fun j => a.val < j.val)).image Fin.val)

theorem successors_nonempty (S : Finset (Fin n)) (a : Fin n) : (successors S a).Nonempty :=
  ⟨n,Finset.mem_insert_self _ _⟩

def next (S : Finset (Fin n)) (a : Fin n) : ℕ := (successors S a).min' (successors_nonempty S a)

theorem next_le (S : Finset (Fin n)) (a : Fin n) : next S a ≤ n :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem lt_next (S : Finset (Fin n)) (a : Fin n) : a.val < next S a := by
  have h : a.val+1 ≤ next S a := by
    apply Finset.le_min'
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact a.isLt
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      have := (Finset.mem_filter.mp hi).2
      omega
  omega

theorem next_le_member (S : Finset (Fin n)) (a j : Fin n) (hj : j ∈ S) (haj : a.val < j.val) :
    next S a ≤ j.val := by
  apply Finset.min'_le
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,haj⟩,rfl⟩)

theorem next_is_member (S : Finset (Fin n)) (a : Fin n) (hnext : next S a < n) :
    ∃ j ∈ S, j.val=next S a := by
  have hm := Finset.min'_mem (successors S a) (successors_nonempty S a)
  change next S a ∈ successors S a at hm
  rcases Finset.mem_insert.mp hm with hn | hj
  · omega
  · obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hj
    exact ⟨j,(Finset.mem_filter.mp hj).1,he⟩

def size (S : Finset (Fin n)) (a : Fin n) : ℕ := next S a-a.val-1

def window (S : Finset (Fin n)) (a : Fin n) : FiniteWindow.Window n (size S a) where
  offset := a.val+1
  fits := by have := next_le S a; have := lt_next S a; unfold size; omega

theorem contains_window (S : Finset (Fin n)) (a i : Fin n) :
    FiniteWindow.Contains (window S a) i ↔ a.val < i.val ∧ i.val < next S a := by
  have := lt_next S a
  unfold FiniteWindow.Contains window size
  dsimp
  omega

def positions (S : Finset (Fin n)) (a : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (FiniteWindow.Contains (window S a))

@[simp] theorem mem_positions (S : Finset (Fin n)) (a i : Fin n) :
    i ∈ positions S a ↔ a.val < i.val ∧ i.val < next S a := by
  simp [positions,contains_window]

theorem gap_avoids_marks (S : Finset (Fin n)) (a i : Fin n) (hi : i ∈ positions S a) : i ∉ S := by
  obtain ⟨hai,hin⟩ := (mem_positions S a i).mp hi
  intro hiS
  have h := next_le_member S a i hiS hai
  omega

theorem gaps_disjoint (S : Finset (Fin n)) : (S : Set (Fin n)).PairwiseDisjoint (positions S) := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro i hia hib
  obtain ⟨hai,hin⟩ := (mem_positions S a i).mp hia
  obtain ⟨hbi,hin'⟩ := (mem_positions S b i).mp hib
  have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have := next_le_member S a b hb hlt
    omega
  · have := next_le_member S b a ha hgt
    omega

theorem outside_in_gap (S : Finset (Fin n)) (hzero : (0 : Fin n) ∈ S)
    (i : Fin n) (hi : i ∉ S) : ∃ a ∈ S, i ∈ positions S a := by
  classical
  let T := S.filter (fun a => a.val ≤ i.val)
  have hn : T.Nonempty := ⟨0,by simp [T,hzero]⟩
  obtain ⟨a,ha,hmax⟩ := T.exists_max_image Fin.val hn
  obtain ⟨haS,hai⟩ := Finset.mem_filter.mp ha
  have hai' : a.val < i.val := by
    have he : a.val ≠ i.val := fun he => hi (Fin.ext he ▸ haS)
    omega
  refine ⟨a,haS,(mem_positions S a i).mpr ⟨hai',?_⟩⟩
  by_contra h
  have hnext : next S a < n := by have := i.isLt; omega
  obtain ⟨j,hj,he⟩ := next_is_member S a hnext
  have hjT : j ∈ T := Finset.mem_filter.mpr ⟨hj,by omega⟩
  have hm := hmax j hjT
  have hn := lt_next S a
  omega

theorem union_gaps (S : Finset (Fin n)) (hzero : (0 : Fin n) ∈ S) :
    S.biUnion (positions S)=Sᶜ := by
  ext i
  simp only [Finset.mem_biUnion,Finset.mem_compl]
  exact ⟨fun ⟨a,_,hi⟩ => gap_avoids_marks S a i hi, outside_in_gap S hzero i⟩

#print axioms gaps_disjoint
#print axioms union_gaps
end LRX.FiniteGaps
