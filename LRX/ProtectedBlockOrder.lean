import LRX.ShallowSelectedPhysicalBound

namespace LRX.ContractionBlocks.System
variable {m k : ℕ} {P : State (m+1)} {q : State (k+1)}

theorem block_rank_separation (B : System P q) :
    ∀ j i : Fin (k+1), i.val < j.val → ∀ x ∈ B.nodes i, ∀ y ∈ B.nodes j,
      x.val+j.val ≤ y.val+i.val := by
  intro j
  induction j using Fin.induction with
  | zero => intro i hij; simp at hij
  | succ j ih =>
    intro i hij x hx y hy
    by_cases he : i=j.castSucc
    · subst i
      have hxy := B.ordered j.castSucc j.succ (by simp) x hx y hy
      simp only [Fin.val_castSucc,Fin.val_succ] at hxy ⊢
      omega
    · have hv : i.val ≠ j.val := fun h => he (Fin.ext h)
      have hlt : i.val < j.castSucc.val := by simp only [Fin.val_succ] at hij; simp; omega
      have hi := ih i hlt x hx (B.firstLabel j.castSucc) (List.head_mem (B.nonempty j.castSucc))
      have hj := B.ordered j.castSucc j.succ (by simp)
        (B.firstLabel j.castSucc) (List.head_mem (B.nonempty j.castSucc)) y hy
      simp only [Fin.val_castSucc,Fin.val_succ] at hi ⊢
      omega

theorem zero_in_first_block (B : System P q) : (0 : Fin (m+1)) ∈ B.nodes 0 := by
  obtain ⟨i,hi⟩ := B.cover 0
  have he : i=0 := by
    by_contra h
    have hp : 0 < i.val := by
      have hn : i.val ≠ 0 := fun he => h (Fin.ext he)
      omega
    have hh := B.ordered 0 i hp (B.firstLabel 0) (List.head_mem (B.nonempty 0)) 0 hi
    simp at hh
  exact he ▸ hi

theorem last_in_last_block (B : System P q) : Fin.last m ∈ B.nodes (Fin.last k) := by
  obtain ⟨i,hi⟩ := B.cover (Fin.last m)
  have he : i=Fin.last k := by
    by_contra h
    have hp : i.val < k := by
      have hn : i.val ≠ k := fun he => h (Fin.ext he)
      have := i.isLt
      omega
    have hh := B.ordered i (Fin.last k) hp (Fin.last m) hi
      (B.firstLabel (Fin.last k)) (List.head_mem (B.nonempty (Fin.last k)))
    have hv := (B.firstLabel (Fin.last k)).isLt
    simp only [Fin.val_last] at hh
    omega
  exact he ▸ hi

theorem protected_extreme_sides (B : System P q) (gap : Fin m) (hB : B.Protected gap.val)
    (x y : Fin (m+1)) (hx : x ∈ B.nodes 0) (hy : y ∈ B.nodes (Fin.last k)) :
    x.val ≤ gap.val ∧ gap.val < y.val := by
  have hl := hB 0 0 B.zero_in_first_block x hx
  have hr := hB (Fin.last k) (Fin.last m) B.last_in_last_block y hy
  have hg := gap.isLt
  simp only [Fin.val_zero,Fin.val_last] at hl hr
  omega

#print axioms block_rank_separation
#print axioms protected_extreme_sides
open scoped BigOperators

theorem protected_extreme_distance (B : System P q) (gap : Fin m)
    (hB : B.Protected gap.val) (hk : 0 < k)
    (holes : Fin m → ℤ) (hh : ∀ j, 0 ≤ holes j)
    (x y : Fin (m+1)) (hx : x ∈ B.nodes 0) (hy : y ∈ B.nodes (Fin.last k)) :
    (k : ℤ)+holes gap ≤ position holes y-position holes x := by
  have hr := B.block_rank_separation (Fin.last k) 0 hk x hx y hy
  simp only [Fin.val_last,Fin.val_zero,Nat.add_zero] at hr
  have hxy : x ≤ y := by change x.val ≤ y.val; omega
  have hc := B.protected_extreme_sides gap hB x y hx hy
  rw [position_difference holes x y hxy]
  have hs := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j : Fin m => if x.val ≤ j.val ∧ j.val < y.val then holes j else 0)
    (fun j _ => by split_ifs <;> simp [hh]) (Finset.mem_univ gap)
  rw [if_pos hc] at hs
  omega

theorem protected_placement_extreme_distance (B : System P q) (gap : Fin m)
    (hB : B.Protected gap.val) (hk : 0 < k)
    (f : Fin (m+1) → ℤ) (hf : StrictMono f)
    (x y : Fin (m+1)) (hx : x ∈ B.nodes 0) (hy : y ∈ B.nodes (Fin.last k)) :
    (k : ℤ)+(f gap.succ-f gap.castSucc-1) ≤ f y-f x := by
  have hnon : ∀ j : Fin m, 0 ≤ f j.succ-f j.castSucc-1 := by
    intro j
    have hh := hf (show j.castSucc < j.succ by simp [Fin.lt_def])
    omega
  have he := B.protected_extreme_distance gap hB hk
    (fun j : Fin m => f j.succ-f j.castSucc-1) hnon x y hx hy
  rw [placement_from_holes,placement_from_holes] at he
  linarith

theorem protected_no_extreme_arrows (B : System P q) (gap : Fin m)
    (hB : B.Protected gap.val) (hk : 0 < k)
    (f : Fin (m+1) → ℤ) (hf : StrictMono f) (h : ℤ)
    (hshort : ∀ x, |f (P x)-f x| ≤ h)
    (hwide : h < (k : ℤ)+(f gap.succ-f gap.castSucc-1)) :
    q 0 ≠ Fin.last k ∧ q (Fin.last k) ≠ 0 := by
  constructor
  · intro he
    have hd := B.protected_placement_extreme_distance gap hB hk f hf
      (B.lastLabel 0) (B.firstLabel (Fin.last k))
      (List.getLast_mem (B.nonempty 0)) (List.head_mem (B.nonempty (Fin.last k)))
    have hp : P (B.lastLabel 0)=B.firstLabel (Fin.last k) := by
      have he' := B.edge 0
      rwa [he] at he'
    have hs := hshort (B.lastLabel 0)
    rw [hp] at hs
    have hab := le_abs_self (f (B.firstLabel (Fin.last k))-f (B.lastLabel 0))
    omega
  · intro he
    have hd := B.protected_placement_extreme_distance gap hB hk f hf
      (B.firstLabel 0) (B.lastLabel (Fin.last k))
      (List.head_mem (B.nonempty 0)) (List.getLast_mem (B.nonempty (Fin.last k)))
    have hp : P (B.lastLabel (Fin.last k))=B.firstLabel 0 := by
      have he' := B.edge (Fin.last k)
      rwa [he] at he'
    have hs := hshort (B.lastLabel (Fin.last k))
    rw [hp] at hs
    have hab := neg_le_abs (f (B.firstLabel 0)-f (B.lastLabel (Fin.last k)))
    omega

#print axioms protected_no_extreme_arrows
end LRX.ContractionBlocks.System
