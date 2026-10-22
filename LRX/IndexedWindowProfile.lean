import LRX.AreaWindowSizeBounds
import Research.CayleyPy.StrongIntervalCapCutoff

namespace LRX.FiniteWindow
open scoped BigOperators

/-- Indexing keeps repeated equal-size windows distinct. -/
theorem sum_window_indices {α β : Type*} [AddCommMonoid β] (xs : List α) (f : α → β) :
    (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum := by
  calc
    _ = (List.ofFn (fun i : Fin xs.length => f (xs.get i))).sum := List.sum_ofFn.symm
    _ = (List.map f (List.ofFn xs.get)).sum := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [List.ofFn_get]

theorem window_index_count {n : ℕ} (As : List (FillingWindow n)) (b : ℕ) :
    (Finset.univ.filter (fun i : Fin As.length => b ≤ (As.get i).size)).card =
      (As.filter (fun A => decide (b ≤ A.size))).length := by
  have hh := sum_window_indices As (fun A => if b ≤ A.size then (1 : ℕ) else 0)
  simp only [Finset.sum_boole,Nat.cast_id] at hh
  rw [hh]
  clear hh
  induction As with
  | nil => simp
  | cons A As ih =>
    by_cases ha : b ≤ A.size <;> simp [ha,ih,Nat.add_comm]

/-- A finite profile envelope with lower bounds on t actual indexed entries.
Both the two-unit and three-nonempty cases use the same proof. -/
theorem window_profile_envelope {n : ℕ} (As : List (FillingWindow n)) (b t : ℕ) (M : ℤ)
    (ht : 2 ≤ t) (hcount : t ≤ (As.filter (fun A => decide (b ≤ A.size))).length)
    (hM : 0 ≤ M) (hcap : ∀ A ∈ As, (A.size : ℤ) ≤ M)
    (hVcap : (As.map (fun A => (A.size : ℤ))).sum ≤ 2*M) :
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤
      M^2+((As.map (fun A => (A.size : ℤ))).sum-M-(b : ℤ)*((t : ℤ)-2))^2+
        (b : ℤ)^2*((t : ℤ)-2) := by
  classical
  let S : Finset (Fin As.length) := Finset.univ
  let x : Fin As.length → ℤ := fun i => (As.get i).size
  let big : Finset (Fin As.length) := S.filter (fun i => b ≤ (As.get i).size)
  have hbig : t ≤ big.card := by
    rw [← window_index_count As b] at hcount
    exact hcount
  have hnon : S.Nonempty := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < big.card by omega)
    exact ⟨i,(Finset.mem_filter.mp hi).1⟩
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image S x hnon
  have herase : t-1 ≤ (big.erase j).card := by
    by_cases hjb : j ∈ big
    · rw [Finset.card_erase_of_mem hjb]
      omega
    · rw [Finset.erase_eq_of_notMem hjb]
      omega
  obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq herase
  have hsub : A ⊆ S.erase j := by
    intro i hi
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp (hA hi)
    exact Finset.mem_erase.mpr ⟨hne,(Finset.mem_filter.mp hmem).1⟩
  have hlow (i : Fin As.length) (hi : i ∈ A) : (b : ℤ) ≤ x i := by
    have hb := (Finset.mem_filter.mp (Finset.mem_of_mem_erase (hA hi))).2
    change (b : ℤ) ≤ ((As.get i).size : ℤ)
    exact_mod_cast hb
  have hrest := CayleyPy.StrongIntervalCapCutoff.lower_mass_square (S.erase j) A x (b : ℤ)
    hsub (by positivity) (fun i _ => by dsimp [x]; positivity) hlow
  have hcard' : (A.card : ℤ)=(t : ℤ)-1 := by omega
  rw [hcard'] at hrest
  have hsum := Finset.sum_erase_add S x hj
  have hsquare := Finset.sum_erase_add S (fun i => (x i)^2) hj
  have hsmall : (∑ i ∈ S, (x i)^2) ≤ x j*(∑ i ∈ S, x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hp := mul_nonneg (show (0 : ℤ) ≤ x i by dsimp [x]; positivity)
      (show (0 : ℤ) ≤ x j-x i by have := hmax i hi; omega)
    nlinarith
  have hxc : x j ≤ M := hcap _ (List.get_mem As j)
  have hv : (∑ i ∈ S, x i) ≤ 2*M := by
    change (∑ i : Fin As.length, ((As.get i).size : ℤ)) ≤ 2*M
    rw [sum_window_indices As (fun A => (A.size : ℤ))]
    exact hVcap
  have ht2 : (0 : ℤ) ≤ (t : ℤ)-2 := by omega
  have heSum : (∑ i ∈ S.erase j, x i)=(∑ i ∈ S, x i)-x j := by omega
  rw [heSum] at hrest
  have hresult := CayleyPy.StrongIntervalCapCutoff.exact_cap_envelope
    (∑ i ∈ S, x i) M (x j) ((b : ℤ)*((t : ℤ)-2)) ((b : ℤ)^2*((t : ℤ)-2))
    (∑ i ∈ S, (x i)^2) (Finset.sum_nonneg (fun i _ => by dsimp [x]; positivity))
    hM (by positivity) (by positivity) hxc hv hsmall (by nlinarith)
  dsimp only [S,x] at hresult
  rw [sum_window_indices As (fun A => (A.size : ℤ)),
    sum_window_indices As (fun A => (A.size : ℤ)^2)] at hresult
  simpa only [pow_two] using hresult

#print axioms window_profile_envelope
end LRX.FiniteWindow
