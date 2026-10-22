import LRX.InversionIndices

/-! A finite set of all affine inversions, with its explicit double-sum cardinality. -/
namespace LRX.LiftedModel
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def pairIndexEmbedding : (Σ _i : Fin n, Σ _j : Fin n, ℤ) ↪ PairKey n where
  toFun t := ⟨t.1, t.2.1, (n : ℤ)*t.2.2⟩
  inj' := by
    rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
    have hi : i=i' := congrArg PairKey.first h
    have hj : j=j' := congrArg PairKey.second h
    have hk : (n : ℤ)*k=(n : ℤ)*k' := congrArg PairKey.shift h
    have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    have hkk : k=k' := (mul_left_cancel₀ hn hk)
    subst i'; subst j'; subst k'
    rfl

def inversionPairs (F : Fin n → ℤ) : Finset (PairKey n) :=
  ((Finset.univ : Finset (Fin n)).sigma (fun i =>
    (Finset.univ : Finset (Fin n)).sigma (fun j =>
      if i < j then inversionIndices ((F j-F i)/(n : ℤ)) else ∅))).map pairIndexEmbedding

def inversionCount (F : Fin n → ℤ) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then ((F j-F i)/(n : ℤ)).natAbs else 0

theorem mk_mem_inversionPairs (F : Fin n → ℤ) (i j : Fin n) (k : ℤ) :
    (⟨i,j,(n : ℤ)*k⟩ : PairKey n) ∈ inversionPairs F ↔
      i < j ∧ k ∈ inversionIndices ((F j-F i)/(n : ℤ)) := by
  change pairIndexEmbedding ⟨i,j,k⟩ ∈ Finset.map pairIndexEmbedding _ ↔ _
  rw [Finset.mem_map']
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and]
  by_cases hij : i < j <;> simp [hij]

theorem inversionPairs_card (F : Fin n → ℤ) :
    (inversionPairs F).card=inversionCount F := by
  unfold inversionPairs inversionCount
  rw [Finset.card_map, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [card_inversion_indices]

theorem inversionPairs_valid (F : Fin n → ℤ) (key : PairKey n)
    (hk : key ∈ inversionPairs F) : key.Valid := by
  obtain ⟨⟨i,j,k⟩, _, hkey⟩ := Finset.mem_map.mp hk
  change (⟨i,j,(n : ℤ)*k⟩ : PairKey n)=key at hkey
  subst key
  have hmem := (mk_mem_inversionPairs F i j k).mp hk
  exact ⟨hmem.1, dvd_mul_right _ _⟩

theorem mem_inversionPairs_iff {s : Configuration n} (hs : Aligned s) (key : PairKey n) :
    key ∈ inversionPairs s.position ↔
      key.Valid ∧ ¬ (key.Before (initial (n := n)) ↔ key.Before s) := by
  constructor
  · intro hm
    have hk := inversionPairs_valid s.position key hm
    obtain ⟨k, hshift⟩ := hk.2
    cases key with
    | mk i j shift =>
      change shift=(n : ℤ)*k at hshift
      subst shift
      have hmem := (mk_mem_inversionPairs s.position i j k).mp hm
      exact ⟨hk, (inversion_index_order hs i j hmem.1 k).mp hmem.2⟩
  · rintro ⟨hk, hchange⟩
    obtain ⟨k, hshift⟩ := hk.2
    cases key with
    | mk i j shift =>
      change shift=(n : ℤ)*k at hshift
      subst shift
      apply (mk_mem_inversionPairs s.position i j k).mpr
      exact ⟨hk.1, (inversion_index_order hs i j hk.1 k).mpr hchange⟩

/-- In a reduced trace, the number of X is exactly the explicit affine inversion
sum of the final integer positions. -/
theorem reduced_exchange_count (hn : 2 ≤ n) (w : List Letter)
    (hnd : (events w (initial (n := n))).Nodup) :
    BufferProgram.exchanges w=inversionCount (run w (initial (n := n))).position := by
  have hs := run_aligned hn w (initial_aligned (n := n))
  have hset : (events w (initial (n := n))).toFinset=
      inversionPairs (run w (initial (n := n))).position := by
    ext key
    rw [List.mem_toFinset, reduced_trace_inversions hn w (initial_aligned (n := n)) hnd,
      mem_inversionPairs_iff hs]
  have hcard := congrArg Finset.card hset
  rw [List.toFinset_card_of_nodup hnd, event_count_length, inversionPairs_card] at hcard
  exact hcard

#print axioms inversionPairs_card
#print axioms reduced_exchange_count
end LRX.LiftedModel
