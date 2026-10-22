import LRX.FinitePermutationProfile

/-! Every positive finite cut load is available at an incident active port on
either side. Maxima can therefore be moved to genuine cycle vertices. -/
namespace LRX.FiniteCuts
variable {b : ℕ}

theorem forward_succ_of_fixed (p : State b) (e : ℕ) (he : e < b)
    (hfixed : p ⟨e,he⟩=⟨e,he⟩) : forward p (e+1)=forward p e := by
  ext i
  rw [mem_forward, mem_forward]
  have hsame : (p i).val=e ↔ i.val=e := by
    constructor
    · intro h
      have hi : p i=p ⟨e,he⟩ := by rw [hfixed]; exact Fin.ext h
      exact congrArg Fin.val (p.injective hi)
    · intro h
      have hi : i=⟨e,he⟩ := Fin.ext h
      rw [hi, hfixed]
  omega

theorem half_load_succ_of_fixed (p : State b) (e : ℕ) (he : e < b)
    (hfixed : p ⟨e,he⟩=⟨e,he⟩) : halfLoad p (e+1)=halfLoad p e := by
  unfold halfLoad
  rw [forward_succ_of_fixed p e he hfixed]

/-- The same positive load occurs at a right incident port no farther right
than the given cut. -/
theorem left_incident_port (p : State b) (e : ℕ) (he : e ≤ b)
    (hpos : 0 < halfLoad p e) :
    ∃ i : Fin b, p i ≠ i ∧ i.val+1 ≤ e ∧ halfLoad p (i.val+1)=halfLoad p e := by
  let P : ℕ → Prop := fun k => k ≤ e ∧ halfLoad p e ≤ halfLoad p k
  have hex : ∃ k, P k := ⟨e, le_rfl, le_rfl⟩
  let k := Nat.find hex
  have hk : P k := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra h
    have hz : k=0 := by omega
    have hle := hk.2
    rw [hz, half_load_zero] at hle
    omega
  have hkb : k-1 < b := by have := hk.1; omega
  have hs : k-1+1=k := by omega
  have hprev : halfLoad p (k-1) < halfLoad p e := by
    have hm := Nat.find_min hex (show k-1 < k by omega)
    change ¬ P (k-1) at hm
    dsimp [P] at hm
    have := hk.1
    omega
  refine ⟨⟨k-1,hkb⟩, ?_, ?_, ?_⟩
  · intro hf
    have hh := half_load_succ_of_fixed p (k-1) hkb hf
    rw [hs] at hh
    have := hk.2
    omega
  · dsimp
    have := hk.1
    omega
  · dsimp
    rw [hs]
    have hh := half_load_succ_upper p (k-1) hkb
    rw [hs] at hh
    have := hk.2
    omega

/-- The same positive load occurs at a left incident port no farther left
than the given cut. -/
theorem right_incident_port (p : State b) (e : ℕ) (he : e ≤ b)
    (hpos : 0 < halfLoad p e) :
    ∃ i : Fin b, p i ≠ i ∧ e ≤ i.val ∧ halfLoad p i.val=halfLoad p e := by
  let P : ℕ → Prop := fun k => k ≤ b-e ∧ halfLoad p e ≤ halfLoad p (b-k)
  have hex : ∃ k, P k := by
    refine ⟨b-e, le_rfl, ?_⟩
    have h : b-(b-e)=e := by omega
    rw [h]
  let k := Nat.find hex
  have hk : P k := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra h
    have hz : k=0 := by omega
    have hle := hk.2
    rw [hz, Nat.sub_zero, half_load_end] at hle
    omega
  have hkb : b-k < b := by have := hk.1; omega
  have hs : b-(k-1)=b-k+1 := by have := hk.1; omega
  have hnext : halfLoad p (b-k+1) < halfLoad p e := by
    have hm := Nat.find_min hex (show k-1 < k by omega)
    change ¬ P (k-1) at hm
    dsimp [P] at hm
    rw [hs] at hm
    have := hk.1
    omega
  refine ⟨⟨b-k,hkb⟩, ?_, ?_, ?_⟩
  · intro hf
    have hh := half_load_succ_of_fixed p (b-k) hkb hf
    have := hk.2
    omega
  · dsimp
    have := hk.1
    omega
  · dsimp
    have hh := half_load_succ_lower p (b-k) hkb
    have := hk.2
    omega

#print axioms half_load_succ_of_fixed
#print axioms left_incident_port
#print axioms right_incident_port
end LRX.FiniteCuts
