import LRX.IndexedWindowProfile

namespace LRX.FiniteWindow
variable {n : ℕ}

/-- Universal two-cap envelope. Padding by zero-size entries allows the
existing indexed envelope to include empty and singleton families. -/
theorem window_two_cap_envelope (As : List (FillingWindow n)) (M : ℤ)
    (hM : 0 ≤ M) (hcap : ∀ A ∈ As, (A.size : ℤ) ≤ M)
    (hV : (As.map (fun A => (A.size : ℤ))).sum ≤ 2*M) :
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤
      M^2+((As.map (fun A => (A.size : ℤ))).sum-M)^2 := by
  let Z : FillingWindow n := ⟨0,⟨0,by omega⟩,1⟩
  have hz : Z.size=0 := rfl
  have hcap' : ∀ A ∈ As++[Z,Z], (A.size : ℤ) ≤ M := by
    intro A hA
    rcases List.mem_append.mp hA with h | h
    · exact hcap A h
    · have he : A=Z := by simpa using h
      subst A
      simpa only [hz,Nat.cast_zero] using hM
  have h := window_profile_envelope (As++[Z,Z]) 0 2 M (by omega)
    (by simp) hM hcap' (by simpa [hz] using hV)
  simpa [hz,pow_two] using h

#print axioms window_two_cap_envelope
end LRX.FiniteWindow
