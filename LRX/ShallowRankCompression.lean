import LRX.ShallowContraction

namespace LRX.FiniteCuts
variable {n : ℕ}

/-- A shallow cycle can be standardized on its moving support. The increasing
embedding records every original label and intertwines the actual maps. -/
theorem shallow_rank_compression {p : State n} (hp : p.IsCycle) (hs : Shallow p) :
    ∃ m : ℕ, ∃ q : State m, ∃ f : Fin m ↪o Fin n,
      q.IsCycle ∧ Shallow q ∧ q.support=Finset.univ ∧ m=p.support.card ∧
      (∀ i, f (q i)=p (f i)) ∧ (∀ j, j ∈ p.support ↔ ∃ i, f i=j) := by
  classical
  induction n with
  | zero =>
    have hc := hp.two_le_card_support
    have hle : p.support.card ≤ 0 := by simpa using Finset.card_le_univ p.support
    omega
  | succ n ih =>
    by_cases hfix : ∃ a : Fin (n+1), p a=a
    · obtain ⟨a,ha⟩ := hfix
      obtain ⟨hc,hsh,hcard⟩ := contract_fixed_shallow_cycle hp hs a ha
      obtain ⟨m,q,f,hq,hqs,hfull,hm,hcomm,himage⟩ := ih hc hsh
      have hext := contract_fixed_extension p a ha
      have hsupport : p.support=(contract p a).support.map (finSuccAboveEquiv a).asEmbedding := by
        have h := Equiv.Perm.support_extend_domain (finSuccAboveEquiv a) (g := contract p a)
        rwa [hext] at h
      refine ⟨m,q,f.trans (Fin.succAboveOrderEmb a),hq,hqs,hfull,hm.trans hcard,?_,?_⟩
      · intro i
        change a.succAbove (f (q i))=p (a.succAbove (f i))
        rw [hcomm]
        have h := contract_entry p a (f i)
        rwa [ha] at h
      · intro j
        rw [hsupport,Finset.mem_map]
        constructor
        · rintro ⟨k,hk,he⟩
          obtain ⟨i,hi⟩ := (himage k).mp hk
          refine ⟨i,?_⟩
          change a.succAbove (f i)=j
          rw [hi]
          exact he
        · rintro ⟨i,hi⟩
          refine ⟨f i,(himage (f i)).mpr ⟨i,rfl⟩,?_⟩
          exact hi
    · have hfull : p.support=Finset.univ := by
        ext i
        simp only [Finset.mem_univ,iff_true,Equiv.Perm.mem_support]
        exact fun h => hfix ⟨i,h⟩
      refine ⟨n+1,p,(OrderIso.refl _).toOrderEmbedding,hp,hs,hfull,?_,?_,?_⟩
      · simp [hfull]
      · intro i; rfl
      · intro j; simp [hfull]

#print axioms shallow_rank_compression
end LRX.FiniteCuts
