import LX.LinearMatchingGeometry
import Mathlib

namespace LX.Core.FiniteCuts
variable {n : ℕ}

def NoSeparatedPairs (p : State n) : Prop :=
  ∀ a b c d : Fin n, a.val < b.val → b.val < c.val → c.val < d.val →
    p a=b → p c ≠ d

/-- Two separated pair intervals would each contain a distinct adjacent pair. -/
theorem no_separated_pairs_of_unique_adjacent (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (hfixed : ∀ i, p i ≠ i)
    (hunique : ∀ a b : Fin n, a.val+1=(p a).val → b.val+1=(p b).val → a=b) :
    NoSeparatedPairs p := by
  intro a b c d hab hbc hcd hpab hpcd
  obtain ⟨x,y,hx,hy,hxy,hpx⟩ := noncrossing_pair_contains_adjacent p hinv hnc a b hab hpab
    (fun i _ _ => hfixed i)
  obtain ⟨u,v,hu,hv,huv,hpu⟩ := noncrossing_pair_contains_adjacent p hinv hnc c d hcd hpcd
    (fun i _ _ => hfixed i)
  have heq := hunique x u (by rw [hpx]; exact hxy) (by rw [hpu]; exact huv)
  have := congrArg Fin.val heq
  omega

/-- In a fully nested matching, the outside prefix and suffix are paired with each other. -/
theorem nested_pair_exterior (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (hsep : NoSeparatedPairs p) (hfixed : ∀ i, p i ≠ i)
    (a b : Fin n) (hab : a.val < b.val) (hpab : p a=b) (x : Fin n) :
    (x.val < a.val → b.val < (p x).val) ∧
      (b.val < x.val → (p x).val < a.val) := by
  have hpba : p b=a := by rw [← hpab]; exact hinv a
  have hfix : (p x).val ≠ x.val := fun h => hfixed x (Fin.ext h)
  constructor
  · intro hxa
    have hnea : (p x).val ≠ a.val := by
      intro h
      have he := p.injective ((Fin.ext h).trans hpba.symm)
      have := congrArg Fin.val he
      omega
    have hneb : (p x).val ≠ b.val := by
      intro h
      have he := p.injective ((Fin.ext h).trans hpab.symm)
      have := congrArg Fin.val he
      omega
    by_contra h
    have hpb : (p x).val < b.val := by omega
    by_cases hpa : (p x).val < a.val
    · by_cases hxp : x.val < (p x).val
      · exact hsep x (p x) a b hxp hpa hab rfl hpab
      · exact hsep (p x) x a b (by omega) hxa hab (hinv x) hpab
    · exact hnc x a (p x) b hxa (by omega) hpb rfl hpab
  · intro hbx
    have hnea : (p x).val ≠ a.val := by
      intro h
      have he := p.injective ((Fin.ext h).trans hpba.symm)
      have := congrArg Fin.val he
      omega
    have hneb : (p x).val ≠ b.val := by
      intro h
      have he := p.injective ((Fin.ext h).trans hpab.symm)
      have := congrArg Fin.val he
      omega
    by_contra h
    have hap : a.val < (p x).val := by omega
    by_cases hbp : b.val < (p x).val
    · by_cases hxp : x.val < (p x).val
      · exact hsep a b x (p x) hab hbx hxp hpab rfl
      · exact hsep a b (p x) x hab hbp (by omega) hpab (hinv x)
    · exact hnc a (p x) b x hap (by omega) hbx hpab (hinv x)

#print axioms no_separated_pairs_of_unique_adjacent
#print axioms nested_pair_exterior
end LX.Core.FiniteCuts
