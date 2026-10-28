import LX.WordMetric
import Mathlib

namespace LX.FinitePairReduction
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def ShortestFrom (p : State n) (w : List Letter) : Prop :=
  ∀ v : List Letter,p*eval v=p*eval w → w.length ≤ v.length

def HeadPair (p : State n) (a b : Fin n) : Prop :=
  (p 0=a ∧ p 1=b) ∨ (p 0=b ∧ p 1=a)

def headPartners (i : Fin n) (p : State n) : List (Fin n) :=
  if p 0=i then [p 1] else if p 1=i then [p 0] else []

/-- The actual successive exchange partners of one named token. -/
def partners (i : Fin n) : List Letter → State n → List (Fin n)
  | [], _ => []
  | .l::w, p => partners i w (p*eval [.l])
  | .x::w, p => headPartners i p ++ partners i w (p*eval [.x])

theorem eval_cons_action (a : Letter) (w : List Letter) :
    eval (n := n) (a::w)=a.toCore.eval*eval w :=
  LX.Core.eval_cons a.toCore (w.map Letter.toCore)

theorem mem_head_partners (i j : Fin n) (p : State n) :
    j ∈ headPartners i p ↔ HeadPair p i j := by
  unfold headPartners HeadPair
  by_cases h0 : p 0=i <;> by_cases h1 : p 1=i <;> simp [h0,h1,eq_comm]

theorem head_swap (p : State n) (a b : Fin n) (hp : HeadPair p a b) :
    p*eval [.x]=Equiv.swap a b*p := by
  have he : p*eval [.x]=Equiv.swap (p 0) (p 1)*p := by
    apply Equiv.ext
    intro i
    change p (Equiv.swap 0 1 i)=Equiv.swap (p 0) (p 1) (p i)
    exact Function.Injective.map_swap p.injective 0 1 i
  rcases hp with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · simpa only [h0,h1] using he
  · simpa only [h0,h1,Equiv.swap_comm b a] using he

/-- Delete two actual exchanges of the same finite pair. The intervening
word, every L, and the final finite permutation are preserved. -/
theorem delete_returning_pair (p : State n) (a b : Fin n) (u v : List Letter)
    (hfirst : HeadPair p a b) (hsecond : HeadPair (p*eval [.x]*eval u) a b) :
    p*eval (.x::(u++(.x::v)))=p*eval (u++v) := by
  have h1 := head_swap p a b hfirst
  have h2 := head_swap (p*eval [.x]*eval u) a b hsecond
  have hss : (Equiv.swap a b : State n)*Equiv.swap a b=1 := by
    apply Equiv.ext
    intro i
    simp
  have he : (p*eval [.x]*eval u)*eval [.x]=p*eval u := by
    rw [h2,h1]
    simp only [← mul_assoc,hss,one_mul]
  have hh := congrArg (fun q : State n => q*eval v) he
  simpa only [eval_cons_action,eval_nil,mul_one,eval_append,mul_assoc] using hh

theorem shortest_tail (p : State n) (a : Letter) (w : List Letter)
    (h : ShortestFrom p (a::w)) : ShortestFrom (p*eval [a]) w := by
  intro v hv
  have hh := h (a::v) (by simpa only [eval_cons_action,eval_nil,mul_one,mul_assoc] using hv)
  simpa only [List.length_cons,Nat.add_le_add_iff_right] using hh

theorem mem_partners (i j : Fin n) (w : List Letter) (p : State n)
    (hj : j ∈ partners i w p) :
    ∃ u v : List Letter,w=u++(.x::v) ∧ HeadPair (p*eval u) i j := by
  induction w generalizing p with
  | nil => simp [partners] at hj
  | cons a w ih =>
    cases a with
    | l =>
      obtain ⟨u,v,he,hp⟩ := ih (p*eval [.l]) hj
      refine ⟨.l::u,v,by simp [he],?_⟩
      simpa only [eval_cons_action,eval_nil,mul_one,mul_assoc] using hp
    | x =>
      rcases List.mem_append.mp hj with hhead | htail
      · exact ⟨[],w,rfl,by simpa using (mem_head_partners i j p).mp hhead⟩
      · obtain ⟨u,v,he,hp⟩ := ih (p*eval [.x]) htail
        refine ⟨.x::u,v,by simp [he],?_⟩
        simpa only [eval_cons_action,eval_nil,mul_one,mul_assoc] using hp

theorem shortest_no_partner_return (p : State n) (i j : Fin n) (w : List Letter)
    (hmin : ShortestFrom p (.x::w)) (hhead : HeadPair p i j) :
    j ∉ partners i w (p*eval [.x]) := by
  intro hmem
  obtain ⟨u,v,he,hsecond⟩ := mem_partners i j w (p*eval [.x]) hmem
  have hend := delete_returning_pair p i j u v hhead hsecond
  have hshort := hmin (u++v) (by simpa only [he] using hend.symm)
  simp only [he,List.length_cons,List.length_append] at hshort
  omega

theorem shortest_partners_nodup (i : Fin n) (w : List Letter) (p : State n)
    (hmin : ShortestFrom p w) : (partners i w p).Nodup := by
  induction w generalizing p with
  | nil => simp [partners]
  | cons a w ih =>
    have ht := ih (p*eval [a]) (shortest_tail p a w hmin)
    cases a with
    | l => exact ht
    | x =>
      by_cases h0 : p 0=i
      · have hn := shortest_no_partner_return p i (p 1) w hmin (Or.inl ⟨h0,rfl⟩)
        simpa only [partners,headPartners,ite_eq_left h0,List.singleton_append,List.nodup_cons] using And.intro hn ht
      · by_cases h1 : p 1=i
        · have hn := shortest_no_partner_return p i (p 0) w hmin (Or.inr ⟨rfl,h1⟩)
          simpa only [partners,headPartners,ite_eq_right h0,ite_eq_left h1,List.singleton_append,List.nodup_cons] using And.intro hn ht
        · simpa only [partners,headPartners,ite_eq_right h0,ite_eq_right h1,List.nil_append] using ht

theorem partner_ne_self (hn : 2 ≤ n) (i j : Fin n) (w : List Letter) (p : State n)
    (hj : j ∈ partners i w p) : j ≠ i := by
  obtain ⟨u,_,_,hp⟩ := mem_partners i j w p hj
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  let q : State n := p*eval u
  have hne : q 0 ≠ q 1 := fun h => h01 (q.injective h)
  change HeadPair q i j at hp
  rcases hp with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact fun he => hne (h0.trans (h1.trans he).symm)
  · exact fun he => hne ((h0.trans he).trans h1.symm)

theorem shortest_partner_count (hn : 2 ≤ n) (i : Fin n) (w : List Letter) (p : State n)
    (hmin : ShortestFrom p w) : (partners i w p).length ≤ n-1 := by
  have hnd := shortest_partners_nodup i w p hmin
  have hself : i ∉ partners i w p := fun h => partner_ne_self hn i i w p h rfl
  have hc := (List.nodup_cons.mpr ⟨hself,hnd⟩).length_le_card
  simp only [List.length_cons,Fintype.card_fin] at hc
  omega

theorem shortest_from_of_length (p : State n) (w : List Letter)
    (hw : w.length=length (eval (n := n) w)) : ShortestFrom p w := by
  intro v hv
  have he : eval (n := n) v=eval w := mul_left_cancel hv
  have hh := length_le_word (n := n) v
  rw [he,← hw] at hh
  exact hh

#print axioms delete_returning_pair
#print axioms shortest_partner_count
end LX.FinitePairReduction
