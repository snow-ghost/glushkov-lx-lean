import LRX.SuffixComponentTransfer
import LRX.ReversalWindowFamily

namespace LRX.FiniteWindow
open FiniteCuts RotationWords
variable {n b c : ℕ}

def pullSuffixWindow (W : Window n b) (hend : W.offset+b = n)
    (V : Window n c) (hstart : W.offset ≤ V.offset) : Window b c where
  offset := V.offset-W.offset
  fits := by have := V.fits; omega

theorem embed_pull_suffix (W : Window n b) (hend : W.offset+b = n)
    (V : Window n c) (hstart : W.offset ≤ V.offset) (i : Fin c) :
    embed W (embed (pullSuffixWindow W hend V hstart) i) = embed V i := by
  apply Fin.ext
  dsimp [embed,pullSuffixWindow]
  omega

theorem contains_pull_suffix (W : Window n b) (hend : W.offset+b = n)
    (V : Window n c) (hstart : W.offset ≤ V.offset) (i : Fin b) :
    Contains (pullSuffixWindow W hend V hstart) i ↔ Contains V (embed W i) := by
  unfold Contains
  dsimp [pullSuffixWindow,embed]
  omega

def pullSuffixFilling (W : Window n b) (hend : W.offset+b = n)
    (A : FillingWindow n) (hstart : W.offset ≤ A.window.offset) : FillingWindow b :=
  ⟨A.size,pullSuffixWindow W hend A.window hstart,A.filling⟩

theorem pull_suffix_filling_matches (W : Window n b) (hend : W.offset+b = n)
    (p : State n) (f : State b) (hmatch : ∀ i, p (embed W i) = embed W (f i))
    (A : FillingWindow n) (hstart : W.offset ≤ A.window.offset) (hA : A.Matches p) :
    (pullSuffixFilling W hend A hstart).Matches f := by
  intro i
  change Fin A.size at i
  apply embed_injective W
  change embed W (f (embed (pullSuffixWindow W hend A.window hstart) i)) =
    embed W (embed (pullSuffixWindow W hend A.window hstart) (A.filling i))
  rw [← hmatch,embed_pull_suffix,embed_pull_suffix]
  exact hA i

theorem pull_suffix_fillings_apart (W : Window n b) (hend : W.offset+b = n)
    (A B : FillingWindow n) (hA : W.offset ≤ A.window.offset) (hB : W.offset ≤ B.window.offset)
    (hAB : A.Apart B) :
    (pullSuffixFilling W hend A hA).Apart (pullSuffixFilling W hend B hB) := by
  intro i hi hj
  exact hAB (embed W i) ((contains_pull_suffix W hend A.window hA i).mp hi)
    ((contains_pull_suffix W hend B.window hB i).mp hj)

theorem pull_suffix_filling_deficit (W : Window n b) (hend : W.offset+b = n)
    (A : FillingWindow n) (hstart : W.offset ≤ A.window.offset) :
    (pullSuffixFilling W hend A hstart).deficit = A.deficit := rfl

theorem pull_suffix_internal_load [NeZero n] [NeZero b]
    (W : Window n b) (hend : W.offset+b = n)
    (p : State n) (f : State b) (hmatch : ∀ i, p (embed W i) = embed W (f i))
    (A : FillingWindow n) (hstart : W.offset ≤ A.window.offset)
    (hloaded : ∀ r : Fin n, A.window.offset < r.val+1 →
      r.val+1 < A.window.offset+A.size → 0 < portLoad (displacement p) r)
    (r : Fin b)
    (hr : (pullSuffixFilling W hend A hstart).window.offset < r.val+1)
    (hr' : r.val+1 < (pullSuffixFilling W hend A hstart).window.offset+A.size) :
    0 < portLoad (displacement f) r := by
  change A.window.offset-W.offset < r.val+1 at hr
  change r.val+1 < A.window.offset-W.offset+A.size at hr'
  have hh := hloaded (embed W r) (by dsimp [embed]; omega) (by dsimp [embed]; omega)
  rw [suffix_port_load W hend p f hmatch] at hh
  exact hh

#print axioms pull_suffix_filling_matches
#print axioms pull_suffix_internal_load
end LRX.FiniteWindow
