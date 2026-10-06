import Mathlib.Tactic
import Contracts.SortService
import Contracts.MinService

/-! The min service: its implementation, which calls the sort service through the contract in
`Contracts.SortService`, and the proof that it meets its own in `Contracts.MinService`. -/

namespace MinService

open Contracts.SortService Contracts.MinService

opaque SortServiceAPI : SortServiceStructure IO := ⟨fun l => pure l⟩

@[instance]
axiom SortServiceAPI.contract : SortServiceContract SortServiceAPI

example : SortServiceContract (⟨fun l => pure (l.mergeSort)⟩ : SortServiceStructure IO) where
  isSorted l := by grind [List.sortedLE_mergeSort]
  isPerm l := by
    ensures_intro
    exact List.isPerm_iff.2 (List.mergeSort_perm l _)

theorem sortList_perm {s l : List ℕ} (h : s.isPerm l) : s.Perm l :=
  List.isPerm_iff.1 h

theorem sortList_ne_nil {s l : List ℕ} (hp : s.isPerm l) (h : l ≠ []) : s ≠ [] := fun e =>
  h ((sortList_perm hp).symm.trans (e ▸ List.Perm.refl _) |>.eq_nil)

theorem le_getLast {s : List ℕ} (hp : s.Pairwise (· ≤ ·)) (hs : s ≠ []) {x : ℕ} (hx : x ∈ s) :
    x ≤ s.getLast hs := by
  induction s using List.reverseRecOn with
  | nil => exact absurd rfl hs
  | append_singleton s a _ =>
    rw [List.pairwise_append] at hp
    rw [List.mem_append, List.mem_singleton] at hx
    simp only [List.getLast_append_singleton]
    rcases hx with hx | rfl
    · exact hp.2.2 x hx a (by simp)
    · exact le_rfl

theorem getLastD_mem {s l : List ℕ} (hp : s.isPerm l) (h : l ≠ []) :
    s.getLastD 0 ∈ l := by
  have hs := sortList_ne_nil hp h
  simpa [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hs] using
    (sortList_perm hp).mem_iff.1 (List.getLast_mem hs)

theorem le_getLastD {s l : List ℕ} (hs : s.SortedLE) (hp : s.isPerm l) (h : l ≠ [])
    {a : ℕ} (ha : a ∈ l) : a ≤ s.getLastD 0 := by
  have hn := sortList_ne_nil hp h
  simpa [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hn] using
    le_getLast (List.sortedLE_iff_pairwise.1 hs) hn ((sortList_perm hp).mem_iff.2 ha)

def MinServiceAPI : MinServiceStructure IO where
  maxElem {l} _ := do
    let s ← SortServiceAPI.sortList l
    pure (s.getLastD 0)

instance : MinServiceContract MinServiceAPI where
  maxElemIsElem {l} h := by grind [MinServiceAPI, getLastD_mem]
  maxElemIsMax {l} h := by
    ensures_intro [MinServiceAPI]
    exact fun a ha => le_getLastD s_isSorted s_isPerm h ha

end MinService
