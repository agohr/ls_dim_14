import QuaternionicSymmetry.OrbitalOddPartitionNormalization
import Mathlib.Data.List.GetD

/-! Construct increasing exponent selections from partitions. -/

namespace QuaternionicSymmetry.OrbitalOddSelectionBijection

open OrbitalOddRemainderSchur OrbitalOddOrderedSelections
open OrbitalOddFormalKernel

noncomputable section

theorem sorted_getD_antitone (l : List ℕ) (hs : l.SortedGE) :
    Antitone (fun j : ℕ => l.getD j 0) := by
  intro i j hij
  change l.getD j 0 ≤ l.getD i 0
  by_cases hi : i < l.length
  · by_cases hj : j < l.length
    · rw [List.getD_eq_getElem l 0 hi,
        List.getD_eq_getElem l 0 hj]
      exact hs.getElem_ge_getElem_of_le hij
    · rw [List.getD_eq_default l 0 (Nat.le_of_not_gt hj)]
      exact Nat.zero_le _
  · have hj : ¬j < l.length := by omega
    rw [List.getD_eq_default l 0 (Nat.le_of_not_gt hi),
      List.getD_eq_default l 0 (Nat.le_of_not_gt hj)]

theorem getD_le_sum (l : List ℕ) (j : ℕ) : l.getD j 0 ≤ l.sum := by
  by_cases hj : j < l.length
  · rw [List.getD_eq_getElem l 0 hj]
    exact List.le_sum_of_mem (List.getElem_mem hj)
  · rw [List.getD_eq_default l 0 (Nat.le_of_not_gt hj)]
    exact Nat.zero_le _

def selectionOfPartition (n k : ℕ) (lam : List ℕ)
    (hs : lam.SortedGE) (hsum : lam.sum = k) :
    Fin n ↪o Fin (n+k) :=
  OrderEmbedding.ofStrictMono
    (fun i : Fin n =>
      ⟨i.val + lam.getD (n-1-i.val) 0, by
        have hi := i.isLt
        have hle := getD_le_sum lam (n-1-i.val)
        omega⟩)
    (by
      intro i j hij
      apply Fin.lt_def.mpr
      have hidx : n-1-j.val ≤ n-1-i.val := by
        have hi := i.isLt
        have hj := j.isLt
        omega
      have hmon := sorted_getD_antitone lam hs hidx
      change lam.getD (n-1-i.val) 0 ≤
        lam.getD (n-1-j.val) 0 at hmon
      have hij' := Fin.lt_def.mp hij
      dsimp
      omega)

theorem selectionOfPartition_apply (n k : ℕ) (lam : List ℕ)
    (hs : lam.SortedGE) (hsum : lam.sum = k)
    (i : Fin n) :
    ((selectionOfPartition n k lam hs hsum) i).val =
      i.val + lam.getD (n-1-i.val) 0 := rfl

theorem selectionOfPartition_offset (n k : ℕ) (lam : List ℕ)
    (hs : lam.SortedGE) (hsum : lam.sum = k) (i : Fin n) :
    selectionOffset (selectionOfPartition n k lam hs hsum) i =
      lam.getD (n-1-i.val) 0 := by
  simp [selectionOffset, selectionOfPartition_apply]

private theorem ofFn_getD_eq_append_zeros (n : ℕ) (lam : List ℕ)
    (hlen : lam.length ≤ n) :
    List.ofFn (fun i : Fin n => lam.getD i.val 0) =
      lam ++ List.replicate (n-lam.length) 0 := by
  apply List.ext_getElem
  · simp [Nat.add_sub_of_le hlen]
  · intro i hi hright
    rw [List.getElem_ofFn]
    by_cases h : i < lam.length
    · rw [List.getElem_append_left h,
        List.getD_eq_getElem lam 0 h]
    · rw [List.getElem_append_right (Nat.le_of_not_gt h),
        List.getD_eq_default lam 0 (Nat.le_of_not_gt h)]
      simp

theorem selectionOfPartition_rows (n k : ℕ) (lam : List ℕ)
    (hs : lam.SortedGE) (hsum : lam.sum = k)
    (hlen : lam.length ≤ n) :
    selectionPartitionRows (selectionOfPartition n k lam hs hsum) =
      lam ++ List.replicate (n-lam.length) 0 := by
  have hfn : (fun j : Fin n =>
      selectionOffset (selectionOfPartition n k lam hs hsum) (Fin.rev j)) =
      (fun j : Fin n => lam.getD j.val 0) := by
    funext j
    rw [selectionOfPartition_offset]
    have hj := j.isLt
    simp only [Fin.val_rev]
    congr 1
    omega
  unfold selectionPartitionRows
  rw [hfn]
  exact ofFn_getD_eq_append_zeros n lam hlen

theorem selectionOfPartition_right_inverse (n k : ℕ) (lam : List ℕ)
    (hs : lam.SortedGE) (hsum : lam.sum = k)
    (hlen : lam.length ≤ n)
    (hpos : ∀ a ∈ lam, 0 < a) :
    selectionPartition (selectionOfPartition n k lam hs hsum) = lam := by
  unfold selectionPartition
  rw [selectionOfPartition_rows n k lam hs hsum hlen,
    List.filter_append, List.filter_replicate]
  have hfilter : lam.filter (· ≠ 0) = lam :=
    List.filter_eq_self.mpr (by
      intro a ha
      simp [Nat.ne_of_gt (hpos a ha)])
  rw [hfilter]
  simp

theorem selectionPartition_sorted {n N : ℕ} (e : Fin n ↪o Fin N) :
    (selectionPartition e).SortedGE := by
  exact ((selectionPartitionRows_sorted e).pairwise.filter (· ≠ 0)).sortedGE

theorem selectionPartition_length_le {n N : ℕ} (e : Fin n ↪o Fin N) :
    (selectionPartition e).length ≤ n := by
  change ((selectionPartitionRows e).filter (· ≠ 0)).length ≤ n
  calc
    _ ≤ (selectionPartitionRows e).length := List.length_filter_le _ _
    _ = n := by simp [selectionPartitionRows]

theorem selectionPartition_positive {n N : ℕ} (e : Fin n ↪o Fin N) :
    ∀ a ∈ selectionPartition e, 0 < a := by
  intro a ha
  have h := (List.mem_filter.mp ha).2
  have hne : a ≠ 0 := by simpa using h
  exact Nat.pos_of_ne_zero hne

theorem selectionOfPartition_left_inverse (n k : ℕ)
    (e : Fin n ↪o Fin (n+k))
    (hweight : (selectionPartitionRows e).sum = k) :
    selectionOfPartition n k (selectionPartition e)
      (selectionPartition_sorted e)
      ((selectionPartition_sum e).trans hweight) = e := by
  ext i
  rw [selectionOfPartition_apply]
  let j : ℕ := n-1-i.val
  have hj : j < n := by
    have hi := i.isLt
    dsimp [j]
    omega
  have hfilter := OrbitalOddPartitionNormalization.filter_nonzero_getD_sorted
    (selectionPartitionRows e) (selectionPartitionRows_sorted e) j
  have hlen : (selectionPartitionRows e).length = n := by
    simp [selectionPartitionRows]
  have hget : (selectionPartition e).getD j 0 = selectionOffset e i := by
    change ((selectionPartitionRows e).filter (· ≠ 0)).getD j 0 = _
    rw [hfilter, List.getD_eq_getElem (selectionPartitionRows e) 0 (by
      rw [hlen]
      exact hj)]
    have hrev : Fin.rev (⟨j, hj⟩ : Fin n) = i := by
      apply Fin.ext
      simp only [Fin.val_rev]
      dsimp [j]
      have hi := i.isLt
      omega
    simp only [selectionPartitionRows, List.getElem_ofFn, hrev]
  change i.val + (selectionPartition e).getD j 0 = (e i).val
  rw [hget]
  have hbound := orderEmbedding_index_le e i
  simp only [selectionOffset]
  omega

def WeightedSelection (n k : ℕ) :=
  {e : Fin n ↪o Fin (n+k) // (selectionPartitionRows e).sum = k}

def AdmissiblePartition (n k : ℕ) :=
  {lam : List ℕ // lam.SortedGE ∧ lam.length ≤ n ∧ lam.sum = k ∧
    ∀ a ∈ lam, 0 < a}

def weightedSelectionEquivPartition (n k : ℕ) :
    WeightedSelection n k ≃ AdmissiblePartition n k where
  toFun e := ⟨selectionPartition e.1,
    selectionPartition_sorted e.1,
    selectionPartition_length_le e.1,
    (selectionPartition_sum e.1).trans e.2,
    selectionPartition_positive e.1⟩
  invFun lam := ⟨selectionOfPartition n k lam.1 lam.2.1 lam.2.2.2.1, by
    rw [← selectionPartition_sum,
      selectionOfPartition_right_inverse n k lam.1 lam.2.1
        lam.2.2.2.1 lam.2.2.1 lam.2.2.2.2]
    exact lam.2.2.2.1⟩
  left_inv e := by
    apply Subtype.ext
    exact selectionOfPartition_left_inverse n k e.1 e.2
  right_inv lam := by
    apply Subtype.ext
    exact selectionOfPartition_right_inverse n k lam.1 lam.2.1
      lam.2.2.2.1 lam.2.2.1 lam.2.2.2.2

end
end QuaternionicSymmetry.OrbitalOddSelectionBijection
