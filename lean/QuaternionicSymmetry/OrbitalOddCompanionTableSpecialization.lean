import QuaternionicSymmetry.OrbitalOddCompanionSpecialization
import QuaternionicSymmetry.OrbitalCompanionSchurTable
import Mathlib.Data.List.GetD

/-! Specialization of the universal finite companion table to spectral roots. -/

namespace QuaternionicSymmetry.OrbitalOddCompanionTableSpecialization

open Matrix
open OrbitalOddRemainderSchur OrbitalOddSchurTwo
open OrbitalOddCompanionSpecialization OrbitalCompanionSchurTable
open OrbitalOddOrderedSelections OrbitalOddFormalKernel

noncomputable section

private theorem filter_nonzero_getD_sorted (l : List ℕ)
    (hs : l.SortedGE) (k : ℕ) :
    (l.filter (· ≠ 0)).getD k 0 = l.getD k 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
      have hp : (a :: l).Pairwise (· ≥ ·) := hs.pairwise
      have htail : l.SortedGE := by
        exact (List.pairwise_cons.mp hp).2.sortedGE
      by_cases ha : a = 0
      · have hz : ∀ x ∈ l, x = 0 := by
          intro x hx
          have hle := (List.pairwise_cons.mp hp).1 x hx
          omega
        have hf : l.filter (· ≠ 0) = [] :=
          List.filter_eq_nil_iff.mpr (by simpa using hz)
        have hget : ∀ j, l.getD j 0 = 0 := by
          intro j
          by_cases hj : j < l.length
          · rw [List.getD_eq_getElem l 0 hj]
            exact hz _ (List.getElem_mem hj)
          · rw [List.getD_eq_default l 0 (Nat.le_of_not_gt hj)]
        have hdec : decide (a ≠ 0) = false := by simp [ha]
        cases k with
        | zero =>
            simp only [List.filter_cons, hdec, Bool.false_eq_true, ↓reduceIte]
            rw [hf]
            simp [ha]
        | succ k =>
            simp only [List.filter_cons, hdec, Bool.false_eq_true, ↓reduceIte]
            rw [hf]
            simpa using (hget k).symm
      · cases k with
        | zero => simp [ha]
        | succ k => simpa [ha] using ih htail k

theorem selectionPartition_tailOffset (m N : ℕ)
    (e : Fin (m+6) ↪o Fin N) (b : Fin 6) :
    selectionOffset e (Fin.natAdd m b) =
      ((selectionPartition e)[5-b.val]?).getD 0 := by
  have hs := selectionPartitionRows_sorted e
  have hfilter := filter_nonzero_getD_sorted (selectionPartitionRows e) hs (5-b.val)
  have hk : 5-b.val < m+6 := by have := b.isLt; omega
  have hrev : Fin.rev (⟨5-b.val, hk⟩ : Fin (m+6)) = Fin.natAdd m b := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_natAdd]
    have := b.isLt
    omega
  change selectionOffset e (Fin.natAdd m b) =
    ((selectionPartitionRows e).filter (· ≠ 0)).getD (5-b.val) 0
  rw [hfilter]
  have hlen : (selectionPartitionRows e).length = m+6 := by
    simp [selectionPartitionRows]
  rw [List.getD_eq_getElem (selectionPartitionRows e) 0 (by
    rw [hlen]
    exact hk)]
  simp only [selectionPartitionRows, List.getElem_ofFn, hrev]

theorem spectralTail_eq_remainder {n s d : ℕ} (t : Fin n → ℚ)
    (hdpos : 0 < d) (hbound : d + s ≤ n) :
    spectralTail n s d t =
      remainder (fun r => elementary n r t) s d := by
  induction s generalizing d with
  | zero =>
      rw [spectralTail_zero t hdpos (by omega)]
      simp only [remainder]
      ring
  | succ s ih =>
      have hd : d < n := by omega
      rw [spectralTail_succ t hdpos hd]
      simp only [remainder]
      rw [ih (d := d+1) (by omega) (by omega),
        ih (d := 1) (by omega) (by omega)]

/-- The actual final six-by-six spectral remainder block is the universal
companion matrix when its partition row offsets are supplied. -/
theorem remainder_sixBlock_eq_tailMatrix (m N : ℕ) (hm : 5 ≤ m)
    (t : Fin (m+6) → ℚ) (e : Fin (m+6) ↪o Fin N) (lam : List ℕ)
    (hweight : (selectionPartitionRows e).sum ≤ 6)
    (hrows : ∀ b : Fin 6,
      selectionOffset e (Fin.natAdd m b) = (lam[5-b.val]?).getD 0) :
    (remainderCoefficientMatrix t e).submatrix
      (Fin.natAdd m) (Fin.natAdd m) =
        tailMatrix (fun r => elementary (m+6) r t) lam := by
  ext a b
  let i : Fin (m+6) := Fin.natAdd m a
  let j : Fin (m+6) := Fin.natAdd m b
  let q : ℕ := b.val + (lam[5-b.val]?).getD 0
  have hbound := OrbitalOddFormalKernel.orderEmbedding_index_le e j
  have hje : j.val = m+b.val := Fin.val_natAdd m b
  have hrow : selectionOffset e j = (lam[5-b.val]?).getD 0 := by
    exact hrows b
  have hj : (e j).val = m + q := by
    have ho := hrow
    simp only [OrbitalOddOrderedSelections.selectionOffset] at ho
    dsimp [q]
    omega
  have hqle : q ≤ 11 := by
    have ho : selectionOffset e j ≤ ∑ z : Fin (m+6), selectionOffset e z :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hsum : (∑ z : Fin (m+6), selectionOffset e z) ≤ 6 := by
      simpa [selectionPartitionRows_sum] using hweight
    have hb := b.isLt
    dsimp [q]
    rw [hrow] at ho
    omega
  rw [Matrix.submatrix_apply,
    OrbitalOddCompanionSpecialization.remainderCoefficientMatrix_entry]
  change (if (e j).val < m+6 then
      if i.val = (e j).val then 1 else 0
    else spectralTail (m+6) ((e j).val-(m+6)) ((m+6)-i.val) t) =
    tailMatrix (fun r => elementary (m+6) r t) lam a b
  change (if (e j).val < m+6 then
      if i.val = (e j).val then 1 else 0
    else spectralTail (m+6) ((e j).val-(m+6)) ((m+6)-i.val) t) =
    (if q < 6 then if a.val = q then 1 else 0
      else remainder (fun r => elementary (m+6) r t) (q-6) (6-a.val))
  by_cases hq : q < 6
  · have he : (e j).val < m+6 := by omega
    simp only [if_pos he, if_pos hq]
    have hival : i.val = m+a.val := Fin.val_natAdd m a
    rw [hival, hj]
    simp only [Nat.add_left_cancel_iff]
  · have he : ¬(e j).val < m+6 := by omega
    simp only [if_neg he, if_neg hq]
    have hs : (e j).val-(m+6) = q-6 := by omega
    have hd : (m+6)-i.val = 6-a.val := by
      simp only [i, Fin.val_natAdd]
      omega
    rw [hs, hd]
    have hdpos : 0 < 6-a.val := by omega
    have hcomp : (6-a.val)+(q-6) ≤ m+6 := by omega
    exact spectralTail_eq_remainder t hdpos hcomp

/-- The selected odd alternant's Schur candidate specializes exactly to the
universal six-column companion determinant in every rank at least eleven. -/
theorem remainderSchurOnSquares_eq_tailMatrix (m N : ℕ) (hm : 5 ≤ m)
    (x : Fin (m+6) → ℚ) (e : Fin (m+6) ↪o Fin N)
    (hweight : (selectionPartitionRows e).sum ≤ 6) :
    remainderSchurOnSquares x e =
      (tailMatrix (fun r => elementary (m+6) r (fun i => x i ^ 2))
        (selectionPartition e)).det := by
  rw [remainderSchurOnSquares_eq_sixBlock m N x e hweight]
  rw [remainder_sixBlock_eq_tailMatrix m N hm
    (fun i => x i ^ 2) e (selectionPartition e) hweight
    (selectionPartition_tailOffset m N e)]

end
end QuaternionicSymmetry.OrbitalOddCompanionTableSpecialization
