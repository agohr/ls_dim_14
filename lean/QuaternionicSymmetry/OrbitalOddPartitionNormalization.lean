import QuaternionicSymmetry.OrbitalOddRemainderSchur
import Mathlib.Data.List.GetD

/-! Factorial normalization is unchanged when the zero padding of a partition
is removed. -/

namespace QuaternionicSymmetry.OrbitalOddPartitionNormalization

open OrbitalOddRemainderSchur OrbitalOddOrderedSelections

noncomputable section

theorem filter_nonzero_getD_sorted (l : List ℕ)
    (hs : l.SortedGE) (k : ℕ) :
    (l.filter (· ≠ 0)).getD k 0 = l.getD k 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
      have hp : (a :: l).Pairwise (· ≥ ·) := hs.pairwise
      have htail : l.SortedGE := (List.pairwise_cons.mp hp).2.sortedGE
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

private theorem zeroFactor_prod (n k : ℕ) (z : List ℕ)
    (hz : ∀ a ∈ z, a = 0) :
    ((z.zipIdx k).map fun (part, i) =>
      ((Nat.factorial (2 * (n - (i + 1)) + 1) : ℚ) /
        (Nat.factorial (2 * (part + n - (i + 1)) + 1) : ℚ))).prod = 1 := by
  induction z generalizing k with
  | nil => simp
  | cons a z ih =>
      have ha : a = 0 := hz a (by simp)
      have hz' : ∀ b ∈ z, b = 0 := by
        intro b hb
        exact hz b (by simp [hb])
      subst a
      simp only [List.zipIdx_cons, List.map_cons, List.prod_cons]
      have hf : ((Nat.factorial (2 * (n - (k + 1)) + 1) : ℚ) /
          (Nat.factorial (2 * (0 + n - (k + 1)) + 1) : ℚ)) = 1 := by
        simp only [zero_add]
        apply div_self
        exact_mod_cast Nat.factorial_ne_zero (2 * (n - (k + 1)) + 1)
      rw [hf, one_mul]
      exact ih (k+1) hz'

theorem factorialRho_append_zeros (n : ℕ) (l : List ℕ) (r : ℕ) :
    QuarticOrbitalEleven.factorialRho n (l ++ List.replicate r 0) =
      QuarticOrbitalEleven.factorialRho n l := by
  unfold QuarticOrbitalEleven.factorialRho
  rw [List.zipIdx_append, List.map_append, List.prod_append]
  simp only [zero_add]
  rw [zeroFactor_prod n l.length (List.replicate r 0) (by simp)]
  simp

private theorem sorted_filter_append_zeros (l : List ℕ) (hs : l.SortedGE) :
    ∃ r : ℕ, l = l.filter (· ≠ 0) ++ List.replicate r 0 := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
      have hp : (a :: l).Pairwise (· ≥ ·) := hs.pairwise
      have htail : l.SortedGE := (List.pairwise_cons.mp hp).2.sortedGE
      by_cases ha : a = 0
      · have hz : ∀ b ∈ l, b = 0 := by
          intro b hb
          have hle := (List.pairwise_cons.mp hp).1 b hb
          omega
        have hlrep : l = List.replicate l.length 0 :=
          List.eq_replicate_length.mpr hz
        have hf : (a :: l).filter (· ≠ 0) = [] :=
          List.filter_eq_nil_iff.mpr (by
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · simp [ha]
            · simp [hz b hb])
        refine ⟨l.length + 1, ?_⟩
        rw [hf]
        simp only [List.nil_append]
        rw [ha, hlrep]
        simp only [List.replicate_succ]
        simp
      · obtain ⟨r, hr⟩ := ih htail
        refine ⟨r, ?_⟩
        have hdec : decide (a ≠ 0) = true := by simp [ha]
        simp only [List.filter_cons, hdec, ↓reduceIte, List.cons_append]
        exact congrArg (List.cons a) hr

theorem factorialRho_selectionPartition {n N : ℕ}
    (e : Fin n ↪o Fin N) :
    QuarticOrbitalEleven.factorialRho n (selectionPartitionRows e) =
      QuarticOrbitalEleven.factorialRho n (selectionPartition e) := by
  obtain ⟨r, hr⟩ := sorted_filter_append_zeros
    (selectionPartitionRows e) (selectionPartitionRows_sorted e)
  calc
    QuarticOrbitalEleven.factorialRho n (selectionPartitionRows e) =
        QuarticOrbitalEleven.factorialRho n
          ((selectionPartitionRows e).filter (· ≠ 0) ++ List.replicate r 0) := by
            exact congrArg (QuarticOrbitalEleven.factorialRho n) hr
    _ = QuarticOrbitalEleven.factorialRho n
          ((selectionPartitionRows e).filter (· ≠ 0)) :=
            factorialRho_append_zeros n _ r
    _ = QuarticOrbitalEleven.factorialRho n (selectionPartition e) := rfl

end
end QuaternionicSymmetry.OrbitalOddPartitionNormalization
