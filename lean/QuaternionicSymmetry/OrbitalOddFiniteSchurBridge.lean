import QuaternionicSymmetry.OrbitalOddSmallPartitionEnumeration
import QuaternionicSymmetry.OrbitalOddCompanionTableSpecialization
import QuaternionicSymmetry.OrbitalOddNewtonSpecialization
import QuaternionicSymmetry.OrbitalCompanionSchurLongShapes

/-! Identification of the finite odd orbital coefficients with the project's
explicit type-C Schur polynomials through weight six. -/

namespace QuaternionicSymmetry.OrbitalOddFiniteSchurBridge

open OrbitalOddRemainderSchur OrbitalOddCompanionTableSpecialization
open OrbitalOddNewtonSpecialization OrbitalOddSmallPartitionEnumeration
open OrbitalOddFormalKernel OrbitalOddSelectionBijection
open OrbitalOddOrderedSelections
open OrbitalOddSchurTwo
open OrbitalOddDeterminantBase

noncomputable section

theorem remainderSchurOnSquares_eq_schur (m k : ℕ) (hm : 5 ≤ m)
    (hk : k ≤ 6) (x : Fin (m+6) → ℚ)
    (e : Fin (m+6) ↪o Fin (m+6+k))
    (hw : (selectionPartitionRows e).sum = k) :
    remainderSchurOnSquares x e =
      OrbitalOddSchurWeightOne.schurEvalOnSquares x (selectionPartition e) := by
  rw [remainderSchurOnSquares_eq_tailMatrix m (m+6+k) hm x e (hw.le.trans hk)]
  rw [OrbitalCompanionSchurLongShapes.tailMatrix_det_eq_schurValue
    (fun r => elementary (m+6) r
      (fun i => x i ^ 2)) k hk (selectionPartition e)
    (selectionPartition_mem_partitions (m+6) k hk ⟨e, hw⟩)]
  exact schurValue_spectral (m+6) x (selectionPartition e)

theorem sum_weightedSelections_eq_partitions (n k : ℕ) (hn : 6 ≤ n)
    (hk : k ≤ 6) (f : List ℕ → ℚ) :
    (∑ e : Fin n ↪o Fin (n+k),
      if k = (selectionPartitionRows e).sum then f (selectionPartition e) else 0) =
      ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset, f lam := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun e _ => selectionPartition e) ?_ ?_ ?_ ?_
  · intro e he
    have hw : (selectionPartitionRows e).sum = k := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm] using he
    exact List.mem_toFinset.mpr
      (selectionPartition_mem_partitions n k hk ⟨e, hw⟩)
  · intro e he e' he' heq
    have hw : (selectionPartitionRows e).sum = k := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm] using he
    have hw' : (selectionPartitionRows e').sum = k := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm] using he'
    change selectionPartition e = selectionPartition e' at heq
    have hp : (weightedSelectionEquivPartition n k ⟨e, hw⟩) =
        weightedSelectionEquivPartition n k ⟨e', hw'⟩ := Subtype.ext heq
    have hs := (weightedSelectionEquivPartition n k).injective hp
    exact congrArg Subtype.val hs
  · intro lam hlam
    have hmem : lam ∈ FiniteTypeCSchurSix.partitions k :=
      List.mem_toFinset.mp hlam
    obtain ⟨hs, hlen, hsum, hp⟩ :=
      listed_partition_admissible k n hk hn lam hmem
    let e := selectionOfPartition n k lam hs hsum
    refine ⟨e, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← selectionPartition_sum,
        selectionOfPartition_right_inverse n k lam hs hsum hlen hp]
      exact hsum.symm
    · exact selectionOfPartition_right_inverse n k lam hs hsum hlen hp
  · intro e _
    rfl

/-- The source-normalized finite odd determinant has the Schur expansion
through every weight required by the degree-six project tables. -/
theorem sourceFullFormalOddKernel_coeff_schur (m k : ℕ) (hm : 5 ≤ m)
    (hk : k ≤ 6) (x y : Fin (m+6) → ℚ) :
    sourceConstant (m+6) *
      PowerSeries.coeff ((m+6) ^ 2 + 2*k)
        (sourceFullFormalOddKernel x y).det =
      oddVandermonde x * oddVandermonde y *
        ∑ e : Fin (m+6) ↪o Fin (m+6+k),
          if k = (selectionPartitionRows e).sum then
            QuarticOrbitalEleven.factorialRho (m+6) (selectionPartition e) *
              OrbitalOddSchurWeightOne.schurEvalOnSquares x (selectionPartition e) *
                OrbitalOddSchurWeightOne.schurEvalOnSquares y (selectionPartition e)
          else 0 := by
  rw [sourceFullFormalOddKernel_coeff_remainderSchur]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with h
  · rw [OrbitalOddPartitionNormalization.factorialRho_selectionPartition]
    rw [remainderSchurOnSquares_eq_schur m k hm hk x e h.symm,
      remainderSchurOnSquares_eq_schur m k hm hk y e h.symm]
  · rfl

/-- Explicit partition-indexed form of the source-normalized odd determinant
coefficient, valid uniformly for every rank at least eleven and weight at most
six. -/
theorem sourceFullFormalOddKernel_coeff_finiteSchur (m k : ℕ) (hm : 5 ≤ m)
    (hk : k ≤ 6) (x y : Fin (m+6) → ℚ) :
    sourceConstant (m+6) *
      PowerSeries.coeff ((m+6) ^ 2 + 2*k)
        (sourceFullFormalOddKernel x y).det =
      oddVandermonde x * oddVandermonde y *
        ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
          QuarticOrbitalEleven.factorialRho (m+6) lam *
            OrbitalOddSchurWeightOne.schurEvalOnSquares x lam *
              OrbitalOddSchurWeightOne.schurEvalOnSquares y lam := by
  rw [sourceFullFormalOddKernel_coeff_schur m k hm hk x y]
  congr 1
  exact sum_weightedSelections_eq_partitions (m+6) k (by omega) hk
    (fun lam => QuarticOrbitalEleven.factorialRho (m+6) lam *
      OrbitalOddSchurWeightOne.schurEvalOnSquares x lam *
        OrbitalOddSchurWeightOne.schurEvalOnSquares y lam)

/-- Evaluate the project's polynomial orbital coefficient at a rational
spectral power-sum point. The hypothesis expresses that its listed integer
spectrum has the same six power sums as the squared `x` spectrum. -/
theorem orbital_aeval_eq_schur_sum (n k : ℕ) (a : List ℕ)
    (x y : Fin n → ℚ)
    (hpower : ∀ i : Fin 6,
      FiniteTypeCSchurSix.powerSum a (i.val+1) =
        ∑ j : Fin n, (x j ^ 2) ^ (i.val+1)) :
    MvPolynomial.aeval
      (fun i : Fin 6 => ∑ j : Fin n, (y j ^ 2) ^ (i.val+1))
      (FiniteTypeCSchurSix.orbital n k a) =
    (4 : ℚ)^k *
      ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
        QuarticOrbitalEleven.factorialRho n lam *
          OrbitalOddSchurWeightOne.schurEvalOnSquares x lam *
            OrbitalOddSchurWeightOne.schurEvalOnSquares y lam := by
  unfold FiniteTypeCSchurSix.orbital
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lam _
  have hx : FiniteTypeCSchurSix.schurValue a lam =
      OrbitalOddSchurWeightOne.schurEvalOnSquares x lam := by
    unfold FiniteTypeCSchurSix.schurValue
      OrbitalOddSchurWeightOne.schurEvalOnSquares
    exact congrArg
      (fun f : Fin 6 → ℚ => MvPolynomial.aeval f
        (FiniteTypeCSchurSix.schur lam)) (funext hpower)
  rw [hx]
  change (4 : ℚ)^k * QuarticOrbitalEleven.factorialRho n lam *
      OrbitalOddSchurWeightOne.schurEvalOnSquares x lam *
        OrbitalOddSchurWeightOne.schurEvalOnSquares y lam = _
  ring

theorem sourceFullFormalOddKernel_coeff_orbital (m k : ℕ) (hm : 5 ≤ m)
    (hk : k ≤ 6) (a : List ℕ) (x y : Fin (m+6) → ℚ)
    (hpower : ∀ i : Fin 6,
      FiniteTypeCSchurSix.powerSum a (i.val+1) =
        ∑ j : Fin (m+6), (x j ^ 2) ^ (i.val+1)) :
    (4 : ℚ)^k * sourceConstant (m+6) *
      PowerSeries.coeff ((m+6) ^ 2 + 2*k)
        (sourceFullFormalOddKernel x y).det =
      oddVandermonde x * oddVandermonde y *
        MvPolynomial.aeval
          (fun i : Fin 6 => ∑ j : Fin (m+6), (y j ^ 2) ^ (i.val+1))
          (FiniteTypeCSchurSix.orbital (m+6) k a) := by
  rw [orbital_aeval_eq_schur_sum (m+6) k a x y hpower]
  have h := sourceFullFormalOddKernel_coeff_finiteSchur m k hm hk x y
  calc
    _ = (4 : ℚ)^k * (sourceConstant (m+6) *
          PowerSeries.coeff ((m+6) ^ 2 + 2*k)
            (sourceFullFormalOddKernel x y).det) := by ring
    _ = _ := by rw [h]; ring

end
end QuaternionicSymmetry.OrbitalOddFiniteSchurBridge
