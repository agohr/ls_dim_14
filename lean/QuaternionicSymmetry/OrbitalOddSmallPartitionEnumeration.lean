import QuaternionicSymmetry.OrbitalOddSelectionBijection

/-! The project's explicit partition lists exhaust all positive decreasing
partitions through weight six. -/

namespace QuaternionicSymmetry.OrbitalOddSmallPartitionEnumeration

open OrbitalOddSelectionBijection OrbitalOddRemainderSchur

set_option maxHeartbeats 1000000 in
theorem admissible_mem_partitions (k : ℕ) (hk : k ≤ 6) (lam : List ℕ)
    (hs : lam.SortedGE) (hp : ∀ a ∈ lam, 0 < a) (hw : lam.sum = k) :
    lam ∈ FiniteTypeCSchurSix.partitions k := by
  interval_cases k
  all_goals
    rcases lam with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, l⟩⟩⟩⟩⟩⟩⟩
    all_goals simp_all [FiniteTypeCSchurSix.partitions, List.sortedGE_iff_pairwise]
    all_goals omega

set_option maxHeartbeats 1000000 in
theorem listed_partition_admissible (k n : ℕ) (hk : k ≤ 6) (hn : 6 ≤ n)
    (lam : List ℕ) (hmem : lam ∈ FiniteTypeCSchurSix.partitions k) :
    lam.SortedGE ∧ lam.length ≤ n ∧ lam.sum = k ∧ ∀ a ∈ lam, 0 < a := by
  interval_cases k
  all_goals simp_all [FiniteTypeCSchurSix.partitions, List.sortedGE_iff_pairwise]
  all_goals repeat' (rcases hmem with hmem | hmem)
  all_goals
    first
    | solve | omega
    | refine ⟨by decide, ?_, by decide, by decide⟩
      simp only [List.length_cons, List.length_nil]
      omega

theorem selectionPartition_mem_partitions (n k : ℕ) (hk : k ≤ 6)
    (e : WeightedSelection n k) :
    selectionPartition e.1 ∈ FiniteTypeCSchurSix.partitions k := by
  apply admissible_mem_partitions k hk
  · exact selectionPartition_sorted e.1
  · exact selectionPartition_positive e.1
  · exact (selectionPartition_sum e.1).trans e.2

end QuaternionicSymmetry.OrbitalOddSmallPartitionEnumeration
