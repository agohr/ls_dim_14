import QuaternionicSymmetry.ManifoldFormLocalization
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! On a compact smooth manifold a finite smooth partition subordinate to
actual coordinate charts decomposes each tangent form into chart-supported
smooth summands. -/
namespace QuaternionicSymmetry.ManifoldFiniteFormPartition

open Set ManifoldDifferentialForms ManifoldFormLocalization
open scoped Manifold ContDiff Topology
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_finite_chart_partition :
    ∃ (s : Finset M) (ρ : SmoothPartitionOfUnity s 𝓘(ℝ, E) M Set.univ),
      ρ.IsSubordinate (fun i => (chartAt E (i : M)).source) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun p : M => (chartAt E p).source) (fun p => (chartAt E p).open_source)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, mem_chart_source E x⟩)
  have hcover : (Set.univ : Set M) ⊆ ⋃ i : s, (chartAt E (i : M)).source := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E)
    isClosed_univ (fun i : s => (chartAt E (i : M)).source)
    (fun i => (chartAt E (i : M)).open_source) hcover
  exact ⟨s, ρ, hρ⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem partition_sum_form {ι : Type*} [Fintype ι]
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M Set.univ)
    {n : ℕ} (α : Form 𝓘(ℝ, E) M n) :
    ∑ i, scalarMultiply (ρ i) α = α := by
  apply finite_sum_scalarMultiply
  intro x
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] in
theorem partition_summand_smooth {ι : Type*}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M Set.univ)
    {n : ℕ} (α : Form 𝓘(ℝ, E) M n) (hα : ChartSmooth α) (i : ι) :
    ChartSmooth (scalarMultiply (ρ i) α) :=
  scalarMultiply_smooth _ _ (ρ i).contMDiff hα

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] in
theorem partition_sum_exteriorDerivative {ι : Type*} [Fintype ι]
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M Set.univ)
    {n : ℕ} (α : Form 𝓘(ℝ, E) M n) (hα : ChartSmooth α) :
    ∑ i, exteriorDerivative (scalarMultiply (ρ i) α) = exteriorDerivative α := by
  classical
  let β (i : ι) : smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := n) :=
    ⟨scalarMultiply (ρ i) α, partition_summand_smooth ρ α hα i⟩
  have hs : ∑ i, β i = ⟨α, hα⟩ := by
    apply Subtype.ext
    simpa [β] using partition_sum_form ρ α
  have hd := congrArg (smoothExteriorDerivative (E := E) (M₀ := M) n) hs
  rw [map_sum] at hd
  have hv := congrArg (fun z : smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := n + 1) =>
    z.val) hd
  simpa [β, smoothExteriorDerivative] using hv

end QuaternionicSymmetry.ManifoldFiniteFormPartition
