import QuaternionicSymmetry.ManifoldSurjectiveDerivativeNeighborhood
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen

/-! A smooth group homomorphism with surjective derivative at the identity
has open image, hence is onto when its target is connected. These are
internal consequences of the actual manifold derivative and group laws. -/

namespace QuaternionicSymmetry.SmoothGroupHomSurjectiveDerivative

open ManifoldSurjectiveDerivativeNeighborhood
open scoped Manifold ContDiff Topology

noncomputable section

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [IsManifold 𝓘(ℝ, E) ∞ G]
  [Group H] [TopologicalSpace H] [ChartedSpace F H] [IsManifold 𝓘(ℝ, F) ∞ H]
  [ContinuousMul H]

/-- Surjectivity of the genuine derivative at `1` makes the actual
homomorphism range an open subgroup. No closed-image premise is needed. -/
theorem isOpen_range_of_surjective_mfderiv_one
    (f : G →* H) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hdf : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f 1)) :
    IsOpen (Set.range f) := by
  have h := range_mem_nhds_of_surjective_mfderiv (f : G → H) hf 1 hdf
  exact f.range.isOpen_of_mem_nhds h

/-- A smooth homomorphism into a connected group is onto when its actual
identity derivative is onto. This does not require complex-linearity of
any real parametrization. -/
theorem surjective_of_surjective_mfderiv_one [PreconnectedSpace H]
    (f : G →* H) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hdf : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f 1)) :
    Function.Surjective f := by
  have hopen : IsOpen (f.range : Set H) :=
    isOpen_range_of_surjective_mfderiv_one f hf hdf
  have hclosed := f.range.isClosed_of_isOpen hopen
  have hall : (f.range : Set H) = Set.univ :=
    (show IsClopen (f.range : Set H) from ⟨hclosed, hopen⟩).eq_univ
      ⟨1, f.range.one_mem⟩
  intro y
  have hy : y ∈ f.range := by
    change y ∈ (f.range : Set H)
    rw [hall]
    trivial
  exact hy

end

end QuaternionicSymmetry.SmoothGroupHomSurjectiveDerivative
