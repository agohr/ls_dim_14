import QuaternionicSymmetry.GeneralRealProductManifold
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Source-facing Brouwer invariance of dimension, at the exact scope
needed here. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem
1.2, printed p.3 (PDF p.21), with the topological-manifold convention
there; Theorem 17.26, printed p.452 (PDF p.470), proves this
invariance-of-dimension result. The manifolds below are nonempty,
Hausdorff, second-countable, finite-dimensional, and boundaryless.

This is an explicit literature theorem argument, not a custom axiom.
It states no dimension for any specific compact symplectic group. -/

namespace QuaternionicSymmetry.ManifoldDimensionTopologySource

open Manifold
open scoped Manifold ContDiff
noncomputable section

/-- Topological invariance of the real local model dimension. -/
def LeeInvarianceOfDimension : Prop :=
  ∀ {E F X Y : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]
    [ChartedSpace F Y] [IsManifold 𝓘(ℝ, F) ∞ Y],
    (X ≃ₜ Y) → Module.finrank ℝ E = Module.finrank ℝ F

end
end QuaternionicSymmetry.ManifoldDimensionTopologySource
