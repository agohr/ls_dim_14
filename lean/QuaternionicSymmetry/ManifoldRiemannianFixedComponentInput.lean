import QuaternionicSymmetry.ManifoldQuaternionicFixedTangentDimension
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The smooth embedded-submanifold part of BG-R2, Petersen Proposition
5.6.5 and its proof, printed p. 165. The component is the actual subset of
common fixed points, with its inherited topology, not an abstract type
assumed to have smaller dimension. Total geodesicity and quaternionic
curvature inheritance are separate from this limited interface.
`ManifoldRiemannianFixedComponentFromGeneral` derives this specialization
from the general fixed-component source; the final source record retains
only the general version. -/

namespace QuaternionicSymmetry.ManifoldRiemannianFixedComponentInput

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicFixedTangentDimension
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

abbrev FixedComponent (S : Subgroup (QuaternionicIsometries Q)) (x : M) :=
  ↥(connectedComponentIn (fixedPoints Q S) x)

/-- A genuine smooth atlas on the fixed subset with the inclusion's
differential identifying its tangent with the actual fixed vectors. -/
structure FixedComponentAtlas (S : Subgroup (QuaternionicIsometries Q))
    (x : M) (k : ℕ) where
  charts : ChartedSpace (EuclideanSpace ℝ (Fin k)) (FixedComponent Q S x)
  manifold : letI := charts
    IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞ (FixedComponent Q S x)
  inclusion_smooth : letI := charts
    ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E) ∞
      (Subtype.val : FixedComponent Q S x → M)
  inclusion_injective_derivative : letI := charts
    ∀ y : FixedComponent Q S x, Function.Injective
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E)
        (Subtype.val : FixedComponent Q S x → M) y)
  tangent_eq : letI := charts
    ∀ y : FixedComponent Q S x,
      LinearMap.range (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E)
        (Subtype.val : FixedComponent Q S x → M) y).toLinearMap =
      fixedTangentSpace Q S y.1 (connectedComponentIn_subset _ _ y.2)

/-- The precisely cited smooth fixed-component theorem, specialized to
the project's actual tangent metric. All manifold hypotheses are explicit
inside this universal source premise. -/
def RiemannianFixedComponentOnModel : Prop :=
  ∀ [FiniteDimensional ℝ E] [Nontrivial E] [IsManifold 𝓘(ℝ,E) ∞ M]
    [T2Space M] [SecondCountableTopology M],
    ∀ (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
      (S : Subgroup (QuaternionicIsometries Q)) (x : M),
      x ∈ fixedPoints Q S → ∃ k : ℕ, Nonempty (FixedComponentAtlas Q S x k)

end
end QuaternionicSymmetry.ManifoldRiemannianFixedComponentInput
