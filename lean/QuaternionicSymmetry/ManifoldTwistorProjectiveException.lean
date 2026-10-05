import QuaternionicSymmetry.ManifoldTwistorFullAutomorphisms
import QuaternionicSymmetry.ComplexProjectiveManifold
import Mathlib.Geometry.Manifold.Diffeomorph

/-! The literal complex-projective twistor exception in BWW 6.5,
expressed as an actual biholomorphism to `CP^(2n+1)` rather than an opaque
classification flag. Excluding this projective case is slightly stronger
than excluding only the paired `HP^n/CP^(2n+1)` case, hence safe for a
nonprojective specialization of that theorem. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveException

open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ComplexProjectiveTopology
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)

def IsComplexProjectiveTwistor : Prop :=
  letI := B.charts
  Nonempty (Diffeomorph 𝓘(ℂ,ComplexTwistorModel n)
    𝓘(ℂ, Fin (2*n+1) → ℂ)
    (SphereBundleTotal Q) (Space (2*n+1)) ∞)

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveException
