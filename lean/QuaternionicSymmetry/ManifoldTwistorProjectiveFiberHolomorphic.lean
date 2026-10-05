import QuaternionicSymmetry.ManifoldTwistorSphereFiberComplex
import QuaternionicSymmetry.ManifoldTwistorHolomorphicMapCriterion

/-! Every genuine twistor fiber has an explicitly constructed holomorphic
CP¹ parametrization, using the antipodally corrected Hopf map and the
independently built sphere-bundle inclusion. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveFiberHolomorphic

open scoped Manifold ContDiff
open ManifoldTwistorSphereCore ManifoldTwistorSphereFiberInclusion
open ManifoldTwistorSphereFiberComplex ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorHolomorphicMapCriterion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem projectiveFiberInclusion_holomorphic {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (p : M) :
    letI := A.charts
    ContMDiff 𝓘(ℂ,Fin 1 → ℂ) 𝓘(ℂ,ComplexTwistorModel n) ∞
      (projectiveFiberInclusion Q p) :=
  contMDiff_complex_of_twistor_tensor Q D A (projectiveFiberInclusion Q p)
    (projectiveFiberInclusion_smooth Q p)
    (projectiveFiberInclusion_mfderiv_complex Q D p)

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveFiberHolomorphic
