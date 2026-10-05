import QuaternionicSymmetry.FourDimensionalTwistorAntipodalTensor

/-! The actual compatible quaternionic connection's local splitting
commutes with coefficient antipodal differentiation. Together with the
split-tensor calculation, this is the local horizontal input to Hitchin's
anti-complex antipodal convention; it does not use a spin lift. -/

namespace QuaternionicSymmetry.FourDimensionalTwistorAntipodalConnection

open scoped Manifold ContDiff Quaternion Matrix
open FourDimensionalTwistorAntipodalTensor
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorHorizontalConnection
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereBundle
  ManifoldQuaternionicMetric
  ManifoldQuaternionicConnection
  ManifoldQuaternionicAdjointConnection

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem connectionVertical_antipodal (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) (u : E) :
    verticalAntipodal a (connectionVertical Q D p y hy a u) =
      connectionVertical Q D p y hy (antipodalCoefficient a) u := by
  apply Subtype.ext
  change -(inducedForm Q D p y u a.1) =
    inducedForm Q D p y u (-a.1)
  exact (inducedForm Q D p y u).map_neg a.1 |>.symm

theorem rawAntipodal_connectionSplit (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) (uv : E × verticalSubmodule a) :
    rawAntipodal a (connectionSplit Q D p y hy a uv) =
      connectionSplit Q D p y hy (antipodalCoefficient a)
        (rawAntipodal a uv) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change -(uv.2.1 + inducedForm Q D p y uv.1 a.1) =
      -uv.2.1 + inducedForm Q D p y uv.1 (-a.1)
    rw [(inducedForm Q D p y uv.1).map_neg]
    abel

end
end QuaternionicSymmetry.FourDimensionalTwistorAntipodalConnection
