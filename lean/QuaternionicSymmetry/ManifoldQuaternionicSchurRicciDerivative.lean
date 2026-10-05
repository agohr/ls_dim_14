import QuaternionicSymmetry.ManifoldQuaternionicCoordinateRicciDerivative

/-! The actual five-index Schur contraction equals the covariant derivative
of chart-coordinate Ricci. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicSchurRicciDerivative
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateEinstein
open ManifoldQuaternionicCoordinateRicciDerivative
open ManifoldQuaternionicSchurTensor
open ManifoldQuaternionicSchurRicciContraction
open QuaternionicSymmetry.LocalConnectionRicciCovariant
open QuaternionicSymmetry.LocalConnectionRicciTraceDerivative
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

omit [Nontrivial E] in
theorem schurTensor_covariantRicci (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a v w : Fin (Module.finrank ℝ E)) :
    (∑ i, schurTensor Q D p y hy a i v w i) =
      fderiv ℝ (fun z => coordinateRicci Q D p z
        (coordinateOrthonormalBasis Q p y hy v)
        (coordinateOrthonormalBasis Q p y hy w)) y
          (coordinateOrthonormalBasis Q p y hy a) -
      coordinateRicci Q D p y
        (coordinateConnection Q D p y
          (coordinateOrthonormalBasis Q p y hy a)
          (coordinateOrthonormalBasis Q p y hy v))
        (coordinateOrthonormalBasis Q p y hy w) -
      coordinateRicci Q D p y
        (coordinateOrthonormalBasis Q p y hy v)
        (coordinateConnection Q D p y
          (coordinateOrthonormalBasis Q p y hy a)
          (coordinateOrthonormalBasis Q p y hy w)) := by
  rw [schurTensor_ricciTrace Q D p y hy a v w]
  rw [covariantRicci_trace (coordinateConnection Q D p) y
    (coordinateOrthonormalBasis Q p y hy a)
    (coordinateOrthonormalBasis Q p y hy v)
    (coordinateOrthonormalBasis Q p y hy w)
    (ManifoldQuaternionicCoordinateSecondBianchi.coordinateConnection_contDiffAt
      Q D p y hy)]
  simp_rw [← coordinateRicci_eq_ricciTrace Q D p]

end
end QuaternionicSymmetry.ManifoldQuaternionicSchurRicciDerivative
