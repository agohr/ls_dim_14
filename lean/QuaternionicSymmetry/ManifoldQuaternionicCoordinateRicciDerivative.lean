import QuaternionicSymmetry.ManifoldQuaternionicSchurRicciContraction

/-! Fréchet derivative of actual chart-coordinate Ricci, identified with the
continuous trace contraction of the actual curvature. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCoordinateRicciDerivative
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateEinstein
open ManifoldQuaternionicSchurTensor
open ManifoldQuaternionicSchurRicciContraction
open QuaternionicSymmetry.LocalConnectionRicciTraceDerivative
open QuaternionicSymmetry.LocalConnectionRicciCovariant
open QuaternionicSymmetry.ContinuousLinearMapTraceDerivative
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem coordinateRicci_eq_ricciTrace (p : M) (y v w : E) :
    coordinateRicci Q D p y v w =
      ricciTrace (coordinateConnection Q D p) y v w := by
  rw [coordinateRicci, ricciTrace, realTraceCLM_apply]
  congr 1

theorem coordinateRicci_fderiv (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a v w : E) :
    fderiv ℝ (fun z => coordinateRicci Q D p z v w) y a =
      realTraceCLM
        (ricciExtraction v w
          (fderiv ℝ (LocalConnection.curvature (coordinateConnection Q D p)) y a)) := by
  simp_rw [coordinateRicci_eq_ricciTrace Q D p]
  exact ricciTrace_fderiv (coordinateConnection Q D p) y a v w
    (ManifoldQuaternionicCoordinateSecondBianchi.coordinateConnection_contDiffAt
      Q D p y hy)

end
end QuaternionicSymmetry.ManifoldQuaternionicCoordinateRicciDerivative
