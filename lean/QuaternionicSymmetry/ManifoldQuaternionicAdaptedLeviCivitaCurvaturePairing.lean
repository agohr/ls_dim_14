import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaCurvatureBridge
import QuaternionicSymmetry.GeneralLeviCivitaAdaptedMetricBridge

/-! The adapted orthonormal curvature pairing agrees exactly with the
ordinary coordinate Levi-Civita curvature pairing in the metric obtained
from that adapted frame. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaCurvaturePairing

open Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateMetricity
open ManifoldQuaternionicAdaptedLeviCivitaForm
open ManifoldQuaternionicAdaptedLeviCivitaCurvatureBridge
open GeneralLeviCivitaAdaptedMetricBridge
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
    (TangentSpace 𝓘(ℝ,E) : M → Type _))
  (D : CoordinateLeviCivitaConnection g)

theorem adaptedLeviCivita_curvature_inner_eq_chartMetric
    (hmetric : ∀ x (v w : TangentSpace 𝓘(ℝ,E) x),
      g.inner x v w = Q.tangentMetricForm x v w)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v w z : E) :
    inner ℝ
      (LocalConnection.curvature (adaptedLeviCivitaForm Q g D p) y u v w) z =
      chartMetric g p y
        (LocalConnection.curvature (D.form p) y u v
          (coordinateInverse Q p y w))
        (coordinateInverse Q p y z) := by
  rw [adaptedLeviCivita_curvature_eq_solder_coordinate Q g D p y hy u v w]
  rw [chartMetric_eq_coordinateMetric Q g hmetric p y hy]
  change inner ℝ
      (solder Q p y (LocalConnection.curvature (D.form p) y u v
        (coordinateInverse Q p y w))) z =
      inner ℝ
        (solder Q p y (LocalConnection.curvature (D.form p) y u v
          (coordinateInverse Q p y w)))
        (solder Q p y (coordinateInverse Q p y z))
  have hright := coordinateInverse_right Q p y hy
  have hz := congrArg (fun A : E →L[ℝ] E => A z) hright
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using
    congrArg (fun t : E => inner ℝ
      (solder Q p y (LocalConnection.curvature (D.form p) y u v
        (coordinateInverse Q p y w))) t) hz.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaCurvaturePairing
