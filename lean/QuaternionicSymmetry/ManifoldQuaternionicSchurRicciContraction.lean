import QuaternionicSymmetry.ManifoldQuaternionicSchurTensor
import QuaternionicSymmetry.ManifoldQuaternionicCoordinateEinstein
import QuaternionicSymmetry.LocalConnectionRicciCovariant
import QuaternionicSymmetry.ContinuousLinearMapTraceBasis

/-! The five-index Schur contraction is the covariant derivative of the
genuine Ricci trace in the actual adapted chart frame. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicSchurRicciContraction
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateMetricField
open ManifoldQuaternionicSchurTensor
open ManifoldQuaternionicCovariantRiemannSymmetry
open QuaternionicSymmetry.LocalConnectionRicciCovariant
open QuaternionicSymmetry.LocalConnectionRicciTraceDerivative
open QuaternionicSymmetry.ContinuousLinearMapTraceBasis
open QuaternionicSymmetry.ContinuousLinearMapTraceDerivative
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
theorem schurTensor_ricciTrace (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a v w : Fin (Module.finrank ℝ E)) :
    (∑ i, schurTensor Q D p y hy a i v w i) =
      realTraceCLM
        (covariantRicciOperator (coordinateConnection Q D p) y
          (coordinateOrthonormalBasis Q p y hy a)
          (coordinateOrthonormalBasis Q p y hy v)
          (coordinateOrthonormalBasis Q p y hy w)) := by
  let Γ := coordinateConnection Q D p
  let e := solderEquiv Q p y hy
  have hΓ := ManifoldQuaternionicCoordinateSecondBianchi.coordinateConnection_contDiffAt
    Q D p y hy
  rw [trace_in_frame e]
  apply Finset.sum_congr rfl
  intro i _
  rw [schurTensor, covariantRiemann,
    coordinateMetricField_apply Q p y hy,
    ManifoldQuaternionicCoordinateMetricity.coordinateMetric]
  simp only [coordinateOrthonormalBasis, e]
  rw [covariantRicciOperator_apply (coordinateConnection Q D p) y
    ((solderEquiv Q p y hy).symm (stdOrthonormalBasis ℝ E a))
    ((solderEquiv Q p y hy).symm (stdOrthonormalBasis ℝ E i))
    ((solderEquiv Q p y hy).symm (stdOrthonormalBasis ℝ E v))
    ((solderEquiv Q p y hy).symm (stdOrthonormalBasis ℝ E w)) hΓ]
  rw [solder_eq_toFrame Q p y hy]
  simp_rw [← solderEquiv_apply Q p y hy]
  simp only [ContinuousLinearEquiv.apply_symm_apply]

end
end QuaternionicSymmetry.ManifoldQuaternionicSchurRicciContraction
