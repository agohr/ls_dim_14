import QuaternionicSymmetry.QuaternionicWeylExteriorTrace
import QuaternionicSymmetry.QuaternionicMatrixTwoFormTrace
import QuaternionicSymmetry.QuaternionicBilinearOperator

/-! Source matrices on the quaternionic tangent block itself, of rank n.
The standard rank n+1 has a separate zero line; these coefficients are the
rank required by the printed dimension-eleven/twelve density formulas. -/
namespace QuaternionicSymmetry.QuaternionicWeylMatrixCoefficients
open Module QuaternionicCurvatureFiniteExpansion QuaternionicOperatorMatrixLinear
open QuaternionicOperatorMatrix QuaternionicBilinearOperator
open QuaternionicCurvatureOrbitalSign QuaternionicWeylExteriorTrace
open ComplexExteriorTraceBridge ExteriorContinuousPairing QuaternionicMatrixModel
noncomputable section
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] (S : QuaternionicStructure E)
local instance : NormedSpace ℝ E := inferInstance

def centralizerMap : operatorSpace S →ₗ[ℝ] S.skewCentralizer :=
  ((ContinuousLinearMap.coeLM ℝ).comp (operatorSpace S).subtype).codRestrict _
    (fun A => A.property)

def tangentSourceMatrixMap : operatorSpace S →ₗ[ℝ]
    hermitianAntiSelfDualSubmodule S.quaternionicDimension :=
  (1 / (2 * Real.pi) : ℝ) • ((hermitianMatrixMap S).comp (centralizerMap S))

variable (W : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
  (hW : ∀ u v, (W u v).toLinearMap ∈ S.skewCentralizer)

theorem tangentSourceMatrix_expansion (u v : E) :
    ∑ a : Index S, coefficient S W hW a u v • tangentSourceMatrixMap S (operatorBasis S a) =
      tangentSourceMatrixMap S ⟨W u v, hW u v⟩ := by
  have h := congrArg (tangentSourceMatrixMap S) ((operatorBasis S).sum_repr ⟨W u v, hW u v⟩)
  simpa only [map_sum, map_smul, coefficient_apply] using h

def tangentTraceRepresentative (b : Basis ι ℝ E) (j : ℕ) :
    Power E (LocalChernWeilTracePowers.powerDegree (2 * j - 1)) :=
  signedExteriorTrace (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
    (coefficientTwo S W hW b) j

theorem tangentTraceRepresentative_val (b : Basis ι ℝ E) (j : ℕ) (hj : 0 < j) :
    (tangentTraceRepresentative S W hW b j).val =
      (MatrixTracePolynomial.signedTracePower
        (MatrixTracePolynomial.complexifiedMatrix
          (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
          (coefficientExterior S W hW b)) j).val :=
  signedExteriorTrace_val _ _ j hj

end
end QuaternionicSymmetry.QuaternionicWeylMatrixCoefficients
