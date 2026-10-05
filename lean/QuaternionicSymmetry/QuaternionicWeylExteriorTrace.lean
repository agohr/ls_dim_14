import QuaternionicSymmetry.ComplexExteriorTraceBridge
import QuaternionicSymmetry.QuaternionicCurvatureOrbitalSign

/-! The homogeneous exterior representatives of the Weyl tensor's signed
source traces, built from its proved finite hyperholomorphic expansion. -/
namespace QuaternionicSymmetry.QuaternionicWeylExteriorTrace
open Module QuaternionicCurvatureFiniteExpansion QuaternionicCurvatureMatrixExpansion
open QuaternionicCurvatureOrbitalSign ComplexExteriorTraceBridge
open ExteriorContinuousPairing QuaternionicBilinearOperator
noncomputable section
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] (S : QuaternionicStructure E)
variable (W : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
  (hW : ∀ u v, (W u v).toLinearMap ∈ S.skewCentralizer) (b : Basis ι ℝ E)

def coefficientTwo (a : Index S) : Power E 2 :=
  HyperholomorphicExterior.form b (operator (coefficient S W hW a)).toLinearMap

def traceRepresentative (j : ℕ) : Power E (LocalChernWeilTracePowers.powerDegree (2 * j - 1)) :=
  signedExteriorTrace (fun a : Index S => (sourceMatrixMap S (operatorBasis S a)).val)
    (coefficientTwo S W hW b) j

theorem traceRepresentative_val (j : ℕ) (hj : 0 < j) :
    (traceRepresentative S W hW b j).val =
      (MatrixTracePolynomial.signedTracePower
        (MatrixTracePolynomial.complexifiedMatrix
          (fun a : Index S => (sourceMatrixMap S (operatorBasis S a)).val)
          (coefficientExterior S W hW b)) j).val :=
  signedExteriorTrace_val _ _ j hj

end
end QuaternionicSymmetry.QuaternionicWeylExteriorTrace
