import QuaternionicSymmetry.QuaternionicCurvatureMatrixExpansion
import QuaternionicSymmetry.OrbitalPointwisePolynomialSign

/-! Orbital positivity for the finite matrix/form realization constructed
from a pair-symmetric quaternion-linear curvature tensor. -/
namespace QuaternionicSymmetry.QuaternionicCurvatureOrbitalSign
open Module QuaternionicCurvatureFiniteExpansion QuaternionicCurvatureMatrixExpansion
open QuaternionicBilinearOperator QuaternionicProjectiveStandardHilbertStructure
open QuaternionicFundamental HyperholomorphicExterior
open MatrixTracePolynomial OrbitalMatrixPolynomialBridge
noncomputable section
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] (S : QuaternionicStructure E)
variable (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
  (hR : ∀ u v, (R u v).toLinearMap ∈ S.skewCentralizer)

def coefficientExterior (b : Basis ι ℝ E) (a : Index S) : QuaternionicFundamental.E E :=
  evenForm b (operator (coefficient S R hR a)).toLinearMap

theorem coefficient_twoForm_evaluate (b : Basis ι ℝ E)
    (hanti : ∀ u v, R u v = -R v u) (a : Index S) (u v : E) :
    BilinearExterior.evaluate u v
      (HyperholomorphicExterior.form b (operator (coefficient S R hR a)).toLinearMap) =
      coefficient S R hR a u v := by
  rw [evaluate_form b _ (operator_skew _ (coefficient_antisymm S R hR hanti a))]
  exact operator_inner _ u v

theorem sourceMatrix_twoForm_expansion (b : Basis ι ℝ E)
    (hanti : ∀ u v, R u v = -R v u) (u v : E) :
    ∑ a : Index S, BilinearExterior.evaluate u v
        (HyperholomorphicExterior.form b (operator (coefficient S R hR a)).toLinearMap) •
        sourceMatrixMap S (operatorBasis S a) = sourceMatrixMap S ⟨R u v, hR u v⟩ := by
  simp only [coefficient_twoForm_evaluate S R hR b hanti]
  exact sourceMatrix_expansion S R hR u v

theorem coefficientExterior_mem (b : Basis ι ℝ E)
    (hanti : ∀ u v, R u v = -R v u)
    (hpair : ∀ u v w z, inner ℝ (R u v w) z = inner ℝ (R w z u) v)
    (a : Index S) : coefficientExterior S R hR b a ∈ formSpace S b :=
  evenForm_mem S b _ (coefficient_operator_mem S R hR hanti hpair a)

theorem orbital_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (b : Basis ι ℝ E) (hanti : ∀ u v, R u v = -R v u)
    (hpair : ∀ u v w z, inner ℝ (R u v w) z = inner ℝ (R w z u) v)
    (k : ℕ) (hk : k ≤ 6) (hkS : k ≤ S.quaternionicDimension)
    (hn : 11 ≤ (standardStructure S).quaternionicDimension)
    (a : List ℕ) (ha : a.length ≤ (standardStructure S).quaternionicDimension) :
    PositiveRay.Contains (topForm S b)
      (MvPolynomial.aeval (fun i : Fin 6 => signedTracePower
        (complexifiedMatrix (fun j : Index S => (sourceMatrixMap S (operatorBasis S j)).val)
          (coefficientExterior S R hR b)) (i.val + 1))
        (FiniteTypeCSchurSix.orbital (standardStructure S).quaternionicDimension k a) *
        QuaternionicFundamental.form S b ^ (S.quaternionicDimension - k)) := by
  exact OrbitalPointwisePolynomialSign.orbital_mem_positiveRay hsource _ k hn hk a ha
    (fun j : Index S => (sourceMatrixMap S (operatorBasis S j)).val)
    (fun j => (sourceMatrixMap S (operatorBasis S j)).property)
    S b (coefficientExterior S R hR b)
    (coefficientExterior_mem S R hR b hanti hpair) hkS

end
end QuaternionicSymmetry.QuaternionicCurvatureOrbitalSign
