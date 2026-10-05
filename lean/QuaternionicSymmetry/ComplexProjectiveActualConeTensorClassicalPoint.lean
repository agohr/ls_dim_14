import QuaternionicSymmetry.ComplexProjectiveActualConeSpecEvaluationNaturality
import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedClassicalFunctions
import Mathlib.RingTheory.TensorProduct.Maps

/-! A complex-torus parameter and a classical projective chart point give a
literal complex evaluation point of the affine product tensor ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeTensorClassicalPoint

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveActualConeChartClassicalSpecialization
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def evalTorusAlgHom (z : ComplexTorus r) :
    TorusCoordinateRing r →ₐ[ℂ] ℂ where
  toRingHom := evalTorus z
  commutes' c := by simp [evalTorus]

def chartPointEvalAlgHom (A : Set (Space d)) (i : Fin (d + 1))
    (w : Fin d → ℂ) (hw : w ∈ chartLocus A i) :
    (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) →ₐ[ℂ] ℂ where
  toRingHom := chartPointEval A i w hw
  commutes' c :=
    ComplexProjectiveActualConeClassicalCarrierEvaluation.chartPointEval_scalar A i w hw c

def tensorClassicalEval (A : Set (Space d)) (i : Fin (d + 1))
    (z : ComplexTorus r) (w : Fin d → ℂ)
    (hw : w ∈ chartLocus A i) :
    ((TorusCoordinateRing r) ⊗[ℂ]
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)) →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.lift (evalTorusAlgHom z)
    (chartPointEvalAlgHom A i w hw) (fun _ _ => mul_comm _ _)

@[simp] theorem tensorClassicalEval_tmul (A : Set (Space d))
    (i : Fin (d + 1)) (z : ComplexTorus r)
    (w : Fin d → ℂ) (hw : w ∈ chartLocus A i)
    (t : TorusCoordinateRing r)
    (a : MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) :
    tensorClassicalEval A i z w hw (t ⊗ₜ[ℂ] a) =
      evalTorus z t * chartPointEval A i w hw a := rfl

end
end QuaternionicSymmetry.ComplexProjectiveActualConeTensorClassicalPoint
