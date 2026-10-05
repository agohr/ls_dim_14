import QuaternionicSymmetry.ComplexProjectiveDiagonalChartTensorBaseChange

/-! Algebra-equivalence form of the actual chart quotient base change:
the Laurent chart ring is the quotient of the literal torus-coordinate
tensor polynomial algebra by the image of the actual chart ideal. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartTensorQuotient

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartTensorBaseChange
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def tensorExtendedChartIdeal (A : Set (Space d)) (i : Fin (d + 1)) :
    Ideal ((TorusCoordinateRing r) ⊗[ℂ] (MvPolynomial (Fin d) ℂ)) :=
  Ideal.map Algebra.TensorProduct.includeRight.toRingHom
    (chartVanishingIdeal A i)

def chartTensorQuotientEquiv (A : Set (Space d)) (i : Fin (d + 1)) :
    (((TorusCoordinateRing r) ⊗[ℂ] (MvPolynomial (Fin d) ℂ)) ⧸
      tensorExtendedChartIdeal (r := r) A i) ≃ₐ[TorusCoordinateRing r]
    (MvPolynomial (Fin d) (TorusCoordinateRing r) ⧸
      extendedChartIdeal (r := r) A i) :=
  Ideal.quotientEquivAlg (tensorExtendedChartIdeal (r := r) A i)
    (extendedChartIdeal (r := r) A i)
    (chartTensorEquiv (r := r) (d := d))
    (chartTensorEquiv_map_extendedIdeal A i).symm

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartTensorQuotient
