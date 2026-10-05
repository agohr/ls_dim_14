import QuaternionicSymmetry.ComplexProjectiveDiagonalChartIdealDescent
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-! The Laurent-coefficient chart polynomial ring is the literal tensor
product of the torus coordinate ring with the ordinary chart polynomial
ring; the chart ideal extension is the image of the right-factor ideal.
This is the algebraic product identification before passing to quotients. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartTensorBaseChange

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def chartTensorEquiv :
    ((TorusCoordinateRing r) ⊗[ℂ] (MvPolynomial (Fin d) ℂ)) ≃ₐ[TorusCoordinateRing r]
      MvPolynomial (Fin d) (TorusCoordinateRing r) :=
  MvPolynomial.algebraTensorAlgEquiv ℂ (TorusCoordinateRing r)

theorem chartTensorEquiv_comp_includeRight :
    (chartTensorEquiv (r := r) (d := d)).toRingHom.comp
        (Algebra.TensorProduct.includeRight.toRingHom) =
      chartBaseChange (r := r) (d := d) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [chartTensorEquiv, chartBaseChange,
      MvPolynomial.algebraTensorAlgEquiv_tmul]
  · intro i
    simp [chartTensorEquiv, chartBaseChange,
      MvPolynomial.algebraTensorAlgEquiv_tmul]

theorem chartTensorEquiv_map_extendedIdeal
    (A : Set (Space d)) (i : Fin (d + 1)) :
    (Ideal.map Algebra.TensorProduct.includeRight.toRingHom
        (chartVanishingIdeal A i)).map
          (chartTensorEquiv (r := r) (d := d)).toRingHom =
      extendedChartIdeal (r := r) A i := by
  rw [Ideal.map_map]
  exact congrArg (fun f => Ideal.map f (chartVanishingIdeal A i))
    chartTensorEquiv_comp_includeRight

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartTensorBaseChange
