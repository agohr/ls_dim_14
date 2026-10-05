import QuaternionicSymmetry.ComplexProjectiveActualConeProjChartIso
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartTensorQuotient
import Mathlib.RingTheory.TensorProduct.Maps

/-! Product-ring comparison for an actual projective chart and the
Laurent-coordinate torus. The affine family ring is the true tensor
product with the actual chart quotient. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartProductRing

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartTensorQuotient
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def chartTensorQuotientProductEquiv
    (A : Set (Space d)) (i : Fin (d + 1)) :
    (((TorusCoordinateRing r) ⊗[ℂ] (MvPolynomial (Fin d) ℂ)) ⧸
      tensorExtendedChartIdeal (r := r) A i) ≃+*
    ((TorusCoordinateRing r) ⊗[ℂ]
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)) := by
  let P := MvPolynomial (Fin d) ℂ
  let T := TorusCoordinateRing r
  let I := chartVanishingIdeal A i
  letI : Algebra P (T ⊗[ℂ] P) := Algebra.TensorProduct.rightAlgebra
  let e₁ : (((T ⊗[ℂ] P) ⧸ tensorExtendedChartIdeal (r := r) A i) ≃+*
      ((T ⊗[ℂ] P) ⊗[P] (P ⧸ I))) := by
    exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (T ⊗[ℂ] P) I).toRingEquiv
  let e₂ : ((T ⊗[ℂ] P) ⊗[P] (P ⧸ I)) ≃+*
      ((P ⧸ I) ⊗[P] (T ⊗[ℂ] P)) :=
    (Algebra.TensorProduct.comm P (T ⊗[ℂ] P) (P ⧸ I)).toRingEquiv
  let e₃ : ((P ⧸ I) ⊗[P] (T ⊗[ℂ] P)) ≃+*
      ((P ⧸ I) ⊗[P] (P ⊗[ℂ] T)) := by
    exact (Algebra.TensorProduct.congr (AlgEquiv.refl : (P ⧸ I) ≃ₐ[P ⧸ I] (P ⧸ I))
      (Algebra.TensorProduct.commRight ℂ P T).symm).toRingEquiv
  let e₄ : ((P ⧸ I) ⊗[P] (P ⊗[ℂ] T)) ≃+*
      ((P ⧸ I) ⊗[ℂ] T) :=
    (Algebra.TensorProduct.cancelBaseChange ℂ P (P ⧸ I) (P ⧸ I) T).toRingEquiv
  let e₅ : ((P ⧸ I) ⊗[ℂ] T) ≃+* (T ⊗[ℂ] (P ⧸ I)) :=
    (Algebra.TensorProduct.comm ℂ (P ⧸ I) T).toRingEquiv
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartProductRing
