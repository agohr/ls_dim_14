import QuaternionicSymmetry.ComplexProjectiveDiagonalChartProductRing
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartSchemeFamily
import Mathlib.AlgebraicGeometry.Pullbacks

/-! The actual Laurent-parameter affine family chart is the genuine
scheme-theoretic torus × affine-chart product over `Spec ℂ`. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartProductScheme

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartTensorQuotient
open ComplexProjectiveDiagonalChartProductRing
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def chartFamilyProductRingEquiv (A : Set (Space d))
    (i : Fin (d + 1)) :
    (MvPolynomial (Fin d) (TorusCoordinateRing r) ⧸
      extendedChartIdeal (r := r) A i) ≃+*
    ((TorusCoordinateRing r) ⊗[ℂ]
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)) :=
  (chartTensorQuotientEquiv (r := r) A i).symm.toRingEquiv.trans
    (chartTensorQuotientProductEquiv (r := r) A i)

def chartFamilyProductIso (A : Set (Space d))
    (i : Fin (d + 1)) :
    Spec (CommRingCat.of
      (MvPolynomial (Fin d) (TorusCoordinateRing r) ⧸
        extendedChartIdeal (r := r) A i)) ≅
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ
          (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)))) :=
  (Scheme.Spec.mapIso (chartFamilyProductRingEquiv (r := r) A i).symm.toCommRingCatIso.op)
    ≪≫ (pullbackSpecIso ℂ (TorusCoordinateRing r)
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)).symm

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartProductScheme
