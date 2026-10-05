import QuaternionicSymmetry.ComplexProjectiveDiagonalChartProductScheme
import QuaternionicSymmetry.ComplexProjectiveActualConeProjChartIso

/-! A genuine regular torus-product morphism into each coordinate basic open
of the literal actual cone Proj. Agreement on overlapping basic opens and
global gluing are still separate obligations. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProjLocalAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjChartIso
open ComplexProjectiveDiagonalChartSchemeFamily
open ComplexProjectiveDiagonalChartProductScheme
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def chartProductAction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ
          (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)))) ⟶
    Spec (CommRingCat.of
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)) :=
  (chartFamilyProductIso (r := r) A i).inv ≫
    chartSchemeFamilyMap μ A hA hCompact i

def chartProductActionToActualProj
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ
          (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)))) ⟶
    (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).toScheme := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact chartProductAction μ A hA hCompact i ≫
    (actualProjChartIso A hA hNonempty i).inv

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProjLocalAction
