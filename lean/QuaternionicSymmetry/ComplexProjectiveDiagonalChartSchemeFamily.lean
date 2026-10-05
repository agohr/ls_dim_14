import QuaternionicSymmetry.ComplexProjectiveDiagonalChartQuotientFamily
import Mathlib.AlgebraicGeometry.Scheme

/-! Each actual standard projective-chart cutout has a regular
Laurent-parameter affine-scheme family. The identification of these
`Spec` charts with the standard opens of a closed `Proj` scheme, plus
overlap gluing, remains separate. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartSchemeFamily

open AlgebraicGeometry
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartQuotientFamily
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def chartSchemeFamilyMap
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    Spec (CommRingCat.of
      (MvPolynomial (Fin d) (TorusCoordinateRing r) ⧸
        extendedChartIdeal (r := r) A i)) ⟶
    Spec (CommRingCat.of
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)) :=
  Spec.map (CommRingCat.ofHom
    (chartQuotientFamilyHom μ A hA hCompact i))

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartSchemeFamily
