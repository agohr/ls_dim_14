import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularQuotientFamily
import Mathlib.AlgebraicGeometry.Scheme

/-! The descended Laurent-family coordinate map induces a genuine morphism
of affine schemes. The source is the affine spectrum of the Laurent base
change of the cone coordinate ring. Projectivization and compatibility
with the analytic twistor are separate obligations. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalAffineSchemeFamily

open AlgebraicGeometry ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalFamilyIdealDescent
open ComplexProjectiveDiagonalRegularQuotientFamily
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def coneSchemeFamilyMap
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    Spec (CommRingCat.of
      (MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) ⧸
        extendedConeIdeal (r := r) A)) ⟶
    Spec (CommRingCat.of
      (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A)) :=
  Spec.map (CommRingCat.ofHom (quotientFamilyHom μ A hA hCompact))

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalAffineSchemeFamily
