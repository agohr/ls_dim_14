import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleTwistCoherence

/-! Strict quotient-level two-parameter regular action law: successive
applications of the algebraic family in either parameter order agree as
ring homomorphisms into the literal double-Laurent base-change quotient.
This is not inferred solely from equality on complex points. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleQuotientCoaction

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalFamilyIdealDescent
open ComplexProjectiveDiagonalRegularFamily
open ComplexProjectiveDiagonalRegularQuotientFamily
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveDiagonalDoubleTwistPolynomial
open ComplexProjectiveDiagonalDoubleTwistIdeal
open ComplexProjectiveDiagonalDoubleTwistCoherence
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def firstTwistQuotient
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    (MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) ⧸
      extendedConeIdeal (r := r) A) →+*
    (MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r) ⧸
      doubleExtendedConeIdeal (r := r) A) :=
  Ideal.quotientMap (doubleExtendedConeIdeal (r := r) A)
    (firstTwist μ)
    (Ideal.map_le_iff_le_comap.mp
      (firstTwist_map_extendedConeIdeal_le μ A hA hCompact))

def secondTwistQuotient
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    (MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) ⧸
      extendedConeIdeal (r := r) A) →+*
    (MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r) ⧸
      doubleExtendedConeIdeal (r := r) A) :=
  Ideal.quotientMap (doubleExtendedConeIdeal (r := r) A)
    (secondTwist μ)
    (Ideal.map_le_iff_le_comap.mp
      (secondTwist_map_extendedConeIdeal_le μ A hA hCompact))

theorem quotientFamily_twoParameter_coherence
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    (firstTwistQuotient μ A hA hCompact).comp
        (quotientFamilyHom μ A hA hCompact) =
      (secondTwistQuotient μ A hA hCompact).comp
        (quotientFamilyHom μ A hA hCompact) := by
  apply RingHom.ext
  intro q
  induction q using Quotient.inductionOn' with
  | _ p =>
    change Ideal.Quotient.mk (doubleExtendedConeIdeal (r := r) A)
        (firstTwist μ (familySubstitution μ p)) =
      Ideal.Quotient.mk (doubleExtendedConeIdeal (r := r) A)
        (secondTwist μ (familySubstitution μ p))
    exact congrArg (Ideal.Quotient.mk (doubleExtendedConeIdeal (r := r) A))
      (congrFun
        (congrArg (fun f : MvPolynomial (Fin (d + 1)) ℂ →+*
          MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r) => f.toFun)
          (firstTwist_comp_family_eq_secondTwist_comp_family μ)) p)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleQuotientCoaction
