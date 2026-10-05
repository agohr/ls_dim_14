import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartTwistIdeal

/-! Strict quotient-ring two-torus coaction identities for each actual
projective affine chart. These are ring-hom equalities, not pointwise tests. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartQuotientCoaction

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartQuotientFamily
open ComplexProjectiveDiagonalAffineChartComorphism
open ComplexProjectiveDiagonalDoubleChartBaseChange
open ComplexProjectiveDiagonalDoubleChartQuotientMaps
open ComplexProjectiveDiagonalDoubleChartTwistPolynomial
open ComplexProjectiveDiagonalDoubleChartTwistIdeal
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def firstChartTwistQuotient
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    (MvPolynomial (Fin d) (TorusCoordinateRing r) ⧸ extendedChartIdeal (r := r) A i) →+*
      (MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) ⧸
        doubleExtendedChartIdeal (r := r) A i) :=
  Ideal.quotientMap (doubleExtendedChartIdeal (r := r) A i)
    (firstChartTwist μ i)
    (Ideal.map_le_iff_le_comap.mp
      (firstChartTwist_map_extendedChartIdeal_le μ A hA hCompact i))

def secondChartTwistQuotient
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    (MvPolynomial (Fin d) (TorusCoordinateRing r) ⧸ extendedChartIdeal (r := r) A i) →+*
      (MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) ⧸
        doubleExtendedChartIdeal (r := r) A i) :=
  Ideal.quotientMap (doubleExtendedChartIdeal (r := r) A i)
    (secondChartTwist μ i)
    (Ideal.map_le_iff_le_comap.mp
      (secondChartTwist_map_extendedChartIdeal_le μ A hA hCompact i))

theorem chartFamily_comultiplication_first
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    (comultiplicationChartQuotient (r := r) A i).comp
        (chartQuotientFamilyHom μ A hA hCompact i) =
      (firstChartTwistQuotient μ A hA hCompact i).comp
        (chartQuotientFamilyHom μ A hA hCompact i) := by
  apply RingHom.ext
  intro q
  induction q using Quotient.inductionOn' with
  | _ p =>
    change Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
        (comultiplicationChartPolynomial
          (chartActionComorphism μ i p)) =
      Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
        (firstChartTwist μ i (chartActionComorphism μ i p))
    exact congrArg (Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i))
      (congrFun (congrArg (fun f : _ →+* _ => f.toFun)
        (comultiplication_comp_chartAction_eq_first μ i)) p)

theorem chartFamily_comultiplication_second
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    (comultiplicationChartQuotient (r := r) A i).comp
        (chartQuotientFamilyHom μ A hA hCompact i) =
      (secondChartTwistQuotient μ A hA hCompact i).comp
        (chartQuotientFamilyHom μ A hA hCompact i) := by
  apply RingHom.ext
  intro q
  induction q using Quotient.inductionOn' with
  | _ p =>
    change Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
        (comultiplicationChartPolynomial
          (chartActionComorphism μ i p)) =
      Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
        (secondChartTwist μ i (chartActionComorphism μ i p))
    exact congrArg (Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i))
      (congrFun (congrArg (fun f : _ →+* _ => f.toFun)
        (comultiplication_comp_chartAction_eq_second μ i)) p)

theorem chartFamily_twoParameter_coherence
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    (firstChartTwistQuotient μ A hA hCompact i).comp
        (chartQuotientFamilyHom μ A hA hCompact i) =
      (secondChartTwistQuotient μ A hA hCompact i).comp
        (chartQuotientFamilyHom μ A hA hCompact i) :=
  (chartFamily_comultiplication_first μ A hA hCompact i).symm.trans
    (chartFamily_comultiplication_second μ A hA hCompact i)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartQuotientCoaction
