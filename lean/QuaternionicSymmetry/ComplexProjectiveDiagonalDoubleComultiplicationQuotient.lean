import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleQuotientCoaction

/-! The two-parameter quotient coaction equals Laurent coordinate-ring
comultiplication followed by the one-parameter regular family. This is
the strict algebraic multiplication law for the affine-cone family. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleComultiplicationQuotient

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
open ComplexProjectiveDiagonalDoubleQuotientCoaction
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def comultiplicationPolynomial :
    MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) →+*
      MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r) :=
  MvPolynomial.map (comultiplication (r := r))

theorem comultiplication_comp_algebraMap :
    (comultiplication (r := r)).comp (algebraMap ℂ (TorusCoordinateRing r)) =
      algebraMap ℂ (DoubleTorusCoordinateRing r) := by
  ext c
  simp [comultiplication]

theorem comultiplicationPolynomial_comp_baseChange :
    (comultiplicationPolynomial (r := r) (d := d)).comp
        (baseChange (r := r)) = doubleBaseChange (r := r) (d := d) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [comultiplicationPolynomial, baseChange, doubleBaseChange]
    exact congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
      comultiplication_comp_algebraMap
  · intro i
    simp [comultiplicationPolynomial, baseChange, doubleBaseChange]

theorem comultiplicationPolynomial_map_extendedConeIdeal
    (A : Set (Space d)) :
    (extendedConeIdeal (r := r) A).map comultiplicationPolynomial =
      doubleExtendedConeIdeal (r := r) A := by
  simp only [extendedConeIdeal, doubleExtendedConeIdeal,
    Ideal.map_map, ← comultiplicationPolynomial_comp_baseChange]

def comultiplicationQuotient (A : Set (Space d)) :
    (MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) ⧸
      extendedConeIdeal (r := r) A) →+*
    (MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r) ⧸
      doubleExtendedConeIdeal (r := r) A) :=
  Ideal.quotientMap (doubleExtendedConeIdeal (r := r) A)
    comultiplicationPolynomial
    (Ideal.map_le_iff_le_comap.mp
      (le_of_eq (comultiplicationPolynomial_map_extendedConeIdeal A)))

theorem comultiplication_comp_family_eq_firstTwist_comp_family
    (μ : Fin (d + 1) → Fin r → ℤ) :
    (comultiplicationPolynomial (r := r)).comp (familySubstitution μ) =
      (firstTwist μ).comp (familySubstitution μ) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [comultiplicationPolynomial, familySubstitution,
      firstTwist, comultiplication, secondParameter]
  · intro i
    simp [comultiplicationPolynomial, familySubstitution,
      firstTwist, comultiplication_laurentMonomial,
      secondParameter_monomial, ← mul_assoc]
    simp [← map_mul, AddMonoidAlgebra.single_mul_single]

theorem quotientFamily_comultiplication_coherence
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    (comultiplicationQuotient A).comp
        (quotientFamilyHom μ A hA hCompact) =
      (firstTwistQuotient μ A hA hCompact).comp
        (quotientFamilyHom μ A hA hCompact) := by
  apply RingHom.ext
  intro q
  induction q using Quotient.inductionOn' with
  | _ p =>
    change Ideal.Quotient.mk (doubleExtendedConeIdeal (r := r) A)
        (comultiplicationPolynomial (familySubstitution μ p)) =
      Ideal.Quotient.mk (doubleExtendedConeIdeal (r := r) A)
        (firstTwist μ (familySubstitution μ p))
    exact congrArg (Ideal.Quotient.mk (doubleExtendedConeIdeal (r := r) A))
      (congrFun (congrArg (fun f : _ →+* _ => f.toFun)
        (comultiplication_comp_family_eq_firstTwist_comp_family μ)) p)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleComultiplicationQuotient
