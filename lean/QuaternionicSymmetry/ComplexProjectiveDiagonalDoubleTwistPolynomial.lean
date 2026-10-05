import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleQuotientMaps
import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamily

/-! Two successive regular diagonal substitutions in literal two-parameter
Laurent coordinates. Their equality with the direct character product is
proved on the polynomial algebra before quotient descent. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleTwistPolynomial

open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalRegularFamily
open ComplexProjectiveDiagonalFamilyIdealDescent
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveDiagonalDoubleBaseChangeMaps
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r d : ℕ}

def firstTwist (μ : Fin (d + 1) → Fin r → ℤ) :
    MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) →+*
      MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (secondParameter (r := r)))
    (fun i => MvPolynomial.C
      (AddMonoidAlgebra.single (μ i, 0) 1) * MvPolynomial.X i)

def secondTwist (μ : Fin (d + 1) → Fin r → ℤ) :
    MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) →+*
      MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (firstParameter (r := r)))
    (fun i => MvPolynomial.C
      (AddMonoidAlgebra.single (0, μ i) 1) * MvPolynomial.X i)

theorem firstTwist_comp_baseChange
    (μ : Fin (d + 1) → Fin r → ℤ) :
    (firstTwist μ).comp (baseChange (r := r)) =
      (firstPolynomial (r := r)).comp (familySubstitution μ) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [firstTwist, baseChange, firstPolynomial,
      familySubstitution, secondParameter_comp_algebraMap]
    calc
      secondParameter (algebraMap ℂ (TorusCoordinateRing r) c) =
          algebraMap ℂ (DoubleTorusCoordinateRing r) c :=
        congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
          secondParameter_comp_algebraMap
      _ = firstParameter (algebraMap ℂ (TorusCoordinateRing r) c) :=
        (congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
          firstParameter_comp_algebraMap).symm
  · intro i
    simp [firstTwist, baseChange, firstPolynomial,
      familySubstitution, firstParameter_monomial]

theorem secondTwist_comp_baseChange
    (μ : Fin (d + 1) → Fin r → ℤ) :
    (secondTwist μ).comp (baseChange (r := r)) =
      (secondPolynomial (r := r)).comp (familySubstitution μ) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [secondTwist, baseChange, secondPolynomial,
      familySubstitution, firstParameter_comp_algebraMap]
    calc
      firstParameter (algebraMap ℂ (TorusCoordinateRing r) c) =
          algebraMap ℂ (DoubleTorusCoordinateRing r) c :=
        congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
          firstParameter_comp_algebraMap
      _ = secondParameter (algebraMap ℂ (TorusCoordinateRing r) c) :=
        (congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
          secondParameter_comp_algebraMap).symm
  · intro i
    simp [secondTwist, baseChange, secondPolynomial,
      familySubstitution, secondParameter_monomial]

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleTwistPolynomial
