import QuaternionicSymmetry.ComplexTorusLaurentCoassociative
import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularQuotientFamily

/-! The two inclusions of the Laurent coordinate ring into the literal
two-parameter ring, and the corresponding two-parameter extension of the
actual cone ideal. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleBaseChange

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalFamilyIdealDescent
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r d : ℕ}

def firstWeight : (Fin r → ℤ) →+ ((Fin r → ℤ) × (Fin r → ℤ)) where
  toFun μ := (μ, 0)
  map_zero' := rfl
  map_add' _ _ := rfl

def secondWeight : (Fin r → ℤ) →+ ((Fin r → ℤ) × (Fin r → ℤ)) where
  toFun μ := (0, μ)
  map_zero' := rfl
  map_add' _ _ := rfl

def firstParameter : TorusCoordinateRing r →+* DoubleTorusCoordinateRing r :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (firstWeight (r := r))

def secondParameter : TorusCoordinateRing r →+* DoubleTorusCoordinateRing r :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (secondWeight (r := r))

@[simp] theorem firstParameter_monomial (μ : Fin r → ℤ) :
    firstParameter (laurentMonomial μ) =
      AddMonoidAlgebra.single (μ, 0) 1 := by
  simp [firstParameter, firstWeight, laurentMonomial]

@[simp] theorem secondParameter_monomial (μ : Fin r → ℤ) :
    secondParameter (laurentMonomial μ) =
      AddMonoidAlgebra.single (0, μ) 1 := by
  simp [secondParameter, secondWeight, laurentMonomial]

def doubleBaseChange : MvPolynomial (Fin (d + 1)) ℂ →+*
    MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r) :=
  MvPolynomial.map (algebraMap ℂ (DoubleTorusCoordinateRing r))

def doubleExtendedConeIdeal (A : Set (Space d)) :
    Ideal (MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r)) :=
  Ideal.map (doubleBaseChange (r := r)) (vanishingIdeal A)

theorem firstParameter_comp_algebraMap :
    (firstParameter (r := r)).comp (algebraMap ℂ (TorusCoordinateRing r)) =
      algebraMap ℂ (DoubleTorusCoordinateRing r) := by
  ext c
  simp [firstParameter]

theorem secondParameter_comp_algebraMap :
    (secondParameter (r := r)).comp (algebraMap ℂ (TorusCoordinateRing r)) =
      algebraMap ℂ (DoubleTorusCoordinateRing r) := by
  ext c
  simp [secondParameter]

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleBaseChange
