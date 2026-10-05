import QuaternionicSymmetry.FourDimensionalHalfSpinHopfNorthVerticalSign

/-! A checked local convention calculation for the antipodal Hopf map.
Antipodal composition changes the north-affine Hopf differential from
anti-complex to complex-linear for the sphere's cross-product vertical
tensor at the antipodal point. This is local vertical evidence only;
the horizontal AHS tensor is not identified here. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinAntipodalVerticalSign

open scoped Quaternion
open FourDimensionalHalfSpinHopfNorthDerivative
  FourDimensionalTwistorHomogeneousFiber
  ManifoldTwistorVerticalComplex
  FourDimensionalHalfSpinHopfNorthVerticalSign
  ManifoldTwistorSphereBundle

noncomputable section

def antipodalCoefficient (a : coefficientSphere) : coefficientSphere :=
  ⟨-a.1, by simpa [squareNorm] using a.2⟩

def south : coefficientSphere := antipodalCoefficient north

def southDifferential : ℂ →L[ℝ] (Fin 3 → ℝ) := -northDifferential

theorem southCoordinates_hasFDerivAt_zero :
    HasFDerivAt (fun z : ℂ => -northCoordinates z) southDifferential 0 := by
  simpa only [southDifferential] using northCoordinates_hasFDerivAt_zero.neg

theorem southCoordinates_eq_antipodal_actualHopf (z : ℂ) :
    -northCoordinates z =
      -(FourDimensionalHalfSpinHopfSphere.hopfSphere
        (FourDimensionalHalfSpinHopfChartFormula.affineZeroSpinor z)
        (FourDimensionalHalfSpinHopfChartFormula.affineZero_nonzero z)).1 := by
  rw [northCoordinates_eq_actualHopf]

def southTangent (w : ℂ) : verticalSubmodule south :=
  ⟨southDifferential w, by
    simp [verticalSubmodule, VerticalVector, south, antipodalCoefficient,
      north, southDifferential, northDifferential, dotProduct,
      Pi.basisFun_apply, Fin.sum_univ_succ]⟩

theorem southTangent_complex (w : ℂ) :
    southTangent (Complex.I * w) =
      verticalComplex south (southTangent w) := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [southTangent, southDifferential, south, antipodalCoefficient,
      north, northDifferential, verticalComplex, crossProduct, Pi.basisFun_apply,
      Complex.mul_re, Complex.mul_im]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinAntipodalVerticalSign
