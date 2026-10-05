import QuaternionicSymmetry.FourDimensionalHalfSpinHopfNorthSection

/-! The second quaternionic local section covers the south pole omitted by
the `i`-based section. Right multiplication by the fixed `j` unit changes
the starting Hopf axis from `i` to `-i`. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSouthSection

open scoped Quaternion
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfUnitSection
  FourDimensionalHalfSpinHopfLocalInverseRaw
  FourDimensionalHalfSpinHopfNorthSection
open QuaternionicUnitQuaternionTransport
  QuaternionicUnitQuaternionLocalSections
  QuaternionicUnitQuaternionSmoothTransport
  QuaternionicUnitScalarIsometries
open ManifoldTwistorSphereBundle
  ComplexProjectiveTopology

noncomputable section

private def jUnit : unitary ℍ := ofNormSqOne basisJ basisJ_unit.2

private theorem jUnit_intertwines : (jUnit : ℍ) * basisI = -basisI * jUnit := by
  change basisJ * basisI = -basisI * basisJ
  ext <;> norm_num [basisI, basisJ, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

def southSpinor (v : ℍ) : Spinor :=
  spinorQuaternionEquiv.symm (normalizedRaw (-basisI) v * basisJ)

def southProjective (v : ℍ) : ProjectiveSpinor :=
  projectivize 1 (southSpinor v)

theorem southSpinor_ne_zero (v : ℍ) (hv : v ≠ basisI) :
    southSpinor v ≠ 0 := by
  let q : unitary ℍ := localTransport (-basisI)
    (by rw [neg_mul_neg]; exact imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2)
    ⟨v, by simpa using hv⟩
  have hraw : normalizedRaw (-basisI) v = (q : ℍ) := rfl
  have hprod : normalizedRaw (-basisI) v * basisJ = ((q * jUnit : unitary ℍ) : ℍ) := by
    rw [hraw]
    rfl
  intro hz
  have hqz : ((q * jUnit : unitary ℍ) : ℍ) = 0 := by
    have h := congrArg (spinorQuaternionEquiv : Spinor →ₗ[ℝ] ℍ) hz
    simpa [southSpinor, hprod] using h
  have hn := normSq_one_of_unitary (q * jUnit)
  rw [hqz, map_zero] at hn
  norm_num at hn

theorem projectiveHopf_localSouth (a : coefficientSphere)
    (ha : pureScalar a.1 ≠ basisI) :
    projectiveHopf (southProjective (pureScalar a.1)) = a := by
  let q : unitary ℍ := localTransport (-basisI)
    (by rw [neg_mul_neg]; exact imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2)
    ⟨pureScalar a.1, by simpa using ha⟩
  have hq : (q : ℍ) * (-basisI) = pureScalar a.1 * q :=
    localTransport_intertwines (-basisI)
      (by rw [neg_mul_neg]; exact imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2)
      ⟨pureScalar a.1, by simpa using ha⟩ (pureScalar_sq a)
  have htotal : ((q * jUnit : unitary ℍ) : ℍ) * basisI =
      pureScalar a.1 * (q * jUnit : unitary ℍ) := by
    change ((q : ℍ) * (jUnit : ℍ)) * basisI =
      pureScalar a.1 * ((q : ℍ) * (jUnit : ℍ))
    rw [mul_assoc, jUnit_intertwines, ← mul_assoc, hq, mul_assoc]
  have hspin : southSpinor (pureScalar a.1) =
      spinorQuaternionEquiv.symm ((q * jUnit : unitary ℍ) : ℍ) := by
    rfl
  rw [southProjective, projectivize_of_ne_zero 1 _
    (southSpinor_ne_zero (pureScalar a.1) ha)]
  simpa only [hspin] using projectiveHopf_of_unitIntertwiner a (q * jUnit) htotal

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSouthSection
