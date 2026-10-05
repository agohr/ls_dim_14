import QuaternionicSymmetry.FourDimensionalHalfSpinHopfProjectiveSmooth
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSurjective

/-! A unit quaternion that intertwines the selected `i` axis with an actual
sphere point supplies its projective-spinor preimage by the literal Hopf map.
This is the algebraic certificate needed for local smooth inverse sections. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfUnitSection

open scoped Quaternion
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfProjectiveDescent
open QuaternionicUnitQuaternionTransport
  QuaternionicUnitScalarIsometries
open ManifoldTwistorSphereBundle

noncomputable section

theorem projectiveHopf_of_unitIntertwiner (a : coefficientSphere)
    (q : unitary ℍ)
    (hq : (q : ℍ) * basisI = pureScalar a.1 * q) :
    projectiveHopf
      (Projectivization.mk ℂ
        (spinorQuaternionEquiv.symm (q : ℍ))
        (by
          intro hz
          have hqz : (q : ℍ) = 0 := by
            have he := congrArg
              (spinorQuaternionEquiv : Spinor →ₗ[ℝ] ℍ) hz
            simpa using he
          have hn := normSq_one_of_unitary q
          rw [hqz, map_zero] at hn
          norm_num at hn)) = a := by
  let v : Spinor := spinorQuaternionEquiv.symm (q : ℍ)
  have hv : v ≠ 0 := by
    intro hz
    have hqz : (q : ℍ) = 0 := by
      have he := congrArg (spinorQuaternionEquiv : Spinor →ₗ[ℝ] ℍ) hz
      simpa [v] using he
    have hn := normSq_one_of_unitary q
    rw [hqz, map_zero] at hn
    norm_num at hn
  have hfrom : fromSpinor v = (q : ℍ) :=
    spinorQuaternionEquiv.apply_symm_apply _
  have hunit : spinorUnit v hv = q := by
    apply Subtype.ext
    rw [spinorUnit, normalize_coe, hfrom]
    have hn : ‖(q : ℍ)‖ = 1 := by
      have hqnorm := normSq_one_of_unitary q
      rw [Quaternion.normSq_eq_norm_mul_self] at hqnorm
      nlinarith [norm_nonneg (q : ℍ)]
    simp
  have hhopf : hopfQuaternion v hv = pureScalar a.1 := by
    rw [hopfQuaternion, hunit]
    calc
      (q : ℍ) * basisI * star (q : ℍ) =
          pureScalar a.1 * ((q : ℍ) * star (q : ℍ)) := by
            rw [hq, mul_assoc]
      _ = pureScalar a.1 := by rw [q.property.2, mul_one]
  rw [projectiveHopf_mk]
  apply Subtype.ext
  have hp := pureScalar_hopfSphere v hv
  rw [hhopf] at hp
  have hvec := congrArg (fun p : ℍ => ![p.imI,p.imJ,p.imK]) hp
  funext i
  fin_cases i
  · simpa [pureScalar] using congrFun hvec 0
  · simpa [pureScalar] using congrFun hvec 1
  · simpa [pureScalar] using congrFun hvec 2

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfUnitSection
