import QuaternionicSymmetry.FourDimensionalHalfSpinHopfUnitFiber

/-! Injectivity of the genuine projective Hopf map: equal normalized
quaternionic axes force two nonzero complex spinors to differ by a complex
scalar, using the proved complex stabilizer rather than an assumed CP¹=S². -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfInjective

open scoped Quaternion
open FourDimensionalHalfSpinMatrix FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfUnitFiber
  FourDimensionalHalfSpinHopfScalar
open QuaternionicUnitQuaternionTransport

noncomputable section

private theorem fromSpinor_eq_norm_smul_unit (v : Spinor) (hv : v ≠ 0) :
    fromSpinor v = ‖fromSpinor v‖ • (spinorUnit v hv : ℍ) := by
  rw [spinorUnit, normalize_coe]
  have hn : ‖fromSpinor v‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro hz
    apply hv
    apply fromSpinor_injective
    simpa [fromSpinor] using hz
  simp [smul_smul, hn]

theorem projectiveHopf_injective : Function.Injective projectiveHopf := by
  intro p s h
  induction p using Projectivization.ind with
  | h v hv =>
    induction s using Projectivization.ind with
    | h w hw =>
      rw [projectiveHopf_mk, projectiveHopf_mk] at h
      have hh : hopfQuaternion v hv = hopfQuaternion w hw := by
        have hp := congrArg
          (fun a : ManifoldTwistorSphereBundle.coefficientSphere =>
            QuaternionicUnitScalarIsometries.pureScalar a.1) h
        simpa only [pureScalar_hopfSphere] using hp
      let q := spinorUnit v hv
      let r := spinorUnit w hw
      let c : ℂ := first (star (r : ℍ) * (q : ℍ))
      have hq : (q : ℍ) = (r : ℍ) * (c : ℍ) :=
        unit_eq_right_complex_mul_of_hopf_eq q r hh
      have hnw : ‖fromSpinor w‖ ≠ 0 := by
        apply norm_ne_zero_iff.mpr
        intro hz
        apply hw
        apply fromSpinor_injective
        simpa [fromSpinor] using hz
      let d : ℂ := ((‖fromSpinor v‖ / ‖fromSpinor w‖ : ℝ) : ℂ) * c
      have hdquat : (d : ℍ) =
          (‖fromSpinor v‖ / ‖fromSpinor w‖) • (c : ℍ) := by
        dsimp only [d]
        rw [Quaternion.coeComplex_mul, Quaternion.coeComplex_coe]
        rw [Algebra.smul_def]
        rfl
      have hspin : v = d • w := by
        apply fromSpinor_injective
        rw [fromSpinor_smul, hdquat]
        calc
          fromSpinor v = ‖fromSpinor v‖ • (q : ℍ) :=
            fromSpinor_eq_norm_smul_unit v hv
          _ = ‖fromSpinor v‖ • ((r : ℍ) * (c : ℍ)) := by rw [hq]
          _ = (‖fromSpinor w‖ • (r : ℍ)) *
                ((‖fromSpinor v‖ / ‖fromSpinor w‖) • (c : ℍ)) := by
              have hs : ‖fromSpinor w‖ *
                  (‖fromSpinor v‖ / ‖fromSpinor w‖) =
                  ‖fromSpinor v‖ := by field_simp [hnw]
              rw [smul_mul_assoc, mul_smul_comm, smul_smul, hs]
          _ = fromSpinor w *
                ((‖fromSpinor v‖ / ‖fromSpinor w‖) • (c : ℍ)) := by
              rw [← fromSpinor_eq_norm_smul_unit w hw]
      apply (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).2
      exact ⟨d,hspin.symm⟩

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfInjective
