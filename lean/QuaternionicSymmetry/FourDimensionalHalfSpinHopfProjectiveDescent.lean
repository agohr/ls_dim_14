import QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalization

/-! Descend the normalized Hopf direction through actual complex
projectivization, using its proved scalar-scaling law. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfProjectiveDescent

open scoped Quaternion
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfRaw
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfScalar
  FourDimensionalHalfSpinHopfNormalization
open ManifoldTwistorSphereBundle

noncomputable section

private theorem normSq_coeComplex (c : ℂ) :
    Quaternion.normSq (c : ℍ) = Complex.normSq c := by
  simp [Quaternion.normSq_def', Complex.normSq_apply, pow_two]

theorem spinor_normSq_smul (c : ℂ) (v : Spinor) :
    Quaternion.normSq (fromSpinor (c • v)) =
      Complex.normSq c * Quaternion.normSq (fromSpinor v) := by
  rw [fromSpinor_smul, map_mul, normSq_coeComplex]
  rw [mul_comm]

theorem hopfQuaternion_smul (c : ℂ) (hc : c ≠ 0)
    (v : Spinor) (hv : v ≠ 0) :
    hopfQuaternion (c • v) (smul_ne_zero hc hv) =
      hopfQuaternion v hv := by
  rw [hopfQuaternion_eq_ratio, hopfQuaternion_eq_ratio,
    hopfRaw_smul, spinor_normSq_smul]
  have hn : Complex.normSq c ≠ 0 := by
    exact (Complex.normSq_eq_zero).not.mpr hc
  simp [mul_inv_rev, smul_smul, hn]

theorem hopfSphere_smul (c : ℂ) (hc : c ≠ 0)
    (v : Spinor) (hv : v ≠ 0) :
    hopfSphere (c • v) (smul_ne_zero hc hv) = hopfSphere v hv := by
  apply Subtype.ext
  exact congrArg (fun p : ℍ => ![p.imI,p.imJ,p.imK])
    (hopfQuaternion_smul c hc v hv)

/-- The Hopf map on true complex projective lines, obtained from the
canonical representative only after proving scalar invariance. -/
def projectiveHopf (p : ProjectiveSpinor) : coefficientSphere :=
  hopfSphere p.rep p.rep_nonzero

theorem projectiveHopf_mk (v : Spinor) (hv : v ≠ 0) :
    projectiveHopf (Projectivization.mk ℂ v hv) = hopfSphere v hv := by
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  have hcn : (c : ℂ) ≠ 0 := Units.ne_zero c
  have hrep : (Projectivization.mk ℂ v hv).rep = (c : ℂ) • v := hc.symm
  change hopfSphere (Projectivization.mk ℂ v hv).rep _ = hopfSphere v hv
  simpa only [hrep] using hopfSphere_smul (c : ℂ) hcn v hv

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfProjectiveDescent
