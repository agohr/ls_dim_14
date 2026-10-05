import QuaternionicSymmetry.FourDimensionalHalfSpinHopfInfinitesimal
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalization

/-! Algebraic one-parameter expansion of the normalized quaternionic Hopf
direction under an infinitesimal pure-imaginary left-spinor rotation. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalizedPath

open scoped Quaternion
open FourDimensionalHalfSpinHopfInfinitesimal
  QuaternionicUnitScalarIsometries

noncomputable section

def normalizedQuaternionHopf (q : ℍ) : ℍ :=
  (Quaternion.normSq q)⁻¹ • quaternionHopf q

theorem pureQuaternion_path_star (a : ℍ) (ha : a.re = 0)
    (t : ℝ) :
    star ((1 : ℍ) + t • a) = 1 - t • a := by
  simp [star_add, Quaternion.star_smul, Quaternion.star_eq_neg.mpr ha]
  abel

theorem pureQuaternion_path_normSq (a : ℍ) (ha : a.re = 0)
    (t : ℝ) :
    Quaternion.normSq ((1 : ℍ) + t • a) =
      1 + t^2 * Quaternion.normSq a := by
  simp [Quaternion.normSq_def', Quaternion.normSq_def', Quaternion.add_re,
    Quaternion.add_imI, Quaternion.add_imJ, Quaternion.add_imK,
    Quaternion.smul_re, Quaternion.smul_imI, Quaternion.smul_imJ,
    Quaternion.smul_imK, ha, pow_two]
  ring

theorem normalizedQuaternionHopf_path (a q : ℍ) (ha : a.re = 0)
    (t : ℝ) :
    normalizedQuaternionHopf (((1 : ℍ) + t • a) * q) =
      (Quaternion.normSq ((1 : ℍ) + t • a))⁻¹ •
        (((1 : ℍ) + t • a) * normalizedQuaternionHopf q *
          ((1 : ℍ) - t • a)) := by
  unfold normalizedQuaternionHopf quaternionHopf
  rw [map_mul, star_mul, pureQuaternion_path_star a ha]
  simp only [mul_inv_rev, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm (Quaternion.normSq q)⁻¹
    (Quaternion.normSq ((1 : ℍ) + t • a))⁻¹]
  noncomm_ring

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalizedPath
