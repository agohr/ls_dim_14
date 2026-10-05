import QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerImage
import QuaternionicSymmetry.QuaternionicUnitQuaternionPairTransport

/-! First source-free step toward `SO(4)` equals the quaternionic
normalizer: an arbitrary real orthogonal map fixing the scalar axis
induces a genuine unit-quaternion transport of its two imaginary axes.
The remaining orientation check on the third axis is separate. -/

namespace QuaternionicSymmetry.FourDimensionalSO4PairTransport

open scoped Quaternion
open QuaternionicUnitQuaternionTransport
  QuaternionicUnitQuaternionPairTransport

noncomputable section

theorem fixed_one_imaginary_axes
    (G : ℍ ≃ₗᵢ[ℝ] ℍ) (h1 : G 1 = 1) :
    (G basisI).re = 0 ∧ (G basisJ).re = 0 ∧
    Quaternion.normSq (G basisI) = 1 ∧
    Quaternion.normSq (G basisJ) = 1 ∧
    G basisI * G basisJ = -G basisJ * G basisI := by
  let u := G basisI
  let v := G basisJ
  have hu : u.re = 0 := by
    have h := G.inner_map_map basisI 1
    rw [h1] at h
    simpa [u, Quaternion.inner_def, basisI] using h
  have hv : v.re = 0 := by
    have h := G.inner_map_map basisJ 1
    rw [h1] at h
    simpa [v, Quaternion.inner_def, basisJ] using h
  have hnormI : ‖u‖ = 1 := by
    rw [show ‖u‖ = ‖basisI‖ from G.norm_map basisI]
    have h := Quaternion.normSq_eq_norm_mul_self basisI
    rw [basisI_unit.2] at h
    nlinarith [norm_nonneg basisI]
  have hnormJ : ‖v‖ = 1 := by
    rw [show ‖v‖ = ‖basisJ‖ from G.norm_map basisJ]
    have h := Quaternion.normSq_eq_norm_mul_self basisJ
    rw [basisJ_unit.2] at h
    nlinarith [norm_nonneg basisJ]
  have hnu : Quaternion.normSq u = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hnormI]
    norm_num
  have hnv : Quaternion.normSq v = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hnormJ]
    norm_num
  have horth : inner ℝ u v = 0 := by
    rw [show inner ℝ u v = inner ℝ basisI basisJ from G.inner_map_map _ _]
    simp [Quaternion.inner_def, basisI, basisJ]
  have hdot : u.imI * v.imI + u.imJ * v.imJ + u.imK * v.imK = 0 := by
    simp only [Quaternion.inner_def, Quaternion.re_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star, hu, hv] at horth
    linarith
  have hanti : u * v = -v * u := by
    ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_neg,
      Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
      hu, hv, zero_mul, mul_zero, zero_add, add_zero, neg_zero]
      <;> nlinarith [hdot]
  exact ⟨hu,hv,hnu,hnv,hanti⟩

theorem exists_unit_pair_for_fixed_one
    (G : ℍ ≃ₗᵢ[ℝ] ℍ) (h1 : G 1 = 1) :
    ∃ q : unitary ℍ,
      (q : ℍ) * basisI = G basisI * q ∧
      (q : ℍ) * basisJ = G basisJ * q := by
  obtain ⟨hu,hv,hnu,hnv,hanti⟩ := fixed_one_imaginary_axes G h1
  exact exists_unitPairTransport (G basisI) (G basisJ)
    hu hv hnu hnv hanti

end
end QuaternionicSymmetry.FourDimensionalSO4PairTransport
