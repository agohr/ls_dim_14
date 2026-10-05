import QuaternionicSymmetry.LocalConnection
import QuaternionicSymmetry.ContinuousLinearConstraintDerivative

/-! A local connection that commutes with a constant endomorphism has
curvature commuting with that same endomorphism. -/
namespace QuaternionicSymmetry.LocalConnectionCommutantCurvature
open scoped Topology
noncomputable section
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

theorem curvature_commutes (Γ : LocalConnection.Form (E := E) (A := A))
    (T : A) (x u v : E) (hΓ : DifferentiableAt ℝ Γ x)
    (hcomm : ∀ᶠ y in 𝓝 x, ∀ w, Γ y w * T = T * Γ y w) :
    LocalConnection.curvature Γ x u v * T =
      T * LocalConnection.curvature Γ x u v := by
  let C : A →L[ℝ] A := (ContinuousLinearMap.mul ℝ A).flip T -
    ContinuousLinearMap.mul ℝ A T
  have hd (a b : E) : fderiv ℝ Γ x a b * T = T * fderiv ℝ Γ x a b := by
    let L := C.comp (ContinuousLinearMap.apply ℝ A b)
    have hz := ContinuousLinearConstraintDerivative.annihilates_fderiv L Γ x a hΓ (by
      filter_upwards [hcomm] with y hy
      exact sub_eq_zero.mpr (hy b))
    exact sub_eq_zero.mp hz
  have hu := hcomm.self_of_nhds u
  have hv := hcomm.self_of_nhds v
  have hp : (Γ x u * Γ x v - Γ x v * Γ x u) * T =
      T * (Γ x u * Γ x v - Γ x v * Γ x u) := by
    calc
      _ = Γ x u * (Γ x v * T) - Γ x v * (Γ x u * T) := by
        simp only [sub_mul, mul_assoc]
      _ = Γ x u * (T * Γ x v) - Γ x v * (T * Γ x u) := by rw [hu, hv]
      _ = (Γ x u * T) * Γ x v - (Γ x v * T) * Γ x u := by
        simp only [mul_assoc]
      _ = (T * Γ x u) * Γ x v - (T * Γ x v) * Γ x u := by rw [hu, hv]
      _ = _ := by simp only [mul_sub, mul_assoc]
  have hs : LocalConnection.curvature Γ x u v =
      (fderiv ℝ Γ x u v - fderiv ℝ Γ x v u) +
        (Γ x u * Γ x v - Γ x v * Γ x u) := by
    rw [LocalConnection.curvature_apply]
    abel
  rw [hs, add_mul, sub_mul, hd u v, hd v u, hp]
  simp only [mul_add, mul_sub]

end
end QuaternionicSymmetry.LocalConnectionCommutantCurvature
