import QuaternionicSymmetry.ManifoldTwistorSphereBundle
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! The coefficient quadratic two-sphere is explicitly the unit sphere in
Euclidean three-space. The original coefficient type has the Pi sup norm,
so this conversion is needed before using Mathlib's sphere charts. -/

namespace QuaternionicSymmetry.ManifoldTwistorCoefficientSphere

open QuaternionicSymmetry.ManifoldTwistorSphereBundle

noncomputable section

abbrev EuclideanThree := EuclideanSpace ℝ (Fin 3)
abbrev geometricSphere := Metric.sphere (0 : EuclideanThree) 1

def toEuclidean (a : Fin 3 → ℝ) : EuclideanThree :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm a

theorem norm_sq_toEuclidean (a : Fin 3 → ℝ) :
    ‖toEuclidean a‖ ^ 2 = squareNorm a := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [toEuclidean, EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply,
    PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  simp [squareNorm, pow_two]

theorem mem_geometricSphere (a : Fin 3 → ℝ) :
    toEuclidean a ∈ Metric.sphere (0 : EuclideanThree) 1 ↔
      squareNorm a = 1 := by
  rw [mem_sphere_zero_iff_norm]
  constructor
  · intro h
    rw [← norm_sq_toEuclidean a, h]
    norm_num
  · intro h
    have hsq : ‖toEuclidean a‖ ^ 2 = 1 := by
      rw [norm_sq_toEuclidean, h]
    nlinarith [norm_nonneg (toEuclidean a)]

/-- Identification of the actual coefficient sphere with Mathlib's smooth
Euclidean unit two-sphere. -/
def coefficientSphereHomeomorph : coefficientSphere ≃ₜ geometricSphere where
  toFun a := ⟨toEuclidean a.1, (mem_geometricSphere a.1).2 a.2⟩
  invFun u := ⟨EuclideanSpace.equiv (Fin 3) ℝ u.1,
    (mem_geometricSphere _).1 (by simp [toEuclidean])⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    rfl
  continuous_toFun :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
      continuous_subtype_val |>.subtype_mk _
  continuous_invFun :=
    (EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp
      continuous_subtype_val |>.subtype_mk _

end
end QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
