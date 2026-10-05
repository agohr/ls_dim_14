import QuaternionicSymmetry.FourDimensionalHalfSpinHopfHorizontalVertical
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveLocalAHS

/-! The algebraic connection-graph naturality used below.  Both inputs
are independently verified differential identities: complex-linearity
on the vertical projective tangent and preservation of horizontal lifts. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfGraphAlgebra

open scoped Matrix Quaternion
open FourDimensionalHalfSpinProjectiveLocalAHS

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def sphereGraphComplex (J : ℍ →ₗ[ℝ] ℍ) (C : ℍ →ₗ[ℝ] V)
    (Iv : V →ₗ[ℝ] V) : (ℍ × V) →ₗ[ℝ] (ℍ × V) where
  toFun uv := (J uv.1, Iv (uv.2 + C uv.1) - C (J uv.1))
  map_add' u v := by
    apply Prod.ext
    · simp [map_add]
    · simp [map_add]; abel
  map_smul' r u := by
    apply Prod.ext
    · simp [map_smul]
    · simp [map_smul, smul_add, smul_sub]

theorem graphComplex_intertwining
    (J : ℍ →ₗ[ℝ] ℍ) (K : ℍ →ₗ[ℝ] ℂ)
    (H : ℂ →ₗ[ℝ] V) (C : ℍ →ₗ[ℝ] V)
    (Iv : V →ₗ[ℝ] V)
    (hvertical : ∀ w : ℂ, H (Complex.I * w) = Iv (H w))
    (hhorizontal : ∀ u : ℍ, H (K u) = C u)
    (uw : ℍ × ℂ) :
    (fun v : ℍ × ℂ => (v.1, H v.2)) (graphComplex J K uw) =
      sphereGraphComplex J C Iv (uw.1, H uw.2) := by
  apply Prod.ext
  · rfl
  · change H (Complex.I * (uw.2 + K uw.1) - K (J uw.1)) =
      Iv (H uw.2 + C uw.1) - C (J uw.1)
    calc
      H (Complex.I * (uw.2 + K uw.1) - K (J uw.1)) =
          H (Complex.I * (uw.2 + K uw.1)) - H (K (J uw.1)) := by
            rw [map_sub]
      _ = Iv (H (uw.2 + K uw.1)) - C (J uw.1) := by
            rw [hvertical, hhorizontal]
      _ = Iv (H uw.2 + C uw.1) - C (J uw.1) := by
            rw [map_add, hhorizontal]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfGraphAlgebra
