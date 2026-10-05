import QuaternionicSymmetry.FourDimensionalQuaternionicFrameOrientation

/-! The Hodge-positive half in every actual quaternionic orthonormal frame is
the rank-three quaternionic two-form plane. The preceding orientation theorem
shows these frames all use the same orientation sign. -/
namespace QuaternionicSymmetry.FourDimensionalQuaternionicPositiveHalf

open FourDimensionalCoordinateHodge FourDimensionalQuaternionicHodgeFrame
open FourDimensionalQuaternionicFrameOrientation
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

theorem positive_iff_quaternionic_coordinates (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) (x : Two) :
    FourDimensionalCoordinateHodge.star x = x ↔
      x = (x 0) • operatorTwoCoords (frameBasis Q hdim v hv)
            Q.I.toLinearEquiv.toLinearMap +
          (x 1) • operatorTwoCoords (frameBasis Q hdim v hv)
            Q.J.toLinearEquiv.toLinearMap +
          (x 2) • operatorTwoCoords (frameBasis Q hdim v hv)
            Q.K.toLinearEquiv.toLinearMap := by
  rw [I_coordinates, J_coordinates, K_coordinates]
  exact plus_iff x

theorem positive_iff_quaternionic_span (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) (x : Two) :
    FourDimensionalCoordinateHodge.star x = x ↔
      ∃ a b c : ℝ,
        x = a • operatorTwoCoords (frameBasis Q hdim v hv)
              Q.I.toLinearEquiv.toLinearMap +
            b • operatorTwoCoords (frameBasis Q hdim v hv)
              Q.J.toLinearEquiv.toLinearMap +
            c • operatorTwoCoords (frameBasis Q hdim v hv)
              Q.K.toLinearEquiv.toLinearMap := by
  rw [I_coordinates, J_coordinates, K_coordinates]
  constructor
  · intro hx
    exact ⟨x 0, x 1, x 2, (plus_iff x).mp hx⟩
  · rintro ⟨a, b, c, hx⟩
    rw [hx]
    simp

theorem quaternionic_frame_orientation_independent (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v w : V)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    (frameTransitionMatrix Q hdim v w hv hw).det = 1 :=
  frameTransitionMatrix_det_one Q hdim v w hv hw

end
end QuaternionicSymmetry.FourDimensionalQuaternionicPositiveHalf
