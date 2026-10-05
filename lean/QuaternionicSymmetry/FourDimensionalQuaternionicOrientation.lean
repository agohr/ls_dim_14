import QuaternionicSymmetry.FourDimensionalQuaternionicFrameOrientation
import Mathlib.Analysis.InnerProductSpace.Orientation

/-! The determinant-one transition theorem identifies every unit quaternionic
frame with one genuine Mathlib orientation, not just a coordinate sign. -/
namespace QuaternionicSymmetry.FourDimensionalQuaternionicOrientation

open FourDimensionalQuaternionicHodgeFrame
open FourDimensionalQuaternionicFrameOrientation
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

theorem frame_orientation_eq (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v w : V)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    (frameBasis Q hdim v hv).toBasis.orientation =
      (frameBasis Q hdim w hw).toBasis.orientation := by
  rw [Module.Basis.orientation_eq_iff_det_pos]
  change 0 < (frameTransitionMatrix Q hdim v w hv hw).det
  rw [frameTransitionMatrix_det_one]
  norm_num

end
end QuaternionicSymmetry.FourDimensionalQuaternionicOrientation
