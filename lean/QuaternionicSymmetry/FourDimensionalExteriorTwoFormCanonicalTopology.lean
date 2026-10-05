import QuaternionicSymmetry.FourDimensionalExteriorTwoFormTopology
import Mathlib.LinearAlgebra.Dimension.Free

/-! A basis-independent canonical topology on genuine real-four-dimensional
exterior two-covectors. Every six-coordinate chart is a homeomorphism for
this same topology; no preferred quaternionic frame is built into it. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorTwoFormCanonicalTopology

open Module FourDimensionalExteriorHodge
open FourDimensionalExteriorTwoFormTopology
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def canonicalBasis (hdim : Module.finrank ℝ V = 4) : Basis (Fin 4) ℝ V :=
  Module.finBasisOfFinrankEq (R := ℝ) (M := V) hdim

def canonicalTwoFormTopology (hdim : Module.finrank ℝ V = 4) :
    TopologicalSpace (TwoForm V) :=
  twoFormTopology (canonicalBasis hdim)

theorem canonicalTwoFormTopology_eq (hdim : Module.finrank ℝ V = 4)
    (b : Basis (Fin 4) ℝ V) :
    canonicalTwoFormTopology hdim = twoFormTopology b :=
  twoFormTopology_basis_independent (canonicalBasis hdim) b

theorem continuous_coordinates (hdim : Module.finrank ℝ V = 4)
    (b : Basis (Fin 4) ℝ V) :
    @Continuous (TwoForm V) (FourDimensionalCoordinateHodge.Two)
      (canonicalTwoFormTopology hdim) inferInstance (coordinates b) := by
  rw [canonicalTwoFormTopology_eq hdim b]
  exact continuous_induced_dom

theorem continuous_reconstruct (hdim : Module.finrank ℝ V = 4)
    (b : Basis (Fin 4) ℝ V) :
    @Continuous (FourDimensionalCoordinateHodge.Two) (TwoForm V)
      inferInstance (canonicalTwoFormTopology hdim) (reconstruct b) := by
  rw [canonicalTwoFormTopology_eq hdim b]
  apply continuous_induced_rng.mpr
  have hfun : (fun x : FourDimensionalCoordinateHodge.Two =>
      coordinates b (reconstruct b x)) = id := by
    funext x
    exact coordinates_reconstruct b x
  change Continuous (fun x : FourDimensionalCoordinateHodge.Two =>
    coordinates b (reconstruct b x))
  rw [hfun]
  exact continuous_id

theorem coordinate_homeomorphism_data (hdim : Module.finrank ℝ V = 4)
    (b : Basis (Fin 4) ℝ V) :
    @Continuous (TwoForm V) FourDimensionalCoordinateHodge.Two
        (canonicalTwoFormTopology hdim) inferInstance (coordinates b) ∧
      @Continuous FourDimensionalCoordinateHodge.Two (TwoForm V)
        inferInstance (canonicalTwoFormTopology hdim) (reconstruct b) ∧
      Function.LeftInverse (reconstruct b) (coordinates b) ∧
      Function.RightInverse (reconstruct b) (coordinates b) := by
  exact ⟨continuous_coordinates hdim b,
    continuous_reconstruct hdim b,
    reconstruct_coordinates b, coordinates_reconstruct b⟩

end
end QuaternionicSymmetry.FourDimensionalExteriorTwoFormCanonicalTopology
