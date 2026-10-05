import QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitSphere

/-! The normalized operator-form map from quaternionic coefficients is
faithful. This is the fiberwise injectivity needed for the sphere comparison. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitInjective

open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalExteriorQuaternionicUnitSphere
open FourDimensionalQuaternionicHodgeFrame
open FourDimensionalCoordinateHodge
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

theorem normalized_operatorForm_synth_injective
    (Q : QuaternionicStructure V) (hdim : Module.finrank ℝ V = 4)
    (v : V) (hv : ‖v‖ = 1) (a c : Fin 3 → ℝ)
    (h : (Real.sqrt 2)⁻¹ •
        operatorForm (frameBasis Q hdim v hv).toBasis (synth Q a) =
      (Real.sqrt 2)⁻¹ •
        operatorForm (frameBasis Q hdim v hv).toBasis (synth Q c)) :
    a = c := by
  have hcoords := congrArg
    (coordinates (frameBasis Q hdim v hv).toBasis) h
  simp only [map_smul, coordinates_synth] at hcoords
  have hs : (Real.sqrt 2)⁻¹ ≠ (0 : ℝ) :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  funext t
  fin_cases t
  · have ht := congrFun hcoords 0
    simp [hs, plusI, plusJ, plusK, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at ht
    exact ht
  · have ht := congrFun hcoords 1
    simp [hs, plusI, plusJ, plusK, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at ht
    exact ht
  · have ht := congrFun hcoords 2
    simp [hs, plusI, plusJ, plusK, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at ht
    exact ht

end
end QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitInjective
