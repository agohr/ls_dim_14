import QuaternionicSymmetry.FourDimensionalExteriorUnitMapContinuous

/-! Explicit inverse coefficients for a normalized quaternionic two-form:
multiply its first three Q-frame exterior coordinates by √2. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorUnitInverse

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalExteriorQuaternionicUnitSphere
open FourDimensionalExteriorQuaternionicUnitSurjective
open FourDimensionalExteriorTwoFormCanonicalTopology
open FourDimensionalExteriorUnitMapContinuous
open FourDimensionalQuaternionicHodgeFrame
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

def firstThree (x : FourDimensionalCoordinateHodge.Two) : Fin 3 → ℝ :=
  fun t => x (t.castLE (by omega : 3 ≤ 6))

def inverseCoefficients (b : Basis (Fin 4) ℝ V) (α : TwoForm V) :
    Fin 3 → ℝ :=
  Real.sqrt 2 • firstThree (coordinates b α)

theorem inverseCoefficients_normalized_synth
    (Q : QuaternionicStructure V) (hdim : Module.finrank ℝ V = 4)
    (v : V) (hv : ‖v‖ = 1) (a : Fin 3 → ℝ) :
    inverseCoefficients (frameBasis Q hdim v hv).toBasis
      ((Real.sqrt 2)⁻¹ •
        operatorForm (frameBasis Q hdim v hv).toBasis (synth Q a)) = a := by
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  funext t
  fin_cases t <;>
    simp [inverseCoefficients, firstThree, coordinates_synth,
      FourDimensionalCoordinateHodge.plusI,
      FourDimensionalCoordinateHodge.plusJ,
      FourDimensionalCoordinateHodge.plusK,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hn, Fin.castLE] <;>
    field_simp

theorem inverseCoefficients_negativeUnitHalf
    (Q : QuaternionicStructure V) (hdim : Module.finrank ℝ V = 4)
    (v : V) (hv : ‖v‖ = 1)
    (α : negativeUnitHalf (frameBasis Q hdim v hv)) :
    let a := inverseCoefficients (frameBasis Q hdim v hv).toBasis α.1
    coefficientSquare a = 1 ∧
      (Real.sqrt 2)⁻¹ •
        operatorForm (frameBasis Q hdim v hv).toBasis (synth Q a) = α.1 := by
  obtain ⟨a,ha,hα⟩ := negativeUnitHalf_surjective Q hdim v hv α
  have hcoeff := inverseCoefficients_normalized_synth Q hdim v hv a
  rw [hα] at hcoeff
  simp only [hcoeff, ha, hα, and_self]

end
end QuaternionicSymmetry.FourDimensionalExteriorUnitInverse
