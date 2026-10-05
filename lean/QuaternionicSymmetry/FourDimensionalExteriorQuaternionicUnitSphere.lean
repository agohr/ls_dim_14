import QuaternionicSymmetry.FourDimensionalExteriorHodgeReversedHalves
import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal

/-! The metric normalization of the quaternionic operator-to-two-form map.
In an adapted orthonormal four-frame each generator form has squared norm two,
so the unit coefficient sphere maps to the unit exterior sphere after scaling
by the inverse square root of two. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitSphere

open FourDimensionalExteriorHodge FourDimensionalCoordinateHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalQuaternionicHodgeFrame
open FourDimensionalQuaternionicPositiveSubmodule
open FourDimensionalExteriorHodgeOrientationFlip
open FourDimensionalExteriorHodgeReversedHalves
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldQuaternionicRankThreeOrthogonal
open scoped BigOperators
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

def coefficientSquare (a : Fin 3 → ℝ) : ℝ := ∑ t : Fin 3, a t * a t
def coordinateSquare (x : Two) : ℝ := ∑ t : Fin 6, x t * x t

theorem coordinates_synth (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1)
    (a : Fin 3 → ℝ) :
    coordinates (frameBasis Q hdim v hv).toBasis
      (operatorForm (frameBasis Q hdim v hv).toBasis (synth Q a)) =
      a 0 • plusI + a 1 • plusJ + a 2 • plusK := by
  have hg (t : Fin 3) :
      coordinates (frameBasis Q hdim v hv).toBasis
        (operatorForm (frameBasis Q hdim v hv).toBasis
          (quaternionicGenerator Q t)) = ![plusI, plusJ, plusK] t := by
    change coordinates (frameBasis Q hdim v hv).toBasis
      (HyperholomorphicExterior.form (frameBasis Q hdim v hv).toBasis
        (quaternionicGenerator Q t).toLinearMap) = _
    rw [coordinates_operatorForm _ _
      (quaternionicSpan_skew Q _ (generator_mem_span Q t))]
    exact generator_coordinates Q hdim v hv t
  rw [synth_apply]
  simp only [map_sum, map_smul]
  simp only [Fin.sum_univ_three]
  rw [hg 0, hg 1, hg 2]
  rfl

theorem coordinateSquare_synth (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1)
    (a : Fin 3 → ℝ) :
    coordinateSquare (coordinates (frameBasis Q hdim v hv).toBasis
      (operatorForm (frameBasis Q hdim v hv).toBasis (synth Q a))) =
      2 * coefficientSquare a := by
  rw [coordinates_synth]
  simp [coordinateSquare, coefficientSquare, Fin.sum_univ_six,
    Fin.sum_univ_three, plusI, plusJ, plusK, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem normalized_coordinateSquare_synth (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1)
    (a : Fin 3 → ℝ) (ha : coefficientSquare a = 1) :
    coordinateSquare (coordinates (frameBasis Q hdim v hv).toBasis
      ((Real.sqrt 2)⁻¹ •
        operatorForm (frameBasis Q hdim v hv).toBasis (synth Q a))) = 1 := by
  rw [map_smul]
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [coordinates_synth]
  have hsq : coordinateSquare (a 0 • plusI + a 1 • plusJ + a 2 • plusK) =
      2 * coefficientSquare a := by
    simpa only [coordinates_synth] using coordinateSquare_synth Q hdim v hv a
  have hscale (x : Two) (c : ℝ) :
      coordinateSquare (c • x) = c ^ 2 * coordinateSquare x := by
    simp [coordinateSquare, Fin.sum_univ_six, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hscale, hsq, ha]
  have : (Real.sqrt 2)⁻¹ ^ 2 * (2 * 1) = 1 := by
    field_simp
    nlinarith
  exact this

theorem normalized_synth_negative_after_orientationFlip
    (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1)
    (a : Fin 3 → ℝ) :
    frameStar (swap01 (frameBasis Q hdim v hv))
      ((Real.sqrt 2)⁻¹ •
        operatorForm (frameBasis Q hdim v hv).toBasis (synth Q a)) =
      -((Real.sqrt 2)⁻¹ •
        operatorForm (frameBasis Q hdim v hv).toBasis (synth Q a)) := by
  apply quaternionicForms_negative_after_orientationFlip Q hdim v hv
  exact Submodule.smul_mem _ _ ⟨synth Q a, synth_mem Q a, rfl⟩

end
end QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitSphere
