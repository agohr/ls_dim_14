import QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitInjective

/-! In a genuine quaternionic orthonormal four-frame, the normalized
quaternionic operator forms are exactly the unit sphere in the Hodge-negative
half for the reversed orientation. This is a pointwise fiber statement. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitSurjective

open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalExteriorQuaternionicUnitSphere
open FourDimensionalExteriorHodgeOrientationFlip
open FourDimensionalQuaternionicHodgeFrame
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

def negativeUnitHalf (b : OrthonormalBasis (Fin 4) ℝ V) :=
  {α : TwoForm V // frameStar (swap01 b) α = -α ∧
    coordinateSquare (coordinates b.toBasis α) = 1}

theorem normalized_synth_in_negativeUnitHalf
    (Q : QuaternionicStructure V) (hdim : Module.finrank ℝ V = 4)
    (v : V) (hv : ‖v‖ = 1) (a : Fin 3 → ℝ)
    (ha : coefficientSquare a = 1) :
    (Real.sqrt 2)⁻¹ • operatorForm (frameBasis Q hdim v hv).toBasis
      (synth Q a) ∈
    {α : TwoForm V | frameStar (swap01 (frameBasis Q hdim v hv)) α = -α ∧
      coordinateSquare (coordinates (frameBasis Q hdim v hv).toBasis α) = 1} :=
  ⟨normalized_synth_negative_after_orientationFlip Q hdim v hv a,
    normalized_coordinateSquare_synth Q hdim v hv a ha⟩

theorem negativeUnitHalf_surjective
    (Q : QuaternionicStructure V) (hdim : Module.finrank ℝ V = 4)
    (v : V) (hv : ‖v‖ = 1)
    (α : negativeUnitHalf (frameBasis Q hdim v hv)) :
    ∃ a : Fin 3 → ℝ, coefficientSquare a = 1 ∧
      (Real.sqrt 2)⁻¹ •
        operatorForm (frameBasis Q hdim v hv).toBasis (synth Q a) = α.1 := by
  let b := frameBasis Q hdim v hv
  have hp : frameStar b α.1 = α.1 := by
    have h := α.2.1
    rw [frameStar_swap01] at h
    exact neg_inj.mp h
  have hmem : α.1 ∈ (quaternionicSpan Q).map (operatorForm b.toBasis) := by
    rw [← positiveExteriorHalf_eq_quaternionicFormImage Q hdim v hv]
    exact (mem_positiveExteriorHalf b α.1).mpr hp
  obtain ⟨A,hA,hAα⟩ := hmem
  let a := coeff Q A
  have hα : operatorForm b.toBasis (synth Q a) = α.1 := by
    rw [synth_coeff_of_mem Q A hA]
    exact hAα
  have hnorm : 2 * coefficientSquare a = 1 := by
    calc
      2 * coefficientSquare a =
          coordinateSquare (coordinates b.toBasis
            (operatorForm b.toBasis (synth Q a))) :=
        (coordinateSquare_synth Q hdim v hv a).symm
      _ = coordinateSquare (coordinates b.toBasis α.1) := by rw [hα]
      _ = 1 := α.2.2
  let c : Fin 3 → ℝ := Real.sqrt 2 • a
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hc : coefficientSquare c = 1 := by
    have hscale (r : ℝ) : coefficientSquare (r • a) =
        r ^ 2 * coefficientSquare a := by
      simp [coefficientSquare, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      ring
    change coefficientSquare ((Real.sqrt 2) • a) = 1
    rw [hscale, hs]
    exact hnorm
  refine ⟨c, hc, ?_⟩
  change (Real.sqrt 2)⁻¹ • operatorForm b.toBasis (synth Q c) = α.1
  simp only [c, map_smul, smul_smul]
  rw [inv_mul_cancel₀ hn, one_smul, hα]

end
end QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitSurjective
