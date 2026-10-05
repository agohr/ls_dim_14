import QuaternionicSymmetry.SelectedTorusExpDerivativeEquiv
import QuaternionicSymmetry.TorusWeightCharacterDifferentialLinear
import QuaternionicSymmetry.SelectedIntegralCharacterSmooth
import QuaternionicSymmetry.SelectedTorusCoordinateCurveSmooth
import QuaternionicSymmetry.TorusWeightCoordinateExponentialDerivative

/-! The actual selected-atlas differential of an integral character,
pulled back through the selected coordinate-exponential differential,
has the literal coordinate value `i μ_j`. -/

namespace QuaternionicSymmetry.SelectedTorusWeightDifferentialCoordinates

open CompactLieTorusInputs SelectedTorusEmbeddedLieAtlas
open SelectedTorusCompactExponentialSmooth
open SelectedTorusCompactExponentialLift
open TorusWeightCharacterDifferentialLinear
open TorusWeightCoordinateExponentialDerivative
open SelectedTorusCoordinateCurveSmooth SelectedIntegralCharacterSmooth
open ManifoldQuaternionicTorusAction
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [T2Space G]
  [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [LieGroup 𝓘(ℝ,V) ∞ G]
  {r d : ℕ}

private def singleCLM (j : Fin r) : ℝ →L[ℝ] (Fin r → ℝ) :=
  ⟨LinearMap.single ℝ (fun _ : Fin r => ℝ) j,
    (LinearMap.single ℝ (fun _ : Fin r => ℝ) j).continuous_of_finiteDimensional⟩

private theorem singleCLM_zero (j : Fin r) : singleCLM j 0 = 0 := by simp [singleCLM]

private theorem exp_comp_single (j : Fin r) :
    circleExpPi r ∘ singleCLM j = coordinateCircleExp j := by
  classical
  funext t k
  by_cases h : k = j
  · subst k
    simp [singleCLM, circleExpPi, coordinateCircleExp, Pi.mulSingle_apply,
      Pi.single_apply]
  · simp [singleCLM, circleExpPi, coordinateCircleExp, Pi.mulSingle_apply,
      Pi.single_apply, h]

theorem weightCharacterDifferential_comp_exp_single
    (T : TorusEmbedding G r)
    (g : EmbeddedRealLieAtlas V (Torus r) G T.hom d)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (μ : Fin r → ℤ) (j : Fin r) :
    letI := g.charts
    weightCharacterDifferentialLinear μ g.charts
      (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin d → ℝ)
        (circleExpPi r) 0 (Pi.single j 1)) =
      Complex.I * (μ j : ℂ) := by
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.lieGroup
  have hExp := circleExpPi_smooth_selected T g hClosed hImm hLee
  have hχ : MDifferentiableAt 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
      (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 :=
    (weightCharacter_complex_contMDiff μ g.charts g.manifold g.lieGroup
      hClosed hImm hLee).mdifferentiableAt (by simp)
  have hSingle : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin r → ℝ)
      (singleCLM j) 0 :=
    ((singleCLM j).contMDiff (n := ∞)).mdifferentiableAt (by simp)
  have hExpComp := mfderiv_comp (I := 𝓘(ℝ,ℝ))
    (I' := 𝓘(ℝ,Fin r → ℝ)) (I'' := 𝓘(ℝ,Fin d → ℝ))
    (x := (0 : ℝ)) (hExp.mdifferentiableAt (by simp)) hSingle
  rw [singleCLM_zero, exp_comp_single] at hExpComp
  have hSingleDeriv : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin r → ℝ)
      (singleCLM j) 0 = singleCLM j := by
    rw [mfderiv_eq_fderiv]
    exact (singleCLM j).hasFDerivAt.fderiv
  rw [hSingleDeriv] at hExpComp
  have hCurve : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin d → ℝ)
      (coordinateCircleExp j) 0 :=
    (coordinateCircleExp_smooth_of_exp j g.charts hExp).mdifferentiableAt (by simp)
  have hχ0 : MDifferentiableAt 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
      (fun t : Torus r => (weightCharacter μ t : ℂ))
      (coordinateCircleExp j 0) := by
    simpa only [coordinateCircleExp_zero] using hχ
  have hCharComp := mfderiv_comp (I := 𝓘(ℝ,ℝ))
    (I' := 𝓘(ℝ,Fin d → ℝ)) (I'' := 𝓘(ℝ,ℂ))
    (x := (0 : ℝ)) hχ0 hCurve
  rw [coordinateCircleExp_zero] at hCharComp
  have hCurveDeriv : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ)
      ((fun t : Torus r => (weightCharacter μ t : ℂ)) ∘ coordinateCircleExp j) 0 =
      coordinateCharacterDerivative μ j := by
    rw [mfderiv_eq_fderiv]
    exact (character_curve_hasFDerivAt_zero μ j).fderiv
  rw [hExpComp] at hCharComp
  have hCombined := hCurveDeriv.symm.trans hCharComp
  have hAt1 := congrArg (fun F : ℝ →L[ℝ] ℂ => F 1) hCombined
  simpa [weightCharacterDifferentialLinear_apply,
    coordinateCharacterDerivative_apply, ContinuousLinearMap.comp_apply,
    singleCLM] using hAt1.symm

end
end QuaternionicSymmetry.SelectedTorusWeightDifferentialCoordinates
