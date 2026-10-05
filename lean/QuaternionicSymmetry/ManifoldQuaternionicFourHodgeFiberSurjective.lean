import QuaternionicSymmetry.ManifoldQuaternionicFourNegativeHodgeSphere

/-! Every normalized negative-Hodge two-form on an actual tangent fiber
comes from a point of the original quaternionic twistor sphere over that
base point. No topology on the exterior-form sphere bundle is asserted here. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberSurjective

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicUnitSphere
open FourDimensionalExteriorQuaternionicUnitSurjective
open FourDimensionalExteriorHodgeOrientationFlip
open FourDimensionalExteriorCanonicalHodge
open FourDimensionalQuaternionicHodgeFrame
open ManifoldQuaternionicFourHodgeOverlapExterior
open ManifoldQuaternionicFourGlobalHodge
open ManifoldQuaternionicFourTangentOrientation
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldQuaternionicFourTwistorHodgeGlobalMap
open ManifoldQuaternionicFourNegativeHodgeSphere
open ManifoldQuaternionicMetric
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

theorem negativeTangentUnitHalf_exists_twistor
    (x : M) (α : TwoForm (TangentSpace 𝓘(ℝ,E) x))
    (hα : α ∈ negativeTangentUnitHalf Q hdim x) :
    ∃ z : TwistorSphere Q, projection Q z = x ∧
      twistorTangentTwoForm Q hdim z = α := by
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  let C := localToTangentEquiv Q k x hk
  let b := localBasis Q hdim k
  let β : TwoForm E := pullbackTwoForm b C.toLinearMap α
  have hpos : tangentHodgeStar Q hdim x α = α := by
    have h := hα.1
    change -(tangentHodgeStar Q hdim x α) = -α at h
    exact neg_inj.mp h
  have hstar : canonicalStar (Q.reduction.Q k) hdim β = β := by
    have h := tangentHodgeStar_local Q hdim k x hk b α
    rw [hpos] at h
    exact h.symm
  have hrev : frameStar (swap01 (frameBasis (Q.reduction.Q k) hdim
      (unit : E) unit_norm)) β = -β := by
    rw [frameStar_swap01,
      ← canonicalStar_eq_frameStar (Q.reduction.Q k) hdim
        (unit : E) unit_norm, hstar]
  have hnorm : coordinateSquare (coordinates b β) = 1 := hα.2
  let γ : negativeUnitHalf (frameBasis (Q.reduction.Q k) hdim
      (unit : E) unit_norm) := ⟨β, hrev, hnorm⟩
  obtain ⟨a,ha,hform⟩ := negativeUnitHalf_surjective
    (Q.reduction.Q k) hdim (unit : E) unit_norm γ
  let z := pointOfLocal Q k x hk ⟨a, by exact ha⟩
  refine ⟨z, projection_pointOfLocal Q k x hk _, ?_⟩
  have hz := twistorTangentTwoForm_local Q hdim z k
    (by simpa [z, projection_pointOfLocal] using hk)
  have hcoord : (localCoordinate Q k z
      (by simpa [z, projection_pointOfLocal] using hk)).1 = a := by
    simpa [z, projection_pointOfLocal] using
      congrArg Subtype.val
        (localCoordinate_pointOfLocal Q k x hk (⟨a, ha⟩ : coefficientSphere))
  have hp := localTangentTwoForm_pullback Q hdim k x hk b a
  change (Real.sqrt 2)⁻¹ •
      FourDimensionalExteriorQuaternionicHalf.operatorForm b
        (VectorBundleFrameTransitions.QuaternionicFrameReduction.synth
          (Q.reduction.Q k) a) = β at hform
  rw [hform] at hp
  change pullbackTwoForm b C.toLinearMap
      (localTangentTwoForm Q hdim k x hk a) =
    pullbackTwoForm b C.toLinearMap α at hp
  have heq : localTangentTwoForm Q hdim k x hk a = α := by
    apply ExteriorDuality.twoform_ext b
    intro v w
    have he := congrArg (fun θ : TwoForm E =>
      BilinearExterior.evaluate (C.symm v) (C.symm w) θ) hp
    change BilinearExterior.evaluate (C.symm v) (C.symm w)
        (pullbackTwoForm b C.toLinearMap
          (localTangentTwoForm Q hdim k x hk a)) =
      BilinearExterior.evaluate (C.symm v) (C.symm w)
        (pullbackTwoForm b C.toLinearMap α) at he
    rw [evaluate_pullbackTwoForm, evaluate_pullbackTwoForm] at he
    change BilinearExterior.evaluate (C (C.symm v) : E)
        (C (C.symm w) : E) (localTangentTwoForm Q hdim k x hk a) =
      BilinearExterior.evaluate (C (C.symm v) : E)
        (C (C.symm w) : E) α at he
    rw [C.apply_symm_apply, C.apply_symm_apply] at he
    exact he
  simpa only [hz, hcoord, projection_pointOfLocal] using heq

end
end QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberSurjective
