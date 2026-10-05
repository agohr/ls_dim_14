import QuaternionicSymmetry.ManifoldTwistorRadialRetraction
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
namespace QuaternionicSymmetry.ManifoldTwistorRadialRetraction
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

private theorem inclusion_mfderiv (x : nonzeroOpen) :
    mfderiv 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,EuclideanThree)
      (Subtype.val : nonzeroOpen → EuclideanThree) x =
    ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ,EuclideanThree) x) := by
  have h : HasMFDerivAt 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,EuclideanThree)
      (Subtype.val : nonzeroOpen → EuclideanThree) x
      (ContinuousLinearMap.id ℝ _) := by
    constructor
    · exact continuous_subtype_val.continuousAt
    · apply (hasFDerivWithinAt_id _ (Set.range 𝓘(ℝ,EuclideanThree))).congr_of_eventuallyEq
      · filter_upwards [extChartAt_target_mem_nhdsWithin
          (I := 𝓘(ℝ,EuclideanThree)) x] with y hy
        simp [writtenInExtChartAt, extChartAt] at hy ⊢
        exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
          (Subtype.val : nonzeroOpen → EuclideanThree) nonzeroOpen.isOpenEmbedding'
          ⟨⟨y,hy⟩,rfl⟩
      · simp [writtenInExtChartAt, extChartAt]
        exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
          (Subtype.val : nonzeroOpen → EuclideanThree) nonzeroOpen.isOpenEmbedding'
  exact h.mfderiv

theorem sphereIntoNonzero_mfderiv (a : geometricSphere)
    (v : TangentSpace (𝓡 2) a) :
    mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree) sphereIntoNonzero a v =
      mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree)
        ((↑) : geometricSphere → EuclideanThree) a v := by
  have hcomp := mfderiv_comp (f := sphereIntoNonzero)
    (g := (Subtype.val : nonzeroOpen → EuclideanThree)) (I := 𝓡 2)
    (I' := 𝓘(ℝ,EuclideanThree)) (I'' := 𝓘(ℝ,EuclideanThree))
    a ((contMDiff_isOpenEmbedding nonzeroOpen.isOpenEmbedding'
      (I := 𝓘(ℝ,EuclideanThree)) (n := ∞)).mdifferentiableAt
      (by norm_num))
    (sphereIntoNonzero_smooth.mdifferentiableAt (by norm_num))
  have heq : ((Subtype.val : nonzeroOpen → EuclideanThree) ∘ sphereIntoNonzero) =
      ((↑) : geometricSphere → EuclideanThree) := rfl
  rw [heq, inclusion_mfderiv] at hcomp
  have hv := congrArg (fun L : TangentSpace (𝓡 2) a →L[ℝ] EuclideanThree => L v) hcomp
  simpa [ContinuousLinearMap.comp_apply] using hv.symm

theorem radialTangent_left_inverse
    (p : TangentBundle (𝓡 2) geometricSphere) :
    tangentMap 𝓘(ℝ,EuclideanThree) (𝓡 2) radial
      (tangentMap (𝓡 2) 𝓘(ℝ,EuclideanThree) sphereIntoNonzero p) = p := by
  have hcomp := tangentMap_comp
    (I := 𝓡 2) (I' := 𝓘(ℝ,EuclideanThree)) (I'' := 𝓡 2)
    (radial_smooth.mdifferentiable (by norm_num))
    (sphereIntoNonzero_smooth.mdifferentiable (by norm_num))
  have hid : radial ∘ sphereIntoNonzero = id := by
    funext a
    exact radial_sphereIntoNonzero a
  change (tangentMap 𝓘(ℝ,EuclideanThree) (𝓡 2) radial ∘
    tangentMap (𝓡 2) 𝓘(ℝ,EuclideanThree) sphereIntoNonzero) p = p
  rw [← hcomp, hid, tangentMap_id]
  rfl
end
end QuaternionicSymmetry.ManifoldTwistorRadialRetraction
