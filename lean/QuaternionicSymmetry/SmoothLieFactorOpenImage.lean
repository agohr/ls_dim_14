import QuaternionicSymmetry.LinearMapSurjectiveFactor
import QuaternionicSymmetry.SmoothGroupHomSurjectiveDerivative
import QuaternionicSymmetry.SmoothLieHomDerivativeComposition

/-! The derivative comparison needed for a possibly disconnected closed
centralizer gives an open image, not surjectivity onto all components. -/

namespace QuaternionicSymmetry.SmoothLieFactorOpenImage

open QuaternionicSymmetry.LinearMapSurjectiveFactor
open QuaternionicSymmetry.SmoothGroupHomSurjectiveDerivative
open QuaternionicSymmetry.SmoothLieHomDerivativeComposition
open scoped Manifold ContDiff
noncomputable section

variable {E F V G H K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G]
  [Group H] [TopologicalSpace H] [ChartedSpace F H]
  [IsManifold 𝓘(ℝ,F) ∞ H] [ContinuousMul H]
  [Group K] [TopologicalSpace K] [ChartedSpace V K]
  [IsManifold 𝓘(ℝ,V) ∞ K]

theorem isOpen_range_of_composite_range_exact
    (f : G →* H) (i : H →* K)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (hi : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,V) ∞ i)
    (hdi : Function.Injective
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) i 1))
    (S : Submodule ℝ V)
    (hComposite : LinearMap.range
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) (i.comp f) 1).toLinearMap) = S)
    (hUpper : LinearMap.range
      ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) i 1).toLinearMap) ≤ S) :
    IsOpen (f.range : Set H) := by
  have hChain := mfderiv_comp_hom_one i f hi hf
  have hLinear :
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) (i.comp f) 1).toLinearMap =
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) i 1).toLinearMap.comp
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f 1).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap hChain
  have hLower : S ≤ LinearMap.range
      ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) i 1).toLinearMap) := by
    rw [← hComposite, hLinear]
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    exact ⟨(mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f 1).toLinearMap u, rfl⟩
  have hEq : LinearMap.range
      (((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) i 1).toLinearMap).comp
        ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f 1).toLinearMap)) =
      LinearMap.range ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) i 1).toLinearMap) := by
    rw [← hLinear, hComposite]
    exact le_antisymm hLower hUpper
  have hdf : Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f 1) :=
    surjective_of_injective_comp_range_eq
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) i 1).toLinearMap
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f 1).toLinearMap hdi hEq
  exact isOpen_range_of_surjective_mfderiv_one f hf hdf

end
end QuaternionicSymmetry.SmoothLieFactorOpenImage
