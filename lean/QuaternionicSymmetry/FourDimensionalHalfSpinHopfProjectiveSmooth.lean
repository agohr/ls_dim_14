import QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineSphere
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfHomeomorph

/-! The explicit Hopf homeomorphism is real C∞ from the independently
constructed complex-projective affine atlas to the independently constructed
round-sphere atlas. Inverse smoothness and AHS complex compatibility are
separate obligations. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfProjectiveSmooth

open scoped Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfAffineSphere
open ComplexProjectiveTopology
  ManifoldTwistorCoefficientSphere

noncomputable section

def projectiveHopfGeometric (p : ProjectiveSpinor) : geometricSphere :=
  coefficientSphereHomeomorph (projectiveHopf p)

theorem projectiveHopfGeometric_chart (i : Fin 2) (w : Fin 1 → ℂ) :
    projectiveHopfGeometric ((projectiveChart 1 i).symm w) =
      affineSphere i w := by
  rw [projectiveChart_symm_apply, affineSphere_eq_hopf]
  exact congrArg coefficientSphereHomeomorph
    (projectiveHopf_mk (homogeneousVector 1 i w)
      (homogeneousVector_ne_zero 1 i w))

theorem projectiveHopfGeometric_contMDiff :
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) ∞ projectiveHopfGeometric := by
  intro p
  let i : Fin 2 := Classical.choose (exists_mem_affineDomain 1 p)
  have hp : p ∈ (projectiveChart 1 i).source := by
    rw [projectiveChart_source]
    exact Classical.choose_spec (exists_mem_affineDomain 1 p)
  rw [contMDiffAt_iff_source]
  have hlocal : ContMDiffWithinAt 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) ∞
      (affineSphere i) (Set.range 𝓘(ℝ, Fin 1 → ℂ))
      ((extChartAt 𝓘(ℝ, Fin 1 → ℂ) p) p) :=
    ((contMDiff_affineSphere i) _).contMDiffWithinAt
  apply hlocal.congr_of_eventuallyEq
  · filter_upwards [extChartAt_target_mem_nhdsWithin
      (I := 𝓘(ℝ, Fin 1 → ℂ)) p] with w hw
    have hchart : (chartAt (Fin 1 → ℂ) p) = projectiveChart 1 i := by
      rfl
    simpa only [extChartAt, hchart, mfld_simps] using
      (projectiveHopfGeometric_chart i w)
  · have hchart : (chartAt (Fin 1 → ℂ) p) = projectiveChart 1 i := rfl
    simpa only [extChartAt, hchart, mfld_simps] using
      (projectiveHopfGeometric_chart i ((projectiveChart 1 i) p))

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfProjectiveSmooth
