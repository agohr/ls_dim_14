import QuaternionicSymmetry.HolomorphicLineOneFormCoordinates
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-! Chain rules for the actual holomorphic coordinate representatives. -/
namespace QuaternionicSymmetry.HolomorphicChartDerivative
open HolomorphicLineOneFormCoordinates
open scoped Manifold ContDiff
noncomputable section
variable {E V G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [TopologicalSpace G] [ChartedSpace E G] [IsManifold 𝓘(ℂ,E) ∞ G]
  [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℂ,V) ∞ M]

theorem chart_derivative (i : atlas V M) (x : M) (hx : x ∈ i.1.source) :
    mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) i.1 x =
      (tangentBundleCore 𝓘(ℂ,V) M).coordChange (achart V x) i x := by
  have hs := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,V)) (n := ∞)
    (IsManifold.subset_maximalAtlas i.2) hx
  rw [(hs.mdifferentiableAt (by simp)).mfderiv,tangent_coordChange_eq_fderiv]
  simp only [writtenInExtChartAt,mfld_simps,fderivWithin_univ]

theorem conjugate_derivative (f : G → M) (hf : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,V) ∞ f)
    (j : atlas E G) (i : atlas V M) (y : E) (hy : y ∈ j.1.target)
    (hi : f (j.1.symm y) ∈ i.1.source) :
    fderiv ℂ (fun q => i.1 (f (j.1.symm q))) y =
      ((tangentBundleCore 𝓘(ℂ,V) M).coordChange (achart V (f (j.1.symm y))) i (f (j.1.symm y))).comp
        ((mfderiv 𝓘(ℂ,E) 𝓘(ℂ,V) f (j.1.symm y)).comp
          ((tangentBundleCore 𝓘(ℂ,E) G).coordChange j (achart E (j.1.symm y)) (j.1.symm y))) := by
  have hj := (contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ,E)) (n := ∞)
    (IsManifold.subset_maximalAtlas j.2) hy).mdifferentiableAt (by simp)
  have hc := (contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,V)) (n := ∞)
    (IsManifold.subset_maximalAtlas i.2) hi).mdifferentiableAt (by simp)
  have hfj := (hf.mdifferentiableAt (by simp) (x := j.1.symm y)).comp y hj
  rw [← mfderiv_eq_fderiv]
  change mfderiv 𝓘(ℂ,E) 𝓘(ℂ,V) (i.1 ∘ (f ∘ j.1.symm)) y = _
  rw [mfderiv_comp y hc hfj,mfderiv_comp y (hf.mdifferentiableAt (by simp)) hj]
  dsimp only [Function.comp_def]
  rw [chart_derivative i _ hi,mfderiv_chart_symm_eq_coordChange j y hy]

end
end QuaternionicSymmetry.HolomorphicChartDerivative
