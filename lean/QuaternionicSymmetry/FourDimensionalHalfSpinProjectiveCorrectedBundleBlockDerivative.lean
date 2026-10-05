import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleMFDeriv

/-! The corrected local Hopf differential is block-diagonal in true
projective/sphere bundle charts; its fiber block is the genuine `mfderiv`
of the antipodally corrected CP¹-to-sphere map. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative

open scoped Manifold ContDiff Quaternion
open FourDimensionalHalfSpinProjectiveCorrectedBundleChart
  FourDimensionalHalfSpinProjectiveCorrectedBundleChartSmooth
  FourDimensionalHalfSpinProjectiveFixedChartTarget
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorCorrectedHopf

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def indexedCorrectedHopf (i : Fin 2) (z : ℂ) : geometricSphere :=
  correctedHopf (FourDimensionalHalfSpinProjectiveAllCoreChartDomain.indexedSourcePoint i z)

theorem indexedCorrectedHopf_mdifferentiableAt (p : M) (i : Fin 2)
    (c : ℍ × ℂ) (hc : c ∈ fixedChartTarget Q p i) :
    MDifferentiableAt 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf i) c.2 := by
  have hslice : ContMDiff 𝓘(ℝ,ℂ)
      (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ)) ∞
      (fun z : ℂ => (c.1,z)) :=
    contMDiff_const.prodMk contMDiff_id
  have hlocal : ContMDiffAt (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ))
      (𝓘(ℝ,ℍ).prod (𝓡 2)) ∞ (fixedCorrectedHopf i) c := by
    simpa only [modelWithCornersSelf_prod, chartedSpaceSelf_prod] using
      fixedCorrectedHopf_smoothAt Q p i c hc
  have h := hlocal.comp c.2 hslice.contMDiffAt
  have hsnd : ContMDiffAt 𝓘(ℝ,ℂ) (𝓡 2) ∞
      (fun z : ℂ => (fixedCorrectedHopf i (c.1,z)).2) c.2 :=
    contMDiffAt_snd.comp c.2 h
  exact hsnd.mdifferentiableAt (by simp)

theorem fixedCorrectedHopf_mfderiv (p : M) (i : Fin 2)
    (c : ℍ × ℂ) (hc : c ∈ fixedChartTarget Q p i)
    (u : ℍ) (w : ℂ) :
    mfderiv (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ))
      (𝓘(ℝ,ℍ).prod (𝓡 2))
      (fixedCorrectedHopf i) c (u,w) =
        (u, mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf i) c.2 w) := by
  have hid : MDifferentiableAt 𝓘(ℝ,ℍ) 𝓘(ℝ,ℍ) id c.1 :=
    mdifferentiableAt_id
  have hg := indexedCorrectedHopf_mdifferentiableAt Q p i c hc
  change mfderiv (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ))
    (𝓘(ℝ,ℍ).prod (𝓡 2))
    (Prod.map id (indexedCorrectedHopf i)) c (u,w) = _
  rw [mfderiv_prodMap hid hg, mfderiv_id]
  rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
