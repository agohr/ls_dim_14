import QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientExtraction
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeBilinearInclusion

/-! The explicit inverse coefficients vary jointly smoothly in the base
point and native alternating form. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientSmooth

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeCoefficientExtraction
open ManifoldQuaternionicFourNativeBilinearInclusion
open ManifoldQuaternionicFourTwistorHodgeFiber
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance

theorem nativeCoefficientRaw_smooth (i : atlas E M) :
    ContMDiffOn (𝓘(ℝ,E).prod 𝓘(ℝ,E [⋀^Fin 2]→L[ℝ] ℝ))
      𝓘(ℝ,Fin 3 → ℝ) ∞
      (fun p : M × (E [⋀^Fin 2]→L[ℝ] ℝ) =>
        nativeCoefficientRaw Q hdim i p.1 p.2)
      (Q.frames.adaptedCore.baseSet i ×ˢ Set.univ) := by
  let J := 𝓘(ℝ,E).prod 𝓘(ℝ,E [⋀^Fin 2]→L[ℝ] ℝ)
  let S : Set (M × (E [⋀^Fin 2]→L[ℝ] ℝ)) :=
    Q.frames.adaptedCore.baseSet i ×ˢ Set.univ
  have hbase : ContMDiffOn J 𝓘(ℝ,E) ∞
      (fun p : M × (E [⋀^Fin 2]→L[ℝ] ℝ) => p.1) S :=
    contMDiffOn_fst
  have hnative : ContMDiffOn J 𝓘(ℝ,E [⋀^Fin 2]→L[ℝ] ℝ) ∞
      (fun p : M × (E [⋀^Fin 2]→L[ℝ] ℝ) => p.2) S :=
    contMDiffOn_snd
  have hfrom : ContMDiffOn J 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun p : M × (E [⋀^Fin 2]→L[ℝ] ℝ) =>
        Q.frames.fromFrame i p.1) S :=
    (Q.frames.smooth_from i).comp hbase (by intro p hp; exact hp.1)
  have hbilinear : ContMDiffOn J 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : M × (E [⋀^Fin 2]→L[ℝ] ℝ) =>
        nativeToBilinearCLM p.2) S :=
    nativeToBilinearCLM.contMDiff.comp_contMDiffOn hnative
  apply contMDiffOn_pi_space.mpr
  intro t
  have hleft : ContMDiffOn J 𝓘(ℝ,E) ∞
      (fun p : M × (E [⋀^Fin 2]→L[ℝ] ℝ) =>
        Q.frames.fromFrame i p.1 ((localBasis Q hdim i) 0)) S :=
    hfrom.clm_apply contMDiffOn_const
  have hright : ContMDiffOn J 𝓘(ℝ,E) ∞
      (fun p : M × (E [⋀^Fin 2]→L[ℝ] ℝ) =>
        Q.frames.fromFrame i p.1 ((localBasis Q hdim i) t.succ)) S :=
    hfrom.clm_apply contMDiffOn_const
  have heval : ContMDiffOn J 𝓘(ℝ) ∞
      (fun p : M × (E [⋀^Fin 2]→L[ℝ] ℝ) =>
        p.2 ![Q.frames.fromFrame i p.1 ((localBasis Q hdim i) 0),
          Q.frames.fromFrame i p.1 ((localBasis Q hdim i) t.succ)]) S := by
    simpa only [nativeToBilinearCLM_apply] using
      (hbilinear.clm_apply hleft).clm_apply hright
  simpa only [nativeCoefficientRaw, Pi.smul_apply, smul_eq_mul] using
    (contMDiffOn_const : ContMDiffOn J 𝓘(ℝ) ∞
      (fun _ : M × (E [⋀^Fin 2]→L[ℝ] ℝ) => Real.sqrt 2) S).smul heval

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientSmooth
