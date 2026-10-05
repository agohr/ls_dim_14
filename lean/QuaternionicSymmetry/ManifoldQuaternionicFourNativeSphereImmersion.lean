import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereEmbeddingCharts

/-! The local native negative-sphere parametrization has injective actual
manifold derivative. The proof differentiates its smooth ambient left inverse
on the genuine adapted open set. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereImmersion

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSphereEmbeddingCharts
open scoped Manifold ContDiff Topology

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance

include hdim in
theorem nativeSphereProductMap_mfderiv_injective
    (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a : ManifoldTwistorCoefficientSphere.geometricSphere) :
    Function.Injective
      (mfderiv (𝓘(ℝ,E).prod (𝓡 2))
        (𝓘(ℝ,E).prod 𝓘(ℝ,E [⋀^Fin 2]→L[ℝ] ℝ))
        (nativeSphereProductMap Q i) (x,a)) := by
  let J := 𝓘(ℝ,E).prod (𝓡 2)
  let K := 𝓘(ℝ,E).prod 𝓘(ℝ,E [⋀^Fin 2]→L[ℝ] ℝ)
  let f := nativeSphereProductMap Q i
  let g := nativeSphereAmbientInverse Q hdim i
  have hS : IsOpen (Q.frames.adaptedCore.baseSet i ×ˢ Set.univ :
      Set (M × ManifoldTwistorCoefficientSphere.geometricSphere)) :=
    (Q.frames.adaptedCore.isOpen_baseSet i).prod isOpen_univ
  have hp : (x,a) ∈ (Q.frames.adaptedCore.baseSet i ×ˢ Set.univ :
      Set (M × ManifoldTwistorCoefficientSphere.geometricSphere)) :=
    ⟨hi,Set.mem_univ _⟩
  have hf : MDifferentiableAt J K f (x,a) :=
    (((nativeSphereProductMap_smooth Q i) (x,a) hp).contMDiffAt
      (hS.mem_nhds hp)).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt K J g (f (x,a)) :=
    (nativeSphereAmbientInverse_smoothAt Q hdim i x hi
      (ManifoldQuaternionicFourNativeSphereFormSmooth.nativeSphereForm Q i (x,a))
      ⟨ManifoldTwistorCoefficientSphere.coefficientSphereHomeomorph.symm a,
        by simp [ManifoldTwistorCoefficientSphere.coefficientSphereHomeomorph.apply_symm_apply]⟩)
      |>.mdifferentiableAt (by simp)
  have hEq : (g ∘ f) =ᶠ[𝓝 (x,a)] (id : M × ManifoldTwistorCoefficientSphere.geometricSphere → _) :=
    Filter.eventuallyEq_of_mem (hS.mem_nhds hp) (by
      intro p hp
      exact nativeSphereAmbientInverse_left Q hdim i p.1 hp.1 p.2)
  have hdf : (mfderiv K J g (f (x,a))).comp
      (mfderiv J K f (x,a)) = ContinuousLinearMap.id ℝ _ := by
    have h := hEq.mfderiv_eq (I := J) (I' := J)
    rw [mfderiv_comp (x,a) hg hf, mfderiv_id] at h
    exact h
  intro u v huv
  have h := congrArg (mfderiv K J g (f (x,a))) huv
  have hu := congrArg (fun L => L u) hdf
  have hv := congrArg (fun L => L v) hdf
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using hu.symm.trans (h.trans hv)

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereImmersion
