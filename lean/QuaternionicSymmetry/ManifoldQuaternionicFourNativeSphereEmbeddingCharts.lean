import QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientSphereSmooth
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereFormSmooth

/-! The native negative-sphere parametrization and its explicit ambient
inverse are C∞ in local base–fiber product charts. This certifies the local
embedded-sphere geometry before any smooth structure is put on the global
Hodge subset. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereEmbeddingCharts

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldQuaternionicFourNativeNegativeSphereSet
open ManifoldQuaternionicFourNativeCoefficientSphereSmooth
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff

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

def nativeSphereProductMap (i : atlas E M)
    (p : M × geometricSphere) :
    M × (E [⋀^Fin 2]→L[ℝ] ℝ) :=
  (p.1,nativeSphereForm Q i p)

theorem nativeSphereProductMap_smooth (i : atlas E M) :
    ContMDiffOn (𝓘(ℝ,E).prod (𝓡 2))
      (𝓘(ℝ,E).prod 𝓘(ℝ,E [⋀^Fin 2]→L[ℝ] ℝ)) ∞
      (nativeSphereProductMap Q i)
      (Q.frames.adaptedCore.baseSet i ×ˢ Set.univ) := by
  exact contMDiffOn_fst.prodMk
    (nativeSphereForm_smooth Q i)

def nativeSphereAmbientInverse (i : atlas E M)
    (p : M × (E [⋀^Fin 2]→L[ℝ] ℝ)) : M × geometricSphere :=
  (p.1,nativeCoefficientSphereExtension Q hdim i p)

theorem nativeSphereAmbientInverse_smoothAt (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ)
    (hα : α ∈ nativeLocalSphereSet Q i x) :
    ContMDiffAt
      (𝓘(ℝ,E).prod 𝓘(ℝ,E [⋀^Fin 2]→L[ℝ] ℝ))
      (𝓘(ℝ,E).prod (𝓡 2)) ∞
      (nativeSphereAmbientInverse Q hdim i) (x,α) := by
  exact contMDiffAt_fst.prodMk
    (nativeCoefficientSphereExtension_smoothAt Q hdim i x hi α hα)

theorem nativeSphereAmbientInverse_left (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a : geometricSphere) :
    nativeSphereAmbientInverse Q hdim i
      (nativeSphereProductMap Q i (x,a)) = (x,a) := by
  apply Prod.ext
  · rfl
  · let c := coefficientSphereHomeomorph.symm a
    have hc : coefficientSphereHomeomorph c = a :=
      coefficientSphereHomeomorph.apply_symm_apply a
    change nativeCoefficientSphereExtension Q hdim i
      (x,nativeSphereForm Q i (x,a)) = a
    rw [← hc]
    exact nativeCoefficientSphereExtension_on_sphere Q hdim i x hi c

theorem nativeSphereAmbientInverse_right (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ)
    (hα : α ∈ nativeLocalSphereSet Q i x) :
    nativeSphereProductMap Q i
      (nativeSphereAmbientInverse Q hdim i (x,α)) = (x,α) := by
  obtain ⟨a,ha⟩ := hα
  apply Prod.ext
  · rfl
  · change nativeSphereForm Q i
      (x,nativeCoefficientSphereExtension Q hdim i (x,α)) = α
    have h := nativeCoefficientSphereExtension_on_sphere Q hdim i x hi a
    rw [ha]
    rw [h]

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereEmbeddingCharts
