import QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientSmooth
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeNegativeSphereSet
import QuaternionicSymmetry.ManifoldTwistorRadialRetraction

/-! The inverse coefficient extraction extends smoothly to a neighbourhood
of each native negative-unit sphere point after radial normalization in
Euclidean three-space. This is an ambient smoothness certificate for the
future embedded-sphere atlas, independent of the twistor topology. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientRadialSmooth

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeCoefficientExtraction
open ManifoldQuaternionicFourNativeCoefficientSmooth
open ManifoldQuaternionicFourNativeNegativeSphereSet
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereBundle
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

def nativeCoefficientEuclidean (i : atlas E M)
    (p : M × (E [⋀^Fin 2]→L[ℝ] ℝ)) : EuclideanThree :=
  toEuclidean (nativeCoefficientRaw Q hdim i p.1 p.2)

theorem nativeCoefficientEuclidean_smooth (i : atlas E M) :
    ContMDiffOn (𝓘(ℝ,E).prod 𝓘(ℝ,E [⋀^Fin 2]→L[ℝ] ℝ))
      𝓘(ℝ,EuclideanThree) ∞
      (nativeCoefficientEuclidean Q hdim i)
      (Q.frames.adaptedCore.baseSet i ×ˢ Set.univ) := by
  exact ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contMDiff)
    |>.comp_contMDiffOn (nativeCoefficientRaw_smooth Q hdim i)

theorem nativeCoefficientEuclidean_nonzero (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ)
    (hα : α ∈ nativeLocalSphereSet Q i x) :
    nativeCoefficientEuclidean Q hdim i (x,α) ≠ 0 := by
  obtain ⟨a,ha⟩ := hα
  have hraw : nativeCoefficientRaw Q hdim i x α = a.1 := by
    rw [ha]
    simpa using nativeCoefficientRaw_map Q hdim i x hi
      (coefficientSphereHomeomorph a)
  change toEuclidean (nativeCoefficientRaw Q hdim i x α) ≠ 0
  rw [hraw]
  exact ne_zero_of_mem_unit_sphere (coefficientSphereHomeomorph a)

def nativeCoefficientRadial (i : atlas E M)
    (p : M × (E [⋀^Fin 2]→L[ℝ] ℝ)) : EuclideanThree :=
  ‖nativeCoefficientEuclidean Q hdim i p‖⁻¹ •
    nativeCoefficientEuclidean Q hdim i p

theorem nativeCoefficientRadial_smoothAt_sphere (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ)
    (hα : α ∈ nativeLocalSphereSet Q i x) :
    ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E [⋀^Fin 2]→L[ℝ] ℝ))
      𝓘(ℝ,EuclideanThree) ∞
      (nativeCoefficientRadial Q hdim i) (x,α) := by
  let J := 𝓘(ℝ,E).prod 𝓘(ℝ,E [⋀^Fin 2]→L[ℝ] ℝ)
  let S : Set (M × (E [⋀^Fin 2]→L[ℝ] ℝ)) :=
    Q.frames.adaptedCore.baseSet i ×ˢ Set.univ
  have hS : IsOpen S :=
    (Q.frames.adaptedCore.isOpen_baseSet i).prod isOpen_univ
  have hpoint : (x,α) ∈ S := ⟨hi, Set.mem_univ _⟩
  have hf : ContMDiffAt J 𝓘(ℝ,EuclideanThree) ∞
      (nativeCoefficientEuclidean Q hdim i) (x,α) :=
    ((nativeCoefficientEuclidean_smooth Q hdim i) (x,α) hpoint).contMDiffAt
      (hS.mem_nhds hpoint)
  have hne := nativeCoefficientEuclidean_nonzero Q hdim i x hi α hα
  have hn : ContMDiffAt J 𝓘(ℝ) ∞
      (fun p => ‖nativeCoefficientEuclidean Q hdim i p‖) (x,α) :=
    (contDiffAt_norm ℝ hne).contMDiffAt.comp (x,α) hf
  have hn0 : ‖nativeCoefficientEuclidean Q hdim i (x,α)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hne
  exact (hn.inv₀ hn0).smul hf

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientRadialSmooth
