import QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientRadialSmooth
import QuaternionicSymmetry.ManifoldQuaternionicSphereSmoothAt

/-! The native coefficient inverse admits a genuine smooth sphere-valued
ambient extension near every negative-unit Hodge form. At the sphere locus
it equals the original coefficient, and no smooth structure is transported
from the twistor total space. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientSphereSmooth

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeCoefficientRadialSmooth
open ManifoldQuaternionicFourNativeNegativeSphereSet
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorRadialRetraction
open ManifoldTwistorSphereBundle
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
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) :=
  ⟨by simp [EuclideanThree]⟩

def nativeCoefficientSphereExtension (i : atlas E M)
    (p : M × (E [⋀^Fin 2]→L[ℝ] ℝ)) : geometricSphere :=
  if h : nativeCoefficientEuclidean Q hdim i p ≠ 0 then
    radial ⟨nativeCoefficientEuclidean Q hdim i p,h⟩
  else radial (Classical.choice nonzeroNonempty)

theorem nativeCoefficientSphereExtension_smoothAt (i : atlas E M)
    (x : M) (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ)
    (hα : α ∈ nativeLocalSphereSet Q i x) :
    ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E [⋀^Fin 2]→L[ℝ] ℝ))
      (𝓡 2) ∞
      (nativeCoefficientSphereExtension Q hdim i) (x,α) := by
  let J := 𝓘(ℝ,E).prod 𝓘(ℝ,E [⋀^Fin 2]→L[ℝ] ℝ)
  have hne := nativeCoefficientEuclidean_nonzero Q hdim i x hi α hα
  have hambient : ContMDiffAt J 𝓘(ℝ,EuclideanThree) ∞
      (nativeCoefficientRadial Q hdim i) (x,α) :=
    nativeCoefficientRadial_smoothAt_sphere Q hdim i x hi α hα
  have hcont : ContinuousAt (nativeCoefficientEuclidean Q hdim i) (x,α) :=
    (((nativeCoefficientEuclidean_smooth Q hdim i).continuousOn).continuousAt
      (((Q.frames.adaptedCore.isOpen_baseSet i).prod isOpen_univ).mem_nhds
        ⟨hi,Set.mem_univ _⟩))
  have hevent : ∀ᶠ p in 𝓝 (x,α),
      nativeCoefficientEuclidean Q hdim i p ≠ 0 :=
    hcont.eventually_ne hne
  have hEq : (fun p => (nativeCoefficientSphereExtension Q hdim i p : EuclideanThree))
      =ᶠ[𝓝 (x,α)] nativeCoefficientRadial Q hdim i := by
    filter_upwards [hevent] with p hp
    simp [nativeCoefficientSphereExtension, hp,
      ManifoldTwistorRadialRetraction.radial,
      nativeCoefficientRadial]
  have hcod : ContMDiffAt J (𝓡 2) ∞
      (Set.codRestrict
        (fun p => (nativeCoefficientSphereExtension Q hdim i p : EuclideanThree))
        (Metric.sphere (0 : EuclideanThree) 1)
        (fun p => (nativeCoefficientSphereExtension Q hdim i p).2))
      (x,α) :=
    ManifoldQuaternionicSphereSmoothAt.contMDiffAt_codRestrict_sphere
      (hambient.congr_of_eventuallyEq hEq) _
  exact hcod.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl))

theorem nativeCoefficientSphereExtension_on_sphere (i : atlas E M)
    (x : M) (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a : coefficientSphere) :
    nativeCoefficientSphereExtension Q hdim i
      (x,ManifoldQuaternionicFourNativeSphereFormSmooth.nativeSphereForm Q i
        (x,coefficientSphereHomeomorph a)) =
      coefficientSphereHomeomorph a := by
  have hraw := ManifoldQuaternionicFourNativeCoefficientExtraction.nativeCoefficientRaw_map
    Q hdim i x hi (coefficientSphereHomeomorph a)
  have hnonzero := nativeCoefficientEuclidean_nonzero Q hdim i x hi _
    (show _ ∈ nativeLocalSphereSet Q i x from ⟨a,rfl⟩)
  simp only [nativeCoefficientSphereExtension, dif_pos hnonzero]
  apply Subtype.ext
  change (‖nativeCoefficientEuclidean Q hdim i
    (x,ManifoldQuaternionicFourNativeSphereFormSmooth.nativeSphereForm Q i
      (x,coefficientSphereHomeomorph a))‖)⁻¹ •
      nativeCoefficientEuclidean Q hdim i
        (x,ManifoldQuaternionicFourNativeSphereFormSmooth.nativeSphereForm Q i
          (x,coefficientSphereHomeomorph a)) =
      (coefficientSphereHomeomorph a).1
  simp only [nativeCoefficientEuclidean, hraw]
  have hcoe : toEuclidean
      ((EuclideanSpace.equiv (Fin 3) ℝ)
        (coefficientSphereHomeomorph a).1) =
      (coefficientSphereHomeomorph a).1 := by
    exact (EuclideanSpace.equiv (Fin 3) ℝ).symm_apply_apply _
  rw [hcoe]
  have hn : ‖(coefficientSphereHomeomorph a : EuclideanThree)‖ = 1 :=
    (mem_sphere_zero_iff_norm).mp (coefficientSphereHomeomorph a).2
  simp [hn]

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientSphereSmooth
