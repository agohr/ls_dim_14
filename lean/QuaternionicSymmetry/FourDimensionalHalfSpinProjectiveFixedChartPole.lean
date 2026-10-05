import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartGerm

/-! The north and south coordinate poles have unique affine projective
charts. This turns every fixed base/affine chart into a genuine selected
total-space chart centered at an appropriate pole over its base point. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartPole

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveAllCoreChartDomain
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjective
  ComplexProjectiveTopology

noncomputable section

def coordinatePole (i : Fin 2) : ProjectiveSpinor :=
  indexedSourcePoint i 0

theorem coordinatePole_mem_iff (i j : Fin 2) :
    coordinatePole i ∈ affineDomain 1 j ↔ i = j := by
  rw [coordinatePole, indexedSourcePoint_mk,
    mem_affineDomain_mk]
  fin_cases i <;> fin_cases j <;>
    simp [indexedSourceVector]

theorem preferredIndex_coordinatePole (i : Fin 2) :
    preferredProjectiveChartIndex (coordinatePole i) = i := by
  have h := preferredProjectiveChartIndex_mem (coordinatePole i)
  exact (coordinatePole_mem_iff i _).mp h |>.symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def chartPole (p : M) (i : Fin 2) : SpinorBundleTotal Q :=
  ⟨p, coordinatePole i⟩

theorem chartPole_base (p : M) (i : Fin 2) :
    (chartPole Q p i).1 = p := rfl

theorem chartPole_preferredIndex (p : M) (i : Fin 2) :
    preferredProjectiveChartIndex (chartPole Q p i).2 = i :=
  preferredIndex_coordinatePole i

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartPole
