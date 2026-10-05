import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartCore

/-! The actual fixed-projective-chart composition has the same germ,
hence the same true manifold derivative, as the literal bundle-core
transition. This closes the core-versus-total-chart expression gap. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartMFDeriv

open scoped Quaternion Manifold ContDiff Topology
open FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem fixedProjectiveChart_transition_eventuallyEq
    (p q : M) (i j : Fin 2) (y : ℍ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q) (z : ℂ) :
    (fun t : ℍ × ℂ => fixedProjectiveChart Q q j
      (fixedProjectiveChartInv Q p i t)) =ᶠ[𝓝 (y,z)]
        indexedCoreTransition Q i j p q := by
  have hopen : IsOpen
      (chartOverlap (I := 𝓘(ℝ, ℍ)) p q ×ˢ Set.univ : Set (ℍ × ℂ)) :=
    (chartOverlap_isOpen p q).prod isOpen_univ
  have hmem : (y,z) ∈
      (chartOverlap (I := 𝓘(ℝ, ℍ)) p q ×ˢ Set.univ : Set (ℍ × ℂ)) :=
    ⟨hy, Set.mem_univ _⟩
  filter_upwards [hopen.mem_nhds hmem] with t ht
  exact fixedProjectiveChart_transition Q p q i j t.1 ht.1 t.2

theorem fixedProjectiveChart_transition_mfderiv
    (p q : M) (i j : Fin 2) (y : ℍ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q) (z : ℂ) :
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ)
      (fun t : ℍ × ℂ => fixedProjectiveChart Q q j
        (fixedProjectiveChartInv Q p i t)) (y,z) =
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ)
      (indexedCoreTransition Q i j p q) (y,z) :=
  (fixedProjectiveChart_transition_eventuallyEq Q p q i j y hy z).mfderiv_eq

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartMFDeriv
