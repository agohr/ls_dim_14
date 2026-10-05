import QuaternionicSymmetry.ManifoldTwistorProjectiveBasisCoordinates
import QuaternionicSymmetry.ManifoldTwistorSectionComparison
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! Holomorphicity of actual finite-basis evaluation coefficients in genuine
holomorphic line-bundle charts. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveHolomorphicCoefficients

open ManifoldTwistorProjectiveBasisCoordinates
open ManifoldTwistorProjectiveEvaluation
open ManifoldTwistorLinearSystem
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicMetric ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A) (r : ℤ)

/-- Every actual holomorphic global section has a holomorphic scalar
coefficient in each genuine line-bundle chart. -/
theorem contMDiffOn_chartEvaluation (i : L.Index)
    (s : GlobalSections Q D L r) :
    letI := A.charts
    ContMDiffOn 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ℂ) ∞
      (fun x : SphereBundleTotal Q => chartEvaluation Q D L r i x s)
      ((L.integerTwistCore Q D r).baseSet i) := by
  letI := A.charts
  letI := L.integerTwistCore_holomorphic Q D r
  let Z := L.integerTwistCore Q D r
  letI (j : L.Index) : MemTrivializationAtlas (Z.localTriv j) := ⟨⟨j, rfl⟩⟩
  let t := globalCoefficientSectionsEquiv Q D L r s
  have htotal : ContMDiff 𝓘(ℂ, ComplexTwistorModel n)
      (𝓘(ℂ, ComplexTwistorModel n).prod 𝓘(ℂ,ℂ)) ∞
      (fun x : SphereBundleTotal Q =>
        (⟨x, s.1 ⟨x, Set.mem_univ x⟩⟩ : Bundle.TotalSpace ℂ Z.Fiber)) :=
    t.contMDiff
  intro x hx
  have hsource : (⟨x, s.1 ⟨x, Set.mem_univ x⟩⟩ : Bundle.TotalSpace ℂ Z.Fiber) ∈
      (Z.localTriv i).source := (Z.mem_localTriv_source i _).mpr hx
  have h := ((Z.localTriv i).contMDiffAt_iff
    (f := fun z : SphereBundleTotal Q =>
      (⟨z, s.1 ⟨z, Set.mem_univ z⟩⟩ : Bundle.TotalSpace ℂ Z.Fiber)) hsource).mp
      (htotal x)
  exact h.2.contMDiffWithinAt

variable (d : ℕ)
  (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections Q D L r))

/-- The full vector of basis coefficients is holomorphic on each actual
line-bundle chart. -/
theorem contMDiffOn_basisChartEvaluation (i : L.Index) :
    letI := A.charts
    ContMDiffOn 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, Fin (d + 1) → ℂ) ∞
      (basisChartEvaluation Q D L r d b i)
      ((L.integerTwistCore Q D r).baseSet i) := by
  letI := A.charts
  apply contMDiffOn_pi_space.mpr
  intro k
  exact contMDiffOn_chartEvaluation Q D L r i (b k)

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveHolomorphicCoefficients
