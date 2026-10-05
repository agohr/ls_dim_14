import QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointConnection

/-! Smoothness of the local commutator connection on the standard endomorphism bundle. -/
namespace QuaternionicSymmetry.QuaternionicManifoldAdjointConnectionSmooth
open QuaternionicProjectiveStandardL2 QuaternionicProjectiveStandardAdjoint
  QuaternionicManifoldProjectiveAdjointConnection QuaternionicManifoldProjectiveSmooth
  ManifoldQuaternionicConnection
open scoped ContDiff Manifold
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ (StandardEnd (E := E)) := inferInstance
local instance : NormedAddCommGroup
    (StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) := inferInstance
local instance : NormedSpace ℝ (StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) := inferInstance
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

theorem adjointConnection_smooth (p : M) :
    ContDiffOn ℝ ∞ (adjointConnection S Q D p) (extChartAt 𝓘(ℝ, E) p).target := by
  exact contDiffOn_const.clm_comp (standardConnection_smooth S Q D p)

end
end QuaternionicSymmetry.QuaternionicManifoldAdjointConnectionSmooth
