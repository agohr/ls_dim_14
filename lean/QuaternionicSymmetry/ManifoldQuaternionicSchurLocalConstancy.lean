import QuaternionicSymmetry.ManifoldQuaternionicSchurPointwise

/-! The pointwise Schur contraction annihilates the full Fréchet derivative,
since the adapted vectors are an actual basis of each chart tangent space. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicSchurLocalConstancy
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicSchurTensor
open ManifoldQuaternionicSchurPointwise
open ManifoldQuaternionicEinsteinFactor
open ManifoldQuaternionicKSWEq38Input
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem einsteinFactor_fderiv_eq_zero
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (c : E) (hc : c ≠ 0) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (hcard : 3 ≤ Module.finrank ℝ E) :
    fderiv ℝ (einsteinFactor Q D p c) y = 0 := by
  let e := solderEquiv Q p y hy
  let L := fderiv ℝ (einsteinFactor Q D p c) y
  have hcomp : (L.comp e.symm.toContinuousLinearMap).toLinearMap = 0 := by
    apply (stdOrthonormalBasis ℝ E).toBasis.ext
    intro i
    change L (e.symm (stdOrthonormalBasis ℝ E i)) = 0
    exact einsteinFactor_fderiv_basis_zero Q D S hdecomp p c hc y hy hcard i
  ext u
  have h := congrArg (fun A : E →ₗ[ℝ] ℝ => A (e u)) hcomp
  change L (e.symm (e u)) = 0 at h
  simpa only [ContinuousLinearEquiv.symm_apply_apply, L] using h

end
end QuaternionicSymmetry.ManifoldQuaternionicSchurLocalConstancy
