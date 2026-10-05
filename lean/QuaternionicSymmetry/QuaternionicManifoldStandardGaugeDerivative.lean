import QuaternionicSymmetry.QuaternionicManifoldStandardGaugeEquivariance
import QuaternionicSymmetry.QuaternionicManifoldProductGaugeInverse

/-! The derivative term in the actual locally lifted standard connection
overlap is the image of the fixed tangent derivative term. -/

namespace QuaternionicSymmetry.QuaternionicManifoldStandardGaugeDerivative

open scoped Manifold ContDiff Quaternion Topology
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldProductGaugeIdentity
open QuaternionicManifoldProductGaugeInverse
open QuaternionicManifoldFixedConnectionOverlap
open QuaternionicManifoldLocalStandardMaurer
open QuaternionicManifoldStandardMaurerIdentity
open QuaternionicProjectiveProductMaurer
open QuaternionicProjectiveStandardLie
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

theorem standardLie_fixedGauge_derivative (p q : M) (lift : unitary ℍ)
    (y u : E) (hy : y ∈ ManifoldQuaternionicConnection.chartOverlap
      (I := 𝓘(ℝ, E)) p q)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    standardLie S (fixedGaugeInv S Q p q y *
      fderiv ℝ (fixedGauge S Q p q) y u) =
      standardChartInverse S Q p (achart E p) (achart E q) lift y *
        fderiv ℝ (standardChart S Q p (achart E p) (achart E q) lift) y u := by
  let r := scalarChart Q p (achart E p) (achart E q) lift
  let h := kernelChart S Q p (achart E p) (achart E q) lift
  have hneigh : ∀ᶠ z in 𝓝 y,
      (extChartAt 𝓘(ℝ, E) p).symm z ∈
        liftNeighborhood Q (achart E p) (achart E q) lift :=
    (continuousAt_extChartAt_symm'' hy.1).preimage_mem_nhds
      ((isOpen_liftNeighborhood Q _ _ lift).mem_nhds hx)
  have hevent : fixedGauge S Q p q =ᶠ[𝓝 y] productGauge S r h := by
    filter_upwards [hneigh] with z hz
    exact fixedGauge_eq_product S Q p q lift z hz
  have hderiv : fderiv ℝ (fixedGauge S Q p q) y u =
      fderiv ℝ (productGauge S r h) y u :=
    congrArg (fun F : E →L[ℝ] (E →L[ℝ] E) => F u) hevent.fderiv_eq
  rw [fixedGaugeInv_eq_productInverse S Q p q lift y hy hx, hderiv]
  exact standard_maurer_identity S Q p (achart E p) (achart E q) lift y u hy.1 hx

end
end QuaternionicSymmetry.QuaternionicManifoldStandardGaugeDerivative
