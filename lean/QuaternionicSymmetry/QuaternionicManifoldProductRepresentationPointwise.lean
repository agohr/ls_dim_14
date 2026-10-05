import QuaternionicSymmetry.QuaternionicManifoldStandardMaurerIdentity
import QuaternionicSymmetry.QuaternionicManifoldProductGaugeInverse
import QuaternionicSymmetry.QuaternionicProjectiveProductEquivariance

/-! The chart-local operator formulas equal the genuine product group
representation at each point of the refined overlap. -/

namespace QuaternionicSymmetry.QuaternionicManifoldProductRepresentationPointwise

open scoped Manifold ContDiff Quaternion
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldSmoothProductLifts
open QuaternionicManifoldSignedLocalLifts
open QuaternionicManifoldFixedConnectionOverlap
open QuaternionicManifoldStandardMaurerIdentity
open QuaternionicProjectiveStandardL2
open QuaternionicUnitScalarIsometries
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

theorem fixedGauge_eq_localProductLift (p q : M) (lift : unitary ℍ)
    (y : E)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    fixedGauge S Q p q y =
      ((symplecticProductAction S
        (localProductLift S Q (achart E p) (achart E q) lift
          ((extChartAt 𝓘(ℝ, E) p).symm y) hx)).1.1.toContinuousLinearMap) := by
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  rw [fixedGauge_eq_transition,
    fixedTransitionCLM_eq S Q _ _ x hx.1.1 hx.1.2,
    localProductLift_image S Q _ _ lift x hx]
  rfl

theorem fixedGaugeInv_eq_localProductLift (p q : M) (lift : unitary ℍ)
    (y : E)
    (hy : y ∈ ManifoldQuaternionicConnection.chartOverlap
      (I := 𝓘(ℝ, E)) p q)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    fixedGaugeInv S Q p q y =
      ((symplecticProductAction S
        (localProductLift S Q (achart E p) (achart E q) lift
          ((extChartAt 𝓘(ℝ, E) p).symm y) hx)).1.1.symm.toContinuousLinearMap) := by
  let t := localProductLift S Q (achart E p) (achart E q) lift
    ((extChartAt 𝓘(ℝ, E) p).symm y) hx
  let g := (symplecticProductAction S t).1.1
  have hg := fixedGauge_eq_localProductLift S Q p q lift y hx
  have hleft := (fixedGauge_inverse S Q p q y hy).1
  have hright : g.toContinuousLinearMap * g.symm.toContinuousLinearMap = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    exact g.apply_symm_apply v
  calc
    fixedGaugeInv S Q p q y =
      fixedGaugeInv S Q p q y *
        (g.toContinuousLinearMap * g.symm.toContinuousLinearMap) := by rw [hright, mul_one]
    _ = (fixedGaugeInv S Q p q y * fixedGauge S Q p q y) *
        g.symm.toContinuousLinearMap := by rw [hg, mul_assoc]
    _ = g.symm.toContinuousLinearMap := by rw [hleft, one_mul]

theorem standardChart_eq_localProductLift (p q : M) (lift : unitary ℍ)
    (y : E)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    standardChart S Q p (achart E p) (achart E q) lift y =
      (standardActionL2 S
        (localProductLift S Q (achart E p) (achart E q) lift
          ((extChartAt 𝓘(ℝ, E) p).symm y) hx)).toContinuousLinearMap := by
  exact QuaternionicManifoldStandardLocalOperator.localStandardOperator_eq
    S Q _ _ lift _ hx

theorem standardChartInverse_mul_standardChart (p q : M) (lift : unitary ℍ)
    (y : E)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    standardChartInverse S Q p (achart E p) (achart E q) lift y *
      standardChart S Q p (achart E p) (achart E q) lift y = 1 := by
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  have hh := (QuaternionicManifoldKernelOperatorProperties.symplecticFactor_adjoint_inverse
    S Q (achart E p) (achart E q) lift x hx).1
  have hq : Quaternion.normSq (scalarLiftRaw Q (achart E p) (achart E q) lift x) = 1 :=
    (scalarLiftRaw_valid Q S _ _ lift x hx).1
  have hq₁ : star (scalarLiftRaw Q (achart E p) (achart E q) lift x) *
      scalarLiftRaw Q (achart E p) (achart E q) lift x = 1 := by
    rw [Quaternion.star_mul_self, hq]
    rfl
  have hq₂ : scalarLiftRaw Q (achart E p) (achart E q) lift x *
      star (scalarLiftRaw Q (achart E p) (achart E q) lift x) = 1 := by
    rw [Quaternion.self_mul_star, hq]
    rfl
  have hr := (QuaternionicProjectiveLineMaurer.rightStar_inverse _ hq₁ hq₂).1
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  rw [standardChart_eq_block]
  apply Prod.ext
  · change ((symplecticFactorOperator S Q (achart E p) (achart E q) lift x).adjoint *
        symplecticFactorOperator S Q (achart E p) (achart E q) lift x) z.fst = z.fst
    rw [hh]
    rfl
  · change (QuaternionicProjectiveLineMaurer.rightStar
        (star (scalarLiftRaw Q (achart E p) (achart E q) lift x)) *
          QuaternionicProjectiveLineMaurer.rightStar
            (scalarLiftRaw Q (achart E p) (achart E q) lift x)) z.snd = z.snd
    rw [hr]
    rfl

theorem standardChartInverse_eq_localProductLift (p q : M) (lift : unitary ℍ)
    (y : E)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    standardChartInverse S Q p (achart E p) (achart E q) lift y =
      (standardActionL2 S
        (localProductLift S Q (achart E p) (achart E q) lift
          ((extChartAt 𝓘(ℝ, E) p).symm y) hx)).symm.toContinuousLinearMap := by
  let t := localProductLift S Q (achart E p) (achart E q) lift
    ((extChartAt 𝓘(ℝ, E) p).symm y) hx
  have hG := standardChart_eq_localProductLift S Q p q lift y hx
  have hleft := standardChartInverse_mul_standardChart S Q p q lift y hx
  have hright : (standardActionL2 S t).toContinuousLinearMap *
      (standardActionL2 S t).symm.toContinuousLinearMap = 1 := by
    apply ContinuousLinearMap.ext
    intro z
    exact (standardActionL2 S t).apply_symm_apply z
  calc
    standardChartInverse S Q p (achart E p) (achart E q) lift y =
      standardChartInverse S Q p (achart E p) (achart E q) lift y *
        ((standardActionL2 S t).toContinuousLinearMap *
          (standardActionL2 S t).symm.toContinuousLinearMap) := by rw [hright, mul_one]
    _ = (standardChartInverse S Q p (achart E p) (achart E q) lift y *
        standardChart S Q p (achart E p) (achart E q) lift y) *
          (standardActionL2 S t).symm.toContinuousLinearMap := by rw [hG, mul_assoc]
    _ = (standardActionL2 S t).symm.toContinuousLinearMap := by rw [hleft, one_mul]

end
end QuaternionicSymmetry.QuaternionicManifoldProductRepresentationPointwise
