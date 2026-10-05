import QuaternionicSymmetry.HolomorphicLineHermitianMetric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! A Hermitian metric on an actual positive tensor power has a unique
positive local `k`-th root. The cocycle law, smoothness, and curvature
positivity descend without assuming a preexisting metric on the root line.
This is the internal positive-root step needed after a separate gauge
comparison with an anticanonical metric. -/

namespace QuaternionicSymmetry.HolomorphicLineHermitianPositiveRoot

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLinePowers
open QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
open QuaternionicSymmetry.HolomorphicLineHermitianMetric
open scoped Manifold ContDiff Topology
noncomputable section
universe uB uF uI

variable {B : Type uB} {F : Type uF}
  [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace F B]
  (L : LineCore.{uI} (B := B) 𝓘(ℂ,F))

/-- The positive real kth root of each local frame squared norm. -/
def rootMetric (k : ℕ) (hk : 0 < k)
    (p : HermitianLineMetric (powerCoreRep 𝓘(ℂ,F) L k)) :
    HermitianLineMetric L where
  frameNormSq i x := (p.frameNormSq i x) ^ ((k : ℝ)⁻¹)
  positive i x hx := Real.rpow_pos_of_pos (p.positive i x hx) _
  smooth i := by
    intro x hx
    have hp := p.smooth i x hx
    have hpne : p.frameNormSq i x ≠ 0 := ne_of_gt (p.positive i x hx)
    have hr := (Real.contDiffAt_rpow_const_of_ne
      (n := ∞) (p := ((k : ℝ)⁻¹)) hpne).contMDiffAt
    exact hr.comp_contMDiffWithinAt x hp
  overlap i j x hx := by
    have h := p.overlap i j x hx
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    change (p.frameNormSq i x) ^ ((k : ℝ)⁻¹) =
      Complex.normSq (transitionScalar L.core i j x) *
        (p.frameNormSq j x) ^ ((k : ℝ)⁻¹)
    rw [h]
    have hpower :
        transitionScalar (powerCoreRep 𝓘(ℂ,F) L k).core i j x =
          (transitionScalar L.core i j x)^k := by
      change (((transitionScalar L.core i j x)^k •
        ContinuousLinearMap.id ℂ ℂ) 1) = _
      simp
    rw [hpower, HermitianLineMetric.normSq_pow]
    rw [Real.mul_rpow (pow_nonneg (Complex.normSq_nonneg _) k)
      (le_of_lt (p.positive j x hx.2))]
    rw [Real.pow_rpow_inv_natCast (Complex.normSq_nonneg _) hk0]

/-- Taking a positive local root and powering back recovers every local
frame norm of the original power metric. -/
theorem powerMetric_rootMetric_frameNormSq (k : ℕ) (hk : 0 < k)
    (p : HermitianLineMetric (powerCoreRep 𝓘(ℂ,F) L k))
    (i : L.Index) (x : B) (hx : x ∈ L.core.baseSet i) :
    ((rootMetric L k hk p).powerMetric L k).frameNormSq i x =
      p.frameNormSq i x := by
  change ((p.frameNormSq i x) ^ ((k : ℝ)⁻¹)) ^ k = _
  exact Real.rpow_inv_natCast_pow
    (le_of_lt (p.positive i x hx)) (Nat.ne_of_gt hk)

/-- At every point of a line chart, the positive root metric has exactly
the same second Chern-potential derivative as the supplied power metric.
The frame weights need only agree on their open chart; outside it a local
frame has no geometric meaning. -/
theorem powerMetric_rootMetric_hessian (k : ℕ) (hk : 0 < k)
    (p : HermitianLineMetric (powerCoreRep 𝓘(ℂ,F) L k))
    (i : L.Index) (x : B) (hx : x ∈ L.core.baseSet i) :
    fderiv ℝ (fderiv ℝ
      (HermitianLineMetric.localChernPotential
        (powerCoreRep 𝓘(ℂ,F) L k)
        ((rootMetric L k hk p).powerMetric L k) i x))
        ((chartAt F x) x) =
    fderiv ℝ (fderiv ℝ
      (HermitianLineMetric.localChernPotential
        (powerCoreRep 𝓘(ℂ,F) L k) p i x))
        ((chartAt F x) x) := by
  let z := (chartAt F x) x
  have hz : z ∈ (chartAt F x).target := by
    dsimp [z]
    exact mem_chart_target F x
  have hzsymm : (chartAt F x).symm z = x := by
    dsimp [z]
    exact (chartAt F x).left_inv (mem_chart_source F x)
  have hnear : ∀ᶠ w in 𝓝 z,
      (chartAt F x).symm w ∈ L.core.baseSet i := by
    apply ((chartAt F x).continuousAt_symm hz).preimage_mem_nhds
    rw [hzsymm]
    exact (L.core.isOpen_baseSet i).mem_nhds hx
  have heq :
      HermitianLineMetric.localChernPotential
        (powerCoreRep 𝓘(ℂ,F) L k)
        ((rootMetric L k hk p).powerMetric L k) i x =ᶠ[𝓝 z]
      HermitianLineMetric.localChernPotential
        (powerCoreRep 𝓘(ℂ,F) L k) p i x := by
    filter_upwards [hnear] with w hw
    simp only [HermitianLineMetric.localChernPotential]
    rw [powerMetric_rootMetric_frameNormSq L k hk p i _ hw]
  exact (heq.fderiv (𝕜 := ℝ)).fderiv_eq

/-- Arbitrary strictly positive Hermitian curvature on the *actual*
`k`-th power produces strictly positive curvature on `L` itself. -/
theorem rootMetric_positive (k : ℕ) (hk : 0 < k)
    (p : HermitianLineMetric (powerCoreRep 𝓘(ℂ,F) L k))
    (hp : p.PositiveChernCurvature (powerCoreRep 𝓘(ℂ,F) L k)) :
    (rootMetric L k hk p).PositiveChernCurvature L := by
  apply HermitianLineMetric.positive_of_powerMetric_positive L
    (rootMetric L k hk p) k hk
  intro i x hx v hv
  have hp' := hp i x hx v hv
  dsimp [HermitianLineMetric.PositiveChernCurvature] at hp' ⊢
  rw [powerMetric_rootMetric_hessian L k hk p i x hx]
  exact hp'

end
end QuaternionicSymmetry.HolomorphicLineHermitianPositiveRoot
