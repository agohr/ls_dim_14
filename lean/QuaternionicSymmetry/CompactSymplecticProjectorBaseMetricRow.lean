import QuaternionicSymmetry.CompactSymplecticProjectorBaseTangentRange
import QuaternionicSymmetry.CompactSymplecticProjectorBlockFrobenius
import QuaternionicSymmetry.CompactSymplecticProjectorRiemannianMetric
import QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionic

/-! The actual projector-immersion metric at the base quotient point is
four times the standard squared norm of its unrestricted quaternionic row. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseMetricRow

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseTangentRange
open CompactSymplecticProjectorQuaternionicBlock
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticProjectorRiemannianMetric
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorBlockFrobenius
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 1000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

theorem actual_base_frobenius_self_row
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      frobeniusPairing n
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
          (quotientOrbitProjector n) (baseCoset n) v)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
          (quotientOrbitProjector n) (baseCoset n) v) =
        4 * ∑ c : Fin n ⊕ Fin n,
          Complex.normSq ((baseTangentUpperLinear hDesc n d e q g a v).1 0 c) := by
  letI := a.quotientCharts
  intro v
  let X : Mat n := mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
    (quotientOrbitProjector n) (baseCoset n) v
  let B : Matrix (Fin 2) (Fin n ⊕ Fin n) ℂ := (baseBlockMatrix n X).toBlocks₁₂
  have hBlock : baseBlockMatrix n X = offDiagonal B := by
    exact base_tangent_eq_offDiagonal hDesc n d e q g a v
  have hB : B * CompactSymplecticHaar.standardJ n =
      CompactSymplecticStabilizerFormBlocks.firstBlockJ * B.map star :=
    base_tangent_upper_quaternionic hDesc n d e q g a v
  calc
    frobeniusPairing n X X =
        ∑ i : I n, ∑ j : I n, Complex.normSq (X i j) :=
      frobeniusPairing_self_eq_sum_normSq n X
    _ = ∑ i : Fin 2 ⊕ (Fin n ⊕ Fin n),
          ∑ j : Fin 2 ⊕ (Fin n ⊕ Fin n),
            Complex.normSq ((baseBlockMatrix n X) i j) := by
      exact (sum_normSq_reindex (CompactSymplecticStabilizerIndex.blockIndexEquiv n) X).symm
    _ = 4 * ∑ c : Fin n ⊕ Fin n, Complex.normSq (B 0 c) := by
      rw [hBlock]
      exact quaternionicUpper_full_sum_normSq n B hB
    _ = _ := rfl

theorem actual_base_metric_self_row
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n) v v =
        4 * ∑ c : Fin n ⊕ Fin n,
          Complex.normSq ((baseTangentUpperLinear hDesc n d e q g a v).1 0 c) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v
  rw [smoothProjectorMetric_apply hDesc hImm n d e q g a (baseCoset n) v v]
  exact actual_base_frobenius_self_row hDesc n d e q g a v

theorem baseTangentEuclideanEquiv_normSq
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      ‖baseTangentEuclideanEquiv hDesc hImm n d e q g a hq v‖ ^ 2 =
        ∑ c : Fin n ⊕ Fin n,
          Complex.normSq ((baseTangentUpperLinear hDesc n d e q g a v).1 0 c) := by
  letI := a.quotientCharts
  intro v
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Complex.normSq_eq_norm_sq]
  rfl

theorem actual_base_metric_self_euclidean
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n) v v =
        4 * ‖baseTangentEuclideanEquiv hDesc hImm n d e q g a hq v‖ ^ 2 := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v
  rw [actual_base_metric_self_row hDesc hImm n d e q g a v]
  rw [baseTangentEuclideanEquiv_normSq hDesc hImm n d e q g a hq v]

theorem actual_base_metric_euclidean
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ v w : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n) v w =
        4 * inner ℝ
          (baseTangentEuclideanEquiv hDesc hImm n d e q g a hq v)
          (baseTangentEuclideanEquiv hDesc hImm n d e q g a hq w) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v w
  let G := (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n)
  let T := baseTangentEuclideanEquiv hDesc hImm n d e q g a hq
  have hsym : G w v = G v w := by
    dsimp [G]
    rw [smoothProjectorMetric_apply hDesc hImm n d e q g a (baseCoset n),
      smoothProjectorMetric_apply hDesc hImm n d e q g a (baseCoset n)]
    exact frobeniusCLM_symm n _ _
  have hv := actual_base_metric_self_euclidean hDesc hImm n d e q g a hq v
  have hw := actual_base_metric_self_euclidean hDesc hImm n d e q g a hq w
  have hsum := actual_base_metric_self_euclidean hDesc hImm n d e q g a hq (v + w)
  change G v v = 4 * ‖T v‖ ^ 2 at hv
  change G w w = 4 * ‖T w‖ ^ 2 at hw
  change G (v + w) (v + w) = 4 * ‖T (v + w)‖ ^ 2 at hsum
  simp only [map_add, ContinuousLinearMap.add_apply] at hsum
  rw [norm_add_sq_real] at hsum
  rw [hsym] at hsum
  change G v w = 4 * inner ℝ (T v) (T w)
  linarith [real_inner_comm (T v) (T w)]

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseMetricRow
