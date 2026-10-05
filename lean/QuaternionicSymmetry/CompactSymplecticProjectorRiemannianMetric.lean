import QuaternionicSymmetry.CompactSymplecticProjectorSmoothAction
import QuaternionicSymmetry.ManifoldImmersionPullbackMetric
import QuaternionicSymmetry.FinitePositiveBilinearBounded
import QuaternionicSymmetry.CompactSymplecticProjectiveCarrierDimension

/-! The genuine smooth invariant Riemannian metric on the selected Lee
quotient atlas of the rank-two quaternionic projector orbit. It is the
derivative pullback of the actual ambient Frobenius pairing. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorRiemannianMetric

open Manifold Bundle
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticProjectorSmoothAction
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticProjectiveCarrierDimension
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- The actual smooth Riemannian metric on the projector quotient, obtained
from its injective smooth matrix-orbit immersion and Hilbert--Schmidt form.
The only external premises are the two general Lee differential theorems. -/
def smoothProjectorMetric
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, RModel q) ∞ (RModel q)
      (TangentSpace 𝓘(ℝ, RModel q) : ProjectiveCarrier n → Type _) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  exact ManifoldImmersionPullbackMetric.smoothMetric
    (E := RModel q) (quotientOrbitProjector n) (frobeniusCLM n)
    (smooth_quotientOrbitProjector_actual hDesc n d e q g a)
    (quotientOrbitProjector_mfderiv_injective hDesc hImm n d e q g a)
    (frobeniusCLM_symm n) (frobeniusCLM_pos n)
    (FinitePositiveBilinearBounded.unitBall_isVonNBounded
      (frobeniusCLM n) (frobeniusCLM_pos n))

/-- The chosen smooth metric is pointwise the literal pullback of the
ambient trace pairing along the true manifold derivative. -/
theorem smoothProjectorMetric_apply
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ (v w : TangentSpace 𝓘(ℝ, RModel q) x),
      (smoothProjectorMetric hDesc hImm n d e q g a).inner x v w =
        frobeniusCLM n
          (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
            (quotientOrbitProjector n) x v)
          (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
            (quotientOrbitProjector n) x w) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v w
  exact ManifoldImmersionPullbackMetric.metricCLM_apply
    (E := RModel q) (quotientOrbitProjector n) (frobeniusCLM n) x v w

/-- Every actual compact symplectic left translation preserves the
constructed smooth Riemannian metric on the quotient. -/
theorem smoothProjectorMetric_invariant
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (u : G n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ (v w : TangentSpace 𝓘(ℝ, RModel q) x),
      (smoothProjectorMetric hDesc hImm n d e q g a).inner
        (leftCosetAction n u x)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n u) x v)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n u) x w) =
      (smoothProjectorMetric hDesc hImm n d e q g a).inner x v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v w
  rw [smoothProjectorMetric_apply hDesc hImm n d e q g a
      (leftCosetAction n u x),
    smoothProjectorMetric_apply hDesc hImm n d e q g a x]
  exact projector_pullback_pairing_invariant hDesc n d e q g a u x v w

/-- Concrete selected atlas data for the first projector model. Its metric
is obtained by `FirstProjectorModel.metric` below, not stored as a premise. -/
structure FirstProjectorModel (m : ℕ) where
  d : ℕ
  e : ℕ
  q : ℕ
  groupAtlas : EmbeddedRealLieAtlas (m + 1) d
  quotientAtlas : SmoothHomogeneousAtlas (m + 1) d e q groupAtlas
  realDimension : q = 4 * (m + 1)

/-- The model's actual smooth invariant metric, selected canonically from
its Lee quotient atlas and the ambient matrix projector immersion. -/
def FirstProjectorModel.metric (m : ℕ)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (M : FirstProjectorModel m) :
    letI := M.quotientAtlas.quotientCharts
    letI := M.quotientAtlas.quotientManifold
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, RModel M.q) ∞ (RModel M.q)
      (TangentSpace 𝓘(ℝ, RModel M.q) : ProjectiveCarrier (m + 1) → Type _) :=
  smoothProjectorMetric hDesc hImm (m + 1) M.d M.e M.q
    M.groupAtlas M.quotientAtlas

/-- The source-constructed model metric is invariant under every actual
left translation on the concrete projector quotient. -/
theorem FirstProjectorModel.metric_invariant (m : ℕ)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (M : FirstProjectorModel m)
    (u : G (m + 1)) (x : ProjectiveCarrier (m + 1)) :
    letI := M.quotientAtlas.quotientCharts
    letI := M.quotientAtlas.quotientManifold
    ∀ (v w : TangentSpace 𝓘(ℝ, RModel M.q) x),
      (FirstProjectorModel.metric m hDesc hImm M).inner (leftCosetAction (m + 1) u x)
        (mfderiv 𝓘(ℝ, RModel M.q) 𝓘(ℝ, RModel M.q)
          (leftCosetAction (m + 1) u) x v)
        (mfderiv 𝓘(ℝ, RModel M.q) 𝓘(ℝ, RModel M.q)
          (leftCosetAction (m + 1) u) x w) =
      (FirstProjectorModel.metric m hDesc hImm M).inner x v w := by
  letI := M.quotientAtlas.quotientCharts
  letI := M.quotientAtlas.quotientManifold
  exact smoothProjectorMetric_invariant hDesc hImm
    (m + 1) M.d M.e M.q M.groupAtlas M.quotientAtlas u x

/-- The first real Riemannian projector model exists solely from the
registered general Lee and Knapp dimension sources, plus the general
submersion/equivariant immersion theorems used by its defined metric. -/
theorem exists_firstProjectorModel
    (hClosed : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem)
    (hQuot : GeneralLieHomogeneousSpaceSource.LeeHomogeneousSpaceTheorem)
    (hKnapp : CompactSymplecticKnappDimensionSource.KnappCompactSymplecticMatrixDimension)
    (hDim : ManifoldDimensionTopologySource.LeeInvarianceOfDimension)
    (m : ℕ) : Nonempty (FirstProjectorModel m) := by
  obtain ⟨d, ⟨g⟩⟩ :=
    (leeClosedSubgroupForCompactSymplectic_of_general hClosed) (m + 1)
  obtain ⟨e, q, ⟨a⟩⟩ :=
    (leeHomogeneousSpaceForProjectorStabilizer_of_general hClosed hQuot)
      (m + 1) d g
  exact ⟨{
    d := d
    e := e
    q := q
    groupAtlas := g
    quotientAtlas := a
    realDimension := actual_projective_carrier_real_dimension
      hKnapp hDim m d e q g a
  }⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorRiemannianMetric
