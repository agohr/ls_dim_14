import QuaternionicSymmetry.CompactSymplecticProjectorQuotientImaginaryPlane
import QuaternionicSymmetry.CompactSymplecticProjectorLocalSection

/-! Smooth local representative gauges for the actual descended
rank-three quaternionic tangent plane. Derivative-frame smoothness is
not inferred from this statement and remains the next obligation. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicGauge

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorTranslatedImaginaryPlane
open CompactSymplecticProjectorLocalSection
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- Through each genuine quotient point, Lee's local section yields a
smooth representative gauge in which the pointwise Q-plane has the
explicit derivative-transport formula. -/
theorem quotientImaginaryPlane_local_gauge
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := g.charts
    letI := a.quotientCharts
    ∃ U : Set (ProjectiveCarrier n), IsOpen U ∧ x ∈ U ∧
      ∃ σ : ProjectiveCarrier n → G n,
        ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞ σ U ∧
        (∀ y ∈ U, (σ y : ProjectiveCarrier n) = y) ∧
        (∀ y ∈ U, quotientImaginaryPlane hDesc hImm n d e q g a hq hn y =
          translatedImaginaryPlane hDesc hImm n d e q g a hq (σ y)) := by
  letI := g.charts
  letI := a.quotientCharts
  obtain ⟨u, rfl⟩ := Quotient.exists_rep x
  obtain ⟨U, hU, hx, σ, hσ, _, hright⟩ :=
    quotient_local_section hLee n d e q g a u
  refine ⟨U, hU, hx, σ, hσ, hright, ?_⟩
  intro y hy
  conv_lhs => rw [← hright y hy]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicGauge
