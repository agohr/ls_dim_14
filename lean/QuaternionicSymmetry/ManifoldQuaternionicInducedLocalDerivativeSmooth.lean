import QuaternionicSymmetry.ManifoldQuaternionicInducedLocalIntertwining
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The rectangular inclusion derivative is smooth in fixed source/target
tangent charts. This is the analytic input for the local metric quotient
formula for induced quaternionic coefficients. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedLocalDerivativeSmooth
open ManifoldQuaternionicInducedLocalIntertwining
open scoped Manifold ContDiff Topology
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem localDerivative_smoothAt_center (ι : N → M)
    (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι) (c : N) :
    ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] E) ∞
      (localDerivative ι (achart F c) (achart E (ι c))) c := by
  have hlocal : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] E) ∞
      (inTangentCoordinates 𝓘(ℝ,F) 𝓘(ℝ,E) id ι
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι) c) c :=
    hι.contMDiffAt.mfderiv_const (by simp)
  have hsource : ∀ᶠ x in 𝓝 c, x ∈ (chartAt F c).source :=
    (chartAt F c).open_source.mem_nhds (mem_chart_source F c)
  have htarget : ∀ᶠ x in 𝓝 c,
      ι x ∈ (chartAt E (ι c)).source :=
    (((chartAt E (ι c)).open_source.preimage hι.continuous).mem_nhds
      (mem_chart_source E (ι c)))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hsource, htarget] with x hx hy
  exact (inTangentCoordinates_eq id ι
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι) hx hy).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedLocalDerivativeSmooth
