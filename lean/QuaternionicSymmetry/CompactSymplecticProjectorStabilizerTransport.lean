import QuaternionicSymmetry.CompactSymplecticProjectorStabilizerPlane
import QuaternionicSymmetry.CompactSymplecticProjectorTranslatedImaginaryPlane

/-! The translated imaginary plane is unchanged by changing the base
representative through an actual projector-stabilizer element. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStabilizerTransport

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseImaginaryPlane
open CompactSymplecticProjectorTranslatedImaginaryPlane
open CompactSymplecticProjectorStabilizerTangentEquiv
open CompactSymplecticProjectorStabilizerPlane
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

theorem translatedImaginaryPlane_stabilizer
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : firstPairStabilizer n) :
    letI := atlas.quotientCharts
    translatedImaginaryPlane hDesc hImm n d e q g atlas hq u.1 =
      baseImaginaryPlane hDesc hImm n d e q g atlas hq := by
  letI := atlas.quotientCharts
  exact stabilizer_conj_preserves_imaginary hDesc hImm n d e q g atlas hq hn u

end
end QuaternionicSymmetry.CompactSymplecticProjectorStabilizerTransport
