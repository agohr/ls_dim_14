import QuaternionicSymmetry.CompactSymplecticProjectorStrongTwistorAction
import QuaternionicSymmetry.CompactSymplecticProjectorCarrierConnected
import QuaternionicSymmetry.ManifoldQuaternionicJointSphereContinuity
import QuaternionicSymmetry.ManifoldTwistorSphereHomeomorph

/-! Joint continuity of the *actual* derivative-induced Sp action on the
strong quotient's twistor sphere. The only external input is the already
registered general isometry Lie theorem BG-R3, used for joint derivative
continuity; the Sp representation itself is the checked projector action. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongTwistorActionContinuous

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongTwistorAction
open CompactSymplecticProjectorStrongTranslationHom
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorCarrierConnected
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicIsometryTopology
open ManifoldQuaternionicJointSphereContinuity
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
open ManifoldTwistorSphereManifold
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxRecDepth 4000

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem continuous_strongTwistorAction
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
    Continuous (fun p : G n × TwistorSphere
        (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn) =>
      p.1 • p.2) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := g.charts
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
  letI : ConnectedSpace (ProjectiveCarrier n) := projectiveCarrier_connectedSpace n
  let ρ := translationQuaternionicIsometryHom hLee hDesc hImm n d e q g a hq hn
  have hρ : Continuous ρ := by
    apply continuous_representation_of_action Q ρ
    simpa only [ρ] using a.actionSmooth.continuous
  have hpair : Continuous (fun p : G n × TwistorSphere Q =>
      (ρ p.1, (sphereTotalHomeomorph Q).symm p.2)) :=
    (hρ.comp continuous_fst).prodMk
      ((sphereTotalHomeomorph Q).symm.continuous.comp continuous_snd)
  have h := (sphereTotalHomeomorph Q).continuous.comp
    ((continuous_jointSphereTotalMap Q hR3).comp hpair)
  convert h using 1
  funext p
  change twistorMap Q (ρ p.1) p.2 =
    (sphereTotalHomeomorph Q)
      (sphereTotalMap Q (ρ p.1) ((sphereTotalHomeomorph Q).symm p.2))
  change twistorMap Q (ρ p.1) p.2 =
    (sphereTotalEquiv Q)
      ((sphereTotalEquiv Q).symm
        (twistorMap Q (ρ p.1)
          ((sphereTotalEquiv Q) ((sphereTotalEquiv Q).symm p.2))))
  simp only [(sphereTotalEquiv Q).apply_symm_apply]

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongTwistorActionContinuous
