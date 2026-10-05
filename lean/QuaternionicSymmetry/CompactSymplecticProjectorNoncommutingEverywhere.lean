import QuaternionicSymmetry.ProjectorQuaternionicNoncommutingBaseTangent
import QuaternionicSymmetry.ProjectorCommutatorConjugation
import QuaternionicSymmetry.CompactSymplecticProjectorTangentRangeEverywhere

/-! The explicit noncommuting base tangent pair propagates to every point
of the genuine compact symplectic quotient under its proved smooth,
transitive and projector-equivariant action. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorNoncommutingEverywhere

open Matrix Manifold
open CompactSymplecticHaar
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorSmoothAction
open CompactSymplecticProjectorAmbientMetric
open ProjectorQuaternionicNoncommutingBaseTangent
open ProjectorCommutatorConjugation
open ProjectorPeirceCurvatureBracket
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem actual_tangent_noncommuting_everywhere
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    ∀ x : ProjectiveCarrier n,
      ∃ v w : TangentSpace 𝓘(ℝ,RModel q) x,
        ProjectorPeirceCurvatureBracket.commutator
          (show Mat n from mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
            (quotientOrbitProjector n) x v)
          (show Mat n from mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
            (quotientOrbitProjector n) x w) ≠ 0 := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  obtain ⟨v, w, hcomm⟩ :=
    actual_base_tangent_noncommuting hDesc hImm n d e q g a hq hn
  intro x
  induction x using Quotient.inductionOn' with
  | _ u =>
    letI := g.charts
    let U : Mat n := (u.1 : Mat n)
    let V : Mat n := ((u⁻¹).1 : Mat n)
    have hUV : U * V = 1 := by
      change ((u * u⁻¹ : G n).1.1 : Mat n) = 1
      simp
    have hVU : V * U = 1 := by
      change ((u⁻¹ * u : G n).1.1 : Mat n) = 1
      simp
    let v' : TangentSpace 𝓘(ℝ,RModel q) (u : ProjectiveCarrier n) :=
      mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,RModel q)
        (leftCosetAction n u) (baseCoset n) v
    let w' : TangentSpace 𝓘(ℝ,RModel q) (u : ProjectiveCarrier n) :=
      mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,RModel q)
        (leftCosetAction n u) (baseCoset n) w
    refine ⟨v', w', ?_⟩
    have hAct : ContMDiff 𝓘(ℝ,RModel q) 𝓘(ℝ,RModel q) ∞
        (leftCosetAction n u) := by
      have hpair : ContMDiff 𝓘(ℝ,RModel q)
          (𝓘(ℝ,RModel d).prod 𝓘(ℝ,RModel q)) ∞
          (fun z : ProjectiveCarrier n => (u,z)) :=
        contMDiff_const.prodMk contMDiff_id
      exact a.actionSmooth.comp hpair
    have hbase : leftCosetAction n u (baseCoset n) = (u : ProjectiveCarrier n) := by
      change ((u * 1 : G n) : ProjectiveCarrier n) = u
      simp
    have hEqv := ManifoldEquivariantPullbackPairing.mfderiv_equivariance
      (quotientOrbitProjector n) (leftCosetAction n u)
      (conjugationCLM n u)
      (smooth_quotientOrbitProjector_actual hDesc n d e q g a)
      hAct (quotient_projector_equivariant n u) (baseCoset n) v
    have hEqw := ManifoldEquivariantPullbackPairing.mfderiv_equivariance
      (quotientOrbitProjector n) (leftCosetAction n u)
      (conjugationCLM n u)
      (smooth_quotientOrbitProjector_actual hDesc n d e q g a)
      hAct (quotient_projector_equivariant n u) (baseCoset n) w
    rw [hbase] at hEqv hEqw
    simp only [conjugationCLM_apply] at hEqv hEqw
    have hstrict := commutator_conjugate_ne_zero U V
      (show Mat n from mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
        (quotientOrbitProjector n) (baseCoset n) v)
      (show Mat n from mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
        (quotientOrbitProjector n) (baseCoset n) w)
      hVU hUV hcomm
    let X' : Mat n := mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
      (quotientOrbitProjector n) (u : ProjectiveCarrier n) v'
    let Y' : Mat n := mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
      (quotientOrbitProjector n) (u : ProjectiveCarrier n) w'
    have hX' : X' = U *
        (show Mat n from mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
          (quotientOrbitProjector n) (baseCoset n) v) * V := hEqv
    have hY' : Y' = U *
        (show Mat n from mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
          (quotientOrbitProjector n) (baseCoset n) w) * V := hEqw
    change ProjectorPeirceCurvatureBracket.commutator X' Y' ≠ 0
    rw [hX', hY']
    exact hstrict

end
end QuaternionicSymmetry.CompactSymplecticProjectorNoncommutingEverywhere
