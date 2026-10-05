import QuaternionicSymmetry.CompactSymplecticProjectorBaseTangentCharacterization
import QuaternionicSymmetry.ProjectorQuaternionicConjugationConstraints
import QuaternionicSymmetry.CompactSymplecticProjectorSmoothAction
import QuaternionicSymmetry.ManifoldEquivariantPullbackPairing

/-! The exact quaternionic-Hermitian Peirce tangent characterization
propagates from the actual base projector to every point of its genuine
compact symplectic quotient orbit. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTangentRangeEverywhere

open Matrix Manifold
open CompactSymplecticHaar
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseTangentCharacterization
open CompactSymplecticProjectorSmoothAction
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticProjectorAmbientMetric
open ProjectorQuaternionicConjugationConstraints
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem actual_quaternionicHermitian_tangent_surjective
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (x : ProjectiveCarrier n) (X : Mat n)
    (hSelf : Xᴴ = X)
    (hPeirce : quotientOrbitProjector n x * X + X * quotientOrbitProjector n x = X)
    (hQuat : X * standardJ (n + 1) = standardJ (n + 1) * X.map star) :
    letI := a.quotientCharts
    ∃ v : TangentSpace 𝓘(ℝ,RModel q) x,
      mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
        (quotientOrbitProjector n) x v = X := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := g.charts
  induction x using Quotient.inductionOn' with
  | _ u =>
    let U : Mat n := (u.1 : Mat n)
    let V : Mat n := ((u⁻¹).1 : Mat n)
    let P : Mat n := orbitProjector n u
    let J : Mat n := standardJ (n + 1)
    let Y : Mat n := V * X * U
    have hUV : U * V = 1 := by
      change ((u * u⁻¹ : G n).1.1 : Mat n) = 1
      simp
    have hVU : V * U = 1 := by
      change ((u⁻¹ * u : G n).1.1 : Mat n) = 1
      simp
    have hVadj : Vᴴ = U := by
      change (Uᴴ)ᴴ = U
      exact Matrix.conjTranspose_conjTranspose U
    have hUadj : Uᴴ = V := by
      rfl
    have hP : P = U * firstPairProjector n * V := by
      exact orbitProjector_eq_mul_inverse n u
    have hPpull : V * P * U = firstPairProjector n := by
      rw [hP]
      simp only [mul_assoc, ← mul_assoc V U, hVU, one_mul,
        ← mul_assoc (firstPairProjector n) V U, hUV, mul_one]
    have hYself : Yᴴ = Y := by
      simpa only [Y, hVadj] using conjugation_hermitian V X hSelf
    have hYpeirce : firstPairProjector n * Y + Y * firstPairProjector n = Y := by
      have h := conjugation_tangent V U P X hUV (by
        simpa only [P, quotientOrbitProjector_mk] using hPeirce)
      simpa only [hPpull, Y] using h
    have hUJ : U * J = J * U.map star :=
      (QuaternionicMatrixModel.unitary_mem_stabilizer_iff_commutes_J
        (n + 1) u.1).mp u.2
    have hVJ : V * J = J * V.map star :=
      (QuaternionicMatrixModel.unitary_mem_stabilizer_iff_commutes_J
        (n + 1) (u⁻¹).1).mp (u⁻¹).2
    have hYquat : Y * J = J * Y.map star :=
      conjugation_quaternionic J V U X hVJ hUJ hQuat
    obtain ⟨v, hv⟩ := base_quaternionicHermitian_tangent_surjective
      hDesc hImm n d e q g a hq Y hYself hYpeirce hYquat
    let w : TangentSpace 𝓘(ℝ,RModel q) (u : ProjectiveCarrier n) :=
      mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,RModel q)
        (leftCosetAction n u) (baseCoset n) v
    refine ⟨w, ?_⟩
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
    have hEq := ManifoldEquivariantPullbackPairing.mfderiv_equivariance
      (quotientOrbitProjector n) (leftCosetAction n u)
      (conjugationCLM n u)
      (smooth_quotientOrbitProjector_actual hDesc n d e q g a)
      hAct (quotient_projector_equivariant n u) (baseCoset n) v
    rw [hbase] at hEq
    simp only [conjugationCLM_apply] at hEq
    rw [hv] at hEq
    calc
      _ = U * Y * V := hEq
      _ = X := by
        simp only [Y, mul_assoc, ← mul_assoc U V, hUV, one_mul,
          ← mul_assoc X U V, hUV, mul_one]

end
end QuaternionicSymmetry.CompactSymplecticProjectorTangentRangeEverywhere
