import QuaternionicSymmetry.CompactSymplecticProjectorTangentConstraints

/-! The reflection associated to an actual quaternionic Hermitian projector
is an element of the compact symplectic group. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorReflection

open Matrix
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticQuaternionicOrbit
open CompactSymplecticProjectorSmoothAction
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticProjectorAmbientMetric
open Manifold
open scoped Manifold ContDiff
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- The involution that is `+1` on the projector image and `-1` on its
orthogonal complement. -/
def reflectionMatrix {n : ℕ} (P : Mat n) : Mat n := P + P - 1

theorem reflectionMatrix_selfAdjoint {n : ℕ} (P : Mat n) (hP : Pᴴ = P) :
    (reflectionMatrix P)ᴴ = reflectionMatrix P := by
  simp [reflectionMatrix, hP]

theorem reflectionMatrix_sq {n : ℕ} (P : Mat n) (hP : P * P = P) :
    reflectionMatrix P * reflectionMatrix P = 1 := by
  unfold reflectionMatrix
  calc
    (P + P - 1) * (P + P - 1) =
        (P * P + P * P + P * P + P * P) - (P + P + P + P) + 1 := by
          noncomm_ring
    _ = 1 := by rw [hP]; abel

private theorem reflectionMatrix_quaternionic {n : ℕ} (P : Mat n)
    (hP : P * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * P.map star) :
    reflectionMatrix P * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * (reflectionMatrix P).map star := by
  have hmap : (P + P - 1).map star = P.map star + P.map star - 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  unfold reflectionMatrix
  rw [hmap]
  calc
    (P + P - 1) * CompactSymplecticHaar.standardJ (n + 1) =
        P * CompactSymplecticHaar.standardJ (n + 1) +
          P * CompactSymplecticHaar.standardJ (n + 1) -
          CompactSymplecticHaar.standardJ (n + 1) := by noncomm_ring
    _ = CompactSymplecticHaar.standardJ (n + 1) *
          (P.map star + P.map star - 1) := by rw [hP]; noncomm_ring

private def reflectionOfProjector {n : ℕ} (P : Mat n)
    (hSelf : Pᴴ = P) (hIdem : P * P = P)
    (hQuat : P * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * P.map star) :
    CompactSymplecticHaar.Group (n + 1) := by
  let R := reflectionMatrix P
  let J := CompactSymplecticHaar.standardJ (n + 1)
  have hAdj : Rᴴ = R := reflectionMatrix_selfAdjoint P hSelf
  have hSq : R * R = 1 := reflectionMatrix_sq P hIdem
  have hUnit : R ∈ Matrix.unitaryGroup (I n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    simpa only [Matrix.star_eq_conjTranspose, hAdj] using hSq
  have hTranspose : Rᵀ = R.map star := by
    have h := congrArg Matrix.transpose hAdj
    simpa only [Matrix.conjTranspose, Matrix.transpose_map,
      Matrix.transpose_transpose] using h.symm
  have hRJ : R * J = J * Rᵀ := by
    rw [hTranspose]
    exact reflectionMatrix_quaternionic P hQuat
  have hTransposeJ : Rᵀ * J = J * R := by
    have hJ2 : J * J = -1 := CompactSymplecticHaar.standardJ_sq (n + 1)
    calc
      Rᵀ * J = -(J * J) * Rᵀ * J := by rw [hJ2]; noncomm_ring
      _ = -J * (J * Rᵀ) * J := by noncomm_ring
      _ = -J * (R * J) * J := by rw [hRJ]
      _ = J * R := by
        calc
          -J * (R * J) * J = -J * R * (J * J) := by noncomm_ring
          _ = J * R := by rw [hJ2]; noncomm_ring
  refine ⟨⟨R, hUnit⟩, ?_⟩
  change Rᵀ * J * R = J
  rw [hTransposeJ, mul_assoc, hSq, mul_one]

/-- An actual compact symplectic element reflecting about any projector
in the conjugation orbit. -/
def reflectionElement (n : ℕ) (x : ProjectiveCarrier n) :
    CompactSymplecticHaar.Group (n + 1) := by
  let P := quotientOrbitProjector n x
  have hSelf : Pᴴ = P := by
    induction x using Quotient.inductionOn' with
    | _ u => exact orbitProjector_selfAdjoint n u
  have hIdem : P * P = P := by
    induction x using Quotient.inductionOn' with
    | _ u => exact orbitProjector_idempotent n u
  have hQuat : P * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * P.map star := by
    induction x using Quotient.inductionOn' with
    | _ u => exact orbitProjector_commutes_quaternionicJ n u
  exact reflectionOfProjector P hSelf hIdem hQuat

theorem reflectionElement_matrix (n : ℕ) (x : ProjectiveCarrier n) :
    ((reflectionElement n x).1 : Mat n) =
      reflectionMatrix (quotientOrbitProjector n x) := rfl

theorem reflectionMatrix_fixes_projector {n : ℕ} (P : Mat n)
    (hIdem : P * P = P) :
    reflectionMatrix P * P * reflectionMatrix P = P := by
  unfold reflectionMatrix
  calc
    (P + P - 1) * P * (P + P - 1) =
        (P * P * P + P * P * P + P * P * P + P * P * P) -
          (P * P + P * P + P * P + P * P) + P := by noncomm_ring
    _ = P := by rw [hIdem]; simp [hIdem]

/-- The genuine compact symplectic reflection fixes its center in the
quotient, not merely its ambient projector. -/
theorem reflectionElement_fixes (n : ℕ) (x : ProjectiveCarrier n) :
    leftCosetAction n (reflectionElement n x) x = x := by
  apply quotientOrbitProjector_injective n
  rw [quotient_projector_equivariant, reflectionElement_matrix]
  have hAdj := reflectionMatrix_selfAdjoint
    (quotientOrbitProjector n x) (by
      induction x using Quotient.inductionOn' with
      | _ u => exact orbitProjector_selfAdjoint n u)
  rw [hAdj]
  exact reflectionMatrix_fixes_projector _ (by
    induction x using Quotient.inductionOn' with
    | _ u => exact orbitProjector_idempotent n u)

/-- An individual actual left translation is smooth in the selected Lee
quotient atlas. -/
private theorem smooth_leftCosetAction (n d e q : ℕ)
    (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (u : CompactSymplecticHaar.Group (n + 1)) :
    letI := a.quotientCharts
    ContMDiff 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q) ∞
      (leftCosetAction n u) := by
  letI := g.charts
  letI := a.quotientCharts
  have hpair : ContMDiff 𝓘(ℝ, RModel q)
      (𝓘(ℝ, RModel d).prod 𝓘(ℝ, RModel q)) ∞
      (fun y : ProjectiveCarrier n => (u, y)) :=
    contMDiff_const.prodMk contMDiff_id
  exact a.actionSmooth.comp hpair

/-- The actual point reflection has derivative `-Id` on the true manifold
tangent space, established through the injective projector immersion. -/
theorem reflectionElement_mfderiv_neg
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) x),
      mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n (reflectionElement n x)) x v = -v := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v
  let u := reflectionElement n x
  have hEq : ∀ y : ProjectiveCarrier n,
      quotientOrbitProjector n (leftCosetAction n u y) =
        conjugationCLM n u (quotientOrbitProjector n y) := by
    intro y
    simpa only [conjugationCLM_apply] using quotient_projector_equivariant n u y
  have hDer := ManifoldEquivariantPullbackPairing.mfderiv_equivariance
    (quotientOrbitProjector n) (leftCosetAction n u)
    (conjugationCLM n u)
    (smooth_quotientOrbitProjector_actual hDesc n d e q g a)
    (smooth_leftCosetAction n d e q g a u) hEq x v
  rw [reflectionElement_fixes] at hDer
  simp only [conjugationCLM_apply] at hDer
  dsimp only [u] at hDer
  rw [reflectionElement_matrix] at hDer
  have hAdj : (reflectionMatrix (quotientOrbitProjector n x))ᴴ =
      reflectionMatrix (quotientOrbitProjector n x) :=
    reflectionMatrix_selfAdjoint _ (by
      induction x using Quotient.inductionOn' with
      | _ w => exact orbitProjector_selfAdjoint n w)
  rw [hAdj] at hDer
  have hNeg := CompactSymplecticProjectorTangentConstraints.tangent_projector_reflection_negates
    hDesc n d e q g a x v
  simp only [reflectionMatrix] at hDer
  rw [hNeg] at hDer
  apply (quotientOrbitProjector_mfderiv_injective hDesc hImm n d e q g a x)
  simpa using hDer

end
end QuaternionicSymmetry.CompactSymplecticProjectorReflection
