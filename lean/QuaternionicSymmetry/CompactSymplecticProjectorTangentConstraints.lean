import QuaternionicSymmetry.CompactSymplecticProjectorRiemannianMetric
import QuaternionicSymmetry.CompactSymplecticQuaternionicOrbit

/-! Matrix equations satisfied by tangent vectors in the genuine differential
image of the projector quotient. These describe the actual model tangent
space inside the ambient matrix vector space. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTangentConstraints

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticProjectorSmoothAction
open CompactSymplecticQuaternionicOrbit
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- Any ambient continuous-linear equation holding at every orbit point
also holds on the image of its true manifold differential. -/
private theorem derivative_linear_constraint
    {M : Type*} {E V W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [TopologicalSpace M] [ChartedSpace E M]
    (f : M → V) (L : V →L[ℝ] W)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f)
    (h : ∀ y, L (f y) = 0)
    (x : M) (v : TangentSpace 𝓘(ℝ,E) x) :
    L (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x v) = 0 := by
  have hfun : L ∘ f = fun _ => (0 : W) := funext h
  have hd := mfderiv_comp x L.mdifferentiableAt
    (hf.mdifferentiableAt (by simp))
  rw [hfun, mfderiv_const, L.mfderiv_eq] at hd
  have hv := congrArg (fun D : TangentSpace 𝓘(ℝ,E) x →L[ℝ] W => D v) hd
  simpa using hv.symm

/-- Conjugate transpose is real-linear and continuous in the operator-norm
topology, as both matrix spaces are finite-dimensional. -/
private def adjointCLM (n : ℕ) : Mat n →L[ℝ] Mat n :=
  (show Mat n →ₗ[ℝ] Mat n from {
    toFun := Matrix.conjTranspose
    map_add' := by intro A B; simp
    map_smul' := by intro c A; simp
  }).toContinuousLinearMap

private def selfAdjointConstraint (n : ℕ) : Mat n →L[ℝ] Mat n :=
  adjointCLM n - ContinuousLinearMap.id ℝ (Mat n)

/-- Every true tangent projector matrix is Hermitian. -/
theorem tangent_projector_selfAdjoint
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) x),
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x v)ᴴ =
      mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x v := by
  letI := a.quotientCharts
  intro v
  have hvalue : ∀ y : ProjectiveCarrier n,
      selfAdjointConstraint n (quotientOrbitProjector n y) = 0 := by
    intro y
    induction y using Quotient.inductionOn' with
    | _ u =>
      change (orbitProjector n u)ᴴ - orbitProjector n u = 0
      rw [orbitProjector_selfAdjoint]
      simp
  have hder := derivative_linear_constraint (quotientOrbitProjector n)
    (selfAdjointConstraint n)
    (smooth_quotientOrbitProjector_actual hDesc n d e q g a)
    hvalue x v
  dsimp [selfAdjointConstraint, adjointCLM] at hder
  exact sub_eq_zero.mp hder

/-- Real-linear ambient equation expressing commutation with the standard
quaternionic anti-linear structure. -/
private def quaternionicConstraint (n : ℕ) : Mat n →L[ℝ] Mat n :=
  (show Mat n →ₗ[ℝ] Mat n from {
    toFun := fun A => A * CompactSymplecticHaar.standardJ (n + 1) -
      CompactSymplecticHaar.standardJ (n + 1) * A.map star
    map_add' := by
      intro A B
      simp [add_mul, mul_add, Matrix.map_add, sub_add_sub_comm]
    map_smul' := by
      intro c A
      simp [Matrix.map_smul, smul_sub]
  }).toContinuousLinearMap

/-- Every true tangent projector matrix obeys the quaternionic
anti-linear commutation law, inherited by differentiating the checked
equation at every orbit point. -/
theorem tangent_projector_commutes_quaternionicJ
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) x),
      let X : Mat n := mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x v
      X * CompactSymplecticHaar.standardJ (n + 1) =
        CompactSymplecticHaar.standardJ (n + 1) * X.map star := by
  letI := a.quotientCharts
  intro v
  have hvalue : ∀ y : ProjectiveCarrier n,
      quaternionicConstraint n (quotientOrbitProjector n y) = 0 := by
    intro y
    induction y using Quotient.inductionOn' with
    | _ u =>
      change orbitProjector n u * CompactSymplecticHaar.standardJ (n + 1) -
        CompactSymplecticHaar.standardJ (n + 1) * (orbitProjector n u).map star = 0
      exact sub_eq_zero.mpr (orbitProjector_commutes_quaternionicJ n u)
  have hder := derivative_linear_constraint (quotientOrbitProjector n)
    (quaternionicConstraint n)
    (smooth_quotientOrbitProjector_actual hDesc n d e q g a)
    hvalue x v
  dsimp [quaternionicConstraint] at hder
  exact sub_eq_zero.mp hder

/-- Differentiating the genuine idempotency equation puts every tangent
matrix in the off-diagonal Peirce component at its base projector. -/
theorem tangent_projector_offDiagonal
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) x),
      let P : Mat n := quotientOrbitProjector n x
      let X : Mat n := mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x v
      P * X + X * P = X := by
  letI := a.quotientCharts
  intro v
  let P : Mat n := quotientOrbitProjector n x
  let X : Mat n := mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
    (quotientOrbitProjector n) x v
  have hid : ∀ y : ProjectiveCarrier n,
      quotientOrbitProjector n y * quotientOrbitProjector n y =
        quotientOrbitProjector n y := by
    intro y
    induction y using Quotient.inductionOn' with
    | _ u => exact orbitProjector_idempotent n u
  have hfun : (fun A : Mat n => A * A) ∘ quotientOrbitProjector n =
      quotientOrbitProjector n := funext hid
  have hsqd : DifferentiableAt ℝ (fun A : Mat n => A * A) P := by
    fun_prop
  have hd := mfderiv_comp x hsqd.mdifferentiableAt
    ((smooth_quotientOrbitProjector_actual hDesc n d e q g a).mdifferentiableAt
      (by simp))
  change mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
    ((fun A : Mat n => A * A) ∘ quotientOrbitProjector n) x = _ at hd
  rw [hfun, mfderiv_eq_fderiv] at hd
  have hv := congrArg
    (fun D : TangentSpace 𝓘(ℝ, RModel q) x →L[ℝ] Mat n => D v) hd
  change X = (fderiv ℝ (fun A : Mat n => A * A) P) X at hv
  have hmul := fderiv_fun_mul' (a := id) (b := id)
    (differentiableAt_id : DifferentiableAt ℝ (id : Mat n → Mat n) P)
    differentiableAt_id
  change fderiv ℝ (fun A : Mat n => A * A) P = _ at hmul
  rw [hmul] at hv
  simpa [P, X, fderiv_id, MulOpposite.op_smul] using hv.symm

/-- The Peirce tangent equation forces the diagonal projector block to vanish. -/
private theorem projector_tangent_diagonal_zero
    {n : ℕ} (P X : Mat n) (hP : P * P = P)
    (hX : P * X + X * P = X) : P * X * P = 0 := by
  have hleft := congrArg (fun Y : Mat n => P * Y) hX
  have hleft' : P * X + P * (X * P) = P * X := by
    simpa only [mul_add, ← mul_assoc, hP] using hleft
  have hzero : P * (X * P) = 0 := by
    apply add_left_cancel (a := P * X)
    simpa using hleft'
  simpa only [mul_assoc] using hzero

/-- Matrix reflection in an idempotent negates every off-diagonal tangent
matrix. This is the ambient algebra behind the point symmetry. -/
private theorem projector_reflection_negates_tangent
    {n : ℕ} (P X : Mat n) (hP : P * P = P)
    (hX : P * X + X * P = X) :
    (P + P - 1) * X * (P + P - 1) = -X := by
  have hzero := projector_tangent_diagonal_zero P X hP hX
  calc
    (P + P - 1) * X * (P + P - 1) =
        (P * X * P + P * X * P + P * X * P + P * X * P) -
          ((P * X + X * P) + (P * X + X * P)) + X := by
            noncomm_ring
    _ = -X := by rw [hzero, hX]; simp

/-- At every point of the actual quotient, reflection in its projector
negates the ambient image of each genuine tangent vector. -/
theorem tangent_projector_reflection_negates
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) x),
      let P : Mat n := quotientOrbitProjector n x
      let X : Mat n := mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x v
      (P + P - 1) * X * (P + P - 1) = -X := by
  letI := a.quotientCharts
  intro v
  apply projector_reflection_negates_tangent
  · induction x using Quotient.inductionOn' with
    | _ u => exact orbitProjector_idempotent n u
  · exact tangent_projector_offDiagonal hDesc n d e q g a x v

end
end QuaternionicSymmetry.CompactSymplecticProjectorTangentConstraints
