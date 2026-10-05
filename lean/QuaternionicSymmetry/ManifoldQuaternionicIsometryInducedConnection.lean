import QuaternionicSymmetry.ManifoldQuaternionicIsometryConnectionNaturality
import QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap
import QuaternionicSymmetry.ManifoldQuaternionicLocalCoefficientComparison

/-! Transport of the actual induced quaternionic rank-three connection
under an actual smooth metric-quaternionic isometry. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryInducedConnection

open Filter
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicConnection
open ManifoldQuaternionicAdjointConnection
open ManifoldQuaternionicAdjointOverlap
open ManifoldQuaternionicIsometryChartFields
open ManifoldQuaternionicIsometryConnectionPullback
open ManifoldQuaternionicIsometryConnectionNaturality
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicLocalCoefficientComparison
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The genuine coefficient action for a fixed quaternionic vector,
expressed as a function of source chart coordinates. -/
def coefficientOrbit (f : QuaternionicIsometries Q) (p : M)
    (a : Fin 3 → ℝ) : E → (Fin 3 → ℝ) :=
  fun y => ManifoldQuaternionicIsometryLocalDerivative.localCoefficientRotation
    Q f p ((extChartAt 𝓘(ℝ,E) p).symm y) a

/-- Differentiating the actual derivative-conjugation coefficient action. -/
theorem coefficientOrbit_fderiv_center
    (f : QuaternionicIsometries Q) (p : M)
    (a : Fin 3 → ℝ) (u : E) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    let A := forwardFrameField Q f p
    let B := reverseFrameField Q f p
    let T := synth (Q.reduction.Q (achart E p)) a
    fderiv ℝ (coefficientOrbit Q f p a) y₀ u =
      coeff (Q.reduction.Q (achart E (f • p)))
        (fderiv ℝ A y₀ u * T * B y₀ +
          A y₀ * T * fderiv ℝ B y₀ u) := by
  dsimp only
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let A := forwardFrameField Q f p
  let B := reverseFrameField Q f p
  let T := synth (Q.reduction.Q (achart E p)) a
  let c := coeff (Q.reduction.Q (achart E (f • p)))
  have hA : DifferentiableAt ℝ A y₀ :=
    (localAdaptedDerivative_coordinate_smoothAt_center Q f p).differentiableAt
      (by norm_num)
  have hB : DifferentiableAt ℝ B y₀ :=
    (localAdaptedInverseDerivative_coordinate_smoothAt_center Q f p).differentiableAt
      (by norm_num)
  have hprod : DifferentiableAt ℝ (fun y => A y * T * B y) y₀ :=
    (hA.mul (differentiableAt_const T)).mul hB
  have hfun : coefficientOrbit Q f p a =
      fun y => c (A y * T * B y) := rfl
  rw [hfun]
  have hc := fderiv_comp y₀ c.differentiableAt hprod
  change fderiv ℝ (fun y => c (A y * T * B y)) y₀ = _ at hc
  rw [hc, c.fderiv]
  exact congrArg c (fderiv_conjugate_const A B T y₀ u hA hB)

/-- The reverse adapted derivative differentiates as the genuine inverse
of the forward adapted derivative. -/
theorem reverseFrameField_fderiv_center
    (f : QuaternionicIsometries Q) (p : M) (u : E) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    let A := forwardFrameField Q f p
    let B := reverseFrameField Q f p
    fderiv ℝ B y₀ u = -(B y₀ * fderiv ℝ A y₀ u * B y₀) := by
  dsimp only
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let A := forwardFrameField Q f p
  let B := reverseFrameField Q f p
  have hA : DifferentiableAt ℝ A y₀ :=
    (localAdaptedDerivative_coordinate_smoothAt_center Q f p).differentiableAt
      (by norm_num)
  have hB : DifferentiableAt ℝ B y₀ :=
    (localAdaptedInverseDerivative_coordinate_smoothAt_center Q f p).differentiableAt
      (by norm_num)
  have hleft : (fun y => B y * A y) =ᶠ[nhds y₀] fun _ => 1 := by
    filter_upwards [localAdaptedInverse_forward_eventually Q f p] with y hy
    apply ContinuousLinearMap.ext
    intro z
    exact hy z
  have hsrc : (extChartAt 𝓘(ℝ,E) p).symm y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hright : A y₀ * B y₀ = 1 := by
    apply ContinuousLinearMap.ext
    intro z
    simpa only [A, B, forwardFrameField, reverseFrameField, hsrc] using
      ManifoldQuaternionicIsometryLocalDerivative.localAdaptedDerivative_inverse_center
        Q f p z
  exact LocalConnectionGauge.fderiv_inverse_pair A B y₀ hA hB hleft hright u

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem affine_adjoint_identity
    (g h Λ dg Γ T dh : E →L[ℝ] E)
    (hgh : g * h = 1)
    (hΓ : Γ = h * (Λ * g + dg))
    (hdh : dh = -(h * dg * h)) :
    g * (Γ * T - T * Γ) * h =
      Λ * (g * T * h) - (g * T * h) * Λ +
        (dg * T * h + g * T * dh) := by
  subst Γ
  subst dh
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, mul_assoc]
  simp only [← mul_assoc g h, hgh, one_mul]
  noncomm_ring

/-- The actual quaternionic coefficient action intertwines the induced
rank-three connection by the affine gauge law. This follows from genuine
tangent-connection naturality, not a separate invariance assumption. -/
theorem inducedForm_isometry_affine_center
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (p : M) (u : E)
    (a : Fin 3 → ℝ) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    coefficientOrbit Q f p (inducedForm Q D p y₀ u a) y₀ =
      inducedForm Q D (f • p) (localIsometryChartMap Q f p y₀)
        (fderiv ℝ (localIsometryChartMap Q f p) y₀ u)
        (coefficientOrbit Q f p a y₀) +
      fderiv ℝ (coefficientOrbit Q f p a) y₀ u := by
  dsimp only
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let F := localIsometryChartMap Q f p
  let g := forwardFrameField Q f p
  let h := reverseFrameField Q f p
  let c := coeff (Q.reduction.Q (achart E (f • p)))
  let T := synth (Q.reduction.Q (achart E p)) a
  let Γ := D.form p y₀ u
  let Λ := D.form (f • p) (F y₀) (fderiv ℝ F y₀ u)
  have hsrc : (extChartAt 𝓘(ℝ,E) p).symm y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hF : F y₀ = extChartAt 𝓘(ℝ,E) (f • p) (f • p) := by
    simp only [F, localIsometryChartMap, hsrc]
  have hmemsrc : y₀ ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  have hmemtgt : F y₀ ∈ (extChartAt 𝓘(ℝ,E) (f • p)).target := by
    rw [hF]
    exact (extChartAt 𝓘(ℝ,E) (f • p)).map_source (by simp)
  have hgh : g y₀ * h y₀ = 1 := by
    apply ContinuousLinearMap.ext
    intro z
    simpa only [g, h, forwardFrameField, reverseFrameField, hsrc] using
      ManifoldQuaternionicIsometryLocalDerivative.localAdaptedDerivative_inverse_center
        Q f p z
  have hdh : fderiv ℝ h y₀ u =
      -(h y₀ * fderiv ℝ g y₀ u * h y₀) :=
    reverseFrameField_fderiv_center Q f p u
  have hΓ : Γ = h y₀ * (Λ * g y₀ + fderiv ℝ g y₀ u) := by
    have hd := congrArg (fun L : E →L[ℝ] (E →L[ℝ] E) => L u)
      (pulledConnectionForm_eq_center Q D f p)
    apply ContinuousLinearMap.ext
    intro z
    have hz := congrArg (fun L : E →L[ℝ] E => L z) hd.symm
    simpa only [pulledConnectionForm_apply, g, h, Γ, Λ, F,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply] using hz
  have hPa (b : Fin 3 → ℝ) :
      coefficientOrbit Q f p b y₀ =
        ManifoldQuaternionicIsometryCoefficients.coefficientAction Q f p b := by
    simpa only [coefficientOrbit, hsrc] using
      localCoefficientRotation_center Q f p b
  have hconj (b : Fin 3 → ℝ) :
      g y₀ * synth (Q.reduction.Q (achart E p)) b * h y₀ =
        synth (Q.reduction.Q (achart E (f • p)))
          (coefficientOrbit Q f p b y₀) := by
    rw [hPa]
    simpa only [g, h, forwardFrameField, reverseFrameField, hsrc]
      using localDerivative_conjugates_synth_center Q f p b
  calc
    coefficientOrbit Q f p (inducedForm Q D p y₀ u a) y₀ =
        c (g y₀ * synth (Q.reduction.Q (achart E p))
          (inducedForm Q D p y₀ u a) * h y₀) := by
          simp only [coefficientOrbit, hsrc,
            ManifoldQuaternionicIsometryLocalDerivative.localCoefficientRotation,
            g, h, forwardFrameField, reverseFrameField,
            ContinuousLinearMap.mul_def]
          congr 1
    _ = c (g y₀ * (Γ * T - T * Γ) * h y₀) := by
      rw [synth_inducedForm Q D p y₀ u hmemsrc a]
      rfl
    _ = c (Λ * (g y₀ * T * h y₀) - (g y₀ * T * h y₀) * Λ +
          (fderiv ℝ g y₀ u * T * h y₀ +
            g y₀ * T * fderiv ℝ h y₀ u)) := by
      exact congrArg c (affine_adjoint_identity (g y₀) (h y₀)
        Λ (fderiv ℝ g y₀ u) Γ T (fderiv ℝ h y₀ u)
        hgh hΓ hdh)
    _ = _ := by
      rw [inducedForm_apply, ← hconj a,
        coefficientOrbit_fderiv_center Q f p a u]
      simp only [← ContinuousLinearMap.mul_def, map_sub, map_add]
      abel

/-- The local horizontal graph equation is carried exactly to the target
horizontal graph by the derivative-conjugation coefficient action. This is
the coefficient-coordinate core of contact-distribution equivariance. -/
theorem horizontal_coefficient_graph_covariant_center
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (p : M) (u : E)
    (a : Fin 3 → ℝ) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    coefficientOrbit Q f p (-(inducedForm Q D p y₀ u a)) y₀ +
      fderiv ℝ (coefficientOrbit Q f p a) y₀ u =
      -(inducedForm Q D (f • p)
        (localIsometryChartMap Q f p y₀)
        (fderiv ℝ (localIsometryChartMap Q f p) y₀ u)
        (coefficientOrbit Q f p a y₀)) := by
  dsimp only
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  have hsrc : (extChartAt 𝓘(ℝ,E) p).symm y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hlin (b : Fin 3 → ℝ) :
      coefficientOrbit Q f p (-b) y₀ =
        -(coefficientOrbit Q f p b y₀) := by
    simp only [coefficientOrbit, hsrc,
      ManifoldQuaternionicLocalCoefficientComparison.localCoefficientRotation_center]
    exact map_neg _ _
  rw [hlin]
  have h := inducedForm_isometry_affine_center Q D f p u a
  dsimp only at h
  rw [h]
  abel

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryInducedConnection
