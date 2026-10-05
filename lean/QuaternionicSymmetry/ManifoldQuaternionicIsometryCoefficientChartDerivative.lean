import QuaternionicSymmetry.ManifoldQuaternionicIsometryInducedConnection

/-! The jointly varying coefficient map behind the true twistor-sphere
lift, before restriction to the unit sphere. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryCoefficientChartDerivative

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryChartFields
open ManifoldQuaternionicIsometryConnectionPullback
open ManifoldQuaternionicIsometryInducedConnection
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The actual derivative-conjugation coefficient action as a continuous
linear map on the three-dimensional quaternionic coefficient space. -/
def coefficientLinearField (f : QuaternionicIsometries Q) (p : M)
    (y : E) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (coeff (Q.reduction.Q (achart E (f • p)))).comp
    (((ContinuousLinearMap.compL ℝ E E E).flip (reverseFrameField Q f p y)).comp
      ((ContinuousLinearMap.compL ℝ E E E (forwardFrameField Q f p y)).comp
        (synth (Q.reduction.Q (achart E p)))))

theorem coefficientLinearField_apply (f : QuaternionicIsometries Q)
    (p : M) (y : E) (a : Fin 3 → ℝ) :
    coefficientLinearField Q f p y a = coefficientOrbit Q f p a y := by
  rfl

/-- The actual coefficient rotation is differentiable as a field of
continuous linear maps; this makes its joint base/fiber derivative canonical. -/
theorem coefficientLinearField_differentiableAt_center
    (f : QuaternionicIsometries Q) (p : M) :
    DifferentiableAt ℝ (coefficientLinearField Q f p)
      (extChartAt 𝓘(ℝ,E) p p) := by
  have hA : DifferentiableAt ℝ (forwardFrameField Q f p)
      (extChartAt 𝓘(ℝ,E) p p) :=
    (localAdaptedDerivative_coordinate_smoothAt_center Q f p).differentiableAt
      (by norm_num)
  have hB : DifferentiableAt ℝ (reverseFrameField Q f p)
      (extChartAt 𝓘(ℝ,E) p p) :=
    (localAdaptedInverseDerivative_coordinate_smoothAt_center Q f p).differentiableAt
      (by norm_num)
  unfold coefficientLinearField
  fun_prop

/-- The ordinary joint chart derivative splits into base variation and
linear vertical variation. -/
theorem coefficientLinearField_joint_fderiv_center
    (f : QuaternionicIsometries Q) (p : M)
    (a w : Fin 3 → ℝ) (u : E) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    fderiv ℝ (fun q : E × (Fin 3 → ℝ) =>
      coefficientLinearField Q f p q.1 q.2) (y₀,a) (u,w) =
      fderiv ℝ (coefficientOrbit Q f p a) y₀ u +
        coefficientOrbit Q f p w y₀ := by
  dsimp only
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let P := coefficientLinearField Q f p
  have hP : DifferentiableAt ℝ P y₀ :=
    coefficientLinearField_differentiableAt_center Q f p
  have hPpair : DifferentiableAt ℝ (fun q : E × (Fin 3 → ℝ) => P q.1)
      (y₀,a) := by fun_prop
  have ha : DifferentiableAt ℝ (fun q : E × (Fin 3 → ℝ) => q.2)
      (y₀,a) := differentiableAt_snd
  have hderiv := fderiv_clm_apply hPpair ha
  have hval := congrArg (fun L : (E × (Fin 3 → ℝ)) →L[ℝ]
      (Fin 3 → ℝ) => L (u,w)) hderiv
  change fderiv ℝ (fun q : E × (Fin 3 → ℝ) => P q.1 q.2)
      (y₀,a) (u,w) = _ at hval
  have hPf : fderiv ℝ (fun q : E × (Fin 3 → ℝ) => P q.1) (y₀,a) =
      (fderiv ℝ P y₀).comp
        (ContinuousLinearMap.fst ℝ E (Fin 3 → ℝ)) := by
    have hfst : DifferentiableAt ℝ
        (fun q : E × (Fin 3 → ℝ) => q.1) (y₀,a) :=
      differentiableAt_fst
    have hc := fderiv_comp (y₀,a) hP hfst
    have hfd : fderiv ℝ (fun q : E × (Fin 3 → ℝ) => q.1) (y₀,a) =
        ContinuousLinearMap.fst ℝ E (Fin 3 → ℝ) := fderiv_fst
    rw [hfd] at hc
    exact hc
  rw [hPf] at hval
  have hcol : fderiv ℝ (coefficientOrbit Q f p a) y₀ u =
      ((fderiv ℝ P y₀) u) a := by
    change fderiv ℝ (fun z => P z a) y₀ u = _
    rw [fderiv_clm_apply hP (differentiableAt_const a)]
    simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, fderiv_snd] at hval
  rw [hcol]
  simpa [ContinuousLinearMap.fst, ContinuousLinearMap.snd,
    coefficientLinearField_apply, add_comm] using hval

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryCoefficientChartDerivative
