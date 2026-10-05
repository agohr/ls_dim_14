import QuaternionicSymmetry.ManifoldQuaternionicJointMovingDerivative

/-! Joint continuity of the actual moving isometry derivative after passing
to two frozen adapted quaternionic frames. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicJointMovingAdaptedDerivative

open Manifold
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicJointMovingDerivative
open ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicIsometryTopology
open ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The derivative of a moving isometry expressed in the two adapted
frames fixed at the chosen source and target chart centers. -/
def movingAdaptedDerivative (f₀ : QuaternionicIsometries Q) (x₀ : M)
    (p : QuaternionicIsometries Q × M) : E →L[ℝ] E :=
  (Q.frames.toFrame (achart E (f₀ • x₀)) (p.1 • p.2)).comp
    (((tangentBundleCore 𝓘(ℝ,E) M).coordChange
      (achart E (p.1 • p.2)) (achart E (f₀ • x₀)) (p.1 • p.2)).comp
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (p.1.1 : M → M) p.2).comp
        (((tangentBundleCore 𝓘(ℝ,E) M).coordChange
          (achart E x₀) (achart E p.2) p.2).comp
          (Q.frames.fromFrame (achart E x₀) p.2))))

/-- BG-R3 proves joint continuity of the actual moving adapted derivative
at every isometry and point. The chart centers remain fixed while `(f,x)`
varies; no isotropy or common-fixed-point hypothesis is used. -/
theorem continuousAt_movingAdaptedDerivative
    (hR3 : IsometryLieSource.{0,0})
    (f₀ : QuaternionicIsometries Q) (x₀ : M) :
    ContinuousAt (movingAdaptedDerivative Q f₀ x₀) (f₀,x₀) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  obtain ⟨V, hNorm, hSpace, hFinite, hChart,
    hManifold, hLie, hAction⟩ := hR3 Q
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  let g₀ := toFullMetricIsometry Q f₀
  let A : QuaternionicIsometries Q × M → E →L[ℝ] E := fun p =>
    (inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
      (fun q : (M ≃ᵢ M) × M => q.1 q.2)
      (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
        (fun q : (M ≃ᵢ M) × M => q.1 q.2))
      (g₀,x₀) (toFullMetricIsometry Q p.1,p.2)).comp
      (ContinuousLinearMap.inr ℝ V E)
  have hA : ContinuousAt A (f₀,x₀) :=
    continuousAt_actionPartialX_along_families Q hChart hManifold hAction
      (toFullMetricIsometry Q) (toFullMetricIsometry_continuous Q)
      id continuous_id f₀ x₀
  let F : QuaternionicIsometries Q × M → E →L[ℝ] E := fun p =>
    (Q.frames.toFrame (achart E (f₀ • x₀)) (p.1 • p.2)).comp
      ((A p).comp (Q.frames.fromFrame (achart E x₀) p.2))
  have hbase : ContinuousAt (fun p : QuaternionicIsometries Q × M =>
      p.1 • p.2) (f₀,x₀) := (continuous_action Q).continuousAt
  have hto : ContinuousAt (Q.frames.toFrame (achart E (f₀ • x₀))) (f₀ • x₀) :=
    (Q.frames.smooth_to _).continuousOn.continuousAt
      ((Q.frames.adaptedCore.isOpen_baseSet _).mem_nhds
        (Q.frames.adaptedCore.mem_baseSet_at _))
  have hfrom : ContinuousAt (Q.frames.fromFrame (achart E x₀)) x₀ :=
    (Q.frames.smooth_from _).continuousOn.continuousAt
      ((Q.frames.adaptedCore.isOpen_baseSet _).mem_nhds
        (Q.frames.adaptedCore.mem_baseSet_at _))
  have hto' : ContinuousAt (fun p : QuaternionicIsometries Q × M =>
      Q.frames.toFrame (achart E (f₀ • x₀)) (p.1 • p.2)) (f₀,x₀) :=
    ContinuousAt.comp (f := fun p : QuaternionicIsometries Q × M => p.1 • p.2)
      (x := (f₀,x₀)) hto hbase
  have hfrom' : ContinuousAt (fun p : QuaternionicIsometries Q × M =>
      Q.frames.fromFrame (achart E x₀) p.2) (f₀,x₀) :=
    ContinuousAt.comp (f := Prod.snd) (x := (f₀,x₀)) hfrom continuousAt_snd
  have hF : ContinuousAt F (f₀,x₀) :=
    hto'.clm_comp (hA.clm_comp hfrom')
  have hgroup : ∀ᶠ p : QuaternionicIsometries Q × M in nhds (f₀,x₀),
      toFullMetricIsometry Q p.1 ∈ (chartAt V g₀).source := by
    exact ((chartAt V g₀).open_source.preimage
      ((toFullMetricIsometry_continuous Q).comp continuous_fst)).mem_nhds
        (mem_chart_source V g₀)
  have hsource : ∀ᶠ p : QuaternionicIsometries Q × M in nhds (f₀,x₀),
      p.2 ∈ (chartAt E x₀).source :=
    ((chartAt E x₀).open_source.preimage continuous_snd).mem_nhds
      (mem_chart_source E x₀)
  have htarget : ∀ᶠ p : QuaternionicIsometries Q × M in nhds (f₀,x₀),
      p.1 • p.2 ∈ (chartAt E (f₀ • x₀)).source :=
    ((chartAt E (f₀ • x₀)).open_source.preimage (continuous_action Q)).mem_nhds
      (mem_chart_source E (f₀ • x₀))
  apply hF.congr_of_eventuallyEq
  filter_upwards [hgroup, hsource, htarget] with p hg hs ht
  have hpart := jointPartial_eq_individualMovingCharts Q hChart hManifold hAction
    g₀ (toFullMetricIsometry Q p.1) x₀ p.2 hg hs (by simpa using ht)
  have hcong := congrArg (fun D : E →L[ℝ] E =>
    (Q.frames.toFrame (achart E (f₀ • x₀)) (p.1 • p.2)).comp
      (D.comp (Q.frames.fromFrame (achart E x₀) p.2))) hpart
  exact hcong.symm

/-- The reverse matrix is expressed in the same frozen pair of adapted
charts, with source and target interchanged. -/
def movingAdaptedInverseDerivative (f₀ : QuaternionicIsometries Q) (x₀ : M)
    (p : QuaternionicIsometries Q × M) : E →L[ℝ] E :=
  movingAdaptedDerivative Q f₀⁻¹ (f₀ • x₀) (p.1⁻¹, p.1 • p.2)

theorem continuousAt_movingAdaptedInverseDerivative
    (hR3 : IsometryLieSource.{0,0})
    (f₀ : QuaternionicIsometries Q) (x₀ : M) :
    ContinuousAt (movingAdaptedInverseDerivative Q f₀ x₀) (f₀,x₀) := by
  have hpair : ContinuousAt (fun p : QuaternionicIsometries Q × M =>
      (p.1⁻¹, p.1 • p.2)) (f₀,x₀) :=
    ((continuous_inv.comp continuous_fst).prodMk (continuous_action Q)).continuousAt
  have h := (continuousAt_movingAdaptedDerivative Q hR3 f₀⁻¹ (f₀ • x₀)).comp
    (f := fun p : QuaternionicIsometries Q × M => (p.1⁻¹, p.1 • p.2))
    (x := (f₀,x₀)) (by simpa only [inv_smul_smul] using hpair)
  exact h

/-- The SO(3) coefficient produced by forward and reverse moving adapted
derivatives in one fixed pair of quaternionic frames. -/
def movingCoefficientRotation (f₀ : QuaternionicIsometries Q) (x₀ : M)
    (a : Fin 3 → ℝ) (p : QuaternionicIsometries Q × M) : Fin 3 → ℝ :=
  coeff (Q.reduction.Q (achart E (f₀ • x₀)))
    ((movingAdaptedDerivative Q f₀ x₀ p).comp
      ((synth (Q.reduction.Q (achart E x₀)) a).comp
        (movingAdaptedInverseDerivative Q f₀ x₀ p)))

theorem continuousAt_movingCoefficientRotation
    (hR3 : IsometryLieSource.{0,0})
    (f₀ : QuaternionicIsometries Q) (x₀ : M) (a : Fin 3 → ℝ) :
    ContinuousAt (movingCoefficientRotation Q f₀ x₀ a) (f₀,x₀) := by
  have hforward := continuousAt_movingAdaptedDerivative Q hR3 f₀ x₀
  have hbackward := continuousAt_movingAdaptedInverseDerivative Q hR3 f₀ x₀
  have hconj : ContinuousAt (fun p : QuaternionicIsometries Q × M =>
      (movingAdaptedDerivative Q f₀ x₀ p).comp
        ((synth (Q.reduction.Q (achart E x₀)) a).comp
          (movingAdaptedInverseDerivative Q f₀ x₀ p))) (f₀,x₀) :=
    hforward.clm_comp (continuousAt_const.clm_comp hbackward)
  exact (coeff (Q.reduction.Q (achart E (f₀ • x₀)))).continuous.continuousAt.comp
    (f := fun p : QuaternionicIsometries Q × M =>
      (movingAdaptedDerivative Q f₀ x₀ p).comp
        ((synth (Q.reduction.Q (achart E x₀)) a).comp
          (movingAdaptedInverseDerivative Q f₀ x₀ p)))
    (x := (f₀,x₀)) hconj

end
end QuaternionicSymmetry.ManifoldQuaternionicJointMovingAdaptedDerivative
