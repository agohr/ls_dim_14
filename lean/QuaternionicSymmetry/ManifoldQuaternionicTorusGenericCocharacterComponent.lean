import QuaternionicSymmetry.ComplexProjectiveImageGenericFixedComponent
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerProjectiveEquivariance
import QuaternionicSymmetry.ManifoldQuaternionicTorusFixedComplexComponent

/-! A separating integral cocharacter in the genuine contact-power
projective embedding fixes exactly the same *literal twistor component*
as the original compact torus. The projective embedding, homogeneous
equations, and eigenbasis are explicit inputs here; their existence is
proved elsewhere from actual ampleness and the registered analytic sources.
No Białynicki–Birula source/attracting-cell assertion occurs here. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTorusGenericCocharacterComponent

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexProjectivePolynomialLocus ComplexProjectiveImageTorusAction
open ComplexProjectiveImageGenericFixedComponent
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicContactPowerProjectiveEquivariance
open ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicContactPowerContinuity
open ManifoldQuaternionicContactPowerWeights
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses HolomorphicLineCoreProjectiveEvaluation
open TorusLaurentRepresentation TorusIntegralCocharacter TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Equality is on the genuine connected fixed component of the actual
twistor sphere, not on a chosen model for it. The cocharacter acts through
the independently built invariant-image Laurent action. -/
theorem exists_generic_cocharacter_same_actual_component
    {r d : ℕ} (T : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (b : letI := B.charts;
      Module.Basis (Fin (d + 1)) ℂ (PowerSections Q D B C k))
    (hGen : letI := B.charts;
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k))
    (μ : Fin (d + 1) → Fin r → ℤ)
    (hEig : letI := B.charts; ∀ (t : Torus r) (i : Fin (d + 1)),
      contactPowerTorusRepresentation Q T D B C k t (b i) =
        (weightCharacter (μ i) t : ℂ) • b i)
    (hEmb : letI := B.charts;
      Topology.IsEmbedding (projectiveEvaluationOfGenerated
        𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k) d b hGen))
    (hA : letI := B.charts;
      HasHomogeneousEquations (Set.range (projectiveEvaluationOfGenerated
        𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k) d b hGen)))
    (z : SphereBundleTotal Q) :
    letI := B.charts
    let f := projectiveEvaluationOfGenerated
      𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line) k) d b hGen
    let α : Torus r → SphereBundleTotal Q → SphereBundleTotal Q :=
      fun t x => sphereTotalMap Q (T.representation t) x
    let hα : ∀ t x, f (α t x) =
        projectiveAction (fun i => -(μ i)) (compactInclusion r t) (f x) :=
      fun t x => contactPower_projectiveEvaluation_diagonal_compact
        Q T D B C k b hGen μ hEig t x
    ∃ u : Fin r → ℤ,
      connectedComponentIn
        {x : SphereBundleTotal Q | ∀ w : ℂˣ,
          imageAction (fun i => -(μ i)) f hEmb.injective hA α hα
            (cocharacter u w) x = x} z =
      component Q T z := by
  letI := B.charts
  let f := projectiveEvaluationOfGenerated
    𝓘(ℂ,ComplexTwistorModel n)
    (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore Q D C.line) k) d b hGen
  let α : Torus r → SphereBundleTotal Q → SphereBundleTotal Q :=
    fun t x => sphereTotalMap Q (T.representation t) x
  let hα : ∀ t x, f (α t x) =
      projectiveAction (fun i => -(μ i)) (compactInclusion r t) (f x) :=
    fun t x => contactPower_projectiveEvaluation_diagonal_compact
      Q T D B C k b hGen μ hEig t x
  obtain ⟨u,hu⟩ := exists_cocharacter_same_image_fixed_component
    (fun i => -(μ i)) f hEmb.injective hA α hα z
  refine ⟨u,?_⟩
  rw [hu]
  congr 1
  ext x
  simpa only [Set.mem_setOf_eq, α] using
    (mem_fixedSpherePoints_iff_torus Q T x).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicTorusGenericCocharacterComponent
