import QuaternionicSymmetry.ManifoldQuaternionicBWWLinearizationComparison
import QuaternionicSymmetry.ManifoldQuaternionicContactComponentRestriction
import QuaternionicSymmetry.ManifoldTwistorComplexContactLinearizationFromSources

/-! Actual application of the separately disclosed universal analytic BWW
corollary. The fixed-component atlas, line, fiber weight and restriction map
are the original objects. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicBWWExtremalApplication
open GeneralBWWAnalyticExtremalSource ManifoldQuaternionicBWWLinearizationComparison
open ManifoldTwistorComplexContactLinearization
open ManifoldQuaternionicContactComponentRestriction
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicActualWeightHull ManifoldQuaternionicVerticalCircleCharacter
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLineCoreClasses HolomorphicLineComplexTorusLinearization
open HolomorphicLineCorePullback HolomorphicLineCoreClasses
open HolomorphicLineCoreAmpleFiniteMap TorusLaurentRepresentation TorusIntegralVertexExposure
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M]
  [SecondCountableTopology M] [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)
  {r : ℕ} (A : ContinuousTorusAction Q r)
  (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal Q))
  (hJoint : letI := B.charts
    ContMDiff (𝓘(ℂ,Fin r → ℂ).prod 𝓘(ℂ,ComplexTwistorModel n))
      𝓘(ℂ,ComplexTwistorModel n) ∞
      (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2))
  (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal Q),
    ρ (compactInclusion r t) z = sphereTotalMap Q (A.representation t) z)



include hJoint hRestrict in
theorem actual_extremal_restriction_and_small_sections
    (hBWW : AnalyticExtremalRestrictionAndSmallSections)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hr : 0 < r)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (hPic : letI := B.charts
      Function.Bijective (fun m : ℤ =>
        (Quotient.mk _ (contactLineCore Q D C.line) :
          CoreClass.{0} (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n)) ^ m))
    (hFaith : Function.Injective ρ)
    (z : SphereBundleTotal Q) (hz : ∀ t, A.representation t • z = z)
    (ν : Fin r → ℤ)
    (hν : ∀ t, torusVerticalCircleCharacter Q hR3 A z hz t = weightCharacter ν t)
    (hExt : realWeight ν ∈ (convexHull ℝ (actualRealWeights Q hR3 A)).extremePoints ℝ)
    {b : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin b)) (↥(component Q A z))]
    [IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞ (↥(component Q A z))]
    (hIncl : letI := B.charts
      ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) 𝓘(ℂ,ComplexTwistorModel n) ∞
        (Subtype.val : ↥(component Q A z) → SphereBundleTotal Q))
    (hImm : letI := B.charts
      ∀ y, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin b))
        𝓘(ℝ,ComplexTwistorModel n)
        (Subtype.val : ↥(component Q A z) → SphereBundleTotal Q) y)) :
    letI := B.charts
    Function.Surjective (contactRestriction Q A D B C z hIncl) ∧
    (0 < b → b ≤ 3 → 2 ≤ Module.finrank ℂ
      (RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,EuclideanSpace ℂ (Fin b)) (contactLineCore Q D C.line)
        (Subtype.val : ↥(component Q A z) → SphereBundleTotal Q) hIncl)) := by
  letI := B.charts
  letI := B.complexManifold
  letI : ConnectedSpace M := {
    toPreconnectedSpace := inferInstance
    toNonempty := inferInstance }
  let a := actualContactLineLinearization Q D B C A ρ hJoint hRestrict
  have hFiber := actual_hasFiberWeight Q D B C A ρ hJoint hRestrict hR3 z hz ν hν
  have hExt' : realWeight ν ∈
      (convexHull ℝ (fixedWeights (contactLineCore Q D C.line) a)).extremePoints ℝ := by
    rw [actual_fixedWeights_eq Q D B C A ρ hJoint hRestrict hR3]
    exact hExt
  have hY : component Q A z = connectedComponentIn
      (fixedSet (contactLineCore Q D C.line) a) z := by
    rw [actual_fixedSet_eq Q D B C A ρ hJoint hRestrict]
    rfl
  have hs := hBWW (contactLineCore Q D C.line) hr hAmple hPic a hFaith z ν hFiber hExt' (component Q A z) hY (b := b)
  exact hs inferInstance inferInstance hIncl hImm

theorem actual_extremal_restriction_and_small_sections_from_sources
    (hBWW : AnalyticExtremalRestrictionAndSmallSections)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (hCircle : TorusCharacterInput.CircleCharacterSource)
    (hLee : GeneralSmoothMapSource.LeeEmbeddedCodomainRestrictionTheorem)
    (hr : 0 < r)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (hPic : letI := B.charts
      Function.Bijective (fun m : ℤ =>
        (Quotient.mk _ (contactLineCore Q D C.line) :
          CoreClass.{0} (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n)) ^ m))
    (hFaithful : A.Faithful)
    (z : SphereBundleTotal Q) (hz : ∀ t, A.representation t • z = z)
    (ν : Fin r → ℤ)
    (hν : ∀ t, torusVerticalCircleCharacter Q hR3 A z hz t = weightCharacter ν t)
    (hExt : realWeight ν ∈ (convexHull ℝ (actualRealWeights Q hR3 A)).extremePoints ℝ)
    {b : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin b)) (↥(component Q A z))]
    [IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞ (↥(component Q A z))]
    (hIncl : letI := B.charts
      ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) 𝓘(ℂ,ComplexTwistorModel n) ∞
        (Subtype.val : ↥(component Q A z) → SphereBundleTotal Q))
    (hImm : letI := B.charts
      ∀ y, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin b))
        𝓘(ℝ,ComplexTwistorModel n)
        (Subtype.val : ↥(component Q A z) → SphereBundleTotal Q) y)) :
    letI := B.charts
    Function.Surjective (contactRestriction Q A D B C z hIncl) ∧
    (0 < b → b ≤ 3 → 2 ≤ Module.finrank ℂ
      (RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,EuclideanSpace ℂ (Fin b)) (contactLineCore Q D C.line)
        (Subtype.val : ↥(component Q A z) → SphereBundleTotal Q) hIncl)) := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨ρ,hJoint,hRestrict,hFaith,_⟩ :=
    ManifoldTwistorComplexContactLinearizationFromSources.exists_faithful_actualContactLineLinearization
      Q hR3 hFinite hEigen hCircle hLee A hFaithful D B C hAmple
  exact actual_extremal_restriction_and_small_sections Q D B C A ρ hJoint hRestrict
    hBWW hR3 hr hAmple hPic hFaith z hz ν hν hExt hIncl hImm

end
end QuaternionicSymmetry.ManifoldQuaternionicBWWExtremalApplication
