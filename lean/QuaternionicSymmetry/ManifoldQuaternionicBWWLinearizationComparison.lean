import QuaternionicSymmetry.GeneralBWWAnalyticExtremalSource
import QuaternionicSymmetry.ManifoldTwistorComplexContactLinearization
import QuaternionicSymmetry.ManifoldQuaternionicContactIsotropyScalar
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismIsometrySections
import QuaternionicSymmetry.ManifoldQuaternionicTorusFixedComplexComponent
import QuaternionicSymmetry.ManifoldQuaternionicActualWeightHull

/-! Literal action, fiber-weight and fixed-set comparison for the universal
analytic BWW application. The same complex torus, original contact line
and connected component are retained. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicBWWLinearizationComparison
open GeneralBWWAnalyticExtremalSource ManifoldTwistorComplexContactLinearization
open ManifoldTwistorComplexContactAction ManifoldTwistorContactAutomorphismFiber
open ManifoldTwistorContactAutomorphismIsometrySections
open ManifoldQuaternionicContactIsotropyScalar ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicVerticalCircleCharacter ManifoldQuaternionicActualWeightHull
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLineCoreClasses HolomorphicLineComplexTorusLinearization
open TorusLaurentRepresentation TorusIntegralVertexExposure
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


theorem actual_fixedSet_eq :
    letI := B.charts
    fixedSet (contactLineCore Q D C.line)
      (actualContactLineLinearization Q D B C A ρ hJoint hRestrict) =
      fixedSpherePoints Q A.imageSubgroup := by
  letI := B.charts
  ext z
  rw [mem_fixedSpherePoints_iff_torus]
  change (∀ t, ρ (compactInclusion r t) z = z) ↔ _
  simp only [hRestrict]

theorem actual_hasFiberWeight
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (z : SphereBundleTotal Q) (hz : ∀ t, A.representation t • z = z)
    (ν : Fin r → ℤ)
    (hν : ∀ t, torusVerticalCircleCharacter Q hR3 A z hz t = weightCharacter ν t) :
    letI := B.charts
    HasFiberWeight (contactLineCore Q D C.line)
      (actualContactLineLinearization Q D B C A ρ hJoint hRestrict) z ν := by
  letI := B.charts
  refine ⟨?_,?_⟩
  · intro t
    exact (hRestrict t z).trans (hz t)
  · intro t v
    change ℂ at v
    change (⟨ρ (compactInclusion r t) z,
      contactFiberEquiv Q D B C.line
        (complexContactAction Q D B C A ρ hJoint hRestrict (compactInclusion r t)) z v⟩ :
        Bundle.TotalSpace ℂ C.line.core.Fiber) = ⟨z,(weightCharacter ν t : ℂ) • v⟩
    rw [complexContactAction_compact, contactFiberEquiv_isometry]
    have hc : contactScalar Q D C.line (A.representation t) z =
        (weightCharacter ν t : ℂ) := by
      rw [contactScalar_eq_verticalScalar Q D C.line z (A.representation t) (hz t)]
      exact congrArg (fun c : Circle => (c : ℂ)) (hν t)
    change contactLineFiberEquiv Q D C.line (A.representation t) z (1 : ℂ) =
      (weightCharacter ν t : ℂ) at hc
    have hlin : contactLineFiberEquiv Q D C.line (A.representation t) z v =
        (weightCharacter ν t : ℂ) * v := by
      have hm := (contactLineFiberEquiv Q D C.line (A.representation t) z).map_smul v (1 : ℂ)
      simpa [hc, smul_eq_mul, mul_comm] using hm
    refine Bundle.TotalSpace.ext ((hRestrict t z).trans (hz t)) ?_
    exact heq_of_eq (by simpa only [smul_eq_mul] using hlin)

 theorem actual_fixedWeights_eq
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0}) :
    letI := B.charts
    fixedWeights (contactLineCore Q D C.line)
      (actualContactLineLinearization Q D B C A ρ hJoint hRestrict) =
      actualRealWeights Q hR3 A := by
  letI := B.charts
  ext w
  constructor
  · rintro ⟨z,ν,hWeight,hEq⟩
    have hz : ∀ t, A.representation t • z = z := by
      intro t
      exact (hRestrict t z).symm.trans (hWeight.1 t)
    refine ⟨ν,⟨z,hz,?_⟩,hEq⟩
    intro t
    have hv := hWeight.2 t (1 : ℂ)
    have hscalar := congrArg
      (fun v : Bundle.TotalSpace ℂ C.line.core.Fiber => (v.2 : ℂ)) hv
    change contactFiberEquiv Q D B C.line
      (complexContactAction Q D B C A ρ hJoint hRestrict (compactInclusion r t)) z
      (1 : ℂ) = (weightCharacter ν t : ℂ) • (1 : ℂ) at hscalar
    rw [complexContactAction_compact, contactFiberEquiv_isometry] at hscalar
    change contactScalar Q D C.line (A.representation t) z =
      (weightCharacter ν t : ℂ) * (1 : ℂ) at hscalar
    rw [mul_one, contactScalar_eq_verticalScalar Q D C.line z
      (A.representation t) (hz t)] at hscalar
    exact Subtype.ext hscalar
  · rintro ⟨ν,⟨z,hz,hν⟩,hEq⟩
    exact ⟨z,ν,actual_hasFiberWeight Q D B C A ρ hJoint hRestrict hR3 z hz ν hν,hEq⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicBWWLinearizationComparison
