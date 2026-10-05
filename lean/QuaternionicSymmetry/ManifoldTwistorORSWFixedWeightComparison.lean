import QuaternionicSymmetry.GeneralContactFanoORSWRecognitionSource
import QuaternionicSymmetry.ManifoldQuaternionicBWWLinearizationComparison
import QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusAction

/-! The compact canonical quotient derivative has exactly the actual vertical
fixed weights, on the same genuine twistor and original contact line. This
comparison does not require selecting a complexified action or line gauge. -/
namespace QuaternionicSymmetry.ManifoldTwistorORSWFixedWeightComparison

open GeneralContactFanoORSWRecognitionSource
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicHolomorphicContactFiberAction
open ManifoldQuaternionicContactIsotropyScalar ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicVerticalCircleCharacter ManifoldQuaternionicActualWeightHull
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicMaximalTorusAction ManifoldQuaternionicSpanSymmetry
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : NondegenerateHolomorphicContactData Q D n B)
  {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries Q) r)

/-- The literal compact torus permutation action on the geometric twistor. -/
def compactTwistorAction : Torus r →* Equiv.Perm (SphereBundleTotal Q) where
  toFun t := MulAction.toPerm (T.hom t)
  map_one' := by ext z; simp
  map_mul' s t := by ext z; simp [mul_smul]

/-- The intrinsic, unpowered contact quotient lift of the compact action. -/
def compactContactFiberEquiv (t : Torus r) (z : SphereBundleTotal Q) :
    C.contact.line.core.Fiber z ≃ₗ[ℂ]
      C.contact.line.core.Fiber (compactTwistorAction Q T t z) :=
  contactLineFiberEquiv Q D C.contact.line (T.hom t) z

/-- The derivative law fixes the character normalization of the same line. -/
theorem compactContactFiberEquiv_isCanonical :
    IsCanonicalContactLift (𝓘(ℝ,E).prod (𝓡 2)) C.toGeneralContactGeometry
      (compactTwistorAction Q T) (compactContactFiberEquiv Q D B C T) := by
  intro t z v
  exact contactLineFiberMap_contactFormReal Q D C.contact.line (T.hom t) z v

/-- A literal fixed character agrees with the geometric vertical character. -/
theorem fixedFiberCharacter_iff_vertical
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M]
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (z : SphereBundleTotal Q)
    (hz : ∀ t, (actionOfEmbedding Q T).representation t • z = z)
    (μ : Fin r → ℤ) :
    FixedFiberCharacter (𝓘(ℝ,E).prod (𝓡 2)) C.toGeneralContactGeometry
      (compactTwistorAction Q T) (compactContactFiberEquiv Q D B C T) z μ ↔
    ∀ t, torusVerticalCircleCharacter Q hR3 (actionOfEmbedding Q T) z hz t =
      weightCharacter μ t := by
  constructor
  · intro h t
    have hscalar := congrArg
      (fun v : Bundle.TotalSpace ℂ C.contact.line.core.Fiber => (v.2 : ℂ))
      (h t (1 : ℂ))
    change contactScalar Q D C.contact.line (T.hom t) z =
      (weightCharacter μ t : ℂ) * (1 : ℂ) at hscalar
    rw [mul_one,contactScalar_eq_verticalScalar Q D C.contact.line z
      (T.hom t) (hz t)] at hscalar
    exact Subtype.ext hscalar
  · intro h t v
    change ℂ at v
    have hc : contactScalar Q D C.contact.line (T.hom t) z =
        (weightCharacter μ t : ℂ) := by
      rw [contactScalar_eq_verticalScalar Q D C.contact.line z (T.hom t) (hz t)]
      exact congrArg (fun c : Circle => (c : ℂ)) (h t)
    change contactLineFiberEquiv Q D C.contact.line (T.hom t) z (1 : ℂ) =
      (weightCharacter μ t : ℂ) at hc
    have hlin : contactLineFiberEquiv Q D C.contact.line (T.hom t) z v =
        (weightCharacter μ t : ℂ) * v := by
      have hm := (contactLineFiberEquiv Q D C.contact.line (T.hom t) z).map_smul
        (show ℂ from v) (1 : ℂ)
      simpa [hc,smul_eq_mul,mul_comm] using hm
    refine Bundle.TotalSpace.ext (hz t) ?_
    exact heq_of_eq (by simpa only [smul_eq_mul] using hlin)

/-- The actual unpowered fiber-weight polytope uses the same real weight set
as the fixed quaternionic geometry and section/root-space development. -/
theorem realFixedFiberWeights_eq_actual
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M]
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0}) :
    realFixedFiberWeights (𝓘(ℝ,E).prod (𝓡 2)) C.toGeneralContactGeometry
      (compactTwistorAction Q T) (compactContactFiberEquiv Q D B C T) =
      actualRealWeights Q hR3 (actionOfEmbedding Q T) := by
  ext w
  constructor
  · rintro ⟨z,μ,hEq,hWeight⟩
    have hz : ∀ t, (actionOfEmbedding Q T).representation t • z = z := by
      intro t
      exact congrArg Bundle.TotalSpace.proj (hWeight t (0 : ℂ))
    exact ⟨μ,⟨z,hz,(fixedFiberCharacter_iff_vertical Q D B C T hR3 z hz μ).mp hWeight⟩,
      hEq.symm⟩
  · rintro ⟨μ,⟨z,hz,hμ⟩,hEq⟩
    exact ⟨z,μ,hEq.symm,(fixedFiberCharacter_iff_vertical Q D B C T hR3 z hz μ).mpr hμ⟩


/-- Geometric isolation transfers to the literal ORSW hypothesis without
changing the component or its unpowered fixed weight polytope. -/
theorem isolatedExtremalComponents_of_actual
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M]
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hIso : ∀ (z : SphereBundleTotal Q)
      (hz : ∀ t, (actionOfEmbedding Q T).representation t • z = z)
      (μ : Fin r → ℤ),
      (∀ t, torusVerticalCircleCharacter Q hR3 (actionOfEmbedding Q T) z hz t =
        weightCharacter μ t) →
      (fun i => (μ i : ℝ)) ∈
        (convexHull ℝ (actualRealWeights Q hR3 (actionOfEmbedding Q T))).extremePoints ℝ →
      (component Q (actionOfEmbedding Q T) z).Subsingleton) :
    HasIsolatedExtremalComponents (𝓘(ℝ,E).prod (𝓡 2)) C.toGeneralContactGeometry
      (compactTwistorAction Q T) (compactContactFiberEquiv Q D B C T) := by
  intro z μ hz hWeight hExtreme
  have hzA : ∀ t, (actionOfEmbedding Q T).representation t • z = z := hz
  have hChar := (fixedFiberCharacter_iff_vertical Q D B C T hR3 z hzA μ).mp hWeight
  rw [realFixedFiberWeights_eq_actual Q D B C T hR3] at hExtreme
  have hPoint := hIso z hzA μ hChar hExtreme
  have hFixed : {x : SphereBundleTotal Q | ∀ t, compactTwistorAction Q T t x = x} =
      ManifoldQuaternionicTwistorLiftedFixedSet.fixedSpherePoints Q
        (actionOfEmbedding Q T).imageSubgroup := by
    ext x
    exact (mem_fixedSpherePoints_iff_torus Q (actionOfEmbedding Q T) x).symm
  rw [hFixed]
  exact hPoint

end
end QuaternionicSymmetry.ManifoldTwistorORSWFixedWeightComparison
