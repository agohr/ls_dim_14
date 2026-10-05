import QuaternionicSymmetry.ManifoldTwistorMaximalIndexRoot
import QuaternionicSymmetry.HolomorphicLineCoordinatePowerGauge

/-! Internal geometric Picard dichotomy: the actual contact class generates,
or a genuine ample primitive line squares to the contact line and has
anticanonical power `2n+2`. The actual simple-connectedness, integral rank
and fiber-degree hypotheses are not discharged here; the second branch is
not yet identified with projective space. -/

namespace QuaternionicSymmetry.ManifoldTwistorPicardDichotomy

open ManifoldPositiveQuaternionicKahlerGeometry ManifoldTwistorSphereCore
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorContactDegreeGenerator ManifoldTwistorMaximalIndexRoot
open GeneralComplexContactData HolomorphicExponentialCohomology
open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open HolomorphicLineTensorPowerClasses HolomorphicLineHermitianMetric
open HolomorphicPositiveLineKodairaSource HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineCoordinatePowerGauge FiniteRankOneAbelian
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
  {n : ℕ} {A : CompatibleComplexAtlas P.tangent P.connection n}
  (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)

theorem contact_generator_or_ample_maximal_index_root
    (hSW : SWCohomologicalSource.{0,0,1})
    (hGeneral : GeneralContactCanonicalTheorem.{0,0,0})
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hSC : SimplyConnectedSpace (SphereBundleTotal P.tangent))
    (hRank : Module.finrank ℤ
      (integralCohomology (B := SphereBundleTotal P.tangent) 2) = 1) :
    letI := A.charts
    ∀ (degree : Additive (CoreClass.{0} (B := SphereBundleTotal P.tangent)
        𝓘(ℂ,ComplexTwistorModel n)) →+ ℤ),
      degree (Additive.ofMul (contactClass P.tangent P.connection C.contact.line)) = 2 →
      ∀ (m : HermitianLineMetric (anticanonicalLineCore P.tangent P.connection A)),
        m.PositiveChernCurvature (anticanonicalLineCore P.tangent P.connection A) →
        Function.Bijective (fun r : ℤ =>
          (contactClass P.tangent P.connection C.contact.line) ^ r) ∨
        ∃ H : LineCore.{0} (B := SphereBundleTotal P.tangent) 𝓘(ℂ,ComplexTwistorModel n),
          Function.Bijective (fun r : ℤ =>
            (Quotient.mk _ H : CoreClass 𝓘(ℂ,ComplexTwistorModel n)) ^ r) ∧
          Isomorphic 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) H 2)
            (contactLineCore P.tangent P.connection C.contact.line) ∧
          Isomorphic 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) H (2*n+2))
            (anticanonicalLineCore P.tangent P.connection A) ∧
          AmpleCore 𝓘(ℂ,ComplexTwistorModel n) H := by
  letI := A.charts
  intro degree hDegree m hm
  obtain ⟨e, he | he⟩ := contactClass_coordinate_one_or_two P C
    hSW hGeneral hn hDim hSC hRank degree hDegree
  · exact Or.inl (zsmul_bijective_of_coordinate_one e
      (Additive.ofMul (contactClass P.tangent P.connection C.contact.line)) he)
  · obtain ⟨H,hH,hbij,hAnti,hAmple⟩ :=
      exists_ample_primitive_maximal_index_root P C hGeneral hKodaira e he m hm
    have hContact := isomorphic_power_of_coordinate H
      (contactLineCore P.tangent P.connection C.contact.line) e hH 2 he
    exact Or.inr ⟨H,hbij,hContact,hAnti,hAmple⟩

end
end QuaternionicSymmetry.ManifoldTwistorPicardDichotomy
