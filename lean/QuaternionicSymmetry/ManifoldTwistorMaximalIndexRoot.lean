import QuaternionicSymmetry.ManifoldTwistorContactDegreeGenerator
import QuaternionicSymmetry.HolomorphicLinePositivePrimitiveRoot
import QuaternionicSymmetry.HolomorphicPositiveLineKodairaSource

/-! In the contact-coordinate-two branch, construct an actual ample
primitive line whose `(2n+2)`-th power is the actual anticanonical line.
This is the internal input to the separately registered projective-space
index characterization, not an invocation or proof of that characterization. -/

namespace QuaternionicSymmetry.ManifoldTwistorMaximalIndexRoot

open ManifoldPositiveQuaternionicKahlerGeometry ManifoldTwistorSphereCore
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorContactDegreeGenerator
open GeneralComplexContactData HolomorphicLineCoreClasses
open HolomorphicLineCoreClassGroup HolomorphicLineTensorPowerClasses
open HolomorphicLineHermitianMetric HolomorphicLinePositivePrimitiveRoot
open HolomorphicPositiveLineKodairaSource HolomorphicLineCoreAmpleFiniteMap
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

theorem exists_ample_primitive_maximal_index_root
    (hGeneral : GeneralContactCanonicalTheorem.{0,0,0})
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0}) :
    letI := A.charts
    ∀ (e : Additive (CoreClass.{0} (B := SphereBundleTotal P.tangent)
          𝓘(ℂ,ComplexTwistorModel n)) ≃+ ℤ),
      e (Additive.ofMul (contactClass P.tangent P.connection C.contact.line)) = 2 →
      ∀ (m : HermitianLineMetric (anticanonicalLineCore P.tangent P.connection A)),
        m.PositiveChernCurvature (anticanonicalLineCore P.tangent P.connection A) →
        ∃ H : LineCore.{0} (B := SphereBundleTotal P.tangent) 𝓘(ℂ,ComplexTwistorModel n),
          e (Additive.ofMul (Quotient.mk _ H)) = 1 ∧
          Function.Bijective (fun r : ℤ =>
            (Quotient.mk _ H : CoreClass 𝓘(ℂ,ComplexTwistorModel n)) ^ r) ∧
          Isomorphic 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) H (2*n+2))
            (anticanonicalLineCore P.tangent P.connection A) ∧
          AmpleCore 𝓘(ℂ,ComplexTwistorModel n) H := by
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  intro e he m hm
  have hcoord : e (Additive.ofMul
      (Quotient.mk _ (anticanonicalLineCore P.tangent P.connection A))) =
      ((2*n+2 : ℕ) : ℤ) := by
    change e (Additive.ofMul (anticanonicalClass P.tangent P.connection A)) = _
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      anticanonical_coordinate_of_contact_two P C hGeneral e he
  obtain ⟨H, hH, hbij, hIso, mH, hmH⟩ :=
    exists_positive_primitive_root (anticanonicalLineCore P.tangent P.connection A)
      e (2*n+2) (by omega) hcoord m hm
  exact ⟨H, hH, hbij, hIso, ampleCore_of_positiveHermitian hKodaira H mH hmH⟩

end
end QuaternionicSymmetry.ManifoldTwistorMaximalIndexRoot
