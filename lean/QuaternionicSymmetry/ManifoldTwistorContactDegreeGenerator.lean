import QuaternionicSymmetry.ManifoldTwistorSWExponentialCohomology
import QuaternionicSymmetry.ManifoldTwistorCanonicalClassGroup
import QuaternionicSymmetry.HolomorphicLineDegreeGenerator

/-! The internal Picard-generator deduction on the actual contact twistor.
Registered SW vanishings and the constructed line/cohomology equivalence
remove the analytic vanishing hypotheses. Simple connectedness, rank one
and a genuine degree-two restriction map remain explicit obligations.
Finite generation is deduced, not assumed. The coordinate-two branch is
not identified with projective space in this file. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactDegreeGenerator

open ManifoldPositiveQuaternionicKahlerGeometry ManifoldTwistorSphereCore
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorCanonicalClassGroup
open GeneralComplexContactData HolomorphicExponentialCohomology
open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open HolomorphicLineDegreeGenerator
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

theorem contactClass_coordinate_one_or_two
    (hSW : SWCohomologicalSource.{0,0,1})
    (hGeneral : GeneralContactCanonicalTheorem.{0,0,0})
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n)
    (hSC : SimplyConnectedSpace (SphereBundleTotal P.tangent))
    (hRank : Module.finrank ℤ
      (integralCohomology (B := SphereBundleTotal P.tangent) 2) = 1) :
    letI := A.charts
    ∀ (degree : Additive (CoreClass.{0} (B := SphereBundleTotal P.tangent)
        𝓘(ℂ,ComplexTwistorModel n)) →+ ℤ),
      degree (Additive.ofMul (contactClass P.tangent P.connection C.contact.line)) = 2 →
      ∃ e : Additive (CoreClass.{0} (B := SphereBundleTotal P.tangent)
          𝓘(ℂ,ComplexTwistorModel n)) ≃+ ℤ,
        e (Additive.ofMul (contactClass P.tangent P.connection C.contact.line)) = 1 ∨
        e (Additive.ofMul (contactClass P.tangent P.connection C.contact.line)) = 2 := by
  letI := A.charts
  letI := hSC
  letI : LocPathConnectedSpace (SphereBundleTotal P.tangent) :=
    ChartedSpace.locPathConnectedSpace (ComplexTwistorModel n) _
  intro degree hDegree
  exact exists_coordinate_one_or_two_of_degree 𝓘(ℂ,ComplexTwistorModel n)
    (swFunctionCohomology_subsingleton P C hSW hGeneral hn hDim 1 (by omega) (by omega))
    (swFunctionCohomology_subsingleton P C hSW hGeneral hn hDim 2 (by omega) (by omega))
    hRank degree (contactClass P.tangent P.connection C.contact.line) hDegree

/-- In the coordinate-two branch, the actual anticanonical class has
integer coordinate `2n+2`. This is the numerical input to the separate
projective-space index characterization, not that characterization itself. -/
theorem anticanonical_coordinate_of_contact_two
    (hGeneral : GeneralContactCanonicalTheorem.{0,0,0}) :
    letI := A.charts
    ∀ (e : Additive (CoreClass.{0} (B := SphereBundleTotal P.tangent)
          𝓘(ℂ,ComplexTwistorModel n)) ≃+ ℤ),
      e (Additive.ofMul (contactClass P.tangent P.connection C.contact.line)) = 2 →
      e (Additive.ofMul (anticanonicalClass P.tangent P.connection A)) =
        2 * (n : ℤ) + 2 := by
  letI := A.charts
  intro e he
  rw [anticanonicalClass_eq_contactClass_pow_of_generalContact
    P.tangent P.connection hGeneral C, ofMul_pow, map_nsmul, he]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

end
end QuaternionicSymmetry.ManifoldTwistorContactDegreeGenerator
