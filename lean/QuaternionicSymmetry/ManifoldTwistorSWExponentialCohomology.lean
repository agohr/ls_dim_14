import QuaternionicSymmetry.ManifoldTwistorFunctionCohomology
import QuaternionicSymmetry.ManifoldTwistorSWSourceContract
import QuaternionicSymmetry.HolomorphicLineDerivedTensor

/-! The registered complex-cohomology source now implies the two actual
function-sheaf vanishings needed by the exponential sequence. Hence the
genuine tensor group of holomorphic line cores is isomorphic to actual
integral H². No new Picard or coefficient-comparison source is introduced;
the separate integral H² rank/generator computation remains open. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open ManifoldPositiveQuaternionicKahlerGeometry ManifoldTwistorSphereCore
open GeneralComplexContactData CategoryTheory TopologicalSpace
open HolomorphicExponentialCohomology HolomorphicLineCoreClasses
open HolomorphicLineCoreClassGroup
open scoped Manifold ContDiff
noncomputable section

local instance (X : TopCat.{0}) : HasExt.{1} (TopCat.Sheaf (ModuleCat.{0} ℂ) X) :=
  HasExt.standard _

variable {E M : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
  {n : ℕ} {A : CompatibleComplexAtlas P.tangent P.connection n}
  (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)

include C in
theorem swFunctionCohomology_subsingleton
    (hSW : SWCohomologicalSource.{0,0,1})
    (hGeneral : GeneralContactCanonicalTheorem.{0,0,0})
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n)
    (s : ℕ) (hs : 0 < s) (hs' : s ≤ 2 * n + 1) :
    letI := A.charts
    Subsingleton (functionCohomology (B := SphereBundleTotal P.tangent)
      𝓘(ℂ, ComplexTwistorModel n) s) := by
  letI := A.charts
  exact functionCohomology_subsingleton_of_zeroTwist
    P.tangent P.connection C.contact.line s
      ((swCohomology_of_generalContact P C hSW hGeneral hn hDim).2.1
        0 (by omega) s hs hs')

def swExponentialCohomologyEquiv
    (hSW : SWCohomologicalSource.{0,0,1})
    (hGeneral : GeneralContactCanonicalTheorem.{0,0,0})
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n) :
    letI := A.charts
    unitCohomology (B := SphereBundleTotal P.tangent)
        𝓘(ℂ, ComplexTwistorModel n) 1 ≃+
      integralCohomology (B := SphereBundleTotal P.tangent) 2 := by
  letI := A.charts
  exact exponentialCohomologyEquiv 𝓘(ℂ, ComplexTwistorModel n) 1
    (swFunctionCohomology_subsingleton P C hSW hGeneral hn hDim 1
      (by omega) (by omega))
    (swFunctionCohomology_subsingleton P C hSW hGeneral hn hDim 2
      (by omega) (by omega))

/-- Actual tensor classes of holomorphic line bundles, represented by
holomorphic line cores, are classified by integral H² of the twistor.
This is not yet an identification of that group with ℤ. -/
def swLineCoreIntegralCohomologyEquiv
    (hSW : SWCohomologicalSource.{0,0,1})
    (hGeneral : GeneralContactCanonicalTheorem.{0,0,0})
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n) :
    letI := A.charts
    Additive (CoreClass.{0} (B := SphereBundleTotal P.tangent)
        𝓘(ℂ, ComplexTwistorModel n)) ≃+
      integralCohomology (B := SphereBundleTotal P.tangent) 2 := by
  letI := A.charts
  exact (HolomorphicLineDerivedTensor.classAddEquiv
    𝓘(ℂ, ComplexTwistorModel n)).trans
      (swExponentialCohomologyEquiv P C hSW hGeneral hn hDim)

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
