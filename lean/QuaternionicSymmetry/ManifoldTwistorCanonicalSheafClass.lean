import QuaternionicSymmetry.ManifoldTwistorCanonicalClassGroup
import QuaternionicSymmetry.HolomorphicLineSheafClassGroup

/-! The actual twistor contact canonical relation in the group of genuine
locally free rank-one holomorphic module sheaves. Its multiplication is the
checked sheafified tensor product, not a merely formal cocycle operation.
This does not assert that the contact line generates the group. -/

namespace QuaternionicSymmetry.ManifoldTwistorCanonicalSheafClass

open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open ManifoldTwistorLineCoreClasses ManifoldTwistorCanonicalClassGroup
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicMetric ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def contactSheafClass {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n A) :
    letI := A.charts
    SheafClass (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n) := by
  letI := A.charts
  exact Quotient.mk _ (toLineSheaf _ (contactLineCore Q D L))

def anticanonicalSheafClass {n : ℕ} (A : CompatibleComplexAtlas Q D n) :
    letI := A.charts
    SheafClass (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n) := by
  letI := A.charts
  exact Quotient.mk _ (toLineSheaf _ (anticanonicalLineCore Q D A))

theorem anticanonicalSheafClass_eq_contactSheafClass_pow
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (C : NondegenerateHolomorphicContactData Q D n A) :
    letI := A.charts
    anticanonicalSheafClass Q D A = contactSheafClass Q D C.contact.line ^ (n + 1) := by
  letI := A.charts
  let e := classMulEquiv (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n)
  change e (anticanonicalClass Q D A) = e (contactClass Q D C.contact.line) ^ (n + 1)
  rw [anticanonicalClass_eq_contactClass_pow_of_generalContact Q D hGeneral C, map_pow]

end
end QuaternionicSymmetry.ManifoldTwistorCanonicalSheafClass
