import QuaternionicSymmetry.HolomorphicLineIntegralChernClass
import QuaternionicSymmetry.ManifoldTwistorProjectiveFiberO2

/-! The actual integral Chern class of a line restricted to a twistor
fiber. Holomorphic O(2) restriction gives twice the genuine exponential
Chern class of O(1) in actual integral H²(CP¹). A normalized integer
pairing is a separate topological obligation, not part of this definition. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveFiberChernClass

open scoped Manifold ContDiff
open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open HolomorphicExponentialCohomology HolomorphicLineIntegralChernClass
open ManifoldTwistorSphereCore ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses ManifoldTwistorProjectiveFiberRestriction
open ManifoldTwistorProjectiveFiberO2 ProjectiveLineHyperplaneCore
open FourDimensionalHalfSpinProjective ProjectiveLineTangentDeterminant
noncomputable section

def hyperplaneChernClass : integralCohomology (B := ProjectiveSpinor) 2 :=
  integralFirstChern 𝓘(ℂ,Model)
    (Additive.ofMul (Quotient.mk _ hyperplaneLineCore))

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def fiberChernHom {n : ℕ} (A : CompatibleComplexAtlas Q D n) (p : M) :
    letI := A.charts
    Additive (CoreClass.{0} (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n)) →+
      integralCohomology (B := ProjectiveSpinor) 2 := by
  letI := A.charts
  exact (integralFirstChern 𝓘(ℂ,Model)).comp
    (restrictionHom Q D A p).toAdditive

theorem fiberChernHom_contact {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (C : HolomorphicContactData Q D n A) (p : M) :
    letI := A.charts
    fiberChernHom Q D A p (Additive.ofMul (contactClass Q D C.line)) =
      2 • hyperplaneChernClass := by
  letI := A.charts
  change integralFirstChern 𝓘(ℂ,Model)
    (Additive.ofMul (restrictionHom Q D A p (contactClass Q D C.line))) = _
  rw [restrictionHom_contactClass_eq_O2 Q D A C p, integralFirstChern_pow]
  rfl

/-- Once an actual normalized integral pairing is constructed, degree two
is a consequence of the checked O(2) gauge, not a separate contact premise. -/
theorem fiberChernHom_contact_pairing {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (C : HolomorphicContactData Q D n A) (p : M)
    (pairing : integralCohomology (B := ProjectiveSpinor) 2 →+ ℤ)
    (hPairing : pairing hyperplaneChernClass = 1) :
    letI := A.charts
    (pairing.comp (fiberChernHom Q D A p))
      (Additive.ofMul (contactClass Q D C.line)) = 2 := by
  letI := A.charts
  rw [AddMonoidHom.comp_apply, fiberChernHom_contact Q D A C p,
    map_nsmul, hPairing]
  norm_num

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveFiberChernClass
