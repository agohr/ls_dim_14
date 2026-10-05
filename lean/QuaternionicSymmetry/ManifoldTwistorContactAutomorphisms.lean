import QuaternionicSymmetry.GeneralHolomorphicDistributionAutomorphisms
import QuaternionicSymmetry.ManifoldQuaternionicTwistorIsometryDiffeomorph
import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactComplexNaturality
import QuaternionicSymmetry.ManifoldQuaternionicTwistorActionFaithful

/-! The actual holomorphic contact-automorphism group of a compatible
twistor contact structure, and the faithful homomorphism furnished by
quaternionic metric isometries. No Lie-group complexification, algebraicity
or maximal-torus comparison is asserted. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactAutomorphisms

open GeneralHolomorphicDistributionAutomorphisms
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorIsometryDiffeomorph
open ManifoldQuaternionicIsometryContactComplexNaturality
open ManifoldQuaternionicTwistorActionFaithful
open ManifoldTwistorSphereCore ManifoldTwistorLeBrunComplexAtlas
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (L : HolomorphicContactLine Q D n B)

def contactDistribution : SphereBundleTotal Q → Submodule ℂ (ComplexTwistorModel n) :=
  fun z => LinearMap.ker (L.contactFormComplex Q D z)

def ContactAutomorphisms :=
  letI := B.charts
  letI := B.complexManifold
  Automorphisms (contactDistribution Q D B L)

instance : Group (ContactAutomorphisms Q D B L) := by
  letI := B.charts
  letI := B.complexManifold
  unfold ContactAutomorphisms
  infer_instance

theorem complexLift_preserves_contact_forward (f : QuaternionicIsometries Q) :
    letI := B.charts
    letI := B.complexManifold
    PreservesForward (contactDistribution Q D B L) (complexLift Q D B f) := by
  letI := B.charts
  letI := B.complexManifold
  intro z v hv
  change L.contactFormComplex Q D z v = 0 at hv
  change L.contactFormComplex Q D (sphereTotalMap Q f z)
    (mfderiv 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
      (sphereTotalMap Q f) z v) = 0
  rw [contactLineFiberEquiv_contactFormComplex Q D B L f z v, hv, map_zero]

def isometryContactLift : QuaternionicIsometries Q →* ContactAutomorphisms Q D B L := by
  letI := B.charts
  letI := B.complexManifold
  refine {
    toFun := fun f => ⟨complexLift Q D B f, ?_⟩
    map_one' := ?_
    map_mul' := ?_ }
  · refine ⟨complexLift_preserves_contact_forward Q D B L f, ?_⟩
    exact complexLift_preserves_contact_forward Q D B L f⁻¹
  · apply Subtype.ext
    apply Diffeomorph.ext
    intro z
    change (1 : QuaternionicIsometries Q) • z = z
    exact one_smul _ _
  · intro f g
    apply Subtype.ext
    apply Diffeomorph.ext
    intro z
    change (f*g) • z = f • (g • z)
    exact mul_smul _ _ _

theorem isometryContactLift_apply (f : QuaternionicIsometries Q)
    (z : SphereBundleTotal Q) :
    ((isometryContactLift Q D B L f).1 : SphereBundleTotal Q → SphereBundleTotal Q) z =
      sphereTotalMap Q f z := rfl

theorem isometryContactLift_injective :
    Function.Injective (isometryContactLift Q D B L) := by
  intro f g h
  apply sphereTotalMap_injective Q
  funext z
  exact congrArg (fun a : ContactAutomorphisms Q D B L => a.1 z) h

end
end QuaternionicSymmetry.ManifoldTwistorContactAutomorphisms
