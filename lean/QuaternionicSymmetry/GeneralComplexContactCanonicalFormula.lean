import QuaternionicSymmetry.GeneralComplexContactData

/-! The canonical-bundle formula for a general complex contact manifold,
with no twistor or quaternionic hypothesis. LeBrun 1995, Definition 2.1,
pp. 3–4 states the holomorphic exact sequence, the nondegenerate
`L`-valued Levi form, and the induced `L^(n+1) ≅ K⁻¹`. The theorem is a
precisely named external general-background premise until the full
holomorphic exterior calculus and determinant-of-exact-sequence proof are
developed here. -/

namespace QuaternionicSymmetry.GeneralComplexContactData

open QuaternionicSymmetry.HolomorphicLinePowers
open QuaternionicSymmetry.HolomorphicDeterminantLine
open QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
open scoped Manifold ContDiff

noncomputable section

variable {R H Z : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]
variable {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n)

def ContactGeometry.tangentCore :
    letI := C.charts
    VectorBundleCore ℂ Z (ComplexTwistorModel n)
      (atlas (ComplexTwistorModel n) Z) := by
  letI := C.charts
  letI := C.complexManifold
  exact tangentBundleCore 𝓘(ℂ,ComplexTwistorModel n) Z

theorem ContactGeometry.tangentCore_holomorphic :
    letI := C.charts
    (C.tangentCore).IsContMDiff 𝓘(ℂ,ComplexTwistorModel n) ∞ := by
  letI := C.charts
  letI := C.complexManifold
  letI : IsManifold 𝓘(ℂ,ComplexTwistorModel n) (∞ + 1) Z := by
    simpa using C.complexManifold
  exact tangentBundleCore.isContMDiff
    (I := 𝓘(ℂ,ComplexTwistorModel n)) (M := Z) (n := ∞)

/-- Anticanonical holomorphic line of the general contact complex atlas. -/
def ContactGeometry.anticanonicalCore :
    letI := C.charts
    VectorBundleCore ℂ Z ℂ (atlas (ComplexTwistorModel n) Z) := by
  letI := C.charts
  exact determinantCore C.tangentCore

theorem ContactGeometry.anticanonicalCore_holomorphic :
    letI := C.charts
    C.anticanonicalCore.IsContMDiff 𝓘(ℂ,ComplexTwistorModel n) ∞ := by
  letI := C.charts
  letI := C.tangentCore_holomorphic
  exact determinantCore_isContMDiff (Z := C.tangentCore)
    (IB := 𝓘(ℂ,ComplexTwistorModel n))

/-- The (n+1)-st holomorphic tensor power of the actual contact line. -/
def ContactGeometry.contactPowerCore : VectorBundleCore ℂ Z ℂ C.Index :=
  powerCore C.line (n + 1)

theorem ContactGeometry.contactPowerCore_holomorphic :
    letI := C.charts
    C.contactPowerCore.IsContMDiff 𝓘(ℂ,ComplexTwistorModel n) ∞ := by
  letI := C.charts
  letI := C.lineHolomorphic
  exact powerCore_isContMDiff (Z := C.line)
    (IB := 𝓘(ℂ,ComplexTwistorModel n)) (n + 1)

/-- Genuine holomorphic line-bundle isomorphism conclusion of the
general contact canonical theorem. -/
structure HolomorphicCanonicalIso where
  fiberEquiv : letI := C.charts
    ∀ z : Z, C.anticanonicalCore.Fiber z ≃ₗ[ℂ]
      C.contactPowerCore.Fiber z
  holomorphicForward : letI := C.charts
    letI := C.complexManifold
    letI := C.anticanonicalCore_holomorphic
    letI := C.contactPowerCore_holomorphic
    ContMDiff ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ))
      ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : Bundle.TotalSpace ℂ C.anticanonicalCore.Fiber =>
        (⟨t.1, fiberEquiv t.1 t.2⟩ : Bundle.TotalSpace ℂ C.contactPowerCore.Fiber))
  holomorphicBackward : letI := C.charts
    letI := C.complexManifold
    letI := C.anticanonicalCore_holomorphic
    letI := C.contactPowerCore_holomorphic
    ContMDiff ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ))
      ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : Bundle.TotalSpace ℂ C.contactPowerCore.Fiber =>
        (⟨t.1, (fiberEquiv t.1).symm t.2⟩ :
          Bundle.TotalSpace ℂ C.anticanonicalCore.Fiber))

/-- Universal, twistor-independent content of LeBrun 1995 Definition 2.1:
every holomorphic contact manifold has the canonical line relation.
This is an explicit source theorem premise, not a project axiom. -/
def GeneralContactCanonicalTheorem : Prop :=
  ∀ {R H Z : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
    {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]
    {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n),
    Nonempty (HolomorphicCanonicalIso C)

end
end QuaternionicSymmetry.GeneralComplexContactData
