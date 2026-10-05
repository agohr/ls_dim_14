import QuaternionicSymmetry.HolomorphicLineCoreSheafPicardGenerator
import QuaternionicSymmetry.GeneralContactDeterminantNonzero
import QuaternionicSymmetry.ManifoldTwistorGeneralContactInstantiation
import QuaternionicSymmetry.ManifoldTwistorContactComplexLinear
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses
import QuaternionicSymmetry.HolomorphicLineGaugeToBundleIso
import QuaternionicSymmetry.HolomorphicLineCoreClassPowers

/-! The squared contact canonical relation is internal. On the Picard-generator
branch its square uniquely determines the canonical contact power itself. -/
namespace QuaternionicSymmetry.ManifoldTwistorSquaredCanonical
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
  ManifoldQuaternionicMetric ManifoldQuaternionicConnection ManifoldTwistorLineCoreClasses
  HolomorphicLineCoreClasses HolomorphicLineTensorPowerClasses
  HolomorphicContactDeterminantGauge HolomorphicLineGaugeToBundleIso
  HolomorphicLineCoreClassPowers
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem squaredCanonical_isomorphic {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (C : NondegenerateHolomorphicContactData Q D n A) :
    letI := A.charts
    letI := A.complexManifold
    Isomorphic 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (anticanonicalLineCore Q D A) 2)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.contact.line) (2*(n+1))) := by
  letI := A.charts
  letI := A.complexManifold
  letI := C.contact.line.holomorphic
  let θ := C.contact.line.contactFormComplex Q D
  have hθ : ContMDiff (𝓘(ℂ,ComplexTwistorModel n)).tangent
      ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TangentBundle 𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q) =>
        (⟨t.1, θ t.1 t.2⟩ : Bundle.TotalSpace ℂ C.contact.line.core.Fiber)) :=
    C.contact.contactHolomorphic
  have hN := GeneralContactDeterminantNonzero.density_ne_zero
    (C.toGeneralContactGeometry Q D) θ (by intro z v; rfl)
  have e := squareGauge C.contact.line.core θ hθ hN
  have hdim : Module.finrank ℂ (ComplexTwistorModel n) + 1 = 2*(n+1) := by
    simp [ComplexTwistorModel]
    omega
  rw [hdim] at e
  exact ⟨e⟩

/-- An infinite cyclic Picard group has no two-torsion, so the internally
proved square relation determines the contact canonical class uniquely. -/
theorem canonicalClass_of_generator {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (C : NondegenerateHolomorphicContactData Q D n A)
    (hPic : letI := A.charts; Function.Bijective (fun k : ℤ =>
      (contactClass Q D C.contact.line) ^ k)) :
    letI := A.charts
    anticanonicalClass Q D A = contactClass Q D C.contact.line ^ (n+1) := by
  letI := A.charts
  letI := A.complexManifold
  have hs : (Quotient.mk _ (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
      (anticanonicalLineCore Q D A) 2) : CoreClass 𝓘(ℂ,ComplexTwistorModel n)) =
      Quotient.mk _ (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.contact.line) (2*(n+1))) :=
    Quotient.sound (squaredCanonical_isomorphic Q D C)
  rw [class_powerCoreRep, class_powerCoreRep] at hs
  change anticanonicalClass Q D A ^ 2 = contactClass Q D C.contact.line ^ (2*(n+1)) at hs
  obtain ⟨k,hk⟩ := hPic.surjective (anticanonicalClass Q D A)
  rw [← hk] at hs
  have hs' : contactClass Q D C.contact.line ^ (k*2) =
      contactClass Q D C.contact.line ^ ((2*(n+1) : ℕ) : ℤ) := by
    simpa only [zpow_mul, zpow_natCast, zpow_ofNat] using hs
  have hk2 := hPic.injective hs'
  have hk' : k = ((n+1 : ℕ) : ℤ) := by omega
  simpa only [hk', zpow_natCast] using hk.symm

/-- The genuine holomorphic canonical isomorphism needed by SW is now
constructed on the Picard branch without the general canonical contract. -/
theorem canonicalIso_of_generator {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (C : NondegenerateHolomorphicContactData Q D n A)
    (hPic : letI := A.charts; Function.Bijective (fun k : ℤ =>
      (contactClass Q D C.contact.line) ^ k)) :
    Nonempty (HolomorphicContactCanonicalIso Q D n A C.contact.line) := by
  letI := A.charts
  letI := A.complexManifold
  have hclass : (Quotient.mk _ (anticanonicalLineCore Q D A) :
      CoreClass 𝓘(ℂ,ComplexTwistorModel n)) =
      Quotient.mk _ (canonicalPowerLineCore Q D C.contact.line) := by
    change anticanonicalClass Q D A = Quotient.mk _
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.contact.line) (n+1))
    rw [class_powerCoreRep]
    exact canonicalClass_of_generator Q D C hPic
  obtain ⟨e⟩ := (class_eq_iff_totalIso (IB := 𝓘(ℂ,ComplexTwistorModel n)) _ _).mp hclass
  exact ⟨{
    fiberEquiv := e.fiberEquiv
    holomorphicForward := e.holomorphicForward
    holomorphicBackward := e.holomorphicBackward }⟩

/-- The same construction expressed in the full analytic Picard group. -/
theorem canonicalIso_of_analyticGenerator {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (C : NondegenerateHolomorphicContactData Q D n A)
    (hPic : letI := A.charts; letI := A.complexManifold
      Function.Bijective (fun k : ℤ =>
        (HolomorphicLineSheafClassGroup.classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
          (contactClass Q D C.contact.line) : HolomorphicLineSheafClasses.SheafClass
            (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n)) ^ k)) :
    Nonempty (HolomorphicContactCanonicalIso Q D n A C.contact.line) := by
  letI := A.charts
  letI := A.complexManifold
  exact canonicalIso_of_generator Q D C
    ((HolomorphicLineCoreSheafPicardGenerator.core_zpow_bijective_iff_analyticPicard
      𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.contact.line)).mpr hPic)

end
end QuaternionicSymmetry.ManifoldTwistorSquaredCanonical
