import QuaternionicSymmetry.HolomorphicLineCoreClasses
import QuaternionicSymmetry.HolomorphicLineGaugeFromBundleIso
import QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
import QuaternionicSymmetry.ManifoldTwistorContactCanonicalApply

/-! The actual LeBrun contact and anticanonical holomorphic line cores
as cover-invariant represented classes. -/

namespace QuaternionicSymmetry.ManifoldTwistorLineCoreClasses

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineGaugeFromBundleIso
open QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
open QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

/-- The genuine contact quotient line of the actual complex twistor,
packaged as a represented holomorphic line core. -/
def contactLineCore {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n A) :
    letI := A.charts
    LineCore.{0} (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n) := by
  letI := A.charts
  exact ⟨L.Index, L.core, L.holomorphic⟩

/-- The actual holomorphic anticanonical determinant core. -/
def anticanonicalLineCore {n : ℕ} (A : CompatibleComplexAtlas Q D n) :
    letI := A.charts
    LineCore.{0} (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n) := by
  letI := A.charts
  exact ⟨atlas (ComplexTwistorModel n) (SphereBundleTotal Q),
    A.anticanonicalCore Q D, A.anticanonicalCore_holomorphic Q D⟩

/-- The actual `(n+1)`-st contact-line power core appearing in the
complex-contact canonical formula. -/
def canonicalPowerLineCore {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n A) :
    letI := A.charts
    LineCore.{0} (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n) := by
  letI := A.charts
  exact ⟨L.Index, L.canonicalPowerCore Q D,
    L.canonicalPowerCore_holomorphic Q D⟩

/-- The represented, cover-invariant class of the actual contact line. -/
def contactClass {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n A) :
    letI := A.charts
    CoreClass.{0} (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n) := by
  letI := A.charts
  exact Quotient.mk _ (contactLineCore Q D L)

/-- The represented, cover-invariant class of the actual anticanonical
determinant line. -/
def anticanonicalClass {n : ℕ} (A : CompatibleComplexAtlas Q D n) :
    letI := A.charts
    CoreClass.{0} (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n) := by
  letI := A.charts
  exact Quotient.mk _ (anticanonicalLineCore Q D A)

/-- The represented class of the contact-line power from T1C. -/
def canonicalPowerClass {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n A) :
    letI := A.charts
    CoreClass.{0} (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n) := by
  letI := A.charts
  exact Quotient.mk _ (canonicalPowerLineCore Q D L)

/-- The exact chartwise condition for the T1C canonical-line
identification to descend to represented core classes.  Converting the
existing total-bundle `HolomorphicContactCanonicalIso` to this gauge is
a separate analytic bridge; this theorem does not assume it implicitly. -/
theorem anticanonicalClass_eq_canonicalPowerClass_iff_gauge
    {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n A) :
    letI := A.charts
    anticanonicalClass Q D A = canonicalPowerClass Q D L ↔
      Isomorphic 𝓘(ℂ,ComplexTwistorModel n)
        (anticanonicalLineCore Q D A) (canonicalPowerLineCore Q D L) := by
  letI := A.charts
  change Quotient.mk _ (anticanonicalLineCore Q D A) =
      Quotient.mk _ (canonicalPowerLineCore Q D L) ↔ _
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    apply Quotient.sound
    exact h

/-- The actual T1C holomorphic total-bundle identification descends to
equality of the cover-invariant anticanonical and contact-power classes. -/
theorem anticanonicalClass_eq_canonicalPowerClass
    {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n A)
    (h : HolomorphicContactCanonicalIso Q D n A L) :
    letI := A.charts
    anticanonicalClass Q D A = canonicalPowerClass Q D L := by
  letI := A.charts
  letI := A.anticanonicalCore_holomorphic Q D
  letI := L.canonicalPowerCore_holomorphic Q D
  let e : TotalIso (IB := 𝓘(ℂ,ComplexTwistorModel n))
      (A.anticanonicalCore Q D) (L.canonicalPowerCore Q D) := {
    fiberEquiv := h.fiberEquiv
    holomorphicForward := h.holomorphicForward
    holomorphicBackward := h.holomorphicBackward }
  apply (anticanonicalClass_eq_canonicalPowerClass_iff_gauge Q D L).2
  exact ⟨e.toGaugeIso⟩

/-- The registered general complex-contact canonical-line theorem,
specialized to the genuine LeBrun twistor contact data, yields the
canonical class relation in the represented holomorphic line-core quotient. -/
theorem anticanonicalClass_eq_canonicalPowerClass_of_generalContact
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (C : NondegenerateHolomorphicContactData Q D n A) :
    letI := A.charts
    anticanonicalClass Q D A = canonicalPowerClass Q D C.contact.line := by
  obtain ⟨h⟩ := contactCanonicalIso_of_generalContact Q D hGeneral C
  exact anticanonicalClass_eq_canonicalPowerClass Q D C.contact.line h

/-- Picard-style form of the actual contact canonical relation: the
anticanonical represented class is the `(n+1)`-fold *tensor iteration*
of the genuine contact line. The bridge to the scalar-cocycle power is
the checked all-overlap gauge, not a definitional identification. -/
theorem anticanonicalClass_eq_contactTensorIterate_of_generalContact
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (C : NondegenerateHolomorphicContactData Q D n A) :
    letI := A.charts
    anticanonicalClass Q D A =
      tensorIterate 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.contact.line) (n + 1) := by
  letI := A.charts
  calc
    anticanonicalClass Q D A = canonicalPowerClass Q D C.contact.line :=
      anticanonicalClass_eq_canonicalPowerClass_of_generalContact Q D hGeneral C
    _ = Quotient.mk _ (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.contact.line) (n + 1)) := rfl
    _ = tensorIterate 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.contact.line) (n + 1) :=
      (tensorIterate_eq_power 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.contact.line) (n + 1)).symm

end
end QuaternionicSymmetry.ManifoldTwistorLineCoreClasses
