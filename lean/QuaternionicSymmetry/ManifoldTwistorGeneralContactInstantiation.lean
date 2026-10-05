import QuaternionicSymmetry.GeneralComplexContactData

/-! The precise LeBrun source contact data on the actual twistor sphere
bundle instantiate the general complex-contact hypotheses. The only
nontrivial matching step is that the kernel of the constructed quotient
form is exactly the checked horizontal distribution. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

/-- No quaternionic field appears in the resulting general contact
hypotheses; the source T1 contact data have been matched to the actual
complex and smooth tangent bundles. -/
def NondegenerateHolomorphicContactData.toGeneralContactGeometry {n : ℕ}
    {A : CompatibleComplexAtlas Q D n}
    (C : NondegenerateHolomorphicContactData Q D n A) :
    GeneralComplexContactData.ContactGeometry
      (IR := RealModel (E := E)) (Z := SphereBundleTotal Q) n where
  charts := A.charts
  complexManifold := A.complexManifold
  realManifold := A.realManifold
  smoothToReal := A.smoothToExisting
  smoothFromReal := A.smoothFromExisting
  Index := C.contact.line.Index
  line := C.contact.line.core
  lineHolomorphic := C.contact.line.holomorphic
  theta := C.contact.line.contactFormReal Q D
  thetaSurjective := C.contact.line.contactFormReal_surjective Q D
  thetaHolomorphic := C.contact.contactHolomorphic
  leviNondegenerate := by
    intro z u hu
    let L := C.contact.line
    have huH : u.1 ∈ horizontalTangentSubmodule Q D z := by
      rw [← L.contactFormReal_ker Q D z]
      exact u.2
    let uH : horizontalTangentSubmodule Q D z := ⟨u.1,huH⟩
    have huHne : uH ≠ 0 := by
      intro h
      apply hu
      apply Subtype.ext
      exact congrArg
        (fun x : horizontalTangentSubmodule Q D z =>
          (x : TangentSpace (RealModel (E := E)) z)) h
    obtain ⟨U,hopen,hz,X,Y,hX,hY,hHX,hHY,hval,hlevi⟩ :=
      C.nondegenerate z uH huHne
    refine ⟨U,hopen,hz,X,Y,hX,hY,?_,?_,hval,hlevi⟩
    · intro y hy
      rw [L.contactFormReal_ker Q D y]
      exact hHX y hy
    · intro y hy
      rw [L.contactFormReal_ker Q D y]
      exact hHY y hy

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
