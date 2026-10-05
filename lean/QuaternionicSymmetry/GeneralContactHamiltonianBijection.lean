import QuaternionicSymmetry.GeneralContactHamiltonianField
import QuaternionicSymmetry.HolomorphicContactHamiltonianBijection

/-! The Nitta--Takeuchi contact-field/section correspondence is proved for
the project's genuine contact geometry. The identification of contact
fields with the Lie algebra of full automorphisms is a separate step. -/
namespace QuaternionicSymmetry.GeneralContactHamiltonianBijection
open GeneralComplexContactData ManifoldTwistorLeBrunComplexAtlas
open GeneralContactComplexForm GeneralContactHamiltonianField
open HolomorphicContactHamiltonianBijection
open scoped Manifold ContDiff
noncomputable section
variable {R H Z : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]
  {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n)
local notation "V" => ComplexTwistorModel n

/-- Contact vector fields defined using the genuine complex form and actual
chart derivatives. -/
def IsContactField (X : C.HolomorphicTangentSections) : Prop := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.lineHolomorphic
  exact IsContact C.line (complexForm C) X

theorem contraction_bijective : Function.Bijective
    (fun X : {X : C.HolomorphicTangentSections // IsContactField C X} => C.sectionOfTangent X.1) := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.lineHolomorphic
  have h := HolomorphicContactHamiltonianBijection.contraction_bijective C.line (complexForm C)
    (complexForm_holomorphic C) (complexForm_nondegenerate C)
  have he (X : C.HolomorphicTangentSections) :
      contractionSection C.line (complexForm C) (complexForm_holomorphic C) X = C.sectionOfTangent X := by
    ext z
    exact complexForm_apply C z (X z)
  simpa only [he] using h

/-- Every section has a unique genuine holomorphic contact vector field. -/
theorem existsUnique_contact_hamiltonian
    (s : letI := C.charts; HolomorphicLineCorePullback.GlobalSections 𝓘(ℂ,V) C.contactLineCore) :
    ∃! X : {X : C.HolomorphicTangentSections // IsContactField C X}, C.sectionOfTangent X.1 = s := by
  obtain ⟨X,hX⟩ := (contraction_bijective C).surjective s
  exact ⟨X,hX,fun Y hY => (contraction_bijective C).injective (hY.trans hX.symm)⟩

end
end QuaternionicSymmetry.GeneralContactHamiltonianBijection
