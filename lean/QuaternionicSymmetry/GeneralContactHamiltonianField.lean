import QuaternionicSymmetry.GeneralContactComplexForm
import QuaternionicSymmetry.GeneralComplexContactSections

/-! Every global section of the genuine contact line has an internally
constructed holomorphic Hamiltonian vector field. This proves surjectivity
of contraction without an automorphism-group or completeness hypothesis. -/
namespace QuaternionicSymmetry.GeneralContactHamiltonianField
open GeneralComplexContactData ManifoldTwistorLeBrunComplexAtlas
open GeneralContactComplexForm HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineOneFormCoordinates ContactExteriorDerivativeCalculus ContactDeterminantAlgebra
open scoped Manifold ContDiff
noncomputable section
variable {R H Z : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]
  {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n)
local notation "V" => ComplexTwistorModel n

theorem complexForm_holomorphic :
    letI := C.charts
    letI := C.complexManifold
    letI := C.lineHolomorphic
    ContMDiff (𝓘(ℂ,V)).tangent ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TangentBundle 𝓘(ℂ,V) Z =>
        (⟨t.1,complexForm C t.1 t.2⟩ : Bundle.TotalSpace ℂ C.line.Fiber)) := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.lineHolomorphic
  simpa only [complexForm_apply] using C.thetaHolomorphic

theorem complexForm_nondegenerate :
    letI := C.charts
    letI := C.complexManifold
    letI := C.lineHolomorphic
    ∀ (i : atlas V Z) (a : C.Index) (z : Z), z ∈ i.1.source → z ∈ C.line.baseSet a →
      (border (coordinateForm C.line (complexForm C) i a (i.1 z)).toLinearMap
        (exteriorDerivative (coordinateForm C.line (complexForm C) i a) (i.1 z))).Nondegenerate := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.lineHolomorphic
  intro i a z hi ha
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
    ((Module.finBasis ℂ V).prod (Module.Basis.singleton Unit ℂ))).mpr
  exact GeneralContactDeterminantNonzero.density_ne_zero C (complexForm C)
    (complexForm_apply C) i a z hi ha

/-- The actual holomorphic tangent section attached to a contact-line section. -/
def hamiltonian (s : letI := C.charts; GlobalSections 𝓘(ℂ,V) C.contactLineCore) :
    C.HolomorphicTangentSections := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.lineHolomorphic
  exact HolomorphicContactHamiltonianField.tangentSection C.line (complexForm C)
    (complexForm_holomorphic C) s s.contMDiff (complexForm_nondegenerate C)

@[simp] theorem contraction_hamiltonian
    (s : letI := C.charts; GlobalSections 𝓘(ℂ,V) C.contactLineCore) :
    C.sectionOfTangent (hamiltonian C s) = s := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.lineHolomorphic
  ext z
  rw [C.sectionOfTangent_apply, ← complexForm_apply]
  exact HolomorphicContactHamiltonianField.contraction C.line (complexForm C)
    (complexForm_holomorphic C) s s.contMDiff (complexForm_nondegenerate C) z

theorem contraction_surjective : Function.Surjective C.sectionOfTangent := by
  intro s
  exact ⟨hamiltonian C s,contraction_hamiltonian C s⟩

end
end QuaternionicSymmetry.GeneralContactHamiltonianField
