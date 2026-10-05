import QuaternionicSymmetry.GeneralComplexContactData
import QuaternionicSymmetry.HolomorphicLineCorePullbackSections

/-! Actual holomorphic tangent sections induce actual contact-line sections.
This is the internal generation step for a homogeneous contact manifold;
the supply of tangent-generating infinitesimal symmetries is separate. -/
namespace QuaternionicSymmetry.GeneralComplexContactData
open ManifoldTwistorLeBrunComplexAtlas
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {R H Z : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]
variable {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n)

/-- The represented holomorphic contact line on the actual complex atlas. -/
def ContactGeometry.contactLineCore :
    letI := C.charts
    LineCore (B := Z) 𝓘(ℂ,ComplexTwistorModel n) := by
  letI := C.charts
  exact ⟨C.Index, C.line, C.lineHolomorphic⟩

/-- Global holomorphic vector fields on the actual complex manifold. -/
abbrev ContactGeometry.HolomorphicTangentSections : Type _ := by
  letI := C.charts
  letI := C.complexManifold
  exact ContMDiffSection 𝓘(ℂ,ComplexTwistorModel n) (ComplexTwistorModel n) ∞
    (TangentSpace 𝓘(ℂ,ComplexTwistorModel n) : Z → Type _)

/-- Compose a genuine holomorphic tangent section with the genuine
holomorphic contact quotient form. No contact-Hamiltonian existence
theorem is needed in this direction. -/
def ContactGeometry.sectionOfTangent (X : C.HolomorphicTangentSections) :
    letI := C.charts
    GlobalSections 𝓘(ℂ,ComplexTwistorModel n) C.contactLineCore := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.lineHolomorphic
  refine ⟨fun z => C.theta z
    (mfderiv 𝓘(ℝ,ComplexTwistorModel n) IR (id : Z → Z) z (X z)), ?_⟩
  exact C.thetaHolomorphic.comp X.contMDiff

theorem ContactGeometry.sectionOfTangent_apply
    (X : C.HolomorphicTangentSections) (z : Z) :
    letI := C.charts
    C.sectionOfTangent X z = C.theta z
      (mfderiv 𝓘(ℝ,ComplexTwistorModel n) IR (id : Z → Z) z (X z)) := by
  rfl

theorem ContactGeometry.realId_deriv_comp_inverse (z : Z) :
    letI := C.charts
    (mfderiv 𝓘(ℝ,ComplexTwistorModel n) IR (id : Z → Z) z).comp
      (mfderiv IR 𝓘(ℝ,ComplexTwistorModel n) (id : Z → Z) z) =
      ContinuousLinearMap.id ℝ (TangentSpace IR z) := by
  letI := C.charts
  have hto : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel n) IR
      (id : Z → Z) z :=
    C.smoothToReal.contMDiffAt.mdifferentiableAt (by simp)
  have hfrom : MDifferentiableAt IR 𝓘(ℝ,ComplexTwistorModel n)
      (id : Z → Z) z :=
    C.smoothFromReal.contMDiffAt.mdifferentiableAt (by simp)
  simpa only [Function.comp_id, mfderiv_id] using
    (mfderiv_comp z hto hfrom).symm

/-- Pointwise generation of the actual holomorphic tangent bundle.
For a complex homogeneous space this will come from its infinitesimal
group action, not from a premise about the desired line-section count. -/
def ContactGeometry.TangentGloballyGenerated : Prop :=
  letI := C.charts
  ∀ z : Z, ∀ v : TangentSpace 𝓘(ℂ,ComplexTwistorModel n) z,
    ∃ X : C.HolomorphicTangentSections, X z = v

/-- The contact line is generated once actual global holomorphic vector
fields span the tangent fibers. This constructs the generating sections
and uses surjectivity of the contact quotient on the actual tangent. -/
theorem ContactGeometry.contactLine_globallyGenerated
    (hTangent : C.TangentGloballyGenerated) :
    letI := C.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n) C.contactLineCore := by
  letI := C.charts
  intro z
  obtain ⟨u,hu⟩ := C.thetaSurjective z (1 : ℂ)
  let v := mfderiv IR 𝓘(ℝ,ComplexTwistorModel n) (id : Z → Z) z u
  obtain ⟨X,hX⟩ := hTangent z v
  refine ⟨C.sectionOfTangent X, ?_⟩
  have hd := congrArg (fun L : TangentSpace IR z →L[ℝ] TangentSpace IR z => L u)
    (C.realId_deriv_comp_inverse z)
  change (mfderiv 𝓘(ℝ,ComplexTwistorModel n) IR (id : Z → Z) z) v = u at hd
  rw [C.sectionOfTangent_apply, hX, hd, hu]
  change (1 : ℂ) ≠ 0
  exact one_ne_zero

end
end QuaternionicSymmetry.GeneralComplexContactData
