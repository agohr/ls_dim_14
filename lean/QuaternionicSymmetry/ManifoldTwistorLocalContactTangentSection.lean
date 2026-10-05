import QuaternionicSymmetry.ManifoldTwistorLocalContactSection

/-! Local holomorphic tangent lifts of the holomorphic contact form,
retaining the tangent section itself for subsequent induced maps. -/
namespace QuaternionicSymmetry.ManifoldTwistorLocalContactTangentSection
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open QuaternionicSymmetry.HolomorphicBundleLocalVector
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

local instance : Fact (Module.finrank ℝ ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) :=
  ⟨by simp⟩

/-- Retain the tangent section's own holomorphicity, which is needed when
the induced twistor differential is applied before the ambient form. -/
theorem exists_local_contact_section_with_tangent {n : ℕ}
    (A : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n A)
    (z : SphereBundleTotal Q)
    (v : ComplexTwistorModel n) :
    letI := A.charts
    letI := A.complexManifold
    letI := C.line.holomorphic
    ∃ U : Set (SphereBundleTotal Q), IsOpen U ∧ z ∈ U ∧
      ∃ s : ∀ y : SphereBundleTotal Q,
        TangentSpace 𝓘(ℂ,ComplexTwistorModel n) y,
        s z = v ∧
        ContMDiffOn 𝓘(ℂ,ComplexTwistorModel n)
          (𝓘(ℂ,ComplexTwistorModel n)).tangent ∞
          (fun y => (⟨y,s y⟩ : TangentBundle
            𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q))) U ∧
        ContMDiffOn 𝓘(ℂ,ComplexTwistorModel n)
          ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ)) ∞
          (fun y => C.line.contactFormTotal Q D
            (⟨y,s y⟩ : TangentBundle 𝓘(ℂ,ComplexTwistorModel n)
              (SphereBundleTotal Q))) U := by
  letI := A.charts
  letI := A.complexManifold
  letI := C.line.holomorphic
  let e := trivializationAt (ComplexTwistorModel n)
    (TangentSpace 𝓘(ℂ,ComplexTwistorModel n) : SphereBundleTotal Q → Type _) z
  letI : MemTrivializationAtlas e := ⟨⟨_,rfl⟩⟩
  have hz : z ∈ e.baseSet := mem_baseSet_trivializationAt
    (ComplexTwistorModel n)
    (TangentSpace 𝓘(ℂ,ComplexTwistorModel n) : SphereBundleTotal Q → Type _) z
  obtain ⟨s,hs,hsv⟩ := exists_local_section_through
    𝓘(ℂ,ComplexTwistorModel n) e z hz v
  refine ⟨e.baseSet,e.open_baseSet,hz,s,hsv,hs,?_⟩
  exact C.contactHolomorphic.comp_contMDiffOn hs

end
end QuaternionicSymmetry.ManifoldTwistorLocalContactTangentSection
