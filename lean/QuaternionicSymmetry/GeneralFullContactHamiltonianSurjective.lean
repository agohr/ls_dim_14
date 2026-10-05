import QuaternionicSymmetry.HolomorphicVectorFieldRealization
import QuaternionicSymmetry.GeneralContactHamiltonianBijection
import QuaternionicSymmetry.GeneralUniqueContactHamiltonianSource

/-! The surjectivity half of the original canonical full-automorphism
Hamiltonian contract, using only the retained closed-subgroup input. -/
namespace QuaternionicSymmetry.GeneralFullContactHamiltonianSurjective
open GeneralComplexContactData ManifoldTwistorLeBrunComplexAtlas
open GeneralUniqueContactHamiltonianSource GeneralHolomorphicFullAutomorphisms
open GeneralClosedSubgroupLieSource
open scoped Manifold ContDiff
noncomputable section
variable {R H Z V : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]
  [CompactSpace Z] [T2Space Z] [SecondCountableTopology Z] [Nonempty Z]
  {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n)
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem fullHamiltonian_surjective (hClosed : LeeClosedEmbeddingTheorem)
    [ChartedSpace V (letI := C.charts; letI := C.complexManifold
      HolomorphicAutomorphisms (ComplexTwistorModel n) Z)]
    [IsManifold 𝓘(ℂ,V) ∞ (letI := C.charts; letI := C.complexManifold
      HolomorphicAutomorphisms (ComplexTwistorModel n) Z)]
    [letI := C.charts; letI := C.complexManifold
      LieGroup 𝓘(ℂ,V) ∞ (HolomorphicAutomorphisms (ComplexTwistorModel n) Z)]
    (hJoint : letI := C.charts; letI := C.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n)) 𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : HolomorphicAutomorphisms (ComplexTwistorModel n) Z × Z => p.1.1 p.2)) :
    letI := C.charts; letI := C.complexManifold
    Function.Surjective (fun v : GroupLieAlgebra 𝓘(ℂ,V)
      (HolomorphicAutomorphisms (ComplexTwistorModel n) Z) =>
        C.sectionOfTangent (fullInfinitesimalActionLinear C hJoint v)) := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.realManifold
  intro s
  obtain ⟨v,hv⟩ := HolomorphicVectorFieldRealization.infinitesimal_surjective hClosed hJoint
    (GeneralContactHamiltonianField.hamiltonian C s)
  refine ⟨v,?_⟩
  change C.sectionOfTangent
    (HolomorphicFamilyInfinitesimalLinear.infinitesimalActionLinear _ 1 hJoint _ v) = s
  rw [hv]
  exact GeneralContactHamiltonianField.contraction_hamiltonian C s

/-- A checked assembly lemma isolating the remaining geometric implication:
automorphism preservation of the kernel must imply contactness of its
infinitesimal fields. This hypothesis is not a literature source field. -/
theorem fullHamiltonian_bijective_of_contact (hClosed : LeeClosedEmbeddingTheorem)
    [ChartedSpace V (letI := C.charts; letI := C.complexManifold
      HolomorphicAutomorphisms (ComplexTwistorModel n) Z)]
    [IsManifold 𝓘(ℂ,V) ∞ (letI := C.charts; letI := C.complexManifold
      HolomorphicAutomorphisms (ComplexTwistorModel n) Z)]
    [letI := C.charts; letI := C.complexManifold
      LieGroup 𝓘(ℂ,V) ∞ (HolomorphicAutomorphisms (ComplexTwistorModel n) Z)]
    (hJoint : letI := C.charts; letI := C.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n)) 𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : HolomorphicAutomorphisms (ComplexTwistorModel n) Z × Z => p.1.1 p.2))
    (hContact : letI := C.charts; letI := C.complexManifold
      ∀ v, GeneralContactHamiltonianBijection.IsContactField C
        (fullInfinitesimalActionLinear C hJoint v)) :
    letI := C.charts; letI := C.complexManifold
    Function.Bijective (fun v : GroupLieAlgebra 𝓘(ℂ,V)
      (HolomorphicAutomorphisms (ComplexTwistorModel n) Z) =>
        C.sectionOfTangent (fullInfinitesimalActionLinear C hJoint v)) := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.realManifold
  refine ⟨?_,fullHamiltonian_surjective C hClosed hJoint⟩
  intro v w hvw
  have he := (GeneralContactHamiltonianBijection.contraction_bijective C).injective
    (a₁ := ⟨fullInfinitesimalActionLinear C hJoint v,hContact v⟩)
    (a₂ := ⟨fullInfinitesimalActionLinear C hJoint w,hContact w⟩) hvw
  exact (HolomorphicVectorFieldRealization.infinitesimal_injective hJoint) (congrArg Subtype.val he)

end
end QuaternionicSymmetry.GeneralFullContactHamiltonianSurjective
