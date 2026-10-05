import QuaternionicSymmetry.HolomorphicTangentSectionCoordinates
import QuaternionicSymmetry.ComplexRealTangentTopology
import QuaternionicSymmetry.ComplexLieRealCompanion

/-! A holomorphic vector field is a real smooth vector field on the same
complex atlas, with identical underlying tangent vectors. -/
namespace QuaternionicSymmetry.HolomorphicVectorFieldRealSmooth
open HolomorphicTangentSectionCoordinates ComplexRealTangentTopology
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ,E) ∞ M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Scalar restriction in the same self-model atlas. -/
theorem real_contMDiffAt {f : M → E} {x : M}
    (hf : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,E) ∞ f x) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ f x := by
  rw [contMDiffAt_iff] at hf ⊢
  exact ⟨hf.1,hf.2.restrict_scalars ℝ⟩

theorem real_smooth (X : ContMDiffSection 𝓘(ℂ,E) E ∞ (TangentSpace 𝓘(ℂ,E) : M → Type _)) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞
      (fun x => (⟨x,X x⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
  letI : IsManifold 𝓘(ℂ,E) (∞+1) M := by simpa using (inferInstance : IsManifold 𝓘(ℂ,E) ∞ M)
  letI : IsManifold 𝓘(ℝ,E) (∞+1) M := by simpa using (inferInstance : IsManifold 𝓘(ℝ,E) ∞ M)
  let TC := tangentBundleCore 𝓘(ℂ,E) M
  let TR := tangentBundleCore 𝓘(ℝ,E) M
  letI : TC.IsContMDiff 𝓘(ℂ,E) ∞ := tangentBundleCore.isContMDiff
  letI : TR.IsContMDiff 𝓘(ℝ,E) ∞ := tangentBundleCore.isContMDiff
  intro x
  let i := achart E x
  letI : MemTrivializationAtlas (TC.localTriv i) := ⟨⟨i,rfl⟩⟩
  letI : MemTrivializationAtlas (TR.localTriv i) := ⟨⟨i,rfl⟩⟩
  have hi : x ∈ i.1.source := mem_chart_source E x
  apply ((TR.localTriv i).contMDiffAt_section_iff hi).2
  have h := real_contMDiffAt (((TC.localTriv i).contMDiffAt_section_iff hi).1 (X.contMDiff x))
  apply h.congr_of_eventuallyEq
  filter_upwards [i.1.open_source.mem_nhds hi] with y hy
  change tangentCoordChange 𝓘(ℝ,E) y x y (X y) = tangentCoordChange 𝓘(ℂ,E) y x y (X y)
  rw [coordChange_real_complex (E := E) y x y (mem_extChartAt_source y) (by simpa only [extChartAt_source] using hy)]
  rfl

end
end QuaternionicSymmetry.HolomorphicVectorFieldRealSmooth
