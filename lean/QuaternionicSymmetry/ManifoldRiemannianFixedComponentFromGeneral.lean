import QuaternionicSymmetry.ManifoldRiemannianFixedComponentGenericInput

/-! Quaternionic-isometry fixed components from the general Riemannian theorem.

Regard the subgroup as a set of metric-preserving diffeomorphisms. Its fixed
locus and fixed tangent vectors agree with the general definitions, so the
chosen atlas, smooth inclusion and derivative properties transfer directly.
This does not assert induced geometry on an arbitrary atlas; that is supplied
separately by the repaired quaternionic-submanifold interfaces.
The proof was first checked in contract-audit experiment E10. -/
namespace QuaternionicSymmetry.ManifoldRiemannianFixedComponentFromGeneral
open QuaternionicSymmetry
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicFixedTangentDimension
open scoped Manifold ContDiff
noncomputable section


variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def diffeomorphismSet
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (S : Subgroup (QuaternionicIsometries Q)) :
    Set (Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞) :=
  Subtype.val '' (S : Set (QuaternionicIsometries Q))

theorem fixedPoints_eq
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (S : Subgroup (QuaternionicIsometries Q)) :
    ManifoldRiemannianFixedComponentGenericInput.fixedPoints 𝓘(ℝ,E) (diffeomorphismSet Q S) = fixedPoints Q S := by
  ext x
  simp [ManifoldRiemannianFixedComponentGenericInput.fixedPoints, diffeomorphismSet, fixedPoints, smul_eq_apply]
  constructor
  · intro h f hf
    exact h f.val f.property hf
  · intro h f hf hS
    exact h ⟨f,hf⟩ hS

theorem specializedFixedComponents_of_general
    (h : ManifoldRiemannianFixedComponentGenericInput.RiemannianFixedComponentOnModel (F := E) (H := E) (N := M) 𝓘(ℝ,E)) :
    ManifoldRiemannianFixedComponentInput.RiemannianFixedComponentOnModel (E := E) (M := M) := by
  intro hFinite hNontrivial hManifold hT2 hSecond Q S x hx
  have hmetric : ∀ f ∈ diffeomorphismSet Q S,
      ManifoldRiemannianFixedComponentGenericInput.PreservesMetric 𝓘(ℝ,E) Q.riemannianMetric f := by
    rintro f ⟨g,hg,rfl⟩
    exact g.property.1
  have hfixed := fixedPoints_eq Q S
  have hx' : x ∈ ManifoldRiemannianFixedComponentGenericInput.fixedPoints 𝓘(ℝ,E) (diffeomorphismSet Q S) := by
    rwa [hfixed]
  obtain ⟨k,⟨A⟩⟩ := h Q.riemannianMetric (diffeomorphismSet Q S) hmetric x hx'
  rcases A with ⟨charts,hmanifold,hincl,hinj,htangent⟩
  simp only [ManifoldRiemannianFixedComponentGenericInput.fixedVectors,
    Set.mem_setOf_eq, eq_rec_constant] at htangent
  revert charts hmanifold hincl hinj htangent
  simp only [ManifoldRiemannianFixedComponentGenericInput.FixedComponent]
  rw [hfixed]
  intro charts hmanifold hincl hinj htangent
  refine ⟨k,⟨{ charts := charts
               manifold := hmanifold
               inclusion_smooth := hincl
               inclusion_injective_derivative := hinj
               tangent_eq := ?_ }⟩⟩
  letI := charts
  intro y
  ext v
  rw [htangent y v]
  simp [diffeomorphismSet, fixedTangentSpace]
  constructor
  · intro h f hf
    exact h f.val f.property hf
  · intro h f hf hS
    exact h ⟨f,hf⟩ hS

end
end QuaternionicSymmetry.ManifoldRiemannianFixedComponentFromGeneral
