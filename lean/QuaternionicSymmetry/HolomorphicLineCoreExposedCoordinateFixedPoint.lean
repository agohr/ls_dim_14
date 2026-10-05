import QuaternionicSymmetry.ComplexProjectiveAnalyticTorusPreservation
import QuaternionicSymmetry.ComplexProjectiveCocharacterLimit
import QuaternionicSymmetry.ComplexProjectiveImageTorusAction
import QuaternionicSymmetry.HolomorphicLineCoreProjectiveAlgebraicImage
import QuaternionicSymmetry.HolomorphicLineCoreProjectiveBasisChangeImmersion

/-! An integrally exposed coordinate weight of the genuine complete linear
system has an actual torus-fixed point where that basis section is nonzero.
This follows by a literal projective orbit limit inside the compact image;
no fixed-point existence or geometric weight-span theorem is sourced. -/
namespace QuaternionicSymmetry.HolomorphicLineCoreExposedCoordinateFixedPoint

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation HolomorphicLineCoreProjectiveAlgebraicImage
open ProjectiveAnalyticAlgebraicSources ComplexProjectiveTopology
open ManifoldQuaternionicTorusAction TorusLaurentRepresentation TorusIntegralCocharacter
open ComplexProjectiveDiagonalAction ComplexProjectiveTorusPreservation
open ComplexProjectiveImageTorusAction ComplexProjectiveMaximalWeightLimit
open ComplexProjectiveCocharacterLimit
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section

variable {X F : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [CompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F X] [IsManifold 𝓘(ℂ,F) ∞ X]

theorem exists_fixedPoint_of_exposed_coordinate
    (L : LineCore.{0} (B := X) 𝓘(ℂ,F))
    {r d : ℕ} (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections 𝓘(ℂ,F) L))
    (hGen : GloballyGenerated 𝓘(ℂ,F) L)
    (hVery : HolomorphicLineCoreAmpleFiniteMap.VeryAmpleCore 𝓘(ℂ,F) L)
    (μ : Fin (d + 1) → Fin r → ℤ) (α : Torus r → X → X)
    (hα : ∀ t x,
      projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen (α t x) =
        projectiveAction μ (compactInclusion r t)
          (projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen x))
    (j : Fin (d + 1)) (u : Fin r → ℤ)
    (hMax : ∀ i, pairing (μ i) u ≤ pairing (μ j) u)
    (hFace : ∀ i, pairing (μ i) u = pairing (μ j) u → μ i = μ j) :
    ∃ x : X, (∀ t : Torus r, α t x = x) ∧ b j x ≠ 0 := by
  let f := projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen
  have hNonzero : ∃ x : X, b j x ≠ 0 := by
    by_contra h
    push_neg at h
    apply b.ne_zero j
    ext x
    exact h x
  obtain ⟨x,hx⟩ := hNonzero
  let v := basisEvaluation 𝓘(ℂ,F) L d b x
  have hv : v ≠ 0 := by
    intro hz
    exact hx (congrFun hz j)
  let m := pairing (μ j) u
  have hTop : ∃ i, pairing (μ i) u = m ∧ v i ≠ 0 := ⟨j,rfl,hx⟩
  let p := Projectivization.mk ℂ (topPart (fun i => pairing (μ i) u) m v)
    (topPart_ne_zero _ m v hTop)
  have hClosed : IsClosed (Set.range f) :=
    (isCompact_range (projectiveEvaluationOfGenerated_contMDiff
      𝓘(ℂ,F) L d b hGen).continuous).isClosed
  have hSmooth := projectiveEvaluationOfGenerated_contMDiff 𝓘(ℂ,F) L d b hGen
  obtain ⟨hEmb,hImm⟩ := HolomorphicLineCoreProjectiveBasisChangeImmersion.veryAmple_projectiveEvaluation_embedding_immersion 𝓘(ℂ,F) L hVery d b hGen
  have hAnalytic := HolomorphicEmbeddingLocalEquations.range_localHolomorphicEquations
    hSmooth hEmb hImm
  have hPres := ComplexProjectiveAnalyticTorusPreservation.mapsTo_of_compact
    μ (Set.range f) hAnalytic hClosed
    (compact_range_mapsTo μ f α hα)
  have hp : p ∈ Set.range f :=
    topPart_mem_of_invariant μ u m hMax v hv hTop (Set.range f) hClosed hPres ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := hp
  refine ⟨y,?_,?_⟩
  · intro t
    apply hEmb.injective
    change f (α t y) = f y
    calc
      f (α t y) = projectiveAction μ (compactInclusion r t) (f y) := hα t y
      _ = f y := by
        rw [hy]
        exact topPart_fixed_by_torus μ u (μ j) m hFace v hTop (compactInclusion r t)
  · have hpj : p ∈ affineDomain d j := by
      apply (mem_affineDomain_mk d j _ _).2
      simpa [topPart,m] using hx
    have hyj : f y ∈ affineDomain d j := hy.symm ▸ hpj
    exact (mem_affineDomain_mk d j
      (basisEvaluation 𝓘(ℂ,F) L d b y) _).1 hyj

end
end QuaternionicSymmetry.HolomorphicLineCoreExposedCoordinateFixedPoint
