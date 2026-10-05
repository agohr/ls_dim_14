import QuaternionicSymmetry.ManifoldTwistorORSWSeedMetricSymmetry

/-! Strong induction over actual positive quaternionic-Kähler geometries.
The predicate quantifies over all supported model spaces and carriers, so
the induction can be instantiated on the genuine induced fixed manifold.
The seed and step arguments here are internal proof obligations; this helper
is not a source-only classification endpoint. -/

namespace QuaternionicSymmetry.Stage2ActualInduction

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldQuaternionicScalarCurvature ManifoldQuaternionicKSWEq38Input
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldQuaternionicHomothetyReduction ManifoldQuaternionicHomothetyConnection
open scoped Manifold ContDiff
noncomputable section

/-- Contact homogeneity on every actual normalized geometry in one dimension.
There is no fixed carrier, atlas, torus, or induction-closure assumption. -/
def NormalizedContactHomogeneity (n : ℕ) : Prop :=
  ∀ {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M)),
    Module.finrank ℝ E = 4*n →
    (∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) →
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
        ∀ z w : SphereBundleTotal P.tangent,
          ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
            f.1 z = w

/-- The actual `2…7` seed and `8…limit` step close by strong induction. -/
theorem through_bound (limit : ℕ)
    (hSeed : ∀ n, 2 ≤ n → n ≤ 7 → NormalizedContactHomogeneity n)
    (hStep : ∀ n, 8 ≤ n → n ≤ limit →
      (∀ m, 2 ≤ m → m < n → NormalizedContactHomogeneity m) →
      NormalizedContactHomogeneity n) :
    ∀ n, 2 ≤ n → n ≤ limit → NormalizedContactHomogeneity n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hLimit
    by_cases hSmall : n ≤ 7
    · exact hSeed n hn hSmall
    · apply hStep n (by omega) hLimit
      intro m hm hmn
      exact ih m hmn hm (by omega)

/-- The same geometric step can start at dimension two. The lower-dimensional
premise is empty in the first dimension, so no separate seed theorem is needed. -/
theorem through_bound_from_two (limit : ℕ)
    (hStep : ∀ n, 2 ≤ n → n ≤ limit →
      (∀ m, 2 ≤ m → m < n → NormalizedContactHomogeneity m) →
      NormalizedContactHomogeneity n) :
    ∀ n, 2 ≤ n → n ≤ limit → NormalizedContactHomogeneity n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hLimit
    apply hStep n hn hLimit
    intro m hm hmn
    exact ih m hmn hm (by omega)

/-- The induction conclusion supplies the exact rescaled full-Aut
homogeneity needed by the already proved higher-component section estimate.
Normalization and forgetting contact preservation are internal. -/
theorem exists_rescaled_fullAut_transitive
    {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (n : ℕ) (hn : 2 ≤ n) (hHom : NormalizedContactHomogeneity n)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 4*n)
    (heq38 : KSWEq38OnModel (E := E) (M := M)) :
    ∃ s : ℝ, ∃ hs : s ≠ 0,
      ∃ A : CompatibleComplexAtlas (rescaleMetric P.tangent s hs)
        (rescaleConnection P.tangent P.connection s hs) n,
        ∀ z w : SphereBundleTotal (rescaleMetric P.tangent s hs),
          ∃ f : TwistorHolomorphicAutomorphisms
            (rescaleMetric P.tangent s hs)
            (rescaleConnection P.tangent P.connection s hs) A,
            f.1 z = w := by
  let S := P.tangent.reduction.Q (achart E (Classical.choice ‹Nonempty M›))
  have hSn : S.quaternionicDimension = n := by
    have hS := S.real_finrank
    omega
  obtain ⟨s,hs,hScalar⟩ := exists_normalized_scalar S P heq38 (by omega)
  let R := rescaleCompact P s hs
  have hScalar' : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature R.tangent R.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2) := by
    simpa only [hSn] using hScalar
  obtain ⟨A,C,hContact⟩ := hHom R hDim hScalar'
  refine ⟨s,ne_of_gt hs,A,?_⟩
  intro z w
  obtain ⟨f,hf⟩ := hContact z w
  exact ⟨contactForget R.tangent R.connection A C.contact.line f,hf⟩

end
end QuaternionicSymmetry.Stage2ActualInduction
