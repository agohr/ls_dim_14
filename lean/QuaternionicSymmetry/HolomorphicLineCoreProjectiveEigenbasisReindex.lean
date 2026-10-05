import QuaternionicSymmetry.HolomorphicLineCoreProjectiveEigenbasis
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerFromSources

/-! Reindex a genuine finite-dimensional torus eigenbasis by the index of
an independently constructed complete projective system.  This does not
transfer embedding or immersion claims; those are basis-invariant geometry
handled separately. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreProjectiveEigenbasisReindex

open ManifoldQuaternionicTorusAction TorusCharacterInput
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicContactPowerWeights
open ManifoldQuaternionicContactPowerContinuity
open ManifoldQuaternionicContactPowerFromSources
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open HolomorphicLineCorePullback HolomorphicLineTensorPowerClasses
open CompactTorusEigenbasisSource
open scoped Manifold ContDiff
noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem reindex_integral_eigenbasis {r d : ℕ}
    (b₀ : Module.Basis (Fin (d + 1)) ℂ V)
    (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V)
    (μ : Fin (Module.finrank ℂ V) → Fin r → ℤ)
    (T : Torus r →* Module.End ℂ V)
    (hEig : ∀ (t : Torus r) (i : Fin (Module.finrank ℂ V)),
      T t (b i) = (weightCharacter (μ i) t : ℂ) • b i) :
    ∃ b' : Module.Basis (Fin (d + 1)) ℂ V,
      ∃ μ' : Fin (d + 1) → Fin r → ℤ,
        ∀ (t : Torus r) (i : Fin (d + 1)),
          T t (b' i) = (weightCharacter (μ' i) t : ℂ) • b' i := by
  have hd : Module.finrank ℂ V = d + 1 := by
    simpa using Module.finrank_eq_card_basis b₀
  let e : Fin (Module.finrank ℂ V) ≃ Fin (d + 1) := finCongr hd
  refine ⟨b.reindex e, (fun i => μ (e.symm i)), ?_⟩
  intro t i
  simpa [Module.Basis.reindex_apply] using hEig t (e.symm i)

/-- The source-derived actual contact-power eigenbasis can be indexed by
the same `Fin (d+1)` as any existing complete-projective-system basis. -/
theorem exists_contactPower_eigenbasis_on_projective_index
    {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M]
    [SecondCountableTopology M] [PreconnectedSpace M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    {r : ℕ} (A : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k d : ℕ)
    (b₀ : letI := B.charts;
      Module.Basis (Fin (d + 1)) ℂ (PowerSections Q D B C k)) :
    letI := B.charts
    ∃ b : Module.Basis (Fin (d + 1)) ℂ (PowerSections Q D B C k),
      ∃ μ : Fin (d + 1) → Fin r → ℤ,
        ∀ (t : Torus r) (i : Fin (d + 1)),
          contactPowerTorusRepresentation Q A D B C k t (b i) =
            (weightCharacter (μ i) t : ℂ) • b i := by
  letI := B.charts
  obtain ⟨b, μ, hμ⟩ :=
    exists_integral_eigenbasis_from_sources Q hR3 hFinite hEigen hCircle A D B C k
  exact reindex_integral_eigenbasis b₀ b μ
    (contactPowerTorusRepresentation Q A D B C k) hμ

end
end QuaternionicSymmetry.HolomorphicLineCoreProjectiveEigenbasisReindex
