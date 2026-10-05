import QuaternionicSymmetry.ManifoldTwistorAmpleCoreBridge

/-! The generic represented-core and original coefficient descriptions
of complete twistor linear systems agree in both directions. This closes
the return path from Kodaira's actual `AmpleCore` to the project's
`AmpleContactLine`, without a new ampleness premise. -/

namespace QuaternionicSymmetry.ManifoldTwistorAmpleCoreReverseBridge

open ManifoldTwistorAmpleCoreBridge
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorProjectiveAmpleness ManifoldTwistorLinearSystem
open ManifoldQuaternionicMetric ManifoldQuaternionicConnection
open HolomorphicLineCoreAmpleFiniteMap HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A)

/-- Actual global generation of a generic positive contact power
transported back to the original coefficient-section presentation. -/
theorem twistorGenerated_of_genericGenerated (k : ℕ)
    (hGen : letI := A.charts
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D L) k)) :
    GloballyGeneratedTwist Q D L (k : ℤ) := by
  letI := A.charts
  intro x
  let e := coefficientPositiveTwistEquiv Q D L k
  obtain ⟨s,hs⟩ := hGen x
  refine ⟨e.symm s, ?_⟩
  have hpoint := coefficientPositiveTwistEquiv_apply Q D L k (e.symm s) x
  change e (e.symm s) x = _ at hpoint
  simpa [e, hpoint] using hs

/-- A complete projective embedding of the generic core gives the same
embedding and immersive derivative for the actual coefficient system. -/
theorem twistorVeryAmple_of_genericVeryAmple (k : ℕ)
    (hVery : letI := A.charts
      letI := A.complexManifold
      VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D L) k)) :
    VeryAmpleTwist Q D L k := by
  letI := A.charts
  letI := A.complexManifold
  obtain ⟨d,b,hGen,hEmbed,hDeriv⟩ := hVery
  let e := coefficientPositiveTwistEquiv Q D L k
  let bTw := b.map e.symm
  have hb : bTw.map e = b := by
    ext j
    simp [bTw]
  have hTwGen := twistorGenerated_of_genericGenerated Q D L k hGen
  have hBase := (globallyGeneratedTwist_iff_baseLocus_empty Q D L (k : ℤ)).1 hTwGen
  have hMap := transportedProjectiveMap_eq Q D L k d bTw hBase hGen
  rw [hb] at hMap
  refine ⟨d,bTw,hBase,?_,?_⟩
  · rw [← hMap]
    exact hEmbed
  · intro x
    rw [← hMap]
    exact hDeriv x

/-- Thus the positive Hermitian Kodaira conclusion on the selected
contact core supplies the original twistor ampleness property verbatim. -/
theorem ampleContactLine_of_ampleCore
    (hAmple : letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D L)) :
    AmpleContactLine Q D L := by
  letI := A.charts
  letI := A.complexManifold
  obtain ⟨k,hk,hVery⟩ := hAmple
  exact ⟨k,hk,twistorVeryAmple_of_genericVeryAmple Q D L k hVery⟩

end
end QuaternionicSymmetry.ManifoldTwistorAmpleCoreReverseBridge
