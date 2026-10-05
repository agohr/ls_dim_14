import QuaternionicSymmetry.ManifoldQuaternionicContactPowerFaithfulness
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerWeights

/-! A nontrivial actual torus action has a nonzero integral eigenweight
on every genuinely very ample contact power. This follows from the proved
projective faithfulness of the full section action, not a weight premise. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactNonzeroSectionWeight

open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicContactPowerContinuity ManifoldQuaternionicContactPowerWeights
open ManifoldQuaternionicContactPowerFaithfulness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open HolomorphicLineTensorPowerClasses HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem faithful_positive_rank_nontrivial
    {r : ℕ} (A : ContinuousTorusAction Q r) (hA : A.Faithful) (hr : 0 < r) :
    ∃ t : Torus r, A.representation t ≠ 1 := by
  let c : Circle := ⟨-1, by
    change (-1 : ℂ) ∈ Metric.sphere 0 1
    simp [Metric.mem_sphere, dist_eq_norm]⟩
  have hc : c ≠ 1 := by
    intro h
    have he := congrArg (fun z : Circle => (z : ℂ)) h
    change (-1 : ℂ) = 1 at he
    norm_num at he
  refine ⟨fun _ => c, ?_⟩
  intro ht
  have he : (fun _ : Fin r => c) = 1 :=
    hA (ht.trans A.representation.map_one.symm)
  exact hc (congrFun he ⟨0,hr⟩)

theorem exists_nonzero_sectionWeight_of_nontrivial
    {r : ℕ} (A : ContinuousTorusAction Q r)
    (hA : ∃ t : Torus r, A.representation t ≠ 1)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hVery : letI := B.charts; letI := B.complexManifold
      VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k))
    {ι : Type*} (b : letI := B.charts; Module.Basis ι ℂ (PowerSections Q D B C k))
    (μ : ι → Fin r → ℤ)
    (hEig : letI := B.charts; ∀ (t : Torus r) (i : ι),
      contactPowerTorusRepresentation Q A D B C k t (b i) =
        (weightCharacter (μ i) t : ℂ) • b i) :
    ∃ i, μ i ≠ 0 := by
  letI := B.charts
  letI := B.complexManifold
  by_contra! hz
  obtain ⟨t,ht⟩ := hA
  apply ht
  apply eq_one_of_scalar_contactPowerAction Q D B C k hVery (A.representation t) 1
  have hLin : contactPowerTorusRepresentation Q A D B C k t = LinearMap.id := by
    apply b.ext
    intro i
    simpa [hz i,weightCharacter] using hEig t i
  intro s
  have hs := LinearMap.congr_fun hLin s
  simpa [contactPowerTorusRepresentation] using hs

end
end QuaternionicSymmetry.ManifoldQuaternionicContactNonzeroSectionWeight
