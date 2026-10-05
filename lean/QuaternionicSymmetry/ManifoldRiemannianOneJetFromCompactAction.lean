import QuaternionicSymmetry.ManifoldRiemannianOneJetInput
import QuaternionicSymmetry.ManifoldRiemannianFixedComponentGenericInput
import QuaternionicSymmetry.CompactActionOneJet
import QuaternionicSymmetry.ManifoldQuaternionicIsometryClosedFromAction
import QuaternionicSymmetry.ManifoldQuaternionicMetricIsometryDistance

/-! One-jet rigidity on the compact bases used by the final theorem. -/
namespace QuaternionicSymmetry.ManifoldRiemannianOneJetFromCompactAction
open Manifold ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldQuaternionicMetricIsometryDistance
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M]

lemma isometry_eq_id_of_fixed_deriv
    [T2Space M] [SecondCountableTopology M] [PreconnectedSpace M]
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hLee : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem)
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (hf : ManifoldQuaternionicFundamentalSymmetry.PreservesMetric Q f)
    (x : M) (hx : f x = x)
    (hd : ∀ v : E, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v = v) :
    ∀ y, f y = y := by
  letI : Nonempty M := ⟨x⟩
  letI : T3Space M := inferInstance
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  obtain ⟨V,hn,hs,hfin,hc,hm,hl,ha⟩ := hR3 Q
  letI := hn
  letI := hs
  letI := hfin
  letI := hc
  letI := hm
  letI := hl
  letI : CompactSpace (M ≃ᵢ M) := isometryEquiv_compactSpace (X := M)
  have hpairs : Topology.IsEmbedding (isometryEquivPairsEquiv (X := M)) :=
    ⟨⟨rfl⟩,(isometryEquivPairsEquiv (X := M)).injective⟩
  letI : T2Space (M ≃ᵢ M) := hpairs.t2Space
  letI : SecondCountableTopology (M ≃ᵢ M) :=
    ChartedSpace.secondCountable_of_sigmaCompact V (M ≃ᵢ M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := topologicalGroup_of_lieGroup 𝓘(ℝ,V) ∞
  exact CompactActionOneJet.eq_id_of_oneJet hLee
    (fun p : (M ≃ᵢ M) × M => p.1 p.2) ha
    (fun _ => rfl) (fun _ _ _ => rfl) (metricIsometryEquiv Q f hf) x hx hd

lemma oneJet
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hLee : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem) :
    ManifoldRiemannianOneJetInput.RiemannianOneJetRigidityOnModel (E := E) (M := M) := by
  intro hFinite hNontrivial hManifold hT2 hSecond hConnected Q f g hf hg x hx hd
  let a := f.trans g.symm
  have haMetric : ManifoldRiemannianFixedComponentGenericInput.PreservesMetric 𝓘(ℝ,E) Q.riemannianMetric a :=
    ManifoldQuaternionicFundamentalSymmetry.metric_trans Q hf
      (ManifoldQuaternionicFundamentalSymmetry.metric_symm Q hg)
  have haPoint : a x = x := by
    change g.symm (f x) = x
    rw [hx]
    exact g.symm_apply_apply x
  have haDeriv : ∀ v : E, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (a : M → M) x v = v := by
    have hid : (g.symm : M → M) ∘ (g : M → M) = id := by
      funext y
      exact g.symm_apply_apply y
    have hc := mfderiv_comp x
      (g.symm.contMDiff.mdifferentiable (by simp) (g x))
      (g.contMDiff.mdifferentiable (by simp) x)
    rw [hid, mfderiv_id] at hc
    intro v
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ((g.symm : M → M) ∘ (f : M → M)) x v = v
    rw [mfderiv_comp x
      (g.symm.contMDiff.mdifferentiable (by simp) (f x))
      (f.contMDiff.mdifferentiable (by simp) x)]
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g.symm : M → M) (f x)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v) = v
    rw [hd v]
    rw [hx]
    exact congrArg (fun D : E →L[ℝ] E => D v) hc.symm
  have ha := isometry_eq_id_of_fixed_deriv hR3 hLee Q a
    haMetric x haPoint haDeriv
  apply Diffeomorph.ext
  intro y
  have h := congrArg g (ha y)
  simpa [a] using h

end
end QuaternionicSymmetry.ManifoldRiemannianOneJetFromCompactAction
