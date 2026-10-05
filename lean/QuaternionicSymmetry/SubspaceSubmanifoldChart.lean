import QuaternionicSymmetry.OpenPartialHomeomorphSubsetRestriction
import QuaternionicSymmetry.SmoothInverseChart
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Local submanifold charts cut out by an ambient linear subspace. -/
namespace QuaternionicSymmetry.SubspaceSubmanifoldChart
open OpenPartialHomeomorphSubsetRestriction Set
open scoped Manifold ContDiff Topology
noncomputable section

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

structure LocalChart (S : Set M) (k : ℕ) where
  chart : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k))
  extension : M → EuclideanSpace ℝ (Fin k)
  ambientSource : Set M
  open_ambientSource : IsOpen ambientSource
  source_subset : ∀ x ∈ chart.source, x.1 ∈ ambientSource
  extension_smooth : ContMDiffOn I 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞
    extension ambientSource
  extension_eq : ∀ x ∈ chart.source, chart x = extension x.1
  inverse_smooth : ContMDiffOn 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I ∞
    (Subtype.val ∘ chart.symm) chart.target

lemma exists_local_chart {S : Set M} [Nonempty S]
    (e : OpenPartialHomeomorph M E) (W : Submodule ℝ E)
    (h : e.IsImage S (W : Set E))
    (he : ContMDiffOn I 𝓘(ℝ,E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ,E) I ∞ e.symm e.target) :
    ∃ C : LocalChart (I := I) S (Module.finrank ℝ W),
      C.chart.source = Subtype.val ⁻¹' e.source := by
  let q := restrictSubsets e S (W : Set E) h
  let L : W ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ W)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let c := q.trans L.toHomeomorph.toOpenPartialHomeomorph
  obtain ⟨P,hP⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := W.subtypeL) Subtype.val_injective
  have hsource : c.source = Subtype.val ⁻¹' e.source := by simp [c,q,restrictSubsets]
  have hc (x : S) (hx : x ∈ c.source) : c x = L (P (e x.1)) := by
    change L (q x) = L (P (e x.1))
    congr 1
    have hv : (q x).1 = e x.1 := restrictSubsets_apply e S (W : Set E) h (by change x ∈ Subtype.val ⁻¹' e.source; rwa [← hsource])
    rw [← hv]
    exact (hP (q x)).symm
  have hci (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ W))) (hy : y ∈ c.target) :
      (c.symm y).1 = e.symm (W.subtypeL (L.symm y)) := by
    exact restrictSubsets_symm_apply e S (W : Set E) h hy.2
  refine ⟨⟨c,(fun x => L (P (e x))),e.source,e.open_source,?_,?_,hc,?_⟩,hsource⟩
  · intro x hx
    change x ∈ Subtype.val ⁻¹' e.source
    rwa [← hsource]
  · exact L.contDiff.contMDiff.comp_contMDiffOn
      (P.contDiff.contMDiff.comp_contMDiffOn he)
  · have hi : ContMDiffOn 𝓘(ℝ,EuclideanSpace ℝ (Fin (Module.finrank ℝ W))) I ∞
        (fun y => e.symm (W.subtypeL (L.symm y))) c.target := hei.comp
      ((W.subtypeL.contDiff.contMDiff.comp L.symm.contDiff.contMDiff).contMDiffOn)
      (fun y hy => hy.2)
    exact hi.congr hci

lemma transition_smooth {S : Set M} {k l : ℕ}
    (C : LocalChart (I := I) S k) (D : LocalChart (I := I) S l) :
    ContDiffOn ℝ ∞ (D.chart ∘ C.chart.symm) (C.chart.symm.trans D.chart).source := by
  have h := D.extension_smooth.comp (C.inverse_smooth.mono inter_subset_left)
    (fun y hy => D.source_subset _ hy.2)
  exact h.contDiffOn.congr (fun y hy => D.extension_eq _ hy.2)

end
end QuaternionicSymmetry.SubspaceSubmanifoldChart
