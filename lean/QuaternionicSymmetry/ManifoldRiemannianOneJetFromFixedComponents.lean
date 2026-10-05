import QuaternionicSymmetry.ManifoldLocalDiffeomorphism
import QuaternionicSymmetry.ManifoldRiemannianFixedComponentGenericInput
import QuaternionicSymmetry.ManifoldRiemannianOneJetInput
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Connected.Clopen

/-! One-jet rigidity from general Riemannian fixed components.

An isometry fixing a point with identity derivative has a full-dimensional
fixed component. Mathlib's inverse function theorem makes its inclusion open;
the component is also closed and nonempty, so connectedness makes it the whole
manifold. Applying this to the quotient of two isometries proves the existing
one-jet contract. The only literature premise is the general fixed-component
theorem; no quaternionic-preservation or compactness assumption is used.
The proof was first checked in contract-audit experiment E15. -/
namespace QuaternionicSymmetry.ManifoldRiemannianOneJetFromFixedComponents
open QuaternionicSymmetry
open scoped Manifold ContDiff Topology
open Set Filter
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

lemma map_nhds_eq_of_bijective_mfderiv {f : M → N} (x : M)
    (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f x)
    (hb : Function.Bijective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x)) :
    Filter.map f (𝓝 x) = 𝓝 (f x) :=
  ManifoldLocalDiffeomorphism.map_nhds_eq_of_bijective_mfderiv x hf hb

lemma isOpenMap_of_bijective_mfderiv {f : M → N}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (hb : ∀ x, Function.Bijective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x)) : IsOpenMap f :=
  ManifoldLocalDiffeomorphism.isOpenMap_of_bijective_mfderiv hf hb


end

section Riemannian
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [SecondCountableTopology M] [PreconnectedSpace M]

open ManifoldRiemannianFixedComponentGenericInput

lemma isometry_eq_id_of_fixed_deriv
    (hFixed : RiemannianFixedComponentOnModel (F := E) (H := E) (N := M) 𝓘(ℝ,E))
    (g : SmoothMetric (F := E) (N := M) 𝓘(ℝ,E))
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (hmetric : PreservesMetric 𝓘(ℝ,E) g f)
    (x : M) (hx : f x = x)
    (hd : ∀ v : E, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v = v) :
    ∀ y, f y = y := by
  let S : Set (Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞) := {f}
  have hS : ∀ a ∈ S, PreservesMetric 𝓘(ℝ,E) g a := by
    intro a ha
    simpa only [S, Set.mem_singleton_iff] using ha ▸ hmetric
  have hxS : x ∈ fixedPoints 𝓘(ℝ,E) S := by
    simpa [fixedPoints, S] using hx
  obtain ⟨k,⟨A⟩⟩ := hFixed g S hS x hxS
  let C := connectedComponentIn (fixedPoints 𝓘(ℝ,E) S) x
  letI := A.charts
  letI := A.manifold
  let i : FixedComponent 𝓘(ℝ,E) S x → M := Subtype.val
  let y0 : FixedComponent 𝓘(ℝ,E) S x := ⟨x, mem_connectedComponentIn hxS⟩
  have hb0 : Function.Bijective
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E) i y0) := by
    refine ⟨A.inclusion_injective_derivative y0, ?_⟩
    intro v
    have hv : v ∈ LinearMap.range
        (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E) i y0).toLinearMap := by
      apply (A.tangent_eq y0 v).mpr
      simpa [fixedVectors, S, y0, eq_rec_constant] using hd v
    exact hv
  let D0 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E :=
    (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E) i y0).toLinearMap
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = Module.finrank ℝ E :=
    (LinearEquiv.ofBijective D0 hb0).finrank_eq
  have hbi : ∀ y, Function.Bijective
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E) i y) := by
    intro y
    let D : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E :=
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E) i y).toLinearMap
    have hi : Function.Injective D := A.inclusion_injective_derivative y
    exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩
  have hopen : IsOpen C := by
    have h := (isOpenMap_of_bijective_mfderiv A.inclusion_smooth hbi).isOpen_range
    simpa [i, C, FixedComponent] using h
  have hclosedS : IsClosed (fixedPoints 𝓘(ℝ,E) S) := by
    simpa [fixedPoints, S] using isClosed_eq f.continuous continuous_id
  have hclosed : IsClosed C := by
    rw [show C = Subtype.val '' connectedComponent (⟨x,hxS⟩ : fixedPoints 𝓘(ℝ,E) S) from
      connectedComponentIn_eq_image hxS]
    exact hclosedS.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  have hC : C = Set.univ := (IsClopen.eq_univ ⟨hclosed,hopen⟩ ⟨x,mem_connectedComponentIn hxS⟩)
  intro y
  have hy : y ∈ C := by rw [hC]; trivial
  have hyS := connectedComponentIn_subset (fixedPoints 𝓘(ℝ,E) S) x hy
  simpa [fixedPoints, S] using hyS


omit [T2Space M] [SecondCountableTopology M] [PreconnectedSpace M] in
/-- The literal original one-jet input follows from the retained general
fixed-component input, with no compactness or quaternionic preservation. -/
theorem oneJet_of_general_fixedComponents
    (hFixed : RiemannianFixedComponentOnModel (F := E) (H := E) (N := M) 𝓘(ℝ,E)) :
    ManifoldRiemannianOneJetInput.RiemannianOneJetRigidityOnModel (E := E) (M := M) := by
  intro hFinite hNontrivial hManifold hT2 hSecond hConnected Q f g hf hg x hx hd
  let a := f.trans g.symm
  have haMetric : PreservesMetric 𝓘(ℝ,E) Q.riemannianMetric a :=
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
  have ha := isometry_eq_id_of_fixed_deriv hFixed Q.riemannianMetric a
    haMetric x haPoint haDeriv
  apply Diffeomorph.ext
  intro y
  have h := congrArg g (ha y)
  simpa [a] using h

end Riemannian
end QuaternionicSymmetry.ManifoldRiemannianOneJetFromFixedComponents
