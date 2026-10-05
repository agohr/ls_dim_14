import QuaternionicSymmetry.ManifoldQuaternionicImmersionLocalFrame
import QuaternionicSymmetry.QuaternionicRangeFrameCoordinates

/-! Local gauges for the exact pullback metric of a quaternionic immersion.
The neighborhoods and inverse gauges are constructed internally. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicImmersionLocalGauge
open ManifoldQuaternionicImmersionRange ManifoldQuaternionicSubmanifoldInput
open ManifoldPositiveQuaternionicKahlerGeometry QuaternionicRangeFrameCoordinates Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)) (ι : N → M)

structure LocalGauge (c : N) where
  Q : QuaternionicStructure F
  domain : Set N
  isOpen_domain : IsOpen domain
  mem_domain : c ∈ domain
  source : domain ⊆ (chartAt F c).source
  target : Set.MapsTo ι domain (chartAt E (ι c)).source
  embedding : N → F →L[ℝ] E
  toFrame : N → F →L[ℝ] F
  fromFrame : N → F →L[ℝ] F
  smooth_embedding : ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] E) ∞ embedding domain
  smooth_to : ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] F) ∞ toFrame domain
  smooth_from : ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] F) ∞ fromFrame domain
  to_from : ∀ x ∈ domain, ∀ v, toFrame x (fromFrame x v) = v
  from_to : ∀ x ∈ domain, ∀ v, fromFrame x (toFrame x v) = v
  inner_embedding : ∀ x ∈ domain, ∀ v w, inner ℝ (embedding x v) (embedding x w) = inner ℝ v w
  intertwines_I : ∀ x ∈ domain, ∀ v,
    embedding x (Q.I v) = (P.tangent.reduction.Q (achart E (ι c))).I (embedding x v)
  intertwines_J : ∀ x ∈ domain, ∀ v,
    embedding x (Q.J v) = (P.tangent.reduction.Q (achart E (ι c))).J (embedding x v)
  inclusion : ∀ x ∈ domain, ∀ v, embedding x (toFrame x v) =
    adaptedDerivative P ι (achart F c) (achart E (ι c)) x v

theorem exists_localGauge
    (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
    (hQ : QuaternionicTangentRange (F := F) P ι) (c : N) :
    Nonempty (LocalGauge (F := F) P ι c) := by
  obtain ⟨S,B,hB⟩ := ManifoldQuaternionicImmersionLocalFrame.exists_local_frame P ι hι hinj hQ c
  let A := adaptedDerivative P ι (achart F c) (achart E (ι c))
  let T : N → F →L[ℝ] F := fun x => (B x).adjoint.comp (A x)
  have hGood : ∀ᶠ x in 𝓝 c,
      x ∈ (chartAt F c).source ∧ ι x ∈ (chartAt E (ι c)).source ∧
      ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] E) ∞ B x ∧
      ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] F) ∞ T x ∧
      ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] F) ∞ (fun y => (T y).inverse) x ∧
      (T x).IsInvertible ∧
      (∀ v w, inner ℝ (B x v) (B x w) = inner ℝ v w) ∧
      (∀ v, B x (S.I v) = (P.tangent.reduction.Q (achart E (ι c))).I (B x v)) ∧
      (∀ v, B x (S.J v) = (P.tangent.reduction.Q (achart E (ι c))).J (B x v)) ∧
      (∀ v, B x (T x v) = A x v) := by
    filter_upwards [hB,(chartAt F c).open_source.mem_nhds (mem_chart_source F c),
      hι.continuous.continuousAt.preimage_mem_nhds
        ((chartAt E (ι c)).open_source.mem_nhds (mem_chart_source E (ι c)))] with x hx hxs hxt
    have hA := adaptedDerivative_contMDiffAt P ι hι (achart F c) (achart E (ι c)) x hxs hxt
    have hAi := adaptedDerivative_injective P ι hinj (achart F c) (achart E (ι c)) x hxs hxt
    have hT : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] F) ∞ T x :=
      (((ContinuousLinearMap.adjoint : (F →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] F)).contDiff.contDiffAt.contMDiffAt).comp x hx.1).clm_comp hA
    have hInv : (T x).IsInvertible :=
      ⟨coordinatesEquiv (A x) (B x) hx.2.1 hx.2.2.1 hAi,rfl⟩
    refine ⟨hxs,hxt,hx.1,hT,(hInv.contDiffAt_map_inverse.contMDiffAt).comp x hT,
      hInv,hx.2.1,hx.2.2.2.1,hx.2.2.2.2,?_⟩
    exact frame_coordinates (A x) (B x) hx.2.1 hx.2.2.1
  obtain ⟨W,hW,hWo,hWc⟩ := mem_nhds_iff.mp hGood
  exact ⟨{
    Q := S, domain := W, isOpen_domain := hWo, mem_domain := hWc
    source := fun x hx => (hW hx).1
    target := fun x hx => (hW hx).2.1
    embedding := B, toFrame := T, fromFrame := fun x => (T x).inverse
    smooth_embedding := fun x hx => (hW hx).2.2.1.contMDiffWithinAt
    smooth_to := fun x hx => (hW hx).2.2.2.1.contMDiffWithinAt
    smooth_from := fun x hx => (hW hx).2.2.2.2.1.contMDiffWithinAt
    to_from := fun x hx => (hW hx).2.2.2.2.2.1.self_apply_inverse
    from_to := fun x hx => (hW hx).2.2.2.2.2.1.inverse_apply_self
    inner_embedding := fun x hx => (hW hx).2.2.2.2.2.2.1
    intertwines_I := fun x hx => (hW hx).2.2.2.2.2.2.2.1
    intertwines_J := fun x hx => (hW hx).2.2.2.2.2.2.2.2.1
    inclusion := fun x hx => (hW hx).2.2.2.2.2.2.2.2.2 }⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicImmersionLocalGauge
