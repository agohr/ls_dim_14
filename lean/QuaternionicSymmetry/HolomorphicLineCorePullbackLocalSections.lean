import QuaternionicSymmetry.HolomorphicLineCorePullback

/-! A holomorphic section *along* a holomorphic map is a holomorphic section
of the pulled-back line. This local version does not assume an ambient
section extending off the image. -/
namespace QuaternionicSymmetry.HolomorphicLineCorePullbackLocalSections
open QuaternionicSymmetry.HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {B B' H H' F F' : Type*}
  [TopologicalSpace B] [TopologicalSpace B']
  [TopologicalSpace H] [TopologicalSpace H']
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [ChartedSpace H B] [ChartedSpace H' B']
  (IB : ModelWithCorners ℂ F H)
  (IB' : ModelWithCorners ℂ F' H')
  {ι : Type*} (Z : VectorBundleCore ℂ B ℂ ι)
  [Z.IsContMDiff IB ∞]
  (f : B' → B) (hf : ContMDiff IB' IB ∞ f)

/-- The identity of local coordinates proves holomorphicity in the
pulled-back core from holomorphicity in the original total space. -/
theorem alongMap_contMDiffOn_pullback
    (U : Set B')
    (s : ∀ x : B', Z.Fiber (f x))
    (hs : ContMDiffOn IB' (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun x : B' => (⟨f x,s x⟩ : Bundle.TotalSpace ℂ Z.Fiber)) U) :
    letI := pullbackCore_isContMDiff IB IB' Z f hf
    ContMDiffOn IB' (IB'.prod 𝓘(ℂ,ℂ)) ∞
      (fun x : B' =>
        (⟨x,s x⟩ : Bundle.TotalSpace ℂ
          (pullbackCore Z f hf.continuous).Fiber)) U := by
  letI := pullbackCore_isContMDiff IB IB' Z f hf
  intro x hx
  let Z' := pullbackCore Z f hf.continuous
  let e := trivializationAt ℂ Z.Fiber (f x)
  let e' := trivializationAt ℂ Z'.Fiber x
  have he : f x ∈ e.baseSet := by
    change f x ∈ Z.baseSet (Z.indexAt (f x))
    exact Z.mem_baseSet_at (f x)
  have he' : x ∈ e'.baseSet := by
    change f x ∈ Z.baseSet (Z.indexAt (f x))
    exact Z.mem_baseSet_at (f x)
  apply (e'.contMDiffWithinAt_section U he').2
  have hcoord : ContMDiffWithinAt IB' 𝓘(ℂ,ℂ) ∞
      (fun y => (e ⟨f y,s y⟩).2) U x :=
    (Bundle.contMDiffWithinAt_totalSpace.mp (hs x hx)).2
  convert hcoord using 1

end
end QuaternionicSymmetry.HolomorphicLineCorePullbackLocalSections
