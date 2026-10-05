import QuaternionicSymmetry.ManifoldTangentMapContinuousAt

/-! Pointwise C¹ joint regularity in a parameter and spatial variable
gives parameter-continuity of the spatial bundled derivative. -/
namespace QuaternionicSymmetry.ManifoldJointSpatialTangentContinuousAt

open Manifold
open ManifoldTangentMapContinuousAt
open scoped Manifold ContDiff
noncomputable section

variable {FG HG G FB HB B FC HC C : Type*}
  [NormedAddCommGroup FG] [NormedSpace ℝ FG]
  [TopologicalSpace HG] [TopologicalSpace G] [ChartedSpace HG G]
  [NormedAddCommGroup FB] [NormedSpace ℝ FB]
  [TopologicalSpace HB] [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup FC] [NormedSpace ℝ FC]
  [TopologicalSpace HC] [TopologicalSpace C] [ChartedSpace HC C]
  {IG : ModelWithCorners ℝ FG HG}
  {IB : ModelWithCorners ℝ FB HB}
  {IC : ModelWithCorners ℝ FC HC}
  [IsManifold IG 1 G] [IsManifold IB 1 B] [IsManifold IC 1 C]

theorem continuousAt_spatialTangentFamily
    {F : G × B → C} {g₀ : G} {v₀ : TangentBundle IB B}
    (hF : ContMDiffAt (IG.prod IB) IC 1 F (g₀,v₀.1)) :
    ContinuousAt (fun p : G × TangentBundle IB B =>
      tangentMap IB IC (fun b => F (p.1,b)) p.2) (g₀,v₀) := by
  let T₁ : G × TangentBundle IB B →
      TangentBundle IG G × TangentBundle IB B :=
    fun p => (⟨p.1,0⟩,p.2)
  have h₁ : Continuous T₁ := by
    have hg : Continuous (fun g : G =>
        (⟨g,0⟩ : TangentBundle IG G)) :=
      (Bundle.contMDiff_zeroSection (IB := IG) (n := 1) ℝ
        (TangentSpace IG : G → Type _)).continuous
    exact (hg.comp continuous_fst).prodMk continuous_snd
  let T₂ := (equivTangentBundleProd IG G IB B).symm
  have h₂ : Continuous T₂ :=
    (contMDiff_equivTangentBundleProd_symm (n := 1)
      (I := IG) (I' := IB)).continuous
  let q₀ := T₂ (T₁ (g₀,v₀))
  have hq : q₀.1 = (g₀,v₀.1) := rfl
  have hF' : ContMDiffAt (IG.prod IB) IC 1 F q₀.1 := hq ▸ hF
  have h₃ : ContinuousAt (tangentMap (IG.prod IB) IC F) q₀ :=
    continuousAt_tangentMap_of_contMDiffAt hF'
  have hcontinuous : ContinuousAt
      (fun p : G × TangentBundle IB B =>
        tangentMap (IG.prod IB) IC F (T₂ (T₁ p))) (g₀,v₀) :=
    ContinuousAt.comp (f := fun p : G × TangentBundle IB B => T₂ (T₁ p))
      h₃ (h₂.comp h₁).continuousAt
  have hnear : ∀ᶠ q : G × B in nhds (g₀,v₀.1),
      ContMDiffAt (IG.prod IB) IC 1 F q :=
    (contMDiffAt_iff_contMDiffAt_nhds (I := IG.prod IB) (I' := IC)
      (n := (1 : WithTop ℕ∞)) (by simp)).mp hF
  have hbase : Continuous (fun p : G × TangentBundle IB B => (p.1,p.2.1)) := by
    have hproj : Continuous (fun w : TangentBundle IB B => w.1) :=
      FiberBundle.continuous_proj FB (TangentSpace IB)
    exact continuous_fst.prodMk (hproj.comp continuous_snd)
  have hnear' : ∀ᶠ p : G × TangentBundle IB B in nhds (g₀,v₀),
      MDifferentiableAt (IG.prod IB) IC F (p.1,p.2.1) :=
    (hbase.continuousAt.tendsto.eventually hnear).mono
      (fun _ hp => hp.mdifferentiableAt (by simp))
  apply hcontinuous.congr_of_eventuallyEq
  filter_upwards [hnear'] with p hmd
  have hc : F ∘ (fun b : B => (p.1,b)) =
      (fun b : B => F (p.1,b)) := rfl
  have hright : MDifferentiableAt IB (IG.prod IB)
      (fun b : B => (p.1,b)) p.2.1 :=
    ((contMDiff_const.prodMk contMDiff_id :
      ContMDiff IB (IG.prod IB) 1 (fun b : B => (p.1,b))).mdifferentiableAt (by simp))
  have hcomp := tangentMap_comp_at (I := IB) (I' := IG.prod IB) (I'' := IC)
    (f := fun b : B => (p.1,b)) (g := F) p.2 hmd hright
  rw [hc, tangentMap_prod_right] at hcomp
  exact hcomp

end
end QuaternionicSymmetry.ManifoldJointSpatialTangentContinuousAt
