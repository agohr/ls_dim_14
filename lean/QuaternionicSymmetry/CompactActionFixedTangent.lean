import QuaternionicSymmetry.SmoothChartDerivativeEquiv
import QuaternionicSymmetry.CompactActionFixedLocalChart

/-! Equivariant smooth charts conjugate the actual action derivatives and
identify their common fixed tangent subspaces. -/
namespace QuaternionicSymmetry.CompactActionFixedTangent
open Set Filter CompactActionFixedLocalChart
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 600000

variable {A E H K M : Type}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  [Group K] [TopologicalSpace K] [ChartedSpace A K]

/-- Common fixed vectors of the actual spatial action derivatives. -/
def fixedDerivatives (a : K × M → M) (x : M) : Submodule ℝ E where
  carrier := {v | ∀ g, mfderiv I I (fun y => a (g,y)) x v = v}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw g; simp [map_add,hv g,hw g]
  smul_mem' := by intro c v hv g; simp [map_smul,hv g]

lemma fixed_derivative_finrank
    (a : K × M → M) (ha : ContMDiff (𝓘(ℝ,A).prod I) I ∞ a)
    (ρ : K →* E →L[ℝ] E) (e : OpenPartialHomeomorph M E)
    (he : ContMDiffOn I 𝓘(ℝ,E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ,E) I ∞ e.symm e.target)
    (heq : ∀ y ∈ e.source, ∀ g, e (a (g,y)) = ρ g (e y))
    {x : M} (hx : x ∈ e.source) (hfix : ∀ g, a (g,x) = x) :
    Module.finrank ℝ (fixedDerivatives (I := I) a x) = Module.finrank ℝ (fixedSubspace ρ) := by
  obtain ⟨D,hD⟩ := SmoothChartDerivativeEquiv.exists_derivative_equiv e he hei hx
  have hconj (g : K) (v : E) : D (mfderiv I I (fun y => a (g,y)) x v) = ρ g (D v) := by
    have hh : (e ∘ fun y => a (g,y)) =ᶠ[𝓝 x] ((ρ g) ∘ e) := by
      filter_upwards [e.open_source.mem_nhds hx] with y hy
      exact heq y hy g
    have hs : MDifferentiableAt I I (fun y => a (g,y)) x :=
      (ha.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp)
    have heD := (he.contMDiffAt (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
    have heD' : MDifferentiableAt I 𝓘(ℝ,E) e (a (g,x)) := by rwa [hfix]
    have hhD := hh.mfderiv_eq (I := I) (I' := 𝓘(ℝ,E))
    rw [mfderiv_comp x heD' hs,mfderiv_comp x
      (((ρ g).contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp)) heD,
      hfix,mfderiv_eq_fderiv,(ρ g).fderiv] at hhD
    change (D : E →L[ℝ] E) (mfderiv I I (fun y => a (g,y)) x v) = ρ g ((D : E →L[ℝ] E) v)
    rw [hD]
    exact congrArg (fun B : E →L[ℝ] E => B v) hhD
  let L : fixedDerivatives (I := I) a x →ₗ[ℝ] fixedSubspace ρ := {
    toFun := fun v => ⟨D v,fun g => by rw [← hconj g v,v.2 g]⟩
    map_add' := by intros; apply Subtype.ext; exact D.map_add _ _
    map_smul' := by intros; apply Subtype.ext; exact D.map_smul _ _ }
  have hbij : Function.Bijective L := by
    constructor
    · intro v w h
      apply Subtype.ext
      exact D.injective (congrArg Subtype.val h)
    · intro v
      refine ⟨⟨D.symm v,?_⟩,?_⟩
      · intro g
        apply D.injective
        rw [hconj,D.apply_symm_apply,v.2 g]
      · apply Subtype.ext
        exact D.apply_symm_apply v
  exact (LinearEquiv.ofBijective L hbij).finrank_eq

end
end QuaternionicSymmetry.CompactActionFixedTangent
