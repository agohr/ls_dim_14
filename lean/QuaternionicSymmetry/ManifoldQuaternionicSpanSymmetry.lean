import QuaternionicSymmetry.ManifoldQuaternionicFundamentalSymmetry

/-!
The direct tangent-span meaning of a quaternionic manifold symmetry. At each
point the endomorphism three-plane is transferred from an adapted orthonormal
frame to the actual tangent fiber. No complex structure is globally chosen.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicSpanSymmetry

open ManifoldQuaternionicReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- One of the adapted quaternionic generators on the genuine tangent fiber. -/
def tangentGenerator (x : M) (t : Fin 3) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x :=
  let i := (tangentBundleCore 𝓘(ℝ,E) M).indexAt x
  (Q.frames.fromFrame i x).comp
    ((VectorBundleFrameTransitions.quaternionicGenerator
      (Q.reduction.Q i) t).comp (Q.frames.toFrame i x))

/-- The quaternionic three-plane in endomorphisms of the actual tangent fiber. -/
def tangentSpan (x : M) :
    Submodule ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) :=
  Submodule.span ℝ (Set.range (tangentGenerator Q x))

/-- The differential intertwines each quaternionic tangent endomorphism with
an endomorphism in the target three-plane. -/
def PreservesSpanForward
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞) : Prop :=
  ∀ x A, A ∈ tangentSpan Q x →
    ∃ B, B ∈ tangentSpan Q (f x) ∧
      ∀ v : TangentSpace 𝓘(ℝ,E) x,
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x (A v) =
          B (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v)

/-- Two-sided preservation avoids a hidden surjectivity assumption on the
induced three-plane action. The two laws are exchanged by inversion. -/
def PreservesSpan (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞) : Prop :=
  PreservesSpanForward Q f ∧ PreservesSpanForward Q f.symm

/-- This is the actual metric/quaternionic-structure automorphism condition.
Identifying it with preservation of the fundamental four-form is a separate
pointwise normalizer theorem, not built into this definition. -/
def IsQuaternionicIsometry
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞) : Prop :=
  ManifoldQuaternionicFundamentalSymmetry.PreservesMetric Q f ∧ PreservesSpan Q f

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem span_forward_refl :
    PreservesSpanForward Q (Diffeomorph.refl 𝓘(ℝ,E) M ∞) := by
  intro x A hA
  refine ⟨A, hA, ?_⟩
  intro v
  simp [mfderiv_id]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem span_forward_trans
    {f g : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞}
    (hf : PreservesSpanForward Q f)
    (hg : PreservesSpanForward Q g) :
    PreservesSpanForward Q (f.trans g) := by
  intro x A hA
  obtain ⟨B, hB, hAB⟩ := hf x A hA
  obtain ⟨C, hC, hBC⟩ := hg (f x) B hB
  refine ⟨C, hC, ?_⟩
  intro v
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
    ((g : M → M) ∘ (f : M → M)) x (A v) =
      C (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
        ((g : M → M) ∘ (f : M → M)) x v)
  rw [mfderiv_comp x
    (g.contMDiff.mdifferentiable (by simp) (f x))
    (f.contMDiff.mdifferentiable (by simp) x)]
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g : M → M) (f x)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x (A v)) =
    C (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g : M → M) (f x)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v))
  rw [hAB v, hBC]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem span_refl :
    PreservesSpan Q (Diffeomorph.refl 𝓘(ℝ,E) M ∞) := by
  constructor
  · exact span_forward_refl Q
  · simpa only [Diffeomorph.symm_refl] using span_forward_refl Q

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem span_trans
    {f g : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞}
    (hf : PreservesSpan Q f) (hg : PreservesSpan Q g) :
    PreservesSpan Q (f.trans g) := by
  constructor
  · exact span_forward_trans Q hf.1 hg.1
  · have hfg : (f.trans g).symm = g.symm.trans f.symm := by
      apply Diffeomorph.ext
      intro x
      rfl
    rw [hfg]
    exact span_forward_trans Q hg.2 hf.2

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem span_symm
    {f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞}
    (hf : PreservesSpan Q f) : PreservesSpan Q f.symm := by
  constructor
  · exact hf.2
  · have hss : f.symm.symm = f := by
      apply Diffeomorph.ext
      intro x
      rfl
    rw [hss]
    exact hf.1

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem quaternionic_isometry_refl :
    IsQuaternionicIsometry Q (Diffeomorph.refl 𝓘(ℝ,E) M ∞) :=
  ⟨ManifoldQuaternionicFundamentalSymmetry.metric_refl Q, span_refl Q⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem quaternionic_isometry_trans
    {f g : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞}
    (hf : IsQuaternionicIsometry Q f)
    (hg : IsQuaternionicIsometry Q g) :
    IsQuaternionicIsometry Q (f.trans g) :=
  ⟨ManifoldQuaternionicFundamentalSymmetry.metric_trans Q hf.1 hg.1,
    span_trans Q hf.2 hg.2⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem quaternionic_isometry_symm
    {f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞}
    (hf : IsQuaternionicIsometry Q f) :
    IsQuaternionicIsometry Q f.symm :=
  ⟨ManifoldQuaternionicFundamentalSymmetry.metric_symm Q hf.1,
    span_symm Q hf.2⟩

/-- The actual quaternionic isometries of the given tangent geometry. This
group is ready for a maximal-torus action once the Lie/topological group
structure and the connected component are constructed. -/
def QuaternionicIsometries :=
  {f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞ // IsQuaternionicIsometry Q f}

instance : Group (QuaternionicIsometries Q) where
  mul f g := ⟨g.1.trans f.1,
    quaternionic_isometry_trans Q g.2 f.2⟩
  one := ⟨Diffeomorph.refl 𝓘(ℝ,E) M ∞,
    quaternionic_isometry_refl Q⟩
  inv f := ⟨f.1.symm, quaternionic_isometry_symm Q f.2⟩
  mul_assoc f g h := by
    apply Subtype.ext
    apply Diffeomorph.ext
    intro x
    rfl
  one_mul f := by
    apply Subtype.ext
    exact Diffeomorph.trans_refl f.1
  mul_one f := by
    apply Subtype.ext
    exact Diffeomorph.refl_trans f.1
  inv_mul_cancel f := by
    apply Subtype.ext
    exact Diffeomorph.self_trans_symm f.1

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem QuaternionicIsometries_mul_apply
    (f g : QuaternionicIsometries Q) (x : M) :
    ((f * g).1 : M → M) x = f.1 (g.1 x) := rfl

/-- Evaluation is the genuine action of the quaternionic-isometry group on
the underlying manifold. -/
instance : MulAction (QuaternionicIsometries Q) M where
  smul f x := f.1 x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem smul_eq_apply (f : QuaternionicIsometries Q) (x : M) :
    f • x = f.1 x := rfl

/-- The set of points fixed by a subgroup of actual quaternionic isometries.
Connected components and their induced tangent structures come later. -/
def fixedPoints (S : Subgroup (QuaternionicIsometries Q)) : Set M :=
  {x | ∀ f ∈ S, f • x = x}

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem isClosed_fixedPoints [T2Space M]
    (S : Subgroup (QuaternionicIsometries Q)) :
    IsClosed (fixedPoints Q S) := by
  have hset : fixedPoints Q S =
      ⋂ f : S, {x : M | f.1.1 x = x} := by
    ext x
    simp [fixedPoints, smul_eq_apply]
  rw [hset]
  exact isClosed_iInter (fun f => isClosed_eq f.1.1.continuous continuous_id)

end
end QuaternionicSymmetry.ManifoldQuaternionicSpanSymmetry
