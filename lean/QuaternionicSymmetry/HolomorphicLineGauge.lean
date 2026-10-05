import QuaternionicSymmetry.HolomorphicLineTensor

/-! Cover-independent holomorphic line-core isomorphisms.  A gauge gives
forward and inverse local scalar maps on every intersection of two covers,
with the transition compatibility on every four-chart overlap. -/

namespace QuaternionicSymmetry.HolomorphicLineGauge

open QuaternionicSymmetry.HolomorphicLinePowers
open scoped Manifold ContDiff
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace H B] {IB : ModelWithCorners ℂ F H}
  {ι κ : Type*}

/-- Multiplicative cocycle identity for scalar line transitions. -/
theorem scalar_comp {α : Type*}
    (Z : VectorBundleCore ℂ B ℂ α) (i j k : α) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet k) :
    transitionScalar Z j k x * transitionScalar Z i j x =
      transitionScalar Z i k x := by
  have h := Z.coordChange_comp i j k x hx (1 : ℂ)
  exact (linear_apply_one (Z.coordChange j k x)
    (Z.coordChange i j x 1)).symm.trans h

/-- A holomorphic line-bundle isomorphism stated on two arbitrary covers.
The scalar maps and their inverse are holomorphic on each intersection;
compatibility is imposed on *all* common four-chart overlaps. -/
structure GaugeIso (Z : VectorBundleCore ℂ B ℂ ι)
    (W : VectorBundleCore ℂ B ℂ κ)
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] where
  forward : ι → κ → B → ℂ
  backward : κ → ι → B → ℂ
  forward_holomorphic (i : ι) (a : κ) :
    ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (forward i a) (Z.baseSet i ∩ W.baseSet a)
  backward_holomorphic (a : κ) (i : ι) :
    ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (backward a i) (W.baseSet a ∩ Z.baseSet i)
  forward_compat (i j : ι) (a b : κ) (x : B)
      (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ W.baseSet a ∩ W.baseSet b) :
    transitionScalar W a b x * forward i a x =
      forward j b x * transitionScalar Z i j x
  backward_compat (a b : κ) (i j : ι) (x : B)
      (hx : x ∈ W.baseSet a ∩ W.baseSet b ∩ Z.baseSet i ∩ Z.baseSet j) :
    transitionScalar Z i j x * backward a i x =
      backward b j x * transitionScalar W a b x
  left_inverse (i : ι) (a : κ) (x : B)
      (hx : x ∈ Z.baseSet i ∩ W.baseSet a) :
    backward a i x * forward i a x = 1
  right_inverse (a : κ) (i : ι) (x : B)
      (hx : x ∈ W.baseSet a ∩ Z.baseSet i) :
    forward i a x * backward a i x = 1

/-- Every holomorphic line core is gauge-isomorphic to itself even when
the source and target copies use different chart indices. -/
def GaugeIso.refl (Z : VectorBundleCore ℂ B ℂ ι) [Z.IsContMDiff IB ∞] :
    GaugeIso (IB := IB) Z Z where
  forward i a x := transitionScalar Z i a x
  backward a i x := transitionScalar Z a i x
  forward_holomorphic i a :=
    (Z.contMDiffOn_coordChange IB i a).clm_apply contMDiffOn_const
  backward_holomorphic a i :=
    (Z.contMDiffOn_coordChange IB a i).clm_apply contMDiffOn_const
  forward_compat i j a b x hx := by
    have h₁ := scalar_comp Z i a b x ⟨⟨hx.1.1.1, hx.1.2⟩, hx.2⟩
    have h₂ := scalar_comp Z i j b x ⟨⟨hx.1.1.1, hx.1.1.2⟩, hx.2⟩
    exact h₁.trans h₂.symm
  backward_compat a b i j x hx := by
    have h₁ := scalar_comp Z a i j x ⟨⟨hx.1.1.1, hx.1.2⟩, hx.2⟩
    have h₂ := scalar_comp Z a b j x ⟨⟨hx.1.1.1, hx.1.1.2⟩, hx.2⟩
    exact h₁.trans h₂.symm
  left_inverse i a x hx := by
    have h := scalar_comp Z i a i x ⟨⟨hx.1, hx.2⟩, hx.1⟩
    exact h.trans (Z.coordChange_self i x hx.1 1)
  right_inverse a i x hx := by
    have h := scalar_comp Z a i a x ⟨⟨hx.1, hx.2⟩, hx.1⟩
    exact h.trans (Z.coordChange_self a x hx.1 1)

/-- An inverse holomorphic gauge is obtained by interchanging its two
families of local maps. -/
def GaugeIso.symm {Z : VectorBundleCore ℂ B ℂ ι}
    {W : VectorBundleCore ℂ B ℂ κ}
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]
    (e : GaugeIso (IB := IB) Z W) : GaugeIso (IB := IB) W Z where
  forward := e.backward
  backward := e.forward
  forward_holomorphic := e.backward_holomorphic
  backward_holomorphic := e.forward_holomorphic
  forward_compat := e.backward_compat
  backward_compat := e.forward_compat
  left_inverse := e.right_inverse
  right_inverse := e.left_inverse

/-- A holomorphic gauge is nondegenerate on every common chart. -/
theorem GaugeIso.forward_ne_zero {Z : VectorBundleCore ℂ B ℂ ι}
    {W : VectorBundleCore ℂ B ℂ κ}
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]
    (e : GaugeIso (IB := IB) Z W) (i : ι) (a : κ) (x : B)
    (hx : x ∈ Z.baseSet i ∩ W.baseSet a) : e.forward i a x ≠ 0 := by
  intro hz
  have h := e.left_inverse i a x hx
  rw [hz, mul_zero] at h
  exact zero_ne_one h

theorem GaugeIso.backward_ne_zero {Z : VectorBundleCore ℂ B ℂ ι}
    {W : VectorBundleCore ℂ B ℂ κ}
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]
    (e : GaugeIso (IB := IB) Z W) (a : κ) (i : ι) (x : B)
    (hx : x ∈ W.baseSet a ∩ Z.baseSet i) : e.backward a i x ≠ 0 := by
  intro hz
  have h := e.right_inverse a i x hx
  rw [hz, mul_zero] at h
  exact zero_ne_one h

private def composeLocal {τ : Type*}
    {Z : VectorBundleCore ℂ B ℂ ι}
    {W : VectorBundleCore ℂ B ℂ κ}
    {V : VectorBundleCore ℂ B ℂ τ}
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] [V.IsContMDiff IB ∞]
    (e : GaugeIso (IB := IB) Z W) (f : GaugeIso (IB := IB) W V)
    (i : ι) (c : τ) (x : B) : ℂ :=
  e.forward i (W.indexAt x) x * f.forward (W.indexAt x) c x

private theorem composeLocal_chart {τ : Type*}
    {Z : VectorBundleCore ℂ B ℂ ι}
    {W : VectorBundleCore ℂ B ℂ κ}
    {V : VectorBundleCore ℂ B ℂ τ}
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] [V.IsContMDiff IB ∞]
    (e : GaugeIso (IB := IB) Z W) (f : GaugeIso (IB := IB) W V)
    (i : ι) (a : κ) (c : τ) (x : B)
    (hx : x ∈ Z.baseSet i ∩ W.baseSet a ∩ V.baseSet c) :
    composeLocal e f i c x = e.forward i a x * f.forward a c x := by
  let k := W.indexAt x
  have hk : x ∈ W.baseSet k := W.mem_baseSet_at x
  have hZ : transitionScalar Z i i x = 1 := Z.coordChange_self i x hx.1.1 1
  have hW : transitionScalar W k k x = 1 := W.coordChange_self k x hk 1
  have hV : transitionScalar V c c x = 1 := V.coordChange_self c x hx.2 1
  have he := e.forward_compat i i a k x
    ⟨⟨⟨hx.1.1, hx.1.1⟩, hx.1.2⟩, hk⟩
  have hf := f.forward_compat a k c c x
    ⟨⟨⟨hx.1.2, hk⟩, hx.2⟩, hx.2⟩
  simp only [hZ, hV, mul_one, one_mul] at he hf
  dsimp [composeLocal]
  change e.forward i k x * f.forward k c x = _
  calc
    e.forward i k x * f.forward k c x =
        (transitionScalar W a k x * e.forward i a x) * f.forward k c x := by
      rw [he]
    _ = e.forward i a x * (f.forward k c x * transitionScalar W a k x) := by ring
    _ = e.forward i a x * f.forward a c x := by rw [← hf]

private theorem composeLocal_holomorphic {τ : Type*}
    {Z : VectorBundleCore ℂ B ℂ ι}
    {W : VectorBundleCore ℂ B ℂ κ}
    {V : VectorBundleCore ℂ B ℂ τ}
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] [V.IsContMDiff IB ∞]
    (e : GaugeIso (IB := IB) Z W) (f : GaugeIso (IB := IB) W V)
    (i : ι) (c : τ) :
    ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (composeLocal e f i c)
      (Z.baseSet i ∩ V.baseSet c) := by
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  let a := W.indexAt x
  refine ⟨W.baseSet a, W.isOpen_baseSet a, W.mem_baseSet_at x, ?_⟩
  have he : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (e.forward i a)
      ((Z.baseSet i ∩ V.baseSet c) ∩ W.baseSet a) :=
    (e.forward_holomorphic i a).mono (by
      intro y hy
      exact ⟨hy.1.1, hy.2⟩)
  have hf : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (f.forward a c)
      ((Z.baseSet i ∩ V.baseSet c) ∩ W.baseSet a) :=
    (f.forward_holomorphic a c).mono (by
      intro y hy
      exact ⟨hy.2, hy.1.2⟩)
  exact (he.mul hf).congr (by
    intro y hy
    exact composeLocal_chart e f i a c y
      ⟨⟨hy.1.1, hy.2⟩, hy.1.2⟩)

private theorem composeLocal_compat {τ : Type*}
    {Z : VectorBundleCore ℂ B ℂ ι}
    {W : VectorBundleCore ℂ B ℂ κ}
    {V : VectorBundleCore ℂ B ℂ τ}
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] [V.IsContMDiff IB ∞]
    (e : GaugeIso (IB := IB) Z W) (f : GaugeIso (IB := IB) W V)
    (i j : ι) (c d : τ) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ V.baseSet c ∩ V.baseSet d) :
    transitionScalar V c d x * composeLocal e f i c x =
      composeLocal e f j d x * transitionScalar Z i j x := by
  let k := W.indexAt x
  have hk : x ∈ W.baseSet k := W.mem_baseSet_at x
  have hW : transitionScalar W k k x = 1 := W.coordChange_self k x hk 1
  have he := e.forward_compat i j k k x
    ⟨⟨⟨hx.1.1.1, hx.1.1.2⟩, hk⟩, hk⟩
  have hf := f.forward_compat k k c d x
    ⟨⟨⟨hk, hk⟩, hx.1.2⟩, hx.2⟩
  simp only [hW, one_mul, mul_one] at he hf
  dsimp [composeLocal]
  change transitionScalar V c d x * (e.forward i k x * f.forward k c x) =
    (e.forward j k x * f.forward k d x) * transitionScalar Z i j x
  calc
    transitionScalar V c d x * (e.forward i k x * f.forward k c x) =
        e.forward i k x * (transitionScalar V c d x * f.forward k c x) := by ring
    _ = e.forward i k x * f.forward k d x := by rw [hf]
    _ = (e.forward j k x * f.forward k d x) * transitionScalar Z i j x := by
      rw [he]
      ring

/-- Gauge isomorphisms compose even when all three local covers differ.
At a point the middle cover chooses a chart; the overlap identities prove
that the resulting scalar is locally independent of this choice and hence
holomorphic. -/
def GaugeIso.trans {τ : Type*}
    {Z : VectorBundleCore ℂ B ℂ ι}
    {W : VectorBundleCore ℂ B ℂ κ}
    {V : VectorBundleCore ℂ B ℂ τ}
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] [V.IsContMDiff IB ∞]
    (e : GaugeIso (IB := IB) Z W) (f : GaugeIso (IB := IB) W V) :
    GaugeIso (IB := IB) Z V where
  forward := composeLocal e f
  backward := composeLocal f.symm e.symm
  forward_holomorphic := composeLocal_holomorphic e f
  backward_holomorphic := composeLocal_holomorphic f.symm e.symm
  forward_compat := composeLocal_compat e f
  backward_compat := composeLocal_compat f.symm e.symm
  left_inverse i c x hx := by
    let k := W.indexAt x
    have hk : x ∈ W.baseSet k := W.mem_baseSet_at x
    have he := e.left_inverse i k x ⟨hx.1, hk⟩
    have hf := f.left_inverse k c x ⟨hk, hx.2⟩
    change (f.backward c k x * e.backward k i x) *
      (e.forward i k x * f.forward k c x) = 1
    calc
      (f.backward c k x * e.backward k i x) *
          (e.forward i k x * f.forward k c x) =
        (f.backward c k x * f.forward k c x) *
          (e.backward k i x * e.forward i k x) := by ring
      _ = 1 := by rw [hf, he]; ring
  right_inverse c i x hx := by
    let k := W.indexAt x
    have hk : x ∈ W.baseSet k := W.mem_baseSet_at x
    have he := e.right_inverse k i x ⟨hk, hx.2⟩
    have hf := f.right_inverse c k x ⟨hx.1, hk⟩
    change (e.forward i k x * f.forward k c x) *
      (f.backward c k x * e.backward k i x) = 1
    calc
      (e.forward i k x * f.forward k c x) *
          (f.backward c k x * e.backward k i x) =
        (e.forward i k x * e.backward k i x) *
          (f.forward k c x * f.backward c k x) := by ring
      _ = 1 := by rw [he, hf]; ring

/-- Tensoring two holomorphic gauges gives a holomorphic gauge between
the tensor cores, including when all four covers differ. -/
def GaugeIso.tensor {ι' κ' : Type*}
    {Z : VectorBundleCore ℂ B ℂ ι}
    {W : VectorBundleCore ℂ B ℂ κ}
    {Z' : VectorBundleCore ℂ B ℂ ι'}
    {W' : VectorBundleCore ℂ B ℂ κ'}
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]
    [Z'.IsContMDiff IB ∞] [W'.IsContMDiff IB ∞]
    (e : GaugeIso (IB := IB) Z W) (f : GaugeIso (IB := IB) Z' W') :
    GaugeIso (IB := IB) (HolomorphicLineTensor.tensorCore Z Z')
      (HolomorphicLineTensor.tensorCore W W') where
  forward p q x := e.forward p.1 q.1 x * f.forward p.2 q.2 x
  backward q p x := e.backward q.1 p.1 x * f.backward q.2 p.2 x
  forward_holomorphic p q := by
    change ContMDiffOn IB 𝓘(ℂ,ℂ) ∞
      (fun x => e.forward p.1 q.1 x * f.forward p.2 q.2 x)
      ((Z.baseSet p.1 ∩ Z'.baseSet p.2) ∩ (W.baseSet q.1 ∩ W'.baseSet q.2))
    have he : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (e.forward p.1 q.1)
        ((Z.baseSet p.1 ∩ Z'.baseSet p.2) ∩ (W.baseSet q.1 ∩ W'.baseSet q.2)) :=
      (e.forward_holomorphic p.1 q.1).mono (by
      intro x hx
      exact ⟨hx.1.1, hx.2.1⟩)
    have hf : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (f.forward p.2 q.2)
        ((Z.baseSet p.1 ∩ Z'.baseSet p.2) ∩ (W.baseSet q.1 ∩ W'.baseSet q.2)) :=
      (f.forward_holomorphic p.2 q.2).mono (by
      intro x hx
      exact ⟨hx.1.2, hx.2.2⟩)
    exact he.mul hf
  backward_holomorphic q p := by
    change ContMDiffOn IB 𝓘(ℂ,ℂ) ∞
      (fun x => e.backward q.1 p.1 x * f.backward q.2 p.2 x)
      ((W.baseSet q.1 ∩ W'.baseSet q.2) ∩ (Z.baseSet p.1 ∩ Z'.baseSet p.2))
    have he : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (e.backward q.1 p.1)
        ((W.baseSet q.1 ∩ W'.baseSet q.2) ∩ (Z.baseSet p.1 ∩ Z'.baseSet p.2)) :=
      (e.backward_holomorphic q.1 p.1).mono (by
      intro x hx
      exact ⟨hx.1.1, hx.2.1⟩)
    have hf : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (f.backward q.2 p.2)
        ((W.baseSet q.1 ∩ W'.baseSet q.2) ∩ (Z.baseSet p.1 ∩ Z'.baseSet p.2)) :=
      (f.backward_holomorphic q.2 p.2).mono (by
      intro x hx
      exact ⟨hx.1.2, hx.2.2⟩)
    exact he.mul hf
  forward_compat p r q s x hx := by
    have he := e.forward_compat p.1 r.1 q.1 s.1 x
      ⟨⟨⟨hx.1.1.1.1, hx.1.1.2.1⟩, hx.1.2.1⟩, hx.2.1⟩
    have hf := f.forward_compat p.2 r.2 q.2 s.2 x
      ⟨⟨⟨hx.1.1.1.2, hx.1.1.2.2⟩, hx.1.2.2⟩, hx.2.2⟩
    simp only [HolomorphicLineTensor.tensorCore_transitionScalar]
    calc
      (transitionScalar W q.1 s.1 x * transitionScalar W' q.2 s.2 x) *
          (e.forward p.1 q.1 x * f.forward p.2 q.2 x) =
        (transitionScalar W q.1 s.1 x * e.forward p.1 q.1 x) *
          (transitionScalar W' q.2 s.2 x * f.forward p.2 q.2 x) := by ring
      _ = (e.forward r.1 s.1 x * f.forward r.2 s.2 x) *
          (transitionScalar Z p.1 r.1 x * transitionScalar Z' p.2 r.2 x) := by
        rw [he, hf]
        ring
  backward_compat q s p r x hx := by
    have he := e.backward_compat q.1 s.1 p.1 r.1 x
      ⟨⟨⟨hx.1.1.1.1, hx.1.1.2.1⟩, hx.1.2.1⟩, hx.2.1⟩
    have hf := f.backward_compat q.2 s.2 p.2 r.2 x
      ⟨⟨⟨hx.1.1.1.2, hx.1.1.2.2⟩, hx.1.2.2⟩, hx.2.2⟩
    simp only [HolomorphicLineTensor.tensorCore_transitionScalar]
    calc
      (transitionScalar Z p.1 r.1 x * transitionScalar Z' p.2 r.2 x) *
          (e.backward q.1 p.1 x * f.backward q.2 p.2 x) =
        (transitionScalar Z p.1 r.1 x * e.backward q.1 p.1 x) *
          (transitionScalar Z' p.2 r.2 x * f.backward q.2 p.2 x) := by ring
      _ = (e.backward s.1 r.1 x * f.backward s.2 r.2 x) *
          (transitionScalar W q.1 s.1 x * transitionScalar W' q.2 s.2 x) := by
        rw [he, hf]
        ring
  left_inverse p q x hx := by
    have he := e.left_inverse p.1 q.1 x ⟨hx.1.1, hx.2.1⟩
    have hf := f.left_inverse p.2 q.2 x ⟨hx.1.2, hx.2.2⟩
    calc
      (e.backward q.1 p.1 x * f.backward q.2 p.2 x) *
          (e.forward p.1 q.1 x * f.forward p.2 q.2 x) =
        (e.backward q.1 p.1 x * e.forward p.1 q.1 x) *
          (f.backward q.2 p.2 x * f.forward p.2 q.2 x) := by ring
      _ = 1 := by rw [he, hf]; ring
  right_inverse q p x hx := by
    have he := e.right_inverse q.1 p.1 x ⟨hx.1.1, hx.2.1⟩
    have hf := f.right_inverse q.2 p.2 x ⟨hx.1.2, hx.2.2⟩
    calc
      (e.forward p.1 q.1 x * f.forward p.2 q.2 x) *
          (e.backward q.1 p.1 x * f.backward q.2 p.2 x) =
        (e.forward p.1 q.1 x * e.backward q.1 p.1 x) *
          (f.forward p.2 q.2 x * f.backward q.2 p.2 x) := by ring
      _ = 1 := by rw [he, hf]; ring

/-- Dualizing a genuine holomorphic gauge reverses its local scalars. -/
def GaugeIso.dual {Z : VectorBundleCore ℂ B ℂ ι}
    {W : VectorBundleCore ℂ B ℂ κ}
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]
    (e : GaugeIso (IB := IB) Z W) :
    GaugeIso (IB := IB)
      (HolomorphicLineIntegerPowers.dualCore Z)
      (HolomorphicLineIntegerPowers.dualCore W) where
  forward i a x := e.backward a i x
  backward a i x := e.forward i a x
  forward_holomorphic i a :=
    (e.backward_holomorphic a i).mono (by
      intro x hx
      exact ⟨hx.2, hx.1⟩)
  backward_holomorphic a i :=
    (e.forward_holomorphic i a).mono (by
      intro x hx
      exact ⟨hx.2, hx.1⟩)
  forward_compat i j a b x hx := by
    have h := e.backward_compat b a j i x
      ⟨⟨⟨hx.2, hx.1.2⟩, hx.1.1.2⟩, hx.1.1.1⟩
    simpa [HolomorphicLineIntegerPowers.dualCore,
      transitionScalar, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm] using h.symm
  backward_compat a b i j x hx := by
    have h := e.forward_compat j i b a x
      ⟨⟨⟨hx.2, hx.1.2⟩, hx.1.1.2⟩, hx.1.1.1⟩
    simpa [HolomorphicLineIntegerPowers.dualCore,
      transitionScalar, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm] using h.symm
  left_inverse i a x hx := e.right_inverse a i x ⟨hx.2, hx.1⟩
  right_inverse a i x hx := e.left_inverse i a x ⟨hx.2, hx.1⟩

end
end QuaternionicSymmetry.HolomorphicLineGauge
