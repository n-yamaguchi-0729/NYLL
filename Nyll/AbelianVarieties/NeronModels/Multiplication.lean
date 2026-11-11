/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.NoetherianSpace
public import Nyll.AbelianVarieties.NeronModels.SeparatedGluing
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced
public import Nyll.AbelianVarieties.NeronModels.Density
public import Nyll.AbelianVarieties.NeronModels.QuasiFiniteGluing
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Extending partial multiplication on a smooth model

Fiberwise dense domains extend multiplication and its translations. Associativity then
constructs a relative group law, while graph closure controls enlargements of the domain.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.MultiplicationExtension

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

namespace Extension

section FibreMax

/-- A point maximal for specialization inside its fiber. -/
def FibMax {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  ∀ x' : X, x' ⤳ x → f.base x' = f.base x → x' = x

theorem fibMax_of_maximal {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} (h : ∀ x' : X, x' ⤳ x → x' = x) :
    FibMax f x := fun x' h' _ => h x' h'

theorem maximal_of_generalizingMap {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : GeneralizingMap f.base)
    {x : X}
    (h : ∀ x' : X, x' ⤳ x → x' = x) : ∀ y' : Y, y' ⤳ f.base x → y' = f.base x := by
  intro y' hy'
  obtain ⟨x', hx', rfl⟩ := hf hy'
  rw [h x' hx']

theorem fibMax_comp_of_injective {A B C : Scheme.{u}} (e : A ⟶ B) (β : B ⟶ C)
    (he : Function.Injective e.base)
    {q : A} (h : FibMax β (e.base q)) : FibMax (e ≫ β) q := by
  intro q' hq' hf
  apply he
  refine h _ (hq'.map e.continuous) ?_
  simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] using hf

theorem fibMax_of_isOpenImmersion {A B C : Scheme.{u}} (e : A ⟶ B) [IsOpenImmersion e] (β : B ⟶ C)
    {q : A} (h : FibMax (e ≫ β) q) : FibMax β (e.base q) := by
  intro x' hx' hf
  have hx'r : x' ∈ Set.range e.base := hx'.mem_open e.isOpenEmbedding.isOpen_range ⟨q, rfl⟩
  obtain ⟨q', rfl⟩ := hx'r
  have hq' : q' ⤳ q := (e.isOpenEmbedding.isEmbedding.isInducing.specializes_iff).mp hx'
  rw [h q' hq' (by
    simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] using hf)]

theorem maximal_of_dominated {A B B'' : Scheme.{u}} (G : A ⟶ B) (H : B'' ⟶ A) (π : B'' ⟶ B)
    (hπ : GeneralizingMap π.base) (hGH : H ≫ G = π) {b : B''} {x : A} (hx : H.base b = x)
    (h : ∀ x' : A, x' ⤳ x → x' = x) : ∀ y' : B, y' ⤳ G.base x → y' = G.base x := by
  intro y' hy'
  have hGx : G.base x = π.base b := by rw [← hx, ← Scheme.Hom.comp_apply, hGH]
  rw [hGx] at hy' ⊢
  obtain ⟨b', hb', rfl⟩ := hπ hy'
  have h1 : H.base b' ⤳ x := hx ▸ hb'.map H.continuous
  have h2 : H.base b' = x := h _ h1
  rw [← hGH, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h2, hx]

theorem fibMax_fst_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) {ω : P} (hω : FibMax snd ω) : FibMax f (fst.base ω) := by
  obtain ⟨φ, hφflat, hφι⟩ : ∃ φ : snd.fiber (snd.base ω) ⟶ f.fiber (g.base (snd.base ω)),
      Flat φ ∧ φ ≫ f.fiberι (g.base (snd.base ω)) = snd.fiberι (snd.base ω) ≫ fst := by
    have : Flat (Spec.map (g.residueFieldMap (snd.base ω))) := by
      have : Subsingleton ↥(Spec (Z.residueField (g.base (snd.base ω)))) :=
        inferInstanceAs (Subsingleton (PrimeSpectrum (Z.residueField (g.base (snd.base ω)))))
      infer_instance
    exact ⟨_, MorphismProperty.of_isPullback
        (isPullback_fiberToSpecResidueField_of_isPullback h (snd.base ω)).flip
      inferInstance, pullback.lift_fst _ _ _⟩
  have : Flat φ := hφflat
  have hgen : GeneralizingMap φ.base := Flat.generalizingMap φ
  let ξ : ↥(snd.fiber (snd.base ω)) := snd.asFiber ω
  have hξ : (snd.fiberι (snd.base ω)).base ξ = ω := snd.fiberι_asFiber ω
  have hfstω : (f.fiberι (g.base (snd.base ω))).base (φ.base ξ) = fst.base ω := by
    have := congrArg (fun k => k.base ξ) hφι
    simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply, hξ] using this
  intro x' hx' hfx'
  have hfω : f.base (fst.base ω) = g.base (snd.base ω) := by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  have hx'mem : x' ∈ Set.range (f.fiberι (g.base (snd.base ω))).base := by
    rw [Scheme.Hom.range_fiberι]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, hfω] using hfx'
  obtain ⟨χ, rfl⟩ := hx'mem
  rw [← hfstω] at hx' ⊢
  have hχ : χ ⤳ φ.base ξ :=
    ((f.fiberι (g.base (snd.base ω))).isEmbedding.isInducing.specializes_iff).mp hx'
  obtain ⟨ξ', hξ', hξ'χ⟩ := hgen hχ
  have h1 : (snd.fiberι (snd.base ω)).base ξ' ⤳ ω := by
    have := hξ'.map (snd.fiberι (snd.base ω)).continuous
    rwa [hξ] at this
  have h2 : snd.base ((snd.fiberι (snd.base ω)).base ξ') = snd.base ω := by
    have : (snd.fiberι (snd.base ω)).base ξ' ∈ snd.base ⁻¹' {snd.base ω} := by
      rw [← Scheme.Hom.range_fiberι]; exact ⟨ξ', rfl⟩
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using this
  have h3 : (snd.fiberι (snd.base ω)).base ξ' = (snd.fiberι (snd.base ω)).base ξ :=
      (hω _ h1 h2).trans hξ.symm
  have h4 : ξ' = ξ := (snd.fiberι (snd.base ω)).isEmbedding.injective h3
  rw [← hξ'χ, h4]

theorem exists_fibMax {X Y : Scheme.{u}} (f : X ⟶ Y) (t : Y) (ht : t ∈ Set.range f.base) :
    ∃ ω : X, f.base ω = t ∧ FibMax f ω := by
  have hne : Nonempty ↥(f.fiber t) := by
    obtain ⟨x, hx⟩ := ht
    have : x ∈ Set.range (f.fiberι t).base := by
      rw [Scheme.Hom.range_fiberι]
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx
    obtain ⟨ξ, _⟩ := this
    exact ⟨ξ⟩
  obtain ⟨ξ₀⟩ := hne
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x :=
      ξ₀)) isClosed_irreducibleComponent
  have hξmax : ∀ x' : ↥(f.fiber t), x' ⤳ ξ → x' = ξ := by
    intro x' hx'
    have h1 : irreducibleComponent ξ₀ ⊆ closure {x'} := by
      rw [← hξ.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr
          (specializes_iff_mem_closure.mp hx')) isClosed_closure
    have h2 : closure {x'} = irreducibleComponent ξ₀ :=
      eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible h1
    exact IsGenericPoint.eq (isGenericPoint_def.mpr h2) hξ
  refine ⟨(f.fiberι t).base ξ, ?_, ?_⟩
  · have : (f.fiberι t).base ξ ∈ f.base ⁻¹' {t} := by rw [← Scheme.Hom.range_fiberι]; exact ⟨ξ, rfl⟩
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using this
  · intro ω' hω' hfω'
    have hmem : ω' ∈ Set.range (f.fiberι t).base := by
      rw [Scheme.Hom.range_fiberι]
      have : (f.fiberι t).base ξ ∈ f.base ⁻¹' {t} := by
        rw [← Scheme.Hom.range_fiberι]
        exact ⟨ξ, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at this ⊢
      rw [hfω', this]
    obtain ⟨ξ', rfl⟩ := hmem
    rw [hξmax ξ' (((f.fiberι t).isEmbedding.isInducing.specializes_iff).mp hω')]

open AbelianVarieties.NOSProofs.GluingFibreDensity.TranslationCharts
  (mem_of_dense_of_forall_specializes)

theorem mem_of_dense_fibre_of_fibMax {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (S : X.Opens)
    (x₀ : Y) (hd : Dense ((Subtype.val : {q : X // f.base q = x₀} → X) ⁻¹' (S : Set X)))
    {q : X} (hq : f.base q = x₀) (hmax : FibMax f q) : q ∈ S := by
  let F : Scheme.{u} := f.fiber x₀
  let ι : F ⟶ X := f.fiberι x₀
  have : IsLocallyNoetherian F := by
    change IsLocallyNoetherian (pullback f (Y.fromSpecResidueField x₀)); infer_instance
  have hrange : Set.range ι.base = f.base ⁻¹' {x₀} := Scheme.Hom.range_fiberι f x₀
  obtain ⟨ξ, hξ⟩ : q ∈ Set.range ι.base := by
    rw [hrange]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hq
  have hξmax : ∀ x : F, x ⤳ ξ → x = ξ := by
    intro x hx
    apply ι.isEmbedding.injective
    rw [hξ]
    refine hmax _ (hξ ▸ hx.map ι.continuous) ?_
    have : ι.base x ∈ f.base ⁻¹' {x₀} := hrange ▸ ⟨x, rfl⟩
    rw [hq]; simpa only [Set.mem_preimage, Set.mem_singleton_iff] using this
  have hO : Dense ((ι ⁻¹ᵁ S : F.Opens) : Set F) := by
    rw [ι.isEmbedding.isInducing.dense_iff]
    intro x
    have hx : ι.base x ∈ f.base ⁻¹' {x₀} := hrange ▸ ⟨x, rfl⟩
    have h1 := (IsInducing.subtypeVal.dense_iff).mp hd ⟨ι.base x, by exact hx⟩
    refine closure_mono ?_ h1
    rintro _ ⟨⟨z, hz⟩, hzS, rfl⟩
    obtain ⟨w, rfl⟩ : z ∈ Set.range ι.base := by rw [hrange]; exact hz
    exact ⟨w, hzS, rfl⟩
  obtain ⟨_, ⟨A, hA, rfl⟩, hξA, -⟩ := F.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ξ) isOpen_univ
  have : IsNoetherianRing Γ(F, A) := IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
  have : TopologicalSpace.NoetherianSpace ↥A := noetherianSpace_of_isAffineOpen A hA
  have hOA : Dense ((Scheme.Opens.ι A).base ⁻¹' ((ι ⁻¹ᵁ S : F.Opens) : Set F)) :=
    hO.preimage (Scheme.Opens.ι A).isOpenEmbedding.isOpenMap
  have hξ' : ∀ x : ↥A, x ⤳ (⟨ξ, hξA⟩ : ↥A) → x = ⟨ξ, hξA⟩ := by
    intro x hx
    apply Subtype.ext
    exact hξmax _ (hx.map continuous_subtype_val)
  have : TopologicalSpace.NoetherianSpace ↥((A : F.Opens) : Scheme.{u}) := this
  have key := mem_of_dense_of_forall_specializes
    ((ι ⁻¹ᵁ S).isOpen.preimage (Scheme.Opens.ι A).continuous) hOA ⟨ξ, hξA⟩ hξ'
  change ι.base ((Scheme.Opens.ι A).base ⟨ξ, hξA⟩) ∈ S at key
  rwa [Scheme.Opens.ι_apply, hξ] at key

theorem dense_of_forall_dense_fibre {X Y : Scheme.{u}} (f : X ⟶ Y) (S : Set X)
    (h : ∀ x : Y, Dense ((Subtype.val : {q : X // f.base q = x} → X) ⁻¹' S)) : Dense S :=
  AbelianVarieties.NOSProofs.GraphClosureRigidity.GraphClosure.dense_of_forall_dense_fibre
    f.base S h

theorem dense_of_forall_maximal_mem {X : Scheme.{u}} {S : Set X}
    (h : ∀ x : X, (∀ x' : X, x' ⤳ x → x' = x) → x ∈ S) : Dense S := by
  intro x
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x :=
      x)) isClosed_irreducibleComponent
  have hξx : ξ ⤳ x := hξ.specializes mem_irreducibleComponent
  have hξmax : ∀ x' : X, x' ⤳ ξ → x' = ξ := by
    intro x' hx'
    have h1 : irreducibleComponent x ⊆ closure {x'} := by
      rw [← hξ.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr
          (specializes_iff_mem_closure.mp hx')) isClosed_closure
    have h2 : closure {x'} = irreducibleComponent x :=
      eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible h1
    exact IsGenericPoint.eq (isGenericPoint_def.mpr h2) hξ
  exact hξx.mem_closed isClosed_closure (subset_closure (h ξ hξmax))

theorem maximal_of_injective {A B : Scheme.{u}} (e : A ⟶ B) (he : Function.Injective e.base) {q : A}
    (h : ∀ x' : B, x' ⤳ e.base q → x' = e.base q) (q' : A) (hq' : q' ⤳ q) : q' = q :=
  he (h _ (hq'.map e.continuous))

end FibreMax

section Descent

theorem exists_extension_of_descent {S Z Z' Yt : Scheme.{u}} (s : Z ⟶ S) (yS : Yt ⟶ S)
    [IsSeparated yS]
    [IsReduced Z] (V : Z.Opens) (f : (V : Scheme.{u}) ⟶ Yt) (hf : f ≫ yS = V.ι ≫ s)
    (p : Z' ⟶ Z) [Flat p] [LocallyOfFinitePresentation p] [Surjective p] [IsReduced (pullback p p)]
    (f' : Z' ⟶ Yt) (hf' : f' ≫ yS = p ≫ s)
    (Ω : Z'.Opens) (hΩ : Dense (Ω : Set Z')) (hΩV : Ω ≤ p ⁻¹ᵁ V)
    (hagree : Ω.ι ≫ f' = p.resLE V Ω hΩV ≫ f) :
    ∃ F : Z ⟶ Yt, p ≫ F = f' ∧ V.ι ≫ F = f ∧ F ≫ yS = s := by
  have key : pullback.fst p p ≫ f' = pullback.snd p p ≫ f' := by
    let Ω₂ : (pullback p p).Opens := pullback.fst p p ⁻¹ᵁ Ω ⊓ pullback.snd p p ⁻¹ᵁ Ω
    have : IsDominant Ω₂.ι := by
      refine ⟨?_⟩
      rw [DenseRange, Scheme.Opens.range_ι]
      simp only [Ω₂, TopologicalSpace.Opens.coe_inf]
      exact (hΩ.preimage (pullback.fst p p).isOpenMap).inter_of_isOpen_left
        (hΩ.preimage (pullback.snd p p).isOpenMap) (pullback.fst p p ⁻¹ᵁ Ω).isOpen
    refine ext_of_isDominant_of_isSeparated yS ?_ Ω₂.ι ?_
    · rw [Category.assoc, hf', Category.assoc, hf', pullback.condition_assoc]
    · let r₁ : (Ω₂ : Scheme.{u}) ⟶ Ω := (pullback.fst p p).resLE Ω Ω₂ inf_le_left
      let r₂ : (Ω₂ : Scheme.{u}) ⟶ Ω := (pullback.snd p p).resLE Ω Ω₂ inf_le_right
      have e₁ : r₁ ≫ Ω.ι = Ω₂.ι ≫ pullback.fst p p := Scheme.Hom.resLE_comp_ι _ _
      have e₂ : r₂ ≫ Ω.ι = Ω₂.ι ≫ pullback.snd p p := Scheme.Hom.resLE_comp_ι _ _
      have e₃ : r₁ ≫ p.resLE V Ω hΩV = r₂ ≫ p.resLE V Ω hΩV := by
        rw [← cancel_mono V.ι, Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι,
            reassoc_of% e₁,
          reassoc_of% e₂, pullback.condition]
      rw [← reassoc_of% e₁, ← reassoc_of% e₂, hagree, reassoc_of% e₃]
  have hdesc : ∀ {T : Scheme.{u}} (g₁ g₂ : T ⟶ Z'), g₁ ≫ p = g₂ ≫ p → g₁ ≫ f' = g₂ ≫ f' := by
    intro T g₁ g₂ h
    rw [← pullback.lift_fst g₁ g₂ h, Category.assoc, key, pullback.lift_snd_assoc]
  let F : Z ⟶ Yt := EffectiveEpi.desc p f' hdesc
  have hF : p ≫ F = f' := EffectiveEpi.fac p f' hdesc
  have hFs : F ≫ yS = s := by
    have : Epi p := inferInstance
    rw [← cancel_epi p, reassoc_of% hF, hf']
  refine ⟨F, hF, ?_, hFs⟩
  let ρ : (Ω : Scheme.{u}) ⟶ V := p.resLE V Ω hΩV
  have hρ : ρ ≫ V.ι = Ω.ι ≫ p := Scheme.Hom.resLE_comp_ι _ _
  have : IsDominant ρ := by
    refine ⟨?_⟩
    have hd : Dense (V.ι.base ⁻¹' (p.base '' (Ω : Set Z'))) :=
      (p.surjective.denseRange.dense_image p.continuous hΩ).preimage V.ι.isOpenMap
    rw [DenseRange]
    refine hd.mono ?_
    rintro v ⟨z, hz, hv⟩
    let zΩ : (Ω : Scheme.{u}) := ⟨z, hz⟩
    refine ⟨zΩ, V.ι.isOpenEmbedding.injective ?_⟩
    change (ρ ≫ V.ι) zΩ = V.ι v
    rw [hρ]
    exact hv
  refine ext_of_isDominant_of_isSeparated yS ?_ ρ ?_
  · rw [Category.assoc, hFs, hf]
  · rw [reassoc_of% hρ, hF, hagree]

end Descent

/-- A partial multiplication with open left and right translations. -/
structure Chunk (R : Type u) [CommRing R] where
  /-- The underlying smooth model. -/
  Y : Scheme.{u}
  /-- The product scheme. -/
  P : Scheme.{u}
  /-- The structure morphism. -/
  y : Y ⟶ Spec (CommRingCat.of R)
  /-- The first projection. -/
  π₁ : P ⟶ Y
  /-- The second projection. -/
  π₂ : P ⟶ Y
  /-- The product square. -/
  hP : IsPullback π₁ π₂ y y
  /-- The domain of the partial multiplication. -/
  U : P.Opens
  /-- The partial multiplication morphism. -/
  m : (U : Scheme.{u}) ⟶ Y
  /-- Multiplication is over the base. -/
  hm : m ≫ y = U.ι ≫ π₁ ≫ y
  /-- The left translation graph. -/
  Φ : (U : Scheme.{u}) ⟶ P
  /-- The right translation graph. -/
  Ψ : (U : Scheme.{u}) ⟶ P
  /-- The left graph preserves the first coordinate. -/
  Φ_fst : Φ ≫ π₁ = U.ι ≫ π₁
  /-- The left graph has multiplication as second coordinate. -/
  Φ_snd : Φ ≫ π₂ = m
  /-- The right graph has multiplication as first coordinate. -/
  Ψ_fst : Ψ ≫ π₁ = m
  /-- The right graph preserves the second coordinate. -/
  Ψ_snd : Ψ ≫ π₂ = U.ι ≫ π₂
  /-- The left translation graph is open. -/
  Φ_open : IsOpenImmersion Φ
  /-- The right translation graph is open. -/
  Ψ_open : IsOpenImmersion Ψ
  /-- The model is smooth over the base. -/
  y_smooth : Smooth y
  /-- The model is separated over the base. -/
  y_sep : IsSeparated y
  /-- The first projection is smooth. -/
  π₁_smooth : Smooth π₁
  /-- The second projection is smooth. -/
  π₂_smooth : Smooth π₂
  /-- The first projection is surjective. -/
  π₁_surj : Surjective π₁
  /-- The second projection is surjective. -/
  π₂_surj : Surjective π₂

attribute [local instance] Chunk.Φ_open Chunk.Ψ_open Chunk.y_smooth Chunk.y_sep
  Chunk.π₁_smooth Chunk.π₂_smooth Chunk.π₁_surj Chunk.π₂_surj

namespace Chunk

variable {R : Type u} [CommRing R] (D : Chunk R)

/-- Exchange the two factors and the left and right translations. -/
def flip : Chunk R where
  Y := D.Y
  P := D.P
  y := D.y
  π₁ := D.π₂
  π₂ := D.π₁
  hP := D.hP.flip
  U := D.U
  m := D.m
  hm := by rw [D.hm, D.hP.w]
  Φ := D.Ψ
  Ψ := D.Φ
  Φ_fst := D.Ψ_snd
  Φ_snd := D.Ψ_fst
  Ψ_fst := D.Φ_snd
  Ψ_snd := D.Φ_fst
  Φ_open := D.Ψ_open
  Ψ_open := D.Φ_open
  y_smooth := D.y_smooth
  y_sep := D.y_sep
  π₁_smooth := D.π₂_smooth
  π₂_smooth := D.π₁_smooth
  π₁_surj := D.π₂_surj
  π₂_surj := D.π₁_surj

/-- Associativity on every test scheme wherever both products are defined. -/
def Assoc : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (u v p q : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y)),
    u.1 ≫ D.U.ι ≫ D.π₂ = v.1 ≫ D.U.ι ≫ D.π₁ →
    p.1 ≫ D.U.ι ≫ D.π₁ = u.1 ≫ D.m → p.1 ≫ D.U.ι ≫ D.π₂ = v.1 ≫ D.U.ι ≫ D.π₂ →
    q.1 ≫ D.U.ι ≫ D.π₁ = u.1 ≫ D.U.ι ≫ D.π₁ → q.1 ≫ D.U.ι ≫ D.π₂ = v.1 ≫ D.m →
    p.1 ≫ D.m = q.1 ≫ D.m

/-- Density on every fiber of the given projection. -/
def FibDense (π : D.P ⟶ D.Y) (S : Set D.P) : Prop :=
  ∀ x : D.Y, Dense ((Subtype.val : {q : D.P // π.base q = x} → D.P) ⁻¹' S)

/-- The open subset contains all fiberwise maximal points. -/
def MaxMem (Y₀ : D.Y.Opens) : Prop :=
  ∀ p : D.Y, (∀ p' : D.Y, p' ⤳ p → D.y.base p' = D.y.base p → p' = p) → p ∈ Y₀

/-- Pairs from the chosen open subset lie in the multiplication domain. -/
def SqSub (Y₀ : D.Y.Opens) : Prop :=
  ∀ q : D.P, D.π₁.base q ∈ Y₀ → D.π₂.base q ∈ Y₀ → q ∈ D.U

theorem assoc_flip (h : D.Assoc) : D.flip.Assoc := by
  intro T t u v p q h1 h2 h3 h4 h5
  change _ ≫ D.m = _ ≫ D.m
  have e : D.U.ι ≫ D.π₁ ≫ D.y = D.U.ι ≫ D.π₂ ≫ D.y := by rw [D.hP.w]
  let c : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₂ ≫ D.y) →
      NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    fun w => ⟨w.1, by rw [e]; exact w.2⟩
  exact (h t (c v) (c u) (c q) (c p) h1.symm h5 h4 h3 h2).symm

theorem sqSub_flip {Y₀ : D.Y.Opens} (h : D.SqSub Y₀) : D.flip.SqSub Y₀ := fun q h₁ h₂ => h q h₂ h₁

theorem isReduced_P [IsDomain R] [IsDiscreteValuationRing R] : IsReduced D.P :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (D.π₁ ≫ D.y)

/-- The scheme of composable pairs. -/
abbrev Y3 : Scheme.{u} := pullback D.π₂ D.π₁

/-- Projection to the first composable pair. -/
abbrev P12 : D.Y3 ⟶ D.P := pullback.fst D.π₂ D.π₁

/-- Projection to the second composable pair. -/
abbrev P23 : D.Y3 ⟶ D.P := pullback.snd D.π₂ D.π₁

/-- Projection to the two outer factors. -/
def outer : D.Y3 ⟶ D.P :=
  D.hP.lift (D.P12 ≫ D.π₁) (D.P23 ≫ D.π₂)
    (by rw [Category.assoc, Category.assoc, D.hP.w, pullback.condition_assoc, D.hP.w])

@[reassoc (attr := simp)]
theorem outer_fst : D.outer ≫ D.π₁ = D.P12 ≫ D.π₁ := D.hP.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem outer_snd : D.outer ≫ D.π₂ = D.P23 ≫ D.π₂ := D.hP.lift_snd _ _ _

theorem isPullback_P12_outer : IsPullback D.P12 D.outer D.π₁ D.π₁ := by
  have s : IsPullback (D.P23 ≫ D.π₂) D.P12 D.y (D.π₁ ≫ D.y) := by
    have := (IsPullback.of_hasPullback D.π₂ D.π₁).flip.paste_horiz D.hP.flip
    rwa [← D.hP.w] at this
  have h : IsPullback D.outer D.P12 D.π₁ D.π₁ :=
    IsPullback.of_right (h₁₂ := D.π₂) (v₁₃ := D.y) (h₂₂ :=
        D.y) (by rwa [outer_snd]) D.outer_fst D.hP.flip
  exact h.flip

theorem isPullback_P23_outer : IsPullback D.P23 D.outer D.π₂ D.π₂ := by
  have s : IsPullback (D.P12 ≫ D.π₁) D.P23 D.y (D.π₂ ≫ D.y) := by
    have := (IsPullback.of_hasPullback D.π₂ D.π₁).paste_horiz D.hP
    rwa [D.hP.w] at this
  have h : IsPullback D.outer D.P23 D.π₂ D.π₂ :=
    IsPullback.of_right (h₁₂ := D.π₁) (v₁₃ := D.y) (h₂₂ :=
        D.y) (by rwa [outer_fst]) D.outer_snd D.hP
  exact h.flip

scoped instance smooth_outer : Smooth D.outer :=
    MorphismProperty.of_isPullback D.isPullback_P12_outer inferInstance

scoped instance surjective_outer : Surjective D.outer :=
  MorphismProperty.of_isPullback D.isPullback_P12_outer inferInstance

/-- The open image of left translation. -/
abbrev V : D.P.Opens := D.Φ.opensRange

theorem coe_V : (D.V : Set D.P) = Set.range D.Φ.base := Scheme.Hom.coe_opensRange D.Φ

/-- The inverse of left translation onto its open image. -/
abbrev linv : (D.V : Scheme.{u}) ⟶ D.U := D.Φ.isoOpensRange.inv

@[reassoc]
theorem linv_Φ : D.linv ≫ D.Φ = D.V.ι := D.Φ.isoOpensRange_inv_comp

@[reassoc]
theorem linv_fst : D.linv ≫ D.U.ι ≫ D.π₁ = D.V.ι ≫ D.π₁ := by rw [← D.Φ_fst, linv_Φ_assoc]

@[reassoc]
theorem linv_m : D.linv ≫ D.m = D.V.ι ≫ D.π₂ := by rw [← D.Φ_snd, linv_Φ_assoc]

/-- Left division on the translation image. -/
def divl : (D.V : Scheme.{u}) ⟶ D.Y := D.linv ≫ D.U.ι ≫ D.π₂

/-- The correspondence used to descend multiplication. -/
abbrev ZM : Scheme.{u} := pullback (D.U.ι ≫ D.π₂) (D.V.ι ≫ D.π₁)

/-- The multiplication correspondence as an open part of the triple product. -/
def jM : D.ZM ⟶ D.Y3 :=
  pullback.map (D.U.ι ≫ D.π₂) (D.V.ι ≫ D.π₁) D.π₂ D.π₁ D.U.ι D.V.ι (𝟙 D.Y)
    ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)

scoped instance : IsOpenImmersion D.jM :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl rfl

@[reassoc (attr := simp)]
theorem jM_P12 : D.jM ≫ D.P12 = pullback.fst _ _ ≫ D.U.ι := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem jM_P23 : D.jM ≫ D.P23 = pullback.snd _ _ ≫ D.V.ι := pullback.lift_snd _ _ _

/-- The pair to be multiplied in the descent correspondence. -/
def FM : D.ZM ⟶ D.P :=
  D.hP.lift (pullback.fst _ _ ≫ D.m) (pullback.snd _ _ ≫ D.divl)
    (by
      rw [Category.assoc, D.hm, Category.assoc, D.hP.w,
        reassoc_of% (pullback.condition (f := D.U.ι ≫ D.π₂) (g :=
            D.V.ι ≫ D.π₁)), divl, Category.assoc,
        Category.assoc, ← D.hP.w, D.linv_fst_assoc])

@[reassoc (attr := simp)]
theorem FM_fst : D.FM ≫ D.π₁ = pullback.fst _ _ ≫ D.m := D.hP.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem FM_snd : D.FM ≫ D.π₂ = pullback.snd _ _ ≫ D.divl := D.hP.lift_snd _ _ _

/-- The open part where the auxiliary product is defined. -/
def ΩM : D.ZM.Opens := D.FM ⁻¹ᵁ D.U

/-- The smooth projection used for multiplication descent. -/
def pM : (D.ΩM : Scheme.{u}) ⟶ D.P := D.ΩM.ι ≫ D.jM ≫ D.outer

/-- The auxiliary product restricted to its domain. -/
def ppM : (D.ΩM : Scheme.{u}) ⟶ D.U := D.FM.resLE D.U _ le_rfl

@[reassoc]
theorem ppM_ι : D.ppM ≫ D.U.ι = D.ΩM.ι ≫ D.FM := Scheme.Hom.resLE_comp_ι _ _

/-- Multiplication on the auxiliary descent cover. -/
def fM : (D.ΩM : Scheme.{u}) ⟶ D.Y := D.ppM ≫ D.m

@[reassoc]
theorem pM_fst : D.pM ≫ D.π₁ = D.ΩM.ι ≫ pullback.fst _ _ ≫ D.U.ι ≫ D.π₁ := by
  rw [pM, Category.assoc, Category.assoc, outer_fst, jM_P12_assoc]

@[reassoc]
theorem pM_snd : D.pM ≫ D.π₂ = D.ΩM.ι ≫ pullback.snd _ _ ≫ D.V.ι ≫ D.π₂ := by
  rw [pM, Category.assoc, Category.assoc, outer_snd, jM_P23_assoc]

scoped instance smooth_pM : Smooth D.pM := by rw [pM]; infer_instance

theorem surjective_pM (hU₁ : D.FibDense D.π₁ D.U) (hV₂ : D.FibDense D.π₂ (Set.range D.Φ.base))
    (Y₀ : D.Y.Opens) (hY₀ : D.MaxMem Y₀) (hY₀U : D.SqSub Y₀) : Surjective D.pM := by
  refine ⟨fun t => ?_⟩
  obtain ⟨ω, hωt, hω⟩ := exists_fibMax D.outer t (D.outer.surjective.range_eq ▸ trivial)
  have h12 : FibMax D.π₁ (D.P12.base ω) := fibMax_fst_of_isPullback D.isPullback_P12_outer hω
  have h23 : FibMax D.π₂ (D.P23.base ω) := fibMax_fst_of_isPullback D.isPullback_P23_outer hω
  have hU : D.P12.base ω ∈ D.U := mem_of_dense_fibre_of_fibMax D.π₁ D.U _ (hU₁ _) rfl h12
  have hV : D.P23.base ω ∈ D.V :=
    mem_of_dense_fibre_of_fibMax D.π₂ D.V _ (by rw [coe_V]; exact hV₂ _) rfl h23
  obtain ⟨ζ, hζ⟩ : ω ∈ Set.range D.jM.base := by
    rw [jM, Scheme.Pullback.range_map]
    exact ⟨by rw [Scheme.Opens.range_ι]; exact hU, by rw [Scheme.Opens.range_ι]; exact hV⟩
  have hsq := D.hP.flip
  have hu : D.U.ι.base (pullback.fst (D.U.ι ≫ D.π₂) (D.V.ι ≫ D.π₁) ζ) = D.P12.base ω := by
    rw [← Scheme.Hom.comp_apply, ← jM_P12, Scheme.Hom.comp_apply, hζ]
  have hv : D.V.ι.base (pullback.snd (D.U.ι ≫ D.π₂) (D.V.ι ≫ D.π₁) ζ) = D.P23.base ω := by
    rw [← Scheme.Hom.comp_apply, ← jM_P23, Scheme.Hom.comp_apply, hζ]
  have h1 : D.π₁.base (D.FM.base ζ) ∈ Y₀ := by
    rw [← Scheme.Hom.comp_apply, FM_fst, Scheme.Hom.comp_apply]
    apply hY₀
    have k1 : FibMax (D.U.ι ≫ D.π₁) (pullback.fst (D.U.ι ≫ D.π₂) (D.V.ι ≫ D.π₁) ζ) :=
      fibMax_comp_of_injective D.U.ι D.π₁ D.U.ι.isOpenEmbedding.injective (hu ▸ h12)
    rw [← D.Φ_fst] at k1
    have k2 := fibMax_of_isOpenImmersion D.Φ D.π₁ k1
    have k3 := fibMax_fst_of_isPullback hsq k2
    rwa [← Scheme.Hom.comp_apply, D.Φ_snd] at k3
  have h2 : D.π₂.base (D.FM.base ζ) ∈ Y₀ := by
    rw [← Scheme.Hom.comp_apply, FM_snd, Scheme.Hom.comp_apply, divl, Scheme.Hom.comp_apply]
    apply hY₀
    have k0 : FibMax D.π₂ (D.Φ.base (D.linv.base (pullback.snd (D.U.ι ≫ D.π₂) (D.V.ι ≫
        D.π₁) ζ))) := by
      rw [← Scheme.Hom.comp_apply, linv_Φ, hv]; exact h23
    have k1 := fibMax_comp_of_injective D.Φ D.π₂ D.Φ.isOpenEmbedding.injective k0
    rw [D.Φ_snd, ← D.Ψ_fst] at k1
    have k2 := fibMax_of_isOpenImmersion D.Ψ D.π₁ k1
    have k3 := fibMax_fst_of_isPullback hsq k2
    rwa [← Scheme.Hom.comp_apply, D.Ψ_snd] at k3
  have hζΩ : ζ ∈ D.ΩM := hY₀U _ h1 h2
  refine ⟨(⟨ζ, hζΩ⟩ : (D.ΩM : Scheme.{u})), ?_⟩
  change D.outer (D.jM ζ) = t
  rw [hζ, hωt]

theorem fM_agree (hassoc : D.Assoc) :
    (D.pM ⁻¹ᵁ D.U).ι ≫ D.fM = D.pM.resLE D.U _ le_rfl ≫ D.m := by
  set Ω' := D.pM ⁻¹ᵁ D.U
  let t : (Ω' : Scheme.{u}) ⟶ Spec (CommRingCat.of R) :=
      Ω'.ι ≫ D.ΩM.ι ≫ pullback.fst _ _ ≫ D.U.ι ≫ D.π₁ ≫ D.y
  have hcond : Ω'.ι ≫ D.ΩM.ι ≫ pullback.fst _ _ ≫ D.U.ι ≫ D.π₂ =
      Ω'.ι ≫ D.ΩM.ι ≫ pullback.snd _ _ ≫ D.V.ι ≫ D.π₁ := by
    rw [pullback.condition]
  let uu : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨Ω'.ι ≫ D.ΩM.ι ≫ pullback.fst _ _, by simp only [t, Category.assoc]⟩
  let vv : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨Ω'.ι ≫ D.ΩM.ι ≫ pullback.snd _ _ ≫ D.linv, by
      simp only [t, Category.assoc]
      rw [D.linv_fst_assoc]
      conv_rhs => rw [D.hP.w]
      rw [reassoc_of% hcond]⟩
  let pp : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨Ω'.ι ≫ D.ppM, by
      simp only [t, Category.assoc]
      rw [D.ppM_ι_assoc, FM_fst_assoc, D.hm]⟩
  let qq : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨D.pM.resLE D.U _ le_rfl, by
      simp only [t]
      rw [Scheme.Hom.resLE_comp_ι_assoc, pM_fst_assoc]⟩
  have key := hassoc t uu vv pp qq
    (by simp only [uu, vv, Category.assoc]; rw [D.linv_fst, hcond])
    (by simp only [pp, uu, Category.assoc]; rw [D.ppM_ι_assoc, FM_fst])
    (by simp only [pp, vv, Category.assoc]; rw [D.ppM_ι_assoc, FM_snd, divl])
    (by simp only [qq, uu, Category.assoc]; rw [Scheme.Hom.resLE_comp_ι_assoc, pM_fst])
    (by simp only [qq, vv, Category.assoc]; rw [Scheme.Hom.resLE_comp_ι_assoc, pM_snd, D.linv_m])
  simpa only [pp, qq, fM, Category.assoc] using key

theorem exists_M [IsDomain R] [IsDiscreteValuationRing R] (hassoc : D.Assoc)
    (hU₁ : D.FibDense D.π₁ D.U)
    (hV₂ : D.FibDense D.π₂ (Set.range D.Φ.base)) (Y₀ : D.Y.Opens) (hY₀ : D.MaxMem Y₀)
        (hY₀U : D.SqSub Y₀) :
    ∃ M : D.P ⟶ D.Y, D.U.ι ≫ M = D.m ∧ M ≫ D.y = D.π₁ ≫ D.y := by
  have : IsReduced D.P := D.isReduced_P
  have : Surjective D.pM := D.surjective_pM hU₁ hV₂ Y₀ hY₀ hY₀U
  have : IsReduced (pullback D.pM D.pM) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (pullback.fst D.pM D.pM ≫ D.ΩM.ι ≫ pullback.fst _ _ ≫ D.U.ι ≫ D.π₁ ≫ D.y)
  have hUd : Dense (D.U : Set D.P) := dense_of_forall_dense_fibre D.π₁ _ hU₁
  have hf' : D.fM ≫ D.y = D.pM ≫ D.π₁ ≫ D.y := by
    rw [fM, Category.assoc, D.hm, D.ppM_ι_assoc, FM_fst_assoc, D.hm, pM_fst_assoc]
  obtain ⟨M, -, hMm, hMy⟩ := exists_extension_of_descent (D.π₁ ≫ D.y) D.y D.U D.m D.hm D.pM D.fM hf'
    (D.pM ⁻¹ᵁ D.U) (hUd.preimage D.pM.isOpenMap) le_rfl (D.fM_agree hassoc)
  exact ⟨M, hMm, hMy⟩

section Division

variable (M : D.P ⟶ D.Y) (hMm : D.U.ι ≫ M = D.m) (hMy : M ≫ D.y = D.π₁ ≫ D.y)

/-- The correspondence used to descend division. -/
abbrev ZD : Scheme.{u} := pullback D.m (D.U.ι ≫ D.π₁)

/-- The division correspondence as an open part of the triple product. -/
def jD : D.ZD ⟶ D.Y3 :=
  pullback.map D.m (D.U.ι ≫ D.π₁) D.π₂ D.π₁ D.Φ D.Φ (𝟙 D.Y)
    ((Category.comp_id _).trans D.Φ_snd.symm) ((Category.comp_id _).trans D.Φ_fst.symm)

scoped instance : IsOpenImmersion D.jD :=
  MorphismProperty.pullbackMap (P :=
      @IsOpenImmersion) inferInstance inferInstance D.Φ_snd.symm D.Φ_fst.symm

@[reassoc (attr := simp)]
theorem jD_P12 : D.jD ≫ D.P12 = pullback.fst _ _ ≫ D.Φ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem jD_P23 : D.jD ≫ D.P23 = pullback.snd _ _ ≫ D.Φ := pullback.lift_snd _ _ _

/-- The pair to be multiplied in the division correspondence. -/
def FD : D.ZD ⟶ D.P :=
  D.hP.lift (pullback.fst _ _ ≫ D.U.ι ≫ D.π₂) (pullback.snd _ _ ≫ D.U.ι ≫ D.π₂)
    (by
      simp only [Category.assoc]
      conv_lhs => rw [← D.hP.w, ← D.hm]
      rw [pullback.condition_assoc, Category.assoc, D.hP.w])

@[reassoc (attr := simp)]
theorem FD_fst : D.FD ≫ D.π₁ = pullback.fst _ _ ≫ D.U.ι ≫ D.π₂ := D.hP.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem FD_snd : D.FD ≫ D.π₂ = pullback.snd _ _ ≫ D.U.ι ≫ D.π₂ := D.hP.lift_snd _ _ _

/-- The open part where the division correspondence is defined. -/
def ΩD : D.ZD.Opens := D.FD ⁻¹ᵁ D.U

/-- The smooth projection used for division descent. -/
def pD : (D.ΩD : Scheme.{u}) ⟶ D.P := D.ΩD.ι ≫ D.jD ≫ D.outer

/-- The auxiliary division pair restricted to the multiplication domain. -/
def ppD : (D.ΩD : Scheme.{u}) ⟶ D.U := D.FD.resLE D.U _ le_rfl

@[reassoc]
theorem ppD_ι : D.ppD ≫ D.U.ι = D.ΩD.ι ≫ D.FD := Scheme.Hom.resLE_comp_ι _ _

/-- The division map on the auxiliary descent cover. -/
def fD : (D.ΩD : Scheme.{u}) ⟶ D.Y := D.ppD ≫ D.m

@[reassoc]
theorem pD_fst : D.pD ≫ D.π₁ = D.ΩD.ι ≫ pullback.fst _ _ ≫ D.U.ι ≫ D.π₁ := by
  rw [pD, Category.assoc, Category.assoc, outer_fst, jD_P12_assoc, D.Φ_fst]

@[reassoc]
theorem pD_snd : D.pD ≫ D.π₂ = D.ΩD.ι ≫ pullback.snd _ _ ≫ D.m := by
  rw [pD, Category.assoc, Category.assoc, outer_snd, jD_P23_assoc, D.Φ_snd]

scoped instance smooth_pD : Smooth D.pD := by rw [pD]; infer_instance

theorem fD_y : D.fD ≫ D.y = D.pD ≫ D.π₁ ≫ D.y := by
  rw [fD, Category.assoc, D.hm, D.ppD_ι_assoc, FD_fst_assoc, ← D.hP.w, pD_fst_assoc]

/-- The pair formed from the base point and the auxiliary quotient. -/
def GD : (D.ΩD : Scheme.{u}) ⟶ D.P :=
  D.hP.lift (D.pD ≫ D.π₁) D.fD (by rw [Category.assoc, fD_y])

@[reassoc (attr := simp)]
theorem GD_fst : D.GD ≫ D.π₁ = D.pD ≫ D.π₁ := D.hP.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem GD_snd : D.GD ≫ D.π₂ = D.fD := D.hP.lift_snd _ _ _

/-- The open locus where division agrees with the original partial law. -/
def ΩD' : (D.ΩD : Scheme.{u}).Opens := D.pD ⁻¹ᵁ D.V ⊓ D.GD ⁻¹ᵁ D.U

theorem ΩD'_le_left : D.ΩD' ≤ D.pD ⁻¹ᵁ D.V := inf_le_left

theorem ΩD'_le_right : D.ΩD' ≤ D.GD ⁻¹ᵁ D.U := inf_le_right

theorem surjective_pD (hV₁ : D.FibDense D.π₁ (Set.range D.Φ.base))
    (hV₂ : D.FibDense D.π₂ (Set.range D.Φ.base))
    (Y₀ : D.Y.Opens) (hY₀ : D.MaxMem Y₀) (hY₀U : D.SqSub Y₀) : Surjective D.pD := by
  refine ⟨fun t => ?_⟩
  obtain ⟨ω, hωt, hω⟩ := exists_fibMax D.outer t (D.outer.surjective.range_eq ▸ trivial)
  have h12 : FibMax D.π₁ (D.P12.base ω) := fibMax_fst_of_isPullback D.isPullback_P12_outer hω
  have h23 : FibMax D.π₂ (D.P23.base ω) := fibMax_fst_of_isPullback D.isPullback_P23_outer hω
  have hV12 : D.P12.base ω ∈ Set.range D.Φ.base :=
    mem_of_dense_fibre_of_fibMax D.π₁ D.V _ (by rw [coe_V]; exact hV₁ _) rfl h12
  have hV23 : D.P23.base ω ∈ Set.range D.Φ.base :=
    mem_of_dense_fibre_of_fibMax D.π₂ D.V _ (by rw [coe_V]; exact hV₂ _) rfl h23
  obtain ⟨ζ, hζ⟩ : ω ∈ Set.range D.jD.base := by
    rw [jD, Scheme.Pullback.range_map]; exact ⟨hV12, hV23⟩
  have hsq := D.hP.flip
  have hu : D.Φ.base (pullback.fst D.m (D.U.ι ≫ D.π₁) ζ) = D.P12.base ω := by
    rw [← Scheme.Hom.comp_apply, ← jD_P12, Scheme.Hom.comp_apply, hζ]
  have hv : D.Φ.base (pullback.snd D.m (D.U.ι ≫ D.π₁) ζ) = D.P23.base ω := by
    rw [← Scheme.Hom.comp_apply, ← jD_P23, Scheme.Hom.comp_apply, hζ]
  have h1 : D.π₁.base (D.FD.base ζ) ∈ Y₀ := by
    rw [← Scheme.Hom.comp_apply, FD_fst, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    apply hY₀
    have k1 := fibMax_comp_of_injective D.Φ D.π₁ D.Φ.isOpenEmbedding.injective (hu ▸ h12)
    rw [D.Φ_fst] at k1
    exact fibMax_fst_of_isPullback hsq (fibMax_of_isOpenImmersion D.U.ι D.π₁ k1)
  have h2 : D.π₂.base (D.FD.base ζ) ∈ Y₀ := by
    rw [← Scheme.Hom.comp_apply, FD_snd, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    apply hY₀
    have k1 := fibMax_comp_of_injective D.Φ D.π₂ D.Φ.isOpenEmbedding.injective (hv ▸ h23)
    rw [D.Φ_snd] at k1
    have k1' : FibMax (D.Ψ ≫ D.π₁) (pullback.snd D.m (D.U.ι ≫ D.π₁) ζ) := by rw [D.Ψ_fst]; exact k1
    have k3 := fibMax_fst_of_isPullback hsq (fibMax_of_isOpenImmersion D.Ψ D.π₁ k1')
    rwa [← Scheme.Hom.comp_apply, D.Ψ_snd, Scheme.Hom.comp_apply] at k3
  have hζΩ : ζ ∈ D.ΩD := hY₀U _ h1 h2
  refine ⟨(⟨ζ, hζΩ⟩ : (D.ΩD : Scheme.{u})), ?_⟩
  change D.outer (D.jD ζ) = t
  rw [hζ, hωt]

theorem fD_agree (hassoc : D.Assoc) :
    D.ΩD'.ι ≫ D.fD = D.pD.resLE D.V D.ΩD' D.ΩD'_le_left ≫ D.divl := by
  set Ω' := D.ΩD'
  have hleft : Ω' ≤ D.pD ⁻¹ᵁ D.V := D.ΩD'_le_left
  have hright : Ω' ≤ D.GD ⁻¹ᵁ D.U := D.ΩD'_le_right
  change Ω'.ι ≫ D.fD = D.pD.resLE D.V Ω' hleft ≫ D.divl
  let t : (Ω' : Scheme.{u}) ⟶ Spec (CommRingCat.of R) :=
      Ω'.ι ≫ D.ΩD.ι ≫ pullback.fst _ _ ≫ D.U.ι ≫ D.π₁ ≫ D.y
  have hcond : Ω'.ι ≫ D.ΩD.ι ≫ pullback.fst _ _ ≫ D.m = Ω'.ι ≫ D.ΩD.ι ≫ pullback.snd _ _ ≫
      D.U.ι ≫ D.π₁ := by
    rw [pullback.condition]
  let uu : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨Ω'.ι ≫ D.ΩD.ι ≫ pullback.fst _ _, by simp only [t, Category.assoc]⟩
  let vv : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨Ω'.ι ≫ D.ppD, by
      simp only [t, Category.assoc]
      rw [D.ppD_ι_assoc, FD_fst_assoc, ← D.hP.w]⟩
  let pp : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨Ω'.ι ≫ D.ΩD.ι ≫ pullback.snd _ _, by
      simp only [t, Category.assoc]
      rw [← reassoc_of% hcond, D.hm]⟩
  let qq : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨D.GD.resLE D.U Ω' hright, by
      simp only [t]
      rw [Scheme.Hom.resLE_comp_ι_assoc, GD_fst_assoc, pD_fst_assoc]⟩
  have key := hassoc t uu vv pp qq
    (by simp only [uu, vv, Category.assoc]; rw [D.ppD_ι_assoc, FD_fst])
    (by simp only [pp, uu, Category.assoc]; rw [hcond])
    (by simp only [pp, vv, Category.assoc]; rw [D.ppD_ι_assoc, FD_snd])
    (by simp only [qq, uu, Category.assoc]; rw [Scheme.Hom.resLE_comp_ι_assoc, GD_fst, pD_fst])
    (by simp only [qq, vv, Category.assoc]; rw [Scheme.Hom.resLE_comp_ι_assoc, GD_snd, fD])
  have hqΦ : qq.1 ≫ D.Φ = Ω'.ι ≫ D.pD := by
    refine D.hP.hom_ext ?_ ?_
    · dsimp only [qq]
      rw [Category.assoc, D.Φ_fst, Scheme.Hom.resLE_comp_ι_assoc, GD_fst, Category.assoc]
    · rw [Category.assoc, D.Φ_snd, ← key]
      simp only [pp, Category.assoc]
      rw [pD_snd]
  have hρ : D.pD.resLE D.V Ω' hleft ≫ D.linv = qq.1 := by
    rw [← cancel_mono D.Φ, Category.assoc, D.linv_Φ, Scheme.Hom.resLE_comp_ι, hqΦ]
  rw [divl, reassoc_of% hρ]
  simp only [qq]
  rw [Scheme.Hom.resLE_comp_ι_assoc, GD_snd]

/-- The base-changed multiplication correspondence. -/
abbrev BD : Scheme.{u} := pullback (D.U.ι ≫ D.π₂) D.π₁

/-- The multiplication map on the base-changed correspondence. -/
def KD : D.BD ⟶ D.P :=
  D.hP.lift (pullback.fst _ _ ≫ D.m) (pullback.snd _ _ ≫ D.π₂)
    (by
      rw [Category.assoc, D.hm, Category.assoc, D.hP.w,
        reassoc_of% (pullback.condition (f := D.U.ι ≫ D.π₂) (g := D.π₁)), D.hP.w])

@[reassoc (attr := simp)]
theorem KD_fst : D.KD ≫ D.π₁ = pullback.fst _ _ ≫ D.m := D.hP.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem KD_snd : D.KD ≫ D.π₂ = pullback.snd _ _ ≫ D.π₂ := D.hP.lift_snd _ _ _

/-- The open part where the base-changed product is defined. -/
def BD' : D.BD.Opens := D.KD ⁻¹ᵁ D.U

theorem BD'_le : D.BD' ≤ D.KD ⁻¹ᵁ D.U := le_rfl

/-- The map from the base-changed correspondence to the division correspondence. -/
def HD : (D.BD' : Scheme.{u}) ⟶ D.ZD :=
  pullback.lift (D.BD'.ι ≫ pullback.fst _ _) (D.KD.resLE D.U D.BD' D.BD'_le)
    (by rw [Category.assoc, Scheme.Hom.resLE_comp_ι_assoc, KD_fst])

theorem HD_FD : D.HD ≫ D.FD = D.BD'.ι ≫ pullback.snd _ _ := by
  refine D.hP.hom_ext ?_ ?_
  · rw [Category.assoc, FD_fst, HD, pullback.lift_fst_assoc, Category.assoc, Category.assoc,
      pullback.condition]
  · rw [Category.assoc, FD_snd, HD, pullback.lift_snd_assoc, Scheme.Hom.resLE_comp_ι_assoc, KD_snd,
      Category.assoc]

/-- The comparison map into the base-changed correspondence. -/
def LD : D.ZD ⟶ D.BD := pullback.lift (pullback.fst _ _) D.FD (by rw [FD_fst])

theorem LD_KD : D.LD ≫ D.KD = pullback.snd _ _ ≫ D.U.ι := by
  refine D.hP.hom_ext ?_ ?_
  · rw [Category.assoc, KD_fst, LD, pullback.lift_fst_assoc, Category.assoc, pullback.condition]
  · rw [Category.assoc, KD_snd, LD, pullback.lift_snd_assoc, FD_snd, Category.assoc]

theorem range_LD : Set.range D.LD.base ⊆ Set.range D.BD'.ι.base := by
  rintro _ ⟨ζ, rfl⟩
  rw [Scheme.Opens.range_ι]
  change D.KD.base (D.LD.base ζ) ∈ D.U
  rw [← Scheme.Hom.comp_apply, LD_KD, Scheme.Hom.comp_apply]
  exact (pullback.snd D.m (D.U.ι ≫ D.π₁) ζ).2

/-- The comparison map restricted to the open multiplication domain. -/
def LD' : D.ZD ⟶ D.BD' := IsOpenImmersion.lift D.BD'.ι D.LD D.range_LD

theorem LD'_HD : D.LD' ≫ D.HD = 𝟙 _ := by
  have e : D.LD' ≫ D.BD'.ι = D.LD := IsOpenImmersion.lift_fac _ _ _
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, HD, pullback.lift_fst, reassoc_of% e, LD, pullback.lift_fst,
      Category.id_comp]
  · rw [← cancel_mono D.U.ι, Category.assoc, Category.assoc, HD, pullback.lift_snd_assoc,
      Scheme.Hom.resLE_comp_ι, reassoc_of% e, LD_KD, Category.id_comp]

theorem maximal_FD {ζ : D.ZD} (hζ : ∀ x', x' ⤳ ζ → x' = ζ) (q' : D.P) (hq' : q' ⤳ D.FD.base ζ) :
    q' = D.FD.base ζ := by
  revert q' hq'
  refine maximal_of_dominated D.FD D.HD (D.BD'.ι ≫ pullback.snd _ _)
    (Flat.generalizingMap _) D.HD_FD (b := D.LD'.base ζ) ?_ hζ
  rw [← Scheme.Hom.comp_apply, LD'_HD]; rfl

theorem dense_ΩD' (Y₀ : D.Y.Opens) (hY₀ : D.MaxMem Y₀) (hY₀U : D.SqSub Y₀)
    (hV₁ : D.FibDense D.π₁ (Set.range D.Φ.base)) : Dense (D.ΩD' : Set D.ΩD) := by
  have hVd : Dense (D.V : Set D.P) := by rw [coe_V]; exact dense_of_forall_dense_fibre D.π₁ _ hV₁
  have h1 : Dense ((D.pD ⁻¹ᵁ D.V : (D.ΩD : Scheme.{u}).Opens) : Set D.ΩD) :=
      hVd.preimage D.pD.isOpenMap
  have h2 := h1.inter_of_isOpen_left
    (dense_of_forall_maximal_mem (X := D.ΩD) (S := {x | ∀ x', x' ⤳ x → x' = x}) fun x hx => hx)
    (D.pD ⁻¹ᵁ D.V).isOpen
  refine h2.mono ?_
  rintro ζ ⟨hζV, hζmax⟩
  refine ⟨hζV, ?_⟩
  change D.GD.base ζ ∈ D.U
  apply hY₀U
  · rw [← Scheme.Hom.comp_apply, GD_fst, Scheme.Hom.comp_apply]
    apply hY₀
    exact fibMax_of_maximal _ (maximal_of_generalizingMap D.π₁ (Flat.generalizingMap _)
      (maximal_of_generalizingMap D.pD (Flat.generalizingMap _) hζmax))
  · rw [← Scheme.Hom.comp_apply, GD_snd, fD, Scheme.Hom.comp_apply]
    apply hY₀
    apply fibMax_of_maximal
    have hm : GeneralizingMap D.m.base := by
      rw [← D.Ψ_fst]; exact (Flat.generalizingMap D.Ψ).comp (Flat.generalizingMap D.π₁)
    apply maximal_of_generalizingMap D.m hm
    apply maximal_of_injective D.U.ι D.U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ppD_ι, Scheme.Hom.comp_apply]
    exact D.maximal_FD (maximal_of_generalizingMap D.ΩD.ι (Flat.generalizingMap _) hζmax)

theorem exists_Dv [IsDomain R] [IsDiscreteValuationRing R] (hassoc : D.Assoc)
    (hV₁ : D.FibDense D.π₁ (Set.range D.Φ.base)) (hV₂ : D.FibDense D.π₂ (Set.range D.Φ.base))
    (Y₀ : D.Y.Opens) (hY₀ : D.MaxMem Y₀) (hY₀U : D.SqSub Y₀) :
    ∃ Dv : D.P ⟶ D.Y, D.V.ι ≫ Dv = D.divl ∧ Dv ≫ D.y = D.π₁ ≫ D.y := by
  have : IsReduced D.P := D.isReduced_P
  have : Surjective D.pD := D.surjective_pD hV₁ hV₂ Y₀ hY₀ hY₀U
  have : IsReduced (pullback D.pD D.pD) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (pullback.fst D.pD D.pD ≫ D.ΩD.ι ≫ pullback.fst D.m (D.U.ι ≫ D.π₁) ≫ D.U.ι ≫ D.π₁ ≫ D.y)
  have hf : D.divl ≫ D.y = D.V.ι ≫ D.π₁ ≫ D.y := by
    rw [divl, Category.assoc, Category.assoc, ← D.hP.w, D.linv_fst_assoc]
  obtain ⟨Dv, -, hDv, hDy⟩ := exists_extension_of_descent (D.π₁ ≫
      D.y) D.y D.V D.divl hf D.pD D.fD D.fD_y
    D.ΩD' (D.dense_ΩD' Y₀ hY₀ hY₀U hV₁) inf_le_left (D.fD_agree hassoc)
  exact ⟨Dv, hDv, hDy⟩

include hMm hMy in
theorem isIso_translation [IsDomain R] [IsDiscreteValuationRing R] (hassoc : D.Assoc)
    (hV₁ : D.FibDense D.π₁ (Set.range D.Φ.base)) (hV₂ : D.FibDense D.π₂ (Set.range D.Φ.base))
    (Y₀ : D.Y.Opens) (hY₀ : D.MaxMem Y₀) (hY₀U : D.SqSub Y₀) :
    IsIso (D.hP.lift D.π₁ M (by rw [hMy])) := by
  have : IsReduced D.P := D.isReduced_P
  have : IsSeparated D.π₁ := MorphismProperty.of_isPullback D.hP.flip inferInstance
  obtain ⟨Dv, hDv, hDy⟩ := D.exists_Dv hassoc hV₁ hV₂ Y₀ hY₀ hY₀U
  set ΦM := D.hP.lift D.π₁ M (by rw [hMy])
  let N : D.P ⟶ D.P := D.hP.lift D.π₁ Dv (by rw [hDy])
  have hUΦM : D.U.ι ≫ ΦM = D.Φ := by
    refine D.hP.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, D.Φ_fst]
    · rw [Category.assoc, IsPullback.lift_snd, hMm, D.Φ_snd]
  have hVN : D.V.ι ≫ N = D.linv ≫ D.U.ι := by
    refine D.hP.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, Category.assoc, D.linv_fst]
    · rw [Category.assoc, IsPullback.lift_snd, hDv, divl, Category.assoc]
  have hVd : Dense (D.V : Set D.P) := by rw [coe_V]; exact dense_of_forall_dense_fibre D.π₁ _ hV₁
  have hUd : Dense (D.U : Set D.P) := by
    refine dense_of_forall_maximal_mem fun q hq => hY₀U q ?_ ?_
    · exact hY₀ _ (fibMax_of_maximal _ (maximal_of_generalizingMap D.π₁
        (Flat.generalizingMap _) hq))
    · exact hY₀ _ (fibMax_of_maximal _ (maximal_of_generalizingMap D.π₂
        (Flat.generalizingMap _) hq))
  have : IsDominant D.U.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hUd⟩
  have : IsDominant D.V.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hVd⟩
  refine ⟨N, ?_, ?_⟩
  · refine ext_of_isDominant_of_isSeparated (D.π₁ ≫ D.y) ?_ D.U.ι ?_
    · rw [Category.assoc, IsPullback.lift_fst_assoc, IsPullback.lift_fst_assoc, Category.id_comp]
    · rw [Category.comp_id, reassoc_of% hUΦM, ← D.Φ.isoOpensRange_hom_ι, Category.assoc, hVN,
        Iso.hom_inv_id_assoc]
  · refine ext_of_isDominant_of_isSeparated (D.π₁ ≫ D.y) ?_ D.V.ι ?_
    · rw [Category.assoc, IsPullback.lift_fst_assoc, IsPullback.lift_fst_assoc, Category.id_comp]
    · rw [Category.comp_id, reassoc_of% hVN, hUΦM, D.linv_Φ]

end Division

end Chunk

end Extension

open NeronModelInfra GoodReductionJacobian

end
end AbelianVarieties.NOSProofs.MultiplicationExtension

namespace NeronModelInfra

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Topology
open AbelianVarieties.NOSProofs.MultiplicationExtension

theorem
    exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (_hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 →
          p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y →
          q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    (Y₀ : Y.Opens)
    (hY₀ : ∀ p : Y, (∀ p' : Y, p' ⤳ p → y.base p' = y.base p → p' = p) → p ∈ Y₀)
    (hY₀U : ∀ q : ↑(pullback y y), (pullback.fst y y).base q ∈ Y₀ →
        (pullback.snd y y).base q ∈ Y₀ → q ∈ U) :
    ∃ M : SchemeHomOver (pullback.fst y y ≫ y) y,
      U.ι ≫ M.1 = m.1 ∧
      IsIso (pullback.lift (f := y) (g := y) (pullback.fst y y) M.1 M.2.symm) ∧
      IsIso (pullback.lift (f := y) (g := y) M.1 (pullback.snd y y)
          (M.2.trans pullback.condition)) := by
  have : Surjective y := ⟨fun s => ⟨a.base s, by rw [← Scheme.Hom.comp_apply, ha]; rfl⟩⟩
  have := hΦ
  have := hΨ
  let D : Extension.Chunk R :=
    { Y := Y, P := pullback y y, y := y, π₁ := pullback.fst y y, π₂ := pullback.snd y y,
      hP := IsPullback.of_hasPullback y y, U := U, m := m.1, hm := m.2,
      Φ := pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
          ((Category.assoc _ _ _).trans m.2.symm),
      Ψ := pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
        (m.2.trans (by rw [Category.assoc, pullback.condition])),
      Φ_fst := pullback.lift_fst _ _ _, Φ_snd := pullback.lift_snd _ _ _,
      Ψ_fst := pullback.lift_fst _ _ _, Ψ_snd := pullback.lift_snd _ _ _,
      Φ_open := hΦ, Ψ_open := hΨ, y_smooth := inferInstance, y_sep := inferInstance,
      π₁_smooth := inferInstance, π₂_smooth := inferInstance, π₁_surj := inferInstance, π₂_surj :=
          inferInstance }
  have hassoc' : D.Assoc := fun t u v p q => hassoc t u v p q
  have hU₁' : D.FibDense D.π₁ D.U := hU₁
  have hV₁' : D.FibDense D.π₁ (Set.range D.Φ.base) := hΦ₁
  have hV₂' : D.FibDense D.π₂ (Set.range D.Φ.base) := hΦ₂
  have hW₁' : D.flip.FibDense D.flip.π₂ (Set.range D.flip.Φ.base) := hΨ₁
  have hW₂' : D.flip.FibDense D.flip.π₁ (Set.range D.flip.Φ.base) := hΨ₂
  have hY₀' : D.MaxMem Y₀ := hY₀
  have hY₀U' : D.SqSub Y₀ := hY₀U
  obtain ⟨M, hMm, hMy⟩ := D.exists_M hassoc' hU₁' hV₂' Y₀ hY₀' hY₀U'
  have h1 := D.isIso_translation M hMm hMy hassoc' hV₁' hV₂' Y₀ hY₀' hY₀U'
  have hMy' : M ≫ D.flip.y = D.flip.π₁ ≫ D.flip.y := hMy.trans pullback.condition
  have h2 := D.flip.isIso_translation M hMm hMy' (D.assoc_flip hassoc') hW₂' hW₁' Y₀ hY₀'
      (D.sqSub_flip hY₀U')
  refine ⟨⟨M, hMy⟩, hMm, ?_, ?_⟩
  · have e : pullback.lift (f := y) (g := y) (pullback.fst y y) M hMy.symm =
      D.hP.lift D.π₁ M hMy.symm := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]; exact (D.hP.lift_fst _ _ _).symm
      · rw [pullback.lift_snd]; exact (D.hP.lift_snd _ _ _).symm
    rw [e]; exact h1
  · have e : pullback.lift (f := y) (g := y) M (pullback.snd y y) (hMy.trans pullback.condition) =
        D.flip.hP.lift D.flip.π₁ M hMy'.symm := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]; exact (D.flip.hP.lift_snd _ _ _).symm
      · rw [pullback.lift_snd]; exact (D.flip.hP.lift_fst _ _ _).symm
    rw [e]; exact h2

end
end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_relativeGroupLaw_mul_eq_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.GroupLawExtension

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace PointGroupLaw

section Algebra

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))

/-- The pair of relative points viewed as a point of the fiber product. -/
def pair {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (b c : SchemeHomOver t y) : T ⟶ pullback y y :=
  pullback.lift b.1 c.1 (b.2.trans c.2.symm)

@[scoped simp]
theorem pair_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (b c : SchemeHomOver t y) :
    pair y b c ≫ pullback.fst y y = b.1 :=
  pullback.lift_fst _ _ _

@[scoped simp]
theorem pair_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (b c : SchemeHomOver t y) :
    pair y b c ≫ pullback.snd y y = c.1 :=
  pullback.lift_snd _ _ _

theorem comp_pair {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec
    (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (b c : SchemeHomOver t y) :
    ψ ≫ pair y b c =
      pair y (GoodReductionJacobian.schemeHomOverComp ψ hψ b)
          (GoodReductionJacobian.schemeHomOverComp ψ hψ c) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pair_fst, pair_fst, GoodReductionJacobian.schemeHomOverComp_coe]
  · rw [Category.assoc, pair_snd, pair_snd, GoodReductionJacobian.schemeHomOverComp_coe]

theorem eq_pair_of {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (b c : SchemeHomOver t y)
    (q : T ⟶ pullback y y) (h₁ : q ≫ pullback.fst y y = b.1) (h₂ : q ≫ pullback.snd y y = c.1) :
    q = pair y b c := by
  apply pullback.hom_ext
  · rw [h₁, pair_fst]
  · rw [h₂, pair_snd]

variable (M : SchemeHomOver (pullback.fst y y ≫ y) y)

/-- Multiplication of relative points by the extended multiplication morphism. -/
def mulPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (b c : SchemeHomOver t y) : SchemeHomOver t y :=
  ⟨pair y b c ≫ M.1, by rw [Category.assoc, M.2, ← Category.assoc, pair_fst, b.2]⟩

@[scoped simp]
theorem mulPt_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (b c : SchemeHomOver t y) :
    (mulPt y M b c).1 = pair y b c ≫ M.1 :=
  rfl

theorem mulPt_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (b c : SchemeHomOver t y) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (mulPt y M b c) =
      mulPt y M (GoodReductionJacobian.schemeHomOverComp ψ hψ b)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ c) := by
  apply Subtype.ext
  rw [GoodReductionJacobian.schemeHomOverComp_coe, mulPt_coe, mulPt_coe, ← Category.assoc,
      comp_pair]

/-- Left translation paired with its fixed first coordinate. -/
abbrev PhiM : pullback y y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (pullback.fst y y) M.1 M.2.symm

/-- Right translation paired with its fixed second coordinate. -/
abbrev PsiM : pullback y y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) M.1 (pullback.snd y y) (M.2.trans pullback.condition)

theorem pair_PhiM {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (b c : SchemeHomOver t y) :
    pair y b c ≫ PhiM y M = pair y b (mulPt y M b c) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pair_fst, pair_fst]
  · rw [Category.assoc, pullback.lift_snd, pair_snd, mulPt_coe]

theorem pair_PsiM {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (b c : SchemeHomOver t y) :
    pair y b c ≫ PsiM y M = pair y (mulPt y M b c) c := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pair_fst, mulPt_coe]
  · rw [Category.assoc, pullback.lift_snd, pair_snd, pair_snd]

section DivisionLeft

variable [IsIso (PhiM y M)]

theorem inv_PhiM_fst : inv (PhiM y M) ≫ pullback.fst y y = pullback.fst y y := by
  rw [← cancel_epi (PhiM y M), IsIso.hom_inv_id_assoc, pullback.lift_fst]

theorem inv_PhiM_M : inv (PhiM y M) ≫ M.1 = pullback.snd y y := by
  rw [← cancel_epi (PhiM y M), IsIso.hom_inv_id_assoc, pullback.lift_snd]

/-- Left division obtained by inverting the left translation isomorphism. -/
def divL {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (b c : SchemeHomOver t y) : SchemeHomOver t y :=
  ⟨(pair y b c ≫ inv (PhiM y M)) ≫ pullback.snd y y, by
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc (inv (PhiM y M)),
        inv_PhiM_fst,
      ← Category.assoc, pair_fst, b.2]⟩

@[scoped simp]
theorem divL_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (b c : SchemeHomOver t y) :
    (divL y M b c).1 = (pair y b c ≫ inv (PhiM y M)) ≫ pullback.snd y y :=
  rfl

theorem mulPt_divL {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (b c : SchemeHomOver t y) :
    mulPt y M b (divL y M b c) = c := by
  apply Subtype.ext
  have hq : pair y b c ≫ inv (PhiM y M) = pair y b (divL y M b c) := by
    apply eq_pair_of
    · rw [Category.assoc, inv_PhiM_fst, pair_fst]
    · rfl
  rw [mulPt_coe, ← hq, Category.assoc, inv_PhiM_M, pair_snd]

theorem divL_mulPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (b c : SchemeHomOver t y) :
    divL y M b (mulPt y M b c) = c := by
  apply Subtype.ext
  rw [divL_coe, ← pair_PhiM, Category.assoc (pair y b c), IsIso.hom_inv_id, Category.comp_id,
      pair_snd]

end DivisionLeft

section DivisionRight

variable [IsIso (PsiM y M)]

theorem inv_PsiM_snd : inv (PsiM y M) ≫ pullback.snd y y = pullback.snd y y := by
  rw [← cancel_epi (PsiM y M), IsIso.hom_inv_id_assoc, pullback.lift_snd]

theorem inv_PsiM_M : inv (PsiM y M) ≫ M.1 = pullback.fst y y := by
  rw [← cancel_epi (PsiM y M), IsIso.hom_inv_id_assoc, pullback.lift_fst]

/-- Right division obtained by inverting the right translation isomorphism. -/
def divR {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (c b : SchemeHomOver t y) : SchemeHomOver t y :=
  ⟨(pair y c b ≫ inv (PsiM y M)) ≫ pullback.fst y y, by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (inv (PsiM y M)),
        inv_PsiM_snd,
      ← Category.assoc, pair_snd, b.2]⟩

@[scoped simp]
theorem divR_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (c b : SchemeHomOver t y) :
    (divR y M c b).1 = (pair y c b ≫ inv (PsiM y M)) ≫ pullback.fst y y :=
  rfl

theorem mulPt_divR {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (c b : SchemeHomOver t y) :
    mulPt y M (divR y M c b) b = c := by
  apply Subtype.ext
  have hq : pair y c b ≫ inv (PsiM y M) = pair y (divR y M c b) b := by
    apply eq_pair_of
    · rfl
    · rw [Category.assoc, inv_PsiM_snd, pair_snd]
  rw [mulPt_coe, ← hq, Category.assoc, inv_PsiM_M, pair_fst]

theorem divR_mulPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (c b : SchemeHomOver t y) :
    divR y M (mulPt y M c b) b = c := by
  apply Subtype.ext
  rw [divR_coe, ← pair_PsiM, Category.assoc (pair y c b), IsIso.hom_inv_id, Category.comp_id,
      pair_fst]

end DivisionRight

section Group

variable [IsIso (PhiM y M)] [IsIso (PsiM y M)]
variable (hM : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (b c d : SchemeHomOver t y),
  mulPt y M (mulPt y M b c) d = mulPt y M b (mulPt y M c d))
variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)

/-- The relative point induced by the chosen base section. -/
def basePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver t y :=
  ⟨t ≫ a, by rw [Category.assoc, ha, Category.comp_id]⟩

/-- The identity point recovered by dividing the base section by itself. -/
def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver t y :=
  divL y M (basePt y a ha t) (basePt y a ha t)

include hM in
theorem mulPt_onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (b : SchemeHomOver t y) :
    mulPt y M b (onePt y M a ha t) = b := by
  conv_lhs => rw [← mulPt_divR y M b (basePt y a ha t)]
  rw [hM, onePt, mulPt_divL, mulPt_divR]

include hM in
theorem divR_basePt_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (b : SchemeHomOver t y) :
    mulPt y M (divR y M (basePt y a ha t) (basePt y a ha t)) b = b := by
  conv_lhs => rw [← mulPt_divL y M (basePt y a ha t) b]
  rw [← hM, mulPt_divR, mulPt_divL]

include hM in
theorem onePt_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    onePt y M a ha t = divR y M (basePt y a ha t) (basePt y a ha t) := by
  rw [← divR_basePt_mulPt y M hM a ha t (onePt y M a ha t), mulPt_onePt y M hM a ha]

include hM in
theorem onePt_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (b : SchemeHomOver t y) :
    mulPt y M (onePt y M a ha t) b = b := by
  rw [onePt_eq y M hM a ha, divR_basePt_mulPt y M hM a ha]

/-- The relative group law determined by associative multiplication and division. -/
def law : RelativeGroupLaw R y where
  mul _ b c := mulPt y M b c
  one t := onePt y M a ha t
  inv t b := divR y M (onePt y M a ha t) b
  mul_assoc t b c d := hM t b c d
  one_mul t b := onePt_mulPt y M hM a ha t b
  mul_one t b := mulPt_onePt y M hM a ha t b
  inv_mul_cancel _ b := mulPt_divR y M _ b
  mul_natural _ _ ψ hψ b c := mulPt_natural y M ψ hψ b c

@[scoped simp]
theorem law_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (b c : SchemeHomOver t y) :
    (law y M hM a ha).mul t b c = mulPt y M b c :=
  rfl

end Group

end Algebra

open AbelianVarieties.NOSProofs.MultiplicationExtension.Extension
  (dense_of_forall_maximal_mem)

section Geometry

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (M : SchemeHomOver (pullback.fst y y ≫ y) y)

/-- The scheme of composable pairs. -/
abbrev Y3 : Scheme.{u} := pullback (pullback.snd y y) (pullback.fst y y)

/-- Projection to the first composable pair. -/
abbrev P12 : Y3 y ⟶ pullback y y := pullback.fst (pullback.snd y y) (pullback.fst y y)

/-- Projection to the second composable pair. -/
abbrev P23 : Y3 y ⟶ pullback y y := pullback.snd (pullback.snd y y) (pullback.fst y y)

@[reassoc]
theorem P12_snd : P12 y ≫ pullback.snd y y = P23 y ≫ pullback.fst y y := pullback.condition

@[reassoc]
theorem fst_y : pullback.fst y y ≫ y = pullback.snd y y ≫ y := pullback.condition

/-- Multiply the first pair of a composable triple. -/
def mulFst : Y3 y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (P12 y ≫ M.1) (P23 y ≫ pullback.snd y y)
    (by rw [Category.assoc, M.2, Category.assoc, fst_y, P12_snd_assoc, fst_y])

/-- Multiply the second pair of a composable triple. -/
def mulSnd : Y3 y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (P12 y ≫ pullback.fst y y) (P23 y ≫ M.1)
    (by rw [Category.assoc, Category.assoc, M.2, fst_y, P12_snd_assoc, fst_y])

@[reassoc (attr := simp)]
theorem mulFst_fst : mulFst y M ≫ pullback.fst y y = P12 y ≫ M.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem mulFst_snd : mulFst y M ≫ pullback.snd y y = P23 y ≫ pullback.snd y y :=
    pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem mulSnd_fst : mulSnd y M ≫ pullback.fst y y = P12 y ≫ pullback.fst y y :=
    pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem mulSnd_snd : mulSnd y M ≫ pullback.snd y y = P23 y ≫ M.1 := pullback.lift_snd _ _ _

/-- The triple product point determined by three relative points. -/
def triple {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (b c d : SchemeHomOver t y) : T ⟶ Y3 y :=
  pullback.lift (pair y b c) (pair y c d) (by rw [pair_snd, pair_fst])

theorem triple_mulFst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (b c d : SchemeHomOver t y) :
    triple y b c d ≫ mulFst y M = pair y (mulPt y M b c) d := by
  apply pullback.hom_ext
  · rw [Category.assoc, mulFst_fst, ← Category.assoc, triple, pullback.lift_fst, pair_fst,
      mulPt_coe]
  · rw [Category.assoc, mulFst_snd, ← Category.assoc, triple, pullback.lift_snd, pair_snd, pair_snd]

theorem triple_mulSnd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (b c d : SchemeHomOver t y) :
    triple y b c d ≫ mulSnd y M = pair y b (mulPt y M c d) := by
  apply pullback.hom_ext
  · rw [Category.assoc, mulSnd_fst, ← Category.assoc, triple, pullback.lift_fst, pair_fst, pair_fst]
  · rw [Category.assoc, mulSnd_snd, ← Category.assoc, triple, pullback.lift_snd, pair_snd,
      mulPt_coe]

theorem mulPt_assoc_of (hA : mulFst y M ≫ M.1 = mulSnd y M ≫ M.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (b c d : SchemeHomOver t y) :
    mulPt y M (mulPt y M b c) d = mulPt y M b (mulPt y M c d) := by
  apply Subtype.ext
  rw [mulPt_coe, mulPt_coe, ← triple_mulFst, ← triple_mulSnd, Category.assoc, Category.assoc, hA]

/-- The dense locus on which associativity reduces to the partial law. -/
def assocLocus (Y₀ : Y.Opens) : (Y3 y).Opens :=
  (P12 y ≫ pullback.fst y y) ⁻¹ᵁ Y₀ ⊓ (P12 y ≫ pullback.snd y y) ⁻¹ᵁ Y₀ ⊓ (P23 y ≫
      pullback.snd y y) ⁻¹ᵁ Y₀ ⊓
    (P12 y ≫ M.1) ⁻¹ᵁ Y₀ ⊓ (P23 y ≫ M.1) ⁻¹ᵁ Y₀

theorem mem_assocLocus (Y₀ : Y.Opens) (x : Y3 y) :
    x ∈ assocLocus y M Y₀ ↔
      (pullback.fst y y).base ((P12 y).base x) ∈ Y₀ ∧
          (pullback.snd y y).base ((P12 y).base x) ∈ Y₀ ∧
      (pullback.snd y y).base ((P23 y).base x) ∈ Y₀ ∧ M.1.base ((P12 y).base x) ∈ Y₀ ∧
      M.1.base ((P23 y).base x) ∈ Y₀ := by
  simp only [assocLocus, TopologicalSpace.Opens.mem_inf, Scheme.Hom.mem_preimage,
      Scheme.Hom.comp_apply,
    and_assoc]

theorem universallyOpen_M [Smooth y] [IsIso (PhiM y M)] : UniversallyOpen M.1 := by
  have h : M.1 = PhiM y M ≫ pullback.snd y y := (pullback.lift_snd _ _ _).symm
  rw [h]
  infer_instance

theorem dense_assocLocus [Smooth y] [IsIso (PhiM y M)] (Y₀ : Y.Opens) (hd : Dense (Y₀ : Set Y)) :
    Dense (assocLocus y M Y₀ : Set (Y3 y)) := by
  have : UniversallyOpen M.1 := universallyOpen_M y M
  have h1 : Dense ((P12 y ≫ pullback.fst y y) ⁻¹ᵁ Y₀ : Set (Y3 y)) :=
      hd.preimage (Scheme.Hom.isOpenMap _)
  have h2 : Dense ((P12 y ≫ pullback.snd y y) ⁻¹ᵁ Y₀ : Set (Y3 y)) :=
      hd.preimage (Scheme.Hom.isOpenMap _)
  have h3 : Dense ((P23 y ≫ pullback.snd y y) ⁻¹ᵁ Y₀ : Set (Y3 y)) :=
      hd.preimage (Scheme.Hom.isOpenMap _)
  have h4 : Dense ((P12 y ≫ M.1) ⁻¹ᵁ Y₀ : Set (Y3 y)) := hd.preimage (Scheme.Hom.isOpenMap _)
  have h5 : Dense ((P23 y ≫ M.1) ⁻¹ᵁ Y₀ : Set (Y3 y)) := hd.preimage (Scheme.Hom.isOpenMap _)
  simp only [assocLocus, TopologicalSpace.Opens.coe_inf]
  exact (((h1.inter_of_isOpen_left h2 (TopologicalSpace.Opens.isOpen _)).inter_of_isOpen_right h3
    (TopologicalSpace.Opens.isOpen _)).inter_of_isOpen_right h4
    (TopologicalSpace.Opens.isOpen _)).inter_of_isOpen_right h5 (TopologicalSpace.Opens.isOpen _)

variable [IsDomain R] [IsDiscreteValuationRing R] [Smooth y] [IsSeparated y]
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
variable (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 →
          p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y →
          q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
variable (hMm : U.ι ≫ M.1 = m.1) [IsIso (PhiM y M)]
variable (Y₀ : Y.Opens)
    (hY₀ : ∀ p : Y, (∀ p' : Y, p' ⤳ p → y.base p' = y.base p → p' = p) → p ∈ Y₀)
    (hY₀U : ∀ q : ↑(pullback y y), (pullback.fst y y).base q ∈ Y₀ →
        (pullback.snd y y).base q ∈ Y₀ → q ∈ U)

include hassoc hMm hY₀ hY₀U in
theorem mulFst_M_eq_mulSnd_M : mulFst y M ≫ M.1 = mulSnd y M ≫ M.1 := by
  have : IsReduced (Y3 y) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (P12 y ≫
        pullback.fst y y ≫ y)
  let L : (Y3 y).Opens := assocLocus y M Y₀
  have : IsDominant L.ι := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Opens.range_ι]
    exact dense_assocLocus y M Y₀
        (dense_of_forall_maximal_mem fun x hx => hY₀ x fun x' h _ => hx x' h)
  refine ext_of_isDominant_of_isSeparated y ?_ L.ι ?_
  · simp only [Category.assoc, M.2, mulFst_fst_assoc, mulSnd_fst_assoc]
  have memL : ∀ x : (L : Scheme.{u}), (pullback.fst y y).base ((P12 y).base x.1) ∈ Y₀ ∧
      (pullback.snd y y).base ((P12 y).base x.1) ∈ Y₀ ∧
          (pullback.snd y y).base ((P23 y).base x.1) ∈ Y₀ ∧
      M.1.base ((P12 y).base x.1) ∈ Y₀ ∧ M.1.base ((P23 y).base x.1) ∈ Y₀ := fun x =>
    (mem_assocLocus y M Y₀ x.1).mp x.2
  have hc : ∀ x : Y3 y, (pullback.fst y y).base ((P23 y).base x) = (pullback.snd y y).base
      ((P12 y).base x) :=
    fun x => by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, P12_snd]
  have hrU : Set.range U.ι.base = (U : Set ↑(pullback y y)) := Scheme.Opens.range_ι U
  have hr₁ : Set.range (L.ι ≫ P12 y).base ⊆ Set.range U.ι.base := by
    rw [hrU]; rintro _ ⟨x, rfl⟩
    change (P12 y) x.1 ∈ U
    exact hY₀U _ (memL x).1 (memL x).2.1
  have hr₂ : Set.range (L.ι ≫ P23 y).base ⊆ Set.range U.ι.base := by
    rw [hrU]; rintro _ ⟨x, rfl⟩
    change (P23 y) x.1 ∈ U
    exact hY₀U _ ((hc x.1).symm ▸ (memL x).2.1) (memL x).2.2.1
  have hr₃ : Set.range (L.ι ≫ mulFst y M).base ⊆ Set.range U.ι.base := by
    rw [hrU]; rintro _ ⟨x, rfl⟩
    change (mulFst y M) x.1 ∈ U
    refine hY₀U _ ?_ ?_
    · rw [← Scheme.Hom.comp_apply, mulFst_fst, Scheme.Hom.comp_apply]; exact (memL x).2.2.2.1
    · rw [← Scheme.Hom.comp_apply, mulFst_snd, Scheme.Hom.comp_apply]; exact (memL x).2.2.1
  have hr₄ : Set.range (L.ι ≫ mulSnd y M).base ⊆ Set.range U.ι.base := by
    rw [hrU]; rintro _ ⟨x, rfl⟩
    change (mulSnd y M) x.1 ∈ U
    refine hY₀U _ ?_ ?_
    · rw [← Scheme.Hom.comp_apply, mulSnd_fst, Scheme.Hom.comp_apply]; exact (memL x).1
    · rw [← Scheme.Hom.comp_apply, mulSnd_snd, Scheme.Hom.comp_apply]; exact (memL x).2.2.2.2
  let t : (L : Scheme.{u}) ⟶ Spec (CommRingCat.of R) := L.ι ≫ P12 y ≫ pullback.fst y y ≫ y
  have e₁ := IsOpenImmersion.lift_fac U.ι (L.ι ≫ P12 y) hr₁
  have e₂ := IsOpenImmersion.lift_fac U.ι (L.ι ≫ P23 y) hr₂
  have e₃ := IsOpenImmersion.lift_fac U.ι (L.ι ≫ mulFst y M) hr₃
  have e₄ := IsOpenImmersion.lift_fac U.ι (L.ι ≫ mulSnd y M) hr₄
  let uu : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨IsOpenImmersion.lift U.ι (L.ι ≫ P12 y) hr₁, by rw [reassoc_of% e₁]⟩
  let vv : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨IsOpenImmersion.lift U.ι (L.ι ≫ P23 y) hr₂, by rw [reassoc_of% e₂, ← P12_snd_assoc, ← fst_y]⟩
  let pp : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨IsOpenImmersion.lift U.ι (L.ι ≫ mulFst y M) hr₃, by rw [reassoc_of% e₃, mulFst_fst_assoc, M.2]⟩
  let qq : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨IsOpenImmersion.lift U.ι (L.ι ≫ mulSnd y M) hr₄, by rw [reassoc_of% e₄, mulSnd_fst_assoc]⟩
  have key := hassoc t uu vv pp qq
    (by rw [reassoc_of% e₁, reassoc_of% e₂, P12_snd])
    (by rw [← hMm, reassoc_of% e₁, reassoc_of% e₃, mulFst_fst])
    (by rw [reassoc_of% e₃, reassoc_of% e₂, mulFst_snd])
    (by rw [reassoc_of% e₄, reassoc_of% e₁, mulSnd_fst])
    (by rw [← hMm, reassoc_of% e₂, reassoc_of% e₄, mulSnd_snd])
  rw [← hMm, reassoc_of% e₃, reassoc_of% e₄] at key
  simpa only [Category.assoc] using key

include hassoc hMm hY₀ hY₀U in
theorem mulPt_assoc {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (b c d : SchemeHomOver t y) :
    mulPt y M (mulPt y M b c) d = mulPt y M b (mulPt y M c d) :=
  mulPt_assoc_of y M (mulFst_M_eq_mulSnd_M y M U m hassoc hMm Y₀ hY₀ hY₀U) t b c d

end Geometry

end PointGroupLaw

end
end AbelianVarieties.NOSProofs.GroupLawExtension

namespace NeronModelInfra

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Topology
open AbelianVarieties.NOSProofs.GroupLawExtension

theorem exists_relativeGroupLaw_mul_eq_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 →
          p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y →
          q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    (Y₀ : Y.Opens)
    (hY₀ : ∀ p : Y, (∀ p' : Y, p' ⤳ p → y.base p' = y.base p → p' = p) → p ∈ Y₀)
    (hY₀U : ∀ q : ↑(pullback y y), (pullback.fst y y).base q ∈ Y₀ →
        (pullback.snd y y).base q ∈ Y₀ → q ∈ U) :
    ∃ L : RelativeGroupLaw R y,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫
          pullback.fst y y ≫ y))
        (b c d : SchemeHomOver t y),
        b.1 = w.1 ≫ U.ι ≫ pullback.fst y y → c.1 = w.1 ≫ U.ι ≫ pullback.snd y y → d.1 = w.1 ≫ m.1 →
        L.mul t b c = d := by
  obtain ⟨M, hMm, hΦM, hΨM⟩ :=
    exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
      y U m hU₁ hU₂ hΦ hΦ₁ hΦ₂ hΨ hΨ₁ hΨ₂ hassoc a ha Y₀ hY₀ hY₀U
  have : IsIso (PointGroupLaw.PhiM y M) := hΦM
  have : IsIso (PointGroupLaw.PsiM y M) := hΨM
  refine ⟨PointGroupLaw.law y M (PointGroupLaw.mulPt_assoc y M U m hassoc hMm Y₀ hY₀ hY₀U) a ha, ?_⟩
  intro T t w b c d hb hc hd
  apply Subtype.ext
  rw [PointGroupLaw.law_mul, PointGroupLaw.mulPt_coe, hd, ← hMm]
  have hw : PointGroupLaw.pair y b c = w.1 ≫ U.ι := by
    apply pullback.hom_ext
    · rw [PointGroupLaw.pair_fst, hb, Category.assoc]
    · rw [PointGroupLaw.pair_snd, hc, Category.assoc]
  rw [hw, Category.assoc]

end
end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.MultiplicationDomainExtension

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace DomainExtension

open AbelianVarieties.NOSProofs.QuasiFiniteTranslationGluing.TranslationGluing
  (exists_lift_of_isClosedImmersion)

section General

theorem dense_of_forall_dense_fibre {X Y : Type*} [TopologicalSpace X] (p : X → Y)
    (S : Set X) (h : ∀ y : Y, Dense ((Subtype.val : {x : X // p x = y} → X) ⁻¹' S)) :
    Dense S :=
  AbelianVarieties.NOSProofs.GraphClosureRigidity.GraphClosure.dense_of_forall_dense_fibre p S h

theorem eq_univ_of_dense_subset {X : Type*} [TopologicalSpace X] {S C : Set X} (hS : Dense S)
    (hC : IsClosed C) (h : S ⊆ C) : C = Set.univ :=
  Set.eq_univ_of_univ_subset ((hS.closure_eq ▸ closure_minimal h hC :))

end General

section Graph

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
variable (D : (pullback y y).Opens) (hUD : U ≤ D) (M : SchemeHomOver (D.ι ≫ pullback.fst y y ≫ y) y)
variable (hM : (pullback y y).homOfLE hUD ≫ M.1 = m.1)

/-- The triple product containing the multiplication graph. -/
abbrev Y3g : Scheme.{u} := pullback (pullback.fst y y ≫ y) y

/-- The graph of the original partial multiplication. -/
abbrev grm : (U : Scheme.{u}) ⟶ Y3g y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm

/-- The graph of multiplication on the enlarged domain. -/
abbrev grM : (D : Scheme.{u}) ⟶ Y3g y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y) D.ι M.1 M.2.symm

include hM in
theorem homOfLE_grM : (pullback y y).homOfLE hUD ≫ grM y D M = grm y U m := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Scheme.homOfLE_ι]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hM]

theorem dense_range_homOfLE (hU : Dense (U : Set ↑(pullback y y))) :
    Dense (Set.range ((pullback y y).homOfLE hUD).base) := by
  have h1 : Set.range ((pullback y y).homOfLE hUD).base = D.ι.base ⁻¹'
      (U : Set ↑(pullback y y)) := by
    ext d
    constructor
    · rintro ⟨u, rfl⟩
      change D.ι (((pullback y y).homOfLE hUD) u) ∈ U
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      exact u.2
    · intro hd
      change d.1 ∈ U at hd
      let u : (U : Scheme.{u}) := ⟨d.1, hd⟩
      refine ⟨u, D.ι.isOpenEmbedding.injective ?_⟩
      change ((pullback y y).homOfLE hUD ≫ D.ι) u = D.ι d
      rw [Scheme.homOfLE_ι]
      rfl
  rw [h1]
  exact hU.preimage D.ι.isOpenMap

include hM in
theorem range_grM_subset (hU : Dense (U : Set ↑(pullback y y))) :
    Set.range (grM y D M).base ⊆ closure (Set.range (grm y U m).base) := by
  have hC : (grM y D M).base ⁻¹' closure (Set.range (grm y U m).base) = Set.univ := by
    refine eq_univ_of_dense_subset (dense_range_homOfLE y U D hUD hU) (isClosed_closure.preimage
      (grM y D M).base.hom.continuous) ?_
    rintro _ ⟨u, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, homOfLE_grM y U m D hUD M hM]
    exact subset_closure ⟨u, rfl⟩
  rintro _ ⟨d, rfl⟩
  have : d ∈ (grM y D M).base ⁻¹' closure (Set.range (grm y U m).base) := by rw [hC]; trivial
  exact this

/-- Left translation paired with its fixed first coordinate. -/
abbrev PhiM : (D : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (D.ι ≫ pullback.fst y y) M.1
      ((Category.assoc _ _ _).trans M.2.symm)

/-- Right translation paired with its fixed second coordinate. -/
abbrev PsiM : (D : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) M.1 (D.ι ≫ pullback.snd y y)
    (M.2.trans (by rw [Category.assoc, pullback.condition]))

/-- Projection to the first and third coordinates of the graph ambient space. -/
abbrev p13 : Y3g y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y)
    (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫
        y) y)
    (by rw [Category.assoc]; exact pullback.condition)

/-- Projection to the second and third coordinates of the graph ambient space. -/
abbrev p23 : Y3g y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y)
    (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫
        y) y)
    (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)

theorem grM_p13 : grM y D M ≫ p13 y = PhiM y D M := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, pullback.lift_snd]

theorem grM_p23 : grM y D M ≫ p23 y ≫ (pullbackSymmetry y y).hom = PsiM y D M := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_fst, pullback.lift_snd]
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc]

theorem exists_isOpenImmersion_comp_eq_grM [IsReduced (D : Scheme.{u})] {G : Scheme.{u}}
    (γ : G ⟶ Y3g y)
    [IsClosedImmersion γ] [IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)]
    (h : Set.range (grM y D M).base ⊆ Set.range γ.base) :
    ∃ g : (D : Scheme.{u}) ⟶ G, IsOpenImmersion g ∧ g ≫ γ = grM y D M := by
  obtain ⟨g, hg⟩ := exists_lift_of_isClosedImmersion (grM y D M) γ h
  have hgι : g ≫ (γ ≫ pullback.fst (pullback.fst y y ≫ y) y) = D.ι := by
    rw [← Category.assoc, hg, pullback.lift_fst]
  have : IsOpenImmersion (g ≫ (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)) := by
    rw [hgι]; infer_instance
  exact ⟨g, IsOpenImmersion.of_comp g (γ ≫ pullback.fst (pullback.fst y y ≫ y) y), hg⟩

theorem isOpenImmersion_PhiM_of {G : Scheme.{u}} (γ : G ⟶ Y3g y) (g : (D : Scheme.{u}) ⟶ G)
    [IsOpenImmersion g] (hg : g ≫ γ = grM y D M) [IsOpenImmersion (γ ≫ p13 y)] :
    IsOpenImmersion (PhiM y D M) := by
  have h : PhiM y D M = g ≫ (γ ≫ p13 y) := by rw [← grM_p13, ← hg, Category.assoc]
  rw [h]
  infer_instance

theorem isOpenImmersion_PsiM_of {G : Scheme.{u}} (γ : G ⟶ Y3g y) (g : (D : Scheme.{u}) ⟶ G)
    [IsOpenImmersion g] (hg : g ≫ γ = grM y D M) [IsOpenImmersion (γ ≫ p23 y)] :
    IsOpenImmersion (PsiM y D M) := by
  have h : PsiM y D M = g ≫ (γ ≫ p23 y) ≫ (pullbackSymmetry y y).hom := by
    rw [← grM_p23, ← hg]; simp only [Category.assoc]
  rw [h]
  infer_instance

theorem homOfLE_PhiM (hM : (pullback y y).homOfLE hUD ≫ M.1 = m.1) :
    (pullback y y).homOfLE hUD ≫ PhiM y D M =
      pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
          ((Category.assoc _ _ _).trans m.2.symm) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Scheme.homOfLE_ι_assoc]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hM]

theorem homOfLE_PsiM (hM : (pullback y y).homOfLE hUD ≫ M.1 = m.1) :
    (pullback y y).homOfLE hUD ≫ PsiM y D M =
      pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
        (m.2.trans (by rw [Category.assoc, pullback.condition])) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hM]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Scheme.homOfLE_ι_assoc]

theorem dense_fibre_mono {X Z : Type*} [TopologicalSpace X] (p : X →
    Z) {S S' : Set X} (hSS' : S ⊆ S')
    (x : Z) (h : Dense ((Subtype.val : {q : X // p q = x} → X) ⁻¹' S)) :
    Dense ((Subtype.val : {q : X // p q = x} → X) ⁻¹' S') :=
  h.mono (Set.preimage_mono hSS')

theorem range_comp_subset {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g).base ⊆ Set.range g.base := by
  rintro _ ⟨a, rfl⟩
  exact ⟨f.base a, (Scheme.Hom.comp_apply f g a).symm⟩

end Graph

end DomainExtension

end
end AbelianVarieties.NOSProofs.MultiplicationDomainExtension

namespace NeronModelInfra

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Topology
open AbelianVarieties.NOSProofs.MultiplicationDomainExtension

theorem isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 →
          p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y →
          q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (D : (pullback y y).Opens) (hUD : U ≤ D)
    (M : SchemeHomOver (D.ι ≫ pullback.fst y y ≫ y) y)
    (hM : (pullback y y).homOfLE hUD ≫ M.1 = m.1) :
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (D : Set ↑(pullback y y)))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (D : Set ↑(pullback y y)))) ∧
      IsOpenImmersion
          (pullback.lift (f := y) (g := y) (D.ι ≫ pullback.fst y y) M.1
            ((Category.assoc _ _ _).trans M.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (D.ι ≫ pullback.fst y y) M.1
            ((Category.assoc _ _ _).trans M.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (D.ι ≫ pullback.fst y y) M.1
            ((Category.assoc _ _ _).trans M.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y) (g := y) M.1 (D.ι ≫ pullback.snd y y)
            (M.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) M.1 (D.ι ≫ pullback.snd y y)
            (M.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) M.1 (D.ι ≫ pullback.snd y y)
            (M.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (u v p q : SchemeHomOver t (D.ι ≫ pullback.fst y y ≫ y)),
        u.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.fst y y →
        p.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ M.1 →
        p.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.snd y y →
        q.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ D.ι ≫ pullback.fst y y →
        q.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ M.1 →
        p.1 ≫ M.1 = q.1 ≫ M.1) := by
  obtain ⟨G, γ, hγ, -, hrange, hq12, hq13, hq23, -⟩ :=
    exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
      y U m hU₁ hU₂ hΦ hΦ₁ hΦ₂ hΨ hΨ₁ hΨ₂ hassoc
  have := hγ
  have := hq12
  have := hq13
  have := hq23
  have hU : Dense (U : Set ↑(pullback y y)) :=
    DomainExtension.dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hU₁
  have : IsReduced (D : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (D.ι ≫
        pullback.fst y y ≫ y)
  have hsub : Set.range (DomainExtension.grM y D M).base ⊆ Set.range γ.base := by
    rw [hrange]
    exact DomainExtension.range_grM_subset y U m D hUD M hM hU
  obtain ⟨g, hg, hgγ⟩ := DomainExtension.exists_isOpenImmersion_comp_eq_grM y D M γ hsub
  have := hg
  have hΦM : IsOpenImmersion (DomainExtension.PhiM y D M) :=
      DomainExtension.isOpenImmersion_PhiM_of y D M γ g hgγ
  have hΨM : IsOpenImmersion (DomainExtension.PsiM y D M) :=
      DomainExtension.isOpenImmersion_PsiM_of y D M γ g hgγ
  have : UniversallyOpen M.1 := by
    have h : M.1 = DomainExtension.PhiM y D M ≫ pullback.snd y y := (pullback.lift_snd _ _ _).symm
    rw [h]
    infer_instance
  have hUD' : (U : Set ↑(pullback y y)) ⊆ (D : Set ↑(pullback y y)) := hUD
  have hΦr : Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
      ((Category.assoc _ _ _).trans m.2.symm)).base ⊆ Set.range
          (DomainExtension.PhiM y D M).base := by
    rw [← DomainExtension.homOfLE_PhiM y U m D hUD M hM]
    exact DomainExtension.range_comp_subset _ _
  have hΨr : Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
      (m.2.trans (by rw [Category.assoc, pullback.condition]))).base ⊆
      Set.range (DomainExtension.PsiM y D M).base := by
    rw [← DomainExtension.homOfLE_PsiM y U m D hUD M hM]
    exact DomainExtension.range_comp_subset _ _
  refine ⟨fun x => DomainExtension.dense_fibre_mono _ hUD' x (hU₁ x),
    fun x => DomainExtension.dense_fibre_mono _ hUD' x (hU₂ x), hΦM,
    fun x => DomainExtension.dense_fibre_mono _ hΦr x (hΦ₁ x),
    fun x => DomainExtension.dense_fibre_mono _ hΦr x (hΦ₂ x), hΨM,
    fun x => DomainExtension.dense_fibre_mono _ hΨr x (hΨ₁ x),
    fun x => DomainExtension.dense_fibre_mono _ hΨr x (hΨ₂ x), ?_⟩
  intro T t u v p q h₁ h₂ h₃ h₄ h₅
  exact AbelianVarieties.NOSProofs.QuasiFiniteLawExtension.LawExtension.assoc_ext
    y D M U m hUD hM hassoc hU t u v p q h₁ h₂ h₃ h₄ h₅

end
end NeronModelInfra
end
