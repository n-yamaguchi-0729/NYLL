/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.NoetherianSpace
public import Nyll.AbelianVarieties.NeronModels.Density
public import Nyll.AbelianVarieties.NeronModels.GluingDensity
public import Nyll.SchemeTheory.LocalGeometry.Normality
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.LocalGeometry.SmoothNormalStalk
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced

/-!
# Quasi-finite charts for glued partial group laws

Glue the translated multiplication charts and use normality to upgrade quasi-finite charts
with a dense inverse to open immersions. Reuse the existing translation and associativity frames.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
    TopologicalSpace Topology

universe u

open AbelianVarieties.NOSProofs.GluingFibreDensity.TranslationCharts
  (Phi Psi U2 Ua Ub V2 Ya bY bY_ι bY_ι_assoc ch ch_fst ch_fst_assoc ch_fst_y' ch_snd eV eV_hom_ι
    eV_hom_ι_assoc eV_inv_ι eV_inv_ι_assoc fst_y isClosedImmersion_jA isClosedImmersion_kA
    isOpenImmersion_ch isOpenImmersion_rho isOpenImmersion_Θ isPullback_jA isPullback_kA
    isPullback_rho isPullback_Θ jA jA_fst jA_snd kA kA_fst kA_snd la la_ι m_eq_Phi_snd m_y range_ch
    rho rho_kA rho_y universallyOpen_m Θ Θ_fst Θ_fst_y Θ_snd Θ_snd_assoc θ θ_ι θ_ι_assoc)
open scoped AbelianVarieties.NOSProofs.GluingFibreDensity.TranslationCharts
open AbelianVarieties.NOSProofs.GraphClosureRigidity.GraphClosure
  (dense_of_forall_dense_fibre)
open AbelianVarieties.NOSProofs.GluingFibreDensity.TranslationCharts (dense_of_forall_maximal_mem)

namespace AbelianVarieties.NOSProofs.QuasiFiniteTranslationGluing

namespace TranslationGluing

section General

theorem exists_lift_of_isClosedImmersion {D G Z : Scheme.{u}} [IsReduced D] (f : D ⟶ Z) (γ : G ⟶ Z)
    [IsClosedImmersion γ] (h : Set.range f.base ⊆ Set.range γ.base) : ∃ g : D ⟶ G, g ≫ γ = f := by
  have : Surjective (pullback.fst f γ) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro d
    exact h ⟨d, rfl⟩⟩
  have : IsIso (pullback.fst f γ) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.fst f γ) ≫ pullback.snd f γ, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem subset_closure_inter {X : Type*} [TopologicalSpace X] {O A A' : Set X} (hO : IsOpen O)
    (hA : IsOpen A) (h : O ⊆ closure A) (h' : O ⊆ closure A') : O ⊆ closure (A ∩ A') := by
  intro o ho
  rw [mem_closure_iff]
  intro N hN hoN
  obtain ⟨a₁, ⟨ha₁N, ha₁O⟩, ha₁A⟩ : (N ∩ O ∩ A).Nonempty :=
    mem_closure_iff.mp (h ho) (N ∩ O) (hN.inter hO) ⟨hoN, ho⟩
  obtain ⟨a₂, ⟨⟨ha₂N, -⟩, ha₂A⟩, ha₂A'⟩ : (N ∩ O ∩ A ∩ A').Nonempty :=
    mem_closure_iff.mp (h' ha₁O) (N ∩ O ∩ A) ((hN.inter hO).inter hA) ⟨⟨ha₁N, ha₁O⟩, ha₁A⟩
  exact ⟨a₂, ha₂N, ha₂A, ha₂A'⟩

theorem inter_image_subset_closure {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {c : X →
    Z}
    (hc : Continuous c) {P : Set Z} (hP : IsOpen P) {V V' : Set X} (h : V ⊆ closure V') :
    P ∩ c '' V ⊆ closure (P ∩ c '' V') := by
  refine subset_trans ?_ hP.inter_closure
  refine Set.inter_subset_inter_right _ ?_
  exact subset_trans (Set.image_mono h) (image_closure_subset_closure_image hc)

end General

section GlueDense

theorem denseRange_lift {X : Scheme.{u}} (Vi Vj W : X.Opens) (hWi : W ≤ Vi) (hWj : W ≤ Vj)
    (hcl : ((Vi ⊓ Vj : X.Opens) : Set X) ⊆ closure (W : Set X)) :
    DenseRange (pullback.lift (f := Vi.ι) (g := Vj.ι) (X.homOfLE hWi) (X.homOfLE hWj)
      (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι])).base := by
  set ℓ := pullback.lift (f := Vi.ι) (g := Vj.ι) (X.homOfLE hWi) (X.homOfLE hWj)
      (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]) with hℓ
  have hℓι : ℓ ≫ pullback.fst Vi.ι Vj.ι ≫ Vi.ι = W.ι := by
    rw [pullback.lift_fst_assoc, Scheme.homOfLE_ι]
  rw [DenseRange, dense_iff_inter_open]
  intro N hN ⟨n₀, hn₀⟩
  let e : ↑(pullback Vi.ι Vj.ι) → X := (pullback.fst Vi.ι Vj.ι ≫ Vi.ι).base
  have he : IsOpenEmbedding e := (pullback.fst Vi.ι Vj.ι ≫ Vi.ι).isOpenEmbedding
  have hmem : ∀ n : ↑(pullback Vi.ι Vj.ι), e n ∈ ((Vi ⊓ Vj : X.Opens) : Set X) := by
    intro n
    refine ⟨?_, ?_⟩
    · change (pullback.fst Vi.ι Vj.ι ≫ Vi.ι).base n ∈ (Vi : Set X)
      exact ((pullback.fst Vi.ι Vj.ι).base n).2
    · change (pullback.fst Vi.ι Vj.ι ≫ Vi.ι).base n ∈ (Vj : Set X)
      rw [pullback.condition]
      exact ((pullback.snd Vi.ι Vj.ι).base n).2
  have hopen : IsOpen (e '' N) := he.isOpenMap _ hN
  obtain ⟨x, ⟨n, hn, rfl⟩, hxW⟩ : (e '' N ∩ (W : Set X)).Nonempty :=
    mem_closure_iff.mp (hcl (hmem n₀)) (e '' N) hopen ⟨n₀, hn₀, rfl⟩
  let w : ↥(W : Scheme.{u}) := ⟨e n, hxW⟩
  refine ⟨n, hn, ⟨w, ?_⟩⟩
  apply he.injective
  exact congrArg (fun f : (W : Scheme.{u}) ⟶ X => f.base w) hℓι

theorem exists_glue {X Z S : Scheme.{u}} [IsReduced X] (p : X ⟶ S) (s : Z ⟶ S) [IsSeparated s]
    {I : Type*} (V : I → X.Opens) (hV : IsOpenCover V) (f : ∀ i, (V i : Scheme.{u}) ⟶ Z)
    (hf : ∀ i, f i ≫ s = (V i).ι ≫ p)
    (hagree : ∀ i j, ∃ (W : X.Opens) (hWi : W ≤ V i) (hWj : W ≤ V j),
      ((V i ⊓ V j : X.Opens) : Set X) ⊆ closure (W : Set X) ∧ X.homOfLE hWi ≫ f i = X.homOfLE hWj ≫
        f j) :
    ∃ F : X ⟶ Z, (∀ i, (V i).ι ≫ F = f i) ∧ F ≫ s = p := by
  let 𝒰 := X.openCoverOfIsOpenCover V hV
  have hcompat : ∀ i j : I,
      pullback.fst (V i).ι (V j).ι ≫ f i = pullback.snd (V i).ι (V j).ι ≫ f j := by
    intro i j
    obtain ⟨W, hWi, hWj, hcl, hW⟩ := hagree i j
    have : IsReduced (pullback (V i).ι (V j).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst (V i).ι (V j).ι ≫ (V i).ι)
    let ℓ := pullback.lift (f := (V i).ι) (g := (V j).ι) (X.homOfLE hWi) (X.homOfLE hWj)
      (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι])
    have : IsDominant ℓ := ⟨denseRange_lift (V i) (V j) W hWi hWj hcl⟩
    refine ext_of_isDominant_of_isSeparated s ?_ ℓ ?_
    · rw [Category.assoc, Category.assoc, hf, hf, pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hW]
  refine ⟨𝒰.glueMorphisms f hcompat, fun i => 𝒰.ι_glueMorphisms f hcompat i, ?_⟩
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun i => ?_
  exact (𝒰.ι_glueMorphisms_assoc f hcompat i s).trans (hf i)

theorem exists_sup_extension {B Z S : Scheme.{u}} [IsReduced B] (p : B ⟶ S) (s : Z ⟶ S) [IsSeparated
    s]
    (D₁ D₂ : B.Opens) (M₁ : (D₁ : Scheme.{u}) ⟶ Z) (M₂ : (D₂ : Scheme.{u}) ⟶ Z)
    (hM₁ : M₁ ≫ s = D₁.ι ≫ p) (hM₂ : M₂ ≫ s = D₂.ι ≫ p)
    (W : B.Opens) (hW₁ : W ≤ D₁) (hW₂ : W ≤ D₂) (hcl : ((D₁ ⊓ D₂ : B.Opens) : Set B) ⊆ closure (W :
      Set B))
    (hagree : B.homOfLE hW₁ ≫ M₁ = B.homOfLE hW₂ ≫ M₂) :
    ∃ M : ((D₁ ⊔ D₂ : B.Opens) : Scheme.{u}) ⟶ Z,
      B.homOfLE (le_sup_left : D₁ ≤ D₁ ⊔ D₂) ≫ M = M₁ ∧
      B.homOfLE (le_sup_right : D₂ ≤ D₁ ⊔ D₂) ≫ M = M₂ ∧ M ≫ s = (D₁ ⊔ D₂).ι ≫ p := by
  set E : B.Opens := D₁ ⊔ D₂ with hE
  let V : Bool → (E : Scheme.{u}).Opens := fun b => bif b then E.ι ⁻¹ᵁ D₁ else E.ι ⁻¹ᵁ D₂
  have hVt : V true = E.ι ⁻¹ᵁ D₁ := rfl
  have hVf : V false = E.ι ⁻¹ᵁ D₂ := rfl
  have hV : IsOpenCover V := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    rcases x.2 with hx | hx
    · exact Opens.mem_iSup.mpr ⟨true, hx⟩
    · exact Opens.mem_iSup.mpr ⟨false, hx⟩
  have : IsReduced (E : Scheme.{u}) := isReduced_of_isOpenImmersion E.ι
  have hr₁ : Set.range ((V true).ι ≫ E.ι).base ⊆ Set.range D₁.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact x.2
  have hr₂ : Set.range ((V false).ι ≫ E.ι).base ⊆ Set.range D₂.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact x.2
  let g₁ : ((V true : (E : Scheme.{u}).Opens) : Scheme.{u}) ⟶ D₁ := IsOpenImmersion.lift D₁.ι _ hr₁
  let g₂ : ((V false : (E : Scheme.{u}).Opens) : Scheme.{u}) ⟶ D₂ := IsOpenImmersion.lift D₂.ι _ hr₂
  have hg₁ : g₁ ≫ D₁.ι = (V true).ι ≫ E.ι := IsOpenImmersion.lift_fac _ _ _
  have hg₂ : g₂ ≫ D₂.ι = (V false).ι ≫ E.ι := IsOpenImmersion.lift_fac _ _ _
  let f : ∀ b, ((V b : (E : Scheme.{u}).Opens) : Scheme.{u}) ⟶ Z := fun b =>
    match b with
    | true => g₁ ≫ M₁
    | false => g₂ ≫ M₂
  have hft : f true = g₁ ≫ M₁ := rfl
  have hff : f false = g₂ ≫ M₂ := rfl
  have hf : ∀ b, f b ≫ s = (V b).ι ≫ (E.ι ≫ p) := by
    rintro (_ | _)
    · rw [hff, Category.assoc, hM₂, reassoc_of% hg₂]
    · rw [hft, Category.assoc, hM₁, reassoc_of% hg₁]
  let WE : (E : Scheme.{u}).Opens := E.ι ⁻¹ᵁ W
  have hWE₁ : WE ≤ V true := fun x hx => hW₁ hx
  have hWE₂ : WE ≤ V false := fun x hx => hW₂ hx
  have hclE : ((V true ⊓ V false : (E : Scheme.{u}).Opens) : Set E) ⊆ closure (WE : Set E) := by
    intro x hx
    have hx' : E.ι.base x ∈ ((D₁ ⊓ D₂ : B.Opens) : Set B) := hx
    rw [E.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
    refine closure_mono ?_ (hcl hx')
    rintro y hyW
    exact ⟨⟨y, Or.inl (hW₁ hyW)⟩, hyW, rfl⟩
  have hrW : Set.range (WE.ι ≫ E.ι).base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact x.2
  let w : (WE : Scheme.{u}) ⟶ W := IsOpenImmersion.lift W.ι _ hrW
  have hw : w ≫ W.ι = WE.ι ≫ E.ι := IsOpenImmersion.lift_fac _ _ _
  have hw₁ : (E : Scheme.{u}).homOfLE hWE₁ ≫ g₁ = w ≫ B.homOfLE hW₁ := by
    rw [← cancel_mono D₁.ι, Category.assoc, Category.assoc, hg₁, Scheme.homOfLE_ι_assoc,
      Scheme.homOfLE_ι, hw]
  have hw₂ : (E : Scheme.{u}).homOfLE hWE₂ ≫ g₂ = w ≫ B.homOfLE hW₂ := by
    rw [← cancel_mono D₂.ι, Category.assoc, Category.assoc, hg₂, Scheme.homOfLE_ι_assoc,
      Scheme.homOfLE_ι, hw]
  have hcross : (E : Scheme.{u}).homOfLE hWE₁ ≫ f true = (E : Scheme.{u}).homOfLE hWE₂ ≫ f false :=
    by
    rw [hft, hff, reassoc_of% hw₁, reassoc_of% hw₂, hagree]
  have hagree' : ∀ b b', ∃ (W' : (E : Scheme.{u}).Opens) (hWi : W' ≤ V b) (hWj : W' ≤ V b'),
      ((V b ⊓ V b' : (E : Scheme.{u}).Opens) : Set E) ⊆ closure (W' : Set E) ∧
        (E : Scheme.{u}).homOfLE hWi ≫ f b = (E : Scheme.{u}).homOfLE hWj ≫ f b' := by
    rintro (_ | _) (_ | _)
    · exact ⟨V false, le_rfl, le_rfl, by rw [inf_idem]; exact subset_closure, rfl⟩
    · refine ⟨WE, hWE₂, hWE₁, ?_, hcross.symm⟩
      rw [inf_comm]; exact hclE
    · exact ⟨WE, hWE₁, hWE₂, hclE, hcross⟩
    · exact ⟨V true, le_rfl, le_rfl, by rw [inf_idem]; exact subset_closure, rfl⟩
  obtain ⟨F, hF, hFs⟩ := exists_glue (E.ι ≫ p) s V hV f hf hagree'
  have hs₁ : Set.range (B.homOfLE (le_sup_left : D₁ ≤ E)).base ⊆ Set.range (V true).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨d, rfl⟩
    change E.ι.base ((B.homOfLE _).base d) ∈ (D₁ : Set B)
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact d.2
  have hs₂ : Set.range (B.homOfLE (le_sup_right : D₂ ≤ E)).base ⊆ Set.range (V false).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨d, rfl⟩
    change E.ι.base ((B.homOfLE _).base d) ∈ (D₂ : Set B)
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact d.2
  let h₁ : (D₁ : Scheme.{u}) ⟶ V true := IsOpenImmersion.lift (V true).ι _ hs₁
  let h₂ : (D₂ : Scheme.{u}) ⟶ V false := IsOpenImmersion.lift (V false).ι _ hs₂
  have hh₁ : h₁ ≫ (V true).ι = B.homOfLE _ := IsOpenImmersion.lift_fac _ _ _
  have hh₂ : h₂ ≫ (V false).ι = B.homOfLE _ := IsOpenImmersion.lift_fac _ _ _
  have hid₁ : h₁ ≫ g₁ = 𝟙 _ := by
    rw [← cancel_mono D₁.ι, Category.assoc, hg₁, reassoc_of% hh₁, Scheme.homOfLE_ι,
      Category.id_comp]
  have hid₂ : h₂ ≫ g₂ = 𝟙 _ := by
    rw [← cancel_mono D₂.ι, Category.assoc, hg₂, reassoc_of% hh₂, Scheme.homOfLE_ι,
      Category.id_comp]
  refine ⟨F, ?_, ?_, hFs⟩
  · rw [← hh₁, Category.assoc, hF, hft, reassoc_of% hid₁]
  · rw [← hh₂, Category.assoc, hF, hff, reassoc_of% hid₂]

end GlueDense

section Translate

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)

theorem dense_fibre_jA [IsSeparated y] (S : Set ↑(pullback y y)) (s : Spec (CommRingCat.of R))
    (hS : Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s} →
      ↑(pullback y y)) ⁻¹' S)) :
    Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' ((jA y a ha).base ⁻¹' S)) := by
  have hainj : Function.Injective a.base := by
    intro s₁ s₂ h
    have := congrArg y.base h
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ha] at this
  let φ : {b : ↑Y // y.base b = s} → {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s}
    :=
    fun b => ⟨(jA y a ha).base b.1, by rw [← Scheme.Hom.comp_apply, jA_fst, Scheme.Hom.comp_apply,
      b.2]⟩
  have hφc : Continuous φ := ((jA y a ha).base.hom.continuous.comp
    continuous_subtype_val).subtype_mk _
  have hφi : Topology.IsInducing φ := by
    refine Topology.IsInducing.of_comp hφc continuous_subtype_val ?_
    exact (jA y a ha).isClosedEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
  have hE : pullback.fst (pullback.fst y y) a =
      (pullback.fst (pullback.fst y y) a ≫ pullback.snd y y) ≫ jA y a ha := by
    apply pullback.hom_ext
    · rw [Category.assoc, jA_fst, pullback.condition, Category.assoc, ← pullback.condition_assoc,
        reassoc_of% (pullback.condition (f := pullback.fst y y) (g := a)), reassoc_of% ha]
    · rw [Category.assoc, jA_snd, Category.comp_id]
  have hφs : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨z, hz⟩ : q ∈ Set.range (pullback.fst (pullback.fst y y) a).base := by
      rw [Scheme.Pullback.range_fst]; exact ⟨s, hq.symm⟩
    refine ⟨⟨(pullback.snd y y).base q, hainj ?_⟩, ?_⟩
    · congr 1
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hq, ←
        Scheme.Hom.comp_apply, ha]
      rfl
    · apply Subtype.ext
      change (jA y a ha).base ((pullback.snd y y).base q) = q
      conv_rhs => rw [← hz, hE]
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz]
  have hpre : ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' ((jA y a ha).base ⁻¹' S)) =
      φ ⁻¹' ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s} →
        ↑(pullback y y)) ⁻¹' S) :=
    rfl
  rw [hpre, hφi.dense_iff]
  intro b
  rw [Set.image_preimage_eq _ hφs, hS.closure_eq]
  exact Set.mem_univ _

theorem dense_Ub [IsSeparated y]
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (U : Set ↑(pullback y y)))) :
    Dense ((Ub y U a ha : Y.Opens) : Set Y) :=
  dense_of_forall_dense_fibre (fun b => y.base b) _ fun s => dense_fibre_jA y a ha _ s (hU₁ _)

variable {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y)

/-- Insert the section into the first coordinate of the multiplication graph. -/
abbrev sA : pullback y y ⟶ pullback (pullback.fst y y ≫ y) y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y)
    (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
      (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
    (pullback.snd y y)
    (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
      pullback.condition])

/-- The graph map of the partial multiplication. -/
abbrev grm : (U : Scheme.{u}) ⟶ pullback (pullback.fst y y ≫ y) y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm

variable (g₀ : (U : Scheme.{u}) ⟶ G) (hg₀ : g₀ ≫ γ = grm y U m)

/-- Lift a section-compatible pair into the closed multiplication graph. -/
def mkΓa {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    T ⟶ pullback γ (sA y a ha) :=
  pullback.lift (w ≫ g₀)
    (pullback.lift (f := y) (g := y) x (w ≫ m.1)
      (by rw [Category.assoc, m.2, ← h2, Category.assoc, Category.assoc, pullback.condition]))
    (by
      rw [Category.assoc, hg₀]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
          exact h1
        · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst]
          exact h2
      · simp only [Category.assoc, pullback.lift_snd])

theorem mkΓa_pτ {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    mkΓa y U m a ha γ g₀ hg₀ x w h1 h2 ≫ pullback.snd γ (sA y a ha) ≫ pullback.fst y y = x := by
  rw [mkΓa, pullback.lift_snd_assoc, pullback.lift_fst]

theorem mkΓa_pι {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    mkΓa y U m a ha γ g₀ hg₀ x w h1 h2 ≫ pullback.snd γ (sA y a ha) ≫ pullback.snd y y = w ≫ m.1 :=
      by
  rw [mkΓa, pullback.lift_snd_assoc, pullback.lift_snd]

include hg₀ in
theorem translate {Y' : Scheme.{u}} {y' : Y' ⟶ Spec (CommRingCat.of R)} (ι τ : SchemeHomOver y y')
    (hΓa : pullback.snd γ (sA y a ha) ≫ pullback.fst y y ≫ τ.1 = pullback.snd γ (sA y a ha) ≫
      pullback.snd y y ≫ ι.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ Y) (hx : x ≫ y = t) (w : T ⟶ (U :
      Scheme.{u}))
    (hw₁ : w ≫ U.ι ≫ pullback.fst y y = t ≫ a) (hw₂ : w ≫ U.ι ≫ pullback.snd y y = x) :
    x ≫ τ.1 = w ≫ m.1 ≫ ι.1 := by
  have h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a := by rw [hw₁, reassoc_of% hx]
  rw [← mkΓa_pτ y U m a ha γ g₀ hg₀ x w h1 hw₂, Category.assoc, Category.assoc, hΓa, ←
    Category.assoc,
    ← Category.assoc, Category.assoc _ (pullback.snd γ (sA y a ha)), mkΓa_pι, Category.assoc]

end Translate

section Core

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
  {Y' : Scheme.{u}} {y' : Y' ⟶ Spec (CommRingCat.of R)} (ι τ : SchemeHomOver y y') [IsOpenImmersion
    ι.1]
  (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
    u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
    p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
      pullback.snd y y →
    q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1
      ≫ m.1 →
    p.1 ≫ m.1 = q.1 ≫ m.1)
  (htr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ Y) (_ : x ≫ y = t)
      (w : T ⟶ (U : Scheme.{u})),
    w ≫ U.ι ≫ pullback.fst y y = t ≫ a → w ≫ U.ι ≫ pullback.snd y y = x → x ≫ τ.1 = w ≫ m.1 ≫ ι.1)

include hassoc htr in
theorem core01 {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u₀ u₁ wa wq : T ⟶ (U :
    Scheme.{u}))
    (ht₁ : u₁ ≫ U.ι ≫ pullback.fst y y ≫ y = t)
    (h1 : u₀ ≫ U.ι ≫ pullback.fst y y ≫ ι.1 = u₁ ≫ U.ι ≫ pullback.fst y y ≫ τ.1)
    (h2 : u₀ ≫ U.ι ≫ pullback.snd y y = u₁ ≫ U.ι ≫ pullback.snd y y)
    (hwa : wa ≫ U.ι = (u₁ ≫ U.ι ≫ pullback.fst y y) ≫ jA y a ha)
    (hwq : wq ≫ U.ι = (u₁ ≫ m.1) ≫ jA y a ha) :
    u₀ ≫ m.1 ≫ ι.1 = u₁ ≫ m.1 ≫ τ.1 := by
  have hwa₁ : wa ≫ U.ι ≫ pullback.fst y y = t ≫ a := by
    rw [reassoc_of% hwa, jA_fst, reassoc_of% ht₁]
  have hwa₂ : wa ≫ U.ι ≫ pullback.snd y y = u₁ ≫ U.ι ≫ pullback.fst y y := by
    rw [reassoc_of% hwa, jA_snd, Category.comp_id]
  have hm₁ : (u₁ ≫ m.1) ≫ y = t := by rw [Category.assoc, m.2, ht₁]
  have hwq₁ : wq ≫ U.ι ≫ pullback.fst y y = t ≫ a := by
    rw [reassoc_of% hwq, jA_fst, reassoc_of% hm₁]
  have hwq₂ : wq ≫ U.ι ≫ pullback.snd y y = u₁ ≫ m.1 := by
    rw [reassoc_of% hwq, jA_snd, Category.comp_id]
  have e1 : (u₁ ≫ U.ι ≫ pullback.fst y y) ≫ τ.1 = wa ≫ m.1 ≫ ι.1 :=
    htr t _ (by rw [Category.assoc, Category.assoc, ht₁]) wa hwa₁ hwa₂
  have hb : u₀ ≫ U.ι ≫ pullback.fst y y = wa ≫ m.1 := by
    rw [← cancel_mono ι.1]
    simp only [Category.assoc] at e1 ⊢
    rw [h1, e1]
  have e2 : (u₁ ≫ m.1) ≫ τ.1 = wq ≫ m.1 ≫ ι.1 := htr t _ hm₁ wq hwq₁ hwq₂
  have hu₀ : u₀ ≫ U.ι ≫ pullback.fst y y ≫ y = t := by
    rw [reassoc_of% hb, m.2, reassoc_of% hwa₁, ha, Category.comp_id]
  have hwa₀ : wa ≫ U.ι ≫ pullback.fst y y ≫ y = t := by rw [reassoc_of% hwa₁, ha, Category.comp_id]
  have hwq₀ : wq ≫ U.ι ≫ pullback.fst y y ≫ y = t := by rw [reassoc_of% hwq₁, ha, Category.comp_id]
  have key := hassoc t ⟨wa, hwa₀⟩ ⟨u₁, ht₁⟩ ⟨u₀, hu₀⟩ ⟨wq, hwq₀⟩ hwa₂ hb h2 (by rw [hwq₁, hwa₁])
    hwq₂
  change u₀ ≫ m.1 = wq ≫ m.1 at key
  rw [reassoc_of% key, ← e2, Category.assoc]

include hassoc htr in
theorem core02 {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u₀ ub v wd : T ⟶ (U :
    Scheme.{u}))
    (ht : ub ≫ U.ι ≫ pullback.fst y y ≫ y = t)
    (hub : ub ≫ U.ι ≫ pullback.snd y y = t ≫ a) (hv₁ : v ≫ U.ι ≫ pullback.fst y y = ub ≫ m.1)
    (h1 : u₀ ≫ U.ι ≫ pullback.fst y y = ub ≫ U.ι ≫ pullback.fst y y)
    (h2 : u₀ ≫ U.ι ≫ pullback.snd y y ≫ ι.1 = (v ≫ U.ι ≫ pullback.snd y y) ≫ τ.1)
    (hwd : wd ≫ U.ι = (v ≫ U.ι ≫ pullback.snd y y) ≫ jA y a ha) :
    u₀ ≫ m.1 = v ≫ m.1 := by
  have hv₀ : v ≫ U.ι ≫ pullback.fst y y ≫ y = t := by rw [reassoc_of% hv₁, m.2, ht]
  have hd : (v ≫ U.ι ≫ pullback.snd y y) ≫ y = t := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, hv₀]
  have hwd₁ : wd ≫ U.ι ≫ pullback.fst y y = t ≫ a := by rw [reassoc_of% hwd, jA_fst, reassoc_of% hd]
  have hwd₂ : wd ≫ U.ι ≫ pullback.snd y y = v ≫ U.ι ≫ pullback.snd y y := by
    rw [reassoc_of% hwd, jA_snd, Category.comp_id]
  have e1 : (v ≫ U.ι ≫ pullback.snd y y) ≫ τ.1 = wd ≫ m.1 ≫ ι.1 := htr t _ hd wd hwd₁ hwd₂
  have hd₀ : u₀ ≫ U.ι ≫ pullback.snd y y = wd ≫ m.1 := by
    rw [← cancel_mono ι.1, Category.assoc, Category.assoc, h2, e1, Category.assoc]
  have hu₀ : u₀ ≫ U.ι ≫ pullback.fst y y ≫ y = t := by rw [reassoc_of% h1, ht]
  have hwd₀ : wd ≫ U.ι ≫ pullback.fst y y ≫ y = t := by rw [reassoc_of% hwd₁, ha, Category.comp_id]
  have key := hassoc t ⟨ub, ht⟩ ⟨wd, hwd₀⟩ ⟨v, hv₀⟩ ⟨u₀, hu₀⟩ (by rw [hub, hwd₁]) hv₁ hwd₂.symm h1
    hd₀
  exact key.symm

end Core

section Pieces

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R)) (ι τ : SchemeHomOver y y')
  [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]

/-- The original multiplication chart in the glued product. -/
def P0 : (pullback y' y').Opens := ch y y' ι ι ''ᵁ U

/-- The chart translated in its first input. -/
def P1 : (pullback y' y').Opens := ch y y' τ ι ''ᵁ U

/-- The chart translated in its second input. -/
def P2 : (pullback y' y').Opens := ch y y' ι τ ''ᵁ U2 y U m a ha

/-- Identify the original domain with its open image in the glued product. -/
def e0 : (U : Scheme.{u}) ≅ (P0 y U y' ι : Scheme.{u}) := (ch y y' ι ι).isoImage U

/-- Identify the first translated domain with its open image. -/
def e1 : (U : Scheme.{u}) ≅ (P1 y U y' ι τ : Scheme.{u}) := (ch y y' τ ι).isoImage U

/-- Identify the second translated domain with its open image. -/
def e2 : (U2 y U m a ha : Scheme.{u}) ≅ (P2 y U m a ha y' ι τ : Scheme.{u}) := (ch y y' ι
    τ).isoImage _

@[reassoc]
theorem e0_inv_ι : (e0 y U y' ι).inv ≫ U.ι ≫ ch y y' ι ι = (P0 y U y' ι).ι :=
  Scheme.Hom.isoImage_inv_ι _ _
@[reassoc]
theorem e0_hom_ι : (e0 y U y' ι).hom ≫ (P0 y U y' ι).ι = U.ι ≫ ch y y' ι ι :=
  Scheme.Hom.isoImage_hom_ι _ _
@[reassoc]
theorem e1_inv_ι : (e1 y U y' ι τ).inv ≫ U.ι ≫ ch y y' τ ι = (P1 y U y' ι τ).ι :=
  Scheme.Hom.isoImage_inv_ι _ _
@[reassoc]
theorem e1_hom_ι : (e1 y U y' ι τ).hom ≫ (P1 y U y' ι τ).ι = U.ι ≫ ch y y' τ ι :=
  Scheme.Hom.isoImage_hom_ι _ _
@[reassoc]
theorem e2_inv_ι :
    (e2 y U m a ha y' ι τ).inv ≫ (U2 y U m a ha).ι ≫ ch y y' ι τ = (P2 y U m a ha y' ι τ).ι :=
  Scheme.Hom.isoImage_inv_ι _ _
@[reassoc]
theorem e2_hom_ι :
    (e2 y U m a ha y' ι τ).hom ≫ (P2 y U m a ha y' ι τ).ι = (U2 y U m a ha).ι ≫ ch y y' ι τ :=
  Scheme.Hom.isoImage_hom_ι _ _

/-- The multiplication map transported to the original open chart. -/
def f0 : (P0 y U y' ι : Scheme.{u}) ⟶ Y' := (e0 y U y' ι).inv ≫ m.1 ≫ ι.1

/-- The multiplication map transported to the first translated chart. -/
def f1 : (P1 y U y' ι τ : Scheme.{u}) ⟶ Y' := (e1 y U y' ι τ).inv ≫ m.1 ≫ τ.1

/-- The multiplication map transported to the second translated chart. -/
def f2 : (P2 y U m a ha y' ι τ : Scheme.{u}) ⟶ Y' :=
  (e2 y U m a ha y' ι τ).inv ≫ (eV y U m a ha).inv ≫ θ y U m a ha ≫ m.1 ≫ ι.1

theorem f0_y' : f0 y U m y' ι ≫ y' = (P0 y U y' ι).ι ≫ pullback.fst y' y' ≫ y' := by
  rw [f0, Category.assoc, Category.assoc, ι.2, m.2, ← e0_inv_ι_assoc, ch_fst_assoc, ι.2]

theorem f1_y' : f1 y U m y' ι τ ≫ y' = (P1 y U y' ι τ).ι ≫ pullback.fst y' y' ≫ y' := by
  rw [f1, Category.assoc, Category.assoc, τ.2, m.2, ← e1_inv_ι_assoc, ch_fst_assoc, τ.2]

theorem f2_y' : f2 y U m a ha y' ι τ ≫ y' = (P2 y U m a ha y' ι τ).ι ≫ pullback.fst y' y' ≫ y' := by
  rw [f2, Category.assoc, Category.assoc, Category.assoc, Category.assoc, ι.2, m.2, θ_ι_assoc,
    Θ_fst_y,
    ← e2_inv_ι_assoc, ch_fst_assoc, ι.2, ← eV_inv_ι_assoc]

end Pieces

section Agree

variable {R : Type u} [CommRing R]
  {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R)) (ι τ : SchemeHomOver y y')
  [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]

/-- The dense comparison domain for the original and first translated laws. -/
def U01 : (pullback y y).Opens := (pullback.fst y y ⁻¹ᵁ Ub y U a ha) ⊓ U.ι ''ᵁ (m.1 ⁻¹ᵁ Ub y U a ha)

/-- The translated domain with its second coordinate in the section chart. -/
def U2' : (pullback y y).Opens := U2 y U m a ha ⊓ (pullback.snd y y ⁻¹ᵁ Ub y U a ha)

/-- The overlap used to compare the original and first translated laws. -/
def W01 : (pullback y' y').Opens := P0 y U y' ι ⊓ ch y y' τ ι ''ᵁ U01 y U m a ha

/-- The overlap used to compare the original and second translated laws. -/
def W02 : (pullback y' y').Opens := P0 y U y' ι ⊓ ch y y' ι τ ''ᵁ U2' y U m a ha

theorem W01_le_P0 : W01 y U m a ha y' ι τ ≤ P0 y U y' ι := inf_le_left
theorem W01_le_P1 : W01 y U m a ha y' ι τ ≤ P1 y U y' ι τ :=
  le_trans inf_le_right ((Scheme.Hom.image_le_image_iff _ _ _).mpr inf_le_right |>.trans
    ((Scheme.Hom.image_le_image_iff _ _ _).mpr (by
      intro q hq
      have hq' : q ∈ ((U.ι ''ᵁ (m.1 ⁻¹ᵁ Ub y U a ha) : (pullback y y).Opens) : Set _) := hq
      rw [Scheme.Hom.coe_image] at hq'
      obtain ⟨u, -, rfl⟩ := hq'
      exact u.2)))
theorem W02_le_P0 : W02 y U m a ha y' ι τ ≤ P0 y U y' ι := inf_le_left
theorem W02_le_P2 : W02 y U m a ha y' ι τ ≤ P2 y U m a ha y' ι τ :=
  le_trans inf_le_right ((Scheme.Hom.image_le_image_iff _ _ _).mpr inf_le_left)

variable (hU₁ : ∀ x : Y,
    Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y))
      ⁻¹'
      (U : Set ↑(pullback y y))))

include hU₁ in
theorem subset_closure_U01 [Smooth y] [IsSeparated y] [IsOpenImmersion (Phi y U m)] :
    (U : Set ↑(pullback y y)) ⊆ closure (U01 y U m a ha : Set ↑(pullback y y)) := by
  have hUb : Dense ((Ub y U a ha : Y.Opens) : Set Y) := dense_Ub y U a ha hU₁
  have : UniversallyOpen m.1 := universallyOpen_m y U m
  have hA : Dense ((pullback.fst y y ⁻¹ᵁ Ub y U a ha : (pullback y y).Opens) : Set ↑(pullback y y))
    :=
    hUb.preimage (pullback.fst y y).isOpenMap
  have hD : Dense ((m.1 ⁻¹ᵁ Ub y U a ha : (U : Scheme.{u}).Opens) : Set ↑(U : Scheme.{u})) :=
    hUb.preimage m.1.isOpenMap
  have hA' : (U : Set ↑(pullback y y)) ⊆
      closure ((U.ι ''ᵁ (m.1 ⁻¹ᵁ Ub y U a ha) : (pullback y y).Opens) : Set ↑(pullback y y)) := by
    rw [Scheme.Hom.coe_image, ← Scheme.Opens.range_ι U, ← Set.image_univ, ← hD.closure_eq]
    exact image_closure_subset_closure_image U.ι.continuous
  simp only [U01, Opens.coe_inf]
  exact subset_closure_inter U.isOpen (Opens.isOpen _) (Dense.mono (fun _ h => h) hA |>.closure_eq ▸
    fun _ _ => Set.mem_univ _) hA'

include hU₁ in
theorem subset_closure_U2' [Smooth y] [IsSeparated y] :
    (U2 y U m a ha : Set ↑(pullback y y)) ⊆ closure (U2' y U m a ha : Set ↑(pullback y y)) := by
  have hUb : Dense ((Ub y U a ha : Y.Opens) : Set Y) := dense_Ub y U a ha hU₁
  have hA : Dense ((pullback.snd y y ⁻¹ᵁ Ub y U a ha : (pullback y y).Opens) : Set ↑(pullback y y))
    :=
    hUb.preimage (pullback.snd y y).isOpenMap
  simp only [U2', Opens.coe_inf]
  intro q hq
  have := (U2 y U m a ha).isOpen.inter_closure (t := ((pullback.snd y y ⁻¹ᵁ Ub y U a ha : (pullback
    y y).Opens) : Set _))
  exact this ⟨hq, hA.closure_eq ▸ Set.mem_univ q⟩

include hU₁ in
theorem closure_W01 [Smooth y] [IsSeparated y] [IsOpenImmersion (Phi y U m)] :
    ((P0 y U y' ι ⊓ P1 y U y' ι τ : (pullback y' y').Opens) : Set ↑(pullback y' y')) ⊆
      closure (W01 y U m a ha y' ι τ : Set ↑(pullback y' y')) := by
  simp only [W01, P1, Opens.coe_inf, Scheme.Hom.coe_image]
  exact inter_image_subset_closure (ch y y' τ ι).continuous (P0 y U y' ι).isOpen (subset_closure_U01
    y U m a ha hU₁)

include hU₁ in
theorem closure_W02 [Smooth y] [IsSeparated y] :
    ((P0 y U y' ι ⊓ P2 y U m a ha y' ι τ : (pullback y' y').Opens) : Set ↑(pullback y' y')) ⊆
      closure (W02 y U m a ha y' ι τ : Set ↑(pullback y' y')) := by
  simp only [W02, P2, Opens.coe_inf, Scheme.Hom.coe_image]
  exact inter_image_subset_closure (ch y y' ι τ).continuous (P0 y U y' ι).isOpen (subset_closure_U2'
    y U m a ha hU₁)

variable
  (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
    u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
    p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
      pullback.snd y y →
    q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1
      ≫ m.1 →
    p.1 ≫ m.1 = q.1 ≫ m.1)
  (htr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ Y) (_ : x ≫ y = t)
      (w : T ⟶ (U : Scheme.{u})),
    w ≫ U.ι ≫ pullback.fst y y = t ≫ a → w ≫ U.ι ≫ pullback.snd y y = x → x ≫ τ.1 = w ≫ m.1 ≫ ι.1)

include hassoc htr in
theorem agree01 :
    (pullback y' y').homOfLE (W01_le_P0 y U m a ha y' ι τ) ≫ f0 y U m y' ι =
      (pullback y' y').homOfLE (W01_le_P1 y U m a ha y' ι τ) ≫ f1 y U m y' ι τ := by
  set W := W01 y U m a ha y' ι τ
  set u₀ : (W : Scheme.{u}) ⟶ U := (pullback y' y').homOfLE (W01_le_P0 y U m a ha y' ι τ) ≫ (e0 y U
    y' ι).inv
  set u₁ : (W : Scheme.{u}) ⟶ U := (pullback y' y').homOfLE (W01_le_P1 y U m a ha y' ι τ) ≫ (e1 y U
    y' ι τ).inv
  have hu₀ : u₀ ≫ U.ι ≫ ch y y' ι ι = W.ι := by rw [Category.assoc, e0_inv_ι, Scheme.homOfLE_ι]
  have hu₁ : u₁ ≫ U.ι ≫ ch y y' τ ι = W.ι := by rw [Category.assoc, e1_inv_ι, Scheme.homOfLE_ι]
  have h1 : u₀ ≫ U.ι ≫ pullback.fst y y ≫ ι.1 = u₁ ≫ U.ι ≫ pullback.fst y y ≫ τ.1 := by
    have := congrArg (· ≫ pullback.fst y' y') (hu₀.trans hu₁.symm)
    simpa only [Category.assoc, ch_fst] using this
  have h2 : u₀ ≫ U.ι ≫ pullback.snd y y = u₁ ≫ U.ι ≫ pullback.snd y y := by
    have := congrArg (· ≫ pullback.snd y' y') (hu₀.trans hu₁.symm)
    simp only [Category.assoc, ch_snd] at this
    simpa only [← Category.assoc, cancel_mono] using this
  have hW : Set.range (u₁ ≫ U.ι).base ⊆ (U01 y U m a ha : Set ↑(pullback y y)) := by
    rintro _ ⟨w, rfl⟩
    have hw : W.ι.base w ∈ ((ch y y' τ ι ''ᵁ U01 y U m a ha : (pullback y' y').Opens) : Set _) :=
      w.2.2
    rw [Scheme.Hom.coe_image] at hw
    obtain ⟨q, hq, hqw⟩ := hw
    rw [← hu₁, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hqw
    rw [Scheme.Hom.comp_apply, ← (ch y y' τ ι).isOpenEmbedding.injective hqw]
    exact hq
  have hra : Set.range ((u₁ ≫ U.ι ≫ pullback.fst y y) ≫ jA y a ha).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    have := (hW ⟨w, rfl⟩).1
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  have hrq : Set.range ((u₁ ≫ m.1) ≫ jA y a ha).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    have h := (hW ⟨w, rfl⟩).2
    have h' : (U.ι.base (u₁.base w)) ∈ ((U.ι ''ᵁ (m.1 ⁻¹ᵁ Ub y U a ha) : (pullback y y).Opens) : Set
      _) := by
      simpa only [Scheme.Hom.comp_apply] using h
    rw [Scheme.Hom.coe_image] at h'
    obtain ⟨u, hu, huw⟩ := h'
    have hu' : u = u₁.base w := U.ι.isOpenEmbedding.injective huw
    subst hu'
    exact hu
  obtain ⟨wa, hwa⟩ : ∃ wa : (W : Scheme.{u}) ⟶ U, wa ≫ U.ι = (u₁ ≫ U.ι ≫ pullback.fst y y) ≫ jA y a
    ha :=
    ⟨IsOpenImmersion.lift U.ι _ hra, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨wq, hwq⟩ : ∃ wq : (W : Scheme.{u}) ⟶ U, wq ≫ U.ι = (u₁ ≫ m.1) ≫ jA y a ha :=
    ⟨IsOpenImmersion.lift U.ι _ hrq, IsOpenImmersion.lift_fac _ _ _⟩
  have key := core01 y U m a ha ι τ hassoc htr (u₁ ≫ U.ι ≫ pullback.fst y y ≫ y) u₀ u₁ wa wq rfl h1
    h2 hwa hwq
  change u₀ ≫ m.1 ≫ ι.1 = u₁ ≫ m.1 ≫ τ.1 at key
  simp only [f0, f1, u₀, u₁, Category.assoc] at key ⊢
  exact key

include hassoc htr in
theorem agree02 :
    (pullback y' y').homOfLE (W02_le_P0 y U m a ha y' ι τ) ≫ f0 y U m y' ι =
      (pullback y' y').homOfLE (W02_le_P2 y U m a ha y' ι τ) ≫ f2 y U m a ha y' ι τ := by
  set W := W02 y U m a ha y' ι τ
  set u₀ : (W : Scheme.{u}) ⟶ U := (pullback y' y').homOfLE (W02_le_P0 y U m a ha y' ι τ) ≫ (e0 y U
    y' ι).inv
  set p₂ : (W : Scheme.{u}) ⟶ V2 y U m a ha :=
    (pullback y' y').homOfLE (W02_le_P2 y U m a ha y' ι τ) ≫ (e2 y U m a ha y' ι τ).inv ≫ (eV y U m
      a ha).inv
  set ub : (W : Scheme.{u}) ⟶ U := p₂ ≫ (V2 y U m a ha).ι ≫ bY y U a ha ≫ la y U a ha
  set v : (W : Scheme.{u}) ⟶ U := p₂ ≫ θ y U m a ha
  have hu₀ : u₀ ≫ U.ι ≫ ch y y' ι ι = W.ι := by rw [Category.assoc, e0_inv_ι, Scheme.homOfLE_ι]
  have hp₂ : p₂ ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ ch y y' ι τ = W.ι := by
    rw [Category.assoc, Category.assoc, eV_inv_ι_assoc, e2_inv_ι, Scheme.homOfLE_ι]
  have hubι : ub ≫ U.ι = (p₂ ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ pullback.fst y y) ≫ kA y a ha
    := by
    simp only [ub, Category.assoc, la_ι, bY_ι_assoc]
  have hub₁ : ub ≫ U.ι ≫ pullback.fst y y = p₂ ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ pullback.fst
    y y := by
    rw [reassoc_of% hubι, kA_fst, Category.comp_id]
  set t : (W : Scheme.{u}) ⟶ Spec (CommRingCat.of R) := p₂ ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫
    pullback.fst y y ≫ y
  have ht : ub ≫ U.ι ≫ pullback.fst y y ≫ y = t := by rw [reassoc_of% hub₁]
  have hub₂ : ub ≫ U.ι ≫ pullback.snd y y = t ≫ a := by
    rw [reassoc_of% hubι, kA_snd]; simp only [t, Category.assoc]
  have hv₁ : v ≫ U.ι ≫ pullback.fst y y = ub ≫ m.1 := by
    simp only [v, ub, Category.assoc, θ_ι_assoc, Θ_fst, rho]
  have hv₂ : v ≫ U.ι ≫ pullback.snd y y = p₂ ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ pullback.snd y
    y := by
    simp only [v, Category.assoc, θ_ι_assoc, Θ_snd]
  have h1 : u₀ ≫ U.ι ≫ pullback.fst y y = ub ≫ U.ι ≫ pullback.fst y y := by
    have := congrArg (· ≫ pullback.fst y' y') (hu₀.trans hp₂.symm)
    simp only [Category.assoc, ch_fst] at this
    rw [hub₁]
    simpa only [← Category.assoc, cancel_mono] using this
  have h2 : u₀ ≫ U.ι ≫ pullback.snd y y ≫ ι.1 = (v ≫ U.ι ≫ pullback.snd y y) ≫ τ.1 := by
    have := congrArg (· ≫ pullback.snd y' y') (hu₀.trans hp₂.symm)
    simp only [Category.assoc, ch_snd] at this
    rw [this, hv₂]; simp only [Category.assoc]
  have hW : Set.range (p₂ ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι).base ⊆ (U2' y U m a ha : Set
    ↑(pullback y y)) := by
    rintro _ ⟨w, rfl⟩
    have hw : W.ι.base w ∈ ((ch y y' ι τ ''ᵁ U2' y U m a ha : (pullback y' y').Opens) : Set _) :=
      w.2.2
    rw [Scheme.Hom.coe_image] at hw
    obtain ⟨q, hq, hqw⟩ := hw
    rw [← hp₂, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hqw
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← (ch y y' ι τ).isOpenEmbedding.injective hqw]
    exact hq
  have hrd : Set.range ((v ≫ U.ι ≫ pullback.snd y y) ≫ jA y a ha).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι, hv₂]
    rintro _ ⟨w, rfl⟩
    have := (hW ⟨w, rfl⟩).2
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  obtain ⟨wd, hwd⟩ : ∃ wd : (W : Scheme.{u}) ⟶ U, wd ≫ U.ι = (v ≫ U.ι ≫ pullback.snd y y) ≫ jA y a
    ha :=
    ⟨IsOpenImmersion.lift U.ι _ hrd, IsOpenImmersion.lift_fac _ _ _⟩
  have key := core02 y U m a ha ι τ hassoc htr t u₀ ub v wd ht hub₂ hv₁ h1 h2 hwd
  have goal : u₀ ≫ m.1 ≫ ι.1 = v ≫ m.1 ≫ ι.1 := by rw [reassoc_of% key]
  simp only [f0, f2, u₀, v, p₂, Category.assoc] at goal ⊢
  exact goal

end Agree

section Law

variable {R : Type u} [CommRing R]
  {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
  (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]

/-- The union of the three multiplication charts. -/
abbrev U' : (pullback y' y').Opens := (P0 y U y' ι ⊔ P1 y U y' ι τ) ⊔ P2 y U m a ha y' ι τ

theorem P0_le : P0 y U y' ι ≤ U' y U m a ha y' ι τ := le_sup_left.trans le_sup_left
theorem P1_le : P1 y U y' ι τ ≤ U' y U m a ha y' ι τ := le_sup_right.trans le_sup_left
theorem P2_le : P2 y U m a ha y' ι τ ≤ U' y U m a ha y' ι τ := le_sup_right

theorem dense_image_ch [Smooth y'] [LocallyOfFiniteType y'] [QuasiCompact y'] [IsNoetherianRing R]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    {S : Set ↑(pullback y y)} (hS : Dense S) : Dense ((ch y y' ι ι) '' S) := by
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian y'
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace y'
  have : IsNoetherian Y' := {}
  have hd : Dense (Set.range ι.1.base) :=
    dense_of_forall_maximal_mem fun p hp => hιd p fun p' h _ => hp p' h
  have hr : Dense (Set.range (ch y y' ι ι)) := by
    rw [range_ch]
    exact (hd.preimage (pullback.fst y' y').isOpenMap).inter_of_isOpen_left
      (hd.preimage (pullback.snd y' y').isOpenMap)
      ((pullback.fst y' y').continuous.isOpen_preimage _ ι.1.isOpenEmbedding.isOpen_range)
  have h1 : Set.range (ch y y' ι ι) ⊆ closure ((ch y y' ι ι) '' S) := by
    rw [← Set.image_univ, ← hS.closure_eq]
    exact image_closure_subset_closure_image (ch y y' ι ι).continuous
  intro z
  exact (closure_minimal h1 isClosed_closure) (hr.closure_eq ▸ Set.mem_univ z)

variable
  (hU₁ : ∀ x : Y,
    Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y))
      ⁻¹'
      (U : Set ↑(pullback y y))))
  (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
    u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
    p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
      pullback.snd y y →
    q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1
      ≫ m.1 →
    p.1 ≫ m.1 = q.1 ≫ m.1)
  (htr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ Y) (_ : x ≫ y = t)
      (w : T ⟶ (U : Scheme.{u})),
    w ≫ U.ι ≫ pullback.fst y y = t ≫ a → w ≫ U.ι ≫ pullback.snd y y = x → x ≫ τ.1 = w ≫ m.1 ≫ ι.1)
  (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)

include hU₁ hassoc htr hιd in
theorem exists_law [IsDomain R] [IsNoetherianRing R] [Smooth y] [IsSeparated y]
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y'] [IsOpenImmersion (Phi y
      U m)] :
    ∃ M : (U' y U m a ha y' ι τ : Scheme.{u}) ⟶ Y',
      (pullback y' y').homOfLE (P0_le y U m a ha y' ι τ) ≫ M = f0 y U m y' ι ∧
      (pullback y' y').homOfLE (P1_le y U m a ha y' ι τ) ≫ M = f1 y U m y' ι τ ∧
      (pullback y' y').homOfLE (P2_le y U m a ha y' ι τ) ≫ M = f2 y U m a ha y' ι τ ∧
      M ≫ y' = (U' y U m a ha y' ι τ).ι ≫ pullback.fst y' y' ≫ y' := by
  have : IsReduced (pullback y' y') :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.fst y' y' ≫ y')
  obtain ⟨M₁, hM₁0, hM₁1, hM₁y⟩ := exists_sup_extension (pullback.fst y' y' ≫ y') y'
    (P0 y U y' ι) (P1 y U y' ι τ) (f0 y U m y' ι) (f1 y U m y' ι τ) (f0_y' y U m y' ι) (f1_y' y U m
      y' ι τ)
    (W01 y U m a ha y' ι τ) (W01_le_P0 y U m a ha y' ι τ) (W01_le_P1 y U m a ha y' ι τ)
    (closure_W01 y U m a ha y' ι τ hU₁) (agree01 y U m a ha y' ι τ hassoc htr)
  have hW : W02 y U m a ha y' ι τ ≤ P0 y U y' ι ⊔ P1 y U y' ι τ := (W02_le_P0 y U m a ha y' ι
    τ).trans le_sup_left
  have hU : Dense (U : Set ↑(pullback y y)) := dense_of_forall_dense_fibre (fun q => (pullback.fst y
    y).base q) _ hU₁
  have hP0 : Dense ((P0 y U y' ι : (pullback y' y').Opens) : Set ↑(pullback y' y')) := by
    rw [P0, Scheme.Hom.coe_image]; exact dense_image_ch y y' ι hιd hU
  have hcl : (((P0 y U y' ι ⊔ P1 y U y' ι τ) ⊓ P2 y U m a ha y' ι τ : (pullback y' y').Opens) : Set
    _) ⊆
      closure (W02 y U m a ha y' ι τ : Set ↑(pullback y' y')) := by
    intro q hq
    have h1 : q ∈ closure (((P0 y U y' ι ⊓ P2 y U m a ha y' ι τ : (pullback y' y').Opens) : Set _))
      := by
      rw [Opens.coe_inf, Set.inter_comm]
      exact (P2 y U m a ha y' ι τ).isOpen.inter_closure ⟨hq.2, hP0.closure_eq ▸ Set.mem_univ q⟩
    exact (closure_minimal (closure_W02 y U m a ha y' ι τ hU₁) isClosed_closure) h1
  have hagree : (pullback y' y').homOfLE hW ≫ M₁ =
      (pullback y' y').homOfLE (W02_le_P2 y U m a ha y' ι τ) ≫ f2 y U m a ha y' ι τ := by
    rw [← agree02 y U m a ha y' ι τ hassoc htr, ← hM₁0, ← Category.assoc, Scheme.homOfLE_homOfLE]
  obtain ⟨M, hM01, hM2, hMy⟩ := exists_sup_extension (pullback.fst y' y' ≫ y') y'
    (P0 y U y' ι ⊔ P1 y U y' ι τ) (P2 y U m a ha y' ι τ) M₁ (f2 y U m a ha y' ι τ) hM₁y (f2_y' y U m
      a ha y' ι τ)
    (W02 y U m a ha y' ι τ) hW (W02_le_P2 y U m a ha y' ι τ) hcl hagree
  refine ⟨M, ?_, ?_, hM2, hMy⟩
  · rw [← hM₁0, ← hM01, ← Category.assoc, Scheme.homOfLE_homOfLE]
  · rw [← hM₁1, ← hM01, ← Category.assoc, Scheme.homOfLE_homOfLE]

end Law

section Clauses

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
  (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]
  (M : (U' y U m a ha y' ι τ : Scheme.{u}) ⟶ Y')
  (hM0 : (pullback y' y').homOfLE (P0_le y U m a ha y' ι τ) ≫ M = f0 y U m y' ι)
  (hM1 : (pullback y' y').homOfLE (P1_le y U m a ha y' ι τ) ≫ M = f1 y U m y' ι τ)
  (hM2 : (pullback y' y').homOfLE (P2_le y U m a ha y' ι τ) ≫ M = f2 y U m a ha y' ι τ)

include hM0 in
theorem clause0 {T : Scheme.{u}} (w : T ⟶ (U : Scheme.{u})) :
    ∃ w' : T ⟶ (U' y U m a ha y' ι τ : Scheme.{u}), w' ≫ (U' y U m a ha y' ι τ).ι = w ≫ U.ι ≫ ch y
      y' ι ι ∧ w' ≫ M = w ≫ m.1 ≫ ι.1 := by
  refine ⟨w ≫ (e0 y U y' ι).hom ≫ (pullback y' y').homOfLE (P0_le y U m a ha y' ι τ), ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, Scheme.homOfLE_ι, e0_hom_ι]
  · rw [Category.assoc, Category.assoc, hM0, f0, Iso.hom_inv_id_assoc]

include hM1 in
theorem clause1 {T : Scheme.{u}} (w : T ⟶ (U : Scheme.{u})) :
    ∃ w' : T ⟶ (U' y U m a ha y' ι τ : Scheme.{u}), w' ≫ (U' y U m a ha y' ι τ).ι = w ≫ U.ι ≫ ch y
      y' τ ι ∧ w' ≫ M = w ≫ m.1 ≫ τ.1 := by
  refine ⟨w ≫ (e1 y U y' ι τ).hom ≫ (pullback y' y').homOfLE (P1_le y U m a ha y' ι τ), ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, Scheme.homOfLE_ι, e1_hom_ι]
  · rw [Category.assoc, Category.assoc, hM1, f1, Iso.hom_inv_id_assoc]

include hM2 in
theorem clause2 {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (d : T ⟶ Y) (hd : d ≫ y = t)
    (u v : T ⟶ (U : Scheme.{u})) (hut : u ≫ U.ι ≫ pullback.fst y y ≫ y = t)
    (hu : u ≫ U.ι ≫ pullback.snd y y = t ≫ a) (hv₁ : v ≫ U.ι ≫ pullback.fst y y = u ≫ m.1)
    (hv₂ : v ≫ U.ι ≫ pullback.snd y y = d) :
    ∃ w' : T ⟶ (U' y U m a ha y' ι τ : Scheme.{u}),
      w' ≫ (U' y U m a ha y' ι τ).ι = pullback.lift (u ≫ U.ι ≫ pullback.fst y y) d
        (by rw [Category.assoc, Category.assoc, hut, hd]) ≫ ch y y' ι τ ∧ w' ≫ M = v ≫ m.1 ≫ ι.1 :=
          by
  obtain ⟨b, hb⟩ : ∃ b : T ⟶ Y, b = u ≫ U.ι ≫ pullback.fst y y := ⟨_, rfl⟩
  have hbk : b ≫ kA y a ha = u ≫ U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, kA_fst, Category.comp_id, hb, Category.assoc]
    · rw [Category.assoc, kA_snd, Category.assoc, hu, hb]
      simp only [Category.assoc]
      rw [reassoc_of% hut]
  have hbr : Set.range b.base ⊆ Set.range (Ua y U a ha).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change (kA y a ha).base (b.base z) ∈ U
    rw [← Scheme.Hom.comp_apply, hbk, Scheme.Hom.comp_apply]
    exact (u.base z).2
  set b' : T ⟶ Ua y U a ha := IsOpenImmersion.lift (Ua y U a ha).ι b hbr
  have hb' : b' ≫ (Ua y U a ha).ι = b := IsOpenImmersion.lift_fac _ _ _
  have hbla : b' ≫ la y U a ha = u := by
    rw [← cancel_mono U.ι, Category.assoc, la_ι, reassoc_of% hb', hbk]
  set q : T ⟶ pullback y y := pullback.lift b d (by rw [hb, Category.assoc, Category.assoc, hut,
    hd])
  have hqr : Set.range q.base ⊆ Set.range (Ya y U a ha).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change (pullback.fst y y).base (q.base z) ∈ Ua y U a ha
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, ← hb', Scheme.Hom.comp_apply]
    exact (b'.base z).2
  set qY : T ⟶ Ya y U a ha := IsOpenImmersion.lift (Ya y U a ha).ι q hqr
  have hqY : qY ≫ (Ya y U a ha).ι = q := IsOpenImmersion.lift_fac _ _ _
  have hqYb : qY ≫ bY y U a ha = b' := by
    rw [← cancel_mono (Ua y U a ha).ι, Category.assoc, bY_ι, reassoc_of% hqY, pullback.lift_fst,
      hb']
  have hqΘ : qY ≫ Θ y U m a ha = v ≫ U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, Θ_fst, reassoc_of% hqYb, rho, reassoc_of% hbla, Category.assoc, hv₁]
    · rw [Category.assoc, Θ_snd, reassoc_of% hqY, pullback.lift_snd, Category.assoc, hv₂]
  have hqVr : Set.range qY.base ⊆ Set.range (V2 y U m a ha).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change (Θ y U m a ha).base (qY.base z) ∈ U
    rw [← Scheme.Hom.comp_apply, hqΘ, Scheme.Hom.comp_apply]
    exact (v.base z).2
  set qV : T ⟶ V2 y U m a ha := IsOpenImmersion.lift (V2 y U m a ha).ι qY hqVr
  have hqV : qV ≫ (V2 y U m a ha).ι = qY := IsOpenImmersion.lift_fac _ _ _
  have hqθ : qV ≫ θ y U m a ha = v := by
    rw [← cancel_mono U.ι, Category.assoc, θ_ι, reassoc_of% hqV, hqΘ]
  refine ⟨qV ≫ (eV y U m a ha).hom ≫ (e2 y U m a ha y' ι τ).hom ≫ (pullback y' y').homOfLE (P2_le y
    U m a ha y' ι τ), ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, Category.assoc, Scheme.homOfLE_ι, e2_hom_ι, eV_hom_ι_assoc,
      reassoc_of% hqV, reassoc_of% hqY]
    subst hb; rfl
  · rw [Category.assoc, Category.assoc, Category.assoc, hM2, f2, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id_assoc,
      reassoc_of% hqθ]

variable (M' : SchemeHomOver ((U' y U m a ha y' ι τ).ι ≫ pullback.fst y' y' ≫ y') y') (hM' : M'.1 =
    M)

theorem res_fac (P : (pullback y' y').Opens) (hP : P ≤ U' y U m a ha y' ι τ) :
    ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P).ι = ((U' y U m a ha y' ι τ).ι ∣_ P) ≫ (pullback y' y').homOfLE
      hP := by
  rw [← cancel_mono (U' y U m a ha y' ι τ).ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]

/-- The three-chart open cover of the glued multiplication domain. -/
def cov : Option Bool → (U' y U m a ha y' ι τ : Scheme.{u}).Opens
  | some true => (U' y U m a ha y' ι τ).ι ⁻¹ᵁ P0 y U y' ι
  | some false => (U' y U m a ha y' ι τ).ι ⁻¹ᵁ P1 y U y' ι τ
  | none => (U' y U m a ha y' ι τ).ι ⁻¹ᵁ P2 y U m a ha y' ι τ

theorem iSup_eq_top : (⨆ i, cov y U m a ha y' ι τ i) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rcases x.2 with (hx | hx) | hx
  · exact Opens.mem_iSup.mpr ⟨some true, hx⟩
  · exact Opens.mem_iSup.mpr ⟨some false, hx⟩
  · exact Opens.mem_iSup.mpr ⟨none, hx⟩

include hM0 hM1 hM2 hM' in
theorem locallyQuasiFinite_Phi' [IsOpenImmersion (Phi y U m)] [IsOpenImmersion (Psi y U m)] :
    LocallyQuasiFinite (pullback.lift (f := y') (g := y') ((U' y U m a ha y' ι τ).ι ≫ pullback.fst
      y' y') M'.1
      ((Category.assoc _ _ _).trans M'.2.symm)) := by
  set Φ' := pullback.lift (f := y') (g := y') ((U' y U m a ha y' ι τ).ι ≫ pullback.fst y' y') M'.1
      ((Category.assoc _ _ _).trans M'.2.symm)
  have : IsZariskiLocalAtSource (@LocallyQuasiFinite.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyQuasiFinite.{u}) (Q := RingHom.QuasiFinite)
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @LocallyQuasiFinite.{u}) _ (iSup_eq_top y U m a ha y' ι τ) ?_
  rintro (_ | _ | _)
  · change LocallyQuasiFinite (((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P2 y U m a ha y' ι τ).ι ≫ Φ')
    have : IsOpenImmersion (Θ y U m a ha) := isOpenImmersion_Θ y U m a ha
    have hθ : IsOpenImmersion (θ y U m a ha) := inferInstanceAs (IsOpenImmersion (Θ y U m a ha ∣_
      U))
    obtain ⟨φ₂, hφ₁, hφ₂⟩ : ∃ φ₂ : (V2 y U m a ha : Scheme.{u}) ⟶ pullback y y,
        φ₂ ≫ pullback.fst y y = (V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ pullback.fst y y ∧
        φ₂ ≫ pullback.snd y y = θ y U m a ha ≫ m.1 :=
      ⟨pullback.lift ((V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ pullback.fst y y) (θ y U m a ha ≫ m.1)
        (by simp only [Category.assoc]; rw [m.2, θ_ι_assoc, Θ_fst_y]),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hφr : Set.range φ₂.base ⊆ Set.range (Ya y U a ha).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      change (pullback.fst y y).base (φ₂.base z) ∈ Ua y U a ha
      rw [← Scheme.Hom.comp_apply, hφ₁]
      exact ((V2 y U m a ha).ι.base z).2
    let φ₂' : (V2 y U m a ha : Scheme.{u}) ⟶ Ya y U a ha := IsOpenImmersion.lift (Ya y U a ha).ι φ₂
      hφr
    have hφ₂' : φ₂' ≫ (Ya y U a ha).ι = φ₂ := IsOpenImmersion.lift_fac _ _ _
    have hφb : φ₂' ≫ bY y U a ha = (V2 y U m a ha).ι ≫ bY y U a ha := by
      rw [← cancel_mono (Ua y U a ha).ι, Category.assoc, Category.assoc, bY_ι, reassoc_of% hφ₂',
        hφ₁]
    have hφΘ : φ₂' ≫ Θ y U m a ha = θ y U m a ha ≫ Phi y U m := by
      apply pullback.hom_ext
      · rw [Category.assoc, Θ_fst, reassoc_of% hφb, Category.assoc, pullback.lift_fst, θ_ι_assoc,
        Θ_fst]
      · rw [Category.assoc, Θ_snd, reassoc_of% hφ₂', hφ₂, Category.assoc, pullback.lift_snd]
    have : LocallyQuasiFinite (θ y U m a ha ≫ Phi y U m) := inferInstance
    have : LocallyQuasiFinite (φ₂' ≫ Θ y U m a ha) := by rw [hφΘ]; infer_instance
    have : LocallyQuasiFinite φ₂' := LocallyQuasiFinite.of_comp φ₂' (Θ y U m a ha)
    have : LocallyQuasiFinite φ₂ := by rw [← hφ₂']; infer_instance
    have h : ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P2 y U m a ha y' ι τ).ι ≫ Φ' =
        ((U' y U m a ha y' ι τ).ι ∣_ P2 y U m a ha y' ι τ) ≫ (e2 y U m a ha y' ι τ).inv ≫ (eV y U m
          a ha).inv ≫ φ₂ ≫ ch y y' ι ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, reassoc_of% (res_fac y U m a ha y' ι τ _ (P2_le y U m
        a ha y' ι τ)),
          Scheme.homOfLE_ι_assoc]
        simp only [Category.assoc, ch_fst, reassoc_of% hφ₁]
        rw [← e2_inv_ι_assoc, ch_fst, ← eV_inv_ι_assoc]
      · rw [Category.assoc, pullback.lift_snd, res_fac y U m a ha y' ι τ _ (P2_le y U m a ha y' ι
        τ), Category.assoc,
          hM', hM2, f2]
        simp only [Category.assoc, ch_snd, reassoc_of% hφ₂]
    rw [h]; infer_instance
  · change LocallyQuasiFinite (((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P1 y U y' ι τ).ι ≫ Φ')
    have h : ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P1 y U y' ι τ).ι ≫ Φ' =
        ((U' y U m a ha y' ι τ).ι ∣_ P1 y U y' ι τ) ≫ (e1 y U y' ι τ).inv ≫ Phi y U m ≫ ch y y' τ τ
          := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, reassoc_of% (res_fac y U m a ha y' ι τ _ (P1_le y U m
        a ha y' ι τ)),
          Scheme.homOfLE_ι_assoc]
        simp only [Category.assoc, ch_fst, pullback.lift_fst_assoc]
        rw [← e1_inv_ι_assoc, ch_fst]
      · rw [Category.assoc, pullback.lift_snd, res_fac y U m a ha y' ι τ _ (P1_le y U m a ha y' ι
        τ), Category.assoc,
          hM', hM1, f1]
        simp only [Category.assoc, ch_snd, pullback.lift_snd_assoc]
    rw [h]; infer_instance
  · change LocallyQuasiFinite (((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P0 y U y' ι).ι ≫ Φ')
    have h : ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P0 y U y' ι).ι ≫ Φ' =
        ((U' y U m a ha y' ι τ).ι ∣_ P0 y U y' ι) ≫ (e0 y U y' ι).inv ≫ Phi y U m ≫ ch y y' ι ι :=
          by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, reassoc_of% (res_fac y U m a ha y' ι τ _ (P0_le y U m
        a ha y' ι τ)),
          Scheme.homOfLE_ι_assoc]
        simp only [Category.assoc, ch_fst, pullback.lift_fst_assoc]
        rw [← e0_inv_ι_assoc, ch_fst]
      · rw [Category.assoc, pullback.lift_snd, res_fac y U m a ha y' ι τ _ (P0_le y U m a ha y' ι
        τ), Category.assoc,
          hM', hM0, f0]
        simp only [Category.assoc, ch_snd, pullback.lift_snd_assoc]
    rw [h]; infer_instance

include hM0 hM1 hM2 hM' in
theorem locallyQuasiFinite_Psi' [IsOpenImmersion (Phi y U m)] [IsOpenImmersion (Psi y U m)] :
    LocallyQuasiFinite (pullback.lift (f := y') (g := y') M'.1 ((U' y U m a ha y' ι τ).ι ≫
      pullback.snd y' y')
      (M'.2.trans (by rw [Category.assoc, pullback.condition]))) := by
  set Ψ' := pullback.lift (f := y') (g := y') M'.1 ((U' y U m a ha y' ι τ).ι ≫ pullback.snd y' y')
      (M'.2.trans (by rw [Category.assoc, pullback.condition]))
  have : IsZariskiLocalAtSource (@LocallyQuasiFinite.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyQuasiFinite.{u}) (Q := RingHom.QuasiFinite)
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @LocallyQuasiFinite.{u}) _ (iSup_eq_top y U m a ha y' ι τ) ?_
  rintro (_ | _ | _)
  · change LocallyQuasiFinite (((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P2 y U m a ha y' ι τ).ι ≫ Ψ')
    have : IsOpenImmersion (Θ y U m a ha) := isOpenImmersion_Θ y U m a ha
    have h : ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P2 y U m a ha y' ι τ).ι ≫ Ψ' =
        ((U' y U m a ha y' ι τ).ι ∣_ P2 y U m a ha y' ι τ) ≫ (e2 y U m a ha y' ι τ).inv ≫ (eV y U m
          a ha).inv ≫
          θ y U m a ha ≫ Psi y U m ≫ ch y y' ι τ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, res_fac y U m a ha y' ι τ _ (P2_le y U m a ha y' ι
        τ), Category.assoc,
          hM', hM2, f2]
        simp only [Category.assoc, ch_fst, pullback.lift_fst_assoc]
      · rw [Category.assoc, pullback.lift_snd, reassoc_of% (res_fac y U m a ha y' ι τ _ (P2_le y U m
        a ha y' ι τ)),
          Scheme.homOfLE_ι_assoc]
        simp only [Category.assoc, ch_snd, pullback.lift_snd_assoc]
        rw [← e2_inv_ι_assoc, ch_snd, ← eV_inv_ι_assoc, θ_ι_assoc, Θ_snd_assoc]
    have hθ : IsOpenImmersion (θ y U m a ha) := inferInstanceAs (IsOpenImmersion (Θ y U m a ha ∣_
      U))
    rw [h]; infer_instance
  · change LocallyQuasiFinite (((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P1 y U y' ι τ).ι ≫ Ψ')
    have h : ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P1 y U y' ι τ).ι ≫ Ψ' =
        ((U' y U m a ha y' ι τ).ι ∣_ P1 y U y' ι τ) ≫ (e1 y U y' ι τ).inv ≫ Psi y U m ≫ ch y y' τ ι
          := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, res_fac y U m a ha y' ι τ _ (P1_le y U m a ha y' ι
        τ), Category.assoc,
          hM', hM1, f1]
        simp only [Category.assoc, ch_fst, pullback.lift_fst_assoc]
      · rw [Category.assoc, pullback.lift_snd, reassoc_of% (res_fac y U m a ha y' ι τ _ (P1_le y U m
        a ha y' ι τ)),
          Scheme.homOfLE_ι_assoc]
        simp only [Category.assoc, ch_snd, pullback.lift_snd_assoc]
        rw [← e1_inv_ι_assoc, ch_snd]
    rw [h]; infer_instance
  · change LocallyQuasiFinite (((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P0 y U y' ι).ι ≫ Ψ')
    have h : ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P0 y U y' ι).ι ≫ Ψ' =
        ((U' y U m a ha y' ι τ).ι ∣_ P0 y U y' ι) ≫ (e0 y U y' ι).inv ≫ Psi y U m ≫ ch y y' ι ι :=
          by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, res_fac y U m a ha y' ι τ _ (P0_le y U m a ha y' ι
        τ), Category.assoc,
          hM', hM0, f0]
        simp only [Category.assoc, ch_fst, pullback.lift_fst_assoc]
      · rw [Category.assoc, pullback.lift_snd, reassoc_of% (res_fac y U m a ha y' ι τ _ (P0_le y U m
        a ha y' ι τ)),
          Scheme.homOfLE_ι_assoc]
        simp only [Category.assoc, ch_snd, pullback.lift_snd_assoc]
        rw [← e0_inv_ι_assoc, ch_snd]
    rw [h]; infer_instance

end Clauses

end TranslationGluing
end AbelianVarieties.NOSProofs.QuasiFiniteTranslationGluing

open AbelianVarieties.NOSProofs.QuasiFiniteTranslationGluing.TranslationGluing

namespace NeronModelInfra

theorem exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
        pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y =
        v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y) [IsClosedImmersion γ]
    (hΓ : Set.range γ.base =
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1
        m.2.symm).base))
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    (hΓa : pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.fst y y ≫ τ.1 =
          pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.snd y y ≫ ι.1) :
    ∃ (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'),
      LocallyQuasiFinite
          (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      LocallyQuasiFinite
          (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst
        y y ≫ y)),
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
          w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst
        y y ≫ y)),
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ τ.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
          w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ τ.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (d : SchemeHomOver t y)
          (u v : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        u.1 ≫ U.ι ≫ pullback.snd y y = t ≫ a →
        v.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → v.1 ≫ U.ι ≫ pullback.snd y y = d.1 →
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = d.1 ≫ τ.1 ∧
          w'.1 ≫ m'.1 = v.1 ≫ m.1 ≫ ι.1) := by
  have : IsOpenImmersion (Phi y U m) := hΦ
  have : IsOpenImmersion (Psi y U m) := hΨ
  have : IsReduced (U : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (U.ι ≫ pullback.fst y y ≫
      y)
  have hgr : Set.range (grm y U m).base ⊆ Set.range γ.base := hΓ ▸ subset_closure
  obtain ⟨g₀, hg₀⟩ := exists_lift_of_isClosedImmersion (grm y U m) γ hgr
  have htr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ Y) (_ : x ≫ y = t)
      (w : T ⟶ (U : Scheme.{u})),
      w ≫ U.ι ≫ pullback.fst y y = t ≫ a → w ≫ U.ι ≫ pullback.snd y y = x → x ≫ τ.1 = w ≫ m.1 ≫ ι.1
        :=
    fun t x hx w hw₁ hw₂ => translate y U m a ha γ g₀ hg₀ ι τ hΓa t x hx w hw₁ hw₂
  obtain ⟨M, hM0, hM1, hM2, hMy⟩ := exists_law y U m a ha y' ι τ hU₁ hassoc htr hιd
  let m' : SchemeHomOver ((U' y U m a ha y' ι τ).ι ≫ pullback.fst y' y' ≫ y') y' := ⟨M, hMy⟩
  refine ⟨U' y U m a ha y' ι τ, m', locallyQuasiFinite_Phi' y U m a ha y' ι τ M hM0 hM1 hM2 m' rfl,
    locallyQuasiFinite_Psi' y U m a ha y' ι τ M hM0 hM1 hM2 m' rfl, ?_, ?_, ?_⟩
  · intro T t w
    obtain ⟨w', hw', hw'M⟩ := clause0 y U m a ha y' ι τ M hM0 w.1
    refine ⟨⟨w', ?_⟩, ?_, ?_, hw'M⟩
    · rw [reassoc_of% hw', ch_fst_assoc, ι.2, w.2]
    · change w' ≫ _ = _; rw [reassoc_of% hw', ch_fst]
    · change w' ≫ _ = _; rw [reassoc_of% hw', ch_snd]
  · intro T t w
    obtain ⟨w', hw', hw'M⟩ := clause1 y U m a ha y' ι τ M hM1 w.1
    refine ⟨⟨w', ?_⟩, ?_, ?_, hw'M⟩
    · rw [reassoc_of% hw', ch_fst_assoc, τ.2, w.2]
    · change w' ≫ _ = _; rw [reassoc_of% hw', ch_fst]
    · change w' ≫ _ = _; rw [reassoc_of% hw', ch_snd]
  · intro T t d u v hu hv₁ hv₂
    obtain ⟨w', hw', hw'M⟩ := clause2 y U m a ha y' ι τ M hM2 t d.1 d.2 u.1 v.1 u.2 hu hv₁ hv₂
    refine ⟨⟨w', ?_⟩, ?_, ?_, hw'M⟩
    · rw [reassoc_of% hw', ch_fst_assoc, ι.2, pullback.lift_fst_assoc, Category.assoc,
      Category.assoc, u.2]
    · change w' ≫ _ = _; rw [reassoc_of% hw', ch_fst, pullback.lift_fst_assoc, Category.assoc,
      Category.assoc]
    · change w' ≫ _ = _; rw [reassoc_of% hw', ch_snd, pullback.lift_snd_assoc]

end NeronModelInfra

end
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
    TopologicalSpace Topology

universe u

open AbelianVarieties.NOSProofs.GluingFibreDensity.TranslationCharts
  (Phi Psi ch ch_fst ch_snd ch_fst_assoc ch_snd_assoc range_ch)
open scoped AbelianVarieties.NOSProofs.GluingFibreDensity.TranslationCharts
open AbelianVarieties.NOSProofs.GraphClosureRigidity.GraphClosure
  (dense_of_forall_dense_fibre)
open AbelianVarieties.NOSProofs.GluingFibreDensity.TranslationCharts (dense_of_forall_maximal_mem)

namespace AbelianVarieties.NOSProofs.QuasiFiniteLawExtension

namespace LawExtension

open AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication
  (A DD FF GG M_y Q12 Q12_snd Q12_snd_assoc Q23 dF dF_ι dF_ι_assoc dG dG_ι dG_ι_assoc fst_y mem_A
    mulFst mulFst_fst mulFst_fst_assoc mulFst_snd mulSnd mulSnd_fst mulSnd_fst_assoc mulSnd_snd
    range_A_mulFst range_A_mulSnd)

section Topology

theorem dense_image_of_denseRange {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {f : X →
    Z}
    (hf : Continuous f) (hr : DenseRange f) {S : Set X} (hS : Dense S) : Dense (f '' S) :=
  hr.dense_image hf hS

end Topology

section Charts

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R)) (i₁ i₂ : SchemeHomOver y y')

theorem dense_range_ch [Smooth y'] [LocallyOfFiniteType y'] [QuasiCompact y'] [IsNoetherianRing R]
    (ι : SchemeHomOver y y') [IsOpenImmersion ι.1]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
      :
    Dense (Set.range (ch y y' ι ι)) := by
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian y'
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace y'
  have : IsNoetherian Y' := {}
  have hd : Dense (Set.range ι.1.base) :=
    dense_of_forall_maximal_mem fun p hp => hιd p fun p' h _ => hp p' h
  rw [range_ch]
  exact (hd.preimage (pullback.fst y' y').isOpenMap).inter_of_isOpen_left
    (hd.preimage (pullback.snd y' y').isOpenMap) ((pullback.fst y' y').continuous.isOpen_preimage _
      ι.1.isOpenEmbedding.isOpen_range)

theorem dense_image_ch [Smooth y'] [LocallyOfFiniteType y'] [QuasiCompact y'] [IsNoetherianRing R]
    (ι : SchemeHomOver y y') [IsOpenImmersion ι.1]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    {S : Set ↑(pullback y y)} (hS : Dense S) : Dense ((ch y y' ι ι) '' S) := by
  have h1 : Set.range (ch y y' ι ι) ⊆ closure ((ch y y' ι ι) '' S) := by
    rw [← Set.image_univ, ← hS.closure_eq]
    exact image_closure_subset_closure_image (ch y y' ι ι).continuous
  intro z
  have := (dense_range_ch y y' ι hιd).closure_eq
  have h2 : closure (Set.range (ch y y' ι ι)) ⊆ closure ((ch y y' ι ι) '' S) :=
    closure_minimal h1 isClosed_closure
  exact h2 (this ▸ Set.mem_univ z)

end Charts

section Assoc

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (D : (pullback y y).Opens) (M : SchemeHomOver (D.ι ≫ pullback.fst y y ≫ y) y)

/-- The auxiliary product with the first composable pair still unmultiplied. -/
abbrev A0 : Scheme.{u} := pullback (D.ι ≫ pullback.snd y y) (pullback.fst y y)

/-- The auxiliary product after multiplying the first pair. -/
abbrev B0 : Scheme.{u} := pullback M.1 (pullback.fst y y)

@[reassoc]
theorem A0_cond : pullback.fst (D.ι ≫ pullback.snd y y) (pullback.fst y y) ≫ D.ι ≫ pullback.snd y y
    =
    pullback.snd (D.ι ≫ pullback.snd y y) (pullback.fst y y) ≫ pullback.fst y y :=
  pullback.condition

@[reassoc]
theorem B0_cond : pullback.fst M.1 (pullback.fst y y) ≫ M.1 =
    pullback.snd M.1 (pullback.fst y y) ≫ pullback.fst y y :=
  pullback.condition

theorem A0_cond_y : pullback.fst (D.ι ≫ pullback.snd y y) (pullback.fst y y) ≫ M.1 ≫ y =
    pullback.snd (D.ι ≫ pullback.snd y y) (pullback.fst y y) ≫ pullback.snd y y ≫ y := by
  have h : pullback.fst (D.ι ≫ pullback.snd y y) (pullback.fst y y) ≫ D.ι ≫ pullback.snd y y ≫ y =
      pullback.snd (D.ι ≫ pullback.snd y y) (pullback.fst y y) ≫ pullback.fst y y ≫ y := by
    rw [A0_cond_assoc]
  simp only [M_y, fst_y] at h ⊢
  exact h

theorem B0_cond_y : pullback.fst M.1 (pullback.fst y y) ≫ D.ι ≫ pullback.snd y y ≫ y =
    pullback.snd M.1 (pullback.fst y y) ≫ pullback.snd y y ≫ y := by
  have h : pullback.fst M.1 (pullback.fst y y) ≫ M.1 ≫ y =
      pullback.snd M.1 (pullback.fst y y) ≫ pullback.fst y y ≫ y := by
    rw [B0_cond_assoc]
  simp only [M_y, fst_y] at h ⊢
  exact h

/-- Include the second composable pair into the auxiliary product. -/
abbrev i0 : DD y D ⟶ A0 y D :=
  pullback.map _ _ _ _ (𝟙 _) D.ι (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw
    [Category.comp_id])

/-- Multiply the first pair in the auxiliary product. -/
def kA : A0 y D ⟶ B0 y D M :=
  pullback.lift (pullback.fst _ _)
    (pullback.lift (f := y) (g := y) (pullback.fst _ _ ≫ M.1) (pullback.snd _ _ ≫ pullback.snd y y)
      (by simp only [Category.assoc]; exact A0_cond_y y D M))
    (by rw [pullback.lift_fst])

/-- Recover the auxiliary product coordinates after the first multiplication. -/
def kB : B0 y D M ⟶ A0 y D :=
  pullback.lift (pullback.fst _ _)
    (pullback.lift (f := y) (g := y) (pullback.fst _ _ ≫ D.ι ≫ pullback.snd y y)
      (pullback.snd _ _ ≫ pullback.snd y y)
      (by simp only [Category.assoc]; exact B0_cond_y y D M))
    (by rw [pullback.lift_fst])

theorem kA_kB : kA y D M ≫ kB y D M = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [kA, kB, Category.assoc, pullback.lift_fst, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [kA, kB, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc,
        Category.id_comp, A0_cond]
    · simp only [kA, kB, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.id_comp]

theorem kB_kA : kB y D M ≫ kA y D M = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [kA, kB, Category.assoc, pullback.lift_fst, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [kA, kB, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc,
        Category.id_comp, B0_cond]
    · simp only [kA, kB, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.id_comp]

scoped instance : IsIso (kA y D M) := ⟨kB y D M, kA_kB y D M, kB_kA y D M⟩

theorem mulFst_eq : mulFst y D M = i0 y D ≫ kA y D M ≫ pullback.snd M.1 (pullback.fst y y) := by
  apply pullback.hom_ext
  · rw [mulFst_fst, Category.assoc, Category.assoc, ← B0_cond]
    simp only [kA, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [mulFst_snd, Category.assoc, kA, pullback.lift_snd_assoc, pullback.lift_snd]

theorem universallyOpen_mulFst [UniversallyOpen M.1] : UniversallyOpen (mulFst y D M) := by
  rw [mulFst_eq]
  infer_instance

/-- The auxiliary product with the second composable pair still unmultiplied. -/
abbrev A0' : Scheme.{u} := pullback (pullback.snd y y) (D.ι ≫ pullback.fst y y)

/-- The auxiliary product after multiplying the second pair. -/
abbrev B0' : Scheme.{u} := pullback (pullback.snd y y) M.1

@[reassoc]
theorem A0'_cond : pullback.fst (pullback.snd y y) (D.ι ≫ pullback.fst y y) ≫ pullback.snd y y =
    pullback.snd (pullback.snd y y) (D.ι ≫ pullback.fst y y) ≫ D.ι ≫ pullback.fst y y :=
  pullback.condition

@[reassoc]
theorem B0'_cond : pullback.fst (pullback.snd y y) M.1 ≫ pullback.snd y y =
    pullback.snd (pullback.snd y y) M.1 ≫ M.1 :=
  pullback.condition

/-- Include the first composable pair into the auxiliary product. -/
abbrev i0' : DD y D ⟶ A0' y D :=
  pullback.map _ _ _ _ D.ι (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.comp_id,
    Category.id_comp])

/-- Multiply the second pair in the auxiliary product. -/
def kA' : A0' y D ⟶ B0' y D M :=
  pullback.lift
    (pullback.lift (f := y) (g := y) (pullback.fst _ _ ≫ pullback.fst y y) (pullback.snd _ _ ≫ M.1)
      (by simp only [Category.assoc, M_y, fst_y, A0'_cond_assoc]))
    (pullback.snd _ _)
    (by rw [pullback.lift_snd])

/-- Recover the auxiliary product coordinates after the second multiplication. -/
def kB' : B0' y D M ⟶ A0' y D :=
  pullback.lift
    (pullback.lift (f := y) (g := y) (pullback.fst _ _ ≫ pullback.fst y y)
      (pullback.snd _ _ ≫ D.ι ≫ pullback.fst y y)
      (by simp only [Category.assoc, M_y, fst_y, B0'_cond_assoc]))
    (pullback.snd _ _)
    (by rw [pullback.lift_snd])

theorem kA'_kB' : kA' y D M ≫ kB' y D M = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [kA', kB', Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.id_comp]
    · simp only [kA', kB', Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_snd_assoc,
        Category.id_comp, A0'_cond]
  · simp only [kA', kB', Category.assoc, pullback.lift_snd, Category.id_comp]

theorem kB'_kA' : kB' y D M ≫ kA' y D M = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [kA', kB', Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.id_comp]
    · simp only [kA', kB', Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_snd_assoc,
        Category.id_comp, B0'_cond]
  · simp only [kA', kB', Category.assoc, pullback.lift_snd, Category.id_comp]

scoped instance : IsIso (kA' y D M) := ⟨kB' y D M, kA'_kB' y D M, kB'_kA' y D M⟩

theorem mulSnd_eq : mulSnd y D M = i0' y D ≫ kA' y D M ≫ pullback.fst (pullback.snd y y) M.1 := by
  apply pullback.hom_ext
  · simp only [mulSnd_fst, Category.assoc, kA', pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [mulSnd_snd, Category.assoc, Category.assoc, B0'_cond]
    simp only [kA', pullback.lift_snd_assoc, Category.comp_id]

theorem universallyOpen_mulSnd [UniversallyOpen M.1] : UniversallyOpen (mulSnd y D M) := by
  rw [mulSnd_eq]
  infer_instance

variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
variable (hUD : U ≤ D) (hM : (pullback y y).homOfLE hUD ≫ M.1 = m.1)

include hM in
theorem comp_m_eq {T : Scheme.{u}} (w : T ⟶ U) (d : T ⟶ D) (h : w ≫ U.ι = d ≫ D.ι) : w ≫ m.1 = d ≫
    M.1 := by
  rw [← hM, ← Category.assoc]
  congr 1
  rw [← cancel_mono D.ι, Category.assoc, Scheme.homOfLE_ι, h]

/-- The common dense subdomain on which all products lie in the original chart. -/
def L : (A y D M : Scheme.{u}).Opens :=
  ((A y D M).ι ≫ Q12 y D ≫ D.ι) ⁻¹ᵁ U ⊓ ((A y D M).ι ≫ Q23 y D ≫ D.ι) ⁻¹ᵁ U ⊓
    ((A y D M).ι ≫ mulFst y D M) ⁻¹ᵁ U ⊓ ((A y D M).ι ≫ mulSnd y D M) ⁻¹ᵁ U

theorem mem_L (x : ↑(A y D M)) :
    x ∈ L y D M U ↔
      D.ι.base ((Q12 y D).base (((A y D M).ι).base x)) ∈ U ∧
      D.ι.base ((Q23 y D).base (((A y D M).ι).base x)) ∈ U ∧
      (mulFst y D M).base (((A y D M).ι).base x) ∈ U ∧ (mulSnd y D M).base (((A y D M).ι).base x) ∈
        U := by
  simp only [L, TopologicalSpace.Opens.mem_inf, Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply,
    and_assoc]

theorem dense_L [Smooth y] [UniversallyOpen M.1] (hU : Dense (U : Set ↑(pullback y y))) :
    Dense (L y D M U : Set ↑(A y D M)) := by
  have : UniversallyOpen (mulFst y D M) := universallyOpen_mulFst y D M
  have : UniversallyOpen (mulSnd y D M) := universallyOpen_mulSnd y D M
  have h1 : Dense (((A y D M).ι ≫ Q12 y D ≫ D.ι) ⁻¹ᵁ U : Set ↑(A y D M)) :=
    hU.preimage (Scheme.Hom.isOpenMap _)
  have h2 : Dense (((A y D M).ι ≫ Q23 y D ≫ D.ι) ⁻¹ᵁ U : Set ↑(A y D M)) :=
    hU.preimage (Scheme.Hom.isOpenMap _)
  have h3 : Dense (((A y D M).ι ≫ mulFst y D M) ⁻¹ᵁ U : Set ↑(A y D M)) :=
    hU.preimage (Scheme.Hom.isOpenMap _)
  have h4 : Dense (((A y D M).ι ≫ mulSnd y D M) ⁻¹ᵁ U : Set ↑(A y D M)) :=
    hU.preimage (Scheme.Hom.isOpenMap _)
  simp only [L, TopologicalSpace.Opens.coe_inf]
  exact ((h1.inter_of_isOpen_left h2 (TopologicalSpace.Opens.isOpen _)).inter_of_isOpen_right h3
    (TopologicalSpace.Opens.isOpen _)).inter_of_isOpen_right h4 (TopologicalSpace.Opens.isOpen _)

variable (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
        pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y =
        v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)

include hM hassoc in
theorem FF_eq_GG [IsDomain R] [IsDiscreteValuationRing R] [Smooth y] [IsSeparated y]
    [UniversallyOpen M.1]
    (hU : Dense (U : Set ↑(pullback y y))) : FF y D M = GG y D M := by
  have : IsReduced (A y D M : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      ((A y D M).ι ≫ Q12 y D ≫ D.ι ≫ pullback.fst y y ≫ y)
  have : IsDominant (L y D M U).ι := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Opens.range_ι]
    exact dense_L y D M U hU
  refine ext_of_isDominant_of_isSeparated y ?_ (L y D M U).ι ?_
  · simp only [FF, GG, Category.assoc, M_y, dF_ι_assoc, dG_ι_assoc, mulFst_fst_assoc,
    mulSnd_fst_assoc]
  have memL := fun x : ↑(L y D M U) => (mem_L y D M U x.1).mp x.2
  have hrU : Set.range U.ι.base = (U : Set ↑(pullback y y)) := Scheme.Opens.range_ι U
  have hr₁ : Set.range ((L y D M U).ι ≫ (A y D M).ι ≫ Q12 y D ≫ D.ι).base ⊆ Set.range U.ι.base := by
    rw [hrU]; rintro _ ⟨x, rfl⟩
    exact (memL x).1
  have hr₂ : Set.range ((L y D M U).ι ≫ (A y D M).ι ≫ Q23 y D ≫ D.ι).base ⊆ Set.range U.ι.base := by
    rw [hrU]; rintro _ ⟨x, rfl⟩
    exact (memL x).2.1
  have hr₃ : Set.range ((L y D M U).ι ≫ (A y D M).ι ≫ mulFst y D M).base ⊆ Set.range U.ι.base := by
    rw [hrU]; rintro _ ⟨x, rfl⟩
    exact (memL x).2.2.1
  have hr₄ : Set.range ((L y D M U).ι ≫ (A y D M).ι ≫ mulSnd y D M).base ⊆ Set.range U.ι.base := by
    rw [hrU]; rintro _ ⟨x, rfl⟩
    exact (memL x).2.2.2
  let t : (L y D M U : Scheme.{u}) ⟶ Spec (CommRingCat.of R) :=
    (L y D M U).ι ≫ (A y D M).ι ≫ Q12 y D ≫ D.ι ≫ pullback.fst y y ≫ y
  have e₁ := IsOpenImmersion.lift_fac U.ι _ hr₁
  have e₂ := IsOpenImmersion.lift_fac U.ι _ hr₂
  have e₃ := IsOpenImmersion.lift_fac U.ι _ hr₃
  have e₄ := IsOpenImmersion.lift_fac U.ι _ hr₄
  let uu : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨IsOpenImmersion.lift U.ι _ hr₁, by rw [reassoc_of% e₁]⟩
  let vv : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨IsOpenImmersion.lift U.ι _ hr₂, by rw [reassoc_of% e₂, ← Q12_snd_assoc, ← fst_y]⟩
  let pp : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨IsOpenImmersion.lift U.ι _ hr₃, by rw [reassoc_of% e₃, mulFst_fst_assoc, M_y]⟩
  let qq : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨IsOpenImmersion.lift U.ι _ hr₄, by rw [reassoc_of% e₄, mulSnd_fst_assoc]⟩
  have m₁ : uu.1 ≫ m.1 = ((L y D M U).ι ≫ (A y D M).ι ≫ Q12 y D) ≫ M.1 :=
    comp_m_eq y D M U m hUD hM _ _ (by rw [e₁, Category.assoc, Category.assoc])
  have m₂ : vv.1 ≫ m.1 = ((L y D M U).ι ≫ (A y D M).ι ≫ Q23 y D) ≫ M.1 :=
    comp_m_eq y D M U m hUD hM _ _ (by rw [e₂, Category.assoc, Category.assoc])
  have m₃ : pp.1 ≫ m.1 = ((L y D M U).ι ≫ dF y D M) ≫ M.1 :=
    comp_m_eq y D M U m hUD hM _ _ (by rw [e₃, Category.assoc, dF_ι])
  have m₄ : qq.1 ≫ m.1 = ((L y D M U).ι ≫ dG y D M) ≫ M.1 :=
    comp_m_eq y D M U m hUD hM _ _ (by rw [e₄, Category.assoc, dG_ι])
  have key := hassoc t uu vv pp qq
    (by rw [reassoc_of% e₁, reassoc_of% e₂, Q12_snd])
    (by rw [m₁, reassoc_of% e₃, mulFst_fst, Category.assoc, Category.assoc])
    (by rw [reassoc_of% e₃, reassoc_of% e₂, mulFst_snd])
    (by rw [reassoc_of% e₄, reassoc_of% e₁, mulSnd_fst])
    (by rw [m₂, reassoc_of% e₄, mulSnd_snd, Category.assoc, Category.assoc])
  rw [m₃, m₄] at key
  simpa only [FF, GG, Category.assoc] using key

include hM hassoc in
theorem assoc_ext [IsDomain R] [IsDiscreteValuationRing R] [Smooth y] [IsSeparated y]
    [UniversallyOpen M.1]
    (hU : Dense (U : Set ↑(pullback y y)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (u v p q : SchemeHomOver t (D.ι ≫ pullback.fst y y ≫ y))
    (h₁ : u.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.fst y y)
    (h₂ : p.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ M.1)
    (h₃ : p.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.snd y y)
    (h₄ : q.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ D.ι ≫ pullback.fst y y)
    (h₅ : q.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ M.1) :
    p.1 ≫ M.1 = q.1 ≫ M.1 :=
  AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication.assoc_of_FF_eq_GG y D M
    (FF_eq_GG y D M U m hUD hM hassoc hU) t u v p q h₁ h₂ h₃ h₄ h₅

end Assoc

section ZMT

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
  [Smooth y'] [LocallyOfFiniteType y'] [QuasiCompact y']
  (U' : (pullback y' y').Opens)

theorem isOpenImmersion_of_zmt (f : (U' : Scheme.{u}) ⟶ pullback y' y') [LocallyQuasiFinite f]
    (pr : pullback y' y' ⟶ Y') [IsSeparated pr] [LocallyOfFiniteType pr] (hf : f ≫ pr = U'.ι ≫ pr)
    (V : (pullback y' y').Opens) (hV : Dense (V : Set ↑(pullback y' y')))
    (s : (V : Scheme.{u}) ⟶ U') (hs : s ≫ f = V.ι) (hsd : DenseRange s.base) : IsOpenImmersion f :=
      by
  have : IsLocallyNoetherian (pullback y' y') :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst y' y' ≫ y')
  have : CompactSpace ↑(pullback y' y') :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst y' y' ≫ y')
  have : IsNoetherian (pullback y' y') := {}
  have : NoetherianSpace ↑(U' : Scheme.{u}) := U'.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : IsReduced (U' : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (U'.ι ≫ pullback.fst y' y' ≫ y')
  have : IsSeparated (f ≫ pr) := by rw [hf]; infer_instance
  have : IsSeparated f := IsSeparated.of_comp f pr
  have : LocallyOfFiniteType (f ≫ pr) := by rw [hf]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f pr
  have : QuasiCompact f := inferInstance
  have hY : ∀ z : ↑(pullback y' y'), IsDomain ((pullback y' y').presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback y' y').presheaf.stalk z) := fun z =>
    AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      (pullback.fst y' y' ≫ y') z
  exact isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
    f hY V hV s hs hsd

end ZMT

section Ext

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R)) (ι : SchemeHomOver y y') [IsOpenImmersion
    ι.1]
  (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y')

/-- The image of the original multiplication domain inside the new product. -/
def U0 : (pullback y' y').Opens := ch y y' ι ι ''ᵁ U

/-- Identify the original domain with its open image in the glued product. -/
def e0 : (U : Scheme.{u}) ≅ (U0 y U y' ι : Scheme.{u}) := (ch y y' ι ι).isoImage U

@[reassoc]
theorem e0_hom_ι : (e0 y U y' ι).hom ≫ (U0 y U y' ι).ι = U.ι ≫ ch y y' ι ι :=
  Scheme.Hom.isoImage_hom_ι _ _

@[reassoc]
theorem e0_inv_ι : (e0 y U y' ι).inv ≫ U.ι ≫ ch y y' ι ι = (U0 y U y' ι).ι :=
  Scheme.Hom.isoImage_inv_ι _ _

/-- Transport the original partial multiplication to its open image. -/
def m0 : SchemeHomOver ((U0 y U y' ι).ι ≫ pullback.fst y' y' ≫ y') y' :=
  ⟨(e0 y U y' ι).inv ≫ m.1 ≫ ι.1, by
    rw [Category.assoc, Category.assoc, ι.2, m.2, ← e0_inv_ι_assoc, ch_fst_assoc, ι.2]⟩

theorem m0_val : (m0 y U m y' ι).1 = (e0 y U y' ι).inv ≫ m.1 ≫ ι.1 := rfl

variable (hext : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
  ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
    w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
    w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
    w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1)

omit [IsOpenImmersion ι.1] in
include hext in
theorem exists_w0 : ∃ w₀ : (U : Scheme.{u}) ⟶ U', w₀ ≫ U'.ι = U.ι ≫ ch y y' ι ι ∧ w₀ ≫ m'.1 = m.1 ≫
    ι.1 := by
  obtain ⟨w', h1, h2, h3⟩ := hext (U.ι ≫ pullback.fst y y ≫ y) ⟨𝟙 _, Category.id_comp _⟩
  refine ⟨w'.1, ?_, by rw [h3, Category.id_comp]⟩
  apply pullback.hom_ext
  · rw [Category.assoc, h1, Category.id_comp, Category.assoc, ch_fst]
  · rw [Category.assoc, h2, Category.id_comp, Category.assoc, ch_snd]

variable {y U m y' ι U' m'}

section W0

variable (w₀ : (U : Scheme.{u}) ⟶ U') (hw₀ : w₀ ≫ U'.ι = U.ι ≫ ch y y' ι ι) (hw₀m : w₀ ≫ m'.1 = m.1
    ≫ ι.1)

include hw₀ in
theorem U0_le : U0 y U y' ι ≤ U' := by
  intro z hz
  have hz' : z ∈ ((U0 y U y' ι : (pullback y' y').Opens) : Set ↑(pullback y' y')) := hz
  rw [U0, Scheme.Hom.coe_image] at hz'
  obtain ⟨u, hu, rfl⟩ := hz'
  let uU : ↥(U : Scheme.{u}) := ⟨u, hu⟩
  have hpoint : (ch y y' ι ι).base u = U'.ι.base (w₀.base uU) :=
    (congrArg (fun f : (U : Scheme.{u}) ⟶ pullback y' y' => f.base uU) hw₀).symm
  exact hpoint.symm ▸ (w₀.base uU).2

include hw₀ in
theorem e0_hom_homOfLE (h : U0 y U y' ι ≤ U') : (e0 y U y' ι).hom ≫ (pullback y' y').homOfLE h = w₀
    := by
  rw [← cancel_mono U'.ι, Category.assoc, Scheme.homOfLE_ι, e0_hom_ι, hw₀]

include hw₀ hw₀m in
theorem homOfLE_m' (h : U0 y U y' ι ≤ U') : (pullback y' y').homOfLE h ≫ m'.1 = (m0 y U m y' ι).1 :=
    by
  rw [m0_val, ← hw₀m, ← e0_hom_homOfLE w₀ hw₀ h, Category.assoc, Iso.inv_hom_id_assoc]

omit [IsOpenImmersion ι.1] in
include hw₀ hw₀m in
theorem w0_Phi' :
    w₀ ≫ pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
        ((Category.assoc _ _ _).trans m'.2.symm) = Phi y U m ≫ ch y y' ι ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, reassoc_of% hw₀, ch_fst, Category.assoc, ch_fst,
      pullback.lift_fst_assoc, Category.assoc]
  · rw [Category.assoc, pullback.lift_snd, hw₀m, Category.assoc, ch_snd, pullback.lift_snd_assoc]

omit [IsOpenImmersion ι.1] in
include hw₀ hw₀m in
theorem w0_Psi' :
    w₀ ≫ pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
        (m'.2.trans (by rw [Category.assoc, pullback.condition])) = Psi y U m ≫ ch y y' ι ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hw₀m, Category.assoc, ch_fst, pullback.lift_fst_assoc]
  · rw [Category.assoc, pullback.lift_snd, reassoc_of% hw₀, ch_snd, Category.assoc, ch_snd,
      pullback.lift_snd_assoc, Category.assoc]

include hw₀ in
theorem isOpenImmersion_w0 : IsOpenImmersion w₀ := by
  have : IsOpenImmersion (w₀ ≫ U'.ι) := by rw [hw₀]; infer_instance
  exact IsOpenImmersion.of_comp w₀ U'.ι

omit [IsOpenImmersion ι.1] in
include hw₀ in
theorem denseRange_w0 (hd : Dense ((ch y y' ι ι) '' (U : Set ↑(pullback y y)))) : DenseRange w₀.base
    := by
  have h1 : Set.range w₀.base = U'.ι.base ⁻¹' ((ch y y' ι ι) '' (U : Set ↑(pullback y y))) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨U.ι.base u, u.2, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hw₀, Scheme.Hom.comp_apply]
    · rintro ⟨q, hq, hz⟩
      let qU : ↥(U : Scheme.{u}) := ⟨q, hq⟩
      refine ⟨qU, U'.ι.isOpenEmbedding.injective ?_⟩
      exact (congrArg (fun f : (U : Scheme.{u}) ⟶ pullback y' y' => f.base qU) hw₀).trans hz
  rw [DenseRange, h1]
  exact hd.preimage U'.ι.isOpenEmbedding.isOpenMap

theorem range_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g).base = g.base '' Set.range f.base := by
  ext z; constructor
  · rintro ⟨x, rfl⟩; exact ⟨f.base x, ⟨x, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, Scheme.Hom.comp_apply _ _ _⟩

theorem exists_section (F : (U' : Scheme.{u}) ⟶ pullback y' y') (g : (U : Scheme.{u}) ⟶ pullback y'
    y')
    [IsOpenImmersion g] (hF : w₀ ≫ F = g) :
    ∃ s : (g.opensRange : Scheme.{u}) ⟶ U', s ≫ F = g.opensRange.ι ∧ Set.range s.base = Set.range
      w₀.base := by
  refine ⟨g.isoOpensRange.inv ≫ w₀, by rw [Category.assoc, hF, Scheme.Hom.isoOpensRange_inv_comp],
    ?_⟩
  ext z; constructor
  · rintro ⟨v, rfl⟩; exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨g.isoOpensRange.hom.base u, by rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]⟩

end W0

variable (y U m y' ι) in
theorem hassoc_m0
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
        pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y =
        v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (u v p q : SchemeHomOver t ((U0 y U y' ι).ι ≫ pullback.fst y' y' ≫ y'))
    (h₁ : u.1 ≫ (U0 y U y' ι).ι ≫ pullback.snd y' y' = v.1 ≫ (U0 y U y' ι).ι ≫ pullback.fst y' y')
    (h₂ : p.1 ≫ (U0 y U y' ι).ι ≫ pullback.fst y' y' = u.1 ≫ (m0 y U m y' ι).1)
    (h₃ : p.1 ≫ (U0 y U y' ι).ι ≫ pullback.snd y' y' = v.1 ≫ (U0 y U y' ι).ι ≫ pullback.snd y' y')
    (h₄ : q.1 ≫ (U0 y U y' ι).ι ≫ pullback.fst y' y' = u.1 ≫ (U0 y U y' ι).ι ≫ pullback.fst y' y')
    (h₅ : q.1 ≫ (U0 y U y' ι).ι ≫ pullback.snd y' y' = v.1 ≫ (m0 y U m y' ι).1) :
    p.1 ≫ (m0 y U m y' ι).1 = q.1 ≫ (m0 y U m y' ι).1 := by
  have cf : (U0 y U y' ι).ι ≫ pullback.fst y' y' = (e0 y U y' ι).inv ≫ U.ι ≫ pullback.fst y y ≫ ι.1
    := by
    rw [← e0_inv_ι_assoc, ch_fst]
  have cs : (U0 y U y' ι).ι ≫ pullback.snd y' y' = (e0 y U y' ι).inv ≫ U.ι ≫ pullback.snd y y ≫ ι.1
    := by
    rw [← e0_inv_ι_assoc, ch_snd]
  have ht : ∀ r : SchemeHomOver t ((U0 y U y' ι).ι ≫ pullback.fst y' y' ≫ y'),
      (r.1 ≫ (e0 y U y' ι).inv) ≫ U.ι ≫ pullback.fst y y ≫ y = t := by
    have hc : ((e0 y U y' ι).inv ≫ U.ι ≫ pullback.fst y y) ≫ y =
        ((U0 y U y' ι).ι ≫ pullback.fst y' y') ≫ y' := by
      simp only [cf, Category.assoc, ι.2]
    intro r
    calc (r.1 ≫ (e0 y U y' ι).inv) ≫ U.ι ≫ pullback.fst y y ≫ y
        = r.1 ≫ (((e0 y U y' ι).inv ≫ U.ι ≫ pullback.fst y y) ≫ y) := by simp only [Category.assoc]
      _ = r.1 ≫ (((U0 y U y' ι).ι ≫ pullback.fst y' y') ≫ y') := by rw [hc]
      _ = t := by simpa only [Category.assoc] using r.2
  let u' : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) := ⟨u.1 ≫ (e0 y U y' ι).inv, ht u⟩
  let v' : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) := ⟨v.1 ≫ (e0 y U y' ι).inv, ht v⟩
  let p' : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) := ⟨p.1 ≫ (e0 y U y' ι).inv, ht p⟩
  let q' : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) := ⟨q.1 ≫ (e0 y U y' ι).inv, ht q⟩
  simp only [m0_val, cf, cs] at h₁ h₂ h₃ h₄ h₅ ⊢
  simp only [← Category.assoc] at h₁ h₂ h₃ h₄ h₅ ⊢
  rw [cancel_mono] at h₁ h₂ h₃ h₄ h₅
  simp only [Category.assoc] at h₁ h₂ h₃ h₄ h₅
  have key := hassoc t u' v' p' q'
    (by simpa only [u', v', Category.assoc] using h₁) (by simpa only [u', p', Category.assoc] using
      h₂)
    (by simpa only [v', p', Category.assoc] using h₃) (by simpa only [u', q', Category.assoc] using
      h₄)
    (by simpa only [v', q', Category.assoc] using h₅)
  simp only [p', q', Category.assoc] at key
  simp only [Category.assoc]
  rw [reassoc_of% key]

end Ext

end LawExtension
end AbelianVarieties.NOSProofs.QuasiFiniteLawExtension

open AbelianVarieties.NOSProofs.QuasiFiniteLawExtension.LawExtension

namespace NeronModelInfra

theorem isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
        pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y =
        v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι : SchemeHomOver y y') [IsOpenImmersion ι.1]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y')
    (hext : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫
      pullback.fst y y ≫ y)),
      ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
        w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1)
    [LocallyQuasiFinite
      (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
        ((Category.assoc _ _ _).trans m'.2.symm))]
    [LocallyQuasiFinite
      (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
        (m'.2.trans (by rw [Category.assoc, pullback.condition])))] :
    IsOpenImmersion
        (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
          ((Category.assoc _ _ _).trans m'.2.symm)) ∧
    IsOpenImmersion
        (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
          (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
      u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
      p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
      p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
      q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' →
      q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
      p.1 ≫ m'.1 = q.1 ≫ m'.1) := by
  have : IsOpenImmersion (Phi y U m) := hΦ
  have : IsOpenImmersion (Psi y U m) := hΨ
  obtain ⟨w₀, hw₀, hw₀m⟩ := exists_w0 y U m y' ι U' m' hext
  have hUD : U0 y U y' ι ≤ U' := U0_le w₀ hw₀
  have hM : (pullback y' y').homOfLE hUD ≫ m'.1 = (m0 y U m y' ι).1 := homOfLE_m' w₀ hw₀ hw₀m hUD
  have hU : Dense (U : Set ↑(pullback y y)) := dense_of_forall_dense_fibre (fun q => (pullback.fst y
    y).base q) _ hU₁
  have hΦU : Dense (Set.range (Phi y U m).base) :=
    dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hΦ₁
  have hΨU : Dense (Set.range (Psi y U m).base) :=
    dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hΨ₁
  have hU0 : Dense ((U0 y U y' ι : (pullback y' y').Opens) : Set ↑(pullback y' y')) := by
    rw [U0, Scheme.Hom.coe_image]; exact dense_image_ch y y' ι hιd hU
  have hdw₀ : DenseRange w₀.base := denseRange_w0 w₀ hw₀ (by rw [← Scheme.Hom.coe_image]; exact hU0)
  set Φ' := pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
    ((Category.assoc _ _ _).trans m'.2.symm) with hΦ'
  set Ψ' := pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
    (m'.2.trans (by rw [Category.assoc, pullback.condition])) with hΨ'
  have hΦ'oi : IsOpenImmersion Φ' := by
    obtain ⟨s, hs, hsr⟩ := exists_section w₀ Φ' (Phi y U m ≫ ch y y' ι ι) (w0_Phi' w₀ hw₀ hw₀m)
    refine isOpenImmersion_of_zmt y' U' Φ' (pullback.fst y' y') (pullback.lift_fst _ _ _) _ ?_ s hs
      ?_
    · rw [Scheme.Hom.coe_opensRange, range_comp]
      exact dense_image_ch y y' ι hιd hΦU
    · rw [DenseRange, hsr]; exact hdw₀
  have hΨ'oi : IsOpenImmersion Ψ' := by
    obtain ⟨s, hs, hsr⟩ := exists_section w₀ Ψ' (Psi y U m ≫ ch y y' ι ι) (w0_Psi' w₀ hw₀ hw₀m)
    refine isOpenImmersion_of_zmt y' U' Ψ' (pullback.snd y' y') (pullback.lift_snd _ _ _) _ ?_ s hs
      ?_
    · rw [Scheme.Hom.coe_opensRange, range_comp]
      exact dense_image_ch y y' ι hιd hΨU
    · rw [DenseRange, hsr]; exact hdw₀
  refine ⟨hΦ'oi, hΨ'oi, ?_⟩
  have : UniversallyOpen m'.1 := by
    have h : m'.1 = Φ' ≫ pullback.snd y' y' := (pullback.lift_snd _ _ _).symm
    rw [h]; infer_instance
  intro T t u v p q h₁ h₂ h₃ h₄ h₅
  exact assoc_ext y' U' m' (U0 y U y' ι) (m0 y U m y' ι) hUD hM
    (fun t u v p q => hassoc_m0 y U m y' ι hassoc t u v p q) hU0 t u v p q h₁ h₂ h₃ h₄ h₅

end NeronModelInfra

end
end
