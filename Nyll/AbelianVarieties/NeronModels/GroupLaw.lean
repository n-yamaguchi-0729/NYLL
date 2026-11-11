/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.NoetherianSpace
public import Nyll.AbelianVarieties.NeronModels.Density
public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.AbelianVarieties.NeronModels.DenseOpens
public import Nyll.AbelianVarieties.NeronModels.Descent
public import Nyll.AbelianVarieties.NeronModels.GenericFibre
public import Nyll.AbelianVarieties.NeronModels.OpenExtensions
public import Nyll.AbelianVarieties.NeronModels.StalkExtensions
public import Nyll.AbelianVarieties.NeronModels.TranslationCharts
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-! # Extension of partial multiplication to a smooth group model -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul.lean
Upstream NOTICE:
    https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION:
    https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.AssociativityRestriction


noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
    Topology

universe u

namespace PartialMultiplication

open NeronModelInfra.DenseSliceLocus (exists_maximal_specializes exists_fibre_maximal)

section Topo

variable {P : Type*} [TopologicalSpace P]

theorem DenseIn.of_subset {S F : Set P} (h : F ⊆ S) : DenseIn S F :=
  fun _ hx => subset_closure ⟨h hx, hx⟩

theorem DenseIn.of_inter_subset {S S' F : Set P} (h : DenseIn S F) (hS : S ∩ F ⊆ S') : DenseIn S' F
    :=
  h.trans (closure_mono fun _ hx => ⟨hS hx, hx.2⟩)

theorem DenseIn.inter_of_isOpen_left {S T F : Set P} (hS : DenseIn S F) (hT : DenseIn T F)
    (ho : IsOpen S) : DenseIn (S ∩ T) F := by
  intro x hx
  rw [mem_closure_iff]
  intro O hO hxO
  obtain ⟨y, hyO, hyS, hyF⟩ := mem_closure_iff.mp (hS hx) O hO hxO
  obtain ⟨z, ⟨hzO, hzS⟩, hzT, hzF⟩ := mem_closure_iff.mp (hT hyF) (O ∩ S) (hO.inter ho) ⟨hyO, hyS⟩
  exact ⟨z, hzO, ⟨hzS, hzT⟩, hzF⟩

theorem DenseIn.inter_of_isOpen_right {S T F : Set P} (hS : DenseIn S F) (hT : DenseIn T F)
    (ho : IsOpen T) : DenseIn (S ∩ T) F := by
  rw [Set.inter_comm]; exact hT.inter_of_isOpen_left hS ho

theorem DenseIn.of_forall_exists_specializes {S F : Set P}
    (h : ∀ x ∈ F, ∃ θ ∈ F, θ ∈ S ∧ θ ⤳ x) : DenseIn S F := by
  intro x hx
  obtain ⟨θ, hθF, hθS, hθx⟩ := h x hx
  exact closure_mono (Set.singleton_subset_iff.mpr (show θ ∈ S ∩ F from ⟨hθS, hθF⟩)) hθx.mem_closure

theorem DenseIn.image_homeomorph {P' : Type*} [TopologicalSpace P'] (σ : P ≃ₜ P') {S F : Set P}
    (h : DenseIn S F) : DenseIn (σ '' S) (σ '' F) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← Set.image_inter σ.injective, ← σ.image_closure]
  exact ⟨y, h hy, rfl⟩

theorem six_denseIn {X W : Type*} [TopologicalSpace X] [TopologicalSpace W]
    (p₁ p₂ : P → X) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (ι : W → P) (hι : IsOpenEmbedding ι) (m : W → X) (hm : Continuous m)
    (Φ Ψ : W → P) (hΦ : IsInducing Φ) (hΨ : IsInducing Ψ)
    (hΦ₁ : ∀ w, p₁ (Φ w) = p₁ (ι w)) (hΦ₂ : ∀ w, p₂ (Φ w) = m w)
    (hΨ₁ : ∀ w, p₁ (Ψ w) = m w) (hΨ₂ : ∀ w, p₂ (Ψ w) = p₂ (ι w))
    (X' : Set X) (hX' : IsOpen X') (a : X) (ha : a ∈ X')
    (h₁ : DenseIn (Set.range ι ∩ Set.range Φ ∩ Set.range Ψ) (p₁ ⁻¹' {a}))
    (h₂ : DenseIn (Set.range ι ∩ Set.range Φ ∩ Set.range Ψ) (p₂ ⁻¹' {a}))
    (h₃ : DenseIn (p₂ ⁻¹' X') (p₁ ⁻¹' {a}))
    (h₄ : DenseIn (p₁ ⁻¹' X') (p₂ ⁻¹' {a})) :
    DenseIn (ι '' {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'}) (p₁ ⁻¹' {a}) ∧
    DenseIn (ι '' {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'}) (p₂ ⁻¹' {a}) ∧
    DenseIn (Φ '' {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'}) (p₁ ⁻¹' {a}) ∧
    DenseIn (Φ '' {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'}) (p₂ ⁻¹' {a}) ∧
    DenseIn (Ψ '' {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'}) (p₁ ⁻¹' {a}) ∧
    DenseIn (Ψ '' {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'}) (p₂ ⁻¹' {a}) := by
  set UW : Set W := {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'} with hUW
  set F : Set P := p₁ ⁻¹' {a} with hF
  set F' : Set P := p₂ ⁻¹' {a} with hF'
  set A : Set W := ι ⁻¹' (p₁ ⁻¹' X') with hA
  set B : Set W := ι ⁻¹' (p₂ ⁻¹' X') with hB
  set M : Set W := m ⁻¹' X' with hM
  have hAo : IsOpen A := (hX'.preimage hp₁).preimage hι.continuous
  have hBo : IsOpen B := (hX'.preimage hp₂).preimage hι.continuous
  have hMo : IsOpen M := hX'.preimage hm
  have hUW' : UW = A ∩ B ∩ M := by
    ext w; simp only [hUW, hA, hB, hM, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      and_assoc]
  have hιF : DenseIn (Set.range ι) F := h₁.mono fun _ h => h.1.1
  have hΦF : DenseIn (Set.range Φ) F := h₁.mono fun _ h => h.1.2
  have hΨF : DenseIn (Set.range Ψ) F := h₁.mono fun _ h => h.2
  have hιF' : DenseIn (Set.range ι) F' := h₂.mono fun _ h => h.1.1
  have hΦF' : DenseIn (Set.range Φ) F' := h₂.mono fun _ h => h.1.2
  have hΨF' : DenseIn (Set.range Ψ) F' := h₂.mono fun _ h => h.2
  have eΦF : Φ ⁻¹' F = ι ⁻¹' F := by
    ext w; simp only [hF, Set.mem_preimage, Set.mem_singleton_iff, hΦ₁]
  have eΨF' : Ψ ⁻¹' F' = ι ⁻¹' F' := by
    ext w; simp only [hF', Set.mem_preimage, Set.mem_singleton_iff, hΨ₂]
  have eΦF' : Φ ⁻¹' F' = m ⁻¹' {a} := by
    ext w; simp only [hF', Set.mem_preimage, Set.mem_singleton_iff, hΦ₂]
  have eΨF : Ψ ⁻¹' F = m ⁻¹' {a} := by
    ext w; simp only [hF, Set.mem_preimage, Set.mem_singleton_iff, hΨ₁]
  have iA : ι '' A = Set.range ι ∩ p₁ ⁻¹' X' := Set.image_preimage_eq_range_inter
  have iB : ι '' B = Set.range ι ∩ p₂ ⁻¹' X' := Set.image_preimage_eq_range_inter
  have ΦA : Φ '' A = Set.range Φ ∩ p₁ ⁻¹' X' := by
    have : A = Φ ⁻¹' (p₁ ⁻¹' X') := by ext w; simp only [hA, Set.mem_preimage, hΦ₁]
    rw [this]; exact Set.image_preimage_eq_range_inter
  have ΦM : Φ '' M = Set.range Φ ∩ p₂ ⁻¹' X' := by
    have : M = Φ ⁻¹' (p₂ ⁻¹' X') := by ext w; simp only [hM, Set.mem_preimage, hΦ₂]
    rw [this]; exact Set.image_preimage_eq_range_inter
  have ΨM : Ψ '' M = Set.range Ψ ∩ p₁ ⁻¹' X' := by
    have : M = Ψ ⁻¹' (p₁ ⁻¹' X') := by ext w; simp only [hM, Set.mem_preimage, hΨ₁]
    rw [this]; exact Set.image_preimage_eq_range_inter
  have ΨB : Ψ '' B = Set.range Ψ ∩ p₂ ⁻¹' X' := by
    have : B = Ψ ⁻¹' (p₂ ⁻¹' X') := by ext w; simp only [hB, Set.mem_preimage, hΨ₂]
    rw [this]; exact Set.image_preimage_eq_range_inter
  have oX'₁ : IsOpen (p₁ ⁻¹' X') := hX'.preimage hp₁
  have oX'₂ : IsOpen (p₂ ⁻¹' X') := hX'.preimage hp₂
  have dF : DenseIn UW (ι ⁻¹' F) := by
    have dB : DenseIn B (ι ⁻¹' F) := by
      rw [← DenseIn.image_iff hι.isInducing hιF, iB]; exact hιF.inter_of_isOpen_right h₃ oX'₂
    have dM : DenseIn M (ι ⁻¹' F) := by
      rw [← eΦF, ← DenseIn.image_iff hΦ hΦF, ΦM]; exact hΦF.inter_of_isOpen_right h₃ oX'₂
    refine (dB.inter_of_isOpen_left dM hBo).of_inter_subset ?_
    rintro w ⟨⟨hwB, hwM⟩, hwF⟩
    rw [hUW']
    refine ⟨⟨?_, hwB⟩, hwM⟩
    change p₁ (ι w) ∈ X'
    have : p₁ (ι w) = a := hwF
    rw [this]; exact ha
  have dF' : DenseIn UW (ι ⁻¹' F') := by
    have dA : DenseIn A (ι ⁻¹' F') := by
      rw [← DenseIn.image_iff hι.isInducing hιF', iA]; exact hιF'.inter_of_isOpen_right h₄ oX'₁
    have dM : DenseIn M (ι ⁻¹' F') := by
      rw [← eΨF', ← DenseIn.image_iff hΨ hΨF', ΨM]; exact hΨF'.inter_of_isOpen_right h₄ oX'₁
    refine (dA.inter_of_isOpen_left dM hAo).of_inter_subset ?_
    rintro w ⟨⟨hwA, hwM⟩, hwF⟩
    rw [hUW']
    refine ⟨⟨hwA, ?_⟩, hwM⟩
    change p₂ (ι w) ∈ X'
    have : p₂ (ι w) = a := hwF
    rw [this]; exact ha
  have dm : DenseIn UW (m ⁻¹' {a}) := by
    have dA : DenseIn A (m ⁻¹' {a}) := by
      rw [← eΦF', ← DenseIn.image_iff hΦ hΦF', ΦA]; exact hΦF'.inter_of_isOpen_right h₄ oX'₁
    have dB : DenseIn B (m ⁻¹' {a}) := by
      rw [← eΨF, ← DenseIn.image_iff hΨ hΨF, ΨB]; exact hΨF.inter_of_isOpen_right h₃ oX'₂
    refine (dA.inter_of_isOpen_left dB hAo).of_inter_subset ?_
    rintro w ⟨⟨hwA, hwB⟩, hwm⟩
    rw [hUW']
    refine ⟨⟨hwA, hwB⟩, ?_⟩
    change m w ∈ X'
    have : m w = a := hwm
    rw [this]; exact ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (DenseIn.image_iff hι.isInducing hιF UW).mpr dF
  · exact (DenseIn.image_iff hι.isInducing hιF' UW).mpr dF'
  · exact (DenseIn.image_iff hΦ hΦF UW).mpr (eΦF ▸ dF)
  · exact (DenseIn.image_iff hΦ hΦF' UW).mpr (eΦF' ▸ dm)
  · exact (DenseIn.image_iff hΨ hΨF UW).mpr (eΨF ▸ dm)
  · exact (DenseIn.image_iff hΨ hΨF' UW).mpr (eΨF' ▸ dF')

end Topo

section MaxPts

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R))

/-- A generic point of the special fibre. -/
def IsMaxSp (x : P) : Prop :=
  p.base x = IsLocalRing.closedPoint R ∧
    ∀ y : P, y ⤳ x → p.base y = IsLocalRing.closedPoint R → y = x

variable {p}

theorem isMaxSp_comp_iff {W : Scheme.{u}} (i : W ⟶ P) [IsOpenImmersion i] (x : W) :
    IsMaxSp (i ≫ p) x ↔ IsMaxSp p (i.base x) := by
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨by simpa only [Scheme.Hom.comp_apply] using hx, fun y hy hys => ?_⟩
    have hyr : y ∈ Set.range i.base := hy.mem_open i.isOpenEmbedding.isOpen_range ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hyr
    rw [hmax y ((i.isOpenEmbedding.isInducing.specializes_iff).mp hy)
      (by simpa only [Scheme.Hom.comp_apply] using hys)]
  · rintro ⟨hx, hmax⟩
    refine ⟨by simpa only [Scheme.Hom.comp_apply] using hx, fun y hy hys => ?_⟩
    apply i.isOpenEmbedding.injective
    exact hmax _ (hy.map i.base.hom.continuous) (by simpa only [Scheme.Hom.comp_apply] using hys)

theorem IsMaxSp.of_opens {U : P.Opens} {x : U} (hx : IsMaxSp (U.ι ≫ p) x) : IsMaxSp p x.1 :=
  (isMaxSp_comp_iff U.ι x).mp hx

theorem IsMaxSp.to_opens (U : P.Opens) {x : P} (hx : IsMaxSp p x) (hxU : x ∈ U) :
    IsMaxSp (U.ι ≫ p) ⟨x, hxU⟩ :=
  (isMaxSp_comp_iff U.ι ⟨x, hxU⟩).mpr hx

end MaxPts

section GenericPoint

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

variable {R K}

theorem range_fst_specGenericFibreInclusion {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R)) :
    Set.range (pullback.fst p (specGenericFibreInclusion R K)).base = {x | p.base x ≠
      IsLocalRing.closedPoint R} := by
  rw [Scheme.Pullback.range_fst, range_specGenericFibreInclusion]
  rfl

theorem base_ne_closedPoint {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (x : S) :
    (s ≫ specGenericFibreInclusion R K).base x ≠ IsLocalRing.closedPoint R := by
  have : (specGenericFibreInclusion R K).base (s.base x) ∈ Set.range (specGenericFibreInclusion R
    K).base :=
    ⟨_, rfl⟩
  rw [range_specGenericFibreInclusion] at this
  exact this

end GenericPoint

section Algebra

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)

variable {K LXK f e}

theorem MulRel.gfr_eq [IsIso e.1] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {a b τ τ' :
    SchemeHomOver t f}
    (h : MulRel K LXK f e a b τ) (h' : MulRel K LXK f e a b τ') :
    genericFibreRestrict R K f t τ = genericFibreRestrict R K f t τ' :=
  comp_e_injective (h.trans h'.symm)

theorem MulRel.gfr_snd_eq [IsIso e.1] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {a b τ a' b' τ' : SchemeHomOver t f} (h : MulRel K LXK f e a b τ) (h' : MulRel K LXK f e a' b'
      τ')
    (hτ : genericFibreRestrict R K f t τ = genericFibreRestrict R K f t τ')
    (ha : genericFibreRestrict R K f t a = genericFibreRestrict R K f t a') :
    genericFibreRestrict R K f t b = genericFibreRestrict R K f t b' := by
  unfold MulRel at h h'
  rw [hτ, ha, h'] at h
  let : Group (SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K)) gK) :=
    LXK.pointGroup (pullback.snd t (specGenericFibreInclusion R K))
  exact comp_e_injective (mul_left_cancel h).symm

theorem MulRel.gfr_fst_eq [IsIso e.1] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {a b τ a' b' τ' : SchemeHomOver t f} (h : MulRel K LXK f e a b τ) (h' : MulRel K LXK f e a' b'
      τ')
    (hτ : genericFibreRestrict R K f t τ = genericFibreRestrict R K f t τ')
    (hb : genericFibreRestrict R K f t b = genericFibreRestrict R K f t b') :
    genericFibreRestrict R K f t a = genericFibreRestrict R K f t a' := by
  unfold MulRel at h h'
  rw [hτ, hb, h'] at h
  let : Group (SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K)) gK) :=
    LXK.pointGroup (pullback.snd t (specGenericFibreInclusion R K))
  exact comp_e_injective (mul_right_cancel h).symm

end Algebra

section Shear

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- First projection as a morphism over the base. -/
abbrev prj₁ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.fst f f, rfl⟩

/-- Second projection as a morphism over the base. -/
abbrev prj₂ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.snd f f, pullback.condition.symm⟩

/-- First projection on generic-fibre points. -/
def fstK {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K)) :=
  NeronModelInfra.schemeHomOverComp z (genericFibreRestrict R K f _ (prj₁ f))

/-- Second projection on generic-fibre points. -/
def sndK {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K)) :=
  NeronModelInfra.schemeHomOverComp z (genericFibreRestrict R K f _ (prj₂ f))

/-- Pair two generic-fibre points over the same test scheme. -/
noncomputable def pairK {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (a b : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K))) :
    SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)) :=
  ⟨pullback.lift
      (pullback.lift (a.1 ≫ pullback.fst f _) (b.1 ≫ pullback.fst f _)
        (by simp only [Category.assoc, pullback.condition, reassoc_of% a.2, reassoc_of% b.2]))
      t (by rw [pullback.lift_fst_assoc, Category.assoc, pullback.condition, reassoc_of% a.2]),
    pullback.lift_snd _ _ _⟩

variable {K f}

theorem fstK_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    (fstK K f z).1 ≫ pullback.fst f (specGenericFibreInclusion R K) =
      z.1 ≫ pullback.fst _ (specGenericFibreInclusion R K) ≫ pullback.fst f f := by
  simp only [fstK, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
    genericFibreRestrict_coe_comp_fst]

theorem sndK_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    (sndK K f z).1 ≫ pullback.fst f (specGenericFibreInclusion R K) =
      z.1 ≫ pullback.fst _ (specGenericFibreInclusion R K) ≫ pullback.snd f f := by
  simp only [sndK, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
    genericFibreRestrict_coe_comp_fst]

theorem extK {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {z z' : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))}
    (h1 : fstK K f z = fstK K f z') (h2 : sndK K f z = sndK K f z') : z = z' := by
  apply Subtype.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc, fstK_coe] using congrArg (fun w => w.1 ≫ pullback.fst f _) h1
    · simpa only [Category.assoc, sndK_coe] using congrArg (fun w => w.1 ≫ pullback.fst f _) h2
  · rw [z.2, z'.2]

@[scoped simp] theorem fstK_pairK {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (a b : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K))) : fstK K f (pairK K f
      a b) = a := by
  apply Subtype.ext; apply pullback.hom_ext
  · rw [fstK_coe]; simp only [pairK, pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [(fstK K f _).2, a.2]

@[scoped simp] theorem sndK_pairK {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (a b : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K))) : sndK K f (pairK K f
      a b) = b := by
  apply Subtype.ext; apply pullback.hom_ext
  · rw [sndK_coe]; simp only [pairK, pullback.lift_fst_assoc, pullback.lift_snd]
  · rw [(sndK K f _).2, b.2]

theorem fstK_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec
    (CommRingCat.of K)}
    (ψ : SchemeHomOver t' t)
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    fstK K f (NeronModelInfra.schemeHomOverComp ψ z) = NeronModelInfra.schemeHomOverComp ψ (fstK K
      f z) :=
  schemeHomOverComp_assoc _ _ _

theorem sndK_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec
    (CommRingCat.of K)}
    (ψ : SchemeHomOver t' t)
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    sndK K f (NeronModelInfra.schemeHomOverComp ψ z) = NeronModelInfra.schemeHomOverComp ψ (sndK K
      f z) :=
  schemeHomOverComp_assoc _ _ _

theorem fstK_id :
    fstK K f (schemeHomOverId (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R
      K))) =
      genericFibreRestrict R K f _ (prj₁ f) := schemeHomOverComp_id_left _

theorem sndK_id :
    sndK K f (schemeHomOverId (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R
      K))) =
      genericFibreRestrict R K f _ (prj₂ f) := schemeHomOverComp_id_left _

variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
variable (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
variable (K f)

/-- Inverse of the specified generic-fibre identification. -/
noncomputable def eInv : SchemeHomOver gK (pullback.snd f (specGenericFibreInclusion R K)) :=
  ⟨inv e.1, by rw [IsIso.inv_comp_eq, e.2]⟩

omit [IsIso e.1] in
/-- Transport a generic-fibre point to the given group. -/
abbrev rd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (a : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K))) : SchemeHomOver t gK :=
  NeronModelInfra.schemeHomOverComp a e

omit [IsIso e.1] in
theorem rd_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec
    (CommRingCat.of K)}
    (ψ : SchemeHomOver t' t) (a : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K)))
      :
    rd K f e (NeronModelInfra.schemeHomOverComp ψ a) = NeronModelInfra.schemeHomOverComp ψ (rd K f
      e a) :=
  schemeHomOverComp_assoc _ _ _

@[scoped simp] theorem rd_comp_eInv {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (x :
  SchemeHomOver t gK) :
    rd K f e (NeronModelInfra.schemeHomOverComp x (eInv K f e)) = x := by
  have h : NeronModelInfra.schemeHomOverComp (eInv K f e) e = schemeHomOverId gK :=
    Subtype.ext (IsIso.inv_hom_id e.1)
  rw [rd, schemeHomOverComp_assoc, h, schemeHomOverComp_id_right]

@[scoped simp] theorem rd_comp_eInv' {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (a : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K))) :
    NeronModelInfra.schemeHomOverComp (rd K f e a) (eInv K f e) = a := by
  have h : NeronModelInfra.schemeHomOverComp e (eInv K f e) = schemeHomOverId _ :=
    Subtype.ext (IsIso.hom_inv_id e.1)
  rw [rd, schemeHomOverComp_assoc, h, schemeHomOverComp_id_right]

/-- Left shear on the generic fibre. -/
def shL : SchemeHomOver (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
    (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)) :=
  pairK K f (genericFibreRestrict R K f _ (prj₁ f))
    (NeronModelInfra.schemeHomOverComp
      (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) (rd K f e (genericFibreRestrict
        R K f _ (prj₂ f))))
      (eInv K f e))

/-- Inverse left shear on the generic fibre. -/
def shL' : SchemeHomOver (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
    (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)) :=
  pairK K f (genericFibreRestrict R K f _ (prj₁ f))
    (NeronModelInfra.schemeHomOverComp
      (LXK.mul _ (LXK.inv _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))))
        (rd K f e (genericFibreRestrict R K f _ (prj₂ f))))
      (eInv K f e))

/-- Right shear on the generic fibre. -/
def shR : SchemeHomOver (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
    (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)) :=
  pairK K f
    (NeronModelInfra.schemeHomOverComp
      (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) (rd K f e (genericFibreRestrict
        R K f _ (prj₂ f))))
      (eInv K f e))
    (genericFibreRestrict R K f _ (prj₂ f))

/-- Inverse right shear on the generic fibre. -/
def shR' : SchemeHomOver (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
    (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)) :=
  pairK K f
    (NeronModelInfra.schemeHomOverComp
      (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f)))
        (LXK.inv _ (rd K f e (genericFibreRestrict R K f _ (prj₂ f)))))
      (eInv K f e))
    (genericFibreRestrict R K f _ (prj₂ f))

omit [IsIso e.1] in
theorem grj_rd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec
    (CommRingCat.of K)}
    (ψ : SchemeHomOver t' t) (a : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K)))
      :
    GoodReductionJacobian.schemeHomOverComp ψ.1 ψ.2 (rd K f e a) = rd K f e
      (NeronModelInfra.schemeHomOverComp ψ a) :=
  (rd_comp K f e ψ a).symm

section GroupIdentities

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of S)} (G :
    RelativeGroupLaw S g)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a b : SchemeHomOver t g)

theorem inv_mul_mul : G.mul t (G.inv t a) (G.mul t a b) = b := by
  rw [← G.mul_assoc, G.inv_mul_cancel, G.one_mul]

theorem mul_inv_mul : G.mul t a (G.mul t (G.inv t a) b) = b := by
  rw [← G.mul_assoc, G.mul_inv_cancel, G.one_mul]

theorem mul_mul_inv : G.mul t (G.mul t a b) (G.inv t b) = a := by
  rw [G.mul_assoc, G.mul_inv_cancel, G.mul_one]

theorem mul_inv_mul' : G.mul t (G.mul t a (G.inv t b)) b = a := by
  rw [G.mul_assoc, G.inv_mul_cancel, G.mul_one]

end GroupIdentities

theorem fstK_shL : fstK K f (shL K f LXK e) = genericFibreRestrict R K f _ (prj₁ f) := fstK_pairK _
    _
theorem sndK_shL : sndK K f (shL K f LXK e) = NeronModelInfra.schemeHomOverComp
    (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) (rd K f e (genericFibreRestrict R
      K f _ (prj₂ f))))
    (eInv K f e) := sndK_pairK _ _
theorem fstK_shL' : fstK K f (shL' K f LXK e) = genericFibreRestrict R K f _ (prj₁ f) := fstK_pairK
    _ _
theorem sndK_shL' : sndK K f (shL' K f LXK e) = NeronModelInfra.schemeHomOverComp
    (LXK.mul _ (LXK.inv _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f)))) (rd K f e
      (genericFibreRestrict R K f _ (prj₂ f))))
    (eInv K f e) := sndK_pairK _ _
theorem fstK_shR : fstK K f (shR K f LXK e) = NeronModelInfra.schemeHomOverComp
    (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) (rd K f e (genericFibreRestrict R
      K f _ (prj₂ f))))
    (eInv K f e) := fstK_pairK _ _
theorem sndK_shR : sndK K f (shR K f LXK e) = genericFibreRestrict R K f _ (prj₂ f) := sndK_pairK _
    _
theorem fstK_shR' : fstK K f (shR' K f LXK e) = NeronModelInfra.schemeHomOverComp
    (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) (LXK.inv _ (rd K f e
      (genericFibreRestrict R K f _ (prj₂ f)))))
    (eInv K f e) := fstK_pairK _ _
theorem sndK_shR' : sndK K f (shR' K f LXK e) = genericFibreRestrict R K f _ (prj₂ f) := sndK_pairK
    _ _

omit [IsIso e.1] in
theorem rd_fstK_comp {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    GoodReductionJacobian.schemeHomOverComp z.1 z.2 (rd K f e (genericFibreRestrict R K f _ (prj₁
      f))) =
      rd K f e (fstK K f z) := grj_rd K f e z _

omit [IsIso e.1] in
theorem rd_sndK_comp {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    GoodReductionJacobian.schemeHomOverComp z.1 z.2 (rd K f e (genericFibreRestrict R K f _ (prj₂
      f))) =
      rd K f e (sndK K f z) := grj_rd K f e z _

theorem shL_comp_shL' : NeronModelInfra.schemeHomOverComp (shL K f LXK e) (shL' K f LXK e) =
    schemeHomOverId _ := by
  apply extK
  · rw [fstK_comp, fstK_shL', fstK_id]; exact fstK_shL K f LXK e
  · rw [sndK_comp, sndK_id, sndK_shL', ← schemeHomOverComp_assoc, ← grj_comp_eq (shL K f LXK e)
      (LXK.mul _ _ _),
      LXK.mul_natural, LXK.inv_natural,
      rd_fstK_comp, rd_sndK_comp, fstK_shL, sndK_shL, rd_comp_eInv,
      inv_mul_mul, rd_comp_eInv']

theorem shL'_comp_shL : NeronModelInfra.schemeHomOverComp (shL' K f LXK e) (shL K f LXK e) =
    schemeHomOverId _ := by
  apply extK
  · rw [fstK_comp, fstK_shL, fstK_id]; exact fstK_shL' K f LXK e
  · rw [sndK_comp, sndK_id, sndK_shL, ← schemeHomOverComp_assoc, ← grj_comp_eq (shL' K f LXK e)
      (LXK.mul _ _ _),
      LXK.mul_natural,
      rd_fstK_comp, rd_sndK_comp, fstK_shL', sndK_shL', rd_comp_eInv,
      mul_inv_mul, rd_comp_eInv']

theorem shR_comp_shR' : NeronModelInfra.schemeHomOverComp (shR K f LXK e) (shR' K f LXK e) =
    schemeHomOverId _ := by
  apply extK
  · rw [fstK_comp, fstK_id, fstK_shR', ← schemeHomOverComp_assoc, ← grj_comp_eq (shR K f LXK e)
      (LXK.mul _ _ _),
      LXK.mul_natural, LXK.inv_natural,
      rd_fstK_comp, rd_sndK_comp, fstK_shR, sndK_shR, rd_comp_eInv,
      mul_mul_inv, rd_comp_eInv']
  · rw [sndK_comp, sndK_shR', sndK_id]; exact sndK_shR K f LXK e

theorem shR'_comp_shR : NeronModelInfra.schemeHomOverComp (shR' K f LXK e) (shR K f LXK e) =
    schemeHomOverId _ := by
  apply extK
  · rw [fstK_comp, fstK_id, fstK_shR, ← schemeHomOverComp_assoc, ← grj_comp_eq (shR' K f LXK e)
      (LXK.mul _ _ _),
      LXK.mul_natural,
      rd_fstK_comp, rd_sndK_comp, fstK_shR', sndK_shR', rd_comp_eInv,
      mul_inv_mul', rd_comp_eInv']
  · rw [sndK_comp, sndK_shR, sndK_id]; exact sndK_shR' K f LXK e

scoped instance isIso_shL : IsIso (shL K f LXK e).1 :=
  ⟨(shL' K f LXK e).1, congrArg Subtype.val (shL_comp_shL' K f LXK e), congrArg Subtype.val
    (shL'_comp_shL K f LXK e)⟩

scoped instance isIso_shR : IsIso (shR K f LXK e).1 :=
  ⟨(shR' K f LXK e).1, congrArg Subtype.val (shR_comp_shR' K f LXK e), congrArg Subtype.val
    (shR'_comp_shR K f LXK e)⟩

end Shear

section Pieces

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)

/-- Inclusion of an open multiplication domain. -/
abbrev incl (U : (pullback f f).Opens) : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) (pullback.fst f
    f ≫ f) :=
  ⟨U.ι, rfl⟩

/-- Multiplication transported to the generic fibre of the model. -/
def muK [IsIso e.1] : SchemeHomOver (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion
    R K))
    (pullback.snd f (specGenericFibreInclusion R K)) :=
  NeronModelInfra.schemeHomOverComp
    (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) (rd K f e (genericFibreRestrict R
      K f _ (prj₂ f))))
    (eInv K f e)

variable {K LXK f e}

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem mulRel_iff_eq_comp_muK [IsIso e.1] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (w : SchemeHomOver t (pullback.fst f f ≫ f)) (τ : SchemeHomOver t f) :
    MulRel K LXK f e (NeronModelInfra.schemeHomOverComp w (prj₁ f))
      (NeronModelInfra.schemeHomOverComp w (prj₂ f)) τ ↔
      genericFibreRestrict R K f t τ =
        NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K _ t w) (muK K LXK f e) := by
  have key : NeronModelInfra.schemeHomOverComp
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K _ t w) (muK K LXK f e)) e =
      LXK.mul _ (rd K f e (genericFibreRestrict R K f t (NeronModelInfra.schemeHomOverComp w (prj₁
        f))))
        (rd K f e (genericFibreRestrict R K f t (NeronModelInfra.schemeHomOverComp w (prj₂ f)))) :=
          by
    rw [muK, ← schemeHomOverComp_assoc, ← grj_comp_eq _ (LXK.mul _ _ _), LXK.mul_natural, grj_rd,
      grj_rd,
      ← genericFibreRestrict_schemeHomOverComp, ← genericFibreRestrict_schemeHomOverComp]
    exact rd_comp_eInv K f e _
  constructor
  · intro h
    apply comp_e_injective (e := e)
    rw [key]; exact h
  · intro h
    unfold MulRel
    rw [h, key]

end Pieces

section Main

theorem strictify
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hW₁ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W)
    (hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ W)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) :
    ∃ (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W),
      (∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X') ∧
      (∀ x : X, f.base x = IsLocalRing.closedPoint R →
        (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X') ∧
      (∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U) ∧
      (∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f
        f).base q ∈ X' ∧
        m.1.base ⟨q, hUW hq⟩ ∈ X') ∧
      (∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans
              (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans
              (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))) := by
  have : IsLocallyNoetherian (pullback f f) := LocallyOfFiniteType.isLocallyNoetherian
    (pullback.fst f f ≫ f)
  have : CompactSpace ↑(pullback f f) := QuasiCompact.compactSpace_of_compactSpace (pullback.fst f
    f ≫ f)
  set Φ := pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
    ((Category.assoc _ _ _).trans m.2.symm) with hΦdef
  set Ψ := pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
    (m.2.trans (by rw [Category.assoc, pullback.condition])) with hΨdef
  have : IsOpenImmersion Φ := hΦ
  have : IsOpenImmersion Ψ := hΨ
  have Φfst : Φ ≫ pullback.fst f f = W.ι ≫ pullback.fst f f := pullback.lift_fst _ _ _
  have Φsnd : Φ ≫ pullback.snd f f = m.1 := pullback.lift_snd _ _ _
  have Ψfst : Ψ ≫ pullback.fst f f = m.1 := pullback.lift_fst _ _ _
  have Ψsnd : Ψ ≫ pullback.snd f f = W.ι ≫ pullback.snd f f := pullback.lift_snd _ _ _
  have Φfst' : ∀ w, (pullback.fst f f).base (Φ.base w) = (pullback.fst f f).base (W.ι.base w) :=
    fun w => by
    rw [← Scheme.Hom.comp_apply, Φfst, Scheme.Hom.comp_apply]
  have Φsnd' : ∀ w, (pullback.snd f f).base (Φ.base w) = m.1.base w := fun w => by
    rw [← Scheme.Hom.comp_apply, Φsnd]
  have Ψfst' : ∀ w, (pullback.fst f f).base (Ψ.base w) = m.1.base w := fun w => by
    rw [← Scheme.Hom.comp_apply, Ψfst]
  have Ψsnd' : ∀ w, (pullback.snd f f).base (Ψ.base w) = (pullback.snd f f).base (W.ι.base w) :=
    fun w => by
    rw [← Scheme.Hom.comp_apply, Ψsnd, Scheme.Hom.comp_apply]
  have hcond : ∀ q : ↑(pullback f f), f.base ((pullback.fst f f).base q) = f.base ((pullback.snd f
    f).base q) :=
    fun q => by rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hmover : ∀ w : ↑W, f.base (m.1.base w) = f.base ((pullback.fst f f).base (W.ι.base w)) :=
    fun w => by
    rw [← Scheme.Hom.comp_apply, m.2, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  have hpf : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q = f.base ((pullback.fst f
    f).base q) :=
    fun q => Scheme.Hom.comp_apply _ _ q
  set σ : pullback f f ⟶ pullback f f := (pullbackSymmetry f f).hom with hσdef
  have σfst : ∀ q, (pullback.fst f f).base (σ.base q) = (pullback.snd f f).base q := fun q => by
    rw [← Scheme.Hom.comp_apply, hσdef, pullbackSymmetry_hom_comp_fst]
  have σsnd : ∀ q, (pullback.snd f f).base (σ.base q) = (pullback.fst f f).base q := fun q => by
    rw [← Scheme.Hom.comp_apply, hσdef, pullbackSymmetry_hom_comp_snd]
  have σσ' : σ ≫ σ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hσdef, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
        Category.id_comp]
    · rw [Category.assoc, hσdef, pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst,
        Category.id_comp]
  have σσ : ∀ q, σ.base (σ.base q) = q := fun q => by
    rw [← Scheme.Hom.comp_apply, σσ']; rfl
  let σh : ↑(pullback f f) ≃ₜ ↑(pullback f f) := Scheme.homeoOfIso (pullbackSymmetry f f)
  have σh_apply : ∀ q, σh q = σ.base q := fun q => rfl
  have hσover : σ ≫ pullback.fst f f ≫ f = pullback.fst f f ≫ f := by
    rw [hσdef, pullbackSymmetry_hom_comp_fst_assoc, pullback.condition]
  have σmax : ∀ q, IsMaxSp (pullback.fst f f ≫ f) q → IsMaxSp (pullback.fst f f ≫ f) (σ.base q) :=
    by
    intro q hq
    rw [← isMaxSp_comp_iff σ q, hσover]; exact hq
  have σF : ∀ a : X, σh '' {q | (pullback.fst f f).base q = a} = {q | (pullback.snd f f).base q =
    a} := by
    intro a; ext q; constructor
    · rintro ⟨q', hq', rfl⟩
      simpa only [Set.mem_ofPred_eq, σh_apply, σsnd] using hq'
    · intro hq
      exact ⟨σ.base q, by simpa only [Set.mem_ofPred_eq, σfst] using hq,
        by rw [σh_apply, σσ]⟩
  have σpre : ∀ T : Set X, σh '' ((fun q => (pullback.snd f f).base q) ⁻¹' T) =
      (fun q => (pullback.fst f f).base q) ⁻¹' T := by
    intro T; ext q; constructor
    · rintro ⟨q', hq', rfl⟩
      simpa only [Set.mem_preimage, σh_apply, σfst] using hq'
    · intro hq
      exact ⟨σ.base q, by simpa only [Set.mem_preimage, σsnd] using hq,
        by rw [σh_apply, σσ]⟩
  have relm : MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f W) (prj₁ f))
      (NeronModelInfra.schemeHomOverComp (incl f W) (prj₂ f)) m :=
    (mulRel_iff_display W m (prj₁ f) (prj₂ f)).mpr hmK
  let jP := pullback.fst (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
  let jW := pullback.fst (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
  have hgm : genericFibreRestrict R K f _ m =
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K _ _ (incl f W)) (muK K LXK f e) :=
    (mulRel_iff_eq_comp_muK (incl f W) m).mp relm
  have hjWm : jW ≫ m.1 = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ (muK K LXK f e).1 ≫
      pullback.fst f (specGenericFibreInclusion R K) := by
    rw [← genericFibreRestrict_coe_comp_fst R K f _ m, hgm, NeronModelInfra.schemeHomOverComp_coe,
      Category.assoc]
  have hjWι : jW ≫ W.ι = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ jP :=
    (genericFibreRestrict_coe_comp_fst R K _ _ (incl f W)).symm
  have hΦgen : jW ≫ Φ = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ (shL K f LXK e).1 ≫ jP := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, ← fstK_coe, fstK_shL,
        genericFibreRestrict_coe_comp_fst, reassoc_of% hjWι]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc, ← sndK_coe, sndK_shL,
        hjWm]
      rfl
  have hΨgen : jW ≫ Ψ = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ (shR K f LXK e).1 ≫ jP := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, ← fstK_coe, fstK_shR,
        hjWm]
      rfl
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc, ← sndK_coe, sndK_shR,
        genericFibreRestrict_coe_comp_fst, reassoc_of% hjWι]
  have hrange_gfr : ∀ q₁ : ↑(pullback (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)),
      q₁ ∈ Set.range (genericFibreRestrict R K _ _ (incl f W)).1.base := by
    intro q₁
    rw [genericFibreRestrict_coe_eq_pullbackMap _ _ (incl f W) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm), Scheme.Pullback.range_map]
    refine ⟨?_, ⟨(pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)).base q₁,
      by rfl⟩⟩
    change jP.base q₁ ∈ Set.range W.ι.base
    rw [Scheme.Opens.range_ι]
    apply hW₁
    have : jP.base q₁ ∈ Set.range jP.base := ⟨q₁, rfl⟩
    rwa [range_fst_specGenericFibreInclusion] at this
  have hgen_of : ∀ (Θ : (W : Scheme.{u}) ⟶ pullback f f)
      (sh : SchemeHomOver (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
        (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) [IsIso sh.1],
      jW ≫ Θ = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ sh.1 ≫ jP →
      ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R →
        q ∈ Set.range Θ.base := by
    intro Θ sh _ hgen q hq
    have hq' : q ∈ Set.range jP.base := by rw [range_fst_specGenericFibreInclusion]; exact hq
    obtain ⟨q₀, rfl⟩ := hq'
    obtain ⟨q₁, rfl⟩ := (Scheme.homeoOfIso (asIso sh.1)).surjective q₀
    obtain ⟨w₀, hw₀⟩ := hrange_gfr q₁
    refine ⟨jW.base w₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, hgen, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw₀]
    rfl
  have hgenΦ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R →
      q ∈ Set.range Φ.base := hgen_of Φ (shL K f LXK e) hΦgen
  have hgenΨ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R →
      q ∈ Set.range Ψ.base := hgen_of Ψ (shR K f LXK e) hΨgen
  let Z : (pullback f f).Opens := W ⊓ Φ.opensRange ⊓ Ψ.opensRange
  have hZcoe : (Z : Set ↑(pullback f f)) = Set.range W.ι.base ∩ Set.range Φ.base ∩ Set.range
    Ψ.base := by
    simp only [Z, TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι]
  have hZmax : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Z := by
    intro p h1 h2
    refine TopologicalSpace.Opens.mem_inf.mpr ⟨TopologicalSpace.Opens.mem_inf.mpr ⟨hW₂ p h1 h2,
      ?_⟩, ?_⟩
    · exact hΦ₂ p h1 h2
    · exact hΨ₂ p h1 h2
  have hZgen : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R →
    p ∈ Z := by
    intro p hp
    refine TopologicalSpace.Opens.mem_inf.mpr ⟨TopologicalSpace.Opens.mem_inf.mpr ⟨hW₁ p hp, ?_⟩,
      ?_⟩
    · exact hgenΦ p hp
    · exact hgenΨ p hp
  let Z' : (pullback f f).Opens := σ ⁻¹ᵁ Z
  have hZ'max : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Z' := by
    intro p h1 h2
    have h := σmax p ⟨h1, h2⟩
    exact hZmax _ h.1 h.2
  let F₁ : X → Set ↑(pullback f f) := fun a => {q | (pullback.fst f f).base q = a}
  let F₂ : X → Set ↑(pullback f f) := fun a => {q | (pullback.snd f f).base q = a}
  let G : Set X := {a | DenseIn (Z : Set ↑(pullback f f)) (F₁ a) ∧ DenseIn (Z : Set ↑(pullback f
    f)) (F₂ a)}
  let X' : X.Opens := ⟨interior G, isOpen_interior⟩
  have hX'G : ∀ a, a ∈ X' → a ∈ G := fun a ha => interior_subset ha
  have hGgen : ∀ a : X, f.base a ≠ IsLocalRing.closedPoint R → a ∈ G := by
    intro a ha
    constructor
    · refine DenseIn.of_subset fun q hq => hZgen q ?_
      rw [hpf]; change (pullback.fst f f).base q = a at hq; rw [hq]; exact ha
    · refine DenseIn.of_subset fun q hq => hZgen q ?_
      rw [hpf, hcond]; change (pullback.snd f f).base q = a at hq; rw [hq]; exact ha
  have hopen_gen : IsOpen {a : X | f.base a ≠ IsLocalRing.closedPoint R} := by
    have : IsClosed {a : X | f.base a = IsLocalRing.closedPoint R} :=
      (IsLocalRing.isClosed_singleton_closedPoint R).preimage f.continuous
    simpa only [Set.compl_ofPred, not_not] using this.isOpen_compl
  have hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X' := by
    intro x hx
    exact interior_maximal (fun a (ha : a ∈ {a : X | f.base a ≠ IsLocalRing.closedPoint R}) =>
      hGgen a ha)
      hopen_gen hx
  have hX'₂ : ∀ x : X, f.base x = IsLocalRing.closedPoint R →
      (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X' := by
    intro ξ hξ hξmax
    obtain ⟨N₁, hξN₁, hN₁⟩ :=
      NeronModelInfra.exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem f Z hZmax ξ
        hξ hξmax
    obtain ⟨N₂, hξN₂, hN₂⟩ :=
      NeronModelInfra.exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem f Z' hZ'max
        ξ hξ hξmax
    change ξ ∈ interior G
    rw [mem_interior]
    refine ⟨(N₁ : Set X) ∩ (N₂ : Set X), ?_, N₁.2.inter N₂.2, ⟨hξN₁, hξN₂⟩⟩
    rintro a ⟨ha₁, ha₂⟩
    by_cases has : f.base a = IsLocalRing.closedPoint R
    · constructor
      · exact (denseIn_setOf_iff (p := fun q => (pullback.fst f f).base q = a) (Z : Set ↑(pullback
          f f))).mpr
          (hN₁ a ha₁ has)
      · have h := (denseIn_setOf_iff (p := fun q => (pullback.fst f f).base q = a)
          (Z' : Set ↑(pullback f f))).mpr (hN₂ a ha₂ has)
        have h' := h.image_homeomorph σh
        rw [σF a] at h'
        refine h'.mono ?_
        rintro _ ⟨q, hq, rfl⟩
        exact hq
    · exact hGgen a has
  have hsndmax : ∀ (a : X), f.base a = IsLocalRing.closedPoint R → ∀ θ : ↑(pullback f f),
      (pullback.fst f f).base θ = a →
      (∀ y : ↑(pullback f f), (pullback.fst f f).base y = a → y ⤳ θ → y = θ) →
      (pullback.snd f f).base θ ∈ X' := by
    intro a ha θ hθa hθmax
    apply hX'₂
    · rw [← hcond, hθa]; exact ha
    · intro y hy hys
      obtain ⟨θ', hθ'θ, hθ'a, hθ'y⟩ :=
        NeronModelInfra.exists_specializes_fst_eq_snd_eq_of_specializes_snd f θ
          (by rw [hθa]; exact ha) y hy hys
      rw [← hθ'y, hθmax θ' (hθ'a.trans hθa) hθ'θ]
  have hD₃ : ∀ a : X, a ∈ X' → DenseIn ((fun q => (pullback.snd f f).base q) ⁻¹' (X' : Set X)) (F₁
    a) := by
    intro a ha
    by_cases has : f.base a = IsLocalRing.closedPoint R
    · apply DenseIn.of_forall_exists_specializes
      intro q hq
      obtain ⟨θ, hθa, hθq, hθmax⟩ := exists_fibre_maximal (pullback.fst f f) q
      change (pullback.fst f f).base q = a at hq
      rw [hq] at hθa hθmax
      exact ⟨θ, hθa, hsndmax a has θ hθa hθmax, hθq⟩
    · refine DenseIn.of_subset fun q hq => hX'₁ _ ?_
      change (pullback.fst f f).base q = a at hq
      rw [← hcond, hq]; exact has
  have hD₄ : ∀ a : X, a ∈ X' → DenseIn ((fun q => (pullback.fst f f).base q) ⁻¹' (X' : Set X)) (F₂
    a) := by
    intro a ha
    have h := (hD₃ a ha).image_homeomorph σh
    rwa [σF a, σpre] at h
  let UWo : (W : Scheme.{u}).Opens := (W.ι ≫ pullback.fst f f) ⁻¹ᵁ X' ⊓ (W.ι ≫ pullback.snd f f)
    ⁻¹ᵁ X' ⊓ m.1 ⁻¹ᵁ X'
  let U : (pullback f f).Opens := W.ι ''ᵁ UWo
  have hUcoe : (U : Set ↑(pullback f f)) = W.ι.base '' (UWo : Set ↑W) := rfl
  have hUWo : ∀ w : ↑W, w ∈ UWo ↔ (pullback.fst f f).base (W.ι.base w) ∈ X' ∧
      (pullback.snd f f).base (W.ι.base w) ∈ X' ∧ m.1.base w ∈ X' := by
    intro w
    simp only [UWo, TopologicalSpace.Opens.mem_inf, and_assoc]
    rfl
  have hUWocoe : (UWo : Set ↑W) = {w | (pullback.fst f f).base (W.ι.base w) ∈ (X' : Set X) ∧
      (pullback.snd f f).base (W.ι.base w) ∈ (X' : Set X) ∧ m.1.base w ∈ (X' : Set X)} := by
    ext w; exact hUWo w
  have hUW : U ≤ W := by
    rintro _ ⟨w, -, rfl⟩; exact w.2
  have hmemU : ∀ q : ↑(pullback f f), q ∈ U ↔ ∃ h : q ∈ W, (⟨q, h⟩ : ↑W) ∈ UWo := by
    intro q; constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩
    · rintro ⟨h, hw⟩; exact ⟨⟨q, h⟩, hw, rfl⟩
  have hU₃ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q
    ∈ U := by
    intro q hq
    let w : (W : Scheme.{u}) := ⟨q, hW₁ q hq⟩
    have h₁ : (pullback.fst f f).base (W.ι.base w) ∈ X' := hX'₁ _ hq
    have h₂ : (pullback.snd f f).base (W.ι.base w) ∈ X' :=
      hX'₁ _ (fun h => hq ((hcond q).trans h))
    have hm : f.base (m.1.base w) = (pullback.fst f f ≫ f).base q := hmover w
    have h₃ : m.1.base w ∈ X' := hX'₁ _ (fun h => hq (hm.symm.trans h))
    exact (hmemU q).mpr ⟨hW₁ q hq, (hUWo w).mpr ⟨h₁, h₂, h₃⟩⟩
  have hU₄ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧
      (pullback.snd f f).base q ∈ X' ∧ m.1.base ⟨q, hUW hq⟩ ∈ X' := by
    intro q hq
    obtain ⟨h, hw⟩ := (hmemU q).mp hq
    exact (hUWo _).mp hw
  have hpreU : {w : ↑W | W.ι.base w ∈ U} = (UWo : Set ↑W) := by
    ext w
    constructor
    · rintro ⟨w', hw', h⟩
      have : w' = w := W.ι.isOpenEmbedding.injective h
      rw [← this]; exact hw'
    · intro hw; exact ⟨w, hw, rfl⟩
  have hsix : ∀ a : X, a ∈ X' →
      DenseIn (U : Set ↑(pullback f f)) (F₁ a) ∧ DenseIn (U : Set ↑(pullback f f)) (F₂ a) ∧
      DenseIn (Φ.base '' {w : ↑W | W.ι.base w ∈ U}) (F₁ a) ∧ DenseIn (Φ.base '' {w : ↑W | W.ι.base
        w ∈ U}) (F₂ a) ∧
      DenseIn (Ψ.base '' {w : ↑W | W.ι.base w ∈ U}) (F₁ a) ∧ DenseIn (Ψ.base '' {w : ↑W | W.ι.base
        w ∈ U}) (F₂ a) := by
    intro a ha
    have hG := hX'G a ha
    rw [hpreU, hUcoe, hUWocoe]
    have key := six_denseIn (P := ↑(pullback f f)) (X := ↑X) (W := ↑W)
      (fun q => (pullback.fst f f).base q) (fun q => (pullback.snd f f).base q)
      (pullback.fst f f).continuous (pullback.snd f f).continuous
      (fun w => W.ι.base w) W.ι.isOpenEmbedding (fun w => m.1.base w) m.1.continuous
      (fun w => Φ.base w) (fun w => Ψ.base w) Φ.isOpenEmbedding.isInducing
        Ψ.isOpenEmbedding.isInducing
      Φfst' Φsnd' Ψfst' Ψsnd' (X' : Set X) X'.2 a ha
      (by rw [← hZcoe]; exact hG.1) (by rw [← hZcoe]; exact hG.2) (hD₃ a ha) (hD₄ a ha)
    exact key
  refine ⟨X', U, hUW, hX'₁, hX'₂, hU₃, hU₄, fun x hx => ?_⟩
  obtain ⟨d₁, d₂, d₃, d₄, d₅, d₆⟩ := hsix x hx
  exact ⟨(denseIn_setOf_iff _).mp d₁, (denseIn_setOf_iff _).mp d₂, (denseIn_setOf_iff _).mp d₃,
    (denseIn_setOf_iff _).mp d₄, (denseIn_setOf_iff _).mp d₅, (denseIn_setOf_iff _).mp d₆⟩

end Main

end PartialMultiplication

end
end AbelianVarieties.NOSProofs.AssociativityRestriction

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Topology

universe u

noncomputable section

open AbelianVarieties.NOSProofs.AssociativityRestriction

theorem exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hW₁ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W)
    (hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ W)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) :
    ∃ (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W),
      (∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X') ∧
      (∀ x : X, f.base x = IsLocalRing.closedPoint R →
        (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X') ∧
      (∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U) ∧
      (∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f
        f).base q ∈ X' ∧
        m.1.base ⟨q, hUW hq⟩ ∈ X') ∧
      (∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans
              (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans
              (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))) :=
  PartialMultiplication.strictify K LXK f e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂

end
end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension.lean
Upstream NOTICE:
    https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION:
    https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.AssociativityRestriction


noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace PartialMultiplication

open NeronModelInfra.DenseSliceLocus (exists_maximal_specializes exists_fibre_maximal)

section MaxPtsOuter

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

section MaxPts

variable {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R))

/-- The special fibre as a set of points. -/
def spFib : Set P := {x | p.base x = IsLocalRing.closedPoint R}

theorem isClosed_spFib : IsClosed (spFib p) :=
  (IsLocalRing.isClosed_singleton_closedPoint R).preimage p.base.hom.continuous

theorem IsMaxSp.isGenericPoint {x : P} (hx : IsMaxSp p x) {Z : Set P} (hZ : IsIrreducible Z)
    (hZs : Z ⊆ spFib p) (hxZ : x ∈ Z) : IsGenericPoint x (closure Z) := by
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hZ.closure isClosed_closure
  have hζx : ζ ⤳ x := hζ.specializes (subset_closure hxZ)
  have hζs : p.base ζ = IsLocalRing.closedPoint R := by
    have : ζ ∈ closure Z := hζ.mem
    exact (closure_minimal hZs (isClosed_spFib p)) this
  rwa [← hx.2 ζ hζx hζs]

theorem image_subset_spFib (Z : Set {x : P // p.base x = IsLocalRing.closedPoint R}) :
    Subtype.val '' Z ⊆ spFib p := by
  rintro _ ⟨z, -, rfl⟩; exact z.2

open Classical in
theorem finite_isMaxSp [IsLocallyNoetherian P] [CompactSpace P] : {x : P | IsMaxSp p x}.Finite := by
  have : IsNoetherian P := {}
  have : TopologicalSpace.NoetherianSpace {x : P // p.base x = IsLocalRing.closedPoint R} :=
    TopologicalSpace.NoetherianSpace.set (spFib p)
  let c : P → Set {x : P // p.base x = IsLocalRing.closedPoint R} := fun x =>
    if hx : p.base x = IsLocalRing.closedPoint R then
      irreducibleComponent (⟨x, hx⟩ : {x : P // p.base x = IsLocalRing.closedPoint R}) else ∅
  refine Set.Finite.of_finite_image (f := c) ?_ ?_
  · refine (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      (α := {x : P // p.base x = IsLocalRing.closedPoint R})).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [c, dite_eq_left hx.1]
    exact irreducibleComponent_mem_irreducibleComponents _
  · intro x hx y hy hxy
    have hx' : IsMaxSp p x := hx
    have hy' : IsMaxSp p y := hy
    simp only [c, dite_eq_left hx'.1, dite_eq_left hy'.1] at hxy
    have h1 := hx'.isGenericPoint p
      ((irreducibleComponent_mem_irreducibleComponents
        (⟨x, hx'.1⟩ : {x : P // p.base x = IsLocalRing.closedPoint R})).1.image _
        continuous_subtype_val.continuousOn) (image_subset_spFib p _) ⟨_, mem_irreducibleComponent,
          rfl⟩
    have h2 := hy'.isGenericPoint p
      ((irreducibleComponent_mem_irreducibleComponents
        (⟨y, hy'.1⟩ : {x : P // p.base x = IsLocalRing.closedPoint R})).1.image _
        continuous_subtype_val.continuousOn) (image_subset_spFib p _) ⟨_, mem_irreducibleComponent,
          rfl⟩
    rw [hxy] at h1
    exact h1.eq h2

theorem IsMaxSp.mem_of_forall_irreducibleComponents {x : P} (hx : IsMaxSp p x) (V : P.Opens)
    (hV : ∀ Z ∈ irreducibleComponents {x : P // p.base x = IsLocalRing.closedPoint R}, ∃ y ∈ Z, y.1
      ∈ V) :
    x ∈ V := by
  obtain ⟨y, hyZ, hyV⟩ := hV _ (irreducibleComponent_mem_irreducibleComponents
    (⟨x, hx.1⟩ : {x : P // p.base x = IsLocalRing.closedPoint R}))
  have hgen := hx.isGenericPoint p
    ((irreducibleComponent_mem_irreducibleComponents
      (⟨x, hx.1⟩ : {x : P // p.base x = IsLocalRing.closedPoint R})).1.image _
      continuous_subtype_val.continuousOn)
    (image_subset_spFib p _) ⟨_, mem_irreducibleComponent, rfl⟩
  have hxy : x ⤳ y.1 := hgen.specializes (subset_closure ⟨y, hyZ, rfl⟩)
  exact hxy.mem_open V.2 hyV

variable {p}

end MaxPts

end MaxPtsOuter

section Pieces

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)

variable {K LXK f e}
variable [IsIso e.1]

omit [IsDiscreteValuationRing R] in
theorem restrict_eq_restrict [IsSeparated f] [Flat f] {U U₁ U₂ : (pullback f f).Opens} (h₁ : U ≤
    U₁) (h₂ : U ≤ U₂)
    (τ₁ : SchemeHomOver (U₁.ι ≫ pullback.fst f f ≫ f) f) (τ₂ : SchemeHomOver (U₂.ι ≫ pullback.fst f
      f ≫ f) f)
    (r₁ : MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f U₁) (prj₁ f))
      (NeronModelInfra.schemeHomOverComp (incl f U₁) (prj₂ f)) τ₁)
    (r₂ : MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f U₂) (prj₁ f))
      (NeronModelInfra.schemeHomOverComp (incl f U₂) (prj₂ f)) τ₂) :
    (pullback f f).homOfLE h₁ ≫ τ₁.1 = (pullback f f).homOfLE h₂ ≫ τ₂.1 := by
  let l₁ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) (U₁.ι ≫ pullback.fst f f ≫ f) :=
    ⟨(pullback f f).homOfLE h₁, by rw [Scheme.homOfLE_ι_assoc]⟩
  let l₂ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) (U₂.ι ≫ pullback.fst f f ≫ f) :=
    ⟨(pullback f f).homOfLE h₂, by rw [Scheme.homOfLE_ι_assoc]⟩
  have e₁ : NeronModelInfra.schemeHomOverComp l₁ (incl f U₁) = incl f U := Subtype.ext ((pullback
    f f).homOfLE_ι h₁)
  have e₂ : NeronModelInfra.schemeHomOverComp l₂ (incl f U₂) = incl f U := Subtype.ext ((pullback
    f f).homOfLE_ι h₂)
  have r₁' := r₁.comp l₁
  have r₂' := r₂.comp l₂
  rw [← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc, e₁] at r₁'
  rw [← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc, e₂] at r₂'
  have h := NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K f
    (U.ι ≫ pullback.fst f f ≫ f) (r₁'.gfr_eq r₂')
  exact congrArg Subtype.val h

omit [IsFractionRing R K] [IsIso e.1] in
theorem exists_sigma_of_right
    (hR : ∀ η : ↑(pullback f f), IsMaxSp (pullback.fst f f ≫ f) η →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
          ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f U) (prj₂ f))
          (NeronModelInfra.schemeHomOverComp (incl f U) (prj₁ f)) τ)
    (η : ↑(pullback f f)) (hη : IsMaxSp (pullback.fst f f ≫ f) η) :
    ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (σ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
      IsOpenImmersion (pullback.lift (f := f) (g := f) σ.1 (U.ι ≫ pullback.snd f f)
        (σ.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f U) (prj₁ f))
        (NeronModelInfra.schemeHomOverComp (incl f U) (prj₂ f)) σ := by
  let s : pullback f f ⟶ pullback f f := (pullbackSymmetry f f).hom
  have hs : s ≫ pullback.fst f f ≫ f = pullback.fst f f ≫ f := by
    rw [pullbackSymmetry_hom_comp_fst_assoc, pullback.condition]
  have hsη : IsMaxSp (pullback.fst f f ≫ f) (s.base η) := by
    rw [← isMaxSp_comp_iff s η, hs]; exact hη
  obtain ⟨U', hηU', τ', oi', rel'⟩ := hR _ hsη
  refine ⟨s ⁻¹ᵁ U', hηU', ?_⟩
  let ψ : SchemeHomOver ((s ⁻¹ᵁ U').ι ≫ pullback.fst f f ≫ f) (U'.ι ≫ pullback.fst f f ≫ f) :=
    ⟨s ∣_ U', by rw [morphismRestrict_ι_assoc, hs]⟩
  refine ⟨NeronModelInfra.schemeHomOverComp ψ τ', ?_, ?_⟩
  · have heq : pullback.lift (f := f) (g := f) (NeronModelInfra.schemeHomOverComp ψ τ').1
        ((s ⁻¹ᵁ U').ι ≫ pullback.snd f f)
        ((NeronModelInfra.schemeHomOverComp ψ τ').2.trans
          (by rw [Category.assoc, pullback.condition])) =
        (s ∣_ U') ≫ pullback.lift (f := f) (g := f) (U'.ι ≫ pullback.fst f f) τ'.1
          ((Category.assoc _ _ _).trans τ'.2.symm) ≫ s := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst,
          pullback.lift_snd]
        rfl
      · rw [pullback.lift_snd, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd,
          pullback.lift_fst, morphismRestrict_ι_assoc, pullbackSymmetry_hom_comp_fst]
    rw [heq]
    infer_instance
  · have h1 : NeronModelInfra.schemeHomOverComp ψ (NeronModelInfra.schemeHomOverComp (incl f U')
      (prj₂ f)) =
        NeronModelInfra.schemeHomOverComp (incl f (s ⁻¹ᵁ U')) (prj₁ f) := by
      apply Subtype.ext
      change (s ∣_ U') ≫ U'.ι ≫ pullback.snd f f = (s ⁻¹ᵁ U').ι ≫ pullback.fst f f
      rw [morphismRestrict_ι_assoc, pullbackSymmetry_hom_comp_snd]
    have h2 : NeronModelInfra.schemeHomOverComp ψ (NeronModelInfra.schemeHomOverComp (incl f U')
      (prj₁ f)) =
        NeronModelInfra.schemeHomOverComp (incl f (s ⁻¹ᵁ U')) (prj₂ f) := by
      apply Subtype.ext
      change (s ∣_ U') ≫ U'.ι ≫ pullback.fst f f = (s ⁻¹ᵁ U').ι ≫ pullback.snd f f
      rw [morphismRestrict_ι_assoc, pullbackSymmetry_hom_comp_fst]
    have r := rel'.comp ψ
    rw [h1, h2] at r
    exact r

omit [IsDomain R] [IsDiscreteValuationRing R] [IsIso e.1] in
theorem injective_of_local {Y : Scheme.{u}} (Φ' : Y ⟶ pullback f f)
    (hcov : ∀ y : Y, ∃ (U : Scheme.{u}) (i : U ⟶ Y) (_ : IsOpenImmersion i), y ∈ i.opensRange ∧
      IsOpenImmersion (i ≫ Φ'))
    (hagree : ∀ (O : (pullback f f).Opens) (b b' : (O : Scheme.{u}) ⟶ Y), b ≫ Φ' = O.ι → b' ≫ Φ' =
      O.ι → b = b') :
    Function.Injective Φ'.base := by
  intro y y' hyy'
  obtain ⟨U, i, hi, ⟨u, rfl⟩, hio⟩ := hcov y
  obtain ⟨U', i', hi', ⟨u', rfl⟩, hio'⟩ := hcov y'
  let O : (pullback f f).Opens := (i ≫ Φ').opensRange ⊓ (i' ≫ Φ').opensRange
  have hO : Set.range O.ι.base ⊆ Set.range (i ≫ Φ').base := by
    rw [Scheme.Opens.range_ι]; exact fun _ hx => hx.1
  have hO' : Set.range O.ι.base ⊆ Set.range (i' ≫ Φ').base := by
    rw [Scheme.Opens.range_ι]; exact fun _ hx => hx.2
  let b : (O : Scheme.{u}) ⟶ Y := IsOpenImmersion.lift (i ≫ Φ') O.ι hO ≫ i
  let b' : (O : Scheme.{u}) ⟶ Y := IsOpenImmersion.lift (i' ≫ Φ') O.ι hO' ≫ i'
  have hb : b ≫ Φ' = O.ι := by rw [Category.assoc, IsOpenImmersion.lift_fac]
  have hb' : b' ≫ Φ' = O.ι := by rw [Category.assoc, IsOpenImmersion.lift_fac]
  have hbb' := hagree O b b' hb hb'
  have hq : Φ'.base (i.base u) ∈ O := ⟨⟨u, rfl⟩, ⟨u',
    by simpa only [Scheme.Hom.comp_apply] using hyy'.symm⟩⟩
  have h1 : b.base ⟨_, hq⟩ = i.base u := by
    change i.base ((IsOpenImmersion.lift (i ≫ Φ') O.ι hO).base ⟨_, hq⟩) = i.base u
    congr 1
    apply (i ≫ Φ').isOpenEmbedding.injective
    change ((IsOpenImmersion.lift (i ≫ Φ') O.ι hO) ≫ i ≫ Φ').base _ = _
    rw [IsOpenImmersion.lift_fac]
    rfl
  have h2 : b'.base ⟨_, hq⟩ = i'.base u' := by
    change i'.base ((IsOpenImmersion.lift (i' ≫ Φ') O.ι hO').base ⟨_, hq⟩) = i'.base u'
    congr 1
    apply (i' ≫ Φ').isOpenEmbedding.injective
    change ((IsOpenImmersion.lift (i' ≫ Φ') O.ι hO') ≫ i' ≫ Φ').base _ = _
    rw [IsOpenImmersion.lift_fac]
    exact hyy'
  rw [← h1, ← h2, hbb']

omit [IsIso e.1] in
theorem maximal_mem_range [IsLocallyNoetherian (pullback f f)] [CompactSpace ↑(pullback f f)]
    (W : (pullback f f).Opens) (Φ' : (W : Scheme.{u}) ⟶ pullback f f)
    [IsOpenImmersion Φ'] (hover : Φ' ≫ pullback.fst f f ≫ f = W.ι ≫ pullback.fst f f ≫ f)
    (hW : ∀ x, IsMaxSp (pullback.fst f f ≫ f) x → x ∈ W)
    (y : ↑(pullback f f)) (hy : IsMaxSp (pullback.fst f f ≫ f) y) : y ∈ Set.range Φ'.base := by
  have : Finite {x : ↑(pullback f f) // IsMaxSp (pullback.fst f f ≫ f) x} :=
    (finite_isMaxSp (pullback.fst f f ≫ f)).to_subtype
  let g : {x : ↑(pullback f f) // IsMaxSp (pullback.fst f f ≫ f) x} →
      {x : ↑(pullback f f) // IsMaxSp (pullback.fst f f ≫ f) x} := fun x =>
    let w : (W : Scheme.{u}) := ⟨x.1, hW x.1 x.2⟩
    ⟨Φ'.base w, by
      apply (isMaxSp_comp_iff (p := pullback.fst f f ≫ f) Φ' w).mp
      rw [hover]
      exact (isMaxSp_comp_iff W.ι w).mpr x.2⟩
  have hg : Function.Injective g := by
    intro x x' h
    have h' := Φ'.isOpenEmbedding.injective (congrArg Subtype.val h)
    have h'' := Subtype.ext_iff.mp h'
    exact Subtype.ext h''
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hg ⟨y, hy⟩
  exact ⟨_, congrArg Subtype.val hx⟩

end Pieces

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem extendMultiplication
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (hL : ∀ (η : ↑(pullback f f)), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion
          (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
              (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                  ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hR : ∀ (η : ↑(pullback f f)), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion
          (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
              (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                  ⟨pullback.snd f f, pullback.condition.symm⟩) e)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)).1) :
    ∃ (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f),
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R →
          y = p) →
        p ∈ W) ∧
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
        pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
            (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1 ∧
      IsOpenImmersion
        (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
          ((Category.assoc _ _ _).trans m.2.symm)) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R →
          y = p) →
        p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
          ((Category.assoc _ _ _).trans m.2.symm)).base) ∧
      IsOpenImmersion
        (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R →
          y = p) →
        p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) := by
  have : IsLocallyNoetherian (pullback f f) := LocallyOfFiniteType.isLocallyNoetherian
    (pullback.fst f f ≫ f)
  have : CompactSpace ↑(pullback f f) := QuasiCompact.compactSpace_of_compactSpace (pullback.fst f
    f ≫ f)
  have hL' : ∀ η : ↑(pullback f f), IsMaxSp (pullback.fst f f ≫ f) η →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
          ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f U) (prj₁ f))
          (NeronModelInfra.schemeHomOverComp (incl f U) (prj₂ f)) τ := by
    intro η hη
    obtain ⟨U, hηU, τ, oi, hτ⟩ := hL η hη.1 hη.2
    exact ⟨U, hηU, τ, oi, (mulRel_iff_display U τ (prj₁ f) (prj₂ f)).mpr hτ⟩
  have hR' : ∀ η : ↑(pullback f f), IsMaxSp (pullback.fst f f ≫ f) η →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
          ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f U) (prj₂ f))
          (NeronModelInfra.schemeHomOverComp (incl f U) (prj₁ f)) τ := by
    intro η hη
    obtain ⟨U, hηU, τ, oi, hτ⟩ := hR η hη.1 hη.2
    exact ⟨U, hηU, τ, oi, (mulRel_iff_display U τ (prj₂ f) (prj₁ f)).mpr hτ⟩
  have hσ := exists_sigma_of_right hR'
  have hloc : ∀ η : ↑(pullback f f), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) g).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K) (pullback.fst f
            f ≫ f)
            (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ (muK K
              LXK f e).1 := by
    intro η h1 h2
    obtain ⟨U, hηU, τ, -, rel⟩ := hL' η ⟨h1, h2⟩
    refine ⟨U, hηU, τ, ?_⟩
    rw [(mulRel_iff_eq_comp_muK (incl f U) τ).mp rel, NeronModelInfra.schemeHomOverComp_coe,
      genericFibreRestrict_coe_eq_pullbackMap _ _ (incl f U) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm)]
  obtain ⟨V, v, hV₁, hV₂, hvK⟩ :=
    NeronModelInfra.exists_opens_extension_of_forall_nhds_extension R K f (pullback.fst f f ≫ f)
      (muK K LXK f e)
      hloc
  have relv : MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f V) (prj₁ f))
      (NeronModelInfra.schemeHomOverComp (incl f V) (prj₂ f)) v := by
    rw [mulRel_iff_eq_comp_muK]
    apply Subtype.ext
    rw [hvK, NeronModelInfra.schemeHomOverComp_coe, genericFibreRestrict_coe_eq_pullbackMap _ _
      (incl f V)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)]
  have hVmax : ∀ x, IsMaxSp (pullback.fst f f ≫ f) x → x ∈ V := fun x hx =>
    hx.mem_of_forall_irreducibleComponents _ V hV₂
  choose UL hUL τL oiL relL using hL'
  choose UR hUR σR oiR relR using hσ
  let jP := pullback.fst (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
  let Wη : ∀ η : ↑(pullback f f), IsMaxSp (pullback.fst f f ≫ f) η → (pullback f f).Opens :=
    fun η h => V ⊓ UL η h ⊓ UR η h
  let W : (pullback f f).Opens :=
    (V ⊓ jP.opensRange) ⊔ ⨆ (η : ↑(pullback f f)) (h : IsMaxSp (pullback.fst f f ≫ f) η), Wη η h
  have hWV : W ≤ V := sup_le inf_le_left (iSup₂_le fun η h => inf_le_left.trans inf_le_left)
  have hWηW : ∀ η h, Wη η h ≤ W := fun η h =>
    (le_iSup₂ (f := fun η (h : IsMaxSp (pullback.fst f f ≫ f) η) => Wη η h) η h).trans le_sup_right
  have hWηL : ∀ η h, Wη η h ≤ UL η h := fun η h => inf_le_left.trans inf_le_right
  have hWηR : ∀ η h, Wη η h ≤ UR η h := fun η h => inf_le_right
  let lWV : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) (V.ι ≫ pullback.fst f f ≫ f) :=
    ⟨(pullback f f).homOfLE hWV, by rw [Scheme.homOfLE_ι_assoc]⟩
  let m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f := NeronModelInfra.schemeHomOverComp lWV v
  have relm : MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f W) (prj₁ f))
      (NeronModelInfra.schemeHomOverComp (incl f W) (prj₂ f)) m := by
    have h := relv.comp lWV
    have e₁ : NeronModelInfra.schemeHomOverComp lWV (incl f V) = incl f W :=
      Subtype.ext ((pullback f f).homOfLE_ι hWV)
    rw [← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc, e₁] at h
    exact h
  have hW₁ : ∀ x : ↑(pullback f f), (pullback.fst f f ≫ f).base x ≠ IsLocalRing.closedPoint R → x
    ∈ W := by
    intro x hx
    apply TopologicalSpace.Opens.mem_sup.mpr
    left
    have hx' : x ∈ Set.range jP.base := by rw [range_fst_specGenericFibreInclusion]; exact hx
    exact TopologicalSpace.Opens.mem_inf.mpr ⟨hV₁ x hx, hx'⟩
  have hW₂ : ∀ x : ↑(pullback f f), IsMaxSp (pullback.fst f f ≫ f) x → x ∈ W := fun x hx =>
    hWηW x hx (TopologicalSpace.Opens.mem_inf.mpr
      ⟨TopologicalSpace.Opens.mem_inf.mpr ⟨hVmax x hx, hUL x hx⟩, hUR x hx⟩)
  let Φ := pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1 ((Category.assoc _ _
    _).trans m.2.symm)
  let Ψ := pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
    (m.2.trans (by rw [Category.assoc, pullback.condition]))
  have hΦloc : ∀ η h, IsOpenImmersion ((pullback f f).homOfLE (hWηW η h) ≫ Φ) := by
    intro η h
    have heq : (pullback f f).homOfLE (hWηW η h) ≫ Φ =
        (pullback f f).homOfLE (hWηL η h) ≫ pullback.lift (f := f) (g := f) ((UL η h).ι ≫
          pullback.fst f f)
          (τL η h).1 ((Category.assoc _ _ _).trans (τL η h).2.symm) := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst,
          Scheme.homOfLE_ι_assoc,
          Scheme.homOfLE_ι_assoc]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
        exact restrict_eq_restrict (hWηW η h) (hWηL η h) m (τL η h) relm (relL η h)
    rw [heq]
    have : IsOpenImmersion (pullback.lift (f := f) (g := f)
        ((UL η h).ι ≫ pullback.fst f f) (τL η h).1
        ((Category.assoc _ _ _).trans (τL η h).2.symm)) := oiL η h
    infer_instance
  have hΨloc : ∀ η h, IsOpenImmersion ((pullback f f).homOfLE (hWηW η h) ≫ Ψ) := by
    intro η h
    have heq : (pullback f f).homOfLE (hWηW η h) ≫ Ψ =
        (pullback f f).homOfLE (hWηR η h) ≫ pullback.lift (f := f) (g := f) (σR η h).1
          ((UR η h).ι ≫ pullback.snd f f) ((σR η h).2.trans
            (by rw [Category.assoc, pullback.condition])) := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
        exact restrict_eq_restrict (hWηW η h) (hWηR η h) m (σR η h) relm (relR η h)
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd,
          Scheme.homOfLE_ι_assoc,
          Scheme.homOfLE_ι_assoc]
    rw [heq]
    have : IsOpenImmersion (pullback.lift (f := f) (g := f)
        (σR η h).1 ((UR η h).ι ≫ pullback.snd f f)
        ((σR η h).2.trans (by rw [Category.assoc, pullback.condition]))) := oiR η h
    infer_instance
  let jW := pullback.fst (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
  have hgfW : IsOpenImmersion (genericFibreRestrict R K _ _ (incl f W)).1 := by
    rw [genericFibreRestrict_coe_eq_pullbackMap _ _ (incl f W) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstanceAs (IsOpenImmersion
      W.ι))
      (inferInstanceAs (IsOpenImmersion (𝟙 _))) rfl (Category.id_comp _).symm
  have hgm : genericFibreRestrict R K f _ m =
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K _ _ (incl f W)) (muK K LXK f e) :=
    (mulRel_iff_eq_comp_muK (incl f W) m).mp relm
  have hjWm : jW ≫ m.1 = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ (muK K LXK f e).1 ≫
      pullback.fst f (specGenericFibreInclusion R K) := by
    rw [← genericFibreRestrict_coe_comp_fst R K f _ m, hgm, NeronModelInfra.schemeHomOverComp_coe,
      Category.assoc]
  have hjWι : jW ≫ W.ι = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ jP :=
    (genericFibreRestrict_coe_comp_fst R K _ _ (incl f W)).symm
  have hΦgen : jW ≫ Φ = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ (shL K f LXK e).1 ≫ jP := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, ← fstK_coe, fstK_shL,
        genericFibreRestrict_coe_comp_fst, reassoc_of% hjWι]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc, ← sndK_coe, sndK_shL,
        hjWm]
      rfl
  have hΨgen : jW ≫ Ψ = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ (shR K f LXK e).1 ≫ jP := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, ← fstK_coe, fstK_shR,
        hjWm]
      rfl
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc, ← sndK_coe, sndK_shR,
        genericFibreRestrict_coe_comp_fst, reassoc_of% hjWι]
  have hΦgen' : IsOpenImmersion (jW ≫ Φ) := by rw [hΦgen]; infer_instance
  have hΨgen' : IsOpenImmersion (jW ≫ Ψ) := by rw [hΨgen]; infer_instance
  have hcov : ∀ (Θ : (W : Scheme.{u}) ⟶ pullback f f), IsOpenImmersion (jW ≫ Θ) →
      (∀ η h, IsOpenImmersion ((pullback f f).homOfLE (hWηW η h) ≫ Θ)) →
      ∀ y : ↑W, ∃ (U : Scheme.{u}) (i : U ⟶ W) (_ : IsOpenImmersion i), y ∈ i.opensRange ∧
        IsOpenImmersion (i ≫ Θ) := by
    intro Θ hgen hloc' y
    rcases TopologicalSpace.Opens.mem_sup.mp y.2 with hy | hy
    · refine ⟨_, jW, inferInstance, ?_, hgen⟩
      change y ∈ Set.range jW.base
      rw [range_fst_specGenericFibreInclusion]
      have hy2 : y.1 ∈ Set.range jP.base := (TopologicalSpace.Opens.mem_inf.mp hy).2
      rw [range_fst_specGenericFibreInclusion] at hy2
      exact hy2
    · obtain ⟨η, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
      obtain ⟨hη, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
      refine ⟨_, (pullback f f).homOfLE (hWηW η hη), inferInstance, ?_, hloc' η hη⟩
      exact ⟨⟨y.1, hy⟩, by rw [Scheme.homOfLE_apply']; exact Subtype.ext rfl⟩
  have hagreeΦ : ∀ (O : (pullback f f).Opens) (b b' : (O : Scheme.{u}) ⟶ W), b ≫ Φ = O.ι → b' ≫ Φ
    = O.ι →
      b = b' := by
    intro O b b' hb hb'
    have hbf : ∀ {b : (O : Scheme.{u}) ⟶ W}, b ≫ Φ = O.ι → (b ≫ W.ι) ≫ pullback.fst f f = O.ι ≫
      pullback.fst f f :=
      fun {b} hb => by rw [← hb, Category.assoc, Category.assoc, pullback.lift_fst]
    have hbm : ∀ {b : (O : Scheme.{u}) ⟶ W}, b ≫ Φ = O.ι → b ≫ m.1 = O.ι ≫ pullback.snd f f :=
      fun {b} hb => by rw [← hb, Category.assoc, pullback.lift_snd]
    have key : ∀ (b : (O : Scheme.{u}) ⟶ W) (hb : b ≫ Φ = O.ι),
        MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f O) (prj₁ f))
          (NeronModelInfra.schemeHomOverComp (⟨b ≫ W.ι,
            by rw [Category.assoc, reassoc_of% (hbf hb)]⟩ :
            SchemeHomOver (O.ι ≫ pullback.fst f f ≫ f) (pullback.fst f f ≫ f)) (prj₂ f))
          (NeronModelInfra.schemeHomOverComp (incl f O) (prj₂ f)) := by
      intro b hb
      let bO : SchemeHomOver (O.ι ≫ pullback.fst f f ≫ f) (W.ι ≫ pullback.fst f f ≫ f) :=
        ⟨b, by rw [reassoc_of% (hbf hb)]⟩
      have h := relm.comp bO
      have e₁ : NeronModelInfra.schemeHomOverComp bO (NeronModelInfra.schemeHomOverComp (incl f W)
        (prj₁ f)) =
          NeronModelInfra.schemeHomOverComp (incl f O) (prj₁ f) := Subtype.ext
            (by
              change b ≫ (W.ι ≫ pullback.fst f f) =
                O.ι ≫ pullback.fst f f
              simpa only [Category.assoc] using hbf hb)
      have e₂ : NeronModelInfra.schemeHomOverComp bO m = NeronModelInfra.schemeHomOverComp (incl f
        O) (prj₂ f) :=
        Subtype.ext (hbm hb)
      rw [e₁, e₂, ← schemeHomOverComp_assoc] at h
      exact h
    have hτ := (key b hb).gfr_snd_eq (key b' hb') rfl rfl
    have h2 := congrArg Subtype.val
      (NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K f (O.ι ≫
        pullback.fst f f ≫ f) hτ)
    simp only [NeronModelInfra.schemeHomOverComp_coe] at h2
    rw [← cancel_mono W.ι]
    apply pullback.hom_ext
    · rw [hbf hb, hbf hb']
    · simpa only [Category.assoc] using h2
  have hagreeΨ : ∀ (O : (pullback f f).Opens) (b b' : (O : Scheme.{u}) ⟶ W), b ≫ Ψ = O.ι → b' ≫ Ψ
    = O.ι →
      b = b' := by
    intro O b b' hb hb'
    have hbs : ∀ {b : (O : Scheme.{u}) ⟶ W}, b ≫ Ψ = O.ι → (b ≫ W.ι) ≫ pullback.snd f f = O.ι ≫
      pullback.snd f f :=
      fun {b} hb => by rw [← hb, Category.assoc, Category.assoc, pullback.lift_snd]
    have hbm : ∀ {b : (O : Scheme.{u}) ⟶ W}, b ≫ Ψ = O.ι → b ≫ m.1 = O.ι ≫ pullback.fst f f :=
      fun {b} hb => by rw [← hb, Category.assoc, pullback.lift_fst]
    have hover : ∀ {b : (O : Scheme.{u}) ⟶ W}, b ≫ Ψ = O.ι →
        (b ≫ W.ι) ≫ pullback.fst f f ≫ f = O.ι ≫ pullback.fst f f ≫ f := fun {b} hb => by
      rw [pullback.condition, Category.assoc, reassoc_of% (hbs hb)]
    have key : ∀ (b : (O : Scheme.{u}) ⟶ W) (hb : b ≫ Ψ = O.ι),
        MulRel K LXK f e
          (NeronModelInfra.schemeHomOverComp (⟨b ≫ W.ι, hover hb⟩ :
            SchemeHomOver (O.ι ≫ pullback.fst f f ≫ f) (pullback.fst f f ≫ f)) (prj₁ f))
          (NeronModelInfra.schemeHomOverComp (incl f O) (prj₂ f))
          (NeronModelInfra.schemeHomOverComp (incl f O) (prj₁ f)) := by
      intro b hb
      let bO : SchemeHomOver (O.ι ≫ pullback.fst f f ≫ f) (W.ι ≫ pullback.fst f f ≫ f) :=
        ⟨b, by rw [← Category.assoc]; exact hover hb⟩
      have h := relm.comp bO
      have e₁ : NeronModelInfra.schemeHomOverComp bO (NeronModelInfra.schemeHomOverComp (incl f W)
        (prj₂ f)) =
          NeronModelInfra.schemeHomOverComp (incl f O) (prj₂ f) := Subtype.ext
            (by
              change b ≫ (W.ι ≫ pullback.snd f f) =
                O.ι ≫ pullback.snd f f
              simpa only [Category.assoc] using hbs hb)
      have e₂ : NeronModelInfra.schemeHomOverComp bO m = NeronModelInfra.schemeHomOverComp (incl f
        O) (prj₁ f) :=
        Subtype.ext (hbm hb)
      rw [e₁, e₂, ← schemeHomOverComp_assoc] at h
      exact h
    have hτ := (key b hb).gfr_fst_eq (key b' hb') rfl rfl
    have h2 := congrArg Subtype.val
      (NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K f (O.ι ≫
        pullback.fst f f ≫ f) hτ)
    simp only [NeronModelInfra.schemeHomOverComp_coe] at h2
    rw [← cancel_mono W.ι]
    apply pullback.hom_ext
    · simpa only [Category.assoc] using h2
    · rw [hbs hb, hbs hb']
  have hΦ : IsOpenImmersion Φ :=
    IsOpenImmersion.of_forall_source_exists Φ (injective_of_local Φ (hcov Φ hΦgen' hΦloc) hagreeΦ)
      (hcov Φ hΦgen' hΦloc)
  have hΨ : IsOpenImmersion Ψ :=
    IsOpenImmersion.of_forall_source_exists Ψ (injective_of_local Ψ (hcov Ψ hΨgen' hΨloc) hagreeΨ)
      (hcov Ψ hΨgen' hΨloc)
  refine ⟨W, m, hW₁, fun x h1 h2 => hW₂ x ⟨h1, h2⟩, (mulRel_iff_display W m (prj₁ f) (prj₂ f)).mp
    relm, hΦ,
    fun y h1 h2 => ?_, hΨ, fun y h1 h2 => ?_⟩
  · exact maximal_mem_range W Φ (by rw [pullback.lift_fst_assoc, Category.assoc]) hW₂ y ⟨h1, h2⟩
  · exact maximal_mem_range W Ψ (by rw [pullback.lift_fst_assoc, m.2]) hW₂ y ⟨h1, h2⟩

end Main

end PartialMultiplication

end
end AbelianVarieties.NOSProofs.AssociativityRestriction

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Topology

universe u

noncomputable section

open AbelianVarieties.NOSProofs.AssociativityRestriction

theorem exists_partial_multiplication_of_translation_charts
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (hL : ∀ (η : ↑(pullback f f)), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion
          (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
              (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                  ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hR : ∀ (η : ↑(pullback f f)), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion
          (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
              (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                  ⟨pullback.snd f f, pullback.condition.symm⟩) e)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)).1) :
    ∃ (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f),
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R →
          y = p) →
        p ∈ W) ∧
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
        pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
            (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1 ∧
      IsOpenImmersion
        (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
          ((Category.assoc _ _ _).trans m.2.symm)) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R →
          y = p) →
        p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
          ((Category.assoc _ _ _).trans m.2.symm)).base) ∧
      IsOpenImmersion
        (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R →
          y = p) →
        p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) :=
  PartialMultiplication.extendMultiplication K LXK f e hL hR

end
end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_opens_relativeGroupLaw_isOpenImmersion_genericFibre_iso_of_isOpenImmersion_lift_mul_of_henselianLocalRing.lean
Upstream NOTICE:
    https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION:
    https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem exists_groupLaw_of_partial_multiplication
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hXk : ∃ x : X, f.base x = IsLocalRing.closedPoint R)
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hW₁ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W)
    (hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ W)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) :
    ∃ (X' : X.Opens) (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (jY : SchemeHomOver (X'.ι ≫ f) g) (e' : SchemeHomOver (pullback.snd g
        (specGenericFibreInclusion R K)) gK),
      (∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X') ∧
      (∀ x : X, f.base x = IsLocalRing.closedPoint R →
        (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X') ∧
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
      IsOpenImmersion jY.1 ∧
      (∀ b : B, g.base b ≠ IsLocalRing.closedPoint R → b ∈ Set.range jY.1.base) ∧
      (∀ b : B, g.base b = IsLocalRing.closedPoint R →
        (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range jY.1.base) ∧
      IsIso e'.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
          LXK.mul t (NeronModelInfra.schemeHomOverComp x e') (NeronModelInfra.schemeHomOverComp y
            e')) ∧
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g (X'.ι ≫ f) jY) e' =
        NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e :=
          by
  obtain ⟨X', U, hUW, hX'₁, hX'₂, hU₁, hU₂, hU₃⟩ :=
    NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul
      K LXK f e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂
  obtain ⟨B, g, LB, jY, e', hg₁, hg₂, hg₃, hg₄, hjY, hjY₁, hjY₂, he', hhom, hcompat, -⟩ :=
    NeronModelInfra.exists_groupLaw_of_dense_fibres
      K LXK f hXk e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂ X' U hUW hX'₁ hX'₂ hU₁ hU₂ hU₃
  exact ⟨X', B, g, LB, jY, e', hX'₁, hX'₂, hg₁, hg₂, hg₃, hg₄, hjY, hjY₁, hjY₂, he', hhom, hcompat⟩

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative.lean
Upstream NOTICE:
    https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION:
    https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.TranslationGroupLaw


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace TranslationExtension

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Base change of the open model embedding. -/
noncomputable def prodMap {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g) :
    pullback z f ⟶ pullback z g :=
  pullback.map z f z g (𝟙 Z) j.1 (𝟙 _) ((Category.comp_id _).trans (Category.id_comp z).symm)
    ((Category.comp_id _).trans j.2.symm)

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[reassoc (attr := simp)]
theorem prodMap_fst {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g) :
    prodMap z f g j ≫ pullback.fst z g = pullback.fst z f := by
  rw [prodMap, pullback.map, pullback.lift_fst, Category.comp_id]

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[reassoc (attr := simp)]
theorem prodMap_snd {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g) :
    prodMap z f g j ≫ pullback.snd z g = pullback.snd z f ≫ j.1 := by
  rw [prodMap, pullback.map, pullback.lift_snd]

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem isOpenImmersion_prodMap {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g)
    [IsOpenImmersion j.1] : IsOpenImmersion (prodMap z f g j) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) (IsOpenImmersion.of_isIso (𝟙 Z)) ‹_›
    (Category.id_comp z).symm j.2.symm

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem range_prodMap {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g) :
    Set.range (prodMap z f g j).base = (pullback.snd z g).base ⁻¹' Set.range j.1.base := by
  have h := Scheme.Pullback.range_map z f z g (𝟙 Z) j.1 (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp z).symm) ((Category.comp_id _).trans j.2.symm)
  change Set.range (prodMap z f g j).base = _ at h
  rw [h]
  have hid : Set.range (𝟙 Z) = Set.univ :=
    Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩
  rw [hid, Set.preimage_univ, Set.univ_inter]

theorem exists_preimage_maximal {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g)
    [IsOpenImmersion j.1]
    (hj₂ : ∀ b : B, g.base b = IsLocalRing.closedPoint R →
      (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range j.1.base)
    (η' : ↑(pullback z g)) (hη' : (pullback.fst z g ≫ z).base η' = IsLocalRing.closedPoint R)
    (hmax' : ∀ y : ↑(pullback z g), y ⤳ η' → (pullback.fst z g ≫ z).base y =
      IsLocalRing.closedPoint R →
      y = η') :
    ∃ η : ↑(pullback z f), (prodMap z f g j).base η = η' ∧
      (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R ∧
      (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y
        = η) := by
  have : IsOpenImmersion (prodMap z f g j) := isOpenImmersion_prodMap z f g j
  have hb : g.base ((pullback.snd z g).base η') = IsLocalRing.closedPoint R := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition]; exact hη'
  have hbmax : ∀ y : B, y ⤳ (pullback.snd z g).base η' → g.base y = IsLocalRing.closedPoint R →
      y = (pullback.snd z g).base η' := by
    intro y hy hys
    obtain ⟨x, hx, hxy⟩ := Flat.generalizingMap (pullback.snd z g) hy
    have hxs : (pullback.fst z g ≫ z).base x = IsLocalRing.closedPoint R := by
      rw [pullback.condition, Scheme.Hom.comp_apply, hxy]; exact hys
    rw [← hxy, hmax' x hx hxs]
  have hmem : η' ∈ Set.range (prodMap z f g j).base := by
    rw [range_prodMap]
    exact hj₂ _ hb hbmax
  obtain ⟨η, hη⟩ := hmem
  refine ⟨η, hη, ?_, ?_⟩
  · rw [← prodMap_fst z f g j, Category.assoc, Scheme.Hom.comp_apply, hη]; exact hη'
  · intro y hy hys
    apply (prodMap z f g j).isOpenEmbedding.injective
    rw [hη]
    apply hmax' _ ((hy.map (prodMap z f g j).base.hom.continuous).trans (hη ▸ specializes_rfl))
    rw [← prodMap_fst z f g j, Category.assoc, Scheme.Hom.comp_apply] at hys
    exact hys

/-- Base change of the open embedding as a morphism over the base. -/
noncomputable def prodMapOver {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g) :
    SchemeHomOver (pullback.fst z f ≫ z) (pullback.fst z g ≫ z) :=
  ⟨prodMap z f g j, by rw [prodMap_fst_assoc]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[scoped simp]
theorem prodMapOver_coe {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g) :
    (prodMapOver z f g j).1 = prodMap z f g j :=
  rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem transport_twistK
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (LB : RelativeGroupLaw R g) (j : SchemeHomOver f g)
    (e' : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
      NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
        LXK.mul t (NeronModelInfra.schemeHomOverComp x e') (NeronModelInfra.schemeHomOverComp y e'))
    (hcompat : NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g f j) e' = e)
    (uK' : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
      (pullback.snd g (specGenericFibreInclusion R K))) :
    NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K (pullback.fst z g ≫ z) (pullback.fst z f ≫ z) (prodMapOver z f g
          j))
        (NeronModelInfra.schemeHomOverComp
          ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z) (specGenericFibreInclusion
            R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK')
            (genericFibreRestrict R K g (pullback.fst z g ≫ z)
              ⟨pullback.snd z g, pullback.condition.symm⟩)) e') =
      LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩)
          (NeronModelInfra.schemeHomOverComp uK' e'))
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (pullback.fst z f ≫ z) ⟨pullback.snd z f,
            pullback.condition.symm⟩)
          e) := by
  have h1 : NeronModelInfra.schemeHomOverComp (prodMapOver z f g j)
      (⟨pullback.fst z g, rfl⟩ : SchemeHomOver (pullback.fst z g ≫ z) z) =
        (⟨pullback.fst z f, rfl⟩ : SchemeHomOver (pullback.fst z f ≫ z) z) :=
    Subtype.ext (prodMap_fst z f g j)
  have h2 : NeronModelInfra.schemeHomOverComp (prodMapOver z f g j)
      (⟨pullback.snd z g, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst z g ≫ z) g) =
        NeronModelInfra.schemeHomOverComp
          (⟨pullback.snd z f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst z f ≫ z) f) j
            :=
    Subtype.ext (prodMap_snd z f g j)
  rw [hhom]
  have hnat : ∀ (a b : SchemeHomOver (pullback.snd (pullback.fst z g ≫ z)
    (specGenericFibreInclusion R K)) gK),
      NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K (pullback.fst z g ≫ z) (pullback.fst z f ≫ z) (prodMapOver z f g
          j))
        (LXK.mul _ a b) =
      LXK.mul _
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K (pullback.fst z g ≫ z) (pullback.fst z f ≫ z) (prodMapOver z f
            g j)) a)
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K (pullback.fst z g ≫ z) (pullback.fst z f ≫ z) (prodMapOver z f
            g j)) b) := by
    intro a b
    exact LXK.mul_natural _ _ _
      (genericFibreRestrict R K (pullback.fst z g ≫ z) (pullback.fst z f ≫ z) (prodMapOver z f g
        j)).2 a b
  rw [hnat]
  congr 1
  · rw [← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc, ←
      genericFibreRestrict_schemeHomOverComp, h1,
      schemeHomOverComp_assoc]
  · rw [← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp, h2,
      genericFibreRestrict_schemeHomOverComp, schemeHomOverComp_assoc, hcompat]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem genericFibreRestrict_fst_assoc {P Q W : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R))
    (q : Q ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver q p) (h : P ⟶ W) :
    (genericFibreRestrict R K p q φ).1 ≫ pullback.fst p (specGenericFibreInclusion R K) ≫ h =
      pullback.fst q (specGenericFibreInclusion R K) ≫ φ.1 ≫ h := by
  rw [← Category.assoc, genericFibreRestrict_coe_comp_fst, Category.assoc]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem restrict_comp_genericFibre {P P' : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R))
    (p' : P' ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver p p') (U : P.Opens) (U' : P'.Opens)
    (ψ : SchemeHomOver (U'.ι ≫ p') (U.ι ≫ p)) (hψ : ψ.1 ≫ U.ι ≫ φ.1 = U'.ι) :
    (genericFibreRestrict R K (U.ι ≫ p) (U'.ι ≫ p') ψ).1 ≫
      pullback.map (U.ι ≫ p) (specGenericFibreInclusion R K) p (specGenericFibreInclusion R K) U.ι
        (𝟙 _)
        (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
      (genericFibreRestrict R K p' p φ).1 =
    pullback.map (U'.ι ≫ p') (specGenericFibreInclusion R K) p' (specGenericFibreInclusion R K)
      U'.ι (𝟙 _)
        (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      genericFibreRestrict_coe_comp_fst,
      genericFibreRestrict_fst_assoc, hψ]
  · simp only [Category.assoc, pullback.lift_snd, genericFibreRestrict_coe_comp_snd,
      Category.comp_id]

omit [IsFractionRing R K] in
theorem twist
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (LB : RelativeGroupLaw R g) (j : SchemeHomOver f g) [IsOpenImmersion j.1]
    (hj₂ : ∀ b : B, g.base b = IsLocalRing.closedPoint R →
      (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range j.1.base)
    (e' : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK) [IsIso e'.1]
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
      NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
        LXK.mul t (NeronModelInfra.schemeHomOverComp x e') (NeronModelInfra.schemeHomOverComp y e'))
    (hcompat : NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g f j) e' = e)
    (hL : ∀ (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
      (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y
        = η) →
      ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
              (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                  ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (uK' : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
      (pullback.snd g (specGenericFibreInclusion R K)))
    (η' : ↑(pullback z g)) (hη' : (pullback.fst z g ≫ z).base η' = IsLocalRing.closedPoint R)
    (hmax' : ∀ y : ↑(pullback z g), y ⤳ η' → (pullback.fst z g ≫ z).base y =
      IsLocalRing.closedPoint R →
      y = η') :
    ∃ (U' : (pullback z g).Opens) (_ : η' ∈ U') (τ' : SchemeHomOver (U'.ι ≫ pullback.fst z g ≫ z)
      g),
      (genericFibreRestrict R K g (U'.ι ≫ pullback.fst z g ≫ z) τ').1 =
        pullback.map (U'.ι ≫ pullback.fst z g ≫ z) (specGenericFibreInclusion R K)
            (pullback.fst z g ≫ z) (specGenericFibreInclusion R K) U'.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z) (specGenericFibreInclusion
            R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK')
            (genericFibreRestrict R K g (pullback.fst z g ≫ z)
              ⟨pullback.snd z g, pullback.condition.symm⟩)).1 := by
  have : IsOpenImmersion (prodMap z f g j) := isOpenImmersion_prodMap z f g j
  obtain ⟨η, hη, hηs, hηmax⟩ := exists_preimage_maximal z f g j hj₂ η' hη' hmax'
  obtain ⟨U, hηU, τ, hτK⟩ := hL (NeronModelInfra.schemeHomOverComp uK' e') η hηs hηmax
  have hinv : ((prodMap z f g j).isoImage U).inv ≫ U.ι ≫ prodMap z f g j = ((prodMap z f g j) ''ᵁ
    U).ι :=
    (prodMap z f g j).isoImage_inv_ι U
  let ψ : SchemeHomOver (((prodMap z f g j) ''ᵁ U).ι ≫ pullback.fst z g ≫ z) (U.ι ≫ pullback.fst z
    f ≫ z) :=
    ⟨((prodMap z f g j).isoImage U).inv,
      by rw [← hinv, Category.assoc, Category.assoc, prodMap_fst_assoc]⟩
  refine ⟨(prodMap z f g j) ''ᵁ U, ?_,
    NeronModelInfra.schemeHomOverComp ψ (NeronModelInfra.schemeHomOverComp τ j), ?_⟩
  · rw [← hη]; exact ⟨η, hηU, rfl⟩
  rw [← cancel_mono e'.1]
  have hgen : genericFibreRestrict R K g _
      (NeronModelInfra.schemeHomOverComp ψ (NeronModelInfra.schemeHomOverComp τ j)) =
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K _ _ ψ)
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f _ τ)
          (genericFibreRestrict R K g f j)) := by
    rw [genericFibreRestrict_schemeHomOverComp, genericFibreRestrict_schemeHomOverComp]
  have hτK' := hτK
  rw [NeronModelInfra.schemeHomOverComp_coe,
    show e.1 = (genericFibreRestrict R K g f j).1 ≫ e'.1 by
      rw [← hcompat, NeronModelInfra.schemeHomOverComp_coe]] at hτK'
  have htr := congrArg Subtype.val (transport_twistK K LXK z f g e LB j e' hhom hcompat uK')
  simp only [NeronModelInfra.schemeHomOverComp_coe] at htr
  rw [hgen]
  simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
  rw [hτK', ← htr,
    ← restrict_comp_genericFibre K (pullback.fst z f ≫ z) (pullback.fst z g ≫ z) (prodMapOver z f g
      j) U _ ψ
      hinv]
  simp only [Category.assoc]

end TranslationExtension

namespace TranslationExtension

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem map_maximal {P Q : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R)) (q : Q ⟶ Spec
    (CommRingCat.of R))
    (φ : SchemeHomOver p q) [IsOpenImmersion φ.1] (η : P) (hη : p.base η = IsLocalRing.closedPoint
      R)
    (hmax : ∀ y : P, y ⤳ η → p.base y = IsLocalRing.closedPoint R → y = η) :
    q.base (φ.1.base η) = IsLocalRing.closedPoint R ∧
      ∀ y : Q, y ⤳ φ.1.base η → q.base y = IsLocalRing.closedPoint R → y = φ.1.base η := by
  refine ⟨by rw [← Scheme.Hom.comp_apply, φ.2]; exact hη, fun y hy hys => ?_⟩
  obtain ⟨y₁, rfl⟩ : y ∈ Set.range φ.1.base := hy.mem_open (IsOpenImmersion.isOpen_range φ.1) ⟨η,
    rfl⟩
  rw [hmax y₁ ((φ.1.isOpenEmbedding.isInducing.specializes_iff).1 hy)
    (by rw [← φ.2, Scheme.Hom.comp_apply]; exact hys)]

theorem maximal_of_opens {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R)) (U : P.Opens) (η : P)
    (hηU : η ∈ U)
    (hmax : ∀ y : P, y ⤳ η → p.base y = IsLocalRing.closedPoint R → y = η) :
    ∀ y : ↑U, y ⤳ (⟨η, hηU⟩ : ↑U) → (U.ι ≫ p).base y = IsLocalRing.closedPoint R → y = ⟨η, hηU⟩ :=
      by
  intro y hy hys
  apply U.ι.isOpenEmbedding.injective
  have h := hmax (U.ι.base y) (hy.map U.ι.base.hom.continuous)
    (by rw [← Scheme.Hom.comp_apply]; exact hys)
  exact h

theorem snd_maximal {Z X : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (f : X ⟶ Spec (CommRingCat.of R)) (θ : ↑(pullback z f))
    (hθ : (pullback.fst z f ≫ z).base θ = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ θ → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint
      R → y = θ) :
    f.base ((pullback.snd z f).base θ) = IsLocalRing.closedPoint R ∧
      ∀ y : X, y ⤳ (pullback.snd z f).base θ → f.base y = IsLocalRing.closedPoint R →
        y = (pullback.snd z f).base θ := by
  refine ⟨by rw [← Scheme.Hom.comp_apply, ← pullback.condition]; exact hθ, fun y hy hys => ?_⟩
  obtain ⟨x, hx, hxy⟩ := Flat.generalizingMap (pullback.snd z f) hy
  have hxs : (pullback.fst z f ≫ z).base x = IsLocalRing.closedPoint R := by
    rw [pullback.condition, Scheme.Hom.comp_apply, hxy]; exact hys
  rw [← hxy, hmax x hx hxs]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem genericFibre_comp_restrict {P P' : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R))
    (p' : P' ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver p' p) (U : P.Opens) (U' : P'.Opens)
    (ψ : SchemeHomOver (U'.ι ≫ p') (U.ι ≫ p)) (hψ : ψ.1 ≫ U.ι = U'.ι ≫ φ.1) :
    (genericFibreRestrict R K (U.ι ≫ p) (U'.ι ≫ p') ψ).1 ≫
      pullback.map (U.ι ≫ p) (specGenericFibreInclusion R K) p (specGenericFibreInclusion R K) U.ι
        (𝟙 _)
        (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
    pullback.map (U'.ι ≫ p') (specGenericFibreInclusion R K) p' (specGenericFibreInclusion R K)
      U'.ι (𝟙 _)
        (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
      (genericFibreRestrict R K p p' φ).1 := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, genericFibreRestrict_coe_comp_fst,
      genericFibreRestrict_fst_assoc, pullback.lift_fst_assoc, hψ]
  · simp only [Category.assoc, pullback.lift_snd, genericFibreRestrict_coe_comp_snd,
      Category.comp_id]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem transport_mulK
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {Z X : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) (X' : X.Opens)
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK) :
    NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K (pullback.fst z f ≫ z) (pullback.fst z (X'.ι ≫ f) ≫ z)
          (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩))
        (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst z f ≫ z) ⟨pullback.snd z f,
              pullback.condition.symm⟩)
            e)) =
      LXK.mul (pullback.snd (pullback.fst z (X'.ι ≫ f) ≫ z) (specGenericFibreInclusion R K))
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K z (pullback.fst z (X'.ι ≫ f) ≫ z) ⟨pullback.fst z (X'.ι ≫ f),
            rfl⟩) uK)
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K (X'.ι ≫ f) (pullback.fst z (X'.ι ≫ f) ≫ z)
            ⟨pullback.snd z (X'.ι ≫ f), pullback.condition.symm⟩)
          (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩)
            e)) := by
  have h1 : NeronModelInfra.schemeHomOverComp (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)
      (⟨pullback.fst z f, rfl⟩ : SchemeHomOver (pullback.fst z f ≫ z) z) =
        (⟨pullback.fst z (X'.ι ≫ f), rfl⟩ : SchemeHomOver (pullback.fst z (X'.ι ≫ f) ≫ z) z) :=
    Subtype.ext (prodMap_fst z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)
  have h2 : NeronModelInfra.schemeHomOverComp (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)
      (⟨pullback.snd z f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst z f ≫ z) f) =
        NeronModelInfra.schemeHomOverComp
          (⟨pullback.snd z (X'.ι ≫ f), pullback.condition.symm⟩ :
            SchemeHomOver (pullback.fst z (X'.ι ≫ f) ≫ z) (X'.ι ≫ f))
          (⟨X'.ι, rfl⟩ : SchemeHomOver (X'.ι ≫ f) f) :=
    Subtype.ext (prodMap_snd z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)
  have hnat : ∀ (a b : SchemeHomOver (pullback.snd (pullback.fst z f ≫ z)
    (specGenericFibreInclusion R K)) gK),
      NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K (pullback.fst z f ≫ z) (pullback.fst z (X'.ι ≫ f) ≫ z)
          (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩))
        (LXK.mul _ a b) =
      LXK.mul _
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K (pullback.fst z f ≫ z) (pullback.fst z (X'.ι ≫ f) ≫ z)
            (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)) a)
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K (pullback.fst z f ≫ z) (pullback.fst z (X'.ι ≫ f) ≫ z)
            (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)) b) := by
    intro a b
    exact LXK.mul_natural _ _ _
      (genericFibreRestrict R K (pullback.fst z f ≫ z) (pullback.fst z (X'.ι ≫ f) ≫ z)
        (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)).2 a b
  rw [hnat]
  congr 1
  · rw [← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp, h1]
  · rw [← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp, h2,
      genericFibreRestrict_schemeHomOverComp, schemeHomOverComp_assoc]

omit [IsFractionRing R K] in
theorem restrict_translation
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {Z X : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (f : X ⟶ Spec (CommRingCat.of R)) (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion
      R K)) gK)
    (X' : X.Opens)
    (hX'₂ : ∀ x : X, f.base x = IsLocalRing.closedPoint R →
      (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X')
    (hL : ∀ (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
      (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y
        = η) →
      ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
        IsOpenImmersion
          (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
              (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                  ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η₁ : ↑(pullback z (X'.ι ≫ f)))
    (hη₁ : (pullback.fst z (X'.ι ≫ f) ≫ z).base η₁ = IsLocalRing.closedPoint R)
    (hmax₁ : ∀ y : ↑(pullback z (X'.ι ≫ f)), y ⤳ η₁ →
      (pullback.fst z (X'.ι ≫ f) ≫ z).base y = IsLocalRing.closedPoint R → y = η₁) :
    ∃ (U₁ : (pullback z (X'.ι ≫ f)).Opens) (_ : η₁ ∈ U₁)
      (τ₁ : SchemeHomOver (U₁.ι ≫ pullback.fst z (X'.ι ≫ f) ≫ z) (X'.ι ≫ f)),
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K (X'.ι ≫ f) (U₁.ι ≫ pullback.fst z (X'.ι ≫ f) ≫ z) τ₁)
          (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩)
            e)).1 =
        pullback.map (U₁.ι ≫ pullback.fst z (X'.ι ≫ f) ≫ z) (specGenericFibreInclusion R K)
            (pullback.fst z (X'.ι ≫ f) ≫ z) (specGenericFibreInclusion R K) U₁.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst z (X'.ι ≫ f) ≫ z) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K z (pullback.fst z (X'.ι ≫ f) ≫ z) ⟨pullback.fst z (X'.ι ≫
                f), rfl⟩) uK)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K (X'.ι ≫ f) (pullback.fst z (X'.ι ≫ f) ≫ z)
                ⟨pullback.snd z (X'.ι ≫ f), pullback.condition.symm⟩)
              (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι,
                rfl⟩) e))).1 := by
  have hQ : IsOpenImmersion (prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩) := isOpenImmersion_prodMap z
    (X'.ι ≫ f) f _
  have hQ' : IsOpenImmersion (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).1 := hQ
  obtain ⟨hη, hmax⟩ := map_maximal (pullback.fst z (X'.ι ≫ f) ≫ z) (pullback.fst z f ≫ z)
    (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩) η₁ hη₁ hmax₁
  simp only [prodMapOver_coe] at hη hmax
  obtain ⟨U, hηU, τ, hoi, hτK⟩ := hL uK _ hη hmax
  let u : (U : Scheme.{u}) := ⟨(prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).base η₁, hηU⟩
  have hτη : τ.1.base u ∈ X' := by
    let Φ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) (pullback.fst z f ≫ z) :=
      ⟨pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1 ((Category.assoc _ _ _).trans
        τ.2.symm),
        by rw [pullback.lift_fst_assoc, Category.assoc]⟩
    have : IsOpenImmersion Φ.1 := hoi
    have hu : (U.ι ≫ pullback.fst z f ≫ z).base u = IsLocalRing.closedPoint R := hη
    obtain ⟨hθ, hθmax⟩ := map_maximal (U.ι ≫ pullback.fst z f ≫ z)
      (pullback.fst z f ≫ z) Φ u hu
      (maximal_of_opens (pullback.fst z f ≫ z) U _ hηU hmax)
    obtain ⟨hs, hsmax⟩ := snd_maximal z f _ hθ hθmax
    have hΦsnd : Φ.1 ≫ pullback.snd z f = τ.1 := pullback.lift_snd _ _ _
    have hsnd : (pullback.snd z f).base (Φ.1.base u) = τ.1.base u :=
      congrArg (fun h : (U : Scheme.{u}) ⟶ X => h.base u) hΦsnd
    rw [hsnd] at hs hsmax
    exact hX'₂ _ hs hsmax
  let V : (↑U : Scheme.{u}).Opens := τ.1 ⁻¹ᵁ X'
  let U₀ : (pullback z f).Opens := U.ι ''ᵁ V
  let U₁ : (pullback z (X'.ι ≫ f)).Opens := (prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩) ⁻¹ᵁ U₀
  have hη₁U₁ : η₁ ∈ U₁ := by
    change (prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).base η₁ ∈ U.ι ''ᵁ V
    exact ⟨⟨_, hηU⟩, hτη, rfl⟩
  have hr₁ : Set.range (U₁.ι ≫ prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).base ⊆ Set.range U.ι.base := by
    rintro _ ⟨u₁, rfl⟩
    obtain ⟨v, -, hv⟩ : (prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).base (U₁.ι.base u₁) ∈ (U₀ : Set _) :=
      u₁.2
    exact ⟨v, by rw [Scheme.Hom.comp_apply]; exact hv⟩
  let l₁ : (↑U₁ : Scheme.{u}) ⟶ ↑U := IsOpenImmersion.lift U.ι (U₁.ι ≫ prodMap z (X'.ι ≫ f) f
    ⟨X'.ι, rfl⟩) hr₁
  have hl₁ : l₁ ≫ U.ι = U₁.ι ≫ prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩ := IsOpenImmersion.lift_fac _ _ _
  have hl₁V : ∀ u₁ : ↑U₁, l₁.base u₁ ∈ V := by
    intro u₁
    obtain ⟨v, hvV, hv⟩ : (prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).base (U₁.ι.base u₁) ∈ (U₀ : Set _)
      := u₁.2
    have : v = l₁.base u₁ := by
      apply U.ι.isOpenEmbedding.injective
      have h' : U.ι.base (l₁.base u₁) = (prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).base (U₁.ι.base u₁)
        := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hl₁]
      exact hv.trans h'.symm
    exact this ▸ hvV
  have hr₂ : Set.range (l₁ ≫ τ.1).base ⊆ Set.range X'.ι.base := by
    rintro _ ⟨u₁, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hl₁V u₁
  let τv : (↑U₁ : Scheme.{u}) ⟶ ↑X' := IsOpenImmersion.lift X'.ι (l₁ ≫ τ.1) hr₂
  have hτv : τv ≫ X'.ι = l₁ ≫ τ.1 := IsOpenImmersion.lift_fac _ _ _
  let lam : SchemeHomOver (U₁.ι ≫ pullback.fst z (X'.ι ≫ f) ≫ z) (U.ι ≫ pullback.fst z f ≫ z) :=
    ⟨l₁, by rw [reassoc_of% hl₁, prodMap_fst_assoc]⟩
  let τ₁ : SchemeHomOver (U₁.ι ≫ pullback.fst z (X'.ι ≫ f) ≫ z) (X'.ι ≫ f) :=
    ⟨τv, by rw [reassoc_of% hτv, τ.2, reassoc_of% hl₁, prodMap_fst_assoc]⟩
  have hτ₁ : NeronModelInfra.schemeHomOverComp τ₁ (⟨X'.ι, rfl⟩ : SchemeHomOver (X'.ι ≫ f) f) =
      NeronModelInfra.schemeHomOverComp lam τ :=
    Subtype.ext hτv
  refine ⟨U₁, hη₁U₁, τ₁, ?_⟩
  have htr := congrArg Subtype.val (transport_mulK K LXK z f e X' uK)
  simp only [NeronModelInfra.schemeHomOverComp_coe] at htr
  rw [← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp, hτ₁,
    genericFibreRestrict_schemeHomOverComp, schemeHomOverComp_assoc,
      NeronModelInfra.schemeHomOverComp_coe, hτK,
    reassoc_of% (genericFibre_comp_restrict K (pullback.fst z f ≫ z) (pullback.fst z (X'.ι ≫ f) ≫ z)
      (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩) U U₁ lam hl₁), htr]

theorem main [HenselianLocalRing R]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK) (hcomm : LXK.IsCommutative)
    (M : ModelFamily R K gK) (hfin : Finite M.ι)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
      IsIso e.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e =
          LXK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y
            e)) ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
          (pullback.snd g (specGenericFibreInclusion R K)))
        (η : ↑(pullback z g)), (pullback.fst z g ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z g), y ⤳ η → (pullback.fst z g ≫ z).base y = IsLocalRing.closedPoint R →
          y = η) →
        ∃ (U : (pullback z g).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z g ≫ z) g),
          (genericFibreRestrict R K g (U.ι ≫ pullback.fst z g ≫ z) τ).1 =
            pullback.map (U.ι ≫ pullback.fst z g ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z g ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z)
                (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK)
                (genericFibreRestrict R K g (pullback.fst z g ≫ z)
                  ⟨pullback.snd z g, pullback.condition.symm⟩)).1) := by
  obtain ⟨X, f, e, hsm, hsep, hloft, hqc, hXk, he, hL, hR⟩ :=
    NeronModelInfra.exists_model_with_translation_charts
      K LXK hcomm M hfin hM hpts
  have : Smooth f := hsm
  have : IsSeparated f := hsep
  have : LocallyOfFiniteType f := hloft
  have : QuasiCompact f := hqc
  have : IsIso e.1 := he
  obtain ⟨W, m, hW₁, hW₂, hmK, hΦ, hΦ₂, hΨ, hΨ₂⟩ :=
    NeronModelInfra.exists_partial_multiplication_of_translation_charts
      K LXK f e (hL X f e) (hR X f e)
  obtain ⟨X', B, g, LB, jY, e', -, hX'₂, hg₁, hg₂, hg₃, hg₄, hjY, -, hjY₂, he', hhom, hcompat⟩ :=
    NeronModelInfra.exists_groupLaw_of_partial_multiplication
      K LXK f hXk e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂
  have : IsOpenImmersion jY.1 := hjY
  have : IsIso e'.1 := he'
  refine ⟨B, g, LB, e', hg₁, hg₂, hg₃, hg₄, he', hhom, ?_⟩
  intro Z z _ _ uK' η' hη' hmax'
  exact twist K LXK z (X'.ι ≫ f) g
    (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e) LB jY
      hjY₂ e'
    hhom hcompat (restrict_translation K LXK z f e X' hX'₂ (fun uK η hηs hηmax => hL Z z uK η hηs
      hηmax))
    uK' η' hη' hmax'

end TranslationExtension

end AbelianVarieties.NOSProofs.TranslationGroupLaw

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Topology

universe u

noncomputable section

open AbelianVarieties.NOSProofs.TranslationGroupLaw

theorem exists_groupLaw_with_translation_extensions
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK) (hcomm : LXK.IsCommutative)
    (M : ModelFamily R K gK) (hfin : Finite M.ι)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
      IsIso e.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e =
          LXK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y
            e)) ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
          (pullback.snd g (specGenericFibreInclusion R K)))
        (η : ↑(pullback z g)), (pullback.fst z g ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z g), y ⤳ η → (pullback.fst z g ≫ z).base y = IsLocalRing.closedPoint R →
          y = η) →
        ∃ (U : (pullback z g).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z g ≫ z) g),
          (genericFibreRestrict R K g (U.ι ≫ pullback.fst z g ≫ z) τ).1 =
            pullback.map (U.ι ≫ pullback.fst z g ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z g ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z)
                (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK)
                (genericFibreRestrict R K g (pullback.fst z g ≫ z)
                  ⟨pullback.snd z g, pullback.condition.symm⟩)).1) :=
  TranslationExtension.main K LXK hcomm M hfin hM hpts

end
end NeronModelInfra
end
