/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.NoetherianSpace
public import Nyll.AbelianVarieties.NeronModels.Density
public import Nyll.AbelianVarieties.NeronModels.GluingDensity
public import Nyll.AbelianVarieties.NeronModels.QuasiFiniteGluing
public import Nyll.SchemeTheory.LocalGeometry.Normality
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.LocalGeometry.SmoothNormalStalk
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced
public import Nyll.SchemeTheory.Sheaves.IdealSheafDataReducedSubschemeVanishingIdealLeKer

/-!
# Separated models from translation charts

Glue two open charts, prove separation using their graph intersection, and retain dense
partial multiplication after gluing. The reduced graph and fibre-density calculus are shared
with the existing construction modules.
-/

@[expose] public section

private def fieldPoint (k : Type*) [Field k] :
    ↥(AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  IsLocalRing.closedPoint k

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open AbelianVarieties.NOSProofs.QuasiFiniteTranslationGluing.TranslationGluing
  (exists_lift_of_isClosedImmersion dense_fibre_jA)
open AbelianVarieties.NOSProofs.GluingFibreDensity.TranslationCharts
  (mem_of_dense_of_forall_specializes)

namespace AbelianVarieties.NOSProofs.SeparatedTranslationGluing

namespace SeparatedCharts

section General

variable {A B C : Scheme.{u}} (f : A ⟶ B) (g : A ⟶ C) [IsOpenImmersion f] [IsOpenImmersion g]

theorem isOpenImmersion_inl : IsOpenImmersion (pushout.inl f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) .left))

theorem isOpenImmersion_inr : IsOpenImmersion (pushout.inr f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) .right))

theorem inl_eq_inr_iff (b : B) (c : C) :
    (pushout.inl f g).base b = (pushout.inr f g).base c ↔ ∃ x : A, f.base x = b ∧ g.base x = c := by
  refine (Scheme.IsLocallyDirected.ι_eq_ι_iff (span f g) (i := .left) (j := .right) (xi := b)
    (xj := c)).trans ?_
  constructor
  · rintro ⟨k, fi, fj, x, h1, h2⟩
    obtain - | k := fi
    · obtain - | - := fj
    · obtain - | - := fj
      exact ⟨x, h1, h2⟩
  · rintro ⟨x, h1, h2⟩
    exact ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, x, h1, h2⟩

theorem inl_or_inr (p : ↑(pushout f g)) :
    p ∈ Set.range (pushout.inl f g).base ∨ p ∈ Set.range (pushout.inr f g).base := by
  obtain ⟨i, xi, h⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) p
  obtain - | i := i
  · left
    refine ⟨f.base xi, ?_⟩
    rw [← h]
    change (colimit.ι (span f g) WalkingSpan.left).base (((span f g).map WalkingSpan.Hom.fst).base
      xi) = _
    rw [← Scheme.Hom.comp_apply, colimit.w]
  · cases i with
    | left => exact Or.inl ⟨xi, h⟩
    | right => exact Or.inr ⟨xi, h⟩

theorem isPullback_inl_inr : IsPullback f g (pushout.inl f g) (pushout.inr f g) := by
  have : IsOpenImmersion (pushout.inl f g) := isOpenImmersion_inl f g
  have : IsOpenImmersion (pushout.inr f g) := isOpenImmersion_inr f g
  have hrange : Set.range (pullback.snd (pushout.inl f g) (pushout.inr f g)).base = Set.range g.base
    := by
    rw [Scheme.Pullback.range_snd]
    ext c
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨x, -, hx⟩ := (inl_eq_inr_iff f g b c).mp hb
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨f.base x, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]⟩
  let e : A ≅ pullback (pushout.inl f g) (pushout.inr f g) :=
    (IsOpenImmersion.isoOfRangeEq g (pullback.snd (pushout.inl f g) (pushout.inr f g)) hrange.symm)
  have he : e.hom ≫ pullback.snd _ _ = g := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  refine IsPullback.of_iso_pullback ⟨pushout.condition⟩ e ?_ he
  rw [← cancel_mono (pushout.inl f g), Category.assoc, pullback.condition, ← Category.assoc, he,
    pushout.condition]

end General

section Data

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y)
variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)

/-- The triple fibre product containing the multiplication graph. -/
abbrev Y3 : Scheme.{u} := pullback (pullback.fst y y ≫ y) y

/-- The projection onto the first two coordinates. -/
abbrev p12 : Y3 y ⟶ pullback y y := pullback.fst (pullback.fst y y ≫ y) y

/-- The projection onto the first and third coordinates. -/
abbrev p13 : Y3 y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y)
    (pullback.snd (pullback.fst y y ≫ y) y) (by rw [Category.assoc]; exact pullback.condition)

/-- The projection onto the second and third coordinates. -/
abbrev p23 : Y3 y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y)
    (pullback.snd (pullback.fst y y ≫ y) y)
    (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)

/-- Insert the chosen section as the first coordinate. -/
abbrev jA : Y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (y ≫ a) (𝟙 Y) (by rw [Category.assoc, ha, Category.comp_id,
    Category.id_comp])

/-- Insert the section into the multiplication graph. -/
abbrev sA : pullback y y ⟶ Y3 y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y)
    (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
      (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
    (pullback.snd y y)
    (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
      pullback.condition])

/-- The graph restricted to multiplication by the chosen section. -/
abbrev Ga : Scheme.{u} := pullback γ (sA y a ha)

/-- The coordinate map of the restricted multiplication graph. -/
abbrev cA : Ga y γ a ha ⟶ pullback y y := pullback.snd γ (sA y a ha)

/-- The first chart projection of the restricted graph. -/
def pτ : Ga y γ a ha ⟶ Y := cA y γ a ha ≫ pullback.fst y y

/-- The second chart projection of the restricted graph. -/
def pι : Ga y γ a ha ⟶ Y := cA y γ a ha ≫ pullback.snd y y

theorem pτ_def : pτ y γ a ha = cA y γ a ha ≫ pullback.fst y y := rfl

theorem pι_def : pι y γ a ha = cA y γ a ha ≫ pullback.snd y y := rfl

theorem sA_p12 : sA y a ha ≫ p12 y = pullback.fst y y ≫ jA y a ha := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [pullback.lift_fst, Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]

theorem sA_p13 : sA y a ha ≫ p13 y = pullback.snd y y ≫ jA y a ha := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst,
    Category.assoc,
      pullback.lift_fst, ← Category.assoc, pullback.condition, Category.assoc]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, pullback.lift_snd,
      Category.comp_id]

theorem sA_p23 : sA y a ha ≫ p23 y = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd,
    Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

theorem isPullback_sA_fst : IsPullback (sA y a ha) (pullback.fst y y) (p12 y) (jA y a ha) := by
  have comm : sA y a ha ≫ p12 y = pullback.fst y y ≫ jA y a ha := sA_p12 y a ha
  have c1 : pullback.fst (p12 y) (jA y a ha) ≫ p12 y ≫ pullback.fst y y =
      pullback.snd (p12 y) (jA y a ha) ≫ y ≫ a := by
    rw [← Category.assoc, pullback.condition, Category.assoc, pullback.lift_fst]
  have c2 : pullback.fst (p12 y) (jA y a ha) ≫ p12 y ≫ pullback.snd y y =
      pullback.snd (p12 y) (jA y a ha) := by
    rw [← Category.assoc, pullback.condition, Category.assoc, pullback.lift_snd, Category.comp_id]
  have key : pullback.fst (p12 y) (jA y a ha) ≫ p23 y ≫ sA y a ha = pullback.fst (p12 y) (jA y a ha)
    := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [reassoc_of% c2, c1]
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · simp only [Category.assoc, pullback.lift_snd]
  let e : pullback y y ≅ pullback (p12 y) (jA y a ha) :=
    { hom := pullback.lift (sA y a ha) (pullback.fst y y) comm
      inv := pullback.fst (p12 y) (jA y a ha) ≫ p23 y
      hom_inv_id := by rw [pullback.lift_fst_assoc, sA_p23]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, pullback.lift_fst, key, Category.id_comp]
        · rw [Category.assoc, Category.assoc, pullback.lift_snd, Category.id_comp,
          pullback.lift_fst]
          exact c2 }
  exact IsPullback.of_iso_pullback ⟨comm⟩ e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem isPullback_sA_snd : IsPullback (sA y a ha) (pullback.snd y y) (p13 y) (jA y a ha) := by
  have comm : sA y a ha ≫ p13 y = pullback.snd y y ≫ jA y a ha := sA_p13 y a ha
  have c1 : pullback.fst (p13 y) (jA y a ha) ≫ p12 y ≫ pullback.fst y y =
      pullback.snd (p13 y) (jA y a ha) ≫ y ≫ a := by
    have := pullback.condition (f := p13 y) (g := jA y a ha)
    have h2 := congrArg (· ≫ pullback.fst y y) this
    simp only [Category.assoc, pullback.lift_fst] at h2
    exact h2
  have c2 : pullback.fst (p13 y) (jA y a ha) ≫ pullback.snd (pullback.fst y y ≫ y) y =
      pullback.snd (p13 y) (jA y a ha) := by
    have := pullback.condition (f := p13 y) (g := jA y a ha)
    have h2 := congrArg (· ≫ pullback.snd y y) this
    simp only [Category.assoc, pullback.lift_snd, Category.comp_id] at h2
    exact h2
  have key : pullback.fst (p13 y) (jA y a ha) ≫ p23 y ≫ sA y a ha = pullback.fst (p13 y) (jA y a ha)
    := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [← Category.assoc (pullback.snd y y) y a, ← pullback.condition (f := y) (g := y),
          pullback.condition_assoc, reassoc_of% c2]
        exact c1.symm
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · simp only [Category.assoc, pullback.lift_snd]
  let e : pullback y y ≅ pullback (p13 y) (jA y a ha) :=
    { hom := pullback.lift (sA y a ha) (pullback.snd y y) comm
      inv := pullback.fst (p13 y) (jA y a ha) ≫ p23 y
      hom_inv_id := by rw [pullback.lift_fst_assoc, sA_p23]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, pullback.lift_fst, key, Category.id_comp]
        · rw [Category.assoc, Category.assoc, pullback.lift_snd, Category.id_comp,
          pullback.lift_snd]
          exact c2 }
  exact IsPullback.of_iso_pullback ⟨comm⟩ e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem isOpenImmersion_pτ [IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)] :
    IsOpenImmersion (pτ y γ a ha) := by
  have h := (IsPullback.of_hasPullback γ (sA y a ha)).paste_vert (isPullback_sA_fst y a ha)
  rw [pτ_def, show cA y γ a ha ≫ pullback.fst y y = h.isoPullback.hom ≫ pullback.snd _ _ from
    (h.isoPullback_hom_snd).symm]
  infer_instance

theorem isOpenImmersion_pι [IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
    (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y)
      y)
    (by rw [Category.assoc]; exact pullback.condition))] : IsOpenImmersion (pι y γ a ha) := by
  have h := (IsPullback.of_hasPullback γ (sA y a ha)).paste_vert (isPullback_sA_snd y a ha)
  rw [pι_def, show cA y γ a ha ≫ pullback.snd y y = h.isoPullback.hom ≫ pullback.snd _ _ from
    (h.isoPullback_hom_snd).symm]
  infer_instance

end Data

section Glue

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y)
variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
variable [IsOpenImmersion (pτ y γ a ha)] [IsOpenImmersion (pι y γ a ha)]

omit [IsOpenImmersion (pτ y γ a ha)] [IsOpenImmersion (pι y γ a ha)] in
theorem pτ_y : pτ y γ a ha ≫ y = pι y γ a ha ≫ y := by
  simp only [pτ_def, pι_def, Category.assoc, pullback.condition]

/-- The scheme obtained by gluing two translation charts. -/
abbrev Yg : Scheme.{u} := pushout (pτ y γ a ha) (pι y γ a ha)

/-- The structure morphism of the glued scheme. -/
abbrev yg : Yg y γ a ha ⟶ Spec (CommRingCat.of R) := pushout.desc y y (pτ_y y γ a ha)

/-- The first open chart in the glued scheme. -/
abbrev τg : Y ⟶ Yg y γ a ha := pushout.inl (pτ y γ a ha) (pι y γ a ha)

/-- The second open chart in the glued scheme. -/
abbrev ιg : Y ⟶ Yg y γ a ha := pushout.inr (pτ y γ a ha) (pι y γ a ha)

theorem τg_yg : τg y γ a ha ≫ yg y γ a ha = y := pushout.inl_desc _ _ (pτ_y y γ a ha)

theorem ιg_yg : ιg y γ a ha ≫ yg y γ a ha = y := pushout.inr_desc _ _ (pτ_y y γ a ha)

scoped instance : IsOpenImmersion (τg y γ a ha) := isOpenImmersion_inl _ _

scoped instance : IsOpenImmersion (ιg y γ a ha) := isOpenImmersion_inr _ _

theorem isPullback_τg_ιg : IsPullback (pτ y γ a ha) (pι y γ a ha) (τg y γ a ha) (ιg y γ a ha) :=
  isPullback_inl_inr _ _

theorem cover (p : ↑(Yg y γ a ha)) :
    p ∈ Set.range (ιg y γ a ha).base ∨ p ∈ Set.range (τg y γ a ha).base :=
  (inl_or_inr (pτ y γ a ha) (pι y γ a ha) p).symm

theorem of_openCover_yg (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (h0 : P (pτ y γ a ha ≫ y)) (h1 : P y) : P (yg y γ a ha) := by
  apply IsZariskiLocalAtSource.of_openCover
    (Scheme.IsLocallyDirected.openCover (span (pτ y γ a ha) (pι y γ a ha)))
  intro i
  obtain - | i := i
  · simp only [Scheme.IsLocallyDirected.openCover_f]
    rw [← colimit.w (span (pτ y γ a ha) (pι y γ a ha)) WalkingSpan.Hom.fst]
    change P ((pτ y γ a ha ≫ τg y γ a ha) ≫ yg y γ a ha)
    rw [Category.assoc, τg_yg]
    exact h0
  · cases i with
    | left =>
      simp only [Scheme.IsLocallyDirected.openCover_f]
      change P (τg y γ a ha ≫ yg y γ a ha)
      rw [τg_yg]; exact h1
    | right =>
      simp only [Scheme.IsLocallyDirected.openCover_f]
      change P (ιg y γ a ha ≫ yg y γ a ha)
      rw [ιg_yg]; exact h1

theorem locallyOfFiniteType_yg [LocallyOfFiniteType y] : LocallyOfFiniteType (yg y γ a ha) := by
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
  exact of_openCover_yg y γ a ha @LocallyOfFiniteType.{u} inferInstance inferInstance

theorem smooth_yg [Smooth y] : Smooth (yg y γ a ha) := by
  have : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @Smooth.{u}) (Q := RingHom.Smooth)
  exact of_openCover_yg y γ a ha @Smooth.{u} inferInstance inferInstance

theorem quasiCompact_yg [QuasiCompact y] : QuasiCompact (yg y γ a ha) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace y
  have : CompactSpace (Yg y γ a ha) := ⟨by
    have h : (Set.univ : Set ↑(Yg y γ a ha)) =
        Set.range (ιg y γ a ha).base ∪ Set.range (τg y γ a ha).base := by
      ext p
      simp only [Set.mem_univ, Set.mem_union, true_iff]
      exact cover y γ a ha p
    rw [h]
    exact (isCompact_range (ιg y γ a ha).base.hom.continuous).union
      (isCompact_range (τg y γ a ha).base.hom.continuous)⟩
  exact quasiCompact_of_compactSpace (yg y γ a ha)

end Glue

section Separated

theorem range_comp_of_surjective {X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hf : Function.Surjective f.base) : Set.range (f ≫ g).base = Set.range g.base := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f.base x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := hf w
    exact ⟨x, Scheme.Hom.comp_apply _ _ _⟩

theorem isClosed_preimage_range_diagonal {S Y' Y₁ Y₂ P : Scheme.{u}} (y' : Y' ⟶ S)
    (i₁ : Y₁ ⟶ Y') (i₂ : Y₂ ⟶ Y') [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (y₁ : Y₁ ⟶ S) (y₂ : Y₂ ⟶ S) (h₁ : y₁ = i₁ ≫ y') (h₂ : y₂ = i₂ ≫ y')
    (u : P ⟶ Y₁) (v : P ⟶ Y₂) (hP : IsPullback u v i₁ i₂) (huv : u ≫ y₁ = v ≫ y₂)
    (hc : IsClosed (Set.range (pullback.lift u v huv).base)) :
    IsClosed ((pullback.map y₁ y₂ y' y' i₁ i₂ (𝟙 S) (by rw [Category.comp_id, h₁])
      (by rw [Category.comp_id, h₂])).base ⁻¹' Set.range (pullback.diagonal y').base) := by
  subst h₁ h₂
  rw [← Scheme.Pullback.range_snd]
  set e := pullbackDiagonalMapIdIso i₁ i₂ y'
  have h1 : e.inv ≫ pullback.snd _ _ = pullback.lift (pullback.fst i₁ i₂) (pullback.snd i₁ i₂)
      (by rw [← Category.assoc, pullback.condition, Category.assoc]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullbackDiagonalMapIdIso_inv_snd_fst]
    · rw [Category.assoc, pullback.lift_snd, pullbackDiagonalMapIdIso_inv_snd_snd]
  have h2 : hP.isoPullback.hom ≫ pullback.lift (pullback.fst i₁ i₂) (pullback.snd i₁ i₂)
      (by rw [← Category.assoc, pullback.condition, Category.assoc]) = pullback.lift u v huv := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  have h3 : Set.range (pullback.snd (pullback.diagonal y') (pullback.map (i₁ ≫ y') (i₂ ≫ y') y' y'
    i₁ i₂
      (𝟙 S) (by rw [Category.comp_id]) (by rw [Category.comp_id]))).base =
      Set.range (pullback.lift u v huv).base := by
    rw [← h2, ← h1, range_comp_of_surjective _ _ hP.isoPullback.hom.surjective,
      range_comp_of_surjective _ _ e.inv.surjective]
  rw [h3]
  exact hc

theorem exists_open_subset_compl {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (φ : A → B)
    (hφ : IsOpenMap φ) (D : Set B) (hD : IsClosed (φ ⁻¹' D)) (q : B) (hq : q ∈ Set.range φ)
    (hqD : q ∉ D) : ∃ O : Set B, O ⊆ Dᶜ ∧ IsOpen O ∧ q ∈ O := by
  obtain ⟨z, rfl⟩ := hq
  refine ⟨φ '' (φ ⁻¹' D)ᶜ, ?_, hφ _ hD.isOpen_compl, ⟨z, hqD, rfl⟩⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hw

theorem isClosed_range_diagonal_of_two_charts {S Y' Y₁ Y₂ : Scheme.{u}} (y' : Y' ⟶ S)
    (i₁ : Y₁ ⟶ Y') (i₂ : Y₂ ⟶ Y') [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (y₁ : Y₁ ⟶ S) (y₂ : Y₂ ⟶ S) (e₁ : y₁ = i₁ ≫ y') (e₂ : y₂ = i₂ ≫ y')
    (hcov : ∀ p : Y', p ∈ Set.range i₁.base ∨ p ∈ Set.range i₂.base)
    (H₁₁ : IsClosed ((pullback.map y₁ y₁ y' y' i₁ i₁ (𝟙 S) (by rw [Category.comp_id, e₁])
      (by rw [Category.comp_id, e₁])).base ⁻¹' Set.range (pullback.diagonal y').base))
    (H₁₂ : IsClosed ((pullback.map y₁ y₂ y' y' i₁ i₂ (𝟙 S) (by rw [Category.comp_id, e₁])
      (by rw [Category.comp_id, e₂])).base ⁻¹' Set.range (pullback.diagonal y').base))
    (H₂₁ : IsClosed ((pullback.map y₂ y₁ y' y' i₂ i₁ (𝟙 S) (by rw [Category.comp_id, e₂])
      (by rw [Category.comp_id, e₁])).base ⁻¹' Set.range (pullback.diagonal y').base))
    (H₂₂ : IsClosed ((pullback.map y₂ y₂ y' y' i₂ i₂ (𝟙 S) (by rw [Category.comp_id, e₂])
      (by rw [Category.comp_id, e₂])).base ⁻¹' Set.range (pullback.diagonal y').base)) :
    IsClosed (Set.range (pullback.diagonal y').base) := by
  subst e₁ e₂
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro q hq
  rw [Set.mem_compl_iff] at hq
  have key : ∀ {Y₃ Y₄ : Scheme.{u}} (i₃ : Y₃ ⟶ Y') (i₄ : Y₄ ⟶ Y') [IsOpenImmersion i₃]
    [IsOpenImmersion i₄],
      IsClosed ((pullback.map (i₃ ≫ y') (i₄ ≫ y') y' y' i₃ i₄ (𝟙 S) (by rw [Category.comp_id])
        (by rw [Category.comp_id])).base ⁻¹' Set.range (pullback.diagonal y').base) →
      (pullback.fst y' y').base q ∈ Set.range i₃.base → (pullback.snd y' y').base q ∈ Set.range
        i₄.base →
      ∃ O : Set ↑(pullback y' y'), O ⊆ (Set.range (pullback.diagonal y').base)ᶜ ∧ IsOpen O ∧ q ∈ O
        := by
    intro Y₃ Y₄ i₃ i₄ _ _ H h₃ h₄
    refine exists_open_subset_compl _ (Scheme.Hom.isOpenEmbedding _).isOpenMap _ H q ?_ hq
    rw [Scheme.Pullback.range_map]
    exact ⟨h₃, h₄⟩
  rcases hcov ((pullback.fst y' y').base q) with h₃ | h₃ <;>
    rcases hcov ((pullback.snd y' y').base q) with h₄ | h₄
  · exact key i₁ i₁ H₁₁ h₃ h₄
  · exact key i₁ i₂ H₁₂ h₃ h₄
  · exact key i₂ i₁ H₂₁ h₃ h₄
  · exact key i₂ i₂ H₂₂ h₃ h₄

end Separated

section SeparatedGlue

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y)
variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
variable [IsOpenImmersion (pτ y γ a ha)] [IsOpenImmersion (pι y γ a ha)]

theorem isSeparated_yg [IsClosedImmersion γ] [IsSeparated y] : IsSeparated (yg y γ a ha) := by
  have hcov : ∀ p : ↑(Yg y γ a ha), p ∈ Set.range (τg y γ a ha).base ∨ p ∈ Set.range (ιg y γ a
    ha).base :=
    fun p => (cover y γ a ha p).symm
  have hdiag : IsClosed (Set.range (pullback.lift (𝟙 Y) (𝟙 Y) rfl : Y ⟶ pullback y y).base) :=
    (pullback.diagonal y).isClosedEmbedding.isClosed_range
  have hpb := isPullback_τg_ιg y γ a ha
  have hlift : pullback.lift (pτ y γ a ha) (pι y γ a ha) (pτ_y y γ a ha) = cA y γ a ha := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, pτ_def]
    · rw [pullback.lift_snd, pι_def]
  have hc12 : IsClosed (Set.range (pullback.lift (pτ y γ a ha) (pι y γ a ha) (pτ_y y γ a ha)).base)
    := by
    rw [hlift]
    exact (cA y γ a ha).isClosedEmbedding.isClosed_range
  have hlift' : pullback.lift (pι y γ a ha) (pτ y γ a ha) (pτ_y y γ a ha).symm =
      cA y γ a ha ≫ (pullbackSymmetry y y).hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullbackSymmetry_hom_comp_fst, pι_def]
    · rw [pullback.lift_snd, Category.assoc, pullbackSymmetry_hom_comp_snd, pτ_def]
  have hc21 : IsClosed (Set.range (pullback.lift (pι y γ a ha) (pτ y γ a ha) (pτ_y y γ a
    ha).symm).base) := by
    rw [hlift']
    exact (cA y γ a ha ≫ (pullbackSymmetry y y).hom).isClosedEmbedding.isClosed_range
  refine ⟨IsClosedImmersion.of_isPreimmersion _ (isClosed_range_diagonal_of_two_charts (yg y γ a ha)
    (τg y γ a ha) (ιg y γ a ha) y y (τg_yg y γ a ha).symm (ιg_yg y γ a ha).symm hcov ?_ ?_ ?_ ?_)⟩
  · exact isClosed_preimage_range_diagonal (yg y γ a ha) (τg y γ a ha) (τg y γ a ha) y y
      (τg_yg y γ a ha).symm (τg_yg y γ a ha).symm (𝟙 Y) (𝟙 Y) (IsKernelPair.id_of_mono _) rfl hdiag
  · exact isClosed_preimage_range_diagonal (yg y γ a ha) (τg y γ a ha) (ιg y γ a ha) y y
      (τg_yg y γ a ha).symm (ιg_yg y γ a ha).symm _ _ hpb (pτ_y y γ a ha) hc12
  · exact isClosed_preimage_range_diagonal (yg y γ a ha) (ιg y γ a ha) (τg y γ a ha) y y
      (ιg_yg y γ a ha).symm (τg_yg y γ a ha).symm _ _ hpb.flip (pτ_y y γ a ha).symm hc21
  · exact isClosed_preimage_range_diagonal (yg y γ a ha) (ιg y γ a ha) (ιg y γ a ha) y y
      (ιg_yg y γ a ha).symm (ιg_yg y γ a ha).symm (𝟙 Y) (𝟙 Y) (IsKernelPair.id_of_mono _) rfl hdiag

end SeparatedGlue

section Points

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
variable {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y)
variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)

/-- The graph map of the partial multiplication. -/
abbrev grm : (U : Scheme.{u}) ⟶ Y3 y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm

variable (g₀ : (U : Scheme.{u}) ⟶ G) (hg₀ : g₀ ≫ γ = grm y U m)

/-- Lift a section-compatible pair into the restricted multiplication graph. -/
def mkΓa {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    T ⟶ Ga y γ a ha :=
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
    mkΓa y U m γ a ha g₀ hg₀ x w h1 h2 ≫ pτ y γ a ha = x := by
  rw [pτ_def, mkΓa, pullback.lift_snd_assoc, pullback.lift_fst]

theorem mkΓa_pι {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    mkΓa y U m γ a ha g₀ hg₀ x w h1 h2 ≫ pι y γ a ha = w ≫ m.1 := by
  rw [pι_def, mkΓa, pullback.lift_snd_assoc, pullback.lift_snd]

include hg₀ in
theorem translate [IsOpenImmersion (pτ y γ a ha)] [IsOpenImmersion (pι y γ a ha)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t y)
    (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y))
    (hw₁ : w.1 ≫ U.ι ≫ pullback.fst y y = t ≫ a) (hw₂ : w.1 ≫ U.ι ≫ pullback.snd y y = x.1) :
    x.1 ≫ τg y γ a ha = w.1 ≫ m.1 ≫ ιg y γ a ha := by
  have h1 : w.1 ≫ U.ι ≫ pullback.fst y y = x.1 ≫ y ≫ a := by rw [hw₁, reassoc_of% x.2]
  rw [← mkΓa_pτ y U m γ a ha g₀ hg₀ x.1 w.1 h1 hw₂, Category.assoc, pushout.condition, ←
    Category.assoc,
    mkΓa_pι, Category.assoc]

include hg₀ in
theorem exists_pτ_eq_and_exists_pι_eq [IsSeparated y] (u : ↑(U : Scheme.{u}))
    (hu : (U.ι ≫ pullback.fst y y).base u ∈ Set.range a.base) :
    (∃ g : ↑(Ga y γ a ha), (pτ y γ a ha).base g = (U.ι ≫ pullback.snd y y).base u) ∧
      (∃ g : ↑(Ga y γ a ha), (pι y γ a ha).base g = m.1.base u) := by
  have : IsClosedImmersion (a ≫ y) := by rw [ha]; infer_instance
  have : IsClosedImmersion a := IsClosedImmersion.of_comp a y
  set w : Spec ((U : Scheme.{u}).residueField u) ⟶ (U : Scheme.{u}) := (U :
    Scheme.{u}).fromSpecResidueField u
  have hrange : Set.range (w ≫ U.ι ≫ pullback.fst y y).base ⊆ Set.range a.base := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact hu
  obtain ⟨α, hα⟩ := exists_lift_of_isClosedImmersion (w ≫ U.ι ≫ pullback.fst y y) a hrange
  have h1 : w ≫ U.ι ≫ pullback.fst y y = (w ≫ U.ι ≫ pullback.snd y y) ≫ y ≫ a := by
    have hα' : α = (w ≫ U.ι ≫ pullback.snd y y) ≫ y := by
      rw [← Category.comp_id α, ← ha, ← Category.assoc, hα, Category.assoc, Category.assoc,
        Category.assoc,
        Category.assoc, pullback.condition]
    rw [← hα, hα', Category.assoc]
  set z := mkΓa y U m γ a ha g₀ hg₀ _ w h1 rfl
  let c : ↥(Spec ((U : Scheme.{u}).residueField u)) := fieldPoint _
  refine ⟨⟨z.base c, ?_⟩, ⟨z.base c, ?_⟩⟩
  · rw [← Scheme.Hom.comp_apply, mkΓa_pτ, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  · rw [← Scheme.Hom.comp_apply, mkΓa_pι, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

include hg₀ in
theorem preimage_jA_subset_range_pτ [IsSeparated y] :
    (jA y a ha).base ⁻¹' (U : Set ↑(pullback y y)) ⊆ Set.range (pτ y γ a ha).base := by
  intro b hb
  let u : ↥(U : Scheme.{u}) := ⟨(jA y a ha).base b, hb⟩
  have hu : (U.ι ≫ pullback.fst y y).base u ∈ Set.range a.base := by
    refine ⟨y.base b, ?_⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    change (y ≫ a).base b = (pullback.fst y y).base ((jA y a ha).base b)
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  obtain ⟨⟨g, hg⟩, -⟩ := exists_pτ_eq_and_exists_pι_eq y U m γ a ha g₀ hg₀ _ hu
  refine ⟨g, ?_⟩
  rw [hg, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  change (pullback.snd y y).base ((jA y a ha).base b) = b
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  rfl

include hg₀ in
theorem preimage_jA_range_subset_range_pι [IsSeparated y] :
    (jA y a ha).base ⁻¹' Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
      ((Category.assoc _ _ _).trans m.2.symm)).base ⊆ Set.range (pι y γ a ha).base := by
  rintro c ⟨u, hu⟩
  have hu' : (U.ι ≫ pullback.fst y y).base u ∈ Set.range a.base := by
    refine ⟨y.base c, ?_⟩
    rw [← pullback.lift_fst (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _
      _).trans m.2.symm),
      Scheme.Hom.comp_apply, hu]
    change (y ≫ a).base c = (pullback.fst y y).base ((jA y a ha).base c)
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  obtain ⟨-, ⟨g, hg⟩⟩ := exists_pτ_eq_and_exists_pι_eq y U m γ a ha g₀ hg₀ _ hu'
  refine ⟨g, ?_⟩
  rw [hg, ← pullback.lift_snd (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _
    _).trans m.2.symm),
    Scheme.Hom.comp_apply, hu, ← Scheme.Hom.comp_apply, pullback.lift_snd]
  rfl

end Points

section Density

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))

theorem mem_of_dense_fibre [TopologicalSpace.NoetherianSpace Y] (W : Set Y) (hW : IsOpen W)
    (s : Spec (CommRingCat.of R)) (hd : Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' W))
    (x : Y) (hxs : y.base x = s) (hmax : ∀ x' : Y, x' ⤳ x → y.base x' = y.base x → x' = x) : x ∈ W
      := by
  set e := y.fiberι s with he
  have hemb : Topology.IsEmbedding e.base := e.isEmbedding
  have hrange : Set.range e.base = y.base ⁻¹' {s} := y.range_fiberι s
  obtain ⟨ξ, hξ⟩ : x ∈ Set.range e.base := by rw [hrange]; exact hxs
  have : TopologicalSpace.NoetherianSpace ↑(y.fiber s) := hemb.isInducing.noetherianSpace
  have hd' : Dense (e.base ⁻¹' W) := by
    rw [hemb.isInducing.dense_iff]
    intro ζ
    have hζ : e.base ζ ∈ y.base ⁻¹' {s} := hrange ▸ ⟨ζ, rfl⟩
    have h1 : (⟨e.base ζ, hζ⟩ : {b : ↑Y // y.base b = s}) ∈
        closure ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' W) := hd _
    rw [closure_subtype] at h1
    refine closure_mono ?_ h1
    rintro _ ⟨⟨b, hb⟩, hbW, rfl⟩
    obtain ⟨ζ', rfl⟩ : b ∈ Set.range e.base := by rw [hrange]; exact hb
    exact ⟨ζ', hbW, rfl⟩
  have hmax' : ∀ ξ' : ↑(y.fiber s), ξ' ⤳ ξ → ξ' = ξ := by
    intro ξ' hξ'
    apply hemb.injective
    rw [hξ]
    refine hmax _ (hξ ▸ hξ'.map e.base.hom.continuous) ?_
    have h1 : e.base ξ' ∈ y.base ⁻¹' {s} := hrange ▸ ⟨ξ', rfl⟩
    rw [h1, hxs]
  have := mem_of_dense_of_forall_specializes (e.base.hom.continuous.isOpen_preimage W hW) hd' ξ
    hmax'
  rwa [Set.mem_preimage, hξ] at this

variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)

end Density

end SeparatedCharts
end AbelianVarieties.NOSProofs.SeparatedTranslationGluing

open AbelianVarieties.NOSProofs.SeparatedTranslationGluing.SeparatedCharts

namespace NeronModelInfra

theorem exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y) [IsClosedImmersion γ]
    (hγ : Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base ⊆
      Set.range γ.base)
    [IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)]
    [IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc]; exact pullback.condition))]
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _) :
    ∃ (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (CommRingCat.of R)) (ι τ : SchemeHomOver y y'),
      Smooth y' ∧ IsSeparated y' ∧ LocallyOfFiniteType y' ∧ QuasiCompact y' ∧
      IsOpenImmersion ι.1 ∧ IsOpenImmersion τ.1 ∧
      (∀ p : Y', p ∈ Set.range ι.1.base ∨ p ∈ Set.range τ.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range τ.1.base) ∧
      IsPullback
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.fst y y)
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.snd y y)
        τ.1 ι.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t y)
          (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        w.1 ≫ U.ι ≫ pullback.fst y y = t ≫ a → w.1 ≫ U.ι ≫ pullback.snd y y = x.1 →
        x.1 ≫ τ.1 = w.1 ≫ m.1 ≫ ι.1) := by
  have : IsOpenImmersion (pτ y γ a ha) := isOpenImmersion_pτ y γ a ha
  have : IsOpenImmersion (pι y γ a ha) := isOpenImmersion_pι y γ a ha
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian y
  have : CompactSpace ↑Y := QuasiCompact.compactSpace_of_compactSpace y
  have : IsNoetherian Y := {}
  have : IsReduced (U : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (U.ι ≫ pullback.fst y y ≫
      y)
  obtain ⟨g₀, hg₀⟩ := exists_lift_of_isClosedImmersion (grm y U m) γ hγ
  refine ⟨Yg y γ a ha, yg y γ a ha, ⟨ιg y γ a ha, ιg_yg y γ a ha⟩, ⟨τg y γ a ha, τg_yg y γ a ha⟩,
    smooth_yg y γ a ha, isSeparated_yg y γ a ha, locallyOfFiniteType_yg y γ a ha, quasiCompact_yg y
      γ a ha,
    inferInstance, inferInstance, cover y γ a ha, ?_, ?_, isPullback_τg_ιg y γ a ha,
    fun t x w hw₁ hw₂ => translate y U m γ a ha g₀ hg₀ t x w hw₁ hw₂⟩
  · intro p hp
    rcases cover y γ a ha p with h | ⟨x, rfl⟩
    · exact h
    have hxmax : ∀ x' : Y, x' ⤳ x → y.base x' = y.base x → x' = x := by
      intro x' h1 h2
      apply (τg y γ a ha).isOpenEmbedding.injective
      refine hp _ (h1.map (τg y γ a ha).base.hom.continuous) ?_
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, τg_yg]
      exact h2
    have hx : x ∈ Set.range (pτ y γ a ha).base :=
      mem_of_dense_fibre y _ (pτ y γ a ha).isOpenEmbedding.isOpen_range (y.base x)
        ((dense_fibre_jA y a ha _ _ (hU₁ (a.base (y.base x)))).mono
          (Set.preimage_mono (preimage_jA_subset_range_pτ y U m γ a ha g₀ hg₀))) x rfl hxmax
    obtain ⟨g, rfl⟩ := hx
    refine ⟨(pι y γ a ha).base g, ?_⟩
    change (ιg y γ a ha).base ((pι y γ a ha).base g) = (τg y γ a ha).base ((pτ y γ a ha).base g)
    rw [← Scheme.Hom.comp_apply, ← pushout.condition, Scheme.Hom.comp_apply]
  · intro p hp
    rcases cover y γ a ha p with ⟨z, rfl⟩ | h
    swap
    · exact h
    have hzmax : ∀ z' : Y, z' ⤳ z → y.base z' = y.base z → z' = z := by
      intro z' h1 h2
      apply (ιg y γ a ha).isOpenEmbedding.injective
      refine hp _ (h1.map (ιg y γ a ha).base.hom.continuous) ?_
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ιg_yg]
      exact h2
    have hz : z ∈ Set.range (pι y γ a ha).base :=
      mem_of_dense_fibre y _ (pι y γ a ha).isOpenEmbedding.isOpen_range (y.base z)
        ((dense_fibre_jA y a ha _ _ (hΦ₁ (a.base (y.base z)))).mono
          (Set.preimage_mono (preimage_jA_range_subset_range_pι y U m γ a ha g₀ hg₀))) z rfl hzmax
    obtain ⟨g, rfl⟩ := hz
    refine ⟨(pτ y γ a ha).base g, ?_⟩
    change (τg y γ a ha).base ((pτ y γ a ha).base g) = (ιg y γ a ha).base ((pι y γ a ha).base g)
    rw [← Scheme.Hom.comp_apply, pushout.condition, Scheme.Hom.comp_apply]

end NeronModelInfra

end
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre.lean
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

open AbelianVarieties.NOSProofs.GraphClosureRigidity.GraphClosure
  (dense_of_forall_dense_fibre Y3 gr P12 Zc Gc γc range_γc denseRange_g0 exists_comp_γc_eq)
open scoped AbelianVarieties.NOSProofs.GraphClosureRigidity.GraphClosure
open AbelianVarieties.NOSProofs.GluingFibreDensity (dense_fibre_mono)
open AbelianVarieties.NOSProofs.GluingFibreDensity.TranslationCharts
  (dense_fibre_image_of_homeomorph)

namespace AbelianVarieties.NOSProofs.ReducedGraphImmersions

namespace GraphImmersions

section Graph

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

/-- The projection onto the first and third graph coordinates. -/
abbrev P13 : Y3 y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y)
    (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y)
      y)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The projection onto the second and third graph coordinates. -/
abbrev P23 : Y3 y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y)
    (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y)
      y)
    (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)

/-- Pair the first input with the partial multiplication value. -/
abbrev Phi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans
    m.2.symm)

/-- Pair the partial multiplication value with the second input. -/
abbrev Psi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
    (m.2.trans (by rw [Category.assoc, pullback.condition]))

/-- Exchange the coordinates of the second multiplication chart. -/
abbrev Psi' : (U : Scheme.{u}) ⟶ pullback y y := Psi y U m ≫ (pullbackSymmetry y y).hom

theorem gr_P12 : gr y U m ≫ P12 y = U.ι := pullback.lift_fst _ _ _

theorem gr_P13 : gr y U m ≫ P13 y = Phi y U m := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, pullback.lift_snd]

theorem gr_P23 : gr y U m ≫ P23 y = Psi' y U m := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
    pullbackSymmetry_hom_comp_fst,
      pullback.lift_snd]
  · simp only [Category.assoc, pullback.lift_snd, pullbackSymmetry_hom_comp_snd, pullback.lift_fst]

theorem P13_comp : P13 y ≫ pullback.fst y y ≫ y = pullback.fst _ _ ≫ pullback.fst y y ≫ y := by
  rw [pullback.lift_fst_assoc, Category.assoc]

theorem P23_comp : P23 y ≫ pullback.fst y y ≫ y = pullback.fst _ _ ≫ pullback.fst y y ≫ y := by
  rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]

scoped instance [IsSeparated y] : IsSeparated (P13 y) := by
  have : IsSeparated (P13 y ≫ pullback.fst y y ≫ y) := by rw [P13_comp]; infer_instance
  exact IsSeparated.of_comp (P13 y) (pullback.fst y y ≫ y)

scoped instance [IsSeparated y] : IsSeparated (P23 y) := by
  have : IsSeparated (P23 y ≫ pullback.fst y y ≫ y) := by rw [P23_comp]; infer_instance
  exact IsSeparated.of_comp (P23 y) (pullback.fst y y ≫ y)

scoped instance [IsSeparated y] [QuasiCompact y] : QuasiCompact (P13 y) := by
  have : QuasiCompact (P13 y ≫ pullback.fst y y ≫ y) := by rw [P13_comp]; infer_instance
  exact QuasiCompact.of_comp (P13 y) (pullback.fst y y ≫ y)

scoped instance [IsSeparated y] [QuasiCompact y] : QuasiCompact (P23 y) := by
  have : QuasiCompact (P23 y ≫ pullback.fst y y ≫ y) := by rw [P23_comp]; infer_instance
  exact QuasiCompact.of_comp (P23 y) (pullback.fst y y ≫ y)

scoped instance [LocallyOfFiniteType y] : LocallyOfFiniteType (P13 y) := by
  have : LocallyOfFiniteType (P13 y ≫ pullback.fst y y ≫ y) := by rw [P13_comp]; infer_instance
  exact locallyOfFiniteType_of_comp (P13 y) (pullback.fst y y ≫ y)

scoped instance [LocallyOfFiniteType y] : LocallyOfFiniteType (P23 y) := by
  have : LocallyOfFiniteType (P23 y ≫ pullback.fst y y ≫ y) := by rw [P23_comp]; infer_instance
  exact locallyOfFiniteType_of_comp (P23 y) (pullback.fst y y ≫ y)

theorem range_Psi' : Set.range (Psi' y U m).base =
    (pullbackSymmetry y y).hom.base '' Set.range (Psi y U m).base := by
  rw [← Set.range_comp]
  rfl

variable {y U m} in
theorem range_g0_comp_subset (g₀ : (U : Scheme.{u}) ⟶ Gc y U m) {W : Scheme.{u}} (q : Gc y U m ⟶ W)
    :
    Set.range (g₀ ≫ q).base ⊆ Set.range q.base := by
  rintro _ ⟨u, rfl⟩
  exact ⟨g₀.base u, (Scheme.Hom.comp_apply g₀ q u).symm⟩

variable {y U m} in
theorem injective_γc_comp (q : Y3 y ⟶ pullback y y)
    (hq : ∀ (K : Type u) [Field K] (g g' : Spec (CommRingCat.of K) ⟶ Y3 y),
      Set.range g.base ⊆ closure (Set.range (gr y U m).base) →
      Set.range g'.base ⊆ closure (Set.range (gr y U m).base) →
      g ≫ q = g' ≫ q → g = g') :
    Function.Injective (γc y U m ≫ q).base := by
  intro p₁ p₂ h
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := γc y U m ≫ q) (g := γc y U
    m ≫ q)
    p₁ p₂ h
  let P := pullback (γc y U m ≫ q) (γc y U m ≫ q)
  let k : Spec (P.residueField w) ⟶ P := P.fromSpecResidueField w
  have hsub : ∀ (r : Spec (P.residueField w) ⟶ Gc y U m),
      Set.range (r ≫ γc y U m).base ⊆ closure (Set.range (gr y U m).base) := by
    intro r
    rw [← range_γc]
    rintro _ ⟨t, rfl⟩
    exact ⟨r.base t, (Scheme.Hom.comp_apply r _ t).symm⟩
  have key := hq (P.residueField w) ((k ≫ pullback.fst _ _) ≫ γc y U m) ((k ≫ pullback.snd _ _) ≫ γc
    y U m)
    (hsub _) (hsub _) (by simp only [Category.assoc, k, P]; rw [pullback.condition])
  replace key : k ≫ pullback.fst (γc y U m ≫ q) (γc y U m ≫ q) = k ≫ pullback.snd (γc y U m ≫ q) (γc
    y U m ≫ q) :=
    (cancel_mono (γc y U m)).mp (by simpa only [Category.assoc] using key)
  let c : ↥(Spec (P.residueField w)) := fieldPoint _
  have hpt : (k ≫ pullback.fst (γc y U m ≫ q) (γc y U m ≫ q)).base c =
      (k ≫ pullback.snd (γc y U m ≫ q) (γc y U m ≫ q)).base c := by rw [key]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hpt
  simp only [k, P, Scheme.fromSpecResidueField_apply] at hpt
  rw [← hw₁, ← hw₂]
  exact hpt

variable {y U m} in
theorem isOpenImmersion_γc_comp [IsDomain R] [IsDiscreteValuationRing R]
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (q : Y3 y ⟶ pullback y y) [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    (hinj : Function.Injective (γc y U m ≫ q).base)
    (V : (pullback y y).Opens) (hV : Dense (V : Set ↑(pullback y y)))
    (s : (V : Scheme.{u}) ⟶ Gc y U m) (hs : s ≫ (γc y U m ≫ q) = V.ι) (hsd : DenseRange s.base) :
    IsOpenImmersion (γc y U m ≫ q) := by
  have : LocallyQuasiFinite (γc y U m ≫ q) := LocallyQuasiFinite.of_injective hinj
  have : IsLocallyNoetherian (pullback y y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst y y ≫ y)
  have hY : ∀ z : ↑(pullback y y), IsDomain ((pullback y y).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback y y).presheaf.stalk z) := fun z =>
    AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      (pullback.fst y y ≫ y) z
  exact isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
    (γc y U m ≫ q) hY V hV s hs hsd

end Graph

end GraphImmersions
end AbelianVarieties.NOSProofs.ReducedGraphImmersions

open AbelianVarieties.NOSProofs.ReducedGraphImmersions.GraphImmersions

namespace NeronModelInfra

theorem exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
        (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
        (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans
        m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
        Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
          ((Category.assoc _ _ _).trans m.2.symm)).base))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
        Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
          ((Category.assoc _ _ _).trans m.2.symm)).base))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
        Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
        Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
        pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y =
        v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1) :
    ∃ (G : Scheme.{u}) (γ : G ⟶ pullback (pullback.fst y y ≫ y) y),
      IsClosedImmersion γ ∧ IsReduced G ∧
      Set.range γ.base =
        closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1
          m.2.symm).base) ∧
      IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y) ∧
      IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc]; exact pullback.condition)) ∧
      IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition))
          ∧
      (∀ x : Y,
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
          y)) ⁻¹'
          Set.range (γ ≫ pullback.fst (pullback.fst y y ≫ y) y).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
          y)) ⁻¹'
          Set.range (γ ≫ pullback.fst (pullback.fst y y ≫ y) y).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
          y)) ⁻¹'
          Set.range (γ ≫ pullback.lift (f := y) (g := y)
            (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y
              y ≫ y) y)
            (by rw [Category.assoc]; exact pullback.condition)).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
          y)) ⁻¹'
          Set.range (γ ≫ pullback.lift (f := y) (g := y)
            (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y
              y ≫ y) y)
            (by rw [Category.assoc]; exact pullback.condition)).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
          y)) ⁻¹'
          Set.range (γ ≫ pullback.lift (f := y) (g := y)
            (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y
              y ≫ y) y)
            (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact
              pullback.condition)).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
          y)) ⁻¹'
          Set.range (γ ≫ pullback.lift (f := y) (g := y)
            (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y
              y ≫ y) y)
            (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact
              pullback.condition)).base)) := by
  have : IsOpenImmersion (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
      ((Category.assoc _ _ _).trans m.2.symm)) := hΦ
  have : IsOpenImmersion (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
      (m.2.trans (by rw [Category.assoc, pullback.condition]))) := hΨ
  have : IsReduced (U : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (U.ι ≫ pullback.fst y y ≫
      y)
  obtain ⟨g₀, hg₀⟩ := exists_comp_γc_eq y U m (gr y U m) subset_closure
  have hg₀d : DenseRange g₀.base := denseRange_g0 g₀ hg₀
  have hINJ := fun (K : Type u) [Field K] (g g' : Spec (CommRingCat.of K) ⟶ Y3 y)
      (hg : Set.range g.base ⊆ closure (Set.range (gr y U m).base))
      (hg' : Set.range g'.base ⊆ closure (Set.range (gr y U m).base)) =>
    NeronModelInfra.eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre
      y U m hU₁ hΦ hΨ hassoc g g' hg hg'
  have hinj12 : Function.Injective (γc y U m ≫ P12 y).base :=
    injective_γc_comp (P12 y) (fun K _ g g' hg hg' h => (hINJ K g g' hg hg').1 h)
  have hinj13 : Function.Injective (γc y U m ≫ P13 y).base :=
    injective_γc_comp (P13 y) (fun K _ g g' hg hg' h => (hINJ K g g' hg hg').2.1 h)
  have hinj23 : Function.Injective (γc y U m ≫ P23 y).base :=
    injective_γc_comp (P23 y) (fun K _ g g' hg hg' h => (hINJ K g g' hg hg').2.2 h)
  have hUd : Dense (U : Set ↑(pullback y y)) :=
    dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hU₁
  have hΦd : Dense (Set.range (Phi y U m).base) :=
    dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hΦ₁
  have hsym : ∀ q : ↑(pullback y y), (pullback.fst y y).base ((pullbackSymmetry y y).hom.base q) =
      (pullback.snd y y).base q := by
    intro q
    rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst]
  have hsym' : ∀ q : ↑(pullback y y), (pullback.snd y y).base ((pullbackSymmetry y y).hom.base q) =
      (pullback.fst y y).base q := by
    intro q
    rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_snd]
  let esym : ↑(pullback y y) ≃ₜ ↑(pullback y y) := Scheme.homeoOfIso (pullbackSymmetry y y)
  have hΨ'₁ : ∀ x : Y, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x}
    →
      ↑(pullback y y)) ⁻¹' Set.range (Psi' y U m).base) := by
    intro x
    rw [range_Psi']
    exact dense_fibre_image_of_homeomorph esym _ _ hsym x (hΨ₂ x)
  have hΨ'₂ : ∀ x : Y, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x}
    →
      ↑(pullback y y)) ⁻¹' Set.range (Psi' y U m).base) := by
    intro x
    rw [range_Psi']
    exact dense_fibre_image_of_homeomorph esym _ _ hsym' x (hΨ₁ x)
  have hΨ'd : Dense (Set.range (Psi' y U m).base) :=
    dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hΨ'₁
  have h12 : IsOpenImmersion (γc y U m ≫ P12 y) := by
    refine isOpenImmersion_γc_comp (P12 y) hinj12 U hUd g₀ ?_ hg₀d
    rw [← Category.assoc, hg₀, gr_P12]
  have h13 : IsOpenImmersion (γc y U m ≫ P13 y) := by
    have hV : ((Phi y U m).opensRange : Set ↑(pullback y y)) = Set.range (Phi y U m).base := rfl
    refine isOpenImmersion_γc_comp (P13 y) hinj13 (Phi y U m).opensRange (by rw [hV]; exact hΦd)
      ((Phi y U m).isoOpensRange.inv ≫ g₀) ?_ ?_
    · rw [Category.assoc, ← Category.assoc g₀, hg₀, gr_P13, Scheme.Hom.isoOpensRange_inv_comp]
    · rw [Scheme.Hom.comp_base, TopCat.coe_comp]
      exact hg₀d.comp (Scheme.homeoOfIso (Phi y U m).isoOpensRange.symm).surjective.denseRange
        g₀.base.hom.continuous
  have h23 : IsOpenImmersion (γc y U m ≫ P23 y) := by
    have hV : ((Psi' y U m).opensRange : Set ↑(pullback y y)) = Set.range (Psi' y U m).base := rfl
    refine isOpenImmersion_γc_comp (P23 y) hinj23 (Psi' y U m).opensRange (by rw [hV]; exact hΨ'd)
      ((Psi' y U m).isoOpensRange.inv ≫ g₀) ?_ ?_
    · rw [Category.assoc, ← Category.assoc g₀, hg₀, gr_P23, Scheme.Hom.isoOpensRange_inv_comp]
    · rw [Scheme.Hom.comp_base, TopCat.coe_comp]
      exact hg₀d.comp (Scheme.homeoOfIso (Psi' y U m).isoOpensRange.symm).surjective.denseRange
        g₀.base.hom.continuous
  have hr12 : (U : Set ↑(pullback y y)) ⊆ Set.range (γc y U m ≫ P12 y).base := by
    have : Set.range (g₀ ≫ γc y U m ≫ P12 y).base = (U : Set ↑(pullback y y)) := by
      rw [← Category.assoc, hg₀, gr_P12]; exact Scheme.Opens.range_ι U
    rw [← this]; exact range_g0_comp_subset g₀ _
  have hr13 : Set.range (Phi y U m).base ⊆ Set.range (γc y U m ≫ P13 y).base := by
    have : g₀ ≫ γc y U m ≫ P13 y = Phi y U m := by rw [← Category.assoc, hg₀, gr_P13]
    rw [← this]; exact range_g0_comp_subset g₀ _
  have hr23 : Set.range (Psi' y U m).base ⊆ Set.range (γc y U m ≫ P23 y).base := by
    have : g₀ ≫ γc y U m ≫ P23 y = Psi' y U m := by rw [← Category.assoc, hg₀, gr_P23]
    rw [← this]; exact range_g0_comp_subset g₀ _
  refine ⟨Gc y U m, γc y U m, inferInstance, inferInstance, range_γc y U m, h12, h13, h23, fun x =>
    ?_⟩
  exact ⟨dense_fibre_mono _ hr12 x (hU₁ x), dense_fibre_mono _ hr12 x (hU₂ x),
    dense_fibre_mono _ hr13 x (hΦ₁ x), dense_fibre_mono _ hr13 x (hΦ₂ x),
    dense_fibre_mono _ hr23 x (hΨ'₁ x), dense_fibre_mono _ hr23 x (hΨ'₂ x)⟩

end NeronModelInfra

end
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section.lean
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

namespace AbelianVarieties.NOSProofs.TranslationGluingDensity

namespace DenseGluing

open AbelianVarieties.NOSProofs.SeparatedTranslationGluing.SeparatedCharts
  (grm jA sA preimage_jA_subset_range_pτ preimage_jA_range_subset_range_pι
    mem_of_dense_fibre)
open AbelianVarieties.NOSProofs.QuasiFiniteTranslationGluing.TranslationGluing
  (exists_lift_of_isClosedImmersion dense_fibre_jA)

section Density

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))

theorem mem_range_of_maximal [NoetherianSpace Y] {Y' Γ' : Scheme.{u}} (y' : Y' ⟶ Spec
    (CommRingCat.of R))
    (i j : Y ⟶ Y') (hi : i ≫ y' = y) [IsOpenImmersion i]
    (p₁ p₂ : Γ' ⟶ Y) (hp : p₁ ≫ i = p₂ ≫ j)
    (W : Set Y) (hWo : IsOpen W) (hWd : ∀ s, Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y)
      ⁻¹' W))
    (hW : W ⊆ Set.range p₁.base)
    (p : Y') (hp' : ∀ q : Y', q ⤳ p → y'.base q = y'.base p → q = p) (x : Y) (hx : i.base x = p) :
    p ∈ Set.range j.base := by
  have hxmax : ∀ x' : Y, x' ⤳ x → y.base x' = y.base x → x' = x := by
    intro x' h1 h2
    apply i.isOpenEmbedding.injective
    rw [hx]
    refine hp' _ (hx ▸ h1.map i.continuous) ?_
    rw [← hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hi, h2]
  have hxW : x ∈ W := mem_of_dense_fibre y W hWo (y.base x) (hWd _) x rfl hxmax
  obtain ⟨g, hg⟩ := hW hxW
  refine ⟨p₂.base g, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply, hg, hx]

end Density

end DenseGluing
end AbelianVarieties.NOSProofs.TranslationGluingDensity

open AbelianVarieties.NOSProofs.TranslationGluingDensity.DenseGluing
open AbelianVarieties.NOSProofs.SeparatedTranslationGluing.SeparatedCharts
  (grm jA preimage_jA_subset_range_pτ preimage_jA_range_subset_range_pι)
open AbelianVarieties.NOSProofs.QuasiFiniteTranslationGluing.TranslationGluing
  (exists_lift_of_isClosedImmersion dense_fibre_jA)

namespace NeronModelInfra

theorem exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
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
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
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
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
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
    {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y) [IsClosedImmersion γ]
    (hΓ : Set.range γ.base =
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1
        m.2.symm).base))
    [IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)]
    [IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc]; exact pullback.condition))]
    [IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition))]
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]
    (hcov : ∀ p : Y', p ∈ Set.range ι.1.base ∨ p ∈ Set.range τ.1.base)
    (hΓa : IsPullback
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.fst y y)
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.snd y y)
        τ.1 ι.1) :
    ∃ (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'),
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
        p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
        p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
        q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' →
        q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
        p.1 ≫ m'.1 = q.1 ≫ m'.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst
        y y ≫ y)),
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
          w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1) := by
  have : IsOpenImmersion (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
      ((Category.assoc _ _ _).trans m.2.symm)) := hΦ
  have : IsOpenImmersion (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
      (m.2.trans (by rw [Category.assoc, pullback.condition]))) := hΨ
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian y
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace y
  have : IsNoetherian Y := {}
  have : IsReduced (U : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (U.ι ≫ pullback.fst y y ≫
      y)
  have hgr : Set.range (grm y U m).base ⊆ Set.range γ.base := hΓ ▸ subset_closure
  obtain ⟨g₀, hg₀⟩ := exists_lift_of_isClosedImmersion (grm y U m) γ hgr
  have hUb : ∀ s, Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹'
      ((jA y a ha).base ⁻¹' (U : Set ↑(pullback y y)))) := fun s => dense_fibre_jA y a ha _ s (hU₁
        _)
  have hΦb : ∀ s, Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹'
      ((jA y a ha).base ⁻¹' Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)) := fun s => dense_fibre_jA y a ha _ s (hΦ₁
          _)
  have hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range
    ι.1.base := by
    intro p hp
    rcases hcov p with h | ⟨x, hx⟩
    · exact h
    · exact mem_range_of_maximal y y' τ.1 ι.1 τ.2 _ _ hΓa.w _ ((jA y a
      ha).continuous.isOpen_preimage _ U.isOpen)
        hUb (preimage_jA_subset_range_pτ y U m γ a ha g₀ hg₀) p hp x hx
  have hτd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range
    τ.1.base := by
    intro p hp
    rcases hcov p with ⟨x, hx⟩ | h
    · exact mem_range_of_maximal y y' ι.1 τ.1 ι.2 _ _ hΓa.w.symm _
        ((jA y a ha).continuous.isOpen_preimage _
          (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).isOpenEmbedding.isOpen_range)
        hΦb (preimage_jA_range_subset_range_pι y U m γ a ha g₀ hg₀) p hp x hx
    · exact h
  obtain ⟨U', m', hqΦ, hqΨ, hext, hp1, hp2⟩ :=
    exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section
      y U m hU₁ hΦ hΨ hassoc γ hΓ a ha y' ι τ hιd hΓa.w
  have : LocallyQuasiFinite (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
      ((Category.assoc _ _ _).trans m'.2.symm)) := hqΦ
  have : LocallyQuasiFinite (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
      (m'.2.trans (by rw [Category.assoc, pullback.condition]))) := hqΨ
  obtain ⟨hΦ', hΨ', hassoc'⟩ :=
    isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq
      y U m hU₁ hΦ hΦ₁ hΨ hΨ₁ hassoc y' ι hιd U' m' hext
  obtain ⟨d₁, d₂, d₃, d₄, d₅, d₆⟩ :=
    NeronModelInfra.forall_dense_preimage_fibre_of_forall_exists_comp_eq_glue_translate
      y U m hU₁ hU₂ hΦ₁ hΦ₂ hΨ hΨ₁ hΨ₂ a ha y' ι τ hcov hιd hτd U' m' hext hp1 hp2
  exact ⟨U', m', d₁, d₂, hΦ', d₃, d₄, hΨ', d₅, d₆, hassoc', hext⟩

end NeronModelInfra

end
end
