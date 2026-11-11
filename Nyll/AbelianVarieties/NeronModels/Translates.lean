/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Nyll.AbelianVarieties.NeronModels.Density
public import Nyll.AbelianVarieties.NeronModels.GluingDensity
public import Nyll.AbelianVarieties.NeronModels.QuasiFiniteGluing
public import Nyll.AbelianVarieties.NeronModels.SeparatedGluing
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced

/-!
# Translates of a partial group law on a smooth model

Étale descent constructs an open domain for translation. Gluing translates after base
change enlarges the model while preserving the fiberwise dense partial group law.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_opens_forall_range_subset_of_comp_translation_eq_of_etale.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.EtaleTranslationPieces

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian Topology

universe u v

namespace TranslationPiece

open AbelianVarieties.NOSProofs.GraphClosureRigidity.GraphClosure
  (dense_of_forall_dense_fibre)
open AbelianVarieties.NOSProofs.DensityBaseChange.FibreDensity
  (dense_fibre_iff dense_preimage_of_isPullback dense_fibre_of_isPullback)
open AbelianVarieties.NOSProofs.GluingFibreDensity.TranslationCharts
  (universallyOpen_m)

section General

theorem eq_of_comp_ι_eq {X Z S : Scheme.{u}} [IsReduced X] (s : Z ⟶ S) [IsSeparated s]
    {f g : X ⟶ Z} (hs : f ≫ s = g ≫ s) (W : X.Opens) (hW : Dense (W : Set X)) (h : W.ι ≫ f =
        W.ι ≫ g) :
    f = g := by
  have : IsDominant W.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hW⟩
  exact ext_of_isDominant_of_isSeparated s hs W.ι h

end General

section Setup

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

/-- The left translation graph of the partial law. -/
abbrev Phi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
      ((Category.assoc _ _ _).trans m.2.symm)

/-- Insert a base-changed section as the first coordinate. -/
def lamFst {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y = c) :
    pullback y c ⟶ pullback y y :=
  pullback.lift (pullback.snd y c ≫ g) (pullback.fst y c)
      (by rw [Category.assoc, hg, pullback.condition])

@[reassoc]
theorem lamFst_fst {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y = c) :
    lamFst y c g hg ≫ pullback.fst y y = pullback.snd y c ≫ g := pullback.lift_fst _ _ _

@[reassoc]
theorem lamFst_snd {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y = c) :
    lamFst y c g hg ≫ pullback.snd y y = pullback.fst y c := pullback.lift_snd _ _ _

theorem isPullback_lamFst {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y)
    (hg : g ≫ y = c) : IsPullback (pullback.snd y c) (lamFst y c g hg) g (pullback.fst y y) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd y y) (v₂₂ := y) (h₃₁ :=
      y) ?_ (lamFst_fst y c g hg).symm
    (IsPullback.of_hasPullback y y)
  rw [lamFst_snd, hg]
  exact (IsPullback.of_hasPullback y c).flip

end Setup

section Piece

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) y)

/-- Insert a relative section as the first coordinate. -/
def sig : Y ⟶ pullback y y :=
  pullback.lift (y ≫ a.1) (𝟙 Y) (by rw [Category.assoc, a.2, Category.comp_id, Category.id_comp])

@[reassoc]
theorem sig_fst : sig y a ≫ pullback.fst y y = y ≫ a.1 := pullback.lift_fst _ _ _

@[reassoc]
theorem sig_snd : sig y a ≫ pullback.snd y y = 𝟙 Y := pullback.lift_snd _ _ _

theorem isPullback_sig : IsPullback (sig y a) y (pullback.fst y y) a.1 := by
  refine IsPullback.of_right (h₁₂ := pullback.snd y y) (v₁₃ := y) (h₂₂ := y) ?_ (sig_fst y a)
    (IsPullback.of_hasPullback y y).flip
  rw [sig_snd, a.2]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

/-- The open domain on which translation by the section is defined. -/
def Ua : Y.Opens := sig y a ⁻¹ᵁ U

/-- The section-insertion map restricted to the partial-law domain. -/
def zeta : (Ua y U a : Scheme.{u}) ⟶ U := sig y a ∣_ U

@[reassoc]
theorem zeta_ι : zeta y U a ≫ U.ι = (Ua y U a).ι ≫ sig y a := morphismRestrict_ι _ _

/-- Translation by the chosen section on its open domain. -/
def Phia : (Ua y U a : Scheme.{u}) ⟶ Y := zeta y U a ≫ m.1

@[reassoc]
theorem Phia_y : Phia y U m a ≫ y = (Ua y U a).ι ≫ y := by
  rw [Phia, Category.assoc, m.2, zeta_ι_assoc, sig_fst_assoc, a.2, Category.comp_id]

@[reassoc]
theorem Phia_sig : Phia y U m a ≫ sig y a = zeta y U a ≫ Phi y U m := by
  apply pullback.hom_ext
  · rw [Category.assoc, sig_fst, Phia_y_assoc, Category.assoc, pullback.lift_fst, zeta_ι_assoc,
      sig_fst]
  · rw [Category.assoc, sig_snd, Category.comp_id, Category.assoc, pullback.lift_snd, Phia]

theorem isPullback_Phia : IsPullback (Phia y U m a) (zeta y U a) (sig y a) (Phi y U m) := by
  refine IsPullback.of_right (h₁₂ := y) (v₁₃ := a.1) (h₂₂ := pullback.fst y y) ?_ (Phia_sig y U m a)
    (isPullback_sig y a).flip
  rw [Phia_y, pullback.lift_fst]
  exact ((isPullback_morphismRestrict (sig y a) U).paste_vert (isPullback_sig y a)).flip

theorem isOpenImmersion_Phia [IsOpenImmersion (Phi y U m)] : IsOpenImmersion (Phia y U m a) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_Phia y U m a).flip inferInstance

/-- The pair domain where the first input can be translated. -/
def Fa : (pullback y y).Opens := (pullback.fst y y ⁻¹ᵁ Ua y U a) ⊓ U

theorem Fa_le_fst : Fa y U a ≤ pullback.fst y y ⁻¹ᵁ Ua y U a := inf_le_left

theorem Fa_le_U : Fa y U a ≤ U := inf_le_right

/-- The first coordinate restricted to its translation domain. -/
def toUa : (Fa y U a : Scheme.{u}) ⟶ Ua y U a :=
  (pullback y y).homOfLE (Fa_le_fst y U a) ≫ (pullback.fst y y ∣_ Ua y U a)

@[reassoc]
theorem toUa_ι : toUa y U a ≫ (Ua y U a).ι = (Fa y U a).ι ≫ pullback.fst y y := by
  rw [toUa, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]

/-- The inclusion of the translated-pair domain in the partial-law domain. -/
def toU : (Fa y U a : Scheme.{u}) ⟶ U := (pullback y y).homOfLE (Fa_le_U y U a)

@[reassoc]
theorem toU_ι : toU y U a ≫ U.ι = (Fa y U a).ι := Scheme.homOfLE_ι _ _

scoped instance isOpenImmersion_toU : IsOpenImmersion (toU y U a) := by
  unfold toU
  infer_instance

/-- Translate the first coordinate on its inverse-image domain. -/
def ja' : ((pullback.fst y y ⁻¹ᵁ Ua y U a : (pullback y y).Opens) : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift ((pullback.fst y y ∣_ Ua y U a) ≫ Phia y U m a)
    ((pullback.fst y y ⁻¹ᵁ Ua y U a).ι ≫ pullback.snd y y)
    (by rw [Category.assoc, Phia_y, morphismRestrict_ι_assoc, Category.assoc, pullback.condition])

theorem isPullback_ja' :
    IsPullback (ja' y U m a) (pullback.fst y y ∣_ Ua y U a) (pullback.fst y y) (Phia y U m a) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd y y) (v₁₃ := y) (h₂₂ :=
      y) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback y y).flip
  rw [ja', pullback.lift_snd, Phia_y]
  exact (isPullback_morphismRestrict (pullback.fst y y) (Ua y U a)).flip.paste_horiz
    (IsPullback.of_hasPullback y y).flip

scoped instance isOpenImmersion_ja' [IsOpenImmersion (Phi y U m)] : IsOpenImmersion (ja' y U m a) :=
  have : IsOpenImmersion (Phia y U m a) := isOpenImmersion_Phia y U m a
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_ja' y U m a).flip inferInstance

/-- Translate the first coordinate on the common multiplication domain. -/
def ja : (Fa y U a : Scheme.{u}) ⟶ pullback y y :=
  (pullback y y).homOfLE (Fa_le_fst y U a) ≫ ja' y U m a

scoped instance isOpenImmersion_ja [IsOpenImmersion (Phi y U m)] : IsOpenImmersion (ja y U m a) :=
    by
  unfold ja; infer_instance

@[reassoc]
theorem ja_fst : ja y U m a ≫ pullback.fst y y = toUa y U a ≫ Phia y U m a := by
  rw [ja, Category.assoc, ja', pullback.lift_fst, toUa, Category.assoc]

@[reassoc]
theorem ja_snd : ja y U m a ≫ pullback.snd y y = (Fa y U a).ι ≫ pullback.snd y y := by
  rw [ja, Category.assoc, ja', pullback.lift_snd, Scheme.homOfLE_ι_assoc]

@[reassoc]
theorem ja_fst_y : ja y U m a ≫ pullback.fst y y ≫ y = (Fa y U a).ι ≫ pullback.fst y y ≫ y := by
  rw [ja_fst_assoc, Phia_y, toUa_ι_assoc]

/-- Compose partial multiplication with the proposed translation. -/
def ga {Y' : Scheme.{u}} {y' : Y' ⟶ Spec (CommRingCat.of R)} (τ : SchemeHomOver y y') :
    (Fa y U a : Scheme.{u}) ⟶ Y' :=
  toU y U a ≫ m.1 ≫ τ.1

theorem ga_y' {Y' : Scheme.{u}} {y' : Y' ⟶ Spec (CommRingCat.of R)} (τ : SchemeHomOver y y') :
    ga y U m a τ ≫ y' = ja y U m a ≫ pullback.fst y y ≫ y := by
  rw [ga, Category.assoc, Category.assoc, τ.2, m.2, toU_ι_assoc, ja_fst_y]

/-- Insert the product in the section chart. -/
def theta : (Fa y U a : Scheme.{u}) ⟶ pullback y y := (toU y U a ≫ m.1) ≫ sig y a

/-- The common open locus where the associativity comparison is defined. -/
def Ga : (Fa y U a : Scheme.{u}).Opens := (ja y U m a ⁻¹ᵁ U) ⊓ (theta y U m a ⁻¹ᵁ U)

theorem dense_Ua
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y)))) :
    Dense ((Ua y U a : Y.Opens) : Set Y) := by
  refine dense_of_forall_dense_fibre (fun c : Y => y c) _ fun s₀ => ?_
  rw [dense_fibre_iff y s₀]
  let c := (Spec (CommRingCat.of R)).fromSpecResidueField s₀
  have hg : (c ≫ a.1) ≫ y = c := by rw [Category.assoc, a.2, Category.comp_id]
  have hfac : pullback.fst y c ≫ sig y a = lamFst y c (c ≫ a.1) hg := by
    apply pullback.hom_ext
    · rw [Category.assoc, sig_fst, lamFst_fst, pullback.condition_assoc]
    · rw [Category.assoc, sig_snd, lamFst_snd, Category.comp_id]
  have hd : Dense ((lamFst y c (c ≫ a.1) hg) ⁻¹' (U : Set ↑(pullback y y))) :=
    dense_preimage_of_isPullback (pullback.fst y y) (a.1 s₀) (Spec.map
        (a.1.residueFieldMap s₀)) (c ≫ a.1)
      (by rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField])
      (isPullback_lamFst y c _ hg) _
      (hU₁ _)
  have h : (y.fiberι s₀) ⁻¹' ((Ua y U a : Y.Opens) : Set Y) = (lamFst y c (c ≫ a.1) hg) ⁻¹'
      (U : Set _) := by
    rw [← hfac]
    rfl
  rw [h]
  exact hd

theorem dense_theta_preimage [Smooth y] [IsOpenImmersion (Phi y U m)]
    (hUa : Dense ((Ua y U a : Y.Opens) : Set Y)) :
    Dense ((theta y U m a ⁻¹ᵁ U : (Fa y U a : Scheme.{u}).Opens) : Set (Fa y U a)) := by
  have : UniversallyOpen m.1 := universallyOpen_m y U m
  have h : ((theta y U m a ⁻¹ᵁ U : (Fa y U a : Scheme.{u}).Opens) : Set (Fa y U a)) =
      (toU y U a ≫ m.1) ⁻¹' ((Ua y U a : Y.Opens) : Set Y) := rfl
  rw [h]
  exact hUa.preimage (toU y U a ≫ m.1).isOpenMap

theorem dense_Ga [Smooth y] [IsOpenImmersion (Phi y U m)] (hU : Dense (U : Set ↑(pullback y y)))
    (hUa : Dense ((Ua y U a : Y.Opens) : Set Y)) :
    Dense ((Ga y U m a : (Fa y U a : Scheme.{u}).Opens) : Set (Fa y U a)) := by
  have h1 : Dense ((ja y U m a ⁻¹ᵁ U : (Fa y U a : Scheme.{u}).Opens) : Set (Fa y U a)) :=
    hU.preimage (ja y U m a).isOpenMap
  exact h1.inter_of_isOpen_left (dense_theta_preimage y U m a hUa) (ja y U m a ⁻¹ᵁ U).2

theorem agree_piece
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 →
          p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y →
          q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {Y' : Scheme.{u}} {y' : Y' ⟶ Spec (CommRingCat.of R)} (ι τ : SchemeHomOver y y')
    (hτa : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t y)
        (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        w.1 ≫ U.ι ≫ pullback.fst y y = t ≫ a.1 → w.1 ≫ U.ι ≫ pullback.snd y y = x.1 →
        x.1 ≫ τ.1 = w.1 ≫ m.1 ≫ ι.1)
    [IsOpenImmersion (Phi y U m)]
    {T : Scheme.{u}} (t₁ : T ⟶ Fa y U a) (w : T ⟶ U) (h : t₁ ≫ ja y U m a = w ≫ U.ι)
    (hG : ∀ p : T, t₁ p ∈ Ga y U m a) :
    t₁ ≫ ga y U m a τ = w ≫ m.1 ≫ ι.1 := by
  have hθ : Set.range (t₁ ≫ theta y U m a) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact (hG p).2
  let q' : T ⟶ U := IsOpenImmersion.lift U.ι (t₁ ≫ theta y U m a) hθ
  have hq' : q' ≫ U.ι = t₁ ≫ theta y U m a := IsOpenImmersion.lift_fac _ _ _
  let tT : T ⟶ Spec (CommRingCat.of R) := t₁ ≫ (Fa y U a).ι ≫ pullback.fst y y ≫ y
  let u : T ⟶ U := t₁ ≫ toUa y U a ≫ zeta y U a
  let v : T ⟶ U := t₁ ≫ toU y U a
  have hu : u ≫ U.ι = t₁ ≫ (Fa y U a).ι ≫ pullback.fst y y ≫ sig y a := by
    simp only [u, Category.assoc, zeta_ι, toUa_ι_assoc]
  have hv : v ≫ U.ι = t₁ ≫ (Fa y U a).ι := by simp only [v, Category.assoc, toU_ι]
  have hw : w ≫ U.ι = t₁ ≫ ja y U m a := h.symm
  have hq : q' ≫ U.ι = v ≫ m.1 ≫ sig y a := by
    rw [hq', theta]
    simp only [v, Category.assoc]
  have hmy : m.1 ≫ y = U.ι ≫ pullback.fst y y ≫ y := m.2
  have e1 : u ≫ U.ι ≫ pullback.snd y y = v ≫ U.ι ≫ pullback.fst y y := by
    rw [reassoc_of% hu, sig_snd, Category.comp_id, reassoc_of% hv]
  have e2 : w ≫ U.ι ≫ pullback.fst y y = u ≫ m.1 := by
    rw [reassoc_of% hw, ja_fst, Phia]
    simp only [u, Category.assoc]
  have e3 : w ≫ U.ι ≫ pullback.snd y y = v ≫ U.ι ≫ pullback.snd y y := by
    rw [reassoc_of% hw, ja_snd, reassoc_of% hv]
  have e4 : q' ≫ U.ι ≫ pullback.fst y y = u ≫ U.ι ≫ pullback.fst y y := by
    rw [reassoc_of% hq, sig_fst, reassoc_of% hmy, reassoc_of% hv, reassoc_of% hu, sig_fst]
  have e5 : q' ≫ U.ι ≫ pullback.snd y y = v ≫ m.1 := by
    rw [reassoc_of% hq, sig_snd, Category.comp_id]
  have hu' : u ≫ (U.ι ≫ pullback.fst y y ≫ y) = tT := by
    rw [reassoc_of% hu, sig_fst_assoc, a.2, Category.comp_id]
  have hv' : v ≫ (U.ι ≫ pullback.fst y y ≫ y) = tT := by rw [reassoc_of% hv]
  have hw' : w ≫ (U.ι ≫ pullback.fst y y ≫ y) = tT := by rw [reassoc_of% hw, ja_fst_y]
  have hq'' : q' ≫ (U.ι ≫ pullback.fst y y ≫ y) = tT := by
    calc q' ≫ (U.ι ≫ pullback.fst y y ≫ y) = (q' ≫ U.ι ≫ pullback.fst y y) ≫ y := by
          simp only [Category.assoc]
      _ = (u ≫ U.ι ≫ pullback.fst y y) ≫ y := by rw [e4]
      _ = tT := by simp only [Category.assoc]; exact hu'
  have hx : (v ≫ m.1) ≫ y = tT := by rw [Category.assoc, hmy, hv']
  have hqa : q' ≫ U.ι ≫ pullback.fst y y = tT ≫ a.1 := by
    rw [e4, reassoc_of% hu, sig_fst]
    simp only [tT, Category.assoc]
  have H1 : w ≫ m.1 = q' ≫ m.1 := hassoc tT ⟨u, hu'⟩ ⟨v, hv'⟩ ⟨w, hw'⟩ ⟨q', hq''⟩ e1 e2 e3 e4 e5
  have H2 : (v ≫ m.1) ≫ τ.1 = q' ≫ m.1 ≫ ι.1 := hτa tT ⟨v ≫ m.1, hx⟩ ⟨q', hq''⟩ hqa e5
  calc t₁ ≫ ga y U m a τ = (v ≫ m.1) ≫ τ.1 := by simp only [ga, v, Category.assoc]
    _ = q' ≫ m.1 ≫ ι.1 := H2
    _ = w ≫ m.1 ≫ ι.1 := by rw [reassoc_of% H1]

end Piece

section Level

/-- The spectrum map induced by the given algebra structure. -/
abbrev bS (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (R' : Type u) [CommRing R'] [Algebra R R'] (R'' : Type u) [CommRing R''] [Algebra R' R'']

/-- The first base change of the model. -/
abbrev Y1 : Scheme.{u} := pullback y (bS R R')

/-- The iterated base change of the model. -/
abbrev Y2 : Scheme.{u} := pullback y (bS R' R'' ≫ bS R R')

/-- The structure morphism of the first base change. -/
abbrev y1 : Y1 y R' ⟶ Spec (CommRingCat.of R') := pullback.snd y (bS R R')

/-- The structure morphism of the iterated base change. -/
abbrev y2 : Y2 y R' R'' ⟶ Spec (CommRingCat.of R'') := pullback.snd y (bS R' R'' ≫ bS R R')

/-- The first base-change projection to the original model. -/
abbrev p1 : Y1 y R' ⟶ Y := pullback.fst y (bS R R')

/-- The iterated base-change projection to the original model. -/
abbrev p2 : Y2 y R' R'' ⟶ Y := pullback.fst y (bS R' R'' ≫ bS R R')

/-- The transition map between the two base changes. -/
def r : Y2 y R' R'' ⟶ Y1 y R' :=
  pullback.lift (p2 y R' R'') (y2 y R' R'' ≫ bS R' R'')
      (by rw [Category.assoc]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem r_p1 : r y R' R'' ≫ p1 y R' = p2 y R' R'' := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem r_y1 : r y R' R'' ≫ y1 y R' = y2 y R' R'' ≫ bS R' R'' := pullback.lift_snd _ _ _

theorem isPullback_r : IsPullback (r y R' R'') (y2 y R' R'') (y1 y R') (bS R' R'') := by
  refine IsPullback.of_right (h₁₂ := p1 y R') (v₁₃ := y) (h₂₂ := bS R R') ?_ (r_y1 y R' R'')
    (IsPullback.of_hasPullback y (bS R R'))
  rw [r_p1]
  exact IsPullback.of_hasPullback y (bS R' R'' ≫ bS R R')

/-- The pair scheme over the first base ring. -/
abbrev P1 : Scheme.{u} := pullback (y1 y R') (y1 y R')

/-- The pair scheme over the second base ring. -/
abbrev P2 : Scheme.{u} := pullback (y2 y R' R'') (y2 y R' R'')

/-- The first base-change map on pair schemes. -/
def pi1 : P1 y R' ⟶ pullback y y :=
  pullback.map _ _ _ _ (p1 y R') (p1 y R') (bS R R') pullback.condition.symm pullback.condition.symm

/-- The second base-change map on pair schemes. -/
def pi2 : P2 y R' R'' ⟶ pullback y y :=
  pullback.map _ _ _ _ (p2 y R' R'') (p2 y R' R'') (bS R' R'' ≫ bS R R')
    pullback.condition.symm pullback.condition.symm

/-- The transition map between the base-changed pair schemes. -/
def rho : P2 y R' R'' ⟶ P1 y R' :=
  pullback.map _ _ _ _ (r y R' R'') (r y R' R'') (bS R' R'') (r_y1 y R' R'').symm
      (r_y1 y R' R'').symm

@[reassoc (attr := simp)]
theorem pi1_fst : pi1 y R' ≫ pullback.fst y y = pullback.fst _ _ ≫ p1 y R' :=
    pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pi1_snd : pi1 y R' ≫ pullback.snd y y = pullback.snd _ _ ≫ p1 y R' :=
    pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem pi2_fst : pi2 y R' R'' ≫ pullback.fst y y = pullback.fst _ _ ≫ p2 y R' R'' :=
    pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pi2_snd : pi2 y R' R'' ≫ pullback.snd y y = pullback.snd _ _ ≫ p2 y R' R'' :=
    pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem rho_fst : rho y R' R'' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r y R' R'' :=
    pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem rho_snd : rho y R' R'' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ r y R' R'' :=
    pullback.lift_snd _ _ _

@[reassoc]
theorem rho_pi1 : rho y R' R'' ≫ pi1 y R' = pi2 y R' R'' := by
  apply pullback.hom_ext
  · rw [Category.assoc, pi1_fst, rho_fst_assoc, r_p1, pi2_fst]
  · rw [Category.assoc, pi1_snd, rho_snd_assoc, r_p1, pi2_snd]

theorem isPullback_pi1_fst :
    IsPullback (pi1 y R') (pullback.fst (y1 y R') (y1 y R')) (pullback.fst y y) (p1 y R') := by
  refine IsPullback.of_right (h₁₂ := pullback.snd y y) (v₁₃ := y) (h₂₂ := y) ?_ (pi1_fst y R')
    (IsPullback.of_hasPullback y y).flip
  rw [pi1_snd]
  have h := (IsPullback.of_hasPullback (y1 y R') (y1 y R')).flip.paste_horiz
    (IsPullback.of_hasPullback y (bS R R'))
  rwa [← pullback.condition] at h

theorem isPullback_pi2_fst :
    IsPullback (pi2 y R' R'') (pullback.fst (y2 y R' R'') (y2 y R' R'')) (pullback.fst y y)
        (p2 y R' R'') := by
  refine IsPullback.of_right (h₁₂ := pullback.snd y y) (v₁₃ := y) (h₂₂ := y) ?_ (pi2_fst y R' R'')
    (IsPullback.of_hasPullback y y).flip
  rw [pi2_snd]
  have h := (IsPullback.of_hasPullback (y2 y R' R'') (y2 y R' R'')).flip.paste_horiz
    (IsPullback.of_hasPullback y (bS R' R'' ≫ bS R R'))
  rwa [← pullback.condition] at h

theorem isPullback_pi2_snd :
    IsPullback (pi2 y R' R'') (pullback.snd (y2 y R' R'') (y2 y R' R'')) (pullback.snd y y)
        (p2 y R' R'') := by
  refine IsPullback.of_right (h₁₂ := pullback.fst y y) (v₁₃ := y) (h₂₂ := y) ?_ (pi2_snd y R' R'')
    (IsPullback.of_hasPullback y y)
  rw [pi2_fst]
  have h := (IsPullback.of_hasPullback (y2 y R' R'') (y2 y R' R'')).paste_horiz
    (IsPullback.of_hasPullback y (bS R' R'' ≫ bS R R'))
  rwa [← pullback.condition] at h

theorem isPullback_pi2_base :
    IsPullback (pi2 y R' R'') (pullback.fst (y2 y R' R'') (y2 y R' R'') ≫ y2 y R' R'')
      (pullback.fst y y ≫ y) (bS R' R'' ≫ bS R R') :=
  (isPullback_pi2_fst y R' R'').paste_vert (IsPullback.of_hasPullback y (bS R' R'' ≫ bS R R'))

theorem isPullback_rho_snd :
    IsPullback (rho y R' R'') (pullback.snd (y2 y R' R'') (y2 y R' R'')) (pullback.snd
        (y1 y R') (y1 y R'))
      (r y R' R'') := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (y1 y R') (y1 y R')) (v₁₃ := y1 y R') (h₂₂ :=
      y1 y R') ?_
    (rho_snd y R' R'') (IsPullback.of_hasPullback (y1 y R') (y1 y R'))
  rw [rho_fst]
  have h := (IsPullback.of_hasPullback (y2 y R' R'') (y2 y R' R'')).paste_horiz
      (isPullback_r y R' R'')
  rwa [← r_y1] at h

scoped instance etale_bS [Algebra.Etale R' R''] : Etale (bS R' R'') := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
  infer_instance

scoped instance etale_r [Algebra.Etale R' R''] : Etale (r y R' R'') :=
  MorphismProperty.of_isPullback (P := @Etale) (isPullback_r y R' R'').flip inferInstance

scoped instance etale_rho [Algebra.Etale R' R''] : Etale (rho y R' R'') :=
  MorphismProperty.of_isPullback (P := @Etale) (isPullback_rho_snd y R' R'').flip inferInstance

variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

/-- The partial-law domain after the second base change. -/
abbrev U2 : (P2 y R' R'').Opens := pi2 y R' R'' ⁻¹ᵁ U

/-- The base-change map restricted to the partial-law domain. -/
abbrev piU : (U2 y R' R'' U : Scheme.{u}) ⟶ U := pi2 y R' R'' ∣_ U

@[reassoc]
theorem piU_ι : piU y R' R'' U ≫ U.ι = (U2 y R' R'' U).ι ≫ pi2 y R' R'' := morphismRestrict_ι _ _

@[reassoc]
theorem piU_fst : piU y R' R'' U ≫ U.ι ≫ pullback.fst y y =
    (U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ p2 y R' R'' := by
  rw [piU_ι_assoc, pi2_fst]

@[reassoc]
theorem piU_snd : piU y R' R'' U ≫ U.ι ≫ pullback.snd y y =
    (U2 y R' R'' U).ι ≫ pullback.snd _ _ ≫ p2 y R' R'' := by
  rw [piU_ι_assoc, pi2_snd]

theorem m2_w : (piU y R' R'' U ≫ m.1) ≫ y =
    ((U2 y R' R'' U).ι ≫ pullback.fst (y2 y R' R'') (y2 y R' R'') ≫ y2 y R' R'') ≫ (bS R' R'' ≫
        bS R R') := by
  rw [Category.assoc, m.2, piU_fst_assoc, Category.assoc, Category.assoc, ← pullback.condition]

/-- The partial multiplication after the second base change. -/
def m2 : SchemeHomOver ((U2 y R' R'' U).ι ≫ pullback.fst (y2 y R' R'') (y2 y R' R'') ≫ y2 y R' R'')
    (y2 y R' R'') :=
  ⟨pullback.lift (piU y R' R'' U ≫ m.1) ((U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R'')
      (m2_w y R' R'' U m),
    pullback.lift_snd _ _ _⟩

@[reassoc (attr := simp)]
theorem m2_p2 : (m2 y R' R'' U m).1 ≫ p2 y R' R'' = piU y R' R'' U ≫ m.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem m2_y2 : (m2 y R' R'' U m).1 ≫ y2 y R' R'' = (U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫
    y2 y R' R'' :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem Phi2_pi2 : Phi (y2 y R' R'') (U2 y R' R'' U) (m2 y R' R'' U m) ≫ pi2 y R' R'' =
    piU y R' R'' U ≫ Phi y U m := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pi2_fst, pullback.lift_fst, pullback.lift_fst_assoc, piU_fst]
  · simp only [Category.assoc, pi2_snd, pullback.lift_snd, pullback.lift_snd_assoc, m2_p2]

theorem isPullback_Phi2 :
    IsPullback (Phi (y2 y R' R'') (U2 y R' R'' U) (m2 y R' R'' U m)) (piU y R' R'' U) (pi2 y R' R'')
      (Phi y U m) := by
  have HU : IsPullback (piU y R' R'' U) ((U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R'')
      (U.ι ≫ pullback.fst y y ≫ y) (bS R' R'' ≫ bS R R') :=
    (isPullback_morphismRestrict (pi2 y R' R'') U).paste_vert (isPullback_pi2_base y R' R'')
  refine (IsPullback.of_bot (h₁₁ := piU y R' R'' U) (v₁₁ :=
      Phi (y2 y R' R'') (U2 y R' R'' U) (m2 y R' R'' U m))
    (v₁₂ := Phi y U m) ?_ (Phi2_pi2 y R' R'' U m).symm (isPullback_pi2_base y R' R'')).flip
  rwa [pullback.lift_fst_assoc, pullback.lift_fst_assoc]

scoped instance isOpenImmersion_Phi2 [IsOpenImmersion (Phi y U m)] :
    IsOpenImmersion (Phi (y2 y R' R'') (U2 y R' R'' U) (m2 y R' R'' U m)) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_Phi2 y R' R'' U m).flip inferInstance

theorem dense_fibre_U2
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (x₂ : Y2 y R' R'') :
    Dense ((Subtype.val : {q : ↑(P2 y R' R'') // (pullback.fst (y2 y R' R'')
        (y2 y R' R'')).base q = x₂} →
      ↑(P2 y R' R'')) ⁻¹' (U2 y R' R'' U : Set ↑(P2 y R' R''))) :=
  dense_fibre_of_isPullback (pullback.fst y y) (pullback.fst _ _) (pi2 y R' R'') (p2 y R' R'')
    (isPullback_pi2_fst y R' R'') x₂ _ (hU₁ _)

theorem dense_U2
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y)))) :
    Dense (U2 y R' R'' U : Set ↑(P2 y R' R'')) :=
  dense_of_forall_dense_fibre (fun q => (pullback.fst (y2 y R' R'') (y2 y R' R'')).base q) _
    (dense_fibre_U2 y R' R'' U hU₁)

theorem hassoc2
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 →
          p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y →
          q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R''))
    (u v p q : SchemeHomOver t ((U2 y R' R'' U).ι ≫ pullback.fst (y2 y R' R'') (y2 y R' R'') ≫
        y2 y R' R''))
    (h₁ : u.1 ≫ (U2 y R' R'' U).ι ≫ pullback.snd _ _ = v.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _)
    (h₂ : p.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _ = u.1 ≫ (m2 y R' R'' U m).1)
    (h₃ : p.1 ≫ (U2 y R' R'' U).ι ≫ pullback.snd _ _ = v.1 ≫ (U2 y R' R'' U).ι ≫ pullback.snd _ _)
    (h₄ : q.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _ = u.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _)
    (h₅ : q.1 ≫ (U2 y R' R'' U).ι ≫ pullback.snd _ _ = v.1 ≫ (m2 y R' R'' U m).1) :
    p.1 ≫ (m2 y R' R'' U m).1 = q.1 ≫ (m2 y R' R'' U m).1 := by
  let t₀ : T ⟶ Spec (CommRingCat.of R) := t ≫ bS R' R'' ≫ bS R R'
  have hdn : ∀ z : SchemeHomOver t ((U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R''),
      (z.1 ≫ piU y R' R'' U) ≫ (U.ι ≫ pullback.fst y y ≫ y) = t₀ := by
    intro z
    have hz : z.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R'' = t := z.2
    simp only [Category.assoc, t₀]
    rw [piU_fst_assoc, pullback.condition (f := y) (g := bS R' R'' ≫ bS R R'), reassoc_of% hz]
  have hf : ∀ z : T ⟶ (U2 y R' R'' U : Scheme.{u}), (z ≫ piU y R' R'' U) ≫ U.ι ≫ pullback.fst y y =
      z ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ p2 y R' R'' := by
    intro z; rw [Category.assoc, piU_fst]
  have hs : ∀ z : T ⟶ (U2 y R' R'' U : Scheme.{u}), (z ≫ piU y R' R'' U) ≫ U.ι ≫ pullback.snd y y =
      z ≫ (U2 y R' R'' U).ι ≫ pullback.snd _ _ ≫ p2 y R' R'' := by
    intro z; rw [Category.assoc, piU_snd]
  have hm : ∀ z : T ⟶ (U2 y R' R'' U : Scheme.{u}), (z ≫ piU y R' R'' U) ≫ m.1 =
      z ≫ (m2 y R' R'' U m).1 ≫ p2 y R' R'' := by
    intro z; rw [Category.assoc, m2_p2]
  have H := hassoc t₀ ⟨_, hdn u⟩ ⟨_, hdn v⟩ ⟨_, hdn p⟩ ⟨_, hdn q⟩
    (by rw [hs, hf, reassoc_of% h₁])
    (by rw [hf, hm, reassoc_of% h₂])
    (by rw [hs, hs, reassoc_of% h₃])
    (by rw [hf, hf, reassoc_of% h₄])
    (by rw [hs, hm, reassoc_of% h₅])
  apply pullback.hom_ext
  · simpa only [Category.assoc, m2_p2] using H
  · have hp : p.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R'' = t := p.2
    have hq : q.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R'' = t := q.2
    simp only [Category.assoc, m2_y2]
    rw [hp, hq]

end Level

/-- The model, partial law, base changes and translation data. -/
structure Ctx where
  /-- The initial base ring. -/
  R : Type u
  /-- The given CommRing R structure. -/
  [instR : CommRing R]
  /-- The initial model. -/
  Y : Scheme.{u}
  /-- The initial structure morphism. -/
  y : Y ⟶ Spec (CommRingCat.of R)
  /-- The given Smooth y structure. -/
  [smooth : Smooth y]
  /-- The initial partial-law domain. -/
  U : (pullback y y).Opens
  /-- The initial partial multiplication. -/
  m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y
  /-- The domain is dense on each first-projection fiber. -/
  hU₁ : ∀ x : Y,
    Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
        ↑(pullback y y)) ⁻¹'
        (U : Set ↑(pullback y y)))
  /-- The left translation graph is an open immersion. -/
  hΦ : IsOpenImmersion (Phi y U m)
  /-- The partial multiplication is associative wherever both sides are defined. -/
  hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
    u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
    p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 →
        p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
    q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y →
        q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
    p.1 ≫ m.1 = q.1 ≫ m.1
  /-- The first extended base ring. -/
  R' : Type u
  /-- The given CommRing R' structure. -/
  [instR' : CommRing R']
  /-- The given Algebra R R' structure. -/
  [alg : Algebra R R']
  /-- The enlarged model. -/
  Y' : Scheme.{u}
  /-- The enlarged structure morphism. -/
  y' : Y' ⟶ Spec (CommRingCat.of R')
  /-- The given IsSeparated y' structure. -/
  [sep : IsSeparated y']
  /-- The comparison map to the enlarged model. -/
  ι : SchemeHomOver (y1 y R') y'
  /-- The second extended base ring. -/
  R'' : Type u
  /-- The given CommRing R'' structure. -/
  [instR'' : CommRing R'']
  /-- The given IsDomain R'' structure. -/
  [dom : IsDomain R'']
  /-- The given IsDiscreteValuationRing R'' structure. -/
  [dvr : IsDiscreteValuationRing R'']
  /-- The given Algebra R' R'' structure. -/
  [alg' : Algebra R' R'']
  /-- The given Algebra.Etale R' R'' structure. -/
  [etale : Algebra.Etale R' R'']
  /-- The translating section. -/
  a : Spec (CommRingCat.of R'') ⟶ Y
  /-- The translating section is over the prescribed base map. -/
  ha : a ≫ y = bS R' R'' ≫ bS R R'
  /-- The translation morphism. -/
  τ : Y2 y R' R'' ⟶ pullback y' (bS R' R'')
  /-- The translation morphism respects the base. -/
  hτ₁ : τ ≫ pullback.snd y' (bS R' R'') = y2 y R' R''
  /-- The translation agrees with multiplication where defined. -/
  hτ₂ : ∀ {T : Scheme.{u}} (x : T ⟶ Y2 y R' R'') (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ Y1 y R'),
      w ≫ U.ι ≫ pullback.fst y y = x ≫ y2 y R' R'' ≫ a →
      w ≫ U.ι ≫ pullback.snd y y = x ≫ p2 y R' R'' →
      v ≫ p1 y R' = w ≫ m.1 →
      v ≫ y1 y R' = x ≫ y2 y R' R'' ≫ bS R' R'' →
      x ≫ τ ≫ pullback.fst y' (bS R' R'') = v ≫ ι.1

attribute [local instance] Ctx.instR Ctx.smooth Ctx.hΦ Ctx.instR' Ctx.alg Ctx.sep
  Ctx.instR'' Ctx.dom Ctx.dvr Ctx.alg' Ctx.etale

namespace Ctx

variable (C : Ctx.{u})

/-- The translating section viewed on the second base change. -/
def a2 : SchemeHomOver (𝟙 (Spec (CommRingCat.of C.R''))) (y2 C.y C.R' C.R'') :=
  ⟨pullback.lift C.a (𝟙 _) (by rw [C.ha, Category.id_comp]), pullback.lift_snd _ _ _⟩

@[reassoc]
theorem a2_p2 : C.a2.1 ≫ p2 C.y C.R' C.R'' = C.a := pullback.lift_fst _ _ _

/-- The base change of the comparison map to the separated model. -/
def ι2 : SchemeHomOver (y2 C.y C.R' C.R'') (pullback.snd C.y' (bS C.R' C.R'')) :=
  ⟨pullback.lift (r C.y C.R' C.R'' ≫ C.ι.1) (y2 C.y C.R' C.R'')
      (by rw [Category.assoc, C.ι.2, r_y1]),
    pullback.lift_snd _ _ _⟩

@[reassoc]
theorem ι2_fst : C.ι2.1 ≫ pullback.fst C.y' (bS C.R' C.R'') = r C.y C.R' C.R'' ≫ C.ι.1 :=
    pullback.lift_fst _ _ _

/-- The proposed translation as a morphism over the second base. -/
def τ2 : SchemeHomOver (y2 C.y C.R' C.R'') (pullback.snd C.y' (bS C.R' C.R'')) := ⟨C.τ, C.hτ₁⟩

/-- The second base-changed partial-law domain. -/
abbrev U₂ : (P2 C.y C.R' C.R'').Opens := U2 C.y C.R' C.R'' C.U

/-- The second base-changed partial law. -/
abbrev m₂ := m2 C.y C.R' C.R'' C.U C.m

theorem hτa2 {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of C.R'')) (x : SchemeHomOver t
    (y2 C.y C.R' C.R''))
    (w : SchemeHomOver t (C.U₂.ι ≫ pullback.fst _ _ ≫ y2 C.y C.R' C.R''))
    (h₁ : w.1 ≫ C.U₂.ι ≫ pullback.fst _ _ = t ≫ C.a2.1)
    (h₂ : w.1 ≫ C.U₂.ι ≫ pullback.snd _ _ = x.1) :
    x.1 ≫ C.τ2.1 = w.1 ≫ C.m₂.1 ≫ C.ι2.1 := by
  have hx : x.1 ≫ y2 C.y C.R' C.R'' = t := x.2
  have hw : w.1 ≫ C.U₂.ι ≫ pullback.fst _ _ ≫ y2 C.y C.R' C.R'' = t := w.2
  have H := C.hτ₂ x.1 (w.1 ≫ piU C.y C.R' C.R'' C.U) (w.1 ≫ C.m₂.1 ≫ r C.y C.R' C.R'')
    (by rw [Category.assoc, piU_fst, reassoc_of% h₁, a2_p2, reassoc_of% hx])
    (by rw [Category.assoc, piU_snd, reassoc_of% h₂])
    (by simp only [Category.assoc, r_p1, m2_p2])
    (by simp only [Category.assoc, r_y1, m2_y2_assoc]; rw [reassoc_of% hw, reassoc_of% hx])
  apply pullback.hom_ext
  · simpa only [τ2, Category.assoc, ι2_fst] using H
  · have e₂ := C.ι2.2
    simp only [τ2, Category.assoc, C.hτ₁, hx]
    rw [e₂, m2_y2, hw]

/-- The open domain for the translated pair. -/
abbrev F : (P2 C.y C.R' C.R'').Opens := Fa (y2 C.y C.R' C.R'') C.U₂ C.a2

/-- The translated-pair morphism. -/
abbrev j : (C.F : Scheme.{u}) ⟶ P2 C.y C.R' C.R'' := ja (y2 C.y C.R' C.R'') C.U₂ C.m₂ C.a2

/-- The translated partial product over the second base. -/
abbrev g2 : (C.F : Scheme.{u}) ⟶ pullback C.y' (bS C.R' C.R'') :=
    ga (y2 C.y C.R' C.R'') C.U₂ C.m₂ C.a2 C.τ2

/-- The translated partial product mapped to the separated model. -/
def g : (C.F : Scheme.{u}) ⟶ C.Y' := C.g2 ≫ pullback.fst C.y' (bS C.R' C.R'')

/-- The descent map from translated pairs to the first pair scheme. -/
def f0 : (C.F : Scheme.{u}) ⟶ P1 C.y C.R' := C.j ≫ rho C.y C.R' C.R''

@[reassoc]
theorem f0_fst : C.f0 ≫ pullback.fst _ _ = C.j ≫ pullback.fst _ _ ≫ r C.y C.R' C.R'' := by
  rw [f0, Category.assoc, rho_fst]

@[reassoc]
theorem f0_snd : C.f0 ≫ pullback.snd _ _ = C.j ≫ pullback.snd _ _ ≫ r C.y C.R' C.R'' := by
  rw [f0, Category.assoc, rho_snd]

@[reassoc]
theorem f0_pi1 : C.f0 ≫ pi1 C.y C.R' = C.j ≫ pi2 C.y C.R' C.R'' := by
  rw [f0, Category.assoc, rho_pi1]

theorem isOpenMap_f0 : IsOpenMap C.f0.base := by
  rw [f0]; exact (C.j ≫ rho C.y C.R' C.R'').isOpenMap

@[reassoc]
theorem g_y' : C.g ≫ C.y' = C.f0 ≫ pullback.fst _ _ ≫ y1 C.y C.R' := by
  have h : C.g2 ≫ pullback.snd C.y' (bS C.R' C.R'') = C.j ≫ pullback.fst _ _ ≫ y2 C.y C.R' C.R'' :=
    ga_y' (y2 C.y C.R' C.R'') C.U₂ C.m₂ C.a2 C.τ2
  rw [g, Category.assoc, pullback.condition, reassoc_of% h, f0_fst_assoc, r_y1]

/-- The locus on which the translated pair lies in the partial-law domain. -/
abbrev O : (C.F : Scheme.{u}).Opens := C.j ⁻¹ᵁ C.U₂

/-- The translated-pair map restricted to the partial-law domain. -/
def wO : (C.O : Scheme.{u}) ⟶ C.U₂ :=
  IsOpenImmersion.lift C.U₂.ι (C.O.ι ≫ C.j) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact p.2)

@[reassoc]
theorem wO_ι : C.wO ≫ C.U₂.ι = C.O.ι ≫ C.j := IsOpenImmersion.lift_fac _ _ _

scoped instance isReduced_P2 : IsReduced (P2 C.y C.R' C.R'') :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    (pullback.fst (y2 C.y C.R' C.R'') (y2 C.y C.R' C.R'') ≫ y2 C.y C.R' C.R'')

theorem O_agree : C.O.ι ≫ C.g2 = C.wO ≫ C.m₂.1 ≫ C.ι2.1 := by
  let WO : (C.O : Scheme.{u}).Opens := C.O.ι ⁻¹ᵁ (theta (y2 C.y C.R' C.R'') C.U₂ C.m₂ C.a2 ⁻¹ᵁ C.U₂)
  have hWO : Dense (WO : Set C.O) :=
    (dense_theta_preimage (y2 C.y C.R' C.R'') C.U₂ C.m₂ C.a2
      (dense_Ua (y2 C.y C.R' C.R'') C.U₂ C.a2
          (dense_fibre_U2 C.y C.R' C.R'' C.U C.hU₁))).preimage C.O.ι.isOpenMap
  refine eq_of_comp_ι_eq (pullback.snd C.y' (bS C.R' C.R'')) ?_ WO hWO ?_
  · have e₂ := C.ι2.2
    rw [Category.assoc, ga_y', Category.assoc, Category.assoc, e₂, m2_y2, wO_ι_assoc]
  · rw [← Category.assoc, ← Category.assoc]
    refine agree_piece (y2 C.y C.R' C.R'') C.U₂ C.m₂ C.a2
      (fun t u v p q => hassoc2 C.y C.R' C.R'' C.U C.m C.hassoc t u v p q) C.ι2 C.τ2
      (fun t x w => C.hτa2 t x w) _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, wO_ι]
    · intro p
      refine ⟨?_, p.2⟩
      change C.j p.1.1 ∈ C.U₂
      exact p.1.2

@[reassoc]
theorem O_g : C.O.ι ≫ C.g = C.wO ≫ C.m₂.1 ≫ r C.y C.R' C.R'' ≫ C.ι.1 := by
  rw [g, reassoc_of% C.O_agree, ι2_fst]

theorem g_eq_of_O {T : Scheme.{u}} (o : T ⟶ (C.O : Scheme.{u})) (w : T ⟶ (C.U : Scheme.{u}))
    (hw : w ≫ C.U.ι = o ≫ C.wO ≫ piU C.y C.R' C.R'' C.U ≫ C.U.ι)
    (v : T ⟶ Y1 C.y C.R') (hv₁ : v ≫ p1 C.y C.R' = w ≫ C.m.1)
    (hv₂ : v ≫ y1 C.y C.R' = o ≫ C.O.ι ≫ C.f0 ≫ pullback.fst _ _ ≫ y1 C.y C.R') :
    o ≫ C.O.ι ≫ C.g = v ≫ C.ι.1 := by
  have hw' : w = o ≫ C.wO ≫ piU C.y C.R' C.R'' C.U := by
    rw [← cancel_mono C.U.ι, hw]; simp only [Category.assoc]
  rw [O_g]
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, r_p1, m2_p2]
    rw [hv₁, hw']; simp only [Category.assoc]
  · simp only [Category.assoc, r_y1, m2_y2_assoc]
    rw [hv₂, wO_ι_assoc, f0_fst_assoc, r_y1]

/-- The open image of the translated-pair descent map. -/
def V : (P1 C.y C.R').Opens := ⟨Set.range C.f0.base, C.isOpenMap_f0.isOpen_range⟩

/-- The inverse image of the open descent image. -/
abbrev FV : (C.F : Scheme.{u}).Opens := C.f0 ⁻¹ᵁ C.V

scoped instance etale_f0 : Etale C.f0 := by rw [f0]; infer_instance

/-- The surjective étale map onto the open descent image. -/
def c : (C.FV : Scheme.{u}) ⟶ C.V := C.f0 ∣_ C.V

scoped instance etale_c : Etale C.c := by rw [c]; infer_instance

scoped instance surjective_c : Surjective C.c := ⟨by
  rintro ⟨_, x, rfl⟩
  refine ⟨⟨x, ⟨x, rfl⟩⟩, Subtype.ext ?_⟩
  rw [c]
  exact morphismRestrict_base_coe _ _ _⟩

@[reassoc]
theorem FVι_f0 : C.FV.ι ≫ C.f0 = C.c ≫ C.V.ι := by rw [c]; exact (morphismRestrict_ι _ _).symm

/-- The translated partial product restricted to the descent cover. -/
def g' : (C.FV : Scheme.{u}) ⟶ C.Y' := C.FV.ι ≫ C.g

theorem key {T : Scheme.{u}} (i : T ⟶ (C.FV : Scheme.{u})) (hi : ∀ p : T, (i ≫ C.FV.ι) p ∈ C.O) :
    ∃ (w : T ⟶ (C.U : Scheme.{u})) (v : T ⟶ Y1 C.y C.R'),
      w ≫ C.U.ι = i ≫ C.c ≫ C.V.ι ≫ pi1 C.y C.R' ∧
      v ≫ p1 C.y C.R' = w ≫ C.m.1 ∧
      v ≫ y1 C.y C.R' = i ≫ C.c ≫ C.V.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R' ∧
      i ≫ C.g' = v ≫ C.ι.1 := by
  let t : T ⟶ (C.F : Scheme.{u}) := i ≫ C.FV.ι
  have hr : Set.range t.base ⊆ (C.O : Set C.F) := by
    rintro _ ⟨p, rfl⟩; exact hi p
  let o := IsOpenImmersion.lift C.O.ι t (by rwa [Scheme.Opens.range_ι])
  have ho : o ≫ C.O.ι = t := IsOpenImmersion.lift_fac _ _ _
  let w : T ⟶ (C.U : Scheme.{u}) := o ≫ C.wO ≫ piU C.y C.R' C.R'' C.U
  have hw : w ≫ C.U.ι = i ≫ C.c ≫ C.V.ι ≫ pi1 C.y C.R' := by
    simp only [w, Category.assoc]
    rw [piU_ι, wO_ι_assoc, reassoc_of% ho, ← f0_pi1]
    simp only [t, Category.assoc]
    rw [FVι_f0_assoc]
  have hvw : (w ≫ C.m.1) ≫ C.y = (i ≫ C.c ≫ C.V.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R') ≫
      bS C.R C.R' := by
    rw [Category.assoc, C.m.2, reassoc_of% hw, pi1_fst_assoc, pullback.condition (f := C.y) (g :=
        bS C.R C.R')]
    simp only [Category.assoc]
  refine ⟨w, pullback.lift _ _ hvw, hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  have := C.g_eq_of_O o w
      (by simp only [w, Category.assoc]) (pullback.lift _ _ hvw) (pullback.lift_fst _ _ _)
    (by
      rw [pullback.lift_snd, reassoc_of% ho]
      simp only [t, Category.assoc]
      rw [FVι_f0_assoc])
  rw [reassoc_of% ho] at this
  rw [g']
  simpa only [t, Category.assoc] using this

theorem desc_cond {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ (C.FV : Scheme.{u})) (h : g₁ ≫ C.c = g₂ ≫ C.c) :
    g₁ ≫ C.g' = g₂ ≫ C.g' := by
  let k : Z ⟶ pullback C.c C.c := pullback.lift g₁ g₂ h
  suffices H : pullback.fst C.c C.c ≫ C.g' = pullback.snd C.c C.c ≫ C.g' by
    have := congrArg (k ≫ ·) H
    simpa only [k, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
  have : IsReduced (pullback C.c C.c) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (pullback.fst C.c C.c ≫ C.FV.ι ≫ C.F.ι ≫ pullback.fst (y2 C.y C.R' C.R'')
          (y2 C.y C.R' C.R'') ≫ y2 C.y C.R' C.R'')
  let W : (pullback C.c C.c).Opens := ((pullback.fst C.c C.c ≫ C.FV.ι) ⁻¹ᵁ C.O) ⊓
      ((pullback.snd C.c C.c ≫ C.FV.ι) ⁻¹ᵁ C.O)
  have hO : Dense (C.O : Set C.F) := (dense_U2 C.y C.R' C.R'' C.U C.hU₁).preimage C.j.isOpenMap
  have hW : Dense (W : Set ↑(pullback C.c C.c)) := by
    refine Dense.inter_of_isOpen_left ?_ ?_ (TopologicalSpace.Opens.isOpen _)
    · exact hO.preimage (pullback.fst C.c C.c ≫ C.FV.ι).isOpenMap
    · exact hO.preimage (pullback.snd C.c C.c ≫ C.FV.ι).isOpenMap
  refine eq_of_comp_ι_eq C.y' ?_ W hW ?_
  · rw [g', Category.assoc, Category.assoc, Category.assoc, Category.assoc, g_y', FVι_f0_assoc,
      pullback.condition_assoc]
  · obtain ⟨w₁, v₁, hw₁, hv₁, hv₁', H₁⟩ := C.key (W.ι ≫ pullback.fst C.c C.c) (fun p => p.2.1)
    obtain ⟨w₂, v₂, hw₂, hv₂, hv₂', H₂⟩ := C.key (W.ι ≫ pullback.snd C.c C.c) (fun p => p.2.2)
    simp only [Category.assoc] at H₁ H₂
    rw [H₁, H₂]
    congr 1
    have hw12 : w₁ = w₂ := by
      rw [← cancel_mono C.U.ι, hw₁, hw₂]
      simp only [Category.assoc, pullback.condition_assoc]
    apply pullback.hom_ext
    · rw [hv₁, hv₂, hw12]
    · rw [hv₁', hv₂']
      simp only [Category.assoc, pullback.condition_assoc]

/-- The translated partial product descended to the open image. -/
def G : (C.V : Scheme.{u}) ⟶ C.Y' :=
  EffectiveEpi.desc C.c C.g' (fun g₁ g₂ h => C.desc_cond g₁ g₂ h)

theorem c_G : C.c ≫ C.G = C.g' := EffectiveEpi.fac _ _ _

theorem G_y' : C.G ≫ C.y' = C.V.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R' := by
  have : Epi C.c := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi C.c, reassoc_of% C.c_G, g', Category.assoc, g_y', FVι_f0_assoc]

theorem G_agree {T : Scheme.{u}} (s : T ⟶ (C.V : Scheme.{u})) (w : T ⟶ (C.U : Scheme.{u}))
    (v : T ⟶ Y1 C.y C.R')
    (h₁ : s ≫ C.V.ι ≫ pullback.fst _ _ ≫ p1 C.y C.R' = w ≫ C.U.ι ≫ pullback.fst C.y C.y)
    (h₂ : s ≫ C.V.ι ≫ pullback.snd _ _ ≫ p1 C.y C.R' = w ≫ C.U.ι ≫ pullback.snd C.y C.y)
    (h₃ : v ≫ p1 C.y C.R' = w ≫ C.m.1)
    (h₄ : v ≫ y1 C.y C.R' = s ≫ C.V.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R') :
    s ≫ C.G = v ≫ C.ι.1 := by
  have : Epi (pullback.fst s C.c) := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi (pullback.fst s C.c), ← Category.assoc, pullback.condition, Category.assoc,
      C.c_G]
  have hsw : s ≫ C.V.ι ≫ pi1 C.y C.R' = w ≫ C.U.ι := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pi1_fst] using h₁
    · simpa only [Category.assoc, pi1_snd] using h₂
  have hi : ∀ p, (pullback.snd s C.c ≫ C.FV.ι) p ∈ C.O := by
    intro p
    change ((pullback.snd s C.c ≫ C.FV.ι) ≫ C.j ≫ pi2 C.y C.R' C.R'') p ∈ C.U
    rw [← f0_pi1, Category.assoc, FVι_f0_assoc, ← pullback.condition_assoc, hsw,
        Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact (w _).2
  obtain ⟨w', v', hw', hv', hv'', H⟩ := C.key (pullback.snd s C.c) hi
  rw [H, ← Category.assoc]
  congr 1
  have hww : w' = pullback.fst s C.c ≫ w := by
    rw [← cancel_mono C.U.ι, hw', Category.assoc, ← hsw, pullback.condition_assoc]
  apply pullback.hom_ext
  · rw [hv', Category.assoc, h₃, hww, Category.assoc]
  · rw [hv'', Category.assoc, h₄, pullback.condition_assoc]

theorem range_subset_V {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of C.R'')) (w₁ w₂ : T ⟶
    (C.U : Scheme.{u}))
    (s : T ⟶ P1 C.y C.R')
    (hw₁ : w₁ ≫ C.U.ι ≫ pullback.fst C.y C.y = t ≫ C.a)
    (hw₂ : w₂ ≫ C.U.ι ≫ pullback.fst C.y C.y = w₁ ≫ C.U.ι ≫ pullback.snd C.y C.y)
    (hs₁ : s ≫ pullback.fst _ _ ≫ p1 C.y C.R' = w₁ ≫ C.m.1)
    (hs₂ : s ≫ pullback.snd _ _ ≫ p1 C.y C.R' = w₂ ≫ C.U.ι ≫ pullback.snd C.y C.y)
    (hs₃ : s ≫ pullback.fst _ _ ≫ y1 C.y C.R' = t ≫ bS C.R' C.R'') :
    Set.range s.base ⊆ (C.V : Set ↑(P1 C.y C.R')) := by
  have hb : (w₁ ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = t ≫ bS C.R' C.R'' ≫ bS C.R C.R' := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% hw₁, C.ha]
  have hv : (w₂ ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = t ≫ bS C.R' C.R'' ≫ bS C.R C.R' := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% hw₂]
    simpa only [Category.assoc] using hb
  let b : T ⟶ Y2 C.y C.R' C.R'' := pullback.lift _ _ hb
  let v : T ⟶ Y2 C.y C.R' C.R'' := pullback.lift _ _ hv
  have hbv₀ : b ≫ y2 C.y C.R' C.R'' = v ≫ y2 C.y C.R' C.R'' := by
    simp only [b, v, pullback.lift_snd]
  let bv : T ⟶ P2 C.y C.R' C.R'' := pullback.lift b v hbv₀
  have hbv : bv ≫ pi2 C.y C.R' C.R'' = w₂ ≫ C.U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pi2_fst, pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc, hw₂]
    · rw [Category.assoc, pi2_snd, pullback.lift_snd_assoc, pullback.lift_fst, Category.assoc]
  have hbsig : b ≫ sig (y2 C.y C.R' C.R'') C.a2 ≫ pi2 C.y C.R' C.R'' = w₁ ≫ C.U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pi2_fst, sig_fst_assoc, a2_p2,
        pullback.lift_snd_assoc, Category.assoc,
        hw₁]
    · rw [Category.assoc, Category.assoc, pi2_snd, sig_snd_assoc, pullback.lift_fst, Category.assoc]
  have hF : Set.range bv.base ⊆ (C.F : Set ↑(P2 C.y C.R' C.R'')) := by
    rintro _ ⟨p, rfl⟩
    refine ⟨?_, ?_⟩
    · change (bv ≫ pullback.fst _ _ ≫ sig (y2 C.y C.R' C.R'') C.a2 ≫ pi2 C.y C.R' C.R'') p ∈ C.U
      rw [show bv ≫ pullback.fst _ _ ≫ sig (y2 C.y C.R' C.R'') C.a2 ≫ pi2 C.y C.R' C.R'' = w₁ ≫
          C.U.ι by
        rw [pullback.lift_fst_assoc, hbsig], Scheme.Hom.comp_apply]
      exact (w₁ p).2
    · change (bv ≫ pi2 C.y C.R' C.R'') p ∈ C.U
      rw [hbv, Scheme.Hom.comp_apply]
      exact (w₂ p).2
  let φ := IsOpenImmersion.lift C.F.ι bv (by rwa [Scheme.Opens.range_ι])
  have hφ : φ ≫ C.F.ι = bv := IsOpenImmersion.lift_fac _ _ _
  have hφu : φ ≫ toUa (y2 C.y C.R' C.R'') C.U₂ C.a2 ≫ zeta (y2 C.y C.R' C.R'') C.U₂ C.a2 ≫
      piU C.y C.R' C.R'' C.U =
      w₁ := by
    rw [← cancel_mono C.U.ι, Category.assoc, Category.assoc, Category.assoc, piU_ι,
        zeta_ι_assoc, toUa_ι_assoc,
      reassoc_of% hφ, ← hbsig, pullback.lift_fst_assoc]
  have hja₁ : C.j ≫ pullback.fst _ _ ≫ p2 C.y C.R' C.R'' =
      toUa (y2 C.y C.R' C.R'') C.U₂ C.a2 ≫ zeta (y2 C.y C.R' C.R'') C.U₂ C.a2 ≫
          piU C.y C.R' C.R'' C.U ≫ C.m.1 := by
    rw [ja_fst_assoc, Phia, Category.assoc, m2_p2]
  have hja₂ : C.j ≫ pullback.fst _ _ ≫ y2 C.y C.R' C.R'' = C.F.ι ≫ pullback.fst _ _ ≫
      y2 C.y C.R' C.R'' := by
    rw [ja_fst_assoc, Phia_y, toUa_ι_assoc]
  have hja₃ : C.j ≫ pullback.snd _ _ = C.F.ι ≫ pullback.snd _ _ := ja_snd _ _ _ _
  have hs : s = φ ≫ C.f0 := by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;> simp only [Category.assoc]
    · rw [hs₁, f0_fst_assoc, r_p1, hja₁, reassoc_of% hφu]
    · rw [hs₃, f0_fst_assoc, r_y1, reassoc_of% hja₂, reassoc_of% hφ, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc]
    · rw [hs₂, f0_snd_assoc, r_p1, reassoc_of% hja₃, reassoc_of% hφ, pullback.lift_snd_assoc,
        pullback.lift_fst]
    · rw [← pullback.condition (f := y1 C.y C.R') (g :=
        y1 C.y C.R'), hs₃, f0_fst_assoc, r_y1, reassoc_of% hja₂,
        reassoc_of% hφ, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  rw [hs]
  rintro _ ⟨p, rfl⟩
  exact ⟨φ p, by rw [Scheme.Hom.comp_apply]⟩

end Ctx

end TranslationPiece

end
end AbelianVarieties.NOSProofs.EtaleTranslationPieces

namespace NeronModelInfra

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Topology
open AbelianVarieties.NOSProofs.EtaleTranslationPieces.TranslationPiece

theorem exists_opens_forall_range_subset_of_comp_translation_eq_of_etale
    {R : Type u} [CommRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) [Smooth y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 →
          p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y →
          q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (R' : Type u) [CommRing R'] [Algebra R R']
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R')) [IsSeparated y']
    (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
    (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R' R'']
    [Algebra.Etale R' R'']
    (a : Spec (CommRingCat.of R'') ⟶ Y)
    (ha : a ≫ y = (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map
        (CommRingCat.ofHom (algebraMap R R'))))
    (τ : pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map
        (CommRingCat.ofHom (algebraMap R R')))) ⟶
      pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))))
    (hτ₁ : τ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) =
      pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map
          (CommRingCat.ofHom (algebraMap R R')))))
    (hτ₂ : ∀ {T : Scheme.{u}}
        (x : T ⟶ pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map
            (CommRingCat.ofHom (algebraMap R R')))))
        (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom
            (algebraMap R R')))),
      w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom
          (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ a →
      w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y ((Spec.map (CommRingCat.ofHom
          (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) →
      v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
      v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.snd y
          ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom
          (algebraMap R R')))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
      x ≫ τ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = v ≫ ι.1) :
    ∃ (V : (pullback (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))).Opens)
      (G : SchemeHomOver (V.ι ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom
          (algebraMap R R'))))
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y'),
      (∀ {T : Scheme.{u}} (s : T ⟶ (V : Scheme.{u})) (w : T ⟶ (U : Scheme.{u}))
          (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
        s ≫ V.ι ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ U.ι ≫
              pullback.fst y y →
        s ≫ V.ι ≫ pullback.snd (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ U.ι ≫
              pullback.snd y y →
        v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
        v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
          s ≫ V.ι ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
            pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) →
        s ≫ G.1 = v ≫ ι.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'')) (w₁ w₂ : T ⟶ (U : Scheme.{u}))
          (s : T ⟶ pullback (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))),
        w₁ ≫ U.ι ≫ pullback.fst y y = t ≫ a →
        w₂ ≫ U.ι ≫ pullback.fst y y = w₁ ≫ U.ι ≫ pullback.snd y y →
        s ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w₁ ≫ m.1 →
        s ≫ pullback.snd (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w₂ ≫ U.ι ≫
              pullback.snd y y →
        s ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
          t ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
        Set.range s.base ⊆ (V : Set ↑(pullback (pullback.snd y (Spec.map (CommRingCat.ofHom
            (algebraMap R R'))))
          (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))))) := by
  let C : Ctx.{u} :=
    { R := R, Y := Y, y := y, U := U, m := m, hU₁ := hU₁, hΦ := hΦ, hassoc := hassoc, R' :=
        R', Y' := Y', y' := y',
      ι := ι, R'' := R'', a := a, ha := ha, τ := τ, hτ₁ := hτ₁, hτ₂ := hτ₂ }
  refine ⟨C.V, ⟨C.G, C.G_y'⟩, ?_, ?_⟩
  · intro T s w v h₁ h₂ h₃ h₄
    exact C.G_agree s w v h₁ h₂ h₃ h₄
  · intro T t w₁ w₂ s hw₁ hw₂ hs₁ hs₂ hs₃
    exact C.range_subset_V t w₁ w₂ s hw₁ hw₂ hs₁ hs₂ hs₃

end
end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.TranslationEnlargement

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace Enlargement

open AbelianVarieties.NOSProofs.GraphClosureRigidity.GraphClosure
  (dense_of_forall_dense_fibre)
open AbelianVarieties.NOSProofs.QuasiFiniteTranslationGluing.TranslationGluing
  (exists_lift_of_isClosedImmersion)
open AbelianVarieties.NOSProofs.GluingFibreDensity.TranslationCharts
  (jA jA_fst jA_snd jA_fst_assoc isPullback_jA)
open AbelianVarieties.NOSProofs.EtaleTranslationPieces.TranslationPiece (bS)

section General

theorem specMap_apply_ne_closedPoint {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsDomain B]
    [IsLocalRing B] [Ring.DimensionLEOne B] (hA : IsLocalRing.maximalIdeal A ≠ ⊥) (f : A →+* B)
    (hf : Function.Injective f) (p : ↥(Spec (CommRingCat.of B)))
        (hp : p ≠ IsLocalRing.closedPoint B) :
    (Spec.map (CommRingCat.ofHom f)).base p ≠ IsLocalRing.closedPoint A := by
  let p₀ : PrimeSpectrum B := p
  have hbot : p₀.asIdeal = ⊥ := by
    by_contra h
    exact hp (PrimeSpectrum.ext
      (IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal p₀.isPrime h)))
  intro h
  have h' : Ideal.comap f p₀.asIdeal = IsLocalRing.maximalIdeal A := by
    exact congrArg PrimeSpectrum.asIdeal h
  rw [hbot, Ideal.comap_bot_of_injective f hf] at h'
  exact hA h'.symm

theorem maximal_fst_of_maximal {X S Z : Scheme.{u}} (f : X ⟶ S) (g : Z ⟶ S) (p : ↑(pullback f g))
    (hp : ∀ p' : ↑(pullback f g), p' ⤳ p → (pullback.snd f g).base p' =
        (pullback.snd f g).base p → p' = p) :
    ∀ x' : X, x' ⤳ (pullback.fst f g).base p → f.base x' = f.base ((pullback.fst f g).base p) →
      x' = (pullback.fst f g).base p := by
  obtain ⟨z, hz⟩ : ∃ z, (pullback.snd f g).base p = z := ⟨_, rfl⟩
  obtain ⟨φ, sq, hφ⟩ : ∃ φ : (pullback.snd f g).fiber z ⟶ f.fiber (g.base z),
      IsPullback φ ((pullback.snd f g).fiberToSpecResidueField z) (f.fiberToSpecResidueField
          (g.base z))
        (Spec.map (g.residueFieldMap z)) ∧
      φ ≫ f.fiberι (g.base z) = (pullback.snd f g).fiberι z ≫ pullback.fst f g :=
    ⟨_, isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f g) z,
      pullback.lift_fst _ _ _⟩
  let e₂ := (pullback.snd f g).fiberι z
  let e₁ := f.fiberι (g.base z)
  obtain ⟨ζ, hζ⟩ : p ∈ Set.range e₂.base := by
    rw [Scheme.Hom.range_fiberι]; exact hz
  have : Flat (Spec.map (g.residueFieldMap z)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let : Algebra (S.residueField (g z)) (Z.residueField z) :=
      (g.residueFieldMap z).hom.toAlgebra
    exact Module.Flat.of_free
  have : Flat φ := by rw [← sq.isoPullback_hom_fst]; infer_instance
  have hφp : e₁.base (φ.base ζ) = (pullback.fst f g).base p := by
    rw [← Scheme.Hom.comp_apply]
    change (φ ≫ f.fiberι (g.base z)).base ζ = _
    rw [hφ, Scheme.Hom.comp_apply]
    exact congrArg _ hζ
  intro x' hx' hfx'
  obtain ⟨ξ', rfl⟩ : x' ∈ Set.range e₁.base := by
    rw [Scheme.Hom.range_fiberι]
    change f.base x' = g.base z
    rw [hfx', ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hz]
  have h1 : ξ' ⤳ φ.base ζ := by
    apply (e₁.isEmbedding.isInducing.specializes_iff).mp
    rw [hφp]
    exact hx'
  obtain ⟨ζ', hζ', hζ'ξ⟩ := Flat.generalizingMap φ h1
  have hζ'ζ : ζ' = ζ := by
    apply e₂.isEmbedding.injective
    rw [hζ]
    refine hp _ ?_ ?_
    · have := hζ'.map e₂.continuous
      rwa [hζ] at this
    · have : e₂.base ζ' ∈ (pullback.snd f g).base ⁻¹' {z} := by
        rw [← Scheme.Hom.range_fiberι]; exact ⟨ζ', rfl⟩
      rw [hz]; exact this
  rw [hζ'ζ] at hζ'ξ
  rw [← hζ'ξ, hφp]

end General

section StrictLaw

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of A))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

/-- A partial group law with fiberwise dense domains and translation graphs. -/
structure Strict : Prop where
  /-- The domain is dense on each first-projection fiber. -/
  hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y)))
  /-- The domain is dense on each second-projection fiber. -/
  hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y)))
  /-- The left translation graph is an open immersion. -/
  hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm))
  /-- The left graph is dense on first-projection fibers. -/
  hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base))
  /-- The left graph is dense on second-projection fibers. -/
  hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base))
  /-- The right translation graph is an open immersion. -/
  hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition])))
  /-- The right graph is dense on first-projection fibers. -/
  hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
  /-- The right graph is dense on second-projection fibers. -/
  hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
          ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
  /-- The partial multiplication is associative wherever both sides are defined. -/
  hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of A))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 →
          p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y →
          q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1

theorem dense_preimage_jA (a : Spec (CommRingCat.of A) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    (S : Set ↑(pullback y y))
    (hS : ∀ x : Y, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
      ↑(pullback y y)) ⁻¹' S)) :
    Dense ((jA y a ha).base ⁻¹' S) := by
  refine dense_of_forall_dense_fibre y.base _ fun x => ?_
  exact AbelianVarieties.NOSProofs.DensityBaseChange.FibreDensity.dense_fibre_of_isPullback
    (pullback.fst y y) y (jA y a ha) a (isPullback_jA y a ha) x S (hS (a x))

end StrictLaw

/-- The model, partial law, base changes and translation data. -/
structure Ctx : Type (u + 1) where
  /-- The initial base ring. -/
  R : Type u
  /-- The given CommRing R structure. -/
  [cR : CommRing R]
  /-- The given IsDomain R structure. -/
  [domR : IsDomain R]
  /-- The given IsDiscreteValuationRing R structure. -/
  [dvrR : IsDiscreteValuationRing R]
  /-- The initial model. -/
  Y : Scheme.{u}
  /-- The initial structure morphism. -/
  y : Y ⟶ Spec (CommRingCat.of R)
  /-- The given Smooth y structure. -/
  [sm : Smooth y]
  /-- The given IsSeparated y structure. -/
  [sep : IsSeparated y]
  /-- The given LocallyOfFiniteType y structure. -/
  [loft : LocallyOfFiniteType y]
  /-- The given QuasiCompact y structure. -/
  [qc : QuasiCompact y]
  /-- The initial partial-law domain. -/
  U : (pullback y y).Opens
  /-- The initial partial multiplication. -/
  m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y
  /-- The initial law has dense domains and open translation graphs. -/
  hS : Strict y U m
  /-- The domain contains every pair over the generic locus. -/
  hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U
  /-- The first extended base ring. -/
  R' : Type u
  /-- The given CommRing R' structure. -/
  [cR' : CommRing R']
  /-- The given IsDomain R' structure. -/
  [domR' : IsDomain R']
  /-- The given IsDiscreteValuationRing R' structure. -/
  [dvrR' : IsDiscreteValuationRing R']
  /-- The given Algebra R R' structure. -/
  [alg' : Algebra R R']
  /-- The given Module.FaithfullyFlat R R' structure. -/
  [ff' : Module.FaithfullyFlat R R']
  /-- The enlarged model. -/
  Y' : Scheme.{u}
  /-- The enlarged structure morphism. -/
  y' : Y' ⟶ Spec (CommRingCat.of R')
  /-- The given Smooth y' structure. -/
  [sm' : Smooth y']
  /-- The given IsSeparated y' structure. -/
  [sep' : IsSeparated y']
  /-- The given LocallyOfFiniteType y' structure. -/
  [loft' : LocallyOfFiniteType y']
  /-- The given QuasiCompact y' structure. -/
  [qc' : QuasiCompact y']
  /-- The comparison map to the enlarged model. -/
  ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y'
  /-- The given IsOpenImmersion ι.1 structure. -/
  [oi : IsOpenImmersion ι.1]
  /-- The comparison image contains the generic locus. -/
  hgen : ∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base
  /-- The comparison image contains fiberwise maximal points. -/
  hmax : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base
  /-- The enlarged partial-law domain. -/
  U' : (pullback y' y').Opens
  /-- The enlarged partial multiplication. -/
  m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'
  /-- The enlarged law has dense domains and open translation graphs. -/
  hS' : Strict y' U' m'
  /-- The enlarged law extends the original law. -/
  hext : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫
            pullback.fst y y ≫ y))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
      a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
      ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' =
          (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom
              (algebraMap R R'))) a).1 ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' =
          (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom
              (algebraMap R R'))) b).1 ≫ ι.1 ∧
        w'.1 ≫ m'.1 =
          (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom
              (algebraMap R R'))) c).1 ≫ ι.1
  /-- The second extended base ring. -/
  R'' : Type u
  /-- The given CommRing R'' structure. -/
  [cR'' : CommRing R'']
  /-- The given IsDomain R'' structure. -/
  [domR'' : IsDomain R'']
  /-- The given IsDiscreteValuationRing R'' structure. -/
  [dvrR'' : IsDiscreteValuationRing R'']
  /-- The given Algebra R' R'' structure. -/
  [alg'' : Algebra R' R'']
  /-- The given Module.FaithfullyFlat R' R'' structure. -/
  [ff'' : Module.FaithfullyFlat R' R'']
  /-- The given Algebra R R'' structure. -/
  [algR'' : Algebra R R'']
  /-- The given IsScalarTower R R' R'' structure. -/
  [tower : IsScalarTower R R' R'']
  /-- The translating section. -/
  a : Spec (CommRingCat.of R'') ⟶ Y
  /-- The translating section is over the prescribed base map. -/
  ha : a ≫ y = Spec.map (CommRingCat.ofHom (algebraMap R R''))

attribute [local instance] Ctx.cR Ctx.domR Ctx.dvrR Ctx.sm Ctx.sep Ctx.loft Ctx.qc Ctx.cR'
  Ctx.domR' Ctx.dvrR' Ctx.alg' Ctx.ff' Ctx.sm' Ctx.sep' Ctx.loft' Ctx.qc' Ctx.oi Ctx.cR''
  Ctx.domR'' Ctx.dvrR'' Ctx.alg'' Ctx.ff'' Ctx.algR'' Ctx.tower

namespace Ctx

variable (C : Ctx.{u})

/-- The first extension of the base spectrum. -/
abbrev s' : Spec (CommRingCat.of C.R') ⟶ Spec (CommRingCat.of C.R) := bS C.R C.R'

/-- The composite extension of the base spectrum. -/
abbrev s'' : Spec (CommRingCat.of C.R'') ⟶ Spec (CommRingCat.of C.R) := bS C.R C.R''

/-- The second extension of the base spectrum. -/
abbrev t : Spec (CommRingCat.of C.R'') ⟶ Spec (CommRingCat.of C.R') := bS C.R' C.R''

theorem t_s' : C.t ≫ C.s' = C.s'' := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

theorem t_ne (s : ↥(Spec (CommRingCat.of C.R''))) (hs : s ≠ IsLocalRing.closedPoint C.R'') :
    C.t.base s ≠ IsLocalRing.closedPoint C.R' :=
  specMap_apply_ne_closedPoint (IsDiscreteValuationRing.not_a_field C.R') _
    (FaithfulSMul.algebraMap_injective C.R' C.R'') s hs

theorem s'_ne (s : ↥(Spec (CommRingCat.of C.R'))) (hs : s ≠ IsLocalRing.closedPoint C.R') :
    C.s'.base s ≠ IsLocalRing.closedPoint C.R :=
  specMap_apply_ne_closedPoint (IsDiscreteValuationRing.not_a_field C.R) _
    (FaithfulSMul.algebraMap_injective C.R C.R') s hs

/-- The first base change of the model. -/
abbrev Y1 : Scheme.{u} := pullback C.y C.s'

/-- The iterated base change of the model. -/
abbrev Y2 : Scheme.{u} := pullback C.y C.s''

/-- The base change of the enlarged model. -/
abbrev Yp : Scheme.{u} := pullback C.y' C.t

/-- The structure morphism of the enlarged base change. -/
abbrev yp : C.Yp ⟶ Spec (CommRingCat.of C.R'') := pullback.snd C.y' C.t

/-- The projection from the enlarged base change. -/
abbrev π : C.Yp ⟶ C.Y' := pullback.fst C.y' C.t

/-- The transition map between base changes of the original model. -/
def k₁ : C.Y2 ⟶ C.Y1 :=
  pullback.lift (pullback.fst C.y C.s'') (pullback.snd C.y C.s'' ≫ C.t)
    (by rw [Category.assoc, C.t_s']; exact pullback.condition)

@[reassoc (attr := simp)]
theorem k₁_fst : C.k₁ ≫ pullback.fst C.y C.s' = pullback.fst C.y C.s'' := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem k₁_snd : C.k₁ ≫ pullback.snd C.y C.s' = pullback.snd C.y C.s'' ≫ C.t :=
    pullback.lift_snd _ _ _

theorem isPullback_k₁ : IsPullback C.k₁ (pullback.snd C.y C.s'') (pullback.snd C.y C.s') C.t := by
  refine IsPullback.of_right ?_ C.k₁_snd (IsPullback.of_hasPullback C.y C.s')
  rw [k₁_fst, t_s']
  exact IsPullback.of_hasPullback _ _

/-- The original model mapped into the enlarged base change. -/
def k : C.Y2 ⟶ C.Yp :=
  pullback.lift (C.k₁ ≫ C.ι.1) (pullback.snd C.y C.s'') (by rw [Category.assoc, C.ι.2, k₁_snd])

@[reassoc (attr := simp)]
theorem k_π : C.k ≫ C.π = C.k₁ ≫ C.ι.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem k_yp : C.k ≫ C.yp = pullback.snd C.y C.s'' := pullback.lift_snd _ _ _

theorem isPullback_k : IsPullback C.k C.k₁ C.π C.ι.1 := by
  refine IsPullback.of_right ?_ C.k_π (IsPullback.of_hasPullback C.y' C.t).flip
  rw [k_yp, C.ι.2]
  exact C.isPullback_k₁.flip

scoped instance isOpenImmersion_k : IsOpenImmersion C.k :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) C.isPullback_k.flip C.oi

theorem mem_range_k (z : ↥C.Yp)
    (hz : C.π.base z ∈ Set.range C.ι.1.base) : z ∈ Set.range C.k.base := by
  obtain ⟨w, hw⟩ : z ∈ Set.range (pullback.fst C.π C.ι.1).base := by
    rw [Scheme.Pullback.range_fst]; exact hz
  refine ⟨C.isPullback_k.isoPullback.inv.base w, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  exact hw

/-- The translating section on the base-changed original model. -/
def aa : Spec (CommRingCat.of C.R'') ⟶ C.Y2 :=
  pullback.lift C.a (𝟙 _) (by rw [C.ha, Category.id_comp])

@[reassoc (attr := simp)]
theorem aa_fst : C.aa ≫ pullback.fst C.y C.s'' = C.a := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem aa_snd : C.aa ≫ pullback.snd C.y C.s'' = 𝟙 _ := pullback.lift_snd _ _ _

/-- The translating section on the enlarged base change. -/
def ap : Spec (CommRingCat.of C.R'') ⟶ C.Yp := C.aa ≫ C.k

theorem ap_yp : C.ap ≫ C.yp = 𝟙 _ := by
  rw [ap, Category.assoc, k_yp, aa_snd]

/-- The structure morphism of the first base change. -/
abbrev y1 : C.Y1 ⟶ Spec (CommRingCat.of C.R') := pullback.snd C.y C.s'

/-- The first base-change map on pair schemes. -/
def pi1 : pullback C.y1 C.y1 ⟶ pullback C.y C.y :=
  pullback.map _ _ _ _ (pullback.fst C.y C.s') (pullback.fst C.y C.s') C.s'
    pullback.condition.symm pullback.condition.symm

/-- The comparison map on pair schemes. -/
def ιι : pullback C.y1 C.y1 ⟶ pullback C.y' C.y' :=
  pullback.map _ _ _ _ C.ι.1 C.ι.1 (𝟙 _)
      (by rw [Category.comp_id, C.ι.2]) (by rw [Category.comp_id, C.ι.2])

@[reassoc]
theorem ιι_fst : C.ιι ≫ pullback.fst C.y' C.y' = pullback.fst C.y1 C.y1 ≫ C.ι.1 :=
    pullback.lift_fst _ _ _

@[reassoc]
theorem ιι_snd : C.ιι ≫ pullback.snd C.y' C.y' = pullback.snd C.y1 C.y1 ≫ C.ι.1 :=
    pullback.lift_snd _ _ _

theorem mem_U'_of_ne (q : ↥(pullback C.y' C.y'))
    (hq : (pullback.fst C.y' C.y' ≫ C.y').base q ≠ IsLocalRing.closedPoint C.R') : q ∈ C.U' := by
  have h1 : (pullback.fst C.y' C.y').base q ∈ Set.range C.ι.1.base :=
    C.hgen _ (by rw [← Scheme.Hom.comp_apply]; exact hq)
  have h2 : (pullback.snd C.y' C.y').base q ∈ Set.range C.ι.1.base :=
    C.hgen _ (by rw [← Scheme.Hom.comp_apply, ← pullback.condition]; exact hq)
  obtain ⟨q₁, rfl⟩ : q ∈ Set.range C.ιι.base := by
    rw [ιι, Scheme.Pullback.range_map]; exact ⟨h1, h2⟩
  have e2 : C.ιι ≫ pullback.fst C.y' C.y' ≫ C.y' = pullback.fst C.y1 C.y1 ≫ C.y1 := by
    rw [ιι, pullback.lift_fst_assoc, Category.assoc, C.ι.2]
  let U₁ : (pullback C.y1 C.y1).Opens := C.pi1 ⁻¹ᵁ C.U
  have hq₁ : q₁ ∈ U₁ := by
    change C.pi1.base q₁ ∈ C.U
    apply C.hUK
    have e1 : C.pi1 ≫ pullback.fst C.y C.y ≫ C.y = (pullback.fst C.y1 C.y1 ≫ C.y1) ≫ C.s' := by
      rw [pi1, pullback.lift_fst_assoc, Category.assoc, pullback.condition, Category.assoc]
    rw [← Scheme.Hom.comp_apply, e1, Scheme.Hom.comp_apply]
    apply C.s'_ne
    rw [← e2, Scheme.Hom.comp_apply]
    exact hq
  let wU : (U₁ : Scheme.{u}) ⟶ C.U := C.pi1.resLE C.U U₁ le_rfl
  have hwU : wU ≫ C.U.ι = U₁.ι ≫ C.pi1 := Scheme.Hom.resLE_comp_ι _ _
  let t' : (U₁ : Scheme.{u}) ⟶ Spec (CommRingCat.of C.R') := U₁.ι ≫ pullback.fst C.y1 C.y1 ≫ C.y1
  have ht' : t' = U₁.ι ≫ pullback.snd C.y1 C.y1 ≫ C.y1 := by simp only [t', pullback.condition]
  have hA : wU ≫ C.U.ι ≫ pullback.fst C.y C.y = (U₁.ι ≫ pullback.fst C.y1 C.y1) ≫
      pullback.fst C.y C.s' := by
    rw [reassoc_of% hwU, pi1, pullback.lift_fst, Category.assoc]
  have hB : wU ≫ C.U.ι ≫ pullback.snd C.y C.y = (U₁.ι ≫ pullback.snd C.y1 C.y1) ≫
      pullback.fst C.y C.s' := by
    rw [reassoc_of% hwU, pi1, pullback.lift_snd, Category.assoc]
  have ha_ : (wU ≫ C.U.ι ≫ pullback.fst C.y C.y) ≫ C.y = t' ≫ C.s' := by
    rw [hA, Category.assoc, pullback.condition]; simp only [t', Category.assoc]
  have hb_ : (wU ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = t' ≫ C.s' := by
    rw [hB, Category.assoc, pullback.condition, ht']; simp only [Category.assoc]
  have hc_ : (wU ≫ C.m.1) ≫ C.y = t' ≫ C.s' := by
    rw [Category.assoc, C.m.2]; simpa only [Category.assoc] using ha_
  obtain ⟨w', hw'₁, hw'₂, -⟩ :=
    C.hext t' ⟨wU, by simpa only [Category.assoc] using ha_⟩ ⟨_, ha_⟩ ⟨_, hb_⟩ ⟨_, hc_⟩ rfl rfl rfl
  rw [RelativeGroupLaw.baseChangePointOfBase_coe] at hw'₁ hw'₂
  have e₁ : pullback.lift (wU ≫ C.U.ι ≫ pullback.fst C.y C.y) t' ha_ = U₁.ι ≫
      pullback.fst C.y1 C.y1 := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hA]
    · rw [pullback.lift_snd]; simp only [t', Category.assoc]
  have e₂ : pullback.lift (wU ≫ C.U.ι ≫ pullback.snd C.y C.y) t' hb_ = U₁.ι ≫
      pullback.snd C.y1 C.y1 := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hB]
    · rw [pullback.lift_snd, ht']; simp only [Category.assoc]
  have key : w'.1 ≫ C.U'.ι = U₁.ι ≫ C.ιι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hw'₁, e₁, Category.assoc, Category.assoc, ιι_fst]
    · rw [Category.assoc, hw'₂, e₂, Category.assoc, Category.assoc, ιι_snd]
  let qU : (U₁ : Scheme.{u}) := ⟨q₁, hq₁⟩
  have hmem : (U₁.ι ≫ C.ιι) qU ∈ C.U' := by
    rw [← key, Scheme.Hom.comp_apply]
    exact (w'.1 qU).2
  exact hmem

/-- The base-change map on pairs of enlarged points. -/
def cc : pullback C.yp C.yp ⟶ pullback C.y' C.y' :=
  pullback.map _ _ _ _ C.π C.π C.t pullback.condition.symm pullback.condition.symm

theorem cc_fst : C.cc ≫ pullback.fst C.y' C.y' = pullback.fst C.yp C.yp ≫ C.π :=
    pullback.lift_fst _ _ _

theorem cc_snd : C.cc ≫ pullback.snd C.y' C.y' = pullback.snd C.yp C.yp ≫ C.π :=
    pullback.lift_snd _ _ _

/-- The domain of the enlarged partial law after base change. -/
abbrev Up : (pullback C.yp C.yp).Opens := C.cc ⁻¹ᵁ C.U'

theorem mem_Up_of_ne (q : ↥(pullback C.yp C.yp))
    (hq : (pullback.fst C.yp C.yp ≫ C.yp).base q ≠ IsLocalRing.closedPoint C.R'') : q ∈ C.Up := by
  change C.cc.base q ∈ C.U'
  apply C.mem_U'_of_ne
  have e : C.cc ≫ pullback.fst C.y' C.y' ≫ C.y' = (pullback.fst C.yp C.yp ≫ C.yp) ≫ C.t := by
    rw [cc, pullback.lift_fst_assoc, Category.assoc, pullback.condition, Category.assoc]
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact C.t_ne _ hq

/-- The pair map with the translating section as first coordinate. -/
abbrev jAp : C.Yp ⟶ pullback C.yp C.yp := jA C.yp C.ap C.ap_yp

/-- The open domain of translation on the enlarged base change. -/
abbrev W₀ : C.Yp.Opens := C.jAp ⁻¹ᵁ C.Up

theorem mem_W₀_of_ne (z : ↥C.Yp) (hz : C.yp.base z ≠ IsLocalRing.closedPoint C.R'') : z ∈ C.W₀ := by
  change C.jAp.base z ∈ C.Up
  apply C.mem_Up_of_ne
  have e : C.jAp ≫ pullback.fst C.yp C.yp ≫ C.yp = C.yp := by
    rw [jA_fst_assoc, ap_yp, Category.comp_id]
  rw [← Scheme.Hom.comp_apply, e]
  exact hz

/-- The section pair restricted to the partial-law domain. -/
abbrev jW : (C.W₀ : Scheme.{u}) ⟶ C.Up := C.jAp.resLE C.Up C.W₀ le_rfl

theorem jW_ι : C.jW ≫ C.Up.ι = C.W₀.ι ≫ C.jAp := Scheme.Hom.resLE_comp_ι _ _

@[reassoc]
theorem jW_fst : C.jW ≫ C.Up.ι ≫ pullback.fst C.yp C.yp = (C.W₀.ι ≫ C.yp) ≫ C.ap := by
  rw [reassoc_of% C.jW_ι, jA_fst, Category.assoc]

@[reassoc]
theorem jW_snd : C.jW ≫ C.Up.ι ≫ pullback.snd C.yp C.yp = C.W₀.ι := by
  rw [reassoc_of% C.jW_ι, jA_snd, Category.comp_id]

end Ctx

/-- A separated gluing of the enlarged model with its translate. -/
structure Glued (C : Ctx.{u}) : Type (u + 1) where
  /-- The base-changed partial multiplication. -/
  mp : SchemeHomOver (C.Up.ι ≫ pullback.fst C.yp C.yp ≫ C.yp) C.yp
  /-- The base-changed multiplication respects projection. -/
  hmp : mp.1 ≫ C.π = C.cc.resLE C.U' C.Up le_rfl ≫ C.m'.1
  /-- The base-changed law has dense domains and open translation graphs. -/
  hSp : Strict C.yp C.Up mp
  /-- The glued model. -/
  Y'' : Scheme.{u}
  /-- The glued structure morphism. -/
  y'' : Y'' ⟶ Spec (CommRingCat.of C.R'')
  /-- The given Smooth y'' structure. -/
  [sm : Smooth y'']
  /-- The given IsSeparated y'' structure. -/
  [sep : IsSeparated y'']
  /-- The given LocallyOfFiniteType y'' structure. -/
  [loft : LocallyOfFiniteType y'']
  /-- The given QuasiCompact y'' structure. -/
  [qc : QuasiCompact y'']
  /-- The original chart in the gluing. -/
  jj : SchemeHomOver C.yp y''
  /-- The translation morphism. -/
  τ : SchemeHomOver C.yp y''
  /-- The given IsOpenImmersion jj.1 structure. -/
  [oij : IsOpenImmersion jj.1]
  /-- The given IsOpenImmersion τ.1 structure. -/
  [oiτ : IsOpenImmersion τ.1]
  /-- The two charts cover the glued model. -/
  cover : ∀ p : ↥Y'', p ∈ Set.range jj.1.base ∨ p ∈ Set.range τ.1.base
  /-- The original chart contains fiberwise maximal points. -/
  hjjd : ∀ p : ↥Y'', (∀ p' : ↥Y'', p' ⤳ p → y''.base p' = y''.base p → p' = p) →
      p ∈ Set.range jj.1.base
  /-- The translated chart agrees with the partial multiplication. -/
  tr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of C.R'')) (x : SchemeHomOver t C.yp)
      (w : SchemeHomOver t (C.Up.ι ≫ pullback.fst C.yp C.yp ≫ C.yp)),
    w.1 ≫ C.Up.ι ≫ pullback.fst C.yp C.yp = t ≫ C.ap → w.1 ≫ C.Up.ι ≫ pullback.snd C.yp C.yp = x.1 →
    x.1 ≫ τ.1 = w.1 ≫ mp.1 ≫ jj.1
  /-- The glued partial-law domain. -/
  U'' : (pullback y'' y'').Opens
  /-- The glued partial multiplication. -/
  m'' : SchemeHomOver (U''.ι ≫ pullback.fst y'' y'' ≫ y'') y''
  /-- The glued law has dense domains and open translation graphs. -/
  hS'' : Strict y'' U'' m''
  /-- The glued law extends the base-changed law. -/
  hext'' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of C.R''))
      (w : SchemeHomOver t (C.Up.ι ≫ pullback.fst C.yp C.yp ≫ C.yp)),
    ∃ w' : SchemeHomOver t (U''.ι ≫ pullback.fst y'' y'' ≫ y''),
      w'.1 ≫ U''.ι ≫ pullback.fst y'' y'' = w.1 ≫ C.Up.ι ≫ pullback.fst C.yp C.yp ≫ jj.1 ∧
      w'.1 ≫ U''.ι ≫ pullback.snd y'' y'' = w.1 ≫ C.Up.ι ≫ pullback.snd C.yp C.yp ≫ jj.1 ∧
      w'.1 ≫ m''.1 = w.1 ≫ mp.1 ≫ jj.1

attribute [local instance] Glued.sm Glued.sep Glued.loft Glued.qc Glued.oij Glued.oiτ

namespace Ctx

variable (C : Ctx.{u})

theorem nonempty_glued : Nonempty (Glued C) := by
  obtain ⟨mp, hmp, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre
      C.t C.y' C.U' C.m' C.hS'.hU₁ C.hS'.hU₂ C.hS'.hΦ C.hS'.hΦ₁ C.hS'.hΦ₂
      C.hS'.hΨ C.hS'.hΨ₁ C.hS'.hΨ₂
      C.hS'.hassoc C.yp C.π (IsPullback.of_hasPullback C.y' C.t) C.cc C.cc_fst C.cc_snd
  obtain ⟨G, γ, hγ, -, hΓ, hq12, hq13, hq23, -⟩ :=
    exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
      C.yp C.Up mp h1 h2 h3 h4 h5 h6 h7 h8 h9
  have : IsClosedImmersion γ := hγ
  have := hq12
  have := hq13
  have := hq23
  have hsub : Set.range (pullback.lift (f := pullback.fst C.yp C.yp ≫ C.yp) (g :=
      C.yp) C.Up.ι mp.1 mp.2.symm).base ⊆
      Set.range γ.base := hΓ ▸ subset_closure
  obtain ⟨Y'', y'', jj, τ, hsm, hsep, hloft, hqc, hjj, hτ, hcov, hjjd, -, hpb, htr⟩ :=
    exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section
      C.yp C.Up mp h1 h4 γ hsub C.ap C.ap_yp
  have := hsm
  have := hsep
  have := hloft
  have := hqc
  have := hjj
  have := hτ
  obtain ⟨U'', m'', g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, gext⟩ :=
    exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section
      C.yp C.Up mp h1 h2 h3 h4 h5 h6 h7 h8 h9 γ hΓ C.ap C.ap_yp y'' jj τ hcov hpb
  exact ⟨⟨mp, hmp, ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun t u v p q => h9 t u v p q⟩, Y'', y'',
      jj, τ, hcov, hjjd,
    fun t x w => htr t x w, U'', m'', ⟨g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈,
        fun t u v p q => g₉ t u v p q⟩,
    fun t w => gext t w⟩⟩

end Ctx

namespace Ctx

variable (C : Ctx.{u})

theorem dense_W₀ (G : Glued C) : Dense (C.W₀ : Set ↥C.Yp) :=
  dense_preimage_jA C.yp C.ap C.ap_yp _ G.hSp.hU₁

theorem tr_W₀ (G : Glued C) : C.W₀.ι ≫ G.τ.1 = C.jW ≫ G.mp.1 ≫ G.jj.1 :=
  G.tr (C.W₀.ι ≫ C.yp) ⟨C.W₀.ι, rfl⟩
    ⟨C.jW, by rw [reassoc_of% C.jW_ι, jA_fst_assoc, ap_yp, Category.comp_id]⟩
    C.jW_fst C.jW_snd

theorem gen₂ (G : Glued C) (p : ↥G.Y'') (hp : G.y''.base p ≠ IsLocalRing.closedPoint C.R'') :
    p ∈ Set.range (C.k ≫ G.jj.1).base := by
  obtain ⟨z, rfl⟩ : p ∈ Set.range G.jj.1.base := by
    rcases G.cover p with h | ⟨x, rfl⟩
    · exact h
    · have hx : x ∈ C.W₀ := C.mem_W₀_of_ne x (by
        have e : (G.τ.1 ≫ G.y'').base x = C.yp.base x := by rw [G.τ.2]
        rw [Scheme.Hom.comp_apply] at e
        rw [← e]; exact hp)
      let xW : (C.W₀ : Scheme.{u}) := ⟨x, hx⟩
      have h := congrArg (fun f : (C.W₀ : Scheme.{u}) ⟶ G.Y'' => f xW) (C.tr_W₀ G)
      exact ⟨(C.jW ≫ G.mp.1) xW, h.symm⟩
  have hz : C.yp.base z ≠ IsLocalRing.closedPoint C.R'' := by
    have e : (G.jj.1 ≫ G.y'').base z = C.yp.base z := by rw [G.jj.2]
    rw [Scheme.Hom.comp_apply] at e
    rw [← e]; exact hp
  have hπz : C.y'.base (C.π.base z) ≠ IsLocalRing.closedPoint C.R' := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact C.t_ne _ hz
  obtain ⟨w, rfl⟩ := C.mem_range_k z (C.hgen _ hπz)
  exact ⟨w, by rw [Scheme.Hom.comp_apply]⟩

theorem max₂ (G : Glued C) (p : ↥G.Y'') (hp : ∀ p' : ↥G.Y'', p' ⤳ p →
    G.y''.base p' = G.y''.base p → p' = p) :
    p ∈ Set.range (C.k ≫ G.jj.1).base := by
  obtain ⟨z, rfl⟩ := G.hjjd p hp
  have hz : ∀ z' : ↥C.Yp, z' ⤳ z → C.yp.base z' = C.yp.base z → z' = z := by
    intro z' h1 h2
    apply G.jj.1.isOpenEmbedding.injective
    apply hp _ (h1.map G.jj.1.continuous)
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, G.jj.2]
    exact h2
  obtain ⟨w, rfl⟩ := C.mem_range_k z (C.hmax _ (maximal_fst_of_maximal C.y' C.t z hz))
  exact ⟨w, by rw [Scheme.Hom.comp_apply]⟩

theorem hext₂ (G : Glued C) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of C.R''))
    (w : SchemeHomOver (t' ≫ C.s'') (C.U.ι ≫ pullback.fst C.y C.y ≫ C.y))
    (a b c : SchemeHomOver (t' ≫ C.s'') C.y)
    (ha : a.1 = w.1 ≫ C.U.ι ≫ pullback.fst C.y C.y) (hb : b.1 = w.1 ≫ C.U.ι ≫ pullback.snd C.y C.y)
    (hc : c.1 = w.1 ≫ C.m.1) :
    ∃ w' : SchemeHomOver t' (G.U''.ι ≫ pullback.fst G.y'' G.y'' ≫ G.y''),
      w'.1 ≫ G.U''.ι ≫ pullback.fst G.y'' G.y'' = pullback.lift a.1 t' a.2 ≫ C.k ≫ G.jj.1 ∧
      w'.1 ≫ G.U''.ι ≫ pullback.snd G.y'' G.y'' = pullback.lift b.1 t' b.2 ≫ C.k ≫ G.jj.1 ∧
      w'.1 ≫ G.m''.1 = pullback.lift c.1 t' c.2 ≫ C.k ≫ G.jj.1 := by
  have hT : (t' ≫ C.t) ≫ C.s' = t' ≫ C.s'' := by rw [Category.assoc, C.t_s']
  obtain ⟨w', hw'₁, hw'₂, hw'₃⟩ := C.hext (t' ≫ C.t) ⟨w.1,
      by rw [hT]; exact w.2⟩ ⟨a.1, by rw [hT]; exact a.2⟩
    ⟨b.1, by rw [hT]; exact b.2⟩ ⟨c.1, by rw [hT]; exact c.2⟩ ha hb hc
  simp only [RelativeGroupLaw.baseChangePointOfBase_coe] at hw'₁ hw'₂ hw'₃
  have hlift : ∀ (x : SchemeHomOver (t' ≫ C.s'') C.y) (h : x.1 ≫ C.y = (t' ≫ C.t) ≫ C.s'),
      pullback.lift x.1 t' x.2 ≫ C.k ≫ C.π = pullback.lift x.1 (t' ≫ C.t) h ≫ C.ι.1 := by
    intro x h
    rw [k_π, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, k₁_fst, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, k₁_snd, pullback.lift_snd_assoc, pullback.lift_snd]
  let wp : T ⟶ pullback C.yp C.yp :=
    pullback.lift (pullback.lift a.1 t' a.2 ≫ C.k) (pullback.lift b.1 t' b.2 ≫ C.k)
      (by simp only [Category.assoc, k_yp, pullback.lift_snd])
  have hwp : wp ≫ C.cc = w'.1 ≫ C.U'.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, cc_fst, pullback.lift_fst_assoc, Category.assoc, Category.assoc, hw'₁]
      exact hlift a _
    · rw [Category.assoc, cc_snd, pullback.lift_snd_assoc, Category.assoc, Category.assoc, hw'₂]
      exact hlift b _
  have hrange : Set.range wp.base ⊆ Set.range C.Up.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨θ, rfl⟩
    change (wp ≫ C.cc).base θ ∈ C.U'
    rw [hwp, Scheme.Hom.comp_apply]
    exact (w'.1.base θ).2
  let wU : T ⟶ C.Up := IsOpenImmersion.lift C.Up.ι wp hrange
  have hwU : wU ≫ C.Up.ι = wp := IsOpenImmersion.lift_fac _ _ _
  have hres : wU ≫ C.cc.resLE C.U' C.Up le_rfl = w'.1 := by
    rw [← cancel_mono C.U'.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, reassoc_of% hwU, hwp]
  have hm : wU ≫ G.mp.1 = pullback.lift c.1 t' c.2 ≫ C.k := by
    apply pullback.hom_ext
    · rw [Category.assoc, G.hmp, reassoc_of% hres, hw'₃]
      exact ((Category.assoc _ _ _).trans (hlift c _)).symm
    · rw [Category.assoc, G.mp.2, reassoc_of% hwU, pullback.lift_fst_assoc, Category.assoc, k_yp,
        pullback.lift_snd, Category.assoc, k_yp, pullback.lift_snd]
  obtain ⟨w'', h₁, h₂, h₃⟩ := G.hext'' t' ⟨wU, by
    rw [reassoc_of% hwU, pullback.lift_fst_assoc, Category.assoc, k_yp, pullback.lift_snd]⟩
  refine ⟨w'', ?_, ?_, ?_⟩
  · rw [h₁, reassoc_of% hwU, pullback.lift_fst_assoc, Category.assoc]
  · rw [h₂, reassoc_of% hwU, pullback.lift_snd_assoc, Category.assoc]
  · rw [h₃, reassoc_of% hm]

theorem dom (G : Glued C) {T : Scheme.{u}} (x : T ⟶ C.Y2) (x₁ : T ⟶ C.Y1) (x₂ : T ⟶ C.Yp)
    (h₁ : x₁ ≫ pullback.fst C.y C.s' = x ≫ pullback.fst C.y C.s'')
    (h₂ : x₁ ≫ pullback.snd C.y C.s' = x ≫ pullback.snd C.y C.s'' ≫ C.t)
    (h₃ : x₂ ≫ C.π = x₁ ≫ C.ι.1) (h₄ : x₂ ≫ C.yp = x ≫ pullback.snd C.y C.s'') :
    x₂ ≫ G.jj.1 = x ≫ C.k ≫ G.jj.1 := by
  rw [← Category.assoc]
  congr 1
  have hx₁ : x ≫ C.k₁ = x₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, k₁_fst, h₁]
    · rw [Category.assoc, k₁_snd, h₂]
  apply pullback.hom_ext
  · rw [h₃, Category.assoc, k_π, ← Category.assoc, hx₁]
  · rw [h₄, Category.assoc, k_yp]

theorem progress (G : Glued C) :
    ∃ (D : (pullback G.y'' G.y'').Opens) (hle : G.U'' ≤ D)
      (M : SchemeHomOver (D.ι ≫ pullback.fst G.y'' G.y'' ≫ G.y'') G.y''),
      (pullback G.y'' G.y'').homOfLE hle ≫ M.1 = G.m''.1 ∧
      ∀ (a₂ : Spec (CommRingCat.of C.R'') ⟶ C.Y2),
        a₂ ≫ pullback.fst C.y C.s'' = C.a → a₂ ≫ pullback.snd C.y C.s'' = 𝟙 _ →
        ∀ {T : Scheme.{u}} (b : T ⟶ C.Y2) (q : T ⟶ pullback G.y'' G.y''),
          q ≫ pullback.fst G.y'' G.y'' = b ≫ pullback.snd C.y C.s'' ≫ a₂ ≫ C.k ≫ G.jj.1 →
          q ≫ pullback.snd G.y'' G.y'' = b ≫ C.k ≫ G.jj.1 →
          Set.range q.base ⊆ (D : Set ↥(pullback G.y'' G.y'')) := by
  obtain ⟨G₂, γ₂, hγ₂, -, hΓ₂, hq₁₂, -, -, -⟩ :=
    exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
      G.y'' G.U'' G.m'' G.hS''.hU₁ G.hS''.hU₂ G.hS''.hΦ G.hS''.hΦ₁ G.hS''.hΦ₂
      G.hS''.hΨ G.hS''.hΨ₁ G.hS''.hΨ₂
      G.hS''.hassoc
  have : IsClosedImmersion γ₂ := hγ₂
  let q12 : G₂ ⟶ pullback G.y'' G.y'' := γ₂ ≫ pullback.fst (pullback.fst G.y'' G.y'' ≫ G.y'') G.y''
  have : IsOpenImmersion q12 := hq₁₂
  let grm : (G.U'' : Scheme.{u}) ⟶ pullback (pullback.fst G.y'' G.y'' ≫ G.y'') G.y'' :=
    pullback.lift (f := pullback.fst G.y'' G.y'' ≫ G.y'') (g := G.y'') G.U''.ι G.m''.1 G.m''.2.symm
  have hsub : Set.range grm.base ⊆ Set.range γ₂.base := hΓ₂ ▸ subset_closure
  let D : (pullback G.y'' G.y'').Opens := q12.opensRange
  have hDr : Set.range D.ι.base ⊆ Set.range q12.base := by
    rw [Scheme.Opens.range_ι]; exact fun x hx => hx
  let l : (D : Scheme.{u}) ⟶ G₂ := IsOpenImmersion.lift q12 D.ι hDr
  have hl : l ≫ γ₂ ≫ pullback.fst _ _ = D.ι := IsOpenImmersion.lift_fac _ _ _
  let M₀ : (D : Scheme.{u}) ⟶ G.Y'' := l ≫ γ₂ ≫ pullback.snd _ _
  have hM₀ : M₀ ≫ G.y'' = D.ι ≫ pullback.fst G.y'' G.y'' ≫ G.y'' := by
    simp only [M₀, Category.assoc]
    rw [← pullback.condition (f := pullback.fst G.y'' G.y'' ≫ G.y'') (g := G.y''), reassoc_of% hl]
  have hle : G.U'' ≤ D := by
    intro u hu
    let uG : (G.U'' : Scheme.{u}) := ⟨u, hu⟩
    obtain ⟨g, hg⟩ := hsub ⟨uG, rfl⟩
    refine ⟨g, ?_⟩
    change (γ₂ ≫ pullback.fst _ _).base g = u
    rw [Scheme.Hom.comp_apply, hg, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    rfl
  have : IsReduced (G.U'' : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (G.U''.ι ≫ pullback.fst G.y'' G.y'' ≫ G.y'')
  obtain ⟨g₀, hg₀⟩ := exists_lift_of_isClosedImmersion grm γ₂ hsub
  have hM : (pullback G.y'' G.y'').homOfLE hle ≫ M₀ = G.m''.1 := by
    have h1 : (pullback G.y'' G.y'').homOfLE hle ≫ l = g₀ := by
      rw [← cancel_mono q12, Category.assoc]
      change _ ≫ l ≫ γ₂ ≫ pullback.fst _ _ = g₀ ≫ γ₂ ≫ pullback.fst _ _
      rw [hl, Scheme.homOfLE_ι, reassoc_of% hg₀, pullback.lift_fst]
    simp only [M₀]
    rw [reassoc_of% h1, reassoc_of% hg₀, pullback.lift_snd]
  refine ⟨D, hle, ⟨M₀, hM₀⟩, hM, ?_⟩
  intro a₂ ha₁ ha₂ T b q hq₁ hq₂
  have haa : a₂ = C.aa := by
    apply pullback.hom_ext
    · rw [ha₁, aa_fst]
    · rw [ha₂, aa_snd]
  subst haa
  let σ₁₂ : C.Yp ⟶ pullback G.y'' G.y'' :=
    pullback.lift (C.yp ≫ C.ap ≫ G.jj.1) G.jj.1
      (by rw [Category.assoc, Category.assoc, G.jj.2, ap_yp, Category.comp_id])
  let σ : C.Yp ⟶ pullback (pullback.fst G.y'' G.y'' ≫ G.y'') G.y'' :=
    pullback.lift σ₁₂ G.τ.1 (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, G.jj.2,
      ap_yp, Category.comp_id, G.τ.2])
  have hW : (C.W₀ : Set ↥C.Yp) ⊆ σ.base ⁻¹' Set.range γ₂.base := by
    intro v hv
    obtain ⟨w'', h₁, h₂, h₃⟩ := G.hext'' (C.W₀.ι ≫ C.yp)
      ⟨C.jW, by rw [reassoc_of% C.jW_ι, jA_fst_assoc, ap_yp, Category.comp_id]⟩
    have hgr : w''.1 ≫ grm = C.W₀.ι ≫ σ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst]
        apply pullback.hom_ext
        · rw [Category.assoc, h₁, Category.assoc, pullback.lift_fst]
          exact C.jW_fst_assoc _
        · rw [Category.assoc, h₂, Category.assoc, pullback.lift_snd]
          exact C.jW_snd_assoc _
      · rw [Category.assoc, pullback.lift_snd, h₃, Category.assoc, pullback.lift_snd, tr_W₀]
    let vW : (C.W₀ : Scheme.{u}) := ⟨v, hv⟩
    have e : σ v = (w''.1 ≫ grm) vW := by rw [hgr]; rfl
    rw [Set.mem_preimage, e, Scheme.Hom.comp_apply]
    exact hsub ⟨_, rfl⟩
  have hall : σ.base ⁻¹' Set.range γ₂.base = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← (C.dense_W₀ G).closure_eq]
    exact closure_minimal hW ((γ₂.isClosedEmbedding.isClosed_range).preimage σ.continuous)
  have hqσ : q = (b ≫ C.k) ≫ σ₁₂ := by
    apply pullback.hom_ext
    · rw [hq₁, Category.assoc, pullback.lift_fst, Category.assoc, k_yp_assoc, ap, Category.assoc]
    · rw [hq₂, Category.assoc, pullback.lift_snd, Category.assoc]
  rintro _ ⟨θ, rfl⟩
  obtain ⟨g, hg⟩ : σ.base ((b ≫ C.k).base θ) ∈ Set.range γ₂.base := by
    rw [← Set.mem_preimage, hall]; trivial
  refine ⟨g, ?_⟩
  change (γ₂ ≫ pullback.fst _ _).base g = q.base θ
  rw [Scheme.Hom.comp_apply, hg, ← Scheme.Hom.comp_apply, pullback.lift_fst, hqσ]
  simp only [Scheme.Hom.comp_apply]

end Ctx

end Enlargement

end
end AbelianVarieties.NOSProofs.TranslationEnlargement

namespace NeronModelInfra

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Topology
open AbelianVarieties.NOSProofs.TranslationEnlargement.Enlargement

theorem
 exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre
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
    (hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R']
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R'))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
        [IsOpenImmersion ι.1]
    (hgen : ∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base)
    (hmax : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) →
        p ∈ Set.range ι.1.base)
    (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y')
    (hU'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
          ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y'))))
    (hU'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
          ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y'))))
    (hΦ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)))
    (hΦ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
          ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base)))
    (hΦ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
          ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base)))
    (hΨ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
          ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
          ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
        (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
      u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
      p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
          p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
      q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' →
          q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
      p.1 ≫ m'.1 = q.1 ≫ m'.1)
    (hext : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫
            pullback.fst y y ≫ y))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
      a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
      ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map
            (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map
            (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
        w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom
            (algebraMap R R'))) c).1 ≫ ι.1)
    (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R' R'']
    [Module.FaithfullyFlat R' R''] [Algebra R R''] [IsScalarTower R R' R'']
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = Spec.map (CommRingCat.ofHom
        (algebraMap R R''))) :
    ∃ (Y'' : Scheme.{u}) (y'' : Y'' ⟶ Spec (CommRingCat.of R''))
      (ι₂ : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) y'')
      (U'' : (pullback y'' y'').Opens) (m'' : SchemeHomOver (U''.ι ≫ pullback.fst y'' y'' ≫
          y'') y''),
      Smooth y'' ∧ IsSeparated y'' ∧ LocallyOfFiniteType y'' ∧ QuasiCompact y'' ∧
      IsOpenImmersion ι₂.1 ∧
      (∀ p : Y'', y''.base p ≠ IsLocalRing.closedPoint R'' → p ∈ Set.range ι₂.1.base) ∧
      (∀ p : Y'', (∀ p' : Y'', p' ⤳ p → y''.base p' = y''.base p → p' = p) →
          p ∈ Set.range ι₂.1.base) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.fst y'' y'').base q =
          x} → ↑(pullback y'' y'')) ⁻¹'
          (U'' : Set ↑(pullback y'' y'')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.snd y'' y'').base q =
          x} → ↑(pullback y'' y'')) ⁻¹'
          (U'' : Set ↑(pullback y'' y'')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y'') (g := y'') (U''.ι ≫ pullback.fst y'' y'') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.fst y'' y'').base q =
          x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') (U''.ι ≫ pullback.fst y'' y'') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.snd y'' y'').base q =
          x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') (U''.ι ≫ pullback.fst y'' y'') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y'') (g := y'') m''.1 (U''.ι ≫ pullback.snd y'' y'')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.fst y'' y'').base q =
          x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') m''.1 (U''.ι ≫ pullback.snd y'' y'')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.snd y'' y'').base q =
          x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') m''.1 (U''.ι ≫ pullback.snd y'' y'')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R''))
          (u v p q : SchemeHomOver t (U''.ι ≫ pullback.fst y'' y'' ≫ y'')),
        u.1 ≫ U''.ι ≫ pullback.snd y'' y'' = v.1 ≫ U''.ι ≫ pullback.fst y'' y'' →
        p.1 ≫ U''.ι ≫ pullback.fst y'' y'' = u.1 ≫ m''.1 →
        p.1 ≫ U''.ι ≫ pullback.snd y'' y'' = v.1 ≫ U''.ι ≫ pullback.snd y'' y'' →
        q.1 ≫ U''.ι ≫ pullback.fst y'' y'' = u.1 ≫ U''.ι ≫ pullback.fst y'' y'' →
        q.1 ≫ U''.ι ≫ pullback.snd y'' y'' = v.1 ≫ m''.1 →
        p.1 ≫ m''.1 = q.1 ≫ m''.1) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R''))
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) (U.ι ≫
              pullback.fst y y ≫ y))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) y),
        a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
        ∃ w' : SchemeHomOver t' (U''.ι ≫ pullback.fst y'' y'' ≫ y''),
          w'.1 ≫ U''.ι ≫ pullback.fst y'' y'' = (RelativeGroupLaw.baseChangePointOfBase
              (Spec.map (CommRingCat.ofHom (algebraMap R R''))) a).1 ≫ ι₂.1 ∧
          w'.1 ≫ U''.ι ≫ pullback.snd y'' y'' = (RelativeGroupLaw.baseChangePointOfBase
              (Spec.map (CommRingCat.ofHom (algebraMap R R''))) b).1 ≫ ι₂.1 ∧
          w'.1 ≫ m''.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom
              (algebraMap R R''))) c).1 ≫ ι₂.1) ∧
      (∃ a'' : Spec (CommRingCat.of R'') ⟶ Y'', a'' ≫ y'' = 𝟙 _) ∧
      (∃ j : pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ⟶ Y'',
        IsOpenImmersion j ∧ j ≫ y'' = pullback.snd y' (Spec.map (CommRingCat.ofHom
            (algebraMap R' R''))) ∧
        ∀ {T : Scheme.{u}} (x : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R''))))
          (x₁ : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
              (x₂ : T ⟶ pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R'')))),
          x₁ ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫
              pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) →
          x₁ ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫
              pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ≫ Spec.map
              (CommRingCat.ofHom (algebraMap R' R'')) →
          x₂ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = x₁ ≫ ι.1 →
          x₂ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = x ≫
              pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) →
          x₂ ≫ j = x ≫ ι₂.1) ∧
      (∃ (D : (pullback y'' y'').Opens) (hle : U'' ≤ D)
        (M : SchemeHomOver (D.ι ≫ pullback.fst y'' y'' ≫ y'') y''),
        (pullback y'' y'').homOfLE hle ≫ M.1 = m''.1 ∧
        ∀ (a₂ : Spec (CommRingCat.of R'') ⟶ pullback y (Spec.map (CommRingCat.ofHom
            (algebraMap R R'')))),
          a₂ ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) = a →
              a₂ ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) = 𝟙 _ →
          ∀ {T : Scheme.{u}} (b : T ⟶ pullback y (Spec.map (CommRingCat.ofHom
              (algebraMap R R'')))) (q : T ⟶ pullback y'' y''),
            q ≫ pullback.fst y'' y'' = b ≫ pullback.snd y (Spec.map (CommRingCat.ofHom
                (algebraMap R R''))) ≫ a₂ ≫ ι₂.1 →
            q ≫ pullback.snd y'' y'' = b ≫ ι₂.1 →
            Set.range q.base ⊆ (D : Set ↑(pullback y'' y''))) := by
  let C : Ctx.{u} :=
    ⟨R, Y, y, U, m, ⟨hU₁, hU₂, hΦ, hΦ₁, hΦ₂, hΨ, hΨ₁, hΨ₂, fun t u v p q => hassoc t u v p q⟩,
        hUK, R', Y', y', ι,
      hgen, hmax, U', m', ⟨hU'₁, hU'₂, hΦ', hΦ'₁, hΦ'₂, hΨ', hΨ'₁, hΨ'₂,
          fun t u v p q => hassoc' t u v p q⟩,
      fun t' w a b c => hext t' w a b c, R'', a, ha⟩
  obtain ⟨G⟩ := C.nonempty_glued
  have : IsOpenImmersion C.k := Ctx.isOpenImmersion_k C
  have : IsOpenImmersion G.jj.1 := G.oij
  refine ⟨G.Y'', G.y'', ⟨C.k ≫ G.jj.1, ?_⟩, G.U'', G.m'', G.sm, G.sep, G.loft, G.qc, inferInstance,
    C.gen₂ G, C.max₂ G, G.hS''.hU₁, G.hS''.hU₂, G.hS''.hΦ, G.hS''.hΦ₁, G.hS''.hΦ₂, G.hS''.hΨ,
        G.hS''.hΨ₁,
    G.hS''.hΨ₂, fun t u v p q => G.hS''.hassoc t u v p q, ?_, ⟨C.ap ≫ G.jj.1, ?_⟩,
    ⟨G.jj.1, inferInstance, G.jj.2, fun x x₁ x₂ h₁ h₂ h₃ h₄ => C.dom G x x₁ x₂ h₁ h₂ h₃ h₄⟩,
        C.progress G⟩
  · rw [Category.assoc, G.jj.2, Ctx.k_yp]
  · intro T t' w a b c ha hb hc
    simp only [RelativeGroupLaw.baseChangePointOfBase_coe]
    exact C.hext₂ G t' w a b c ha hb hc
  · rw [Category.assoc, G.jj.2, Ctx.ap_yp]

end
end NeronModelInfra
end
