/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.FlatBaseChangeSections
public import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebra
public import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# Flat base change for actual direct-image relative spectra

Compatible pairs of affine charts form a locally directed cover. Both
coordinates use principal affine inclusions, so the native relative
spectrum transitions apply directly. The local maps are induced by the
original morphism on sections. Flat base change on these sections makes
the resulting global comparison cartesian.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

private theorem exists_affine_principal_refinement {X : Scheme.{u}}
    (U V : X.AffineZariskiSite) (W : X.Opens) (x : X)
    (hxU : x ∈ U.1) (hxV : x ∈ V.1) (hxW : x ∈ W) :
    ∃ T : X.AffineZariskiSite, T ≤ U ∧ T ≤ V ∧ T.1 ≤ W ∧ x ∈ T.1 := by
  obtain ⟨r, s, hrs, hxr⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, hxV⟩
  let K : X.AffineZariskiSite := U.basicOpen r
  have hKV : K ≤ V := ⟨s, hrs.symm⟩
  obtain ⟨t, ht, hxt⟩ := K.2.exists_basicOpen_le (⟨x, hxW⟩ : W) hxr
  exact ⟨K.basicOpen t, (K.basicOpen_le t).trans (U.basicOpen_le r),
    (K.basicOpen_le t).trans hKV, ht, hxt⟩

/-- Pairs of affine charts compatible with the given base morphism. -/
def AffineBaseChangeIndex {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  { p : X.AffineZariskiSite × Y.AffineZariskiSite // p.2.1 ≤ f ⁻¹ᵁ p.1.1 }

instance {X Y : Scheme.{u}} (f : Y ⟶ X) : PartialOrder (AffineBaseChangeIndex f) :=
  inferInstanceAs (PartialOrder
    { p : X.AffineZariskiSite × Y.AffineZariskiSite // p.2.1 ≤ f ⁻¹ᵁ p.1.1 })

/-- Compatible affine pairs cover the source of an arbitrary base morphism. -/
def affineBaseChangeCover {X Y : Scheme.{u}} (f : Y ⟶ X) : Y.OpenCover where
  I₀ := AffineBaseChangeIndex f
  X i := i.1.2.1.toScheme
  f i := i.1.2.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun y => ?_, fun i => inferInstance⟩
    obtain ⟨U, hyU⟩ := Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top X).ge (Set.mem_univ (f y)))
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (f ⁻¹ᵁ U.1).isOpen
    exact ⟨⟨(⟨U.1, U.2⟩, ⟨W, hW⟩), hWU⟩, ⟨y, hyW⟩, rfl⟩

instance affineBaseChangeCoverIndexPartialOrder {X Y : Scheme.{u}} (f : Y ⟶ X) :
    PartialOrder (affineBaseChangeCover f).I₀ :=
  inferInstanceAs (PartialOrder (AffineBaseChangeIndex f))

instance affineBaseChangeCoverIndexCategory {X Y : Scheme.{u}} (f : Y ⟶ X) :
    SmallCategory (affineBaseChangeCover f).I₀ :=
  inferInstanceAs (SmallCategory (AffineBaseChangeIndex f))

instance affineBaseChangeCover_locallyDirected {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (affineBaseChangeCover f).LocallyDirected where
  trans {i j} h := Y.homOfLE (AffineZariskiSite.toOpens_mono h.le.2)
  trans_comp {i j k} hij hjk :=
    (Y.homOfLE_homOfLE (AffineZariskiSite.toOpens_mono hij.le.2)
      (AffineZariskiSite.toOpens_mono hjk.le.2)).symm
  w {i j} h := Y.homOfLE_ι (AffineZariskiSite.toOpens_mono h.le.2)
  directed {i j} z := by
    let y : Y := (pullback.fst i.1.2.1.ι j.1.2.1.ι ≫ i.1.2.1.ι) z
    have hyi : y ∈ i.1.2.1 := (pullback.fst i.1.2.1.ι j.1.2.1.ι z).2
    have hyj : y ∈ j.1.2.1 := by
      change (pullback.fst i.1.2.1.ι j.1.2.1.ι ≫ i.1.2.1.ι) z ∈ j.1.2.1
      rw [pullback.condition]
      exact (pullback.snd i.1.2.1.ι j.1.2.1.ι z).2
    obtain ⟨U, hUi, hUj, _, hyU⟩ := exists_affine_principal_refinement
      i.1.1 j.1.1 ⊤ (f y) (i.2 hyi) (j.2 hyj) (Set.mem_univ _)
    obtain ⟨W, hWi, hWj, hWU, hyW⟩ := exists_affine_principal_refinement
      i.1.2 j.1.2 (f ⁻¹ᵁ U.1) y hyi hyj hyU
    let k : AffineBaseChangeIndex f := ⟨(U, W), hWU⟩
    refine ⟨k, homOfLE ⟨hUi, hWi⟩, homOfLE ⟨hUj, hWj⟩, ⟨y, hyW⟩, ?_⟩
    apply (pullback.fst i.1.2.1.ι j.1.2.1.ι ≫ i.1.2.1.ι).isOpenEmbedding.injective
    let li : W.1.toScheme ⟶ i.1.2.1.toScheme :=
      Y.homOfLE (AffineZariskiSite.toOpens_mono hWi)
    let lj : W.1.toScheme ⟶ j.1.2.1.toScheme :=
      Y.homOfLE (AffineZariskiSite.toOpens_mono hWj)
    have hw : li ≫ i.1.2.1.ι = lj ≫ j.1.2.1.ι :=
      (Y.homOfLE_ι (AffineZariskiSite.toOpens_mono hWi)).trans
        (Y.homOfLE_ι (AffineZariskiSite.toOpens_mono hWj)).symm
    have hl : pullback.lift li lj hw ≫ pullback.fst i.1.2.1.ι j.1.2.1.ι ≫
        i.1.2.1.ι = W.1.ι :=
      (pullback.lift_fst_assoc li lj hw i.1.2.1.ι).trans
        (Y.homOfLE_ι (AffineZariskiSite.toOpens_mono hWi))
    exact congrArg (fun q : W.1.toScheme ⟶ Y => q ⟨y, hyW⟩) hl
  property_trans {i j} h :=
    inferInstanceAs
      (IsOpenImmersion (Y.homOfLE (AffineZariskiSite.toOpens_mono h.le.2)))

namespace DirectImageAlgebra

variable {X Y V V' : Scheme.{u}} (g : V ⟶ X) (b : V' ⟶ Y)
  [(RelativeSpec.underlyingModule (structureMap g)).IsQuasicoherent]
  [(RelativeSpec.underlyingModule (structureMap b)).IsQuasicoherent]
  (f : Y ⟶ X) (a : V' ⟶ V) (w : a ≫ g = b ≫ f)

/-- The compatible affine cover pulled back to the source relative spectrum. -/
abbrev comparisonCover : (RelativeSpec.scheme (structureMap b)).OpenCover :=
  (affineBaseChangeCover f).pullback₁ (RelativeSpec.toBase (structureMap b))

/-- Identify each chart of the comparison cover with its affine sections spectrum. -/
def comparisonChartIso (i : AffineBaseChangeIndex f) :
    (comparisonCover b f).X i ≅ Spec Γ(V', b ⁻¹ᵁ i.1.2.1) :=
  (RelativeSpec.isPullback_affineModel (structureMap b) i.1.2).flip.isoPullback.symm

private theorem comparisonChartIso_fst (i : AffineBaseChangeIndex f) :
    (comparisonChartIso b f i).hom ≫ (RelativeSpec.openCover (structureMap b)).f i.1.2 =
      (comparisonCover b f).f i :=
  (RelativeSpec.isPullback_affineModel (structureMap b) i.1.2).flip.isoPullback_inv_fst

private theorem comparisonChartIso_snd (i : AffineBaseChangeIndex f) :
    (comparisonChartIso b f i).hom ≫
        (Spec.map (b.app i.1.2.1) ≫ i.1.2.2.isoSpec.inv) =
      (affineBaseChangeCover f).pullbackHom (RelativeSpec.toBase (structureMap b)) i :=
  (RelativeSpec.isPullback_affineModel (structureMap b) i.1.2).flip.isoPullback_inv_snd

omit [(RelativeSpec.underlyingModule (structureMap g)).IsQuasicoherent]
  [(RelativeSpec.underlyingModule (structureMap b)).IsQuasicoherent] in
include w in
/-- The base-change square restricts the source chart into the target chart. -/
theorem comparison_preimage (i : AffineBaseChangeIndex f) :
    b ⁻¹ᵁ i.1.2.1 ≤ a ⁻¹ᵁ (g ⁻¹ᵁ i.1.1.1) := by
  rw [← Hom.comp_preimage, w, Hom.comp_preimage]
  exact b.preimage_mono i.2

/-- The map on sections induced by the original morphism on compatible charts. -/
abbrev comparisonSectionMap (i : AffineBaseChangeIndex f) :
    Γ(V, g ⁻¹ᵁ i.1.1.1) ⟶ Γ(V', b ⁻¹ᵁ i.1.2.1) :=
  a.appLE _ _ (comparison_preimage g b f a w i)

/-- The relative-spectrum comparison on a compatible affine chart. -/
def comparisonChart (i : AffineBaseChangeIndex f) :
    (comparisonCover b f).X i ⟶ RelativeSpec.scheme (structureMap g) :=
  (comparisonChartIso b f i).hom ≫ Spec.map (comparisonSectionMap g b f a w i) ≫
    (RelativeSpec.openCover (structureMap g)).f i.1.1

/-- The affine comparison maps agree along the cover transitions. -/
theorem comparisonChart_compatible {i j : AffineBaseChangeIndex f} (h : i ⟶ j) :
    (comparisonCover b f).trans h ≫ comparisonChart g b f a w j =
      comparisonChart g b f a w i := by
  let hi : i.1.1 ⟶ j.1.1 := homOfLE h.le.1
  let hj : i.1.2 ⟶ j.1.2 := homOfLE h.le.2
  let Pᵢ : Scheme.{u} := (comparisonCover b f).X i
  let Pⱼ : Scheme.{u} := (comparisonCover b f).X j
  let Aᵢ : CommRingCat.{u} := Γ(V, g ⁻¹ᵁ i.1.1.1)
  let Aⱼ : CommRingCat.{u} := Γ(V, g ⁻¹ᵁ j.1.1.1)
  let Bᵢ : CommRingCat.{u} := Γ(V', b ⁻¹ᵁ i.1.2.1)
  let Bⱼ : CommRingCat.{u} := Γ(V', b ⁻¹ᵁ j.1.2.1)
  let S : Scheme.{u} := RelativeSpec.scheme (structureMap g)
  let S' : Scheme.{u} := RelativeSpec.scheme (structureMap b)
  let t : Pᵢ ⟶ Pⱼ := (comparisonCover b f).trans h
  let eᵢ : Pᵢ ≅ Spec Bᵢ := comparisonChartIso b f i
  let eⱼ : Pⱼ ≅ Spec Bⱼ := comparisonChartIso b f j
  let cᵢ : Spec Aᵢ ⟶ S := (RelativeSpec.openCover (structureMap g)).f i.1.1
  let cⱼ : Spec Aⱼ ⟶ S := (RelativeSpec.openCover (structureMap g)).f j.1.1
  let cᵢ' : Spec Bᵢ ⟶ S' := (RelativeSpec.openCover (structureMap b)).f i.1.2
  let cⱼ' : Spec Bⱼ ⟶ S' := (RelativeSpec.openCover (structureMap b)).f j.1.2
  let sᵢ : Aᵢ ⟶ Bᵢ := comparisonSectionMap g b f a w i
  let sⱼ : Aⱼ ⟶ Bⱼ := comparisonSectionMap g b f a w j
  let rA : Aⱼ ⟶ Aᵢ := V.presheaf.map ((Opens.map g.base).map
    ((AffineZariskiSite.toOpensFunctor X).map hi)).op
  let rB : Bⱼ ⟶ Bᵢ := V'.presheaf.map ((Opens.map b.base).map
    ((AffineZariskiSite.toOpensFunctor Y).map hj)).op
  have hc : Spec.map rA ≫ cⱼ = cᵢ :=
    RelativeSpec.restriction_openCover (structureMap g) hi
  have hc' : Spec.map rB ≫ cⱼ' = cᵢ' :=
    RelativeSpec.restriction_openCover (structureMap b) hj
  have he : t ≫ eⱼ.hom = eᵢ.hom ≫ Spec.map rB := by
    have : IsOpenImmersion cⱼ' :=
      (RelativeSpec.openCover (structureMap b)).map_prop _
    apply (cancel_mono cⱼ').mp
    calc
      (t ≫ eⱼ.hom) ≫ cⱼ' = t ≫ (eⱼ.hom ≫ cⱼ') := Category.assoc _ _ _
      _ = t ≫ (comparisonCover b f).f j :=
        congrArg (fun k : Pⱼ ⟶ S' => t ≫ k) (comparisonChartIso_fst b f j)
      _ = (comparisonCover b f).f i := (comparisonCover b f).trans_map h
      _ = eᵢ.hom ≫ cᵢ' := (comparisonChartIso_fst b f i).symm
      _ = eᵢ.hom ≫ (Spec.map rB ≫ cⱼ') :=
        congrArg (fun k : Spec Bᵢ ⟶ S' => eᵢ.hom ≫ k) hc'.symm
      _ = (eᵢ.hom ≫ Spec.map rB) ≫ cⱼ' := (Category.assoc _ _ _).symm
  have hs : sⱼ ≫ rB = rA ≫ sᵢ :=
    (a.appLE_map (comparison_preimage g b f a w j)
      ((Opens.map b.base).map ((AffineZariskiSite.toOpensFunctor Y).map hj)).op).trans
      (a.map_appLE (comparison_preimage g b f a w i)
        ((Opens.map g.base).map ((AffineZariskiSite.toOpensFunctor X).map hi)).op).symm
  change t ≫ (eⱼ.hom ≫ Spec.map sⱼ ≫ cⱼ) = eᵢ.hom ≫ Spec.map sᵢ ≫ cᵢ
  rw [← Category.assoc, he, Category.assoc, ← Spec.map_comp_assoc, hs,
    Spec.map_comp_assoc, hc]

/-- The actual cross-base morphism of direct-image relative spectra,
constructed from the original morphism on sections. -/
def baseChangeMap :
    RelativeSpec.scheme (structureMap b) ⟶ RelativeSpec.scheme (structureMap g) :=
  (comparisonCover b f).glueMorphismsOfLocallyDirected
    (comparisonChart g b f a w) (comparisonChart_compatible g b f a w)

private theorem comparisonCover_baseChangeMap (i : AffineBaseChangeIndex f) :
    (comparisonCover b f).f i ≫ baseChangeMap g b f a w = comparisonChart g b f a w i :=
  (comparisonCover b f).map_glueMorphismsOfLocallyDirected
    (comparisonChart g b f a w) (comparisonChart_compatible g b f a w) i

omit [(RelativeSpec.underlyingModule (structureMap b)).IsQuasicoherent] in
private theorem isPullback_comparisonChart [QuasiCompact g] [QuasiSeparated g] [Flat f]
    (H : IsPullback a b g f) (i : AffineBaseChangeIndex f) :
    IsPullback (Spec.map (b.app i.1.2.1) ≫ i.1.2.2.isoSpec.inv)
      (Spec.map (comparisonSectionMap g b f a H.w i) ≫
        (RelativeSpec.openCover (structureMap g)).f i.1.1)
      (i.1.2.1.ι ≫ f) (RelativeSpec.toBase (structureMap g)) := by
  let U := i.1.1
  let W := i.1.2
  have hopen : b ⁻¹ᵁ W.1 = a ⁻¹ᵁ (g ⁻¹ᵁ U.1) ⊓ b ⁻¹ᵁ W.1 :=
    (inf_eq_right.mpr (comparison_preimage g b f a H.w i)).symm
  have hIso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H i.2 le_rfl
    hopen U.2 W.2 (g.isCompact_preimage U.2.isCompact)
    (g.isQuasiSeparated_preimage U.2.isQuasiSeparated)
  have hp := (isIso_pushoutSection_iff H i.2 le_rfl hopen).mp hIso
  have hspec := (isPullback_SpecMap_of_isPushout _ _ _ _ hp).flip
  have hs : IsPullback (Spec.map (b.app W.1) ≫ W.2.isoSpec.inv)
      (Spec.map (comparisonSectionMap g b f a H.w i))
      (f.resLE U.1 W.1 i.2) (Spec.map (g.app U.1) ≫ U.2.isoSpec.inv) := by
    refine hspec.of_iso (Iso.refl _) W.2.isoSpec.symm (Iso.refl _)
      U.2.isoSpec.symm ?_ ?_ ?_ ?_
    · change Spec.map (b.appLE W.1 (b ⁻¹ᵁ W.1) le_rfl) ≫ W.2.isoSpec.inv =
        𝟙 _ ≫ (Spec.map (b.app W.1) ≫ W.2.isoSpec.inv)
      exact (congrArg (fun k : Γ(Y, W.1) ⟶ Γ(V', b ⁻¹ᵁ W.1) =>
        Spec.map k ≫ W.2.isoSpec.inv) (b.appLE_eq_app (U := W.1))).trans
          (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · change Spec.map (f.appLE U.1 W.1 i.2) ≫ U.2.isoSpec.inv =
        W.2.isoSpec.inv ≫ f.resLE U.1 W.1 i.2
      apply (cancel_mono U.1.ι).mp
      rw [Category.assoc, Category.assoc, Hom.resLE_comp_ι]
      exact IsAffineOpen.SpecMap_appLE_fromSpec f U.2 W.2 i.2
    · change Spec.map (g.appLE U.1 (g ⁻¹ᵁ U.1) le_rfl) ≫ U.2.isoSpec.inv =
        𝟙 _ ≫ (Spec.map (g.app U.1) ≫ U.2.isoSpec.inv)
      exact (congrArg (fun k : Γ(X, U.1) ⟶ Γ(V, g ⁻¹ᵁ U.1) =>
        Spec.map k ≫ U.2.isoSpec.inv) (g.appLE_eq_app (U := U.1))).trans
          (Category.id_comp _).symm
  have h := hs.paste_vert (RelativeSpec.isPullback_affineModel (structureMap g) U)
  rw [Hom.resLE_comp_ι] at h
  exact h

/-- Flat base change commutes with the constructed direct-image relative
spectrum on arbitrary bases. The original cartesian square supplies all
section-ring comparisons; none are assumed. -/
theorem isPullback_baseChangeMap [QuasiCompact g] [QuasiSeparated g] [Flat f]
    (H : IsPullback a b g f) :
    IsPullback (baseChangeMap g b f a H.w) (RelativeSpec.toBase (structureMap b))
      (RelativeSpec.toBase (structureMap g)) f := by
  apply IsPullback.flip
  apply Scheme.isPullback_of_openCover (RelativeSpec.toBase (structureMap b))
    (baseChangeMap g b f a H.w) f (RelativeSpec.toBase (structureMap g))
    (affineBaseChangeCover f)
  intro i
  let e := comparisonChartIso b f i
  refine (isPullback_comparisonChart g b f a H i).of_iso e.symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change Spec.map (b.app i.1.2.1) ≫ i.1.2.2.isoSpec.inv =
      e.inv ≫ (affineBaseChangeCover f).pullbackHom
        (RelativeSpec.toBase (structureMap b)) i
    exact (Iso.eq_inv_comp e).mpr (comparisonChartIso_snd b f i)
  · change Spec.map (comparisonSectionMap g b f a H.w i) ≫
        (RelativeSpec.openCover (structureMap g)).f i.1.1 =
      e.inv ≫ ((comparisonCover b f).f i ≫ baseChangeMap g b f a H.w)
    exact (Iso.eq_inv_comp e).mpr (comparisonCover_baseChangeMap g b f a H.w i).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

end DirectImageAlgebra

end AlgebraicGeometry.Scheme
