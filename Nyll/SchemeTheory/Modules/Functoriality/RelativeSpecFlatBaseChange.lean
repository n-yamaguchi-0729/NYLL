/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.FlatBaseChangeAffinization
public import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebra
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Actual relative spectra under flat affine base change

The full affine chart identifies the constructed relative spectrum with
the spectrum of its original global-section algebra. Flat base change
on those actual sections therefore gives a cartesian square of the
constructed relative spectra, for any actual cartesian presentation of
the original source. The comparison is the original pullback map on
sections conjugated by these chart isomorphisms.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- Flat base change on global sections for an arbitrary actual
cartesian presentation, retaining its original projection maps. -/
theorem isPushout_appTop_of_flat_of_isPullback
    {X Y V V' : Scheme.{u}} {g : V ⟶ X} {f : Y ⟶ X}
    {a : V' ⟶ V} {b : V' ⟶ Y} [IsAffine X] [IsAffine Y]
    [QuasiCompact g] [QuasiSeparated g] [Flat f] (H : IsPullback a b g f) :
    IsPushout g.appTop f.appTop a.appTop b.appTop := by
  let e : Γ(pullback g f, ⊤) ≅ Γ(V', ⊤) := Scheme.Γ.mapIso H.isoPullback.op
  refine (isPushout_appTop_of_flat g f).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) e ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · change (pullback.fst g f).appTop ≫ H.isoPullback.hom.appTop = 𝟙 _ ≫ a.appTop
    rw [← Scheme.Hom.comp_appTop, H.isoPullback_hom_fst, Category.id_comp]
  · change (pullback.snd g f).appTop ≫ H.isoPullback.hom.appTop = 𝟙 _ ≫ b.appTop
    rw [← Scheme.Hom.comp_appTop, H.isoPullback_hom_snd, Category.id_comp]

namespace Scheme.RelativeSpec

variable {X : Scheme.{u}} [IsAffine X] {A : TopCat.Sheaf CommRingCat.{u} X}
  (α : X.sheaf ⟶ A) [(underlyingModule α).IsQuasicoherent]

/-- Over an affine base, the original full affine chart is an isomorphism
from the spectrum of the actual global-section algebra. -/
def topChartIso : Spec (A.obj.obj (op ⊤)) ≅ scheme α := by
  let W : X.AffineZariskiSite := ⟨⊤, isAffineOpen_top X⟩
  let j : Spec (A.obj.obj (op ⊤)) ⟶ scheme α := (openCover α).f W
  have : IsOpenImmersion j := (openCover α).map_prop W
  have hj : j.opensRange = ⊤ :=
    (toBase_preimage α W).symm.trans (toBase α).preimage_top
  have : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j hj
  exact asIso j

/-- The full chart carries the actual structure map of the algebra. -/
@[reassoc]
theorem topChartIso_hom_toBase :
    (topChartIso α).hom ≫ toBase α =
      Spec.map (α.hom.app (op ⊤)) ≫ X.isoSpec.inv := by
  have h := openCover_toBase α (⟨⊤, isAffineOpen_top X⟩ : X.AffineZariskiSite)
  exact h.trans (congrArg (fun k => Spec.map (α.hom.app (op ⊤)) ≫ k)
    (IsAffineOpen.fromSpec_top (X := X)))

end Scheme.RelativeSpec

namespace Scheme.DirectImageAlgebra

variable {X Y V V' : Scheme.{u}} [IsAffine X] [IsAffine Y]
  (g : V ⟶ X) (b : V' ⟶ Y)
  [(RelativeSpec.underlyingModule (structureMap g)).IsQuasicoherent]
  [(RelativeSpec.underlyingModule (structureMap b)).IsQuasicoherent]

/-- The cross-base comparison uses the original morphism on global
sections and the actual full-chart isomorphisms. -/
def affineBaseChangeMap (a : V' ⟶ V) :
    RelativeSpec.scheme (structureMap b) ⟶ RelativeSpec.scheme (structureMap g) :=
  (RelativeSpec.topChartIso (structureMap b)).inv ≫ Spec.map a.appTop ≫
    (RelativeSpec.topChartIso (structureMap g)).hom

/-- Flat base change gives a cartesian square of the actual relative
spectra over affine bases. No section-ring comparison is an input. -/
theorem isPullback_affineBaseChangeMap (f : Y ⟶ X) [Flat f]
    [QuasiCompact g] [QuasiSeparated g] (a : V' ⟶ V) (H : IsPullback a b g f) :
    IsPullback (affineBaseChangeMap g b a) (RelativeSpec.toBase (structureMap b))
      (RelativeSpec.toBase (structureMap g)) f := by
  let e := RelativeSpec.topChartIso (structureMap g)
  let e' := RelativeSpec.topChartIso (structureMap b)
  have h := isPullback_SpecMap_of_isPushout g.appTop f.appTop a.appTop b.appTop
    (isPushout_appTop_of_flat_of_isPullback H)
  refine h.of_iso e' e Y.isoSpec.symm X.isoSpec.symm ?_ ?_ ?_ ?_
  · change Spec.map a.appTop ≫ e.hom =
      e'.hom ≫ (e'.inv ≫ Spec.map a.appTop ≫ e.hom)
    exact (Iso.hom_inv_id_assoc e' (Spec.map a.appTop ≫ e.hom)).symm
  · exact (RelativeSpec.topChartIso_hom_toBase (structureMap b)).symm
  · exact (RelativeSpec.topChartIso_hom_toBase (structureMap g)).symm
  · change Spec.map f.appTop ≫ X.isoSpec.inv = Y.isoSpec.inv ≫ f
    have hn : f ≫ X.isoSpec.hom = Y.isoSpec.hom ≫ Spec.map f.appTop :=
      Scheme.toSpecΓ_naturality f
    apply (cancel_epi Y.isoSpec.hom).mp
    calc
      Y.isoSpec.hom ≫ (Spec.map f.appTop ≫ X.isoSpec.inv) =
          (Y.isoSpec.hom ≫ Spec.map f.appTop) ≫ X.isoSpec.inv :=
        (Category.assoc _ _ _).symm
      _ = (f ≫ X.isoSpec.hom) ≫ X.isoSpec.inv :=
        congrArg (fun k => k ≫ X.isoSpec.inv) hn.symm
      _ = f := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = Y.isoSpec.hom ≫ (Y.isoSpec.inv ≫ f) :=
        (Iso.hom_inv_id_assoc Y.isoSpec f).symm

end Scheme.DirectImageAlgebra

end AlgebraicGeometry
