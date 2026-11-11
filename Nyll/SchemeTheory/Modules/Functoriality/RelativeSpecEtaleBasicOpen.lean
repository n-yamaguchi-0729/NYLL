/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Functoriality.FiniteRelativeSpec
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHomProperties

/-!
# Étale basic opens of an actual relative spectrum

Quasicoherence identifies the actual algebra sections on a basic open with
the principal localization of the original section ring. An étale map to
that localization therefore gives an étale restriction of the constructed
relative spectrum over the same basic open of the original scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.RelativeSpec

variable {X : Scheme.{u}} {A : TopCat.Sheaf CommRingCat.{u} X}

/-- Étaleness of the original map to a principal localization supplies
étaleness of the actual relative-spectrum morphism over that basic open. -/
theorem etale_restrict_basicOpen_of_etale_away
    (α : X.sheaf ⟶ A) [(underlyingModule α).IsQuasicoherent]
    (U : X.AffineZariskiSite) (r : Γ(X, U.1)) :
    let C : CommRingCat.{u} := A.obj.obj (op U.1)
    let c : Γ(X, U.1) ⟶ C := α.hom.app (op U.1)
    ((algebraMap C (Localization.Away (c.hom r))).comp c.hom).Etale →
      AlgebraicGeometry.Etale (toBase α ∣_ X.basicOpen r) := by
  intro C c hEtale
  let V : X.AffineZariskiSite := U.basicOpen r
  let R : CommRingCat.{u} := Γ(X, U.1)
  let R' : CommRingCat.{u} := Γ(X, V.1)
  let D : CommRingCat.{u} := A.obj.obj (op V.1)
  let k : V.1 ⟶ U.1 := homOfLE (X.basicOpen_le r)
  let q : C ⟶ D := A.obj.map k.op
  let rbase : R ⟶ R' := X.presheaf.map k.op
  let cV : R' ⟶ D := α.hom.app (op V.1)
  let hCD : Algebra C D := q.hom.toAlgebra
  have hDloc : IsLocalization.Away (c.hom r) D :=
    isLocalization_basicOpen α U r
  let e : Localization.Away (c.hom r) ≃ₐ[C] D :=
    IsLocalization.algEquiv (Submonoid.powers (c.hom r))
      (Localization.Away (c.hom r)) D
  have hEtaleComp : (q.hom.comp c.hom).Etale := by
    have h := RingHom.Etale.respectsIso.1
      ((algebraMap C (Localization.Away (c.hom r))).comp c.hom)
      e.toRingEquiv hEtale
    have he : e.toRingEquiv.toRingHom.comp
        ((algebraMap C (Localization.Away (c.hom r))).comp c.hom) =
          q.hom.comp c.hom := by
      apply RingHom.ext
      intro x
      exact e.commutes (c.hom x)
    exact he ▸ h
  have hnat : rbase ≫ cV = c ≫ q := α.hom.naturality k.op
  have hEtaleRing : (rbase ≫ cV).hom.Etale :=
    (congrArg (fun a : R ⟶ D => a.hom.Etale) hnat).mpr hEtaleComp
  have hSpec : AlgebraicGeometry.Etale (Spec.map (rbase ≫ cV)) :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr hEtaleRing
  have hSpecComp : AlgebraicGeometry.Etale (Spec.map cV ≫ Spec.map rbase) := by
    rw [← Spec.map_comp]
    exact hSpec
  let hRR' : Algebra R R' := rbase.hom.toAlgebra
  have hRloc : IsLocalization.Away r R' :=
    U.2.isLocalization_of_eq_basicOpen r k rfl
  have hOpen : IsOpenImmersion (Spec.map rbase) :=
    IsOpenImmersion.of_isLocalization (R := R) (S := R') r
  have hV : AlgebraicGeometry.Etale (Spec.map cV) :=
    AlgebraicGeometry.Etale.of_comp (Spec.map cV) (Spec.map rbase)
  have hModel : AlgebraicGeometry.Etale
      ((affineModelIso α V).hom ≫ Spec.map cV) := inferInstance
  have hRestrict : AlgebraicGeometry.Etale ((toBase α ∣_ V.1) ≫ V.2.isoSpec.hom) :=
    (congrArg (fun a => AlgebraicGeometry.Etale a) (affineModelIso_toBase α V)).mp hModel
  change AlgebraicGeometry.Etale (toBase α ∣_ V.1)
  exact AlgebraicGeometry.Etale.of_comp (toBase α ∣_ V.1) V.2.isoSpec.hom

end AlgebraicGeometry.Scheme.RelativeSpec
