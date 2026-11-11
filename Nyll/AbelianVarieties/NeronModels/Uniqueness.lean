/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Nyll.AbelianVarieties.NeronModels.Basic

/-!
# Uniqueness of Néron models

The existing mapping property extends generic-fibre isomorphisms uniquely.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_NeronModelUniquenessUpToIsomorphism.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

section ValueFunctoriality

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X Y Z : Scheme.{u}}

theorem genericFibreRestrict_val_eq_id (f : X ⟶ Spec (CommRingCat.of R))
    (χ : SchemeHomOver f f) (hχ : χ.1 = 𝟙 X) :
    (genericFibreRestrict R K f f χ).1 =
      𝟙 (pullback f (specGenericFibreInclusion R K)) := by
  have hχ' : χ = schemeHomOverId f := Subtype.ext hχ
  exact congrArg Subtype.val
    ((congrArg (genericFibreRestrict R K f f) hχ').trans
      (genericFibreRestrict_schemeHomOverId R K f))

theorem genericFibreRestrict_val_eq_comp (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (e : Z ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) (χ : SchemeHomOver g e)
    (hχ : χ.1 = φ.1 ≫ ψ.1) :
    (genericFibreRestrict R K e g χ).1 =
      (genericFibreRestrict R K f g φ).1 ≫ (genericFibreRestrict R K e f ψ).1 := by
  have hχ' : χ = schemeHomOverComp φ ψ := Subtype.ext hχ
  exact congrArg Subtype.val
    ((congrArg (genericFibreRestrict R K e g) hχ').trans
      (genericFibreRestrict_schemeHomOverComp R K e f g φ ψ))

end ValueFunctoriality

section MinimalModelLemma

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X : Scheme.{u}}

theorem neronModel_end_eq_id_of_restrict_val_eq_id (f : X ⟶ Spec (CommRingCat.of R))
    (hN : NeronUniqueExtension R K f) (hsf : Smooth f) (w : SchemeHomOver f f)
    (hw : (genericFibreRestrict R K f f w).1 =
      𝟙 (pullback f (specGenericFibreInclusion R K))) :
    w.1 = 𝟙 X := by
  have hres : genericFibreRestrict R K f f w =
      genericFibreRestrict R K f f ⟨𝟙 X, Category.id_comp f⟩ := by
    apply Subtype.ext
    rw [hw, genericFibreRestrict_val_eq_id R K f ⟨𝟙 X, Category.id_comp f⟩ rfl]
  have hwid : w = (⟨𝟙 X, Category.id_comp f⟩ : SchemeHomOver f f) :=
    (hN X f hsf).1 hres
  exact congrArg Subtype.val hwid

end MinimalModelLemma

section TwoModels

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable {X X' : Scheme.{u}}

theorem neronTwoModels_extension_unique
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf' : NeronUniqueExtension R K f') (hsf : Smooth f)
    {u₁ u₂ : SchemeHomOver f f'}
    (h : genericFibreRestrict R K f' f u₁ = genericFibreRestrict R K f' f u₂) :
    u₁ = u₂ :=
  (hNf' X f hsf).1 h

theorem neronTwoModels_existsUnique_homExtension
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf' : NeronUniqueExtension R K f') (hsf : Smooth f)
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))) :
    ∃! u : SchemeHomOver f f', genericFibreRestrict R K f' f u = uK :=
  (hNf' X f hsf).existsUnique uK

theorem neronTwoModels_comp_eq_id
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hsf : Smooth f)
    {uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))}
    {vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    {u : SchemeHomOver f f'} {v : SchemeHomOver f' f}
    (hu : genericFibreRestrict R K f' f u = uK)
    (hv : genericFibreRestrict R K f f' v = vK) :
    u.1 ≫ v.1 = 𝟙 X := by
  have hcomp : (u.1 ≫ v.1) ≫ f = f := by rw [Category.assoc, v.2, u.2]
  have hval : (genericFibreRestrict R K f f ⟨u.1 ≫ v.1, hcomp⟩).1 =
      𝟙 (pullback f (specGenericFibreInclusion R K)) := by
    rw [genericFibreRestrict_val_eq_comp R K f' f f u v ⟨u.1 ≫ v.1, hcomp⟩ rfl, hu, hv]
    exact huv
  exact neronModel_end_eq_id_of_restrict_val_eq_id R K f hNf hsf ⟨u.1 ≫ v.1, hcomp⟩ hval

theorem neronTwoModels_exists_isoExtension
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃ (u : SchemeHomOver f f') (v : SchemeHomOver f' f),
      genericFibreRestrict R K f' f u = uK ∧
      genericFibreRestrict R K f f' v = vK ∧
      u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' := by
  obtain ⟨u, hu⟩ := (hNf' X f hsf).2 uK
  obtain ⟨v, hv⟩ := (hNf X' f' hsf').2 vK
  exact ⟨u, v, hu, hv, neronTwoModels_comp_eq_id hNf hsf huv hu hv,
    neronTwoModels_comp_eq_id hNf' hsf' hvu hv hu⟩

theorem neronTwoModels_existsUnique_isoExtension
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃! u : SchemeHomOver f f',
      genericFibreRestrict R K f' f u = uK ∧
      ∃ v : SchemeHomOver f' f,
        genericFibreRestrict R K f f' v = vK ∧
        u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' := by
  obtain ⟨u, v, hu, hv, huvId, hvuId⟩ :=
    neronTwoModels_exists_isoExtension hNf hNf' hsf hsf' uK vK huv hvu
  refine ⟨u, ⟨hu, v, hv, huvId, hvuId⟩, ?_⟩
  rintro u₂ ⟨hu₂, -⟩
  exact neronTwoModels_extension_unique hNf' hsf (hu₂.trans hu.symm)

theorem neronTwoModels_isoExtension_isIso
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    {uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))}
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K)))
    {u : SchemeHomOver f f'} (hu : genericFibreRestrict R K f' f u = uK) :
    IsIso u.1 := by
  obtain ⟨v, hv⟩ := (hNf X' f' hsf').2 vK
  exact ⟨⟨v.1, neronTwoModels_comp_eq_id hNf hsf huv hu hv,
    neronTwoModels_comp_eq_id hNf' hsf' hvu hv hu⟩⟩

theorem neronTwoModels_existsUnique_isoExtension_of_isIso
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))) [IsIso uK.1] :
    ∃! u : SchemeHomOver f f',
      genericFibreRestrict R K f' f u = uK ∧
      ∃ v : SchemeHomOver f' f,
        (genericFibreRestrict R K f f' v).1 = inv uK.1 ∧
        u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' := by
  have hvKmem : inv uK.1 ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd f' (specGenericFibreInclusion R K) :=
    (IsIso.inv_comp_eq uK.1).mpr uK.2.symm
  obtain ⟨u, ⟨hu, v, hv, huvId, hvuId⟩, -⟩ :=
    neronTwoModels_existsUnique_isoExtension hNf hNf' hsf hsf' uK ⟨inv uK.1, hvKmem⟩
      (IsIso.hom_inv_id uK.1) (IsIso.inv_hom_id uK.1)
  refine ⟨u, ⟨hu, v, congrArg Subtype.val hv, huvId, hvuId⟩, ?_⟩
  rintro u₂ ⟨hu₂, -⟩
  exact neronTwoModels_extension_unique hNf' hsf (hu₂.trans hu.symm)

end TwoModels

section BundleForm

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDedekindDomain R] [IsFractionRing R K]
variable {X X' : Scheme.{u}}
variable {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}

theorem NeronModelPropertyBundle.exists_isoExtension
    (h : NeronModelPropertyBundle R K f) (h' : NeronModelPropertyBundle R K f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃ (u : SchemeHomOver f f') (v : SchemeHomOver f' f),
      genericFibreRestrict R K f' f u = uK ∧
      genericFibreRestrict R K f f' v = vK ∧
      u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' :=
  neronTwoModels_exists_isoExtension h.neronMapping h'.neronMapping h.smooth h'.smooth
    uK vK huv hvu

theorem NeronModelPropertyBundle.existsUnique_isoExtension
    (h : NeronModelPropertyBundle R K f) (h' : NeronModelPropertyBundle R K f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃! u : SchemeHomOver f f',
      genericFibreRestrict R K f' f u = uK ∧
      ∃ v : SchemeHomOver f' f,
        genericFibreRestrict R K f f' v = vK ∧
        u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' :=
  neronTwoModels_existsUnique_isoExtension h.neronMapping h'.neronMapping h.smooth h'.smooth
    uK vK huv hvu

theorem NeronModelPropertyBundle.isoExtension_isIso
    (h : NeronModelPropertyBundle R K f) (h' : NeronModelPropertyBundle R K f')
    {uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))}
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K)))
    {u : SchemeHomOver f f'} (hu : genericFibreRestrict R K f' f u = uK) :
    IsIso u.1 :=
  neronTwoModels_isoExtension_isIso h.neronMapping h'.neronMapping h.smooth h'.smooth
    vK huv hvu hu

end BundleForm


end NeronModelInfra


end
end
