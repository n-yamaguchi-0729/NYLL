/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The support-restriction argument is adapted from RelEffCartierDivRestrict.lean.
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelEffCartierDivRestrict.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Nyll.AlgebraicCurves.RelativeDivisors.Support.RelEffCartierDivSupportedIn
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Restricting supported relative divisors without changing the base

An actual divisor family supported in an open curve restricts to that open
over the same test scheme and base. Its finite flat projection and full ideal
are preserved. Restriction commutes with arbitrary changes of test scheme.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RelEffCartierDiv

variable {C S : Scheme.{u}} (c : C ⟶ S) (U : C.Opens)

/-- The open inclusion of the base-changed open curve over the original base. -/
def openProdMap {T : Scheme.{u}} (t : T ⟶ S) :
    pullback (U.ι ≫ c) t ⟶ pullback c t :=
  pullback.map _ _ _ _ U.ι (𝟙 T) (𝟙 S) (Category.comp_id _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

instance {T : Scheme.{u}} (t : T ⟶ S) : IsOpenImmersion (openProdMap c U t) := by
  delta openProdMap
  infer_instance

@[reassoc] theorem openProdMap_fst {T : Scheme.{u}} (t : T ⟶ S) :
    openProdMap c U t ≫ pullback.fst c t = pullback.fst (U.ι ≫ c) t ≫ U.ι := by
  exact pullback.lift_fst _ _ _

@[reassoc] theorem openProdMap_snd {T : Scheme.{u}} (t : T ⟶ S) :
    openProdMap c U t ≫ pullback.snd c t = pullback.snd (U.ι ≫ c) t := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- This is the actual pullback square for the source open immersion. -/
theorem isPullback_openProdMap {T : Scheme.{u}} (t : T ⟶ S) :
    IsPullback (openProdMap c U t) (pullback.fst (U.ι ≫ c) t)
      (pullback.fst c t) U.ι := by
  have ho := (IsPullback.of_hasPullback (U.ι ≫ c) t).flip
  rw [← openProdMap_snd c U t] at ho
  exact IsPullback.of_right ho (openProdMap_fst c U t) (IsPullback.of_hasPullback c t).flip

theorem range_openProdMap {T : Scheme.{u}} (t : T ⟶ S) :
    Set.range (openProdMap c U t) = (pullback.fst c t) ⁻¹' (U : Set C) := by
  have sq := isPullback_openProdMap c U t
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr sq.isoPullback.hom.surjective, Set.image_univ,
    Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

/-- Base change of a supported divisor along the open immersion is an isomorphism. -/
theorem isIso_pullback_snd_openProdMap {T : Scheme.{u}} {t : T ⟶ S} {n : ℕ}
    (E : RelEffCartierDiv c n t) (hE : E.SupportedIn U) :
    IsIso (pullback.snd (openProdMap c U t) E.I.subschemeι) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  ext z
  rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top,
    Scheme.Pullback.range_snd, range_openProdMap]
  constructor
  · intro _
    trivial
  · intro _
    apply hE
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self z

/-- The actual supported divisor restricted to the open curve over the same base. -/
def restrictToOpen {T : Scheme.{u}} {t : T ⟶ S} {n : ℕ}
    (E : RelEffCartierDiv c n t) (hE : E.SupportedIn U) :
    RelEffCartierDiv (U.ι ≫ c) n t := by
  have := isIso_pullback_snd_openProdMap c U E hE
  have he : (E.I.comap (openProdMap c U t)).subschemeι ≫
      pullback.snd (U.ι ≫ c) t =
      ((E.I.comapIso (openProdMap c U t)).hom ≫
        pullback.snd (openProdMap c U t) E.I.subschemeι) ≫
          (E.I.subschemeι ≫ pullback.snd c t) := by
    rw [← openProdMap_snd c U t, ← Scheme.IdealSheafData.comapIso_hom_fst]
    simp only [Category.assoc, pullback.condition_assoc]
  exact
    { I := E.I.comap (openProdMap c U t)
      isFinite := by have := E.isFinite; rw [he]; infer_instance
      flat := by have := E.flat; rw [he]; infer_instance
      locallyOfFinitePresentation := by
        have := E.locallyOfFinitePresentation
        rw [he]
        infer_instance
      finrank_eq := fun x => by
        have := E.isFinite
        have := E.flat
        rw [he, Scheme.Hom.finrank_comp_left_of_isIso]
        exact E.finrank_eq x }

/-- Restriction retains the entire pulled-back defining ideal. -/
theorem restrictToOpen_I {T : Scheme.{u}} {t : T ⟶ S} {n : ℕ}
    (E : RelEffCartierDiv c n t) (hE : E.SupportedIn U) :
    (restrictToOpen c U E hE).I = E.I.comap (openProdMap c U t) := rfl

/-- The open inclusions commute with changes of the test scheme. -/
theorem openProdMap_naturality {T T' : Scheme.{u}} {t : T ⟶ S} {t' : T' ⟶ S}
    (f : T' ⟶ T) (hf : f ≫ t = t') :
    mapOnProdOver (U.ι ≫ c) f hf ≫ openProdMap c U t =
      openProdMap c U t' ≫ mapOnProdOver c f hf := by
  apply pullback.hom_ext
  · simp only [Category.assoc, openProdMap_fst, mapOnProdOver_fst_assoc,
      mapOnProdOver_fst]
  · simp only [Category.assoc, openProdMap_snd, openProdMap_snd_assoc,
      mapOnProdOver_snd]

/-- Full divisor ideals commute with arbitrary base change under open restriction. -/
theorem restrictToOpen_pullbackAlong {T T' : Scheme.{u}} {t : T ⟶ S} {t' : T' ⟶ S}
    {n : ℕ} (E : RelEffCartierDiv c n t) (hE : E.SupportedIn U)
    (f : T' ⟶ T) (hf : f ≫ t = t') :
    restrictToOpen c U (E.pullbackAlong f hf) (hE.pullbackAlong f hf) =
      (restrictToOpen c U E hE).pullbackAlong f hf := by
  apply RelEffCartierDiv.ext
  change (E.I.comap (mapOnProdOver c f hf)).comap (openProdMap c U t') =
    (E.I.comap (openProdMap c U t)).comap (mapOnProdOver (U.ι ≫ c) f hf)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    openProdMap_naturality]

end AlgebraicGeometry.RelEffCartierDiv
