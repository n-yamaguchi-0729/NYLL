/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationStalkLocalization
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationBaseChange
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The same normalization point over the actual stalk

The canonical stalk pullback of normalization preserves a specified point
and all its fixing source endomorphisms. The point is transported through
the actual normalization comparison. Injectivity comes from the original
stalk map, so there is no choice of an independent local orbit.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u

variable {T X : Scheme.{u}} (f : T ⟶ X) [QuasiCompact f] [QuasiSeparated f] (x : X)

local notation "b" => X.fromSpecStalk x
local notation "fR" => pullback.snd f b

private local instance normalizationStalkComparisonIso :
    IsIso (f.normalizationPullback b) := isIso_normalizationPullback_fromSpecStalk f x

/-- The original map from the normalization over the actual stalk. -/
def normalizationStalkMap : (fR).normalization ⟶ f.normalization :=
  f.normalizationPullback b ≫ pullback.fst f.fromNormalization b

/-- The map embeds the local normalization into the original one. -/
instance normalizationStalkMap_isPreimmersion : IsPreimmersion (normalizationStalkMap f x) :=
  inferInstanceAs (IsPreimmersion
    (f.normalizationPullback b ≫ pullback.fst f.fromNormalization b))

/-- The original source endomorphism commutes with the actual stalk map. -/
@[reassoc]
theorem normalizationStalkMap_endomorphism
    (σ : T ⟶ T) (hσ : σ ≫ f = f) :
    normalizationEndomorphism fR (pullbackEndomorphism f b σ hσ)
        (pullbackEndomorphism_snd f b σ hσ) ≫ normalizationStalkMap f x =
      normalizationStalkMap f x ≫ normalizationEndomorphism f σ hσ := by
  rw [normalizationStalkMap, ← Category.assoc, normalizationPullback_endomorphism,
    Category.assoc, pullbackEndomorphism_fst, Category.assoc]

/-- A specified original normalization point over x has a stalk point over
the closed point, with exactly the same fixing source endomorphisms. -/
theorem exists_normalizationStalkPoint
    (z : f.normalization) (hz : f.fromNormalization z = x) :
    ∃ q : (fR).normalization,
      normalizationStalkMap f x q = z ∧
      (fR).fromNormalization q = IsLocalRing.closedPoint (X.presheaf.stalk x) ∧
      ∀ (σ : T ⟶ T) (hσ : σ ≫ f = f),
        normalizationEndomorphism fR (pullbackEndomorphism f b σ hσ)
            (pullbackEndomorphism_snd f b σ hσ) q = q ↔
          normalizationEndomorphism f σ hσ z = z := by
  obtain ⟨t, htz, htx⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f.fromNormalization) (g := b) z
    (IsLocalRing.closedPoint (X.presheaf.stalk x))
    (hz.trans Scheme.fromSpecStalk_closedPoint.symm)
  let q := inv (f.normalizationPullback b) t
  have hqt : f.normalizationPullback b q = t := by
    exact congrArg (fun h : pullback f.fromNormalization b ⟶
        pullback f.fromNormalization b => h t)
      (IsIso.inv_hom_id (f.normalizationPullback b))
  have hqz : normalizationStalkMap f x q = z := by
    change pullback.fst f.fromNormalization b (f.normalizationPullback b q) = z
    exact (congrArg (pullback.fst f.fromNormalization b) hqt).trans htz
  have hqx : (fR).fromNormalization q = IsLocalRing.closedPoint (X.presheaf.stalk x) := by
    have he := congrArg (fun h : (fR).normalization ⟶ Spec (X.presheaf.stalk x) => h q)
      (Scheme.Hom.normalizationPullback_snd f b)
    exact he.symm.trans ((congrArg (pullback.snd f.fromNormalization b) hqt).trans htx)
  refine ⟨q, hqz, hqx, ?_⟩
  intro σ hσ
  have he := congrArg (fun h : (fR).normalization ⟶ f.normalization => h q)
    (normalizationStalkMap_endomorphism f x σ hσ)
  change normalizationStalkMap f x
      (normalizationEndomorphism fR (pullbackEndomorphism f b σ hσ)
        (pullbackEndomorphism_snd f b σ hσ) q) =
    normalizationEndomorphism f σ hσ (normalizationStalkMap f x q) at he
  rw [hqz] at he
  constructor
  · intro h
    exact he.symm.trans ((congrArg (normalizationStalkMap f x) h).trans hqz)
  · intro h
    apply (normalizationStalkMap f x).isEmbedding.injective
    exact he.trans (h.trans hqz.symm)

end EtaleFundamentalGroups.Inertia
