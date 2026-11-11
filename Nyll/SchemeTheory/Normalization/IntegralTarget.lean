/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Normalization.SourceIso

/-!
# Relative normalization across an integral target map

If the target map is integral, normalizing the original source over either
target gives canonically isomorphic schemes. Both maps are constructed by
the normalization universal property. The comparison retains the original
source and base maps and commutes with the induced maps of the source.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {A Y X : Scheme.{u}} (p : A ⟶ Y) (a : Y ⟶ X)
  [IsIntegralHom a] [QuasiCompact (p ≫ a)] [QuasiSeparated (p ≫ a)]

/-- The original factorization through the integral intermediate target
extends to the normalization over the final target. -/
def normalizationIntegralTargetMap : (p ≫ a).normalization ⟶ Y :=
  (p ≫ a).normalizationDesc p a rfl

/-- The extended map retains the original source map. -/
@[reassoc]
theorem toNormalization_normalizationIntegralTargetMap :
    (p ≫ a).toNormalization ≫ normalizationIntegralTargetMap p a = p :=
  (p ≫ a).toNormalization_normalizationDesc p a rfl

/-- The extended map is over the original final target. -/
@[reassoc]
theorem normalizationIntegralTargetMap_comp :
    normalizationIntegralTargetMap p a ≫ a = (p ≫ a).fromNormalization :=
  (p ≫ a).normalizationDesc_comp p a rfl

instance normalizationIntegralTargetMap_isIntegral :
    IsIntegralHom (normalizationIntegralTargetMap p a) :=
  inferInstanceAs (IsIntegralHom ((p ≫ a).normalizationDesc p a rfl))

variable [QuasiCompact p] [QuasiSeparated p]

/-- The comparison from normalization over the final target to normalization
over the integral intermediate target. -/
def normalizationIntegralTargetHom : (p ≫ a).normalization ⟶ p.normalization :=
  (p ≫ a).normalizationDesc p.toNormalization (p.fromNormalization ≫ a) (by
    rw [← Category.assoc, toNormalization_fromNormalization])

/-- The comparison retains the original map into the normalization. -/
@[reassoc]
theorem toNormalization_normalizationIntegralTargetHom :
    (p ≫ a).toNormalization ≫ normalizationIntegralTargetHom p a = p.toNormalization :=
  (p ≫ a).toNormalization_normalizationDesc _ _ _

/-- The comparison is over the original final target. -/
@[reassoc]
theorem normalizationIntegralTargetHom_comp_fromNormalization :
    normalizationIntegralTargetHom p a ≫ p.fromNormalization ≫ a =
      (p ≫ a).fromNormalization :=
  (p ≫ a).normalizationDesc_comp _ _ _

/-- The comparison also retains the extended intermediate-target map. -/
@[reassoc]
theorem normalizationIntegralTargetHom_fromNormalization :
    normalizationIntegralTargetHom p a ≫ p.fromNormalization =
      normalizationIntegralTargetMap p a := by
  apply normalization.hom_ext (p ≫ a) _ _ a
  · rw [← Category.assoc, toNormalization_normalizationIntegralTargetHom,
      toNormalization_fromNormalization, toNormalization_normalizationIntegralTargetMap]
  · rw [Category.assoc, normalizationIntegralTargetHom_comp_fromNormalization]
  · exact normalizationIntegralTargetMap_comp p a

/-- The reverse comparison uses the actual integral map to the intermediate target. -/
def normalizationIntegralTargetInv : p.normalization ⟶ (p ≫ a).normalization :=
  p.normalizationDesc (p ≫ a).toNormalization (normalizationIntegralTargetMap p a)
    (toNormalization_normalizationIntegralTargetMap p a).symm

/-- The reverse comparison retains the original source. -/
@[reassoc]
theorem toNormalization_normalizationIntegralTargetInv :
    p.toNormalization ≫ normalizationIntegralTargetInv p a = (p ≫ a).toNormalization :=
  p.toNormalization_normalizationDesc _ _ _

/-- The reverse comparison is over the original intermediate target. -/
@[reassoc]
theorem normalizationIntegralTargetInv_comp_map :
    normalizationIntegralTargetInv p a ≫ normalizationIntegralTargetMap p a =
      p.fromNormalization :=
  p.normalizationDesc_comp _ _ _

/-- The reverse comparison is over the original final target. -/
@[reassoc]
theorem normalizationIntegralTargetInv_fromNormalization :
    normalizationIntegralTargetInv p a ≫ (p ≫ a).fromNormalization =
      p.fromNormalization ≫ a := by
  rw [← normalizationIntegralTargetMap_comp p a, ← Category.assoc,
    normalizationIntegralTargetInv_comp_map]

/-- Relative normalization is unchanged by an integral intermediate target. -/
def normalizationIntegralTargetIso : (p ≫ a).normalization ≅ p.normalization where
  hom := normalizationIntegralTargetHom p a
  inv := normalizationIntegralTargetInv p a
  hom_inv_id := by
    apply normalization.hom_ext (p ≫ a) _ _ (p ≫ a).fromNormalization
    · rw [← Category.assoc, toNormalization_normalizationIntegralTargetHom,
        toNormalization_normalizationIntegralTargetInv, Category.comp_id]
    · rw [Category.assoc, normalizationIntegralTargetInv_fromNormalization,
        normalizationIntegralTargetHom_comp_fromNormalization]
    · exact Category.id_comp _
  inv_hom_id := by
    apply normalization.hom_ext p _ _ p.fromNormalization
    · rw [← Category.assoc, toNormalization_normalizationIntegralTargetInv,
        toNormalization_normalizationIntegralTargetHom, Category.comp_id]
    · rw [Category.assoc, normalizationIntegralTargetHom_fromNormalization,
        normalizationIntegralTargetInv_comp_map]
    · exact Category.id_comp _

/-- The isomorphism retains the original source map. -/
@[reassoc]
theorem toNormalization_normalizationIntegralTargetIso_hom :
    (p ≫ a).toNormalization ≫ (normalizationIntegralTargetIso p a).hom =
      p.toNormalization :=
  toNormalization_normalizationIntegralTargetHom p a

/-- The isomorphism retains the original final-target map. -/
@[reassoc]
theorem normalizationIntegralTargetIso_hom_fromNormalization :
    (normalizationIntegralTargetIso p a).hom ≫ p.fromNormalization ≫ a =
      (p ≫ a).fromNormalization :=
  normalizationIntegralTargetHom_comp_fromNormalization p a

/-- Changing the integral target commutes with the actual source endomorphism. -/
@[reassoc]
theorem normalizationIntegralTargetIso_hom_sourceMap
    (σ : A ⟶ A) (hσ : σ ≫ p = p) :
    normalizationSourceMap (p ≫ a) (p ≫ a) σ
        (by rw [← Category.assoc, hσ]) ≫ (normalizationIntegralTargetIso p a).hom =
      (normalizationIntegralTargetIso p a).hom ≫ normalizationSourceMap p p σ hσ := by
  apply normalization.hom_ext (p ≫ a) _ _ (p.fromNormalization ≫ a)
  · rw [← Category.assoc, toNormalization_normalizationSourceMap,
      Category.assoc, toNormalization_normalizationIntegralTargetIso_hom,
      ← Category.assoc, toNormalization_normalizationIntegralTargetIso_hom,
      toNormalization_normalizationSourceMap]
  · rw [Category.assoc, normalizationIntegralTargetIso_hom_fromNormalization,
      normalizationSourceMap_fromNormalization]
  · rw [Category.assoc, ← Category.assoc (normalizationSourceMap p p σ hσ),
      normalizationSourceMap_fromNormalization,
      normalizationIntegralTargetIso_hom_fromNormalization]

end AlgebraicGeometry.Scheme.Hom
