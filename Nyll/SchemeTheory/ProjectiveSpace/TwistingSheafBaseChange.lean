/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafReconstruction
import Nyll.SchemeTheory.Modules.ProjectivePresentation.ProjectivePresentation
import Nyll.SchemeTheory.Modules.ProjectivePresentation.ProjectivePresentationBaseChange
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Coefficient base change of the actual twisting sheaf

Pull back the constructed coordinate presentation along the actual
projective-space base-change square. Its projective morphism is the
identity, by the universal property of that square. The reconstructed
coordinate frames therefore give an isomorphism with the twisting
sheaf over the new coefficient ring, preserving the original pulled
back coordinate sections.

The final comparisons also treat tensor powers and the literal scheme
pullback, as used for the projective space over a Rees algebra.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

/-- The twisting sheaf after coefficient base change, with the images
of the coordinate sections under the original pullback adjunction. -/
theorem exists_twistingSheaf_baseChange_iso :
    ∃ e : ((Scheme.Modules.pullback (map R A n)).obj (twistingSheaf R n)) ≅
        twistingSheaf A n,
      ∀ i : Fin (n + 1),
        e.hom.app ⊤
          ((((pullbackPushforwardAdjunction (map R A n)).unit.app
            (twistingSheaf R n)).app ⊤) (twistingCoordinateSection R n i)) =
          twistingCoordinateSection A n i := by
  obtain ⟨P, hσ, hmap, _⟩ :=
    ProjPresentation.exists_baseChange_of_isPullback (isPullback_map R A n)
      (twistingSheafPresentation R n)
  have hP : P.toProj = 𝟙 (Proj 𝒜A) := by
    apply (isPullback_map R A n).hom_ext
    · calc
        P.toProj ≫ map R A n = map R A n ≫ 𝟙 (Proj 𝒜R) := hmap
        _ = 𝟙 (Proj 𝒜A) ≫ map R A n :=
          (Category.comp_id (map R A n)).trans (Category.id_comp (map R A n)).symm
    · exact P.toProj_π.trans (Category.id_comp (π A n)).symm
  obtain ⟨e, he⟩ := exists_iso_twistingSheaf_of_identity_presentation A n
    ((Scheme.Modules.pullback (map R A n)).obj (twistingSheaf R n)) P hP
  refine ⟨e, ?_⟩
  intro i
  exact (congrArg (e.hom.app ⊤) (hσ i)).symm.trans (he i)

/-- The constructed coefficient-change isomorphism of twisting sheaves. -/
def twistingSheafBaseChangeIso :
    ((Scheme.Modules.pullback (map R A n)).obj (twistingSheaf R n)) ≅
      twistingSheaf A n :=
  (exists_twistingSheaf_baseChange_iso R A n).choose

/-- This comparison carries each original pulled coordinate section to
the same coordinate section over the new coefficient ring. -/
theorem twistingSheafBaseChangeIso_hom_coordinate (i : Fin (n + 1)) :
    (twistingSheafBaseChangeIso R A n).hom.app ⊤
      ((((pullbackPushforwardAdjunction (map R A n)).unit.app
        (twistingSheaf R n)).app ⊤) (twistingCoordinateSection R n i)) =
      twistingCoordinateSection A n i :=
  (exists_twistingSheaf_baseChange_iso R A n).choose_spec i

/-- Coefficient change commutes with every nonnegative twisting power. -/
def twistingPowerBaseChangeIso (d : ℕ) :
    ((Scheme.Modules.pullback (map R A n)).obj ((twistingSheaf R n).tensorPow d)) ≅
      (twistingSheaf A n).tensorPow d :=
  pullbackTensorPowIso (map R A n) (twistingSheaf R n) d ≪≫
    tensorPowMapIso (twistingSheafBaseChangeIso R A n) d

/-- On the literal scheme pullback, pulling back `𝒪(1)` along the first
projection becomes the twisting sheaf under the canonical projective
space isomorphism. -/
def twistingSheafPullbackComparison :
    ((Scheme.Modules.pullback (isPullback_map R A n).isoPullback.hom).obj
      ((Scheme.Modules.pullback
        (pullback.fst (π R n) (Spec.map (CommRingCat.ofHom (algebraMap R A))))).obj
        (twistingSheaf R n))) ≅ twistingSheaf A n :=
  (pullbackComp (isPullback_map R A n).isoPullback.hom
    (pullback.fst (π R n) (Spec.map (CommRingCat.ofHom (algebraMap R A))))).app
      (twistingSheaf R n) ≪≫
    (pullbackCongr (isPullback_map R A n).isoPullback_hom_fst).app (twistingSheaf R n) ≪≫
      twistingSheafBaseChangeIso R A n

end AlgebraicGeometry.ProjSpace
