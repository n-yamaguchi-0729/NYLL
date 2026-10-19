/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafDenominators
import Nyll.SchemeTheory.Modules.Descent.GlueOfCocycle
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Extending an actual local section after twisting

The compatible numerators constructed from quasicoherent localization
are tensored with the local coordinate frames. The transition relation
is precisely what is needed for these actual tensor sections to agree
on every overlap. Sheaf gluing therefore gives a global section of
`F ⊗ 𝒪(1)ᵈ`. On the initial chart its restriction is the original
section tensored with the `d`-th power of the global coordinate section.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules Scheme.Modules.GlueOfCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- A section on one standard chart extends globally after multiplication
by a suitable power of that chart's coordinate section. The extension is
a section of the actual tensor product sheaf. -/
theorem exists_twisting_section_extension (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) F]
    (i : Fin (n + 1)) (s : Γ(F, standardOpen R n i)) :
    ∃ d : ℕ, ∃ z : Γ(F ⊗ (twistingSheaf R n).tensorPow d, ⊤),
      (F ⊗ (twistingSheaf R n).tensorPow d).presheaf.map
          (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op z =
        tensorSections s
          (((twistingSheaf R n).tensorPow d).presheaf.map
            (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op
            (tensorPowSection (twistingCoordinateSection R n i) d)) := by
  obtain ⟨d, t, ht, hcompatible⟩ := exists_compatible_coordinate_numerators R n F i s
  let G : (Proj 𝒜).Modules := F ⊗ (twistingSheaf R n).tensorPow d
  let z : ∀ j : Fin (n + 1), Γ(G, standardOpen R n j) := fun j =>
    tensorSections (t j)
      (tensorPowSection (glueFrame (twistingCocycle R n) (ULift.up j)) d)
  have hz : ∀ j k : Fin (n + 1),
      G.presheaf.map
          (homOfLE (inf_le_left : standardOpen R n j ⊓ standardOpen R n k ≤
            standardOpen R n j)).op (z j) =
        G.presheaf.map (homOfLE inf_le_right).op (z k) := by
    intro j k
    have hframe : (twistingSheaf R n).presheaf.map
        (homOfLE (inf_le_right : standardOpen R n j ⊓ standardOpen R n k ≤
          standardOpen R n k)).op (glueFrame (twistingCocycle R n) (ULift.up k)) =
      rO (inf_le_left : standardOpen R n j ⊓ standardOpen R n k ≤
        standardOpen R n j) (coordinateRatioSection R n j k) •
        (twistingSheaf R n).presheaf.map (homOfLE (inf_le_left :
          standardOpen R n j ⊓ standardOpen R n k ≤ standardOpen R n j)).op
          (glueFrame (twistingCocycle R n) (ULift.up j)) :=
      map_glueFrame_eq_smul (twistingCocycle R n) (ULift.up j) (ULift.up k)
    change (F ⊗ (twistingSheaf R n).tensorPow d).presheaf.map _
        (tensorSections (t j)
          (tensorPowSection (glueFrame (twistingCocycle R n) (ULift.up j)) d)) =
      (F ⊗ (twistingSheaf R n).tensorPow d).presheaf.map _
        (tensorSections (t k)
          (tensorPowSection (glueFrame (twistingCocycle R n) (ULift.up k)) d))
    rw [map_tensorSections, map_tensorSections, map_tensorPowSection,
      map_tensorPowSection, hframe, tensorPowSection_smul, hcompatible j k,
      tensorSections_smul_left, tensorSections_smul_right]
  obtain ⟨S, hS⟩ := (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible G
    (twistingCover R n) ⊤ (fun _ => le_top) (iSup_twistingCover R n).ge).2
      (fun j => z j.down) (fun j k => hz j.down k.down)
  have htself : t i = s := by
    have h := ht i
    rw [coordinateRatioSection_self, map_one, one_pow, one_smul] at h
    have hinj : Function.Injective
        ((F.presheaf.map (homOfLE (inf_le_left : standardOpen R n i ⊓
          standardOpen R n i ≤ standardOpen R n i)).op) :
          Γ(F, standardOpen R n i) → Γ(F, standardOpen R n i ⊓ standardOpen R n i)) := by
      let e : standardOpen R n i ⊓ standardOpen R n i ≅ standardOpen R n i :=
        eqToIso (inf_idem (standardOpen R n i))
      have he : (homOfLE (inf_le_left : standardOpen R n i ⊓ standardOpen R n i ≤
          standardOpen R n i)) = e.hom := Subsingleton.elim _ _
      rw [he]
      exact (ConcreteCategory.bijective_of_isIso (F.presheaf.map e.hom.op)).1
    exact hinj h
  refine ⟨d, S, ?_⟩
  calc
    G.presheaf.map (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op S = z i :=
      hS (ULift.up i)
    _ = tensorSections s
        (tensorPowSection (glueFrame (twistingCocycle R n) (ULift.up i)) d) :=
      congrArg (fun a : Γ(F, standardOpen R n i) => tensorSections a
        (tensorPowSection (glueFrame (twistingCocycle R n) (ULift.up i)) d)) htself
    _ = tensorSections s
        (((twistingSheaf R n).tensorPow d).presheaf.map
          (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op
          (tensorPowSection (twistingCoordinateSection R n i) d)) := by
      rw [map_tensorPowSection, twistingCoordinateSection_restrict_self]

end AlgebraicGeometry.ProjSpace
