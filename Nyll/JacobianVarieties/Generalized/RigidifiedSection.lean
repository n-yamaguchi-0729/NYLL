/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedDivisor
import Nyll.JacobianVarieties.Generalized.RigidifiedPullback
import Nyll.JacobianVarieties.Generalized.RigidifiedTensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIsoInvModuleZeroSchemeIdeal

/-!
# Sections normalized along the full modulus

A section whose restriction is one under the specified trivialization determines
an isomorphism with the canonically rigidified inverse ideal of its zero divisor.
The comparison preserves the actual section and hence the actual trivialization,
including the infinitesimal information on a nonreduced modulus.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X D : Scheme.{u}} {i : D ⟶ X}

private theorem compatible_of_normalized_sections
    (M N : RigidifiedLineBundle i)
    (s : 𝟙_ X.Modules ⟶ M.L) (t : 𝟙_ X.Modules ⟶ N.L)
    (hs : pullbackSection i s ≫ M.trivialization.hom = 𝟙 (𝟙_ D.Modules))
    (ht : pullbackSection i t ≫ N.trivialization.hom = 𝟙 (𝟙_ D.Modules))
    (e : M.L ≅ N.L) (he : s ≫ e.hom = t) :
    (Scheme.Modules.pullback i).map e.hom ≫ N.trivialization.hom =
      M.trivialization.hom := by
  have hsi : pullbackSection i s = M.trivialization.inv := by
    apply (cancel_mono M.trivialization.hom).mp
    exact hs.trans M.trivialization.inv_hom_id.symm
  have hp : pullbackSection i s ≫ (Scheme.Modules.pullback i).map e.hom =
      pullbackSection i t := by
    exact (CategoryTheory.Category.assoc (pullbackUnitIso i).inv
      ((Scheme.Modules.pullback i).map s) ((Scheme.Modules.pullback i).map e.hom)).trans
        (congrArg (fun f => (pullbackUnitIso i).inv ≫ f)
          (((Scheme.Modules.pullback i).map_comp s e.hom).symm.trans
            (congrArg (Scheme.Modules.pullback i).map he)))
  apply (cancel_epi M.trivialization.inv).mp
  calc
    M.trivialization.inv ≫ (Scheme.Modules.pullback i).map e.hom ≫
        N.trivialization.hom = pullbackSection i t ≫ N.trivialization.hom := by
          rw [← hsi, ← Category.assoc, hp]
    _ = 𝟙 (𝟙_ D.Modules) := ht
    _ = M.trivialization.inv ≫ M.trivialization.hom :=
      M.trivialization.inv_hom_id.symm

/-- A section normalized to one along the modulus recovers the actual rigidified
line bundle from its effective zero divisor. No isomorphism of rigidifications
is supplied as an assumption: the section-preserving inverse-ideal comparison
constructs it. -/
def zeroDivisorIso (M : RigidifiedLineBundle i)
    (s : 𝟙_ X.Modules ⟶ M.L)
    (hs : pullbackSection i s ≫ M.trivialization.hom = 𝟙 (𝟙_ D.Modules))
    (I : X.IdealSheafData) (hI : I.IsInvertible)
    (hzero : zeroSchemeIdeal s = I)
    (havoid : ∀ y : D, i.base y ∉ I.support) :
    Iso M (ofInvertibleIdeal i I hI havoid) := by
  subst I
  let hex := M.isInvertible.exists_iso_invModule_zeroSchemeIdeal s hI
  let e := Classical.choose hex
  have he := Classical.choose_spec hex
  exact ⟨e, compatible_of_normalized_sections M
    (ofInvertibleIdeal i (zeroSchemeIdeal s) hI havoid) s
    (zeroSchemeIdeal s).invModuleSection hs
    (ofInvertibleIdeal_section i (zeroSchemeIdeal s) hI havoid) e he⟩

/-- Tensoring sections normalized to one preserves that normalization on the
full modulus, using the canonical monoidal pullback comparison. -/
@[reassoc] theorem tensor_normalized_sections
    (M N : RigidifiedLineBundle i)
    (s : 𝟙_ X.Modules ⟶ M.L) (t : 𝟙_ X.Modules ⟶ N.L)
    (hs : pullbackSection i s ≫ M.trivialization.hom = 𝟙 (𝟙_ D.Modules))
    (ht : pullbackSection i t ≫ N.trivialization.hom = 𝟙 (𝟙_ D.Modules)) :
    pullbackSection i ((λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ t)) ≫
      (M.tensor N).trivialization.hom = 𝟙 (𝟙_ D.Modules) := by
  let F : X.Modules ⥤ D.Modules := Scheme.Modules.pullback i
  have hsm : F.map s ≫ M.trivialization.hom =
      (Scheme.Modules.pullbackTensorUnitObjIso i).hom := by
    apply (cancel_epi (Scheme.Modules.pullbackTensorUnitObjIso i).inv).mp
    rw [← pullbackUnitComparison i]
    exact hs.trans (Scheme.Modules.pullbackUnitIso i).inv_hom_id.symm
  have htm : F.map t ≫ N.trivialization.hom =
      (Scheme.Modules.pullbackTensorUnitObjIso i).hom := by
    apply (cancel_epi (Scheme.Modules.pullbackTensorUnitObjIso i).inv).mp
    rw [← pullbackUnitComparison i]
    exact ht.trans (Scheme.Modules.pullbackUnitIso i).inv_hom_id.symm
  rw [pullbackSection_def, pullbackUnitComparison]
  change Functor.LaxMonoidal.ε F ≫
      F.map ((λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ t)) ≫
      Functor.OplaxMonoidal.δ F M.L N.L ≫
      (M.trivialization.hom ⊗ₘ N.trivialization.hom) ≫
      (λ_ (𝟙_ D.Modules)).hom = 𝟙 (𝟙_ D.Modules)
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_assoc,
    tensorHom_comp_tensorHom_assoc, hsm, htm]
  change Functor.LaxMonoidal.ε F ≫ F.map (λ_ (𝟙_ X.Modules)).inv ≫
      Functor.OplaxMonoidal.δ F (𝟙_ X.Modules) (𝟙_ X.Modules) ≫
      (Functor.OplaxMonoidal.η F ⊗ₘ Functor.OplaxMonoidal.η F) ≫
      (λ_ (𝟙_ D.Modules)).hom = 𝟙 (𝟙_ D.Modules)
  rw [Functor.OplaxMonoidal.δ_comp_η_tensorHom_assoc,
    leftUnitor_naturality, CategoryTheory.Iso.inv_hom_id_assoc,
    ← Functor.map_comp_assoc, CategoryTheory.Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.Monoidal.ε_η]

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
