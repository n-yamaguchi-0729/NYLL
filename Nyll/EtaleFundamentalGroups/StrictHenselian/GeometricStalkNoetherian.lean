/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkPuncture
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ChangeBase
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FreeModuleFlat
import Nyll.SchemeTheory.RingTheory.AdicCompletion.NoetherianOfQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Unramified.Finite

/-!
# Noetherianity of the actual geometric stalk of a local ring

For a Noetherian local base, the maximal ideal of the actual geometric
stalk is finitely generated. Its completion is therefore Noetherian.
The common residue-basis construction shows that this completion is flat
over the original local ring.

Each finite family of stalk coefficients is represented on one actual
affine étale neighborhood. Flatness over its section ring follows from
the unramified scalar-restriction theorem. Mapping the resulting relation
witnesses to the stalk proves that the completion is flat over the stalk.
Its local structure map is thus faithfully flat, and finite generation of
ideals descends. No Noetherianity or closedness of stalk ideals is assumed.

This proves the Noetherian ascent in Stacks, Lemma 15.46.3, for the actual
pointed-neighborhood colimit used by the specialization constructions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace EtaleFundamentalGroups.StrictHenselian

variable {R Ω : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [Field Ω] (φ : R →+* Ω) [IsLocalHom φ]

/-- The actual étale geometric stalk at a closed point of a Noetherian
local ring is Noetherian. The map to its completion is proved faithfully
flat from actual affine étale representatives. -/
theorem geometricStalk_isNoetherianRing :
    IsNoetherianRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  classical
  let s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom φ)
  let H : Type u := geometricStalk s
  let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
  have hmax : (maximalIdeal R).map (algebraMap R H) = maximalIdeal H :=
    geometricStalkStructureMap_map_maximalIdeal φ
  have hmaxfg : (maximalIdeal H).FG := by
    rw [← hmax]
    exact (maximalIdeal R).fg_of_isNoetherianRing.map (algebraMap R H)
  have : IsNoetherianRing (H ⧸ maximalIdeal H) :=
    inferInstanceAs (IsNoetherianRing (ResidueField H))
  let Hhat := AdicCompletion (maximalIdeal H) H
  have : IsNoetherianRing Hhat :=
    AdicCompletion.isNoetherianRing_of_noetherian_quotient (maximalIdeal H) hmaxfg
  have : IsLocalRing Hhat := AdicCompletion.isLocalRing_of_fg hmaxfg
  have : IsLocalHom (algebraMap H Hhat) := AdicCompletion.algebraMap_isLocalHom_of_fg hmaxfg
  have : Module.Flat R H := geometricStalkStructureMap_flat φ
  let e : AdicCompletion (maximalIdeal R) H ≃ₗ[R] Hhat := by
    change AdicCompletion (maximalIdeal R) H ≃ₗ[R] AdicCompletion (maximalIdeal H) H
    rw [← hmax]
    exact AdicCompletion.mapIdealEquiv H (maximalIdeal R) H
  have : Module.Flat R Hhat :=
    (Module.Flat.equiv_iff e).mp (AdicCompletion.flat_maximalIdeal_of_flat H)
  have : Module.Flat H Hhat := by
    apply Module.Flat.of_forall_isTrivialRelation
    intro n c y hrel
    obtain ⟨W, t, z, hz⟩ := geometricStalk_exists_representatives s c
    obtain ⟨V, v, j, hVaffine, hj⟩ := geometricStalk_exists_affine_refinement s W t
    have : IsAffine V.left := hVaffine
    let p : V.left ⟶ Spec (CommRingCat.of R) := V.hom
    have : Etale p := V.prop
    let B : Type u := Γ(V.left, ⊤)
    let β : R →+* B := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop).hom
    let γ : B →+* H := (geometricStalkGerm s V v).hom
    let cB : Fin n → B := fun i => j.left.appTop (z i)
    have hnat : j.left.appTop ≫ geometricStalkGerm s V v =
        geometricStalkGerm s W ((Scheme.pointEtaleNeighborhoods s).fiber.map j v) :=
      (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w j v
        (etaleSections (Spec (CommRingCat.of R)))
    have hnat' : j.left.appTop ≫ geometricStalkGerm s V v = geometricStalkGerm s W t :=
      hnat.trans (congrArg
        (fun t' : (Scheme.pointEtaleNeighborhoods s).fiber.obj W => geometricStalkGerm s W t') hj)
    have hc : ∀ i, γ (cB i) = c i := by
      intro i
      exact (ConcreteCategory.congr_hom hnat' (z i)).trans (hz i)
    let : Algebra R B := β.toAlgebra
    have : Algebra.Etale R B := by
      change (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Etale
      apply RingHom.Etale.stableUnderComposition
      · exact RingHom.Etale.of_bijective
          ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv).mp
            inferInstance)
      · exact HasRingHomProperty.appTop (P := @Etale) p inferInstance
    let : Algebra B H := γ.toAlgebra
    have hβγ : γ.comp β = algebraMap R H := geometricStalkGerm_comp_structure φ V v
    have : IsScalarTower R B H := IsScalarTower.of_algebraMap_eq' hβγ.symm
    have : Module.Flat B Hhat := Algebra.FormallyUnramified.flat_of_restrictScalars R B Hhat
    have hsmul (b : B) (a : Hhat) : b • a = γ b • a := by
      change algebraMap B Hhat b * a = algebraMap H Hhat (γ b) * a
      rw [IsScalarTower.algebraMap_apply B H Hhat]
      rfl
    have hrelB : ∑ i, cB i • y i = 0 := by
      calc
        (∑ i, cB i • y i) = ∑ i, γ (cB i) • y i :=
          Finset.sum_congr rfl fun i _ => hsmul (cB i) (y i)
        _ = ∑ i, c i • y i := by simp only [hc]
        _ = 0 := hrel
    obtain ⟨k, b, w, hyw, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrelB
    refine ⟨k, (fun i a => γ (b i a)), w, ?_, ?_⟩
    · intro i
      calc
        y i = ∑ a, b i a • w a := hyw i
        _ = ∑ a, γ (b i a) • w a :=
          Finset.sum_congr rfl fun a _ => hsmul (b i a) (w a)
    · intro a
      have h := congrArg γ (hb a)
      simp only [map_sum, map_mul, map_zero, hc] at h
      exact h
  have : Module.FaithfullyFlat H Hhat := Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply (isNoetherianRing_iff_ideal_fg H).mpr
  intro J
  exact Ideal.FG.of_FG_map_of_faithfullyFlat (S := Hhat)
    (J.map (algebraMap H Hhat)).fg_of_isNoetherianRing

end EtaleFundamentalGroups.StrictHenselian
