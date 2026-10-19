/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.SchemeTheory.Etale.HenselianLocalGeometricSection
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Limits

/-!
# Canonical maps from the actual geometric stalk to étale neighborhoods

Every pointed étale neighborhood receives a unique map from the spectrum
of the constructed geometric-stalk ring, compatible with its structure
map and its specified geometric point. This includes nonaffine neighborhoods.
The proof applies the existing strictly local étale-section theorem to
the actual native base change. Uniqueness supplies naturality, while the
affine case agrees with the literal germ homomorphism.

These maps define the comparison cocone needed in degree-zero continuity
(Stacks Project, Theorem 59.53.1). No sheaf-continuity assertion is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω]
  (φ : R →+* Ω)

/-- The actual evaluation point lies over the given geometric point. -/
theorem geometricStalkEvaluation_structure :
    Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))) ≫
      Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)) =
        Spec.map (CommRingCat.ofHom φ) := by
  let α : CommRingCat.of R ⟶ geometricStalk (Spec.map (CommRingCat.ofHom φ)) :=
    CommRingCat.ofHom (geometricStalkStructureMap φ)
  let β : geometricStalk (Spec.map (CommRingCat.ofHom φ)) ⟶ CommRingCat.of Ω :=
    geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))
  have h : α ≫ β = CommRingCat.ofHom φ :=
    CommRingCat.hom_ext (geometricStalkStructureMap_evaluation φ)
  exact (Spec.map_comp α β).symm.trans (congrArg Spec.map h)

/-- The geometric evaluation is a closed field point of the actual
strictly local spectrum. -/
theorem geometricStalkEvaluation_closedPoint :
    Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))) default =
      IsLocalRing.closedPoint (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  let x : PrimeSpectrum Ω := (default : Spec (CommRingCat.of Ω))
  exact (congrArg (PrimeSpectrum.comap
      (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))).hom)
      (Subsingleton.elim x (IsLocalRing.closedPoint Ω))).trans
    (IsLocalRing.comap_closedPoint
      (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))).hom)

variable [IsSepClosed Ω]

/-- Every pointed étale neighborhood receives a unique map from the
constructed strictly local spectrum, with both literal compatibilities. -/
theorem existsUnique_geometricStalkNeighborhoodMap
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    ∃! l : Spec (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⟶ U.left,
      l ≫ U.hom = Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)) ∧
      Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))) ≫ l = v.left := by
  let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let h : Spec H ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let j : Spec (CommRingCat.of Ω) ⟶ Spec H :=
    Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ)))
  let uhom : U.left ⟶ Spec (CommRingCat.of R) := U.hom
  let v₀ : Spec (CommRingCat.of Ω) ⟶ U.left := v.left
  have hv : v₀ ≫ uhom = Spec.map (CommRingCat.ofHom φ) := v.w
  let p : pullback uhom h ⟶ Spec H := pullback.snd uhom h
  let s : Spec (CommRingCat.of Ω) ⟶ pullback uhom h :=
    pullback.lift v₀ j (hv.trans (geometricStalkEvaluation_structure φ).symm)
  obtain ⟨σ, hσ, huniq⟩ := @Etale.existsUnique_section_of_closedFieldPoint
    H inferInstance (geometricStalk_henselianLocalRing (Spec.map (CommRingCat.ofHom φ)))
    (geometricStalk_residueField_isSepClosed (Spec.map (CommRingCat.ofHom φ)))
    _ p (inferInstanceAs (Etale (pullback.snd uhom h))) Ω inferInstance
    j (geometricStalkEvaluation_closedPoint φ) s (pullback.lift_snd _ _ _)
  have hσ₁ : σ ≫ pullback.snd uhom h = 𝟙 _ := hσ.1
  have hσ₂ : j ≫ σ = s := hσ.2
  let l : Spec H ⟶ U.left := σ ≫ pullback.fst uhom h
  have hl : l ≫ uhom = h := by
    change (σ ≫ pullback.fst uhom h) ≫ uhom = h
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ₁,
      Category.id_comp]
  have hjl : j ≫ l = v₀ := by
    change j ≫ (σ ≫ pullback.fst uhom h) = v₀
    rw [← Category.assoc, hσ₂]
    exact pullback.lift_fst _ _ _
  refine ⟨l, ⟨hl, hjl⟩, ?_⟩
  intro t ht
  have ht₁ : t ≫ uhom = h := ht.1
  have ht₂ : j ≫ t = v₀ := ht.2
  let τ : Spec H ⟶ pullback uhom h :=
    pullback.lift t (𝟙 (Spec H)) (ht₁.trans (Category.id_comp h).symm)
  have hτ : τ ≫ p = 𝟙 (Spec H) := pullback.lift_snd _ _ _
  have hjτ : j ≫ τ = s := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ht₂, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, pullback.lift_snd]
  have hτσ : τ = σ := huniq τ ⟨hτ, hjτ⟩
  exact (pullback.lift_fst t (𝟙 (Spec H)) _).symm.trans
    (congrArg (fun a => a ≫ pullback.fst uhom h) hτσ)

/-- The unique actual map from the strictly local spectrum to a pointed
étale neighborhood, without an affineness hypothesis on the neighborhood. -/
def geometricStalkNeighborhoodMap
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    Spec (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⟶ U.left :=
  (existsUnique_geometricStalkNeighborhoodMap φ U v).choose

theorem geometricStalkNeighborhoodMap_comp
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    geometricStalkNeighborhoodMap φ U v ≫ U.hom =
      Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)) :=
  (existsUnique_geometricStalkNeighborhoodMap φ U v).choose_spec.1.1

theorem geometricStalkNeighborhoodMap_evaluation
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))) ≫
      geometricStalkNeighborhoodMap φ U v = v.left :=
  (existsUnique_geometricStalkNeighborhoodMap φ U v).choose_spec.1.2

/-- Uniqueness is with respect to the actual base and field maps. -/
theorem geometricStalkNeighborhoodMap_eq_of_properties
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U)
    (l : Spec (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⟶ U.left)
    (hl : l ≫ U.hom = Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)))
    (hj : Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))) ≫ l =
      v.left) : l = geometricStalkNeighborhoodMap φ U v :=
  (existsUnique_geometricStalkNeighborhoodMap φ U v).choose_spec.2 l ⟨hl, hj⟩

/-- Canonical maps respect every map of pointed étale neighborhoods. -/
theorem geometricStalkNeighborhoodMap_naturality
    {U V : (Spec (CommRingCat.of R)).Etale} (a : U ⟶ V)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    geometricStalkNeighborhoodMap φ U v ≫ a.left = geometricStalkNeighborhoodMap φ V
      ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map a v) := by
  apply geometricStalkNeighborhoodMap_eq_of_properties
  · have ha : a.left ≫ V.hom = U.hom := a.w
    exact (Category.assoc (geometricStalkNeighborhoodMap φ U v) a.left V.hom).trans
      ((congrArg (fun t => geometricStalkNeighborhoodMap φ U v ≫ t) ha).trans
        (geometricStalkNeighborhoodMap_comp φ U v))
  · exact (Category.assoc
      (Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))))
      (geometricStalkNeighborhoodMap φ U v) a.left).symm.trans
      (congrArg (fun t => t ≫ a.left) (geometricStalkNeighborhoodMap_evaluation φ U v))

/-- On an affine neighborhood the canonical map is precisely the spectrum
of its actual germ homomorphism, followed by the canonical affine isomorphism. -/
theorem geometricStalkNeighborhoodMap_eq_germ
    (U : (Spec (CommRingCat.of R)).Etale) [IsAffine U.left]
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    geometricStalkNeighborhoodMap φ U v =
      Spec.map (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) U v) ≫
        U.left.isoSpec.inv := by
  let γ : Γ(U.left, ⊤) ⟶ geometricStalk (Spec.map (CommRingCat.ofHom φ)) :=
    geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) U v
  let β : geometricStalk (Spec.map (CommRingCat.ofHom φ)) ⟶ CommRingCat.of Ω :=
    geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))
  let uhom : U.left ⟶ Spec (CommRingCat.of R) := U.hom
  let v₀ : Spec (CommRingCat.of Ω) ⟶ U.left := v.left
  symm
  apply geometricStalkNeighborhoodMap_eq_of_properties
  · have hbase : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ uhom.appTop) ≫ γ =
        CommRingCat.ofHom (geometricStalkStructureMap φ) := by
      apply CommRingCat.hom_ext
      exact geometricStalkGerm_comp_structure φ U v
    change (Spec.map γ ≫ U.left.isoSpec.inv) ≫ uhom =
      Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality uhom,
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, ← Spec.map_comp]
    exact congrArg Spec.map hbase
  · have hγ : γ ≫ β = v₀.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom :=
      geometricStalkGerm_evaluation (Spec.map (CommRingCat.ofHom φ)) U v
    change Spec.map β ≫ (Spec.map γ ≫ U.left.isoSpec.inv) = v₀
    rw [← Spec.map_comp_assoc, hγ, Spec.map_comp,
      Category.assoc, Scheme.isoSpec_inv_naturality v₀, Scheme.isoSpec_Spec_inv,
      ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]

end EtaleCohomology
