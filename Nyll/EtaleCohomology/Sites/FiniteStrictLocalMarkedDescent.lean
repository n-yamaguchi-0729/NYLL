/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.GeometricStalkSectionDescent
import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.SchemeTheory.Etale.FiniteStrictLocalSchemeGeometricSection
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Spreading finite sections with prescribed geometric lifts

The strict-local decomposition of a finite scheme provides a section with
specified values at every geometric point of the closed fiber. Actual scheme
section descent spreads this section to an affine pointed étale neighborhood.
The retained equality at the strict-local limit, evaluated in the geometric
field, preserves every specified field-valued map.

This is the simultaneous neighborhood construction in Stacks Project 59.55.2.
The étale target need not be affine or surjective over the original finite scheme.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

/-- A section with prescribed values at all points of a finite geometric
fiber exists after an actual affine pointed étale refinement of an affine base. -/
theorem exists_affine_pointed_etale_lift_prescribed_of_isFinite
    {R Ω : Type u} [CommRing R] [Field Ω] [IsAlgClosed Ω]
    {Y W : Scheme.{u}} (q : Y ⟶ Spec (.of R)) [IsFinite q]
    (φ : R →+* Ω) (p : W ⟶ Y) [Etale p]
    (w : {s : Spec (.of Ω) ⟶ Y // s ≫ q = Spec.map (CommRingCat.ofHom φ)} →
      (Spec (.of Ω) ⟶ W)) (hw : ∀ s, w s ≫ p = s.val) :
    ∃ (V : (Spec (.of R)).Etale)
      (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V),
      IsAffine V.left ∧ ∃ b : pullback V.hom q ⟶ W,
        b ≫ p = pullback.snd V.hom q ∧
        ∀ s, (etalePushforwardGeometricLift q (Spec.map (CommRingCat.ofHom φ)) s V v).left
          ≫ b = w s := by
  let t : Spec (.of Ω) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom φ)
  let H : Type u := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let α : CommRingCat.of R ⟶ CommRingCat.of H :=
    CommRingCat.ofHom (geometricStalkStructureMap φ)
  let h : Spec (.of H) ⟶ Spec (.of R) := Spec.map α
  let ε : CommRingCat.of H ⟶ CommRingCat.of Ω :=
    geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))
  let e : Spec (.of Ω) ⟶ Spec (.of H) := Spec.map ε
  have he : e ≫ h = t := by
    have hαε : α ≫ ε = CommRingCat.ofHom φ := by
      apply CommRingCat.hom_ext
      exact geometricStalkStructureMap_evaluation φ
    exact (Spec.map_comp α ε).symm.trans (congrArg Spec.map hαε)
  let Q : Scheme.{u} := pullback h q
  let qH : Q ⟶ Spec (.of H) := pullback.fst h q
  let qY : Q ⟶ Y := pullback.snd h q
  have : IsFinite qH := inferInstanceAs (IsFinite (pullback.fst h q))
  let I := {s : Spec (.of Ω) ⟶ Y // s ≫ q = t}
  let J := {z : Spec (.of Ω) ⟶ Q // z ≫ qH = e}
  let f : J → I := fun z => ⟨z.val ≫ qY, by
    calc
      (z.val ≫ qY) ≫ q = z.val ≫ (qY ≫ q) := Category.assoc _ _ _
      _ = z.val ≫ (qH ≫ h) := congrArg (fun a => z.val ≫ a) pullback.condition.symm
      _ = (z.val ≫ qH) ≫ h := (Category.assoc _ _ _).symm
      _ = e ≫ h := congrArg (fun a => a ≫ h) z.property
      _ = t := he⟩
  let a (z : J) : Spec (.of Ω) ⟶ pullback p qY :=
    pullback.lift (w (f z)) z.val (hw (f z))
  have : HenselianLocalRing H :=
    geometricStalk_henselianLocalRing (Spec.map (CommRingCat.ofHom φ))
  have : IsSepClosed (IsLocalRing.ResidueField H) :=
    geometricStalk_residueField_isSepClosed (Spec.map (CommRingCat.ofHom φ))
  have : IsLocalHom ε.hom :=
    geometricStalkEvaluation_isLocalHom (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨σ, hσ, hσmarked⟩ :=
    Etale.exists_section_prescribed_of_isFinite_over_strictlyHenselian
      H qH ε.hom (pullback.snd p qY) a (fun _ => pullback.lift_snd _ _ _)
  let sH : Q ⟶ W := σ ≫ pullback.fst p qY
  have hsH : sH ≫ p = qY := by
    change (σ ≫ pullback.fst p qY) ≫ p = qY
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  let j (s : I) : Spec (.of Ω) ⟶ Q :=
    pullback.lift e s.val (he.trans s.property.symm)
  have hj (s : I) : j s ≫ sH = w s := by
    let z : J := ⟨j s, pullback.lift_fst _ _ _⟩
    have hf : f z = s := Subtype.ext (pullback.lift_snd _ _ _)
    calc
      j s ≫ sH = (z.val ≫ σ) ≫ pullback.fst p qY := (Category.assoc _ _ _).symm
      _ = a z ≫ pullback.fst p qY := congrArg (fun b => b ≫ _) (hσmarked z)
      _ = w (f z) := pullback.lift_fst _ _ _
      _ = w s := congrArg w hf
  obtain ⟨V, v, hV, b, m, hbp, hmb, hmY, hmH⟩ :=
    geometricStalk_exists_affine_section_stage φ q p sH hsH
  have : IsAffine V.left := hV
  let v₀ : Spec (.of Ω) ⟶ V.left := v.left
  let γ : Γ(V.left, ⊤) ⟶ CommRingCat.of H :=
    geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) V v
  have hγ : γ ≫ ε = v₀.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom :=
    geometricStalkGerm_evaluation t V v
  have hev : e ≫ Spec.map γ ≫ V.left.isoSpec.inv = v₀ := by
    change Spec.map ε ≫ Spec.map γ ≫ V.left.isoSpec.inv = v₀
    rw [← Spec.map_comp_assoc, hγ, Spec.map_comp, SpecMap_ΓSpecIso_hom]
    exact (congrArg (fun z => z ≫ V.left.isoSpec.inv)
      (Scheme.toSpecΓ_naturality v₀).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => v₀ ≫ z) V.left.isoSpec.hom_inv_id).trans
          (Category.comp_id _)))
  refine ⟨V, v, hV, b, hbp, ?_⟩
  intro s
  let n : Spec (.of Ω) ⟶ pullback V.hom q :=
    (etalePushforwardGeometricLift q t s V v).left
  have hn : j s ≫ m = n := by
    apply pullback.hom_ext
    · calc
        (j s ≫ m) ≫ pullback.fst V.hom q =
            j s ≫ (qH ≫ Spec.map γ ≫ V.left.isoSpec.inv) := by
          rw [Category.assoc, hmH]
        _ = (j s ≫ qH) ≫ Spec.map γ ≫ V.left.isoSpec.inv :=
          (Category.assoc _ _ _).symm
        _ = e ≫ Spec.map γ ≫ V.left.isoSpec.inv := by rw [pullback.lift_fst]
        _ = v₀ := hev
        _ = n ≫ pullback.fst V.hom q := (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, hmY, pullback.lift_snd]
      exact (pullback.lift_snd _ _ _).symm
  calc
    n ≫ b = (j s ≫ m) ≫ b := congrArg (fun z => z ≫ b) hn.symm
    _ = j s ≫ (m ≫ b) := Category.assoc _ _ _
    _ = j s ≫ sH := congrArg (fun z => j s ≫ z) hmb
    _ = w s := hj s

/-- The prescribed finite-fiber lift construction is invariant under affine
coordinates on the base. The target étale scheme is arbitrary. -/
theorem exists_pointed_etale_lift_prescribed_of_isFinite_of_isAffine
    {X Y W : Scheme.{u}} [IsAffine X] (q : Y ⟶ X) [IsFinite q]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (p : W ⟶ Y) [Etale p]
    (w : {s : Spec (.of Ω) ⟶ Y // s ≫ q = t} → (Spec (.of Ω) ⟶ W))
    (hw : ∀ s, w s ≫ p = s.val) :
    ∃ (V : X.Etale) (v : (Scheme.pointSmallEtale t).fiber.obj V),
      IsAffine V.left ∧ ∃ b : pullback V.hom q ⟶ W,
        b ≫ p = pullback.snd V.hom q ∧
        ∀ s, (etalePushforwardGeometricLift q t s V v).left ≫ b = w s := by
  let A : CommRingCat.{u} := Γ(X, ⊤)
  let q₀ : Y ⟶ Spec A := q ≫ X.isoSpec.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ X.isoSpec.hom)
  let I := {s : Spec (.of Ω) ⟶ Y // s ≫ q = t}
  let J := {s : Spec (.of Ω) ⟶ Y // s ≫ q₀ = Spec.map φ}
  let f : J → I := fun s => ⟨s.val, by
    apply (cancel_mono X.isoSpec.hom).mp
    exact (Category.assoc _ _ _).trans (s.property.trans hφ)⟩
  let g : I → J := fun s => ⟨s.val, by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ X.isoSpec.hom) s.property).trans hφ.symm)⟩
  obtain ⟨V₀, v₀, hV, b₀, hb₀, hbmarked⟩ :=
    exists_affine_pointed_etale_lift_prescribed_of_isFinite q₀ φ.hom p
      (fun s => w (f s)) (fun s => hw (f s))
  let a : V₀.left ⟶ Spec A := V₀.hom
  let vleft : Spec (.of Ω) ⟶ V₀.left := v₀.left
  have hvleft : vleft ≫ a = Spec.map φ := v₀.w
  let aX : V₀.left ⟶ X := a ≫ X.isoSpec.inv
  let V : X.Etale := Scheme.Etale.mk aX
  let v : (Scheme.pointSmallEtale t).fiber.obj V := Over.homMk vleft (by
    change vleft ≫ (a ≫ X.isoSpec.inv) = t
    rw [← Category.assoc, hvleft, hφ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id])
  let m : pullback aX q ⟶ pullback a q₀ :=
    pullback.map aX q a q₀ (𝟙 V₀.left) (𝟙 Y) X.isoSpec.hom
      (by
        change (a ≫ X.isoSpec.inv) ≫ X.isoSpec.hom = (𝟙 _) ≫ a
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp])
      (Category.id_comp _).symm
  have hmY : m ≫ pullback.snd a q₀ = pullback.snd aX q := by
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hmV : m ≫ pullback.fst a q₀ = pullback.fst aX q := by
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  refine ⟨V, v, hV, m ≫ b₀, ?_, ?_⟩
  · change (m ≫ b₀) ≫ p = pullback.snd aX q
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => m ≫ z) hb₀).trans hmY)
  · intro s
    let n : Spec (.of Ω) ⟶ pullback aX q :=
      (etalePushforwardGeometricLift q t s V v).left
    let n₀ : Spec (.of Ω) ⟶ pullback a q₀ :=
      (etalePushforwardGeometricLift q₀ (Spec.map φ) (g s) V₀ v₀).left
    have hn : n ≫ m = n₀ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hmV]
        exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
      · rw [Category.assoc, hmY]
        exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
    have hfg : f (g s) = s := Subtype.ext rfl
    calc
      n ≫ (m ≫ b₀) = (n ≫ m) ≫ b₀ := (Category.assoc _ _ _).symm
      _ = n₀ ≫ b₀ := congrArg (fun z => z ≫ b₀) hn
      _ = w (f (g s)) := hbmarked (g s)
      _ = w s := congrArg w hfg

end EtaleCohomology
