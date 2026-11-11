/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.CanonicalFiniteExtensionUnique
import Nyll.SchemeTheory.RingTheory.RegularLocal.FlatLocalDepth
import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra

/-!
# Recovery over a larger open carrying a finite-etale extension

A specified finite-etale extension to a larger open agrees uniquely with
the restriction of the canonical extension. Its own boundary depth is
derived from the original base depth by its flat local stalk maps. The
compatibility equation retains the given identification over the original
open, rather than merely asserting an unspecified isomorphism.
-/

noncomputable section

universe u

open CategoryTheory
open AlgebraicCurves.Foundations.Algebra.Proofs.Module_depth_quotSMulTop_succ_eq
open Ws14Port.IsLocalRing.IsCohenMacaulayOfDim

namespace EtaleFundamentalGroups.FiniteBoundaryExtension

open AlgebraicGeometry

/-- Any specified finite-etale enlargement agrees uniquely with the
canonical extension on the larger open. The comparison respects the
original specified identification over `U`. -/
theorem existsUnique_iso_restrict_of_etale_enlargement
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens)
    {V : Scheme.{u}} (π : V ⟶ U.toScheme) [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (W : X.Opens) (hUW : U ≤ W) {V' : Scheme.{u}}
    (π' : V' ⟶ W.toScheme) [IsFinite π'] [Etale π']
    (e : ((π' ≫ W.ι) ⁻¹ᵁ U).toScheme ≅ V)
    (he : e.hom ≫ π = (π' ≫ W.ι) ∣_ U) :
    ∃! a : (toBase X U π ⁻¹ᵁ W).toScheme ≅ V',
      a.hom ≫ π' = toBase X U π ∣_ W ∧
      (scheme X U π).homOfLE ((toBase X U π).preimage_mono hUW) ≫ a.hom =
        (openIso X U π).hom ≫ e.inv ≫ ((π' ≫ W.ι) ⁻¹ᵁ U).ι := by
  let S : Scheme.{u} := scheme X U π
  let F : S ⟶ X := toBase X U π
  let T : S.Opens := F ⁻¹ᵁ U
  let Z : S.Opens := F ⁻¹ᵁ W
  let F' : Z.toScheme ⟶ W.toScheme := F ∣_ W
  let g : V' ⟶ X := π' ≫ W.ι
  let T' : V'.Opens := g ⁻¹ᵁ U
  let j : T.toScheme ⟶ Z.toScheme := S.homOfLE (F.preimage_mono hUW)
  let o : T.toScheme ≅ V := openIso X U π
  let r : T.toScheme ⟶ V' := o.hom ≫ e.inv ≫ T'.ι
  have : IsFinite F := isFinite_toBase X U π hdepth
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian F
  have : IsLocallyNoetherian V' := LocallyOfFiniteType.isLocallyNoetherian π'
  have : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (S.homOfLE (F.preimage_mono hUW)))
  have : Flat g := inferInstanceAs (Flat (π' ≫ W.ι))
  have hj : j ≫ Z.ι = T.ι := S.homOfLE_ι (F.preimage_mono hUW)
  have hjrange : j.opensRange = Z.ι ⁻¹ᵁ T :=
    Scheme.opensRange_homOfLE (F.preimage_mono hUW)
  have hZ : ∀ z : Z.toScheme, z ∉ j.opensRange →
      (2 : ℕ∞) ≤ Module.depth (Z.toScheme.presheaf.stalk z)
        (Z.toScheme.presheaf.stalk z) := by
    intro z hz
    have hzU : F (Z.ι z) ∉ U := fun hzU => hz (hjrange.ge hzU)
    exact (two_le_depth_boundary X U π hdepth (Z.ι z) hzU).trans
      (Module.depth_le_depth_of_ringEquiv
        (asIso (Z.ι.stalkMap z)).commRingCatIsoToRingEquiv)
  have hV' : ∀ z : V', z ∉ T' →
      (2 : ℕ∞) ≤ Module.depth (V'.presheaf.stalk z) (V'.presheaf.stalk z) := by
    intro z hz
    exact (hdepth (g z) hz).trans
      (SchemeTheory.depth_le_depth_of_flat_localHom (g.stalkMap z).hom
        (Flat.stalkMap g z))
  have hei : e.inv ≫ (g ∣_ U) = π := by
    rw [← he, Iso.inv_hom_id_assoc]
  have ho : o.hom ≫ π = F ∣_ U := openIso_hom_toBase X U π
  have hrX : r ≫ g = T.ι ≫ F := by
    calc
      r ≫ g = (o.hom ≫ e.inv) ≫ (T'.ι ≫ g) := by
        simp only [r, Category.assoc]
      _ = (o.hom ≫ e.inv) ≫ ((g ∣_ U) ≫ U.ι) :=
        congrArg (fun k : T'.toScheme ⟶ X => (o.hom ≫ e.inv) ≫ k)
          (morphismRestrict_ι g U).symm
      _ = o.hom ≫ (π ≫ U.ι) := by
        rw [Category.assoc, ← Category.assoc e.inv, hei]
      _ = (F ∣_ U) ≫ U.ι := by rw [← Category.assoc, ho]
      _ = T.ι ≫ F := morphismRestrict_ι F U
  have hrW : r ≫ π' = j ≫ F' := by
    apply (cancel_mono W.ι).mp
    calc
      (r ≫ π') ≫ W.ι = r ≫ g := Category.assoc _ _ _
      _ = T.ι ≫ F := hrX
      _ = (j ≫ Z.ι) ≫ F := congrArg (fun k : T.toScheme ⟶ S => k ≫ F) hj.symm
      _ = j ≫ (Z.ι ≫ F) := Category.assoc _ _ _
      _ = j ≫ (F' ≫ W.ι) :=
        congrArg (fun k : Z.toScheme ⟶ X => j ≫ k) (morphismRestrict_ι F W).symm
      _ = (j ≫ F') ≫ W.ι := (Category.assoc _ _ _).symm
  let eT : j.opensRange.toScheme ≅ T'.toScheme :=
    j.isoOpensRange.symm ≪≫ o ≪≫ e.symm
  have heT : eT.hom ≫ T'.ι = j.isoOpensRange.inv ≫ r := by
    change ((j.isoOpensRange.inv ≫ o.hom) ≫ e.inv) ≫ T'.ι =
      j.isoOpensRange.inv ≫ (o.hom ≫ e.inv ≫ T'.ι)
    simp only [Category.assoc]
  have heTW : (eT.hom ≫ T'.ι) ≫ π' = j.opensRange.ι ≫ F' := by
    calc
      (eT.hom ≫ T'.ι) ≫ π' = (j.isoOpensRange.inv ≫ r) ≫ π' :=
        congrArg (fun k : j.opensRange.toScheme ⟶ V' => k ≫ π') heT
      _ = j.isoOpensRange.inv ≫ (j ≫ F') :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k : T.toScheme ⟶ W.toScheme => j.isoOpensRange.inv ≫ k) hrW)
      _ = j.opensRange.ι ≫ F' := (Category.assoc _ _ _).symm.trans
        (congrArg (fun k : j.opensRange.toScheme ⟶ Z.toScheme => k ≫ F')
          j.isoOpensRange_inv_comp)
  have hspec (a : Z.toScheme ≅ V') :
      j.opensRange.ι ≫ a.hom = eT.hom ≫ T'.ι ↔ j ≫ a.hom = r := by
    have hl : j.isoOpensRange.hom ≫ (j.opensRange.ι ≫ a.hom) = j ≫ a.hom :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun k : T.toScheme ⟶ Z.toScheme => k ≫ a.hom)
          j.isoOpensRange_hom_ι)
    have hr : j.isoOpensRange.hom ≫ (eT.hom ≫ T'.ι) = r :=
      (congrArg (fun k : j.opensRange.toScheme ⟶ V' => j.isoOpensRange.hom ≫ k) heT).trans
        (Iso.hom_inv_id_assoc j.isoOpensRange r)
    constructor
    · intro ha
      exact hl.symm.trans ((congrArg
        (fun k : j.opensRange.toScheme ⟶ V' => j.isoOpensRange.hom ≫ k) ha).trans hr)
    · intro ha
      exact (cancel_epi j.isoOpensRange.hom).mp (hl.trans (ha.trans hr.symm))
  obtain ⟨a, ha, huniq⟩ :=
    Scheme.DirectImageAlgebra.existsUnique_iso_of_boundary_two_le_depth
      F' π' j.opensRange T' hZ hV' eT heTW
  refine ⟨a, ⟨ha.1, (hspec a).mp ha.2⟩, ?_⟩
  intro c hc
  exact huniq c ⟨hc.1, (hspec c).mpr hc.2⟩

end EtaleFundamentalGroups.FiniteBoundaryExtension
