/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PointwiseFlatPurity
import Nyll.SchemeTheory.Morphisms.OpenFlatLocus
import Nyll.SchemeTheory.RingTheory.RegularLocal.ModuleDepthBound
import Nyll.SchemeTheory.RingTheory.RegularLocal.ModuleDepthRegularQuotient
import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra

/-!
# Flatness detects etaleness across a depth-two source boundary

Pointwise flat purity applies because every codimension-one source point
is in the original etale open. Both the local neighborhoods and their
maps are those of the original morphism.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicCurves.Foundations.Algebra.Proofs.Module_depth_quotSMulTop_succ_eq
open Ws14Port.IsLocalRing.IsCohenMacaulayOfDim

namespace AlgebraicGeometry

universe u

/-- An etale open neighborhood makes the original stalk map formally
unramified, after cancelling the actual open-immersion stalk isomorphism. -/
theorem formallyUnramified_stalkMap_of_mem_etale_open
    {X Y : Scheme.{u}} (f : X ⟶ Y) (T : X.Opens) [Etale (T.ι ≫ f)]
    {x : X} (hx : x ∈ T) : (f.stalkMap x).hom.FormallyUnramified := by
  let t : T.toScheme := ⟨x, hx⟩
  have h := FormallyUnramified.stalkMap (T.ι ≫ f) t
  have heq : ((T.ι ≫ f).stalkMap t).hom =
      (T.ι.stalkMap t).hom.comp (f.stalkMap (T.ι t)).hom :=
    congrArg (fun a : Y.presheaf.stalk (f (T.ι t)) ⟶
      T.toScheme.presheaf.stalk t => a.hom) (Scheme.Hom.stalkMap_comp T.ι f t)
  have hc : ((T.ι.stalkMap t).hom.comp (f.stalkMap (T.ι t)).hom).FormallyUnramified :=
    heq ▸ h
  have : IsIso (T.ι.stalkMap t) := inferInstance
  exact (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso
    (f.stalkMap (T.ι t)) (T.ι.stalkMap t)).mp hc

/-- A flat quasi-finite morphism is etale if it is already etale away
from a source boundary whose local rings have depth at least two. -/
theorem etale_of_flat_of_boundary_two_le_depth
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [Flat f]
    (T : X.Opens) [Etale (T.ι ≫ f)]
    (hdepth : ∀ x : X, x ∉ T →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x)) : Etale f := by
  have hlocal (x : X) : ∃ W : X.Opens, x ∈ W ∧ Etale (W.ι ≫ f) := by
    by_cases hx : x ∈ T
    · exact ⟨T, hx, inferInstance⟩
    have hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) :=
      (WithBot.coe_le_coe.mpr (hdepth x hx)).trans Module.depth_le_ringKrullDim
    apply exists_etale_open_of_flat_of_quasiFiniteAt_of_positive_dimension
      f x (f.quasiFiniteAt x) ((by norm_num : (1 : WithBot ℕ∞) ≤ 2).trans hdim)
    intro x' _ hdim'
    apply formallyUnramified_stalkMap_of_mem_etale_open f T
    by_contra hx'
    have hd : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x') :=
      (WithBot.coe_le_coe.mpr (hdepth x' hx')).trans Module.depth_le_ringKrullDim
    rw [hdim'] at hd
    norm_num at hd
  have : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
  choose W hW hEtale using hlocal
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale.{u}) (f := f)
    (fun x => W x) ?_ hEtale
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hW x⟩

/-- At each point, an actual flat open neighborhood is equivalent to an
actual etale open neighborhood under the depth-two boundary condition. -/
theorem exists_etale_open_iff_exists_flat_open_of_boundary_two_le_depth
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    (T : X.Opens) [Etale (T.ι ≫ f)]
    (hdepth : ∀ x : X, x ∉ T →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x)) (x : X) :
    (∃ W : X.Opens, x ∈ W ∧ Etale (W.ι ≫ f)) ↔
      ∃ W : X.Opens, x ∈ W ∧ Flat (W.ι ≫ f) := by
  constructor
  · rintro ⟨W, hxW, hW⟩
    exact ⟨W, hxW, inferInstance⟩
  · rintro ⟨W, hxW, hW⟩
    let Z : W.toScheme.Opens := W.ι ⁻¹ᵁ T
    have : Etale (Z.ι ≫ (W.ι ≫ f)) := by
      have he : (W.ι ∣_ T) ≫ (T.ι ≫ f) = Z.ι ≫ (W.ι ≫ f) := by
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
      rw [← he]
      infer_instance
    have hd (w : W.toScheme) (hw : w ∉ Z) :
        (2 : ℕ∞) ≤ Module.depth (W.toScheme.presheaf.stalk w)
          (W.toScheme.presheaf.stalk w) := by
      exact (hdepth (W.ι w) hw).trans
        (Module.depth_le_depth_of_ringEquiv
          (asIso (W.ι.stalkMap w)).commRingCatIsoToRingEquiv)
    exact ⟨W, hxW, etale_of_flat_of_boundary_two_le_depth (W.ι ≫ f) Z hd⟩

/-- The pointwise etale criterion uses flatness of the original stalk map;
the required flat neighborhood is constructed by openness of the flat locus. -/
theorem exists_etale_open_iff_flat_stalkMap_of_boundary_two_le_depth
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    (T : X.Opens) [Etale (T.ι ≫ f)]
    (hdepth : ∀ x : X, x ∉ T →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x)) (x : X) :
    (∃ W : X.Opens, x ∈ W ∧ Etale (W.ι ≫ f)) ↔ (f.stalkMap x).hom.Flat :=
  (exists_etale_open_iff_exists_flat_open_of_boundary_two_le_depth f T hdepth x).trans
    (exists_flat_open_iff_flat_stalkMap f x)

end AlgebraicGeometry
