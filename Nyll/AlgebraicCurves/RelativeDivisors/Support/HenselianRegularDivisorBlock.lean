/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.ProperHenselianClopenLift
import Nyll.AlgebraicCurves.RelativeDivisors.Support.RelEffCartierDivSupportedIn
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# The regular block of a relative divisor over a Henselian local base

The closed fibre of a finite family is Artinian, including in the wildly
ramified case. Its part lying in a prescribed source open is therefore
clopen. Lifting this actual clopen subset produces an open-and-closed finite
flat block of the original family, with its full defining ideal. Properness
over the local base makes the whole block supported in the prescribed open.
No section splitting, separability, or tame ramification is required.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RelEffCartierDiv

/-- Support in an open can be checked on the closed fibre over a local ring.
The finite family itself supplies the closed-map argument. -/
theorem supportedIn_of_closedFiber
    {R : Type u} [CommRing R] [IsLocalRing R]
    {C S : Scheme.{u}} {c : C ⟶ S} {n : ℕ}
    {t : Spec (.of R) ⟶ S} (D : RelEffCartierDiv c n t) (U : C.Opens)
    (h : ∀ x : D.I.subscheme,
      (D.I.subschemeι ≫ pullback.snd c t) x = IsLocalRing.closedPoint R →
      pullback.fst c t (D.I.subschemeι x) ∈ U) : D.SupportedIn U := by
  apply (D.supportedIn_iff_supportedInLocus_eq_top U).2
  exact (IsLocalRing.closedPoint_mem_iff (D.supportedInLocus U)).mp h

/-- The actual finite-flat block whose closed fibre consists precisely of
the points at which the given source open is defined. Its kernel is retained,
so its nilpotents and ramification multiplicities are not discarded. -/
theorem exists_henselian_regularBlock
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {C S : Scheme.{u}} {c : C ⟶ S} {n : ℕ}
    {t : Spec (.of R) ⟶ S} (D : RelEffCartierDiv c n t) (U : C.Opens) :
    let p := D.I.subschemeι ≫ pullback.snd c t
    let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    ∃ V : D.I.subscheme.Opens, IsClosed (V : Set D.I.subscheme) ∧
      (pullback.fst p r ⁻¹' (V : Set D.I.subscheme) =
        (pullback.fst p r ≫ D.I.subschemeι ≫ pullback.fst c t) ⁻¹' (U : Set C)) ∧
      ∃ (m : ℕ) (D₀ : RelEffCartierDiv c m t),
        D₀.I = (V.ι ≫ D.I.subschemeι).ker ∧ D₀.SupportedIn U := by
  intro p r
  have : IsFinite p := D.isFinite
  have : Flat p := D.flat
  have : LocallyOfFinitePresentation p := D.locallyOfFinitePresentation
  have : IsLocallyArtinian (pullback p r) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd p r)
  let W₀ : Set ↥(pullback p r) :=
    (pullback.fst p r ≫ D.I.subschemeι ≫ pullback.fst c t) ⁻¹' (U : Set C)
  have hW₀ : IsClopen W₀ := ⟨isClosed_discrete _, isOpen_discrete _⟩
  obtain ⟨W, hW, hWr⟩ :=
    exists_isClopen_closedFiber_preimage_eq_of_isProper_of_henselianLocalRing p W₀ hW₀
  let V : D.I.subscheme.Opens := ⟨W, hW.isOpen⟩
  have : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]
      exact hW.isClosed)
  let j : V.toScheme ⟶ pullback c t := V.ι ≫ D.I.subschemeι
  have : IsClosedImmersion j :=
    inferInstanceAs (IsClosedImmersion (V.ι ≫ D.I.subschemeι))
  let e : V.toScheme ≅ j.ker.subscheme := asIso j.toImage
  have hι : j.ker.subschemeι = e.inv ≫ j := by
    apply (cancel_epi e.hom).1
    change j.toImage ≫ j.imageι = e.hom ≫ (e.inv ≫ j)
    rw [Scheme.Hom.toImage_imageι, e.hom_inv_id_assoc]
  have hproj : j.ker.subschemeι ≫ pullback.snd c t = e.inv ≫ (V.ι ≫ p) := by
    rw [hι]
    simp only [j, p, Category.assoc]
  let m : ℕ := (V.ι ≫ p).finrank (IsLocalRing.closedPoint R)
  have hrank (x : Spec (.of R)) : (V.ι ≫ p).finrank x = m := by
    have hlc := (V.ι ≫ p).isLocallyConstant_finrank
    have hx : IsLocalRing.closedPoint R ∈
        (V.ι ≫ p).finrank ⁻¹' {(V.ι ≫ p).finrank x} :=
      (IsLocalRing.specializes_closedPoint x).mem_closed
        (hlc.isClopen_fiber ((V.ι ≫ p).finrank x)).isClosed rfl
    exact hx.symm
  let D₀ : RelEffCartierDiv c m t :=
    { I := j.ker
      isFinite := by rw [hproj]; infer_instance
      flat := by rw [hproj]; infer_instance
      locallyOfFinitePresentation := by rw [hproj]; infer_instance
      finrank_eq := fun x => by
        rw [hproj, Scheme.Hom.finrank_comp_left_of_isIso]
        exact hrank x }
  refine ⟨V, hW.isClosed, hWr, m, D₀, rfl, ?_⟩
  apply supportedIn_of_closedFiber D₀ U
  intro x hx
  have hx' : p (V.ι (e.inv x)) = IsLocalRing.closedPoint R := by
    change (j.ker.subschemeι ≫ pullback.snd c t) x = _ at hx
    rw [hproj] at hx
    simpa only [Scheme.Hom.comp_apply] using hx
  let z₀ : Spec (.of (IsLocalRing.ResidueField R)) :=
    IsLocalRing.closedPoint (IsLocalRing.ResidueField R)
  have hr : r z₀ = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := p) (g := r) (V.ι (e.inv x)) z₀ (hx'.trans hr.symm)
  have hzW : z ∈ pullback.fst p r ⁻¹' W := by
    change pullback.fst p r z ∈ W
    rw [hz]
    exact (e.inv x).property
  rw [hWr] at hzW
  change pullback.fst c t (D.I.subschemeι (pullback.fst p r z)) ∈ U at hzW
  rw [hz] at hzW
  change pullback.fst c t (j.ker.subschemeι x) ∈ U
  rw [hι]
  simpa only [j, Scheme.Hom.comp_apply] using hzW

end AlgebraicGeometry.RelEffCartierDiv
