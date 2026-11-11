/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.CompactOpenClosedImmersionExtension
public import Nyll.SchemeTheory.Descent.FiniteClosedThickeningOpenProjections
public import Nyll.SchemeTheory.Descent.FinitePresentationOpenPatch
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# A common finite-presentation overlap for two actual ambient charts

The original overlap of two opens in a separated scheme is closed in the
product of their ambient charts. Finite equations thicken that overlap
while preserving its two closed projections into compact ambient opens.
Extending those equations to both ambient charts produces one common open
overlap, with both Cartesian squares on the original scheme retained.

No Noetherian hypothesis or ambient embedding of the whole scheme is used.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ClosedImmersionApproximation

/-- Two actual closed ambient embeddings can be thickened to compatible
finite-presentation ambient charts. The common overlap is open in both
charts, is quasicompact, and has closed graph over the original base. -/
theorem exists_finitePresentation_twoOpen_overlap
    {S X U V A B : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [IsSeparated f]
    (jU : U ⟶ X) (jV : V ⟶ X) [IsOpenImmersion jU] [IsOpenImmersion jV]
    (iU : U ⟶ A) (iV : V ⟶ B) [IsClosedImmersion iU] [IsClosedImmersion iV]
    (a : A ⟶ S) (b : B ⟶ S)
    [QuasiCompact a] [IsSeparated a] [LocallyOfFinitePresentation a]
    [QuasiCompact b] [IsSeparated b] [LocallyOfFinitePresentation b]
    (hU : iU ≫ a = jU ≫ f) (hV : iV ≫ b = jV ≫ f) :
    ∃ (A' B' C : Scheme.{u}) (mA : A' ⟶ A) (mB : B' ⟶ B)
      (zU : U ⟶ A') (zV : V ⟶ B') (vU : C ⟶ A') (vV : C ⟶ B')
      (t : pullback jU jV ⟶ C),
      IsClosedImmersion mA ∧ LocallyOfFinitePresentation mA ∧
      IsClosedImmersion mB ∧ LocallyOfFinitePresentation mB ∧
      IsClosedImmersion zU ∧ IsClosedImmersion zV ∧
      IsOpenImmersion vU ∧ IsOpenImmersion vV ∧ CompactSpace C ∧
      zU ≫ mA = iU ∧ zV ≫ mB = iV ∧
      IsPullback (pullback.fst jU jV) t zU vU ∧
      IsPullback (pullback.snd jU jV) t zV vV ∧
      ∃ h : vU ≫ (mA ≫ a) = vV ≫ (mB ≫ b),
        IsClosedImmersion (pullback.lift vU vV h) := by
  have : MorphismProperty.IsStableUnderComposition
      (@IsClosedImmersion : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@IsClosedImmersion : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace a
  have : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace b
  have : QuasiSeparatedSpace A := quasiSeparatedSpace_of_quasiSeparated a
  have : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated b
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace iU
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace iV
  have : CompactSpace (pullback jU jV : Scheme.{u}) := inferInstance
  have : CompactSpace (pullback a b : Scheme.{u}) := inferInstance
  have : QuasiSeparatedSpace (pullback a b : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst a b)
  let e : pullback (jU ≫ f) (jV ≫ f) ⟶ pullback a b :=
    pullback.map (jU ≫ f) (jV ≫ f) a b iU iV (𝟙 S)
      ((Category.comp_id _).trans hU.symm) ((Category.comp_id _).trans hV.symm)
  have : IsClosedImmersion e :=
    MorphismProperty.pullbackMap (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
      inferInstance inferInstance hU.symm hV.symm
  let j : pullback jU jV ⟶ pullback a b := pullback.mapDesc jU jV f ≫ e
  have : IsClosedImmersion j := inferInstance
  have hjU : j ≫ pullback.fst a b = pullback.fst jU jV ≫ iU := by
    simp only [j, e, pullback.mapDesc, pullback.map, Category.assoc,
      pullback.lift_fst_assoc, pullback.lift_fst, Category.comp_id]
  have hjV : j ≫ pullback.snd a b = pullback.snd jU jV ≫ iV := by
    simp only [j, e, pullback.mapDesc, pullback.map, Category.assoc,
      pullback.lift_snd_assoc, pullback.lift_snd, Category.comp_id]
  obtain ⟨OU, hOUc, hOU⟩ := exists_isCompact_open_preimage_eq_of_isClosedImmersion
    iU (pullback.fst jU jV).opensRange
      (isCompact_range (pullback.fst jU jV).continuous)
  obtain ⟨OV, hOVc, hOV⟩ := exists_isCompact_open_preimage_eq_of_isClosedImmersion
    iV (pullback.snd jU jV).opensRange
      (isCompact_range (pullback.snd jU jV).continuous)
  have hrU : Set.range (pullback.fst jU jV ≫ iU) ⊆ Set.range OU.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    change pullback.fst jU jV w ∈ iU ⁻¹ᵁ OU
    rw [hOU]
    exact ⟨w, rfl⟩
  have hrV : Set.range (pullback.snd jU jV ≫ iV) ⊆ Set.range OV.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    change pullback.snd jU jV w ∈ iV ⁻¹ᵁ OV
    rw [hOV]
    exact ⟨w, rfl⟩
  let p : pullback jU jV ⟶ OU.toScheme :=
    IsOpenImmersion.lift OU.ι (pullback.fst jU jV ≫ iU) hrU
  let q : pullback jU jV ⟶ OV.toScheme :=
    IsOpenImmersion.lift OV.ι (pullback.snd jU jV ≫ iV) hrV
  have hp : p ≫ OU.ι = pullback.fst jU jV ≫ iU :=
    IsOpenImmersion.lift_fac _ _ hrU
  have hq : q ≫ OV.ι = pullback.snd jU jV ≫ iV :=
    IsOpenImmersion.lift_fac _ _ hrV
  have sqU : IsPullback (pullback.fst jU jV) p iU OU.ι :=
    (IsOpenImmersion.isPullback p (pullback.fst jU jV) OU.ι iU hp.symm
      (by rw [Scheme.Opens.opensRange_ι]; exact hOU)).flip
  have sqV : IsPullback (pullback.snd jU jV) q iV OV.ι :=
    (IsOpenImmersion.isPullback q (pullback.snd jU jV) OV.ι iV hq.symm
      (by rw [Scheme.Opens.opensRange_ι]; exact hOV)).flip
  have : IsClosedImmersion p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
      (self := IsClosedImmersion.isStableUnderBaseChange) sqU inferInstance
  have : IsClosedImmersion q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
      (self := IsClosedImmersion.isStableUnderBaseChange) sqV inferInstance
  let I := j.ker
  let pI : I.subscheme ⟶ OU.toScheme := inv j.toImage ≫ p
  let qI : I.subscheme ⟶ OV.toScheme := inv j.toImage ≫ q
  have hjimage : inv j.toImage ≫ j = I.subschemeι :=
    (congrArg (fun z : pullback jU jV ⟶ pullback a b => inv j.toImage ≫ z)
      j.toImage_imageι.symm).trans (IsIso.inv_hom_id_assoc j.toImage I.subschemeι)
  have hpI : I.subschemeι ≫ pullback.fst a b = pI ≫ OU.ι := by
    change I.subschemeι ≫ pullback.fst a b = (inv j.toImage ≫ p) ≫ OU.ι
    rw [← hjimage, Category.assoc, hjU, Category.assoc, hp]
  have hqI : I.subschemeι ≫ pullback.snd a b = qI ≫ OV.ι := by
    change I.subschemeι ≫ pullback.snd a b = (inv j.toImage ≫ q) ≫ OV.ι
    rw [← hjimage, Category.assoc, hjV, Category.assoc, hq]
  obtain ⟨C, c, d, cU, cV, hc, _hcfp, hcUclosed, hcUfp, hcVclosed, hcVfp,
    hcU, hcV, hd⟩ := exists_finite_thickening_with_open_projections I
      (pullback.fst a b) (pullback.snd a b) OU OV hOUc hOVc pI qI hpI hqI
  have : IsClosedImmersion c := hc
  have : IsClosedImmersion cU := hcUclosed
  have : LocallyOfFinitePresentation cU := hcUfp
  have : IsClosedImmersion cV := hcVclosed
  have : LocallyOfFinitePresentation cV := hcVfp
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  let t : pullback jU jV ⟶ C := j.toImage ≫ d
  have ht : t ≫ c = j := by
    change (j.toImage ≫ d) ≫ c = j
    rw [Category.assoc, hd, Scheme.Hom.toImage_imageι]
  have htp : t ≫ cU = p := by
    apply (cancel_mono OU.ι).mp
    rw [Category.assoc, ← hcU, ← Category.assoc, ht, hjU, hp]
  have htq : t ≫ cV = q := by
    apply (cancel_mono OV.ι).mp
    rw [Category.assoc, ← hcV, ← Category.assoc, ht, hjV, hq]
  obtain ⟨A', mA, zU, vU, hmA, hmAfp, hzU, hvU, hzUmA, sqCU, sqWU⟩ :=
    exists_finitePresentation_ambient_with_open_patch iU OU hOUc
      (pullback.fst jU jV) p sqU cU t htp
  obtain ⟨B', mB, zV, vV, hmB, hmBfp, hzV, hvV, hzVmB, sqCV, sqWV⟩ :=
    exists_finitePresentation_ambient_with_open_patch iV OV hOVc
      (pullback.snd jU jV) q sqV cV t htq
  have : IsClosedImmersion mA := hmA
  have : IsClosedImmersion mB := hmB
  have hcA : c ≫ pullback.fst a b = vU ≫ mA := hcU.trans sqCU.w
  have hcB : c ≫ pullback.snd a b = vV ≫ mB := hcV.trans sqCV.w
  have hab : vU ≫ (mA ≫ a) = vV ≫ (mB ≫ b) := by
    rw [← Category.assoc, ← hcA, Category.assoc, pullback.condition,
      ← Category.assoc, hcB, Category.assoc]
  let γ : C ⟶ pullback (mA ≫ a) (mB ≫ b) := pullback.lift vU vV hab
  let r : pullback (mA ≫ a) (mB ≫ b) ⟶ pullback a b :=
    pullback.map (mA ≫ a) (mB ≫ b) a b mA mB (𝟙 S)
      (Category.comp_id _) (Category.comp_id _)
  have : IsClosedImmersion r :=
    MorphismProperty.pullbackMap (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
      hmA hmB rfl rfl
  have hγr : γ ≫ r = c := by
    apply pullback.hom_ext
    · simpa only [γ, r, pullback.map, Category.assoc,
        pullback.lift_fst_assoc, pullback.lift_fst] using hcA.symm
    · simpa only [γ, r, pullback.map, Category.assoc,
        pullback.lift_snd_assoc, pullback.lift_snd] using hcB.symm
  have : IsClosedImmersion (γ ≫ r) := hγr.symm ▸ hc
  have hγ : IsClosedImmersion γ := IsClosedImmersion.of_comp_isClosedImmersion γ r
  exact ⟨A', B', C, mA, mB, zU, zV, vU, vV, t, hmA, hmAfp, hmB, hmBfp,
    hzU, hzV, hvU, hvV, inferInstance, hzUmA, hzVmB, sqWU, sqWV, hab, hγ⟩

end AlgebraicGeometry.ClosedImmersionApproximation
