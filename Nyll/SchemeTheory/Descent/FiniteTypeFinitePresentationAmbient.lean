/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.FiniteTypeAffineAmbient
public import Nyll.SchemeTheory.Descent.FinitePresentationTwoOpenOverlap
public import Nyll.SchemeTheory.Descent.TwoOpenGluing

/-!
# A separated finite-presentation ambient for the original finite-type scheme

The affine construction extends by induction on compact opens. At each
binary step the actual overlap is thickened, the resulting open charts are
glued, and the original scheme embeds as a closed subscheme of that gluing.
The closed overlap graph gives separatedness of the ambient structure map.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicCurves.Geometry.Schemes.Proofs
open exists_isPullback_glue_of_isPullback_of_isOpenImmersion
open scoped exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue

namespace AlgebraicGeometry

private theorem exists_finitePresentation_ambient_of_twoOpen
    {R : Type u} [CommRing R] {X U V A B : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (jU : U ⟶ X) (jV : V ⟶ X) [IsOpenImmersion jU] [IsOpenImmersion jV]
    (hcov : Set.range jU.base ∪ Set.range jV.base = Set.univ)
    (iU : U ⟶ A) (iV : V ⟶ B) [IsClosedImmersion iU] [IsClosedImmersion iV]
    (a : A ⟶ Spec (CommRingCat.of R)) (b : B ⟶ Spec (CommRingCat.of R))
    [QuasiCompact a] [IsSeparated a] [LocallyOfFinitePresentation a]
    [QuasiCompact b] [IsSeparated b] [LocallyOfFinitePresentation b]
    (hU : iU ≫ a = jU ≫ f) (hV : iV ≫ b = jV ≫ f) :
    ∃ (Y : Scheme.{u}) (i : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of R)),
      IsClosedImmersion i ∧ QuasiCompact g ∧ IsSeparated g ∧
      LocallyOfFinitePresentation g ∧ i ≫ g = f := by
  obtain ⟨A', B', C, mA, mB, zU, zV, vU, vV, t, hmA, hmAfp, hmB, hmBfp,
    hzU, hzV, hvU, hvV, hC, hzUmA, hzVmB, sqWU, sqWV, hab, hΓ⟩ :=
    ClosedImmersionApproximation.exists_finitePresentation_twoOpen_overlap
      f jU jV iU iV a b hU hV
  have : IsClosedImmersion mA := hmA
  have : LocallyOfFinitePresentation mA := hmAfp
  have : IsClosedImmersion mB := hmB
  have : LocallyOfFinitePresentation mB := hmBfp
  have : IsClosedImmersion zU := hzU
  have : IsClosedImmersion zV := hzV
  have : IsOpenImmersion vU := hvU
  have : IsOpenImmersion vV := hvV
  have : CompactSpace C := hC
  let a' := mA ≫ a
  let b' := mB ≫ b
  let Y := TwoOpenGlue.X₀ vU vV
  let g : Y ⟶ Spec (CommRingCat.of R) := TwoOpenGlue.f₀ a' b' vU vV hab
  let hW := IsPullback.of_hasPullback jU jV
  let π : X ⟶ Y := TwoOpenGlue.π vU vV jU jV hcov
    (pullback.fst jU jV) (pullback.snd jU jV) hW zU zV t sqWU sqWV
  have sqU : IsPullback zU jU (TwoOpenGlue.iU vU vV) π :=
    TwoOpenGlue.sqU vU vV jU jV hcov
      (pullback.fst jU jV) (pullback.snd jU jV) hW zU zV t sqWU sqWV
  have sqV : IsPullback zV jV (TwoOpenGlue.iV vU vV) π :=
    TwoOpenGlue.sqV vU vV jU jV hcov
      (pullback.fst jU jV) (pullback.snd jU jV) hW zU zV t sqWU sqWV
  have hπ : IsClosedImmersion π := by
    apply IsZariskiLocalAtTarget.of_openCover
      (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
      (TwoOpenGlue.coverX₀ vU vV)
    rintro (_ | _)
    · change IsClosedImmersion (pullback.snd π (TwoOpenGlue.iV vU vV))
      exact sqV.flip.isoPullback_inv_snd ▸ inferInstanceAs
        (IsClosedImmersion (sqV.flip.isoPullback.inv ≫ zV))
    · change IsClosedImmersion (pullback.snd π (TwoOpenGlue.iU vU vV))
      exact sqU.flip.isoPullback_inv_snd ▸ inferInstanceAs
        (IsClosedImmersion (sqU.flip.isoPullback.inv ≫ zU))
  have : IsSeparated (TwoOpenGlue.iU vU vV ≫ g) := by
    change IsSeparated (TwoOpenGlue.iU vU vV ≫ TwoOpenGlue.f₀ a' b' vU vV hab)
    rw [TwoOpenGlue.iU_f₀]
    infer_instance
  have : IsSeparated (TwoOpenGlue.iV vU vV ≫ g) := by
    change IsSeparated (TwoOpenGlue.iV vU vV ≫ TwoOpenGlue.f₀ a' b' vU vV hab)
    rw [TwoOpenGlue.iV_f₀]
    infer_instance
  have hΓ' : IsClosedImmersion
      (pullback.lift vU vV
        (by rw [← Category.assoc, (TwoOpenGlue.isPullback_charts vU vV).w,
          Category.assoc]) :
        C ⟶ pullback (TwoOpenGlue.iU vU vV ≫ g) (TwoOpenGlue.iV vU vV ≫ g)) := by
    have hgraph (a₀ : A' ⟶ Spec (CommRingCat.of R))
        (b₀ : B' ⟶ Spec (CommRingCat.of R)) (ha : a₀ = a') (hb : b₀ = b')
        (w : vU ≫ a₀ = vV ≫ b₀) : IsClosedImmersion (pullback.lift vU vV w) := by
      subst a₀
      subst b₀
      exact hΓ
    exact hgraph _ _ (TwoOpenGlue.iU_f₀ a' b' vU vV hab)
      (TwoOpenGlue.iV_f₀ a' b' vU vV hab) _
  have hgsep : IsSeparated g :=
    TwoOpenGlue.QSGlue.separated_glue g (TwoOpenGlue.iU vU vV) (TwoOpenGlue.iV vU vV)
      (TwoOpenGlue.range_union vU vV) vU vV (TwoOpenGlue.isPullback_charts vU vV) hΓ'
  have hU' : zU ≫ a' = jU ≫ f := by
    change zU ≫ (mA ≫ a) = jU ≫ f
    rw [← Category.assoc, hzUmA, hU]
  have hV' : zV ≫ b' = jV ≫ f := by
    change zV ≫ (mB ≫ b) = jV ≫ f
    rw [← Category.assoc, hzVmB, hV]
  have hπg : π ≫ g = f :=
    TwoOpenGlue.π_f₀_of_comp a' b' vU vV hab jU jV hcov
      (pullback.fst jU jV) (pullback.snd jU jV) hW zU zV t sqWU sqWV f hU' hV'
  exact ⟨Y, π, g, hπ, TwoOpenGlue.qc a' b' vU vV hab, hgsep,
    TwoOpenGlue.lfp a' b' vU vV hab, hπg⟩

/-- Every separated finite-type scheme over an arbitrary ring is a closed
subscheme of a separated finite-presentation scheme over the same ring.
The embedding retains the original source and structure morphism. -/
theorem exists_finitePresentation_ambient
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    ∃ (Y : Scheme.{u}) (i : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of R)),
      IsClosedImmersion i ∧ QuasiCompact g ∧ IsSeparated g ∧
      LocallyOfFinitePresentation g ∧ i ≫ g = f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let P : X.Opens → Prop := fun O =>
    ∃ (Y : Scheme.{u}) (i : O.toScheme ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of R)),
      IsClosedImmersion i ∧ QuasiCompact g ∧ IsSeparated g ∧
      LocallyOfFinitePresentation g ∧ i ≫ g = O.ι ≫ f
  have hAffine (O : X.Opens) (hO : IsAffineOpen O) : P O := by
    have : IsAffine O.toScheme := hO
    obtain ⟨Y, i, g, hY, hi, hg, hig⟩ :=
      exists_affine_finitePresentation_ambient (O.ι ≫ f)
    have : IsAffine Y := hY
    exact ⟨Y, i, g, hi, inferInstance, inferInstance, hg, hig⟩
  have htop : P ⊤ := by
    refine compact_open_induction_on (⊤ : X.Opens) isCompact_univ
      (hAffine ⊥ (isAffineOpen_bot X)) ?_
    intro O _hOc W hO
    obtain ⟨A, iU, a, hiU, hqa, hsa, hfa, hia⟩ := hO
    obtain ⟨B, iV, b, hiV, hqb, hsb, hfb, hib⟩ := hAffine W.1 W.2
    have : IsClosedImmersion iU := hiU
    have : QuasiCompact a := hqa
    have : IsSeparated a := hsa
    have : LocallyOfFinitePresentation a := hfa
    have : IsClosedImmersion iV := hiV
    have : QuasiCompact b := hqb
    have : IsSeparated b := hsb
    have : LocallyOfFinitePresentation b := hfb
    let T : X.Opens := O ⊔ W.1
    let jU : O.toScheme ⟶ T.toScheme := X.homOfLE (show O ≤ T from le_sup_left)
    let jV : W.1.toScheme ⟶ T.toScheme := X.homOfLE (show W.1 ≤ T from le_sup_right)
    have hcov : Set.range jU.base ∪ Set.range jV.base = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      rcases x.2 with hx | hx
      · refine Or.inl ⟨⟨x.1, hx⟩, ?_⟩
        change X.homOfLE (show O ≤ T from le_sup_left) ⟨x.1, hx⟩ = x
        apply Subtype.ext
        exact Scheme.homOfLE_apply _ _
      · refine Or.inr ⟨⟨x.1, hx⟩, ?_⟩
        change X.homOfLE (show W.1 ≤ T from le_sup_right) ⟨x.1, hx⟩ = x
        apply Subtype.ext
        exact Scheme.homOfLE_apply _ _
    have hU : iU ≫ a = jU ≫ (T.ι ≫ f) := by
      simpa only [jU, ← Category.assoc, Scheme.homOfLE_ι] using hia
    have hV : iV ≫ b = jV ≫ (T.ι ≫ f) := by
      simpa only [jV, ← Category.assoc, Scheme.homOfLE_ι] using hib
    exact exists_finitePresentation_ambient_of_twoOpen
      (T.ι ≫ f) jU jV hcov iU iV a b hU hV
  obtain ⟨Y, i, g, hi, hgqc, hgsep, hgfp, hig⟩ := htop
  have : IsClosedImmersion i := hi
  refine ⟨Y, X.topIso.inv ≫ i, g, inferInstance, hgqc, hgsep, hgfp, ?_⟩
  rw [Category.assoc, hig, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]

end AlgebraicGeometry
