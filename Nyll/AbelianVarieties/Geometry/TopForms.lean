/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Nyll.SchemeTheory.Modules.Differentials.TopFormMaps
public import Nyll.AbelianVarieties.Geometry.InvariantDifferentials
public import Nyll.SchemeTheory.RingTheory.Differentials.TopForms
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.Modules.ExteriorPower.Det
public import Nyll.SchemeTheory.Modules.ExteriorPower.PresheafExteriorPower
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.KaehlerDifferentials
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections

/-!
# Translation invariant top forms at field-valued points

Affine-chart invariance gives pointwise invariance after any compatible field extension.
-/

@[expose] public section

attribute [local instance] AlgebraicGeometry.Scheme.Hom.kaehlerPresheafModule

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_topFormMap_mul_eq_of_forall_topFormMap_appLE_mul_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.PointwiseTopForms

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

universe u

namespace AffinePoints

theorem exists_affineOpen_le {X : Scheme.{u}} (O : X.Opens) (x : X) (hx : x ∈ O) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ O := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx O.2
  exact ⟨W, hW, hxW, hWO⟩

theorem fromSpec_comp_eq {K : Type u} [CommRing K] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of
  K))
    {V : X.Opens} (hV : IsAffineOpen V) :
    let _ : Algebra K Γ(X, V) := g.sectionsAlgebra V
    hV.fromSpec ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, V))) := by
  intro algV
  have h := IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hV (le_top : V ≤ g ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  change _ = Spec.map (CommRingCat.ofHom
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appLE ⊤ V le_top).hom)
  rw [CommRingCat.ofHom_hom, Spec.map_comp, h]

end AffinePoints

end AbelianVarieties.NOSProofs.PointwiseTopForms

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
open AbelianVarieties.NOSProofs.PointwiseTopForms.AffinePoints
open SchemeTheory.TopFormMaps.AffineCharts
  (exists_ringHom_of_mem ringHom_eq_of_specMap_comp_fromSpec)

universe u

theorem topFormMap_mul_eq_of_forall_topFormMap_appLE_mul_eq
    {K : Type u} [Field K] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of K))
    [Smooth g] (LG : RelativeGroupLaw K g) (d : ℕ) [SmoothOfRelativeDimension d g]
    (ω : Γ(g.topDifferentials d, ⊤))
    (hω : ∀ (V U' U'' : G.Opens) (_ : IsAffineOpen V) (_ : IsAffineOpen U')
        (_ : IsAffineOpen U'') (W : (pullback g g).Opens) (_ : IsAffineOpen W)
        (hWV : W ≤ pullback.fst g g ⁻¹ᵁ V) (hWU' : W ≤ pullback.snd g g ⁻¹ᵁ U')
        (hWU'' : W ≤ (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
            ⟨pullback.snd g g, pullback.condition.symm⟩).1 ⁻¹ᵁ U''),
        let _ : Algebra K Γ(G, V) := g.sectionsAlgebra V
        let _ : Algebra K Γ(G, U') := g.sectionsAlgebra U'
        let _ : Algebra K Γ(G, U'') := g.sectionsAlgebra U''
        let _ : Algebra K Γ(pullback g g, W) := (pullback.fst g g ≫ g).sectionsAlgebra W
        let : Algebra Γ(G, V) Γ(pullback g g, W) := ((pullback.fst g g).appLE V W hWV).hom.toAlgebra
        let : Algebra Γ(G, U') Γ(pullback g g, W) := ((pullback.snd g g).appLE U' W
          hWU').hom.toAlgebra
        let : Algebra Γ(G, U'') Γ(pullback g g, W) :=
          ((LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
            ⟨pullback.snd g g, pullback.condition.symm⟩).1.appLE U'' W hWU'').hom.toAlgebra
        ∀ [IsScalarTower K Γ(G, V) Γ(pullback g g, W)] [IsScalarTower K Γ(G, U') Γ(pullback g g, W)]
          [IsScalarTower K Γ(G, U'') Γ(pullback g g, W)],
        ∀ (ω' : ⋀[Γ(G, U')]^d (g.kaehlerPresheaf.obj (op U')))
          (ω'' : ⋀[Γ(G, U'')]^d (g.kaehlerPresheaf.obj (op U''))),
          g.topToSections d U' ω' = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          g.topToSections d U'' ω'' = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K Γ(G, V) Γ(G, U'') Γ(pullback g g, W) d ω'' =
            TopFormOrder.topFormMap K Γ(G, V) Γ(G, U') Γ(pullback g g, W) d ω') :
    ∀ (L F : Type u) [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K
      L F]
        (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) g)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) g)
        (U' U'' : G.Opens) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        [Algebra Γ(G, U') F] [Algebra Γ(G, U'') F],
        let _ : Algebra K Γ(G, U') := g.sectionsAlgebra U'
        let _ : Algebra K Γ(G, U'') := g.sectionsAlgebra U''
        ∀ [IsScalarTower K Γ(G, U') F] [IsScalarTower K Γ(G, U'') F],
        Spec.map (CommRingCat.ofHom (algebraMap Γ(G, U') F)) ≫ hU'.fromSpec = x.1 →
        Spec.map (CommRingCat.ofHom (algebraMap Γ(G, U'') F)) ≫ hU''.fromSpec =
          (LG.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
            ⟨Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1, by
              rw [Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]⟩ x).1 →
        ∀ (ω' : ⋀[Γ(G, U')]^d (g.kaehlerPresheaf.obj (op U')))
          (ω'' : ⋀[Γ(G, U'')]^d (g.kaehlerPresheaf.obj (op U''))),
          g.topToSections d U' ω' = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          g.topToSections d U'' ω'' = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K L Γ(G, U'') F d ω'' = TopFormOrder.topFormMap K L Γ(G, U') F d
            ω' := by
  intro L F _ _ _ _ _ _ a x U' U'' hU' hU'' algU'F algU''F
    algKU' algKU'' _ _ hx hax ω' ω'' hω' hω''
  classical
  let ptF : Spec (CommRingCat.of F) := IsLocalRing.closedPoint F
  let ptL : Spec (CommRingCat.of L) := IsLocalRing.closedPoint L
  let m : pullback g g ⟶ G := (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
    ⟨pullback.snd g g, pullback.condition.symm⟩).1
  have hm : m = (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
    ⟨pullback.snd g g, pullback.condition.symm⟩).1 := rfl
  have hmg : m ≫ g = pullback.fst g g ≫ g :=
    (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g,
      pullback.condition.symm⟩).2
  obtain ⟨V, hV, haV, -⟩ := exists_affineOpen_le (⊤ : G.Opens) (a.1.base ptL) trivial
  let algKV : Algebra K Γ(G, V) := g.sectionsAlgebra V
  obtain ⟨ρ, hρ⟩ := exists_ringHom_of_mem hV a.1 haV
  let algVL : Algebra Γ(G, V) L := ρ.toAlgebra
  let algVF : Algebra Γ(G, V) F := ((algebraMap L F).comp ρ).toAlgebra
  have towerVLF : IsScalarTower Γ(G, V) L F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have towerKVL : IsScalarTower K Γ(G, V) L := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    have h1 : Spec.map (CommRingCat.ofHom ((algebraMap Γ(G, V) L).comp (algebraMap K Γ(G, V)))) =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, ← fromSpec_comp_eq g hV, ← Category.assoc]
      change (Spec.map (CommRingCat.ofHom ρ) ≫ hV.fromSpec) ≫ g = _
      rw [hρ, a.2]
    have h2 := congrArg (fun f => f.hom k) (Spec.map_injective h1)
    exact h2.symm
  let aF : Spec (CommRingCat.of F) ⟶ G := Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1
  have haF : aF = Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1 := rfl
  have haFg : aF ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    rw [haF, Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ←
      IsScalarTower.algebraMap_eq]
  let z : Spec (CommRingCat.of F) ⟶ pullback g g := pullback.lift aF x.1 (by rw [haFg, x.2])
  have hz : z = pullback.lift aF x.1 (by rw [haFg, x.2]) := rfl
  have hzg : z ≫ (pullback.fst g g ≫ g) = Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    rw [← Category.assoc, hz, pullback.lift_fst, haFg]
  have hzm : z ≫ m = (LG.mul (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟨aF, haFg⟩ x).1 := by
    have key := congrArg Subtype.val (LG.mul_natural (pullback.fst g g ≫ g) _ z hzg
      ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩)
    rw [schemeHomOverComp_coe] at key
    have h1 : schemeHomOverComp z hzg ⟨pullback.fst g g, rfl⟩ =
        (⟨aF, haFg⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) g) :=
      Subtype.ext (by rw [schemeHomOverComp_coe, hz, pullback.lift_fst])
    have h2 : schemeHomOverComp z hzg ⟨pullback.snd g g, pullback.condition.symm⟩ = x :=
      Subtype.ext (by rw [schemeHomOverComp_coe, hz, pullback.lift_snd])
    rw [h1, h2] at key
    rw [← hm] at key
    exact key
  have hcp : (Spec.map (CommRingCat.ofHom (algebraMap L F))).base ptF =
      ptL := Subsingleton.elim _ _
  let O : (pullback g g).Opens := (pullback.fst g g ⁻¹ᵁ V ⊓ pullback.snd g g ⁻¹ᵁ U') ⊓ m ⁻¹ᵁ U''
  have hzO : z.base ptF ∈ O := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change (z ≫ pullback.fst g g).base ptF ∈ V
      rw [hz, pullback.lift_fst, haF, Scheme.Hom.comp_base, TopCat.comp_app, hcp]
      exact haV
    · change (z ≫ pullback.snd g g).base ptF ∈ U'
      rw [hz, pullback.lift_snd, ← hx, Scheme.Hom.comp_base, TopCat.comp_app, ← SetLike.mem_coe,
        ← IsAffineOpen.range_fromSpec hU']
      exact ⟨_, rfl⟩
    · change (z ≫ m).base ptF ∈ U''
      rw [hzm, ← hax, Scheme.Hom.comp_base, TopCat.comp_app, ← SetLike.mem_coe, ←
        IsAffineOpen.range_fromSpec hU'']
      exact ⟨_, rfl⟩
  obtain ⟨W, hW, hzW, hWO⟩ := exists_affineOpen_le O _ hzO
  have hWV : W ≤ pullback.fst g g ⁻¹ᵁ V := hWO.trans (inf_le_left.trans inf_le_left)
  have hWU' : W ≤ pullback.snd g g ⁻¹ᵁ U' := hWO.trans (inf_le_left.trans inf_le_right)
  have hWU'' : W ≤ m ⁻¹ᵁ U'' := hWO.trans inf_le_right
  obtain ⟨ζ, hζ⟩ := exists_ringHom_of_mem hW z hzW
  let algKW : Algebra K Γ(pullback g g, W) := (pullback.fst g g ≫ g).sectionsAlgebra W
  let algVW : Algebra Γ(G, V) Γ(pullback g g, W) := ((pullback.fst g g).appLE V W hWV).hom.toAlgebra
  let algU'W : Algebra Γ(G, U') Γ(pullback g g, W) := ((pullback.snd g g).appLE U' W
    hWU').hom.toAlgebra
  let algU''W : Algebra Γ(G, U'') Γ(pullback g g, W) := (m.appLE U'' W hWU'').hom.toAlgebra
  let algWF : Algebra Γ(pullback g g, W) F := ζ.toAlgebra
  have towerKVW : IsScalarTower K Γ(G, V) Γ(pullback g g, W) :=
    AbelianVarieties.NOSProofs.InvariantTopForms.SectionTowers.of_comp_eq
      (pullback.fst g g) g (pullback.fst g g ≫ g) rfl V W hWV
  have towerKUW : IsScalarTower K Γ(G, U') Γ(pullback g g, W) :=
    AbelianVarieties.NOSProofs.InvariantTopForms.SectionTowers.of_comp_eq
      (pullback.snd g g) g (pullback.fst g g ≫ g) pullback.condition.symm U' W hWU'
  have towerKU2W : IsScalarTower K Γ(G, U'') Γ(pullback g g, W) :=
    AbelianVarieties.NOSProofs.InvariantTopForms.SectionTowers.of_comp_eq
      m g (pullback.fst g g ≫ g) hmg U'' W hWU''
  have towerVWF : IsScalarTower Γ(G, V) Γ(pullback g g, W) F := by
    refine IsScalarTower.of_algebraMap_eq fun v => ?_
    have : ζ.comp ((pullback.fst g g).appLE V W hWV).hom = (algebraMap L F).comp ρ := by
      apply ringHom_eq_of_specMap_comp_fromSpec hV
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
        IsAffineOpen.SpecMap_appLE_fromSpec _ hV hW hWV, ← Category.assoc, hζ, hz,
          pullback.lift_fst,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hρ]
    exact (congrArg (fun φ => φ v) this).symm
  have towerUWF : IsScalarTower Γ(G, U') Γ(pullback g g, W) F := by
    refine IsScalarTower.of_algebraMap_eq fun v => ?_
    have : ζ.comp ((pullback.snd g g).appLE U' W hWU').hom = algebraMap Γ(G, U') F := by
      apply ringHom_eq_of_specMap_comp_fromSpec hU'
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
        IsAffineOpen.SpecMap_appLE_fromSpec _ hU' hW hWU', ← Category.assoc, hζ, hz,
          pullback.lift_snd, hx]
    exact (congrArg (fun φ => φ v) this).symm
  have towerU2WF : IsScalarTower Γ(G, U'') Γ(pullback g g, W) F := by
    refine IsScalarTower.of_algebraMap_eq fun v => ?_
    have : ζ.comp (m.appLE U'' W hWU'').hom = algebraMap Γ(G, U'') F := by
      apply ringHom_eq_of_specMap_comp_fromSpec hU''
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
        IsAffineOpen.SpecMap_appLE_fromSpec _ hU'' hW hWU'', ← Category.assoc, hζ, hzm, hax]
    exact (congrArg (fun φ => φ v) this).symm
  have E := hω V U' U'' hV hU' hU'' W hW hWV hWU' hWU'' ω' ω'' hω' hω''
  have E' := congrArg (TopFormOrder.topFormMap Γ(G, V) L Γ(pullback g g, W) F d) E
  have A1 : TopFormOrder.topFormMap Γ(G, V) L Γ(pullback g g, W) F d
      (TopFormOrder.topFormMap K Γ(G, V) Γ(G, U'') Γ(pullback g g, W) d ω'') =
      TopFormOrder.topFormMap K L Γ(G, U'') F d ω'' :=
    @NeronModelInfra.TopFormOrder.topFormMap_topFormMap K Γ(G, V) L Γ(G, U'')
      Γ(pullback g g, W) F _ _ _ _ _ _ algKV algVL _ towerKVL algKU'' algVW _
      algU''W algWF algU''F towerU2WF algKW towerKU2W towerKVW
      algVF towerVWF towerVLF _ _ _ d ω''
  have A2 : TopFormOrder.topFormMap Γ(G, V) L Γ(pullback g g, W) F d
      (TopFormOrder.topFormMap K Γ(G, V) Γ(G, U') Γ(pullback g g, W) d ω') =
      TopFormOrder.topFormMap K L Γ(G, U') F d ω' :=
    @NeronModelInfra.TopFormOrder.topFormMap_topFormMap K Γ(G, V) L Γ(G, U')
      Γ(pullback g g, W) F _ _ _ _ _ _ algKV algVL _ towerKVL algKU' algVW _
      algU'W algWF algU'F towerUWF algKW towerKUW towerKVW
      algVF towerVWF towerVLF _ _ _ d ω'
  exact A1.symm.trans (E'.trans A2)

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

universe u

theorem exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq
    {K : Type u} [Field K] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of K))
    [Smooth g] (LG : RelativeGroupLaw K g) (d : ℕ) [SmoothOfRelativeDimension d g] :
    ∃ ω : Γ(g.topDifferentials d, ⊤), Scheme.Modules.IsFrameOn ω ⊤ ∧
      ∀ (L F : Type u) [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower
        K L F]
        (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) g)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) g)
        (U' U'' : G.Opens) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        [Algebra Γ(G, U') F] [Algebra Γ(G, U'') F],
        let _ : Algebra K Γ(G, U') := g.sectionsAlgebra U'
        let _ : Algebra K Γ(G, U'') := g.sectionsAlgebra U''
        ∀ [IsScalarTower K Γ(G, U') F] [IsScalarTower K Γ(G, U'') F],
        Spec.map (CommRingCat.ofHom (algebraMap Γ(G, U') F)) ≫ hU'.fromSpec = x.1 →
        Spec.map (CommRingCat.ofHom (algebraMap Γ(G, U'') F)) ≫ hU''.fromSpec =
          (LG.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
            ⟨Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1, by
              rw [Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]⟩ x).1 →
        ∀ (ω' : ⋀[Γ(G, U')]^d (g.kaehlerPresheaf.obj (op U')))
          (ω'' : ⋀[Γ(G, U'')]^d (g.kaehlerPresheaf.obj (op U''))),
          g.topToSections d U' ω' = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          g.topToSections d U'' ω'' = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K L Γ(G, U'') F d ω'' = TopFormOrder.topFormMap K L Γ(G, U') F d
            ω' := by
  obtain ⟨ω, hfr, hω⟩ :=
    exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq g LG d
  exact ⟨ω, hfr,
    topFormMap_mul_eq_of_forall_topFormMap_appLE_mul_eq g LG d ω hω⟩

end GoodReductionJacobian.RelativeGroupLaw
end
