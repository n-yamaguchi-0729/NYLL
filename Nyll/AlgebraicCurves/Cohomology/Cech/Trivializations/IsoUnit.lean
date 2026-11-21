/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_nonempty_iso_unit_of_forall_transition_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Tactic.Choose
public import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
public import Nyll.AlgebraicCurves.Geometry.Schemes.Covers.OrderedAffineCoverComap
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.Deformation.CechObstruction
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Sections.UnitAutSectionTransUnitAutSectionRefl
public import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Pullback.PullbackCompHomAppCompPullbackUnitIsoHom
public import Nyll.SchemeTheory.Modules.Functoriality.UniqueIsoPullbackMapIsoEq
public import Nyll.AlgebraicCurves.Cohomology.Cech.Trivializations.IsUnitTransitionTransitionFaceMulEq

/-!
# Scheme Modules Cech Trivialisation nonempty iso unit of forall transition eq one
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules.CechTrivialisation (transitionSection_restrict)

open AlgebraicGeometry.Scheme.Modules.CechTrivialisation (transition_eq_transitionSection)

open AlgebraicGeometry.Scheme.Modules.CechTrivialisation (restrict_trans)

open AlgebraicGeometry.Scheme.Modules
  (unitAutSection_eq unitAutSection_trans unitAutSection_refl
    unitAutSection_symm_mul unitAutSection_mul_symm isUnit_unitAutSection)

open AlgebraicGeometry.Scheme.Modules
  (unitAutSectionValue restrictTrivialisation restrictPullbackIso)
open AlgebraicGeometry.Scheme.Modules.CechTrivialisation (transitionSection)

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivIsoUnitAll

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace L5G
namespace UA
open AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

end L5G.UA

open L5G.UA

open SchemeModulesCechTrivIsUnit.PV1TL
  (pullbackCongr_hom_app_eq pullbackCongr_inv_app_eq assoc_app assoc_app''
  comp_congr_right comp_congr_left congr_unit congr_nat conj_symm_trans_conj
  symm_trans_trans_symm_trans)

namespace L5G

open _root_.AlgebraicGeometry.Scheme.Modules


section conj
variable {X Z : Scheme.{u}} (φ : X ⟶ Z)

/-- View a regular function as a section of the unit module. -/
def toU (U : Z.Opens) (g : Z.presheaf.obj (op U)) :
    Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), U) := g

theorem pullbackUnitIso_hom_app_pls (U : Z.Opens) (g : Z.presheaf.obj (op U)) :
    (pullbackUnitIso φ).hom.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ (toU U g)) =
      toU (φ ⁻¹ᵁ U) ((φ.app U).hom g) := by
  let L : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let N : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let k : L ⟶ (Scheme.Modules.pushforward φ).obj N :=
    SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom
  exact Scheme.Modules.homEquiv_symm_app_pullbackLocalSection φ k (toU U g)

theorem pullbackUnitIso_inv_app_one (U : Z.Opens) :
    (pullbackUnitIso φ).inv.app (φ ⁻¹ᵁ U) (toU (φ ⁻¹ᵁ U) 1) = pullbackLocalSection φ (toU U 1) := by
  have h := pullbackUnitIso_hom_app_pls φ U 1
  rw [map_one] at h
  let L : X.Modules := (Scheme.Modules.pullback φ).obj (SheafOfModules.unit Z.ringCatSheaf)
  let N : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let e : L ≅ N := pullbackUnitIso φ
  let s : Γ(L, φ ⁻¹ᵁ U) := pullbackLocalSection φ (toU U 1)
  have h' : e.hom.app (φ ⁻¹ᵁ U) s = toU (φ ⁻¹ᵁ U) 1 := h
  have he : e.inv.app (φ ⁻¹ᵁ U) (e.hom.app (φ ⁻¹ᵁ U) s) = s :=
    congrArg (fun k : L ⟶ L => k.app (φ ⁻¹ᵁ U) s) e.hom_inv_id
  exact (congrArg (fun z : Γ(N, φ ⁻¹ᵁ U) => e.inv.app (φ ⁻¹ᵁ U) z) h').symm.trans he

end conj

variable {Y : Scheme.{u}}

lemma presheaf_map_op_apply_eq {U V : Y.Opens} (f g : U ⟶ V) (x : Y.presheaf.obj (op V)) :
    (Y.presheaf.map f.op).hom x = (Y.presheaf.map g.op).hom x := by
  rw [Subsingleton.elim f g]

lemma presheaf_comp_apply_eq {U V V' W : Y.Opens} (f : V ⟶ U) (g : W ⟶ V) (f' : V' ⟶ U) (g' : W
  ⟶ V')
    (x : Y.presheaf.obj (op U)) :
    (Y.presheaf.map f.op ≫ Y.presheaf.map g.op).hom x = (Y.presheaf.map f'.op ≫ Y.presheaf.map
      g'.op).hom x := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, Subsingleton.elim (g ≫ f)
    (g' ≫ f')]

theorem unitAutSection_conj {W W' : Y.Opens} (h' : W' ≤ W)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    unitAutSection W' ((pullbackUnitIso (Y.homOfLE h')).symm ≪≫
        (Scheme.Modules.pullback (Y.homOfLE h')).mapIso E ≪≫ pullbackUnitIso (Y.homOfLE h')) =
      (Y.presheaf.map (homOfLE h').op).hom (unitAutSection W E) := by
  have step : unitAutSectionValue W' (show @Iso ((W' : Scheme.{u}).Modules) _ _ _ from
      (pullbackUnitIso (Y.homOfLE h')).symm ≪≫
      (Scheme.Modules.pullback (Y.homOfLE h')).mapIso E ≪≫ pullbackUnitIso (Y.homOfLE h')) 1 =
      ((Y.homOfLE h').appTop).hom (unitAutSectionValue W E 1) := by
    let q := Y.homOfLE h'
    let L : (W : Scheme.{u}).Modules := SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf
    let N : (W' : Scheme.{u}).Modules := SheafOfModules.unit (W' : Scheme.{u}).ringCatSheaf
    let F := Scheme.Modules.pullback q
    let P : (W' : Scheme.{u}).Modules := F.obj L
    let e : P ≅ N := pullbackUnitIso q
    let E' : L ≅ L := E
    let V : (W' : Scheme.{u}).Opens := q ⁻¹ᵁ ⊤
    let one : Γ(N, V) := toU V 1
    let s : Γ(P, V) := pullbackLocalSection q (toU ⊤ 1)
    let t : Γ(L, ⊤) := E'.hom.app ⊤ (toU ⊤ 1)
    have hi : e.inv.app V one = s := pullbackUnitIso_inv_app_one q ⊤
    have hm : (F.map E'.hom).app V s = pullbackLocalSection q t :=
      (pullbackLocalSection_app q E'.hom (toU ⊤ 1)).symm
    have hh : e.hom.app V (pullbackLocalSection q t) = toU V ((q.app ⊤).hom t) :=
      pullbackUnitIso_hom_app_pls q ⊤ t
    have hc : e.hom.app V ((F.map E'.hom).app V (e.inv.app V one)) =
        toU V ((q.app ⊤).hom t) :=
      (congrArg (fun z : Γ(P, V) => e.hom.app V ((F.map E'.hom).app V z)) hi).trans
        ((congrArg (fun z : Γ(P, V) => e.hom.app V z) hm).trans hh)
    exact hc
  refine (congrArg W'.topIso.hom.hom step).trans ?_
  simp only [Scheme.Hom.appTop, Scheme.homOfLE_app, Scheme.Opens.topIso_hom]
  exact presheaf_comp_apply_eq _ _ _ _ _

end L5G

namespace L5G

open _root_.AlgebraicGeometry.Scheme.Modules

end L5G

namespace L5G

open _root_.AlgebraicGeometry.Scheme.Modules

end L5G

namespace L5G

open _root_.AlgebraicGeometry.Scheme.Modules
open UA


variable {Y : Scheme.{u}}

section localAgree
variable (W : Y.Opens)

theorem eq_refl_of_uASm_eq_one
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf))
    (h : unitAutSection W E = 1) : E = Iso.refl _ := by
  have h1 : unitAutSectionValue W E 1 = 1 := by
    rw [unitAutSection_eq] at h
    have h2 := congrArg W.topIso.inv.hom h
    rw [map_one, ← CommRingCat.comp_apply, Iso.hom_inv_id] at h2
    exact h2
  apply Iso.ext
  apply (SheafOfModules.unit ((W : Scheme.{u}).ringCatSheaf)).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  let f : (op ⊤ : ((W : Scheme.{u}).Opens)ᵒᵖ) ⟶ V := (homOfLE (le_top (a := V.unop))).op
  have H : ∀ (s t : (SheafOfModules.unit ((W : Scheme.{u}).ringCatSheaf)).sections),
      s.val (op ⊤) = t.val (op ⊤) → s.val V = t.val V := by
    intro s t hst
    rw [← PresheafOfModules.sections_property s f, ← PresheafOfModules.sections_property t f, hst]
  apply H
  exact h1

end localAgree

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules} (τ : CechTrivialisation 𝒱 𝓜)

theorem restrict_congr_idx {a a' : 𝒱.ι} (e : a = a') {W : Y.Opens} (ha : W ≤ 𝒱.U a) (ha' : W ≤
  𝒱.U a') :
    τ.restrict ha = τ.restrict ha' := by
  subst e; rfl

/-- The increasing one-simplex associated to two strictly ordered cover indices. -/
def pair {a b : 𝒱.ι} (hab : a < b) : 𝒱.Idx 1 :=
  ⟨![a, b], Fin.strictMono_iff_lt_succ.2 (fun i => by
    fin_cases i
    exact hab)⟩

theorem pair_zero {a b : 𝒱.ι} (hab : a < b) : (pair (𝒱 := 𝒱) hab).1 0 = a := rfl
theorem pair_one {a b : 𝒱.ι} (hab : a < b) : (pair (𝒱 := 𝒱) hab).1 1 = b := rfl

theorem le_inter_pair {a b : 𝒱.ι} (hab : a < b) {W : Y.Opens} (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    W ≤ 𝒱.inter (pair hab) := by
  refine le_iInf fun j => ?_
  fin_cases j
  · exact ha
  · exact hb

theorem restrict_eq_of_lt (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1)
    {a b : 𝒱.ι} (hab : a < b) {W : Y.Opens} (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    τ.restrict ha = τ.restrict hb := by
  have hW := le_inter_pair hab ha hb
  have key := transitionSection_restrict τ hW ((pair hab).1 0) ((pair hab).1 1)
    (𝒱.inter_le _ 0) (𝒱.inter_le _ 1)
  rw [← transition_eq_transitionSection, h1, map_one] at key
  have E := eq_refl_of_uASm_eq_one W _ key.symm
  have E' : τ.restrict (hW.trans (𝒱.inter_le (pair hab) 1)) = τ.restrict (hW.trans (𝒱.inter_le
    (pair hab) 0)) := by
    let U : (W : Scheme.{u}).Modules := SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf
    let M : (W : Scheme.{u}).Modules := (Scheme.Modules.pullback W.ι).obj 𝓜
    let Ra : M ≅ U := τ.restrict (hW.trans (𝒱.inter_le (pair hab) 0))
    let Rb : M ≅ U := τ.restrict (hW.trans (𝒱.inter_le (pair hab) 1))
    have he : Ra.inv ≫ Rb.hom = 𝟙 U := congrArg Iso.hom E
    exact Iso.ext (((Iso.inv_comp_eq Ra).mp he).trans (Category.comp_id Ra.hom))
  rw [restrict_congr_idx τ (pair_zero hab) _ ha, restrict_congr_idx τ (pair_one hab) _ hb] at E'
  exact E'.symm

theorem restrict_indep (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1)
    {a b : 𝒱.ι} {W : Y.Opens} (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    τ.restrict ha = τ.restrict hb := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact restrict_eq_of_lt τ h1 hab ha hb
  · rfl
  · exact (restrict_eq_of_lt τ h1 hba hb ha).symm

theorem mapIso_pullbackUnitIso_trans {W W' : Y.Opens} (h' : W' ≤ W) :
    (Scheme.Modules.pullback (Y.homOfLE h')).mapIso (pullbackUnitIso W.ι) ≪≫ pullbackUnitIso
      (Y.homOfLE h') =
      restrictPullbackIso (SheafOfModules.unit Y.ringCatSheaf) h' ≪≫ pullbackUnitIso W'.ι := by
  let L : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let U : (W : Scheme.{u}).Modules := SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf
  let U' : (W' : Scheme.{u}).Modules := SheafOfModules.unit (W' : Scheme.{u}).ringCatSheaf
  let q := Y.homOfLE h'
  let F := Scheme.Modules.pullback q
  let e : (Scheme.Modules.pullback W.ι).obj L ≅ U := pullbackUnitIso W.ι
  let ε : F.obj U ≅ U' := pullbackUnitIso q
  let δ : (Scheme.Modules.pullback W'.ι).obj L ≅ U' := pullbackUnitIso W'.ι
  let b := (pullbackComp q W.ι).hom.app L
  let c := (pullbackCongr (Y.homOfLE_ι h')).hom.app L
  have hu : b ≫ (pullbackUnitIso (q ≫ W.ι)).hom = F.map e.hom ≫ ε.hom :=
    Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom q W.ι
  have hc : c ≫ δ.hom = (pullbackUnitIso (q ≫ W.ι)).hom :=
    congr_unit (T' := (W' : Scheme)) (T := Y) (Y.homOfLE_ι h')
  apply Iso.ext
  exact hu.symm.trans
    ((congrArg (fun k : (Scheme.Modules.pullback (q ≫ W.ι)).obj L ⟶ U' => b ≫ k) hc.symm).trans
      (Category.assoc b c δ.hom).symm)

variable (𝒱) in
/-- Open subsets contained in at least one member of the ordered affine cover. -/
def Sub : Type u := {W : Y.Opens // ∃ a : 𝒱.ι, W ≤ 𝒱.U a}

/-- Choose a cover member containing an open subset subordinate to the cover. -/
noncomputable def ch (i : Sub 𝒱) : 𝒱.ι := i.2.choose

theorem le_ch (i : Sub 𝒱) : i.1 ≤ 𝒱.U (ch i) := i.2.choose_spec

theorem iSup_sub_eq_top : ⨆ i : Sub 𝒱, i.1 = ⊤ := by
  rw [eq_top_iff, ← 𝒱.iSup_eq_top]
  exact iSup_le fun a => le_iSup_of_le (⟨𝒱.U a, a, le_rfl⟩ : Sub 𝒱) le_rfl

theorem sub_basisLike (i j : Sub 𝒱) :
    i.1 ⊓ j.1 ≤ ⨆ (k : {k : Sub 𝒱 // k.1 ≤ i.1 ⊓ j.1}), k.1.1 :=
  le_iSup_of_le (⟨⟨i.1 ⊓ j.1, ch i, inf_le_left.trans (le_ch i)⟩, le_rfl⟩ : {k : Sub 𝒱 // k.1 ≤
    i.1 ⊓ j.1})
    le_rfl

/-- Compare the module with the unit module after pullback to a subordinate open subset. -/
noncomputable def eSub (i : Sub 𝒱) :
    (Scheme.Modules.pullback i.1.ι).obj 𝓜 ≅
      (Scheme.Modules.pullback i.1.ι).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  τ.restrict (le_ch i) ≪≫ (pullbackUnitIso i.1.ι).symm

theorem eSub_compat (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1) (i j : Sub 𝒱) (h : j.1 ≤ i.1) :
    (Scheme.Modules.pullback (Y.homOfLE h)).mapIso (eSub τ i) =
      ((Scheme.Modules.pullbackComp (Y.homOfLE h) i.1.ι).app 𝓜 ≪≫
          (Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app 𝓜) ≪≫
        eSub τ j ≪≫
        ((Scheme.Modules.pullbackComp (Y.homOfLE h) i.1.ι).app (SheafOfModules.unit
          Y.ringCatSheaf) ≪≫
          (Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app (SheafOfModules.unit
            Y.ringCatSheaf)).symm := by
  let Wi : Y.Opens := i.1
  let Wj : Y.Opens := j.1
  let hij : Wj ≤ Wi := h
  let q := Y.homOfLE hij
  let F := Scheme.Modules.pullback q
  let L : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let Ui : (Wi : Scheme.{u}).Modules := SheafOfModules.unit (Wi : Scheme.{u}).ringCatSheaf
  let Uj : (Wj : Scheme.{u}).Modules := SheafOfModules.unit (Wj : Scheme.{u}).ringCatSheaf
  let Mi : (Wi : Scheme.{u}).Modules := (Scheme.Modules.pullback Wi.ι).obj 𝓜
  let Mj : (Wj : Scheme.{u}).Modules := (Scheme.Modules.pullback Wj.ι).obj 𝓜
  let Ki : (Wi : Scheme.{u}).Modules := (Scheme.Modules.pullback Wi.ι).obj L
  let Kj : (Wj : Scheme.{u}).Modules := (Scheme.Modules.pullback Wj.ι).obj L
  let Ra : Mi ≅ Ui := τ.restrict (le_ch i)
  let Rb : Mj ≅ Uj := τ.restrict (le_ch j)
  let a : F.obj Mi ≅ Mj := restrictPullbackIso 𝓜 hij
  let b : F.obj Ki ≅ Kj := restrictPullbackIso L hij
  let c : Ki ≅ Ui := pullbackUnitIso Wi.ι
  let d : Kj ≅ Uj := pullbackUnitIso Wj.ι
  let ε : F.obj Ui ≅ Uj := pullbackUnitIso q
  have hr : a.symm ≪≫ F.mapIso Ra ≪≫ ε = Rb :=
    (restrict_trans τ (le_ch i) hij).symm.trans
      (restrict_indep τ h1 (hij.trans (le_ch i)) (le_ch j))
  have hres : F.mapIso Ra = a ≪≫ Rb ≪≫ ε.symm := by
    apply Iso.ext
    have hx := congrArg (fun k : Mj ⟶ Uj => a.hom ≫ k ≫ ε.inv)
      (congrArg (fun k : Mj ≅ Uj => k.hom) hr)
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using hx
  have hu : F.mapIso c ≪≫ ε = b ≪≫ d := mapIso_pullbackUnitIso_trans (Y := Y) hij
  have hunit : F.mapIso c.symm = ε ≪≫ d.symm ≪≫ b.symm := by
    have hx := congrArg (fun k : F.obj Ki ≅ Uj => ε ≪≫ k.symm) hu
    have hmap : F.mapIso c.symm = (F.mapIso c).symm := F.mapIso_symm c
    refine hmap.trans ?_
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
      Iso.hom_inv_id_assoc] using congrArg (fun k : F.obj Ui ≅ F.obj Ki => k.hom) hx
  have hfinal : F.mapIso (Ra ≪≫ c.symm) = a ≪≫ (Rb ≪≫ d.symm) ≪≫ b.symm := by
    apply Iso.ext
    have hx := congrArg (fun k : F.obj Mi ≅ F.obj Ki => k.hom)
      ((F.mapIso_trans Ra c.symm).trans (congrArg₂ Iso.trans hres hunit))
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using hx
  exact hfinal

theorem main (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1) :
    Nonempty (𝓜 ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  obtain ⟨f, -, -⟩ :=
    Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top 𝓜
      (SheafOfModules.unit Y.ringCatSheaf) (fun i : Sub 𝒱 => i.1) iSup_sub_eq_top sub_basisLike
      (eSub τ) (eSub_compat τ h1)
  exact ⟨f⟩

end L5G

end AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivIsoUnitAll

section PublicStatement

open
  _root_.CategoryTheory
  _root_.CategoryTheory.Limits
  _root_.AlgebraicGeometry
  _root_.Opposite
  _root_.TopologicalSpace
universe u
open _root_.AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivIsoUnitAll.L5G.UA
open _root_.AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivIsoUnitAll

namespace AlgebraicGeometry.Scheme.Modules.CechTrivialisation

theorem nonempty_iso_unit_of_forall_transition_eq_one
    {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    (h : ∀ s : 𝒱.Idx 1, τ.transition s = 1) :
    Nonempty (𝓜 ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  exact L5G.main τ h

end AlgebraicGeometry.Scheme.Modules.CechTrivialisation

end PublicStatement
end ProofImplementation

attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
